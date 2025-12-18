#!/usr/bin/env python3
"""
Benchmark Comparison and Regression Detection Script

This script compares benchmark results between two runs (baseline vs current)
and detects performance regressions based on configurable thresholds.

Usage:
    ./compare_benchmarks.py <baseline.json> <current.json> [--threshold PERCENT] [--ci]

Options:
    --threshold PERCENT  Regression threshold percentage (default: 5.0)
    --ci                 CI mode - fail (exit 1) if regression detected
    --output FILE        Output comparison report to file
    --format FORMAT      Output format: text, json, markdown (default: text)
"""

import sys
import json
import argparse
from typing import Dict, List, Tuple, Any
from dataclasses import dataclass
from enum import Enum


class Status(Enum):
    """Comparison status for a benchmark."""
    IMPROVED = "improved"
    REGRESSION = "regression"
    NO_CHANGE = "no_change"
    NEW = "new"
    MISSING = "missing"


@dataclass
class BenchmarkMetric:
    """Represents a single benchmark metric."""
    name: str
    baseline_value: float
    current_value: float
    unit: str
    lower_is_better: bool = True

    @property
    def percent_change(self) -> float:
        """Calculate percentage change (negative = improvement if lower_is_better)."""
        if self.baseline_value == 0:
            return 0.0
        change = ((self.current_value - self.baseline_value) / self.baseline_value) * 100
        return change

    @property
    def status(self) -> Status:
        """Determine the status based on percent change."""
        threshold = 0.5  # 0.5% is considered "no change"
        change = self.percent_change

        if abs(change) < threshold:
            return Status.NO_CHANGE

        if self.lower_is_better:
            return Status.IMPROVED if change < 0 else Status.REGRESSION
        else:
            return Status.IMPROVED if change > 0 else Status.REGRESSION


@dataclass
class ComparisonResult:
    """Results of benchmark comparison."""
    metrics: List[BenchmarkMetric]
    new_benchmarks: List[str]
    missing_benchmarks: List[str]
    regression_threshold: float

    @property
    def has_regressions(self) -> bool:
        """Check if any regressions exceed threshold."""
        for metric in self.metrics:
            if metric.status == Status.REGRESSION and abs(metric.percent_change) > self.regression_threshold:
                return True
        return False

    @property
    def regressions(self) -> List[BenchmarkMetric]:
        """Get list of regressions exceeding threshold."""
        return [m for m in self.metrics if m.status == Status.REGRESSION
                and abs(m.percent_change) > self.regression_threshold]

    @property
    def improvements(self) -> List[BenchmarkMetric]:
        """Get list of improvements."""
        return [m for m in self.metrics if m.status == Status.IMPROVED]


def load_json(filepath: str) -> Dict[str, Any]:
    """Load JSON file with error handling."""
    try:
        with open(filepath, 'r') as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {filepath}: {e}", file=sys.stderr)
        sys.exit(1)


def extract_metrics(data: Dict[str, Any], label: str) -> Dict[str, Tuple[float, str]]:
    """
    Extract benchmark metrics from JSON data.
    Returns dict mapping benchmark_name -> (value, unit)
    """
    metrics = {}

    # Extract from benchmarks section
    if "benchmarks" in data:
        for bench_name, bench_data in data["benchmarks"].items():
            if isinstance(bench_data, dict):
                # Look for common metric names
                for metric_name in ["mean_time_ns", "time_per_op_ns", "ops_per_second", "memory_usage_mb"]:
                    if metric_name in bench_data:
                        value = bench_data[metric_name]
                        unit = "ns" if "time" in metric_name else ("ops/s" if "ops" in metric_name else "MB")
                        key = f"{bench_name}:{metric_name}"
                        metrics[key] = (float(value), unit)

    return metrics


def compare_benchmarks(baseline_file: str, current_file: str, threshold: float) -> ComparisonResult:
    """
    Compare two benchmark results and detect regressions.

    Args:
        baseline_file: Path to baseline JSON file
        current_file: Path to current JSON file
        threshold: Regression threshold percentage

    Returns:
        ComparisonResult with detailed comparison
    """
    baseline_data = load_json(baseline_file)
    current_data = load_json(current_file)

    baseline_metrics = extract_metrics(baseline_data, "baseline")
    current_metrics = extract_metrics(current_data, "current")

    all_metric_names = set(baseline_metrics.keys()) | set(current_metrics.keys())

    metrics = []
    new_benchmarks = []
    missing_benchmarks = []

    for metric_name in sorted(all_metric_names):
        if metric_name in baseline_metrics and metric_name in current_metrics:
            baseline_val, unit = baseline_metrics[metric_name]
            current_val, _ = current_metrics[metric_name]

            # Determine if lower is better based on metric name
            lower_is_better = "time" in metric_name or "memory" in metric_name

            metric = BenchmarkMetric(
                name=metric_name,
                baseline_value=baseline_val,
                current_value=current_val,
                unit=unit,
                lower_is_better=lower_is_better
            )
            metrics.append(metric)

        elif metric_name in current_metrics and metric_name not in baseline_metrics:
            new_benchmarks.append(metric_name)
        elif metric_name in baseline_metrics and metric_name not in current_metrics:
            missing_benchmarks.append(metric_name)

    return ComparisonResult(
        metrics=metrics,
        new_benchmarks=new_benchmarks,
        missing_benchmarks=missing_benchmarks,
        regression_threshold=threshold
    )


def format_text_report(result: ComparisonResult, baseline_file: str, current_file: str) -> str:
    """Format comparison result as text report."""
    lines = []
    lines.append("=" * 80)
    lines.append("BENCHMARK COMPARISON REPORT")
    lines.append("=" * 80)
    lines.append(f"Baseline: {baseline_file}")
    lines.append(f"Current:  {current_file}")
    lines.append(f"Regression Threshold: {result.regression_threshold}%")
    lines.append("=" * 80)
    lines.append("")

    if result.metrics:
        lines.append("BENCHMARK RESULTS:")
        lines.append("-" * 80)
        lines.append(f"{'Benchmark':<50} {'Baseline':<12} {'Current':<12} {'Change':<10} {'Status':<12}")
        lines.append("-" * 80)

        for metric in result.metrics:
            change_str = f"{metric.percent_change:+.2f}%"
            status_str = metric.status.value.upper()

            # Add visual indicator
            if metric.status == Status.REGRESSION:
                status_str = f"[REGRESSION] {status_str}"
            elif metric.status == Status.IMPROVED:
                status_str = f"[IMPROVED] {status_str}"

            lines.append(
                f"{metric.name:<50} "
                f"{metric.baseline_value:>10.2f}{metric.unit:<2} "
                f"{metric.current_value:>10.2f}{metric.unit:<2} "
                f"{change_str:<10} "
                f"{status_str:<12}"
            )
        lines.append("")

    if result.new_benchmarks:
        lines.append("NEW BENCHMARKS:")
        lines.append("-" * 80)
        for bench in result.new_benchmarks:
            lines.append(f"  + {bench}")
        lines.append("")

    if result.missing_benchmarks:
        lines.append("MISSING BENCHMARKS (in baseline but not in current):")
        lines.append("-" * 80)
        for bench in result.missing_benchmarks:
            lines.append(f"  - {bench}")
        lines.append("")

    lines.append("=" * 80)
    lines.append("SUMMARY")
    lines.append("=" * 80)
    lines.append(f"Total benchmarks compared: {len(result.metrics)}")
    lines.append(f"Improvements: {len(result.improvements)}")
    lines.append(f"Regressions (>{result.regression_threshold}%): {len(result.regressions)}")
    lines.append(f"New benchmarks: {len(result.new_benchmarks)}")
    lines.append(f"Missing benchmarks: {len(result.missing_benchmarks)}")
    lines.append("")

    if result.has_regressions:
        lines.append("REGRESSION DETAILS:")
        lines.append("-" * 80)
        for metric in result.regressions:
            lines.append(
                f"  {metric.name}: {metric.percent_change:+.2f}% "
                f"({metric.baseline_value:.2f}{metric.unit} -> {metric.current_value:.2f}{metric.unit})"
            )
        lines.append("")
        lines.append("VERDICT: PERFORMANCE REGRESSION DETECTED")
    else:
        lines.append("VERDICT: NO SIGNIFICANT REGRESSIONS")

    lines.append("=" * 80)

    return "\n".join(lines)


def format_json_report(result: ComparisonResult, baseline_file: str, current_file: str) -> str:
    """Format comparison result as JSON."""
    report = {
        "baseline_file": baseline_file,
        "current_file": current_file,
        "regression_threshold": result.regression_threshold,
        "summary": {
            "total_compared": len(result.metrics),
            "improvements": len(result.improvements),
            "regressions": len(result.regressions),
            "new_benchmarks": len(result.new_benchmarks),
            "missing_benchmarks": len(result.missing_benchmarks),
            "has_regressions": result.has_regressions
        },
        "metrics": [
            {
                "name": m.name,
                "baseline_value": m.baseline_value,
                "current_value": m.current_value,
                "unit": m.unit,
                "percent_change": m.percent_change,
                "status": m.status.value
            }
            for m in result.metrics
        ],
        "new_benchmarks": result.new_benchmarks,
        "missing_benchmarks": result.missing_benchmarks,
        "regressions": [
            {
                "name": m.name,
                "baseline_value": m.baseline_value,
                "current_value": m.current_value,
                "unit": m.unit,
                "percent_change": m.percent_change
            }
            for m in result.regressions
        ]
    }
    return json.dumps(report, indent=2)


def format_markdown_report(result: ComparisonResult, baseline_file: str, current_file: str) -> str:
    """Format comparison result as Markdown (for GitHub PR comments)."""
    lines = []
    lines.append("## Benchmark Comparison Report")
    lines.append("")
    lines.append(f"**Baseline:** `{baseline_file}`  ")
    lines.append(f"**Current:** `{current_file}`  ")
    lines.append(f"**Regression Threshold:** {result.regression_threshold}%")
    lines.append("")

    if result.metrics:
        lines.append("### Benchmark Results")
        lines.append("")
        lines.append("| Benchmark | Baseline | Current | Change | Status |")
        lines.append("|-----------|----------|---------|--------|--------|")

        for metric in result.metrics:
            change_str = f"{metric.percent_change:+.2f}%"
            status_emoji = {
                Status.IMPROVED: "✅",
                Status.REGRESSION: "❌",
                Status.NO_CHANGE: "➖"
            }.get(metric.status, "")

            lines.append(
                f"| `{metric.name}` | "
                f"{metric.baseline_value:.2f} {metric.unit} | "
                f"{metric.current_value:.2f} {metric.unit} | "
                f"{change_str} | "
                f"{status_emoji} {metric.status.value} |"
            )
        lines.append("")

    if result.new_benchmarks:
        lines.append("### New Benchmarks")
        for bench in result.new_benchmarks:
            lines.append(f"- ➕ `{bench}`")
        lines.append("")

    if result.missing_benchmarks:
        lines.append("### Missing Benchmarks")
        for bench in result.missing_benchmarks:
            lines.append(f"- ➖ `{bench}`")
        lines.append("")

    lines.append("### Summary")
    lines.append("")
    lines.append(f"- **Total benchmarks compared:** {len(result.metrics)}")
    lines.append(f"- **Improvements:** {len(result.improvements)}")
    lines.append(f"- **Regressions (>{result.regression_threshold}%):** {len(result.regressions)}")
    lines.append(f"- **New benchmarks:** {len(result.new_benchmarks)}")
    lines.append(f"- **Missing benchmarks:** {len(result.missing_benchmarks)}")
    lines.append("")

    if result.has_regressions:
        lines.append("### ❌ Performance Regression Detected")
        lines.append("")
        lines.append("The following benchmarks show significant regression:")
        lines.append("")
        for metric in result.regressions:
            lines.append(
                f"- **{metric.name}**: {metric.percent_change:+.2f}% "
                f"({metric.baseline_value:.2f}{metric.unit} → {metric.current_value:.2f}{metric.unit})"
            )
    else:
        lines.append("### ✅ No Significant Regressions")

    return "\n".join(lines)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Compare benchmark results and detect performance regressions",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument("baseline", help="Baseline benchmark JSON file")
    parser.add_argument("current", help="Current benchmark JSON file")
    parser.add_argument("--threshold", type=float, default=5.0,
                        help="Regression threshold percentage (default: 5.0)")
    parser.add_argument("--ci", action="store_true",
                        help="CI mode - fail if regression detected")
    parser.add_argument("--output", help="Output report to file")
    parser.add_argument("--format", choices=["text", "json", "markdown"], default="text",
                        help="Output format (default: text)")

    args = parser.parse_args()

    # Perform comparison
    result = compare_benchmarks(args.baseline, args.current, args.threshold)

    # Format report
    if args.format == "json":
        report = format_json_report(result, args.baseline, args.current)
    elif args.format == "markdown":
        report = format_markdown_report(result, args.baseline, args.current)
    else:  # text
        report = format_text_report(result, args.baseline, args.current)

    # Output report
    if args.output:
        with open(args.output, 'w') as f:
            f.write(report)
        print(f"Report written to: {args.output}")
    else:
        print(report)

    # Exit with appropriate code in CI mode
    if args.ci and result.has_regressions:
        sys.exit(1)

    sys.exit(0)


if __name__ == "__main__":
    main()
