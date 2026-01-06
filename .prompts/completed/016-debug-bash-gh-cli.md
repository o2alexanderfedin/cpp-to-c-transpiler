<objective>
Debug why the bash script `~/.claude/skills/lib/gh-projects/gh-project-list.sh` cannot find the `gh` CLI command when executed from the project directory, but works fine from the home directory.

Focus ONLY on bash script PATH behavior and GitHub CLI availability. This is a pure shell scripting/environment issue.
</objective>

<context>
From the screenshot:
- Command works from home directory: `~/.claude/commands$`
- Command fails from project directory: `~/Projects/hapyy/hupyy-cpp-to-c$`
- Error: "gh: command not found"

This indicates the bash script is not finding `gh` in its PATH when invoked from different working directories.
</context>

<investigation>
1. **Verify gh installation location**:
   ```bash
   which gh
   ls -la /opt/homebrew/bin/gh /usr/local/bin/gh
   ```

2. **Compare PATH in both directories**:
   ```bash
   # From home directory
   cd ~
   echo $PATH

   # From project directory
   cd ~/Projects/hapyy/hupyy-cpp-to-c
   echo $PATH
   ```

3. **Examine the bash script**:
   - Read `~/.claude/skills/lib/gh-projects/gh-project-list.sh`
   - Read `~/.claude/skills/lib/gh-projects/lib/gh-project-common.sh`
   - Check how they invoke `gh` command
   - Look for any PATH modifications or restrictions

4. **Test with explicit PATH**:
   ```bash
   # If gh is in /opt/homebrew/bin, test:
   PATH=/opt/homebrew/bin:$PATH ~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json
   ```
</investigation>

<requirements>
- Identify WHY the bash script loses access to `gh` in different directories
- Determine if it's a PATH issue, shell configuration issue, or script issue
- Implement a fix directly in the bash script to ensure `gh` is always found
- The fix must work regardless of which directory the script is invoked from
</requirements>

<fix_strategy>
Likely solutions (choose the most appropriate):

1. **Add explicit PATH to the bash script**:
   Add near the top of the script:
   ```bash
   export PATH="/opt/homebrew/bin:/usr/local/bin:$PATH"
   ```

2. **Use absolute path to gh**:
   Replace `gh` commands with full path like `/opt/homebrew/bin/gh`

3. **Fix shell initialization**:
   Ensure the script sources necessary environment properly
</fix_strategy>

<output>
1. Modify the bash script(s) to fix the PATH issue
2. Test from project directory to verify the fix works
3. Document the fix in a brief comment in the script
</output>

<verification>
Run from the project directory to confirm success:
```bash
cd ~/Projects/hapyy/hupyy-cpp-to-c
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json
```

Should execute without "gh: command not found" error.
</verification>

<success_criteria>
- [ ] Root cause identified (PATH issue in bash script)
- [ ] Script modified with fix
- [ ] Tested from project directory - works
- [ ] Tested from home directory - still works
- [ ] No other scripts broken
</success_criteria>
