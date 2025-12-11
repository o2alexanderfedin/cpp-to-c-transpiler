<objective>
Add bidirectional cross-linking between the GitHub Pages documentation site and the repository README.md to improve navigation and discoverability.

Users viewing the public documentation site should have a clear path to the repository (for collaboration/licensing inquiries), and users viewing the README should know about the comprehensive documentation site.
</objective>

<context>
The project has:
- A public GitHub Pages site at: https://o2alexanderfedin.github.io/cpp-to-c-transpiler/
- A private repository with README.md at the root
- Documentation files in docs/ directory

The Pages site (docs/index.html) already exists with comprehensive project information.
The README.md needs to prominently link to the documentation site.

@README.md
@docs/index.html
</context>

<requirements>
1. Add a prominent link to the GitHub Pages documentation site in README.md
   - Should appear near the top of the README (after title/badges, before main content)
   - Use a visually distinct format (banner, callout, or dedicated section)
   - Explain what readers will find on the documentation site

2. Add a link to the repository in docs/index.html
   - Include in the footer or header
   - Should indicate repository is private but inquiries welcome
   - Include contact email for collaboration/licensing (alexander.fedin@hapyy.com)

3. Ensure links are:
   - Absolute URLs (not relative paths)
   - Clearly labeled with their purpose
   - Consistent with existing styling
</requirements>

<implementation>
For README.md:
- Add a "Documentation" section or banner after the badge row
- Use markdown formatting that stands out (perhaps a blockquote or table)
- Mention key documentation available: architecture, progress tracking, feature guides

For docs/index.html:
- Add repository link in the footer section (already exists)
- Include note about private repository with collaboration invitation
- Maintain the existing dark theme styling

Keep the tone professional and welcoming - encourage people to reach out.
</implementation>

<output>
Modify these files:
- `./README.md` - Add documentation site link near top
- `./docs/index.html` - Add repository reference in footer
</output>

<verification>
Before completing:
1. Verify the documentation site URL is correct: https://o2alexanderfedin.github.io/cpp-to-c-transpiler/
2. Check that both links are absolute URLs (not relative)
3. Ensure styling is consistent with existing content
4. Confirm email address is correct: alexander.fedin@hapyy.com
5. Test that the added content is visible and prominent
</verification>

<success_criteria>
- README.md has a clear, prominent link to the documentation site
- Documentation site has a footer link back to the repository
- Both links explain their purpose clearly
- Contact information is provided for collaboration inquiries
- All formatting is consistent with existing styles
</success_criteria>
