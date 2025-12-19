# Deployment Guide

## Deploying to Vercel

### Option 1: Vercel Dashboard (Recommended for First Deployment)

1. **Create Vercel Account**
   - Go to https://vercel.com/signup
   - Sign up with GitHub (recommended for automatic deployments)

2. **Import Project**
   - Click "Add New..." → "Project"
   - Import your GitHub repository `hupyy-cpp-to-c`
   - Configure project settings:
     - **Framework Preset**: Astro
     - **Root Directory**: `website`
     - **Build Command**: `npm run build`
     - **Output Directory**: `dist`

3. **Deploy**
   - Click "Deploy"
   - Wait for build to complete
   - Your site will be live at `https://[project-name].vercel.app`

4. **Verify Headers**
   - Open deployed site in browser
   - Open DevTools Console
   - Check for message: `✓ Cross-origin isolation enabled - WebAssembly ready!`
   - Or manually test: `typeof SharedArrayBuffer !== 'undefined'` should return `true`

### Option 2: Vercel CLI

1. **Install Vercel CLI**
   ```bash
   npm install -g vercel
   ```

2. **Login**
   ```bash
   vercel login
   ```
   Follow the prompts to authenticate

3. **Deploy from website directory**
   ```bash
   cd website
   vercel --prod
   ```

4. **Configure on first deploy**
   - Link to existing project or create new
   - Set root directory to `.` (already in website/)
   - Confirm framework detection (Astro)
   - Confirm build settings

### Option 3: GitHub Actions (Automated)

Create `.github/workflows/deploy-website.yml` in repository root:

```yaml
name: Deploy Website to Vercel

on:
  push:
    branches:
      - main
      - develop
    paths:
      - 'website/**'
  workflow_dispatch:

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout
        uses: actions/checkout@v3

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: '18'
          cache: 'npm'
          cache-dependency-path: website/package-lock.json

      - name: Install dependencies
        working-directory: website
        run: npm ci

      - name: Build
        working-directory: website
        run: npm run build

      - name: Deploy to Vercel
        uses: amondnet/vercel-action@v25
        with:
          vercel-token: ${{ secrets.VERCEL_TOKEN }}
          vercel-org-id: ${{ secrets.VERCEL_ORG_ID }}
          vercel-project-id: ${{ secrets.VERCEL_PROJECT_ID }}
          working-directory: website
          vercel-args: '--prod'
```

**Required Secrets** (add in GitHub repository settings):
- `VERCEL_TOKEN`: Generate at https://vercel.com/account/tokens
- `VERCEL_ORG_ID`: Find in Vercel project settings
- `VERCEL_PROJECT_ID`: Find in Vercel project settings

## Verifying COOP/COEP Headers

After deployment, verify headers are correctly set:

### Method 1: Browser DevTools
1. Open deployed site
2. Open DevTools → Network tab
3. Reload page
4. Click on main document request
5. Check Response Headers:
   - `Cross-Origin-Opener-Policy: same-origin`
   - `Cross-Origin-Embedder-Policy: credentialless`

### Method 2: Console Check
Open browser console on deployed site and look for:
```
Cross-origin isolated: true
SharedArrayBuffer available: true
✓ Cross-origin isolation enabled - WebAssembly ready!
```

### Method 3: curl
```bash
curl -I https://your-site.vercel.app
```

Look for headers in response:
```
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: credentialless
```

## Troubleshooting

### Headers Not Applied

**Problem**: `crossOriginIsolated` is `false` or `undefined`

**Solutions**:
1. Verify `vercel.json` exists in website root
2. Check Vercel build logs for errors
3. Ensure `vercel.json` is not in `.gitignore`
4. Try redeploying: `vercel --prod --force`
5. Check Vercel dashboard → Project Settings → Headers

### Build Fails

**Problem**: Build fails on Vercel

**Solutions**:
1. Check Node.js version (requires 18+)
2. Verify `package.json` scripts are correct
3. Check build logs for specific errors
4. Test build locally: `npm run build`
5. Ensure all dependencies are in `package.json` (not just devDependencies)

### SharedArrayBuffer Still Undefined

**Problem**: Headers are set but SharedArrayBuffer is still undefined

**Solutions**:
1. Check browser version (Chrome 92+, Firefox 90+, Safari 15.2+)
2. Hard refresh (Cmd+Shift+R / Ctrl+Shift+F5)
3. Clear browser cache
4. Try incognito/private window
5. Test in different browser

## Custom Domain (Optional)

1. Go to Vercel project settings
2. Navigate to "Domains"
3. Add your custom domain
4. Configure DNS records as instructed
5. Wait for SSL certificate provisioning (automatic)
6. Access site via custom domain

## Environment Variables

For future phases (Phase 2+) that may require environment variables:

1. Go to Vercel project settings
2. Navigate to "Environment Variables"
3. Add variables for Production, Preview, Development
4. Redeploy to apply changes

## Performance Monitoring

Vercel provides built-in analytics:

1. Enable Vercel Analytics (free tier available)
2. View metrics in Vercel dashboard
3. Monitor:
   - Page views
   - Top pages
   - Response times
   - Build times

## Deployment Checklist

Before deploying:

- [ ] All pages build successfully locally (`npm run build`)
- [ ] TypeScript type-check passes (`npx tsc --noEmit`)
- [ ] No console errors in development
- [ ] All routes accessible (/, /playground, /docs, /examples)
- [ ] Layout renders correctly on mobile
- [ ] `vercel.json` includes COOP/COEP headers
- [ ] README.md is updated
- [ ] Git changes are committed

After deploying:

- [ ] Deployment succeeded in Vercel dashboard
- [ ] Site is accessible at provided URL
- [ ] All routes load (/, /playground, /docs, /examples)
- [ ] Headers are correctly set (verify with DevTools)
- [ ] `crossOriginIsolated === true` in console
- [ ] No 404 errors or broken links
- [ ] Mobile responsive design works

## Next Steps

After Phase 1 deployment:

1. **Phase 2**: Add WebAssembly transpiler integration
2. **Phase 3**: Implement interactive playground
3. **Phase 4**: Migrate documentation content
4. **Phase 5**: Add example gallery and optimization

## Support

For Vercel-specific issues:
- Vercel Documentation: https://vercel.com/docs
- Vercel Support: https://vercel.com/support

For Astro-specific issues:
- Astro Documentation: https://docs.astro.build
- Astro Discord: https://astro.build/chat
