const puppeteer = require('puppeteer');
const fs = require('fs');
const path = require('path');
const { URL } = require('url');
const cheerio = require('cheerio');
const readline = require('readline/promises');
const { stdin: input, stdout: output } = require('process');

const MIME_TO_EXTENSION = {
    'image/jpeg': '.jpg',
    'image/jpg': '.jpg',
    'image/png': '.png',
    'image/webp': '.webp',
    'image/avif': '.avif',
    'image/gif': '.gif',
    'image/svg+xml': '.svg',
    'image/x-icon': '.ico',
    'image/vnd.microsoft.icon': '.ico',
    'text/css': '.css',
    'application/javascript': '.js',
    'text/javascript': '.js'
};

const VIEWPORTS = [
    { name: 'Desktop', width: 1280, height: 800, isMobile: false },
    { name: 'Tablet',  width: 768,  height: 1024, isMobile: true, hasTouch: true },
    { name: 'Mobile',  width: 375,  height: 812,  isMobile: true, hasTouch: true }
];

let TARGET_URL = ''; 
let OUTPUT_DIR = '';

let configData;
let FLATTEN_ASSETS = false;
let REMOVE_ALL_SCRIPTS = false;
let REMOVE_ALL_IFRAMES = false;
let REMOVE_NOSCRIPT_TAGS = false;
let STRIP_SRCSETS = true; // NEW: Default to stripping srcsets to match previous behavior

let excludedPatterns = [];
let ignoredPatterns = [];

const flatPathRegistry = new Map();
const filenameCounter = new Map();

function cleanUrlKey(urlStr) {
    try {
        const parsed = new URL(urlStr.startsWith('http') ? urlStr : 'https://' + urlStr.replace(/^\/\//, ''));
        if (parsed.pathname.includes('/_next/image') && parsed.searchParams.has('url')) {
            return parsed.searchParams.get('url').toLowerCase();
        }
        return parsed.pathname.toLowerCase();
    } catch (e) {
        return urlStr.split('?')[0].split('#')[0].toLowerCase();
    }
}

function getStableQueryHash(parsedUrl) {
    let sourceString = parsedUrl.search;
    if (parsedUrl.searchParams.has('url')) {
        sourceString = parsedUrl.searchParams.get('url');
    }
    let hash = 0;
    for (let i = 0; i < sourceString.length; i++) {
        hash = (hash << 5) - hash + sourceString.charCodeAt(i);
        hash |= 0;
    }
    return Math.abs(hash);
}

function getDomain(url) {
    try {
        const parsed = new URL(url.startsWith('http') ? url : 'https:' + url);
        let domain = parsed.hostname;
        if (domain.startsWith('www.')) domain = domain.substring(4);
        return domain;
    } catch (e) {
        let domain = url.replace(/^https?:\/\//, '');
        return domain.split('/')[0].replace(/^www\./, '');
    }
}

function wildcardToRegex(wildcardStr) {
    let escaped = wildcardStr.replace(/[.+^${}()|[\]\\]/g, '\\$&');
    escaped = escaped.replace(/\*/g, '.*').replace(/\?/g, '.');
    return new RegExp('^' + escaped + '$', 'i');
}

function getFlatRelativePath(requestUrl, contentType = '') {
    const registryKey = cleanUrlKey(requestUrl);
    if (flatPathRegistry.has(registryKey)) return flatPathRegistry.get(registryKey);

    try {
        const parsedUrl = new URL(requestUrl);
        let pathname = parsedUrl.pathname.split('?')[0];

        let subDir = 'assets';
        const mime = contentType.toLowerCase();
        if (mime.startsWith('image/')) subDir = 'images';
        else if (mime.includes('css') || pathname.endsWith('.css')) subDir = 'css';
        else if (mime.includes('javascript') || pathname.endsWith('.js')) subDir = 'js';
        else if (pathname.endsWith('.html') || pathname.endsWith('.htm')) subDir = 'html';

        let baseName = path.basename(pathname);
        if (!baseName || baseName === '/' || pathname.endsWith('/')) baseName = 'index';

        let ext = path.extname(baseName);
        if (!ext) {
            if (contentType) ext = MIME_TO_EXTENSION[mime] || '';
            else if (subDir === 'images') ext = '.png'; 
            baseName += ext;
        }

        const nameWithoutExt = path.basename(baseName, ext);
        let finalBaseName = baseName;

        const lowercaseKey = `${subDir}/${finalBaseName}`.toLowerCase();
        if (filenameCounter.has(lowercaseKey)) {
            const count = filenameCounter.get(lowercaseKey) + 1;
            filenameCounter.set(lowercaseKey, count);
            finalBaseName = `${nameWithoutExt}_${count}${ext}`;
        } else {
            filenameCounter.set(lowercaseKey, 1);
        }

        const relativePath = `${subDir}/${finalBaseName}`;
        flatPathRegistry.set(registryKey, relativePath);
        return relativePath;
    } catch (e) {
        return 'assets/unknown_asset';
    }
}

function urlToLocalPath(requestUrl, contentType = '') {
    try {
        if (requestUrl.startsWith('//')) requestUrl = 'https:' + requestUrl;

        if (FLATTEN_ASSETS) {
            const parsedUrl = new URL(requestUrl);
            const cleanTargetUrl = new URL(TARGET_URL);
            if (parsedUrl.href === cleanTargetUrl.href || parsedUrl.pathname === '/' && parsedUrl.hostname === cleanTargetUrl.hostname) {
                return path.join(OUTPUT_DIR, 'index.html');
            }
            const rel = getFlatRelativePath(requestUrl, contentType);
            return path.join(OUTPUT_DIR, rel);
        }

        const parsedUrl = new URL(requestUrl);
        let hostFolder = parsedUrl.hostname;
        if (hostFolder.startsWith('www.')) hostFolder = hostFolder.substring(4);

        let pathname = parsedUrl.pathname;
        const isImageMime = contentType && contentType.startsWith('image/');

        if (isImageMime && (pathname.endsWith('/') || path.extname(pathname) === '')) {
            const ext = MIME_TO_EXTENSION[contentType.toLowerCase()] || '.png';
            if (parsedUrl.search) {
                const stableHash = getStableQueryHash(parsedUrl);
                pathname = pathname.replace(/\/$/, '');
                pathname += `/img_${stableHash}${ext}`;
            } else {
                if (pathname.endsWith('/')) pathname += `image${ext}`;
                else pathname += ext;
            }
        } else {
            let cleanPathname = pathname.split('?')[0];
            if (cleanPathname === '/' || cleanPathname.endsWith('/')) cleanPathname += 'index.html';
            const hasExtension = path.extname(cleanPathname) !== '';
            if (!hasExtension && !cleanPathname.endsWith('.html')) cleanPathname += '/index.html';
            pathname = cleanPathname;
        }

        return path.join(OUTPUT_DIR, hostFolder, pathname);
    } catch (e) {
        return null;
    }
}

function getRelativeAssetPathForRoot(assetUrl, contentType = '') {
    if (assetUrl.startsWith('//')) assetUrl = 'https:' + assetUrl;
    if (FLATTEN_ASSETS) return getFlatRelativePath(assetUrl, contentType);

    const assetLocalPath = urlToLocalPath(assetUrl, contentType);
    if (!assetLocalPath) return assetUrl;

    let relativePath = path.relative(OUTPUT_DIR, assetLocalPath).replace(/\\/g, '/');
    if (relativePath.startsWith('/')) relativePath = relativePath.substring(1);

    try {
        const parsedUrl = new URL(assetUrl.startsWith('http') ? assetUrl : 'https:' + assetUrl);
        let targetDomain = parsedUrl.hostname;
        if (targetDomain.startsWith('www.')) targetDomain = targetDomain.substring(4);

        const doubleDomainPrefix = `${targetDomain}/${targetDomain}/`;
        if (relativePath.startsWith(doubleDomainPrefix)) {
            relativePath = relativePath.substring(targetDomain.length + 1);
        }
    } catch (e) {}

    return relativePath;
}

async function autoScroll(page) {
    await page.evaluate(async () => {
        await new Promise((resolve) => {
            let totalHeight = 0;
            const distance = 150;
            const timer = setInterval(() => {
                const scrollHeight = document.body.scrollHeight;
                window.scrollBy(0, distance);
                totalHeight += distance;
                if (totalHeight >= scrollHeight || totalHeight > 25000) {
                    clearInterval(timer);
                    resolve();
                }
            }, 100);
        });
    });
}

function rewriteCssUrls(cssText, baseUrl) {
    const cssUrlRegex = /url\(['"]?([^'")]+)['"]?\)/g;
    return cssText.replace(cssUrlRegex, (match, originalUrl) => {
        if (originalUrl.startsWith('data:')) return match;
        try {
            const absoluteUrl = new URL(originalUrl, baseUrl).href;
            if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) return match;
            const localRelativePath = getRelativeAssetPathForRoot(absoluteUrl);
            return `url("${localRelativePath}")`;
        } catch (e) {
            return match;
        }
    });
}

// Safely split srcsets avoiding splitting inside base64 data URIs
function parseSrcset(srcsetString) {
    const parts = srcsetString.split(',');
    const candidates = [];
    for (let i = 0; i < parts.length; i++) {
        let part = parts[i].trim();
        if (part.startsWith('data:') && !part.includes(' ') && i + 1 < parts.length) {
            part = part + ',' + parts[++i].trim();
        }
        if (part) candidates.push(part);
    }
    return candidates;
}

async function mainPrompts() {
    const rl = readline.createInterface({ input, output });

    let inputUrl = await rl.question('Enter website URL: ');
    if (!inputUrl.startsWith('http://') && !inputUrl.startsWith('https://')) {
        inputUrl = 'https://' + inputUrl;
    }
    TARGET_URL = inputUrl;

    const defaultFolderName = getDomain(TARGET_URL);
    const inputFolder = await rl.question(`Enter output folder name (Default: ${defaultFolderName}): `);
    const folderName = inputFolder.trim() || defaultFolderName;
    OUTPUT_DIR = path.join(__dirname, 'downloaded_site', folderName);

    if (fs.existsSync(OUTPUT_DIR)) {
        const files = fs.readdirSync(OUTPUT_DIR);
        if (files.length > 0) {
            const cleanConfirm = await rl.question(`\nWarning: The folder "${folderName}" already contains files.\nDo you want to empty this folder first? (yes/no, Default: no): `);
            if (cleanConfirm.toLowerCase().trim() === 'yes' || cleanConfirm.toLowerCase().trim() === 'y') {
                console.log(`Emptying folder: ${OUTPUT_DIR}...`);
                fs.rmSync(OUTPUT_DIR, { recursive: true, force: true });
            }
        }
    }

    rl.close();
    await downloadPage();
}

async function downloadPage() {
    let EVALUATE_HTML = true;

    const configPath = path.join(__dirname, 'config.json');

    if (fs.existsSync(configPath)) {
        try {
            configData = JSON.parse(fs.readFileSync(configPath, 'utf-8'));
            
            if (typeof configData.flattenAssets === 'boolean') FLATTEN_ASSETS = configData.flattenAssets;
            if (typeof configData.removeAllScripts === 'boolean') REMOVE_ALL_SCRIPTS = configData.removeAllScripts;
            if (typeof configData.removeAllIframes === 'boolean') REMOVE_ALL_IFRAMES = configData.removeAllIframes;
            if (typeof configData.removeNoscriptTags === 'boolean') REMOVE_NOSCRIPT_TAGS = configData.removeNoscriptTags;
            if (typeof configData.evaluateHTML === 'boolean') EVALUATE_HTML = configData.evaluateHTML;
            if (typeof configData.stripSrcsets === 'boolean') STRIP_SRCSETS = configData.stripSrcsets;

            if (configData.excludeScripts && Array.isArray(configData.excludeScripts)) {
                excludedPatterns = configData.excludeScripts.map(pattern => wildcardToRegex(pattern));
            }
            if (configData.ignoredSources && Array.isArray(configData.ignoredSources)) {
                ignoredPatterns = configData.ignoredSources.map(pattern => wildcardToRegex(pattern));
            }
            
            console.log(`[Config Loaded] Evaluate HTML: ${EVALUATE_HTML}, Flatten: ${FLATTEN_ASSETS}, Strip Scripts: ${REMOVE_ALL_SCRIPTS}, Strip iFrames: ${REMOVE_ALL_IFRAMES}, Strip NOSCRIPT tags: ${REMOVE_NOSCRIPT_TAGS}, Strip Srcsets: ${STRIP_SRCSETS}`);
        } catch (e) {
            console.error(`[Config Error] Could not read config.json: ${e.message}`);
        }
    }

    const browser = await puppeteer.launch({ headless: true });
    const page = await browser.newPage();
    await page.setViewport(VIEWPORTS[0]);

    const urlContentTypeMap = new Map();
    const savedCssFiles = new Set();

    await page.setRequestInterception(true);

    page.on('request', (request) => {
        const url = request.url();
        if (ignoredPatterns.some(regex => regex.test(url))) {
            request.abort();
            return;
        }
        request.continue();
    });

    page.on('response', async (response) => {
        const url = response.url();
        const status = response.status();
        const headers = response.headers();
        const contentType = headers['content-type'] || '';

        // Ignore data URIs, error codes, redirects, and no-body responses (304 Not Modified, 204 No Content)
        if (url.startsWith('data:') || status >= 400 || status === 302 || status === 304 || status === 204) return;

        try {
            const buffer = await response.buffer();

            // DO NOT write 0-byte files to disk
            if (!buffer || buffer.length === 0) return;

            urlContentTypeMap.set(cleanUrlKey(url), contentType);

            const localPath = urlToLocalPath(url, contentType);
            if (!localPath) return;

            fs.mkdirSync(path.dirname(localPath), { recursive: true });
            fs.writeFileSync(localPath, buffer);

            if (contentType.toLowerCase().includes('css') || url.split('?')[0].endsWith('.css')) {
                savedCssFiles.add({ localPath, originalUrl: url });
            }
        } catch (err) {}
    });

    console.log(`\nNavigating to ${TARGET_URL}...`);
    const initialResponse = await page.goto(TARGET_URL, { waitUntil: 'networkidle2', timeout: 60000 });

    let finalHtml;

    if (EVALUATE_HTML) {
        for (const vp of VIEWPORTS) {
            console.log(`\nEvaluating layout for ${vp.name} (${vp.width}x${vp.height})...`);
            await page.setViewport({ width: vp.width, height: vp.height, isMobile: vp.isMobile || false, hasTouch: vp.hasTouch || false });
            
            // NEW: Force the browser to drop native lazy loading so it downloads images instantly
            await page.evaluate(() => {
                document.querySelectorAll('img[loading="lazy"], iframe[loading="lazy"]').forEach(el => {
                    el.removeAttribute('loading');
                });
                window.scrollTo(0, 0);
            });
            
            await autoScroll(page);
            await new Promise(resolve => setTimeout(resolve, 1500));
        }

        await page.setViewport(VIEWPORTS[0]);
        await page.evaluate(() => window.scrollTo(0, 0));

        console.log("\nCapturing dynamic evaluated HTML...");
        finalHtml = await page.evaluate(() => {
            if (typeof document.documentElement.getHTML === 'function') return document.documentElement.getHTML({ includeShadowRoots: true });
            return document.documentElement.outerHTML;
        });
    } else {
        console.log("Capturing raw pure source HTML (pre-execution)...");
        finalHtml = await initialResponse.text();
    }
    
    const $ = cheerio.load(finalHtml);

    if ($('meta[charset]').length === 0) $('head').prepend('<meta charset="utf-8">');
    else $('meta[charset]').attr('charset', 'utf-8');

    if (REMOVE_ALL_SCRIPTS) {
        console.log("Purging ALL script tags from target HTML...");
        $('script').remove();
        $('*').each((i, el) => {
            for (const attr in el.attribs) {
                if (attr.startsWith('on')) $(el).removeAttr(attr);
            }
        });
    } else if (excludedPatterns.length > 0) {
        // 1. Remove standard static scripts that match the patterns (your existing code)
        $('script').each((index, element) => {
            const src = $(element).attr('src') || '';
            const inlineText = $(element).text() || '';
            if (excludedPatterns.some(regex => regex.test(src)) || excludedPatterns.some(regex => regex.test(inlineText))) {
                $(element).remove();
            }
        });

        // 2. INJECT THE DYNAMIC SCRIPT BLOCKER
        // We pass the raw string patterns from your config.json into the client-side script
        const rawExcludePatterns = configData.excludeScripts || [];
        
        const dynamicBlockerScript = `
        <script id="dynamic-script-blocker">
            (function() {
                const excludedPatterns = ${JSON.stringify(rawExcludePatterns)};
                
                function isBlocked(src) {
                    if (!src) return false;
                    return excludedPatterns.some(pattern => {
                        const regex = new RegExp(pattern.replace(/\\*/g, '.*'));
                        return regex.test(src);
                    });
                }

                // Intercept createElement to catch <script src="..."> assignments
                const originalCreateElement = document.createElement;
                document.createElement = function(tagName) {
                    const el = originalCreateElement.call(document, tagName);
                    if (tagName.toLowerCase() === 'script') {
                        Object.defineProperty(el, 'src', {
                            set: function(val) {
                                if (isBlocked(val)) {
                                    console.warn('[Scraper Blocker] Prevented dynamic script injection:', val);
                                    this.setAttribute('data-blocked-src', val); // Save it safely without executing
                                } else {
                                    this.setAttribute('src', val);
                                }
                            },
                            get: function() {
                                return this.getAttribute('src') || this.getAttribute('data-blocked-src') || '';
                            }
                        });
                    }
                    return el;
                };

                // Intercept appendChild
                const originalAppendChild = Node.prototype.appendChild;
                Node.prototype.appendChild = function(node) {
                    if (node.tagName === 'SCRIPT' && isBlocked(node.src || node.getAttribute('src'))) {
                        console.warn('[Scraper Blocker] Prevented appending script:', node.src || node.getAttribute('src'));
                        return node; // Return the node so the calling script doesn't crash, but don't attach it to the DOM
                    }
                    return originalAppendChild.call(this, node);
                };

                // Intercept insertBefore (many analytics scripts use this instead of appendChild)
                const originalInsertBefore = Node.prototype.insertBefore;
                Node.prototype.insertBefore = function(node, referenceNode) {
                    if (node.tagName === 'SCRIPT' && isBlocked(node.src || node.getAttribute('src'))) {
                        console.warn('[Scraper Blocker] Prevented inserting script:', node.src || node.getAttribute('src'));
                        return node; 
                    }
                    return originalInsertBefore.call(this, node, referenceNode);
                };
            })();
            const originalWrite = document.write;
            document.write = function(html) {
                if (typeof html === 'string') {
                    // Check if the HTML being written contains a blocked URL string
                    const isBlockedWrite = excludedPatterns.some(pattern => {
                        const regex = new RegExp(pattern.replace(/\\*/g, '.*'));
                        return regex.test(html);
                    });
                    
                    if (isBlockedWrite) {
                        console.warn('[Scraper Blocker] Prevented document.write from injecting blocked script:', html);
                        return; // Cancel the write entirely
                    }
                }
                return originalWrite.call(document, html);
            };
        </script>`;

        // Prepend ensures this runs absolutely first, before any other scripts on the page
        $('head').prepend(dynamicBlockerScript);
    }

    if (REMOVE_ALL_IFRAMES) {
        console.log("Purging ALL iframe elements from target HTML...");
        $('iframe').remove();
    }

   if (REMOVE_NOSCRIPT_TAGS) {
        console.log("Purging ALL NOSCRIPT elements from target HTML...");
        $('noscript').remove();
    }    

    // --- SRCSET PROCESSING ---
    if (STRIP_SRCSETS) {
        console.log("\nStripping responsive images (srcset)...");
        $('*[srcset]').removeAttr('srcset');
    } else {
        console.log("\nEvaluating and downloading responsive images (srcset)...");
        const srcsetElements = $('*[srcset]').toArray();
        
        for (const el of srcsetElements) {
            const element = $(el);
            const originalSrcset = element.attr('srcset');
            if (!originalSrcset) continue;

            const candidates = parseSrcset(originalSrcset);
            const newCandidates = [];

            for (const candidate of candidates) {
                const parts = candidate.split(/\s+/);
                const originalImgUrl = parts[0];
                const descriptor = parts.slice(1).join(' ');

                if (originalImgUrl.startsWith('data:')) {
                    newCandidates.push(candidate);
                    continue;
                }

                try {
                    const absoluteUrl = new URL(originalImgUrl, TARGET_URL).href;
                    if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) {
                        newCandidates.push(candidate);
                        continue;
                    }

                    const registryKey = cleanUrlKey(absoluteUrl);
                    let knownContentType = urlContentTypeMap.get(registryKey) || '';

                    if (!knownContentType) {
                        try {
                            const res = await fetch(absoluteUrl, {
                                headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36' }
                            });
                            if (res.ok) {
                                knownContentType = res.headers.get('content-type') || '';
                                urlContentTypeMap.set(registryKey, knownContentType);
                                
                                const buffer = Buffer.from(await res.arrayBuffer());
                                const localPath = urlToLocalPath(absoluteUrl, knownContentType);
                                if (localPath) {
                                    fs.mkdirSync(path.dirname(localPath), { recursive: true });
                                    fs.writeFileSync(localPath, buffer);
                                }
                            }
                        } catch (fetchErr) {}
                    }

                    const localRelativePath = getRelativeAssetPathForRoot(absoluteUrl, knownContentType);
                    newCandidates.push(descriptor ? `${localRelativePath} ${descriptor}` : localRelativePath);
                } catch (e) {
                    newCandidates.push(candidate);
                }
            }
            element.attr('srcset', newCandidates.join(', '));
        }
    }

    const resourcesToRewrite = [
        { selector: '*[src]', attr: 'src' },
        { selector: '*[href]', attr: 'href' }
    ];

    console.log("\n--- Running asset link processing (with manual fallback fetching) ---");
    // NEW: We changed this to an async for...of loop so Node can download missing standard images here too
    for (const { selector, attr } of resourcesToRewrite) {
        const elements = $(selector).toArray();
        for (const el of elements) {
            const element = $(el);
            let originalValue = element.attr(attr);
            if (!originalValue || originalValue.startsWith('data:')) continue;
            if (el.name === 'a') continue; // Don't download entire webpages linked via <a> tags
            if (attr === 'href' && (originalValue.startsWith('#') || originalValue.startsWith('javascript:'))) continue;

            try {
                const absoluteUrl = new URL(originalValue, TARGET_URL).href;
                if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) continue;

                const registryKey = cleanUrlKey(absoluteUrl);
                let knownContentType = urlContentTypeMap.get(registryKey) || '';

                // Helper headers for Node fetch to avoid anti-bot blocks returning empty bodies
                const FETCH_HEADERS = {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                    'Accept': '*/*',
                    'Accept-Language': 'en-US,en;q=0.9',
                    'Referer': TARGET_URL
                };

                // Inside your fetch loops:
                if (!knownContentType && ['img', 'source', 'link', 'script'].includes(el.name)) {
                    try {
                        const res = await fetch(absoluteUrl, { headers: FETCH_HEADERS });
                        if (res.ok) {
                            const buffer = Buffer.from(await res.arrayBuffer());

                            // Only save if content actually exists
                            if (buffer.length > 0) {
                                knownContentType = res.headers.get('content-type') || '';
                                urlContentTypeMap.set(registryKey, knownContentType);
                                
                                const localPath = urlToLocalPath(absoluteUrl, knownContentType);
                                if (localPath) {
                                    fs.mkdirSync(path.dirname(localPath), { recursive: true });
                                    fs.writeFileSync(localPath, buffer);
                                }
                            }
                        }
                    } catch (fetchErr) {}
                }

                const localRelativePath = getRelativeAssetPathForRoot(absoluteUrl, knownContentType);
                element.attr(attr, localRelativePath);
            } catch (e) {}
        }
    }

    console.log("\n--- Scanning inline scripts for hidden dynamic assets (e.g. document.write) ---");
        
    const inlineScripts = $('script:not([src])').toArray();
    for (const el of inlineScripts) {
        const element = $(el);
        let content = element.html() || '';
        let modified = false;
        
        // Regex to find src="..." or href="..." inside javascript strings
        // This handles escaped quotes (src=\") and standard quotes (src=")
        const regex = /(?:src|href)\s*=\s*(?:\\)*['"]([^'"]+?)(?:\\)*['"]/gi;
        const matches = [...content.matchAll(regex)];

        for (const match of matches) {
            const originalUrl = match[1];
            
            // Clean up escaped slashes (e.g., \/domain.com -> /domain.com)
            const cleanUrl = originalUrl.replace(/\\\//g, '/');

            // Ignore empty strings, data URIs, or inline JS
            if (!cleanUrl || cleanUrl.startsWith('data:') || cleanUrl.startsWith('#') || cleanUrl.startsWith('javascript:')) {
                continue;
            }

            try {
                const absoluteUrl = new URL(cleanUrl, TARGET_URL).href;
                if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) continue;

                const registryKey = cleanUrlKey(absoluteUrl);
                let knownContentType = urlContentTypeMap.get(registryKey) || '';

                // Fetch the asset if Puppeteer missed it
                if (!knownContentType) {
                    try {
                        const res = await fetch(absoluteUrl, { headers: { 'User-Agent': 'Mozilla/5.0' } });
                        if (res.ok) {
                            knownContentType = res.headers.get('content-type') || '';
                            urlContentTypeMap.set(registryKey, knownContentType);
                            
                            const buffer = Buffer.from(await res.arrayBuffer());
                            const localPath = urlToLocalPath(absoluteUrl, knownContentType);
                            if (localPath) {
                                fs.mkdirSync(path.dirname(localPath), { recursive: true });
                                fs.writeFileSync(localPath, buffer);
                            }
                        }
                    } catch (fetchErr) {
                        // Ignore obscure fetch errors
                    }
                }

                // Rewrite the URL string inside the JavaScript block
                const localRelativePath = getRelativeAssetPathForRoot(absoluteUrl, knownContentType);
                content = content.split(originalUrl).join(localRelativePath);
                modified = true;
            } catch (e) {
                // Invalid URL construction, skip it
            }
        }

        // Apply the updated JavaScript back to the script tag
        if (modified) {
            element.text(content);
        }
    }

    $('style').each((index, element) => {
        const originalCss = $(element).text();
        const updatedCss = rewriteCssUrls(originalCss, TARGET_URL);
        $(element).text(updatedCss);
    });

    $('[style]').each((index, element) => {
        const originalInlineStyle = $(element).attr('style');
        const updatedInlineStyle = rewriteCssUrls(originalInlineStyle, TARGET_URL);
        $(element).attr('style', updatedInlineStyle);
    });

    if (savedCssFiles.size > 0) {
        console.log(`\n--- Processing ${savedCssFiles.size} standalone CSS file(s) for asset links ---`);
        for (const cssFile of savedCssFiles) {
            if (fs.existsSync(cssFile.localPath)) {
                try {
                    const originalCssContent = fs.readFileSync(cssFile.localPath, 'utf-8');
                    const cssUrlRegex = /url\(['"]?([^'")]+)['"]?\)/g;
                    const updatedCssContent = originalCssContent.replace(cssUrlRegex, (match, originalUrl) => {
                        if (originalUrl.startsWith('data:')) return match;
                        try {
                            const absoluteUrl = new URL(originalUrl, cssFile.originalUrl).href;
                            if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) return match;

                            const localRelativePathToRoot = getRelativeAssetPathForRoot(absoluteUrl);
                            
                            if (FLATTEN_ASSETS) {
                                return `url("../${localRelativePathToRoot}")`;
                            } else {
                                const cssDir = path.dirname(cssFile.localPath);
                                const absoluteAssetPath = path.join(OUTPUT_DIR, localRelativePathToRoot);
                                let relativeToCss = path.relative(cssDir, absoluteAssetPath).replace(/\\/g, '/');
                                return `url("${relativeToCss}")`;
                            }
                        } catch (e) {
                            return match;
                        }
                    });

                    fs.writeFileSync(cssFile.localPath, updatedCssContent, 'utf-8');
                } catch (e) {
                    console.error(`[CSS Engine Error] Failed rewriting ${cssFile.localPath}: ${e.message}`);
                }
            }
        }
    }

    const optimizedHtml = $.html({ decodeEntities: false });

    console.log("\nSaving index.html layout file...");
    const rootHtmlPath = path.join(OUTPUT_DIR, 'index.html');
    fs.mkdirSync(OUTPUT_DIR, { recursive: true });
    fs.writeFileSync(rootHtmlPath, optimizedHtml, 'utf-8'); 

    if (!FLATTEN_ASSETS) {
        const targetDomainFolder = getDomain(TARGET_URL);
        const duplicateHtmlPath = path.join(OUTPUT_DIR, targetDomainFolder, 'index.html');
        if (fs.existsSync(duplicateHtmlPath)) {
            try { fs.unlinkSync(duplicateHtmlPath); } catch (e) {}
        }
    }

    await browser.close();
    function removeEmptyFiles(dir) {
        if (!fs.existsSync(dir)) return;
        const files = fs.readdirSync(dir);

        for (const file of files) {
            const filePath = path.join(dir, file);
            const stat = fs.statSync(filePath);

            if (stat.isDirectory()) {
                removeEmptyFiles(filePath);
            } else if (stat.size === 0) {
                console.warn(`[Cleanup] Removing 0-byte file: ${filePath}`);
                try { fs.unlinkSync(filePath); } catch (e) {}
            }
        }
    }

    // Call it right before browser.close():
    removeEmptyFiles(OUTPUT_DIR);
    console.log(`\n============================================\nFinished! Saved output path: ${rootHtmlPath}\n============================================`);
}
mainPrompts();