import puppeteer from 'puppeteer';
import fs from 'fs';
import path from 'path';
import { URL } from 'url';
import { fileURLToPath } from 'url';
import { dirname } from 'path';
import * as cheerio from 'cheerio';
import { log, askUrl, askText, askYesNo, createProgressBar, createPercentBar, createDownloadStatus, exitCleanly } from './terminal-ui.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

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
    'text/javascript': '.js',
    'font/woff': '.woff',
    'font/woff2': '.woff2',
    'font/ttf': '.ttf',
    'font/otf': '.otf',
    'application/font-woff': '.woff',
    'application/font-woff2': '.woff2',
    'application/x-font-ttf': '.ttf',
    'application/x-font-otf': '.otf',
    'application/vnd.ms-fontobject': '.eot'
};

const HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Accept': '*/*',
    'Accept-Language': 'en-US,en;q=0.9'
}

let VIEWPORTS = [
    { name: 'Desktop', width: 1280, height: 800, isMobile: false, use: true }
];

let TARGET_URL = ''; 
let OUTPUT_DIR = '';

let configData;
let FLATTEN_ASSETS = false;
let REMOVE_ALL_SCRIPTS = false;
let STRIP_SRCSETS = true;
let DISABLE_STRIPPED_ATTRIBUTES = false;
let COMMENT_STRIPPED_TAGS = false;
let COMBINE_ALL_STYLES = false;
let USE_SHADOW_ROOTS = false;
let REWRITE_JS_ASSET_URLS = true;
let WAIT_FOR_DYNAMIC_CONTENT = 5000; // Default wait time in ms
let ERROR_LOG_PATH = '';

let strippedTags = [];
let strippedAttributes = [];
let excludedScriptPatterns = [];
let ignoredPatterns = [];

let EMBED_STYLE_HEAD = false;
let EMBED_SCRIPT_HEAD = false;
let EMBED_SCRIPT_BODY_END = false;

const flatPathRegistry = new Map();

// Keeps one authoritative URL -> relative local path mapping.
// This mapping must be reused everywhere HTML/CSS references are rewritten.
const assetPathRegistry = new Map();

const downloadStats = {
    totalFiles: 0,
    downloaded: 0,
    failed: 0,
    skipped: 0,
    errors: [],
    missingFiles: new Set()
};

function cleanUrlKey(urlStr) {
    try {
        let normalized = urlStr;
        if (normalized.startsWith('//')) {
            normalized = 'https:' + normalized;
        } else if (!normalized.startsWith('http://') && !normalized.startsWith('https://')) {
            normalized = 'https://' + normalized;
        }

        const parsed = new URL(normalized);

        if (parsed.pathname.includes('/_next/image') && parsed.searchParams.has('url')) {
            return decodeURIComponent(parsed.searchParams.get('url')).toLowerCase().split('?')[0];
        }

        return decodeURIComponent(parsed.pathname).toLowerCase();
    } catch (e) {
        return decodeURIComponent(urlStr)
            .split('?')[0]
            .split('#')[0]
            .toLowerCase()
            .replace(/^\/\//, '');
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

function sanitizeFileName(filename) {
    if (!filename) return 'file';

    try {
        // Step 1: Fully decode percent-encoded characters (%20 -> space, etc.)
        filename = decodeURIComponent(filename);
    } catch (e) {
        // In case of malformed URI encoding, fallback to manual replacement
        filename = filename.replace(/%20/g, '_');
    }

    // Step 2: Replace spaces and problematic characters with clean underscores
    // Keeps alphanumeric characters, dots, dashes, and underscores intact
    return filename
        .replace(/\s+/g, '_')                    // Spaces -> underscores
        .replace(/[^a-zA-Z0-9.\-_]/g, '_')       // Remove illegal filename characters
        .replace(/_+/g, '_');                    // Collapse multiple consecutive underscores
}

function getFlatRelativePath(requestUrl, contentType = '') {
    const registryKey = cleanUrlKey(requestUrl);

    if (flatPathRegistry.has(registryKey)) {
        return flatPathRegistry.get(registryKey);
    }

    try {
        let absolute = requestUrl;
        if (absolute.startsWith('//')) {
            absolute = 'https:' + absolute;
        } else if (!/^https?:\/\//i.test(absolute)) {
            absolute = 'https://' + absolute;
        }

        const parsedUrl = new URL(absolute);
        let pathname = parsedUrl.pathname.split('?')[0];
        const mime = (contentType || '').toLowerCase();

        let subDir = 'assets';
        if (
            mime.startsWith('image/') ||
            mime.includes('svg') ||
            /\.(png|jpe?g|gif|svg|webp|avif|ico|bmp|tiff?)$/i.test(pathname)
        ) {
            subDir = 'images';
        } else if (
            mime.includes('font') ||
            mime.includes('woff') ||
            mime.includes('ttf') ||
            mime.includes('otf') ||
            /\.(woff2?|ttf|otf|eot)$/i.test(pathname)
        ) {
            subDir = 'fonts';
        } else if (mime.includes('css') || pathname.endsWith('.css')) {
            subDir = 'css';
        } else if (mime.includes('javascript') || pathname.endsWith('.js')) {
            subDir = 'js';
        } else if (/\.html?$/i.test(pathname)) {
            subDir = 'html';
        }

        let baseName = path.basename(pathname);
        if (!baseName || baseName === '/' || pathname.endsWith('/')) {
            baseName = 'index';
        }

        // --- NEW: Sanitize baseName ---
        let ext = path.extname(baseName);
        let nameWithoutExt = path.basename(baseName, ext);

        // Sanitize the base filename portion
        nameWithoutExt = sanitizeFileName(nameWithoutExt);

        if (!ext) {
            ext = MIME_TO_EXTENSION[mime] || '';
            if (!ext) {
                if (subDir === 'images') {
                    ext = mime.includes('svg') ? '.svg' : '.png';
                }
                else if (subDir === 'fonts') ext = '.woff2';
            }
        }
        
        // Reconstruct baseName clean
        baseName = nameWithoutExt + ext;
        // ------------------------------

        const relativePath = `${subDir}/${baseName}`;

        // Check if an existing URL key already mapped to this relativePath
        const existingPathKey = Array.from(flatPathRegistry.entries()).find(
            ([key, val]) => val === relativePath
        );

        if (existingPathKey) {
            // Map the current registryKey to the existing path to prevent appending hashes
            flatPathRegistry.set(registryKey, relativePath);
            return relativePath;
        }

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
                
        // --- NEW: Decode URI characters in the pathname ---
        try {
            pathname = decodeURIComponent(pathname);
        } catch (e) {}

        // Split pathname into segments, sanitize each segment, and rejoin
        const pathSegments = pathname.split('/').map(segment => {
            if (!segment) return segment;
            const ext = path.extname(segment);
            const name = path.basename(segment, ext);
            return sanitizeFileName(name) + ext;
        });
        pathname = pathSegments.join('/');
        // --------------------------------------------------

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
        } else if (isFontMime && path.extname(pathname) === '') {
            const ext = MIME_TO_EXTENSION[contentType.toLowerCase()] || '.woff2';
            if (parsedUrl.search) {
                const stableHash = getStableQueryHash(parsedUrl);
                pathname = pathname.replace(/\/$/, '');
                pathname += `/font_${stableHash}${ext}`;
            } else {
                if (pathname.endsWith('/')) pathname += `font${ext}`;
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

function getOrCreateAssetPath(assetUrl, contentType = '') {
    if (!assetUrl) {
        return assetUrl;
    }

    if (assetUrl.startsWith('//')) {
        assetUrl = 'https:' + assetUrl;
    }

    try {
        const normalizedUrl = new URL(assetUrl).href;
        const registryKey = cleanUrlKey(normalizedUrl);

        /*
         * If this URL was already assigned a path, ALWAYS use
         * the existing path.
         */
        if (assetPathRegistry.has(registryKey)) {
            return assetPathRegistry.get(registryKey);
        }

        const relativePath = getRelativeAssetPathForRoot(
            normalizedUrl,
            contentType
        );

        assetPathRegistry.set(
            registryKey,
            relativePath
        );

        return relativePath;

    } catch (e) {
        return assetUrl;
    }
}

async function autoScroll(page, label = 'Scrolling page') {
    const distance = 150;
    const maxHeight = 25000;
    const stepDelay = 256;
    let totalHeight = 0;

    const bar = createPercentBar(label);

    try {
        while (true) {
            const scrollHeight = await page.evaluate((d) => {
                window.scrollBy(0, d);
                return document.body.scrollHeight;
            }, distance);

            totalHeight += distance;
            const target = Math.min(scrollHeight, maxHeight) || 1;
            bar.update(totalHeight / target);

            if (totalHeight >= scrollHeight || totalHeight > maxHeight) break;

            await new Promise(resolve => setTimeout(resolve, stepDelay));
        }
    } finally {
        bar.update(1);
        bar.stop();
    }
}

function rewriteCssUrls(cssText, baseUrl) {
    const cssUrlRegex = /url\(['"]?([^'")]+)['"]?\)/g;

    return cssText.replace(
        cssUrlRegex,
        (match, originalUrl) => {

            if (originalUrl.startsWith('data:')) {
                return match;
            }

            try {
                const absoluteUrl =
                    new URL(originalUrl, baseUrl).href;

                if (
                    ignoredPatterns.some(
                        regex => regex.test(absoluteUrl)
                    )
                ) {
                    return match;
                }

                const localRelativePath =
                    getOrCreateAssetPath(absoluteUrl);

                return `url("${localRelativePath}")`;

            } catch (e) {
                return match;
            }
        }
    );
}

// Rewrites embedded asset references inside a downloaded standalone file (typically
// a .js bundle) so they point at the locally-downloaded copies instead of the
// original absolute/site-root URLs. Handles two shapes:
//   1. CSS-style url(...) references — common when a bundle injects <style> text
//      or inline style strings at runtime (e.g. background: url('/assets/x.svg')).
//   2. Bare quoted absolute-root paths ending in a known static-asset extension
//      (e.g. '/assets/icons/x.svg') — common when bundlers bake icon/image paths
//      straight into JS as plain string literals rather than inside url().
// `fileInfo` is { localPath, originalUrl } (the same shape used for savedCssFiles).
async function rewriteEmbeddedAssetUrls(fileInfo, urlContentTypeMap, { includeBareStringPaths = false } = {}) {

    try {
        let content = fs.readFileSync(fileInfo.localPath, 'utf-8');
        let changed = false;

        const patterns = [
            // url('...') / url("...") / url(...)
            { regex: /url\(\s*(['"]?)([^'")]+)\1\s*\)/g, urlGroup: 2, quoteGroup: 1, isUrlFn: true }
        ];

        if (includeBareStringPaths) {
            patterns.push({
                regex: /(['"])(\/[^'"\\]+?\.(?:svg|png|jpe?g|gif|webp|avif|ico|woff2?|ttf|otf|eot))\1/g,
                urlGroup: 2,
                quoteGroup: 1,
                isUrlFn: false
            });
        }

        for (const { regex, urlGroup, quoteGroup, isUrlFn } of patterns) {
            const matches = [...content.matchAll(regex)];
            if (!matches.length) continue;

            // Resolve replacements first (async work), keyed by the exact matched
            // text, then apply them in a single synchronous pass so every
            // occurrence (including duplicates) gets fixed correctly.
            const replacementMap = new Map();

            for (const match of matches) {
                const fullMatch = match[0];
                const originalUrl = match[urlGroup];
                const quote = match[quoteGroup] || '"';

                if (replacementMap.has(fullMatch)) continue;
                if (!originalUrl || originalUrl.startsWith('data:') || originalUrl.startsWith('#')) continue;

                try {
                    const absoluteUrl = new URL(originalUrl, fileInfo.originalUrl).href;

                    if (ignoredPatterns.some(p => p.test(absoluteUrl))) continue;

                    const registryKey = cleanUrlKey(absoluteUrl);
                    let knownContentType = urlContentTypeMap.get(registryKey) || '';

                    let localRelativePath = getOrCreateAssetPath(absoluteUrl, knownContentType);
                    let absoluteAssetPath = path.join(OUTPUT_DIR, localRelativePath);

                    if (!fs.existsSync(absoluteAssetPath)) {
                        const result = await safeDownload(absoluteUrl, absoluteAssetPath, knownContentType);
                        if (result.success) {
                            knownContentType = result.contentType || '';
                            urlContentTypeMap.set(registryKey, knownContentType);
                        }
                    }

                    localRelativePath = getOrCreateAssetPath(absoluteUrl, knownContentType);
                    absoluteAssetPath = path.join(OUTPUT_DIR, localRelativePath);

                    const fileDirectory = path.dirname(fileInfo.localPath);
                    let relativeToFile = path.relative(fileDirectory, absoluteAssetPath).replace(/\\/g, '/');
                    if (!relativeToFile.startsWith('.')) relativeToFile = './' + relativeToFile;

                    const replacement = isUrlFn
                        ? `url("${relativeToFile}")`
                        : `${quote}${relativeToFile}${quote}`;

                    replacementMap.set(fullMatch, replacement);
                } catch (e) {
                    log.error(`Embedded asset URL rewrite failed in ${fileInfo.localPath}: ${originalUrl} - ${e.message}`);
                }
            }

            if (replacementMap.size > 0) {
                content = content.replace(regex, (m) => replacementMap.has(m) ? replacementMap.get(m) : m);
                changed = true;
            }
        }

        if (changed) {
            fs.writeFileSync(fileInfo.localPath, content, 'utf-8');
        }
    } catch (e) {
        log.error(`Embedded asset processing error: ${fileInfo.localPath} - ${e.message}`);
    }
}


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

async function collectAllStylesAsHTML(page) {
    return await page.evaluate(() => {
        let allCSS = '';
        let styleCounter = 0;
        
        const styleTags = document.querySelectorAll('style');
        styleTags.forEach((style) => {
            const css = style.textContent;
            if (css.trim()) {
                allCSS += css + '\n\n';
                styleCounter++;
            }
        });
        
        function getUniqueSelector(element) {
            if (element.id) {
                return `#${element.id}`;
            }
            
            const path = [];
            let current = element;
            
            while (current && current !== document.body) {
                let selector = current.tagName.toLowerCase();
                
                const classAttr = current.getAttribute('class');
                if (classAttr && classAttr.trim()) {
                    const classes = classAttr.trim().split(/\s+/);
                    selector += '.' + classes.join('.');
                }
                
                if (current.parentElement) {
                    const siblings = Array.from(current.parentElement.children);
                    const index = siblings.indexOf(current) + 1;
                    selector += `:nth-child(${index})`;
                }
                
                path.unshift(selector);
                current = current.parentElement;
            }
            
            return path.join(' > ');
        }
        
        const allElements = document.querySelectorAll('*');
        const inlineStylesMap = new Map();
        
        allElements.forEach(el => {
            if (el.style.length > 0) {
                const selector = getUniqueSelector(el);
                const styles = {};
                for (let i = 0; i < el.style.length; i++) {
                    const prop = el.style[i];
                    const value = el.style.getPropertyValue(prop);
                    const priority = el.style.getPropertyPriority(prop);
                    styles[prop] = value + (priority ? ' !important' : '');
                }
                
                if (Object.keys(styles).length > 0) {
                    if (inlineStylesMap.has(selector)) {
                        const existing = inlineStylesMap.get(selector);
                        Object.assign(existing, styles);
                    } else {
                        inlineStylesMap.set(selector, styles);
                    }
                }
            }
        });
        
        for (const [selector, styles] of inlineStylesMap) {
            allCSS += `${selector} {\n`;
            for (const [prop, value] of Object.entries(styles)) {
                allCSS += `  ${prop}: ${value};\n`;
            }
            allCSS += '}\n\n';
        }
        
        const linkTags = document.querySelectorAll('link[rel="stylesheet"]');
        const fetchPromises = [];
        
        linkTags.forEach((link) => {
            const href = link.href;
            if (href && href.startsWith('http')) {
                fetchPromises.push(
                    fetch(href)
                        .then(response => response.text())
                        .then(css => {
                            allCSS += `/* External: ${href} */\n`;
                            allCSS += css + '\n\n';
                        })
                        .catch(() => {
                            allCSS += `/* Could not fetch: ${href} (CORS or network error) */\n\n`;
                        })
                );
            }
        });
        
        return Promise.all(fetchPromises).then(() => {
            const lines = allCSS.split('\n');
            const uniqueLines = [];
            const seenRules = new Set();
            
            for (const line of lines) {
                const trimmed = line.trim();
                if (trimmed && !trimmed.startsWith('/*')) {
                    if (trimmed.includes('{')) {
                        const ruleKey = trimmed;
                        if (!seenRules.has(ruleKey)) {
                            seenRules.add(ruleKey);
                            uniqueLines.push(line);
                        }
                    } else {
                        uniqueLines.push(line);
                    }
                } else {
                    uniqueLines.push(line);
                }
            }
            
            return uniqueLines.join('\n');
        });
    });
}

// Serializes the live DOM to a static HTML string, inlining declarative shadow
// roots (<template shadowrootmode="...">) and any adoptedStyleSheets (both
// per-shadow-root and document-level) as <style> tags. This runs entirely
// inside the page context via page.evaluate, so it must be self-contained.
async function captureHTMLWithShadowRoots(page) {
    return await page.evaluate(() => {
        // Helper function to extract CSS from adoptedStyleSheets, including sheet-level media queries
        function extractAdoptedStyleSheets(sheets) {
            if (!sheets || !sheets.length) return '';
            let cssText = '';
            for (const sheet of sheets) {
                try {
                    let sheetRules = Array.from(sheet.cssRules).map(rule => rule.cssText).join('\n');

                    // Preserve sheet-level media conditions (e.g. new CSSStyleSheet({ media: "(max-width: 768px)" }))
                    const mediaText = sheet.media && sheet.media.mediaText;
                    if (mediaText) {
                        sheetRules = `@media ${mediaText} {\n${sheetRules}\n}`;
                    }

                    cssText += sheetRules + '\n';
                } catch (e) {
                    console.warn('Could not read cssRules from adopted sheet:', e);
                }
            }
            return cssText;
        }

        function serializeNode(node) {
            // 1. Text Nodes
            if (node.nodeType === Node.TEXT_NODE) {
                return node.textContent
                    .replace(/&/g, '&amp;')
                    .replace(/</g, '&lt;')
                    .replace(/>/g, '&gt;');
            }

            // 2. Comment Nodes
            if (node.nodeType === Node.COMMENT_NODE) {
                return `<!--${node.nodeValue}-->`;
            }

            // Skip non-element nodes
            if (node.nodeType !== Node.ELEMENT_NODE) return '';

            const tagName = node.tagName.toLowerCase();

            // Remove <script> tags entirely
            if (tagName === 'script') return '';

            // Build element attributes
            let attrs = '';
            for (const attr of node.attributes) {
                attrs += ` ${attr.name}="${attr.value.replace(/"/g, '&quot;')}"`;
            }

            // Handle HTML Void (self-closing) elements
            const voidTags = new Set([
                'area', 'base', 'br', 'col', 'embed', 'hr', 'img',
                'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'
            ]);
            if (voidTags.has(tagName)) {
                return `<${tagName}${attrs}>`;
            }

            let innerContent = '';

            // 3. Process Shadow Root (Declarative Shadow DOM + Adopted Stylesheets)
            if (node.shadowRoot) {
                const shadowCSS = extractAdoptedStyleSheets(node.shadowRoot.adoptedStyleSheets);

                let shadowDOMContent = '';
                if (shadowCSS) {
                    shadowDOMContent += `<style>\n${shadowCSS}\n</style>\n`;
                }

                for (const child of node.shadowRoot.childNodes) {
                    shadowDOMContent += serializeNode(child);
                }

                const mode = node.shadowRoot.mode || 'open';
                innerContent += `<template shadowrootmode="${mode}">\n${shadowDOMContent}\n</template>\n`;
            }

            // 4. Process global Document-level adoptedStyleSheets inside <head>
            if (tagName === 'head' && document.adoptedStyleSheets?.length) {
                const globalCSS = extractAdoptedStyleSheets(document.adoptedStyleSheets);
                if (globalCSS) {
                    innerContent += `<style>\n${globalCSS}\n</style>\n`;
                }
            }

            // 5. Process Light DOM child nodes
            for (const child of node.childNodes) {
                innerContent += serializeNode(child);
            }

            return `<${tagName}${attrs}>${innerContent}</${tagName}>`;
        }

        return '<!DOCTYPE html>\n' + serializeNode(document.documentElement);
    });
}

async function downloadWithRetry(url, options = {}, maxRetries = 2) {
    for (let attempt = 1; attempt <= maxRetries; attempt++) {
        try {
            const response = await fetch(url, {
                ...options,
                headers: {
                    ...HEADERS,
                    'Referer': TARGET_URL,
                    ...options.headers
                }
            });
            
            if (!response.ok) {
                throw new Error(`HTTP ${response.status}: ${response.statusText}`);
            }
            
            const buffer = Buffer.from(await response.arrayBuffer());
            const contentType = response.headers.get('content-type') || '';
            
            return { buffer, contentType, status: response.status };
        } catch (error) {
            if (attempt === maxRetries) {
                throw error;
            }
            await new Promise(resolve => setTimeout(resolve, 1000 * attempt));
        }
    }
}

let downloadStatus = null;

function getDownloadStatus() {
    if (!downloadStatus) downloadStatus = createDownloadStatus();
    return downloadStatus;
}

async function safeDownload(url, localPath, contentType = '') {
    downloadStats.totalFiles++;
    getDownloadStatus().update(downloadStats);

    try {
        if (ignoredPatterns.some(regex => regex.test(url))) {
            downloadStats.skipped++;
            getDownloadStatus().update(downloadStats);
            return {
                success: false,
                reason: 'ignored'
            };
        }

        const result = await downloadWithRetry(url);

        if (result.buffer && result.buffer.length > 0) {
            if (localPath) {
                fs.mkdirSync(
                    path.dirname(localPath),
                    { recursive: true }
                );

                fs.writeFileSync(
                    localPath,
                    result.buffer
                );
            }

            downloadStats.downloaded++;
            getDownloadStatus().update(downloadStats);

            return {
                success: true,
                contentType: result.contentType
            };
        }

        throw new Error('Empty response');

    } catch (error) {
        downloadStats.failed++;
        getDownloadStatus().update(downloadStats);

        const errorMsg =
            `[${error.status || 'ERROR'}] ${url} -> ${error.message}`;

        // Save error internally, but DON'T print it to console.
        downloadStats.errors.push(errorMsg);
        downloadStats.missingFiles.add(url);

        return {
            success: false,
            error: error.message
        };
    }
}

// Simplified wait for dynamic content - just wait for network idle and stability
async function waitForDynamicContent(page, timeout = 10000) {
    log.info(`Waiting ${timeout/1000}s for dynamic content to load...`);
    
    const startTime = Date.now();
    let lastHTML = '';
    let stableChecks = 0;
    const requiredStableChecks = 3;
    const checkInterval = 500; // Check every 500ms
    
    // First, wait for any pending network requests to complete
    await page.waitForNetworkIdle({ 
        idleTime: 2000, 
        timeout: timeout 
    }).catch(() => {
        log.info(`Network idle timeout reached, continuing...`);
    });
    
    // Then wait for the DOM to become stable (not changing)
    while (Date.now() - startTime < timeout) {
        const currentHTML = await page.evaluate(() => document.documentElement.outerHTML);
        
        if (currentHTML === lastHTML) {
            stableChecks++;
        } else {
            stableChecks = 0;
            lastHTML = currentHTML;
        }
        
        // If HTML is stable for required checks, break
        if (stableChecks >= requiredStableChecks) {
            log.success(`Page HTML stable after ${Math.round((Date.now() - startTime)/1000)}s`);
            break;
        }
        
        await new Promise(resolve => setTimeout(resolve, checkInterval));
    }
    
    // Additional wait for any lazy-loaded content to appear
    {
        const maxScrolls = 3;
        let lastHeight = await page.evaluate(() => document.body.scrollHeight);
        const bar = createProgressBar('Triggering lazy-load scroll', maxScrolls);

        for (let i = 0; i < maxScrolls; i++) {
            await page.evaluate(() => window.scrollBy(0, 500));
            await new Promise(resolve => setTimeout(resolve, 300));

            const newHeight = await page.evaluate(() => document.body.scrollHeight);
            bar.step(`pass ${i + 1}/${maxScrolls}`);

            if (newHeight === lastHeight) break;
            lastHeight = newHeight;
        }

        await page.evaluate(() => window.scrollTo(0, 0));
        bar.stop();
    }
    
    // Final small delay for any post-scroll rendering
    await new Promise(resolve => setTimeout(resolve, 1000));
    
    log.info(`Total wait time: ${Math.round((Date.now() - startTime)/1000)}s`);
}

async function mainPrompts() {
    log.title('Website Downloader');

    TARGET_URL = await askUrl('Enter website URL: ');

    const defaultFolderName = getDomain(TARGET_URL);
    const folderName = (await askText('Enter output folder name: ', defaultFolderName)) || defaultFolderName;
    OUTPUT_DIR = path.join(__dirname, 'downloaded_site', folderName);
    ERROR_LOG_PATH = path.join(OUTPUT_DIR, 'errorlog.txt');

    if (fs.existsSync(OUTPUT_DIR)) {
        const files = fs.readdirSync(OUTPUT_DIR);
        if (files.length > 0) {
            const shouldEmpty = await askYesNo(
                `Warning: the folder "${folderName}" already contains files. Empty it first?`,
                false
            );
            if (shouldEmpty) {
                log.info(`Emptying folder: ${OUTPUT_DIR}...`);
                fs.rmSync(OUTPUT_DIR, { recursive: true, force: true });
            }
        }
    }

    await downloadPage();
}


function writeErrorLog() {
    if (!ERROR_LOG_PATH) {
        return;
    }

    try {
        fs.mkdirSync(
            path.dirname(ERROR_LOG_PATH),
            { recursive: true }
        );

        if (downloadStats.errors.length === 0) {
            // Remove an old error log if this download had no errors.
            if (fs.existsSync(ERROR_LOG_PATH)) {
                fs.unlinkSync(ERROR_LOG_PATH);
            }

            return;
        }

        const lines = [];

        lines.push(
            '============================================'
        );
        lines.push('DOWNLOAD ERROR LOG');
        lines.push(
            '============================================'
        );
        lines.push('');

        lines.push(
            `Generated: ${new Date().toISOString()}`
        );

        lines.push(
            `Target: ${TARGET_URL}`
        );

        lines.push(
            `Failed downloads: ${downloadStats.errors.length}`
        );

        lines.push('');

        for (const error of downloadStats.errors) {
            lines.push(error);
        }

        lines.push('');
        lines.push(
            '============================================'
        );

        fs.writeFileSync(
            ERROR_LOG_PATH,
            lines.join('\n'),
            'utf-8'
        );

        log.info(
            `${downloadStats.errors.length} download errors saved to: ${ERROR_LOG_PATH}`
        );

    } catch (error) {
        log.error(
            `Could not write errorlog.txt: ${error.message}`
        );
    }
}

async function downloadPage() {
    let EVALUATE_HTML = true;

    const configPath = path.join(__dirname, 'config.json');

    if (fs.existsSync(configPath)) {
        try {
            configData = JSON.parse(fs.readFileSync(configPath, 'utf-8'));
            
            if (configData.useViewports && Array.isArray(configData.useViewports)) {
                VIEWPORTS = configData.useViewports;
            }
            if (typeof configData.flattenAssets === 'boolean') FLATTEN_ASSETS = configData.flattenAssets;
            if (typeof configData.removeAllScripts === 'boolean') REMOVE_ALL_SCRIPTS = configData.removeAllScripts;
            if (typeof configData.evaluateHTML === 'boolean') EVALUATE_HTML = configData.evaluateHTML;
            if (typeof configData.commentStrippedTags === 'boolean') COMMENT_STRIPPED_TAGS = configData.commentStrippedTags;
            if (configData.strippedTags && Array.isArray(configData.strippedTags)) {
                strippedTags = configData.strippedTags;
            }
            if (typeof configData.disableStrippedAttributes === 'boolean') DISABLE_STRIPPED_ATTRIBUTES = configData.disableStrippedAttributes;                  
            if (configData.strippedAttributes && Array.isArray(configData.strippedAttributes)) {
                strippedAttributes = configData.strippedAttributes;
            }            
            if (strippedAttributes.includes("srcset")) STRIP_SRCSETS = true;
            if (typeof configData.combineAllStyles === 'boolean') COMBINE_ALL_STYLES = configData.combineAllStyles;
            if (typeof configData.useShadowRoots === 'boolean') USE_SHADOW_ROOTS = configData.useShadowRoots;
            if (typeof configData.rewriteAssetUrlsInJs === 'boolean') REWRITE_JS_ASSET_URLS = configData.rewriteAssetUrlsInJs;
            if (configData.waitForDynamicContent) {
                WAIT_FOR_DYNAMIC_CONTENT = configData.waitForDynamicContent;
            }

            if (configData.excludeScripts && Array.isArray(configData.excludeScripts)) {
                excludedScriptPatterns = configData.excludeScripts.map(pattern => wildcardToRegex(pattern));
            }
            if (configData.ignoredSources && Array.isArray(configData.ignoredSources)) {
                ignoredPatterns = configData.ignoredSources.map(pattern => wildcardToRegex(pattern));
            }

            if (configData.embedStyleHead) EMBED_STYLE_HEAD = configData.embedStyleHead;
            if (configData.embedScriptHead) EMBED_SCRIPT_HEAD = configData.embedScriptHead;
            if (configData.embedScriptBodyEnd) EMBED_SCRIPT_BODY_END = configData.embedScriptBodyEnd;
            
            log.info(`[Config Loaded] Evaluate HTML: ${EVALUATE_HTML}, Flatten: ${FLATTEN_ASSETS}, Strip Scripts: ${REMOVE_ALL_SCRIPTS}, Combine Styles: ${COMBINE_ALL_STYLES}, Shadow Roots: ${USE_SHADOW_ROOTS}, Rewrite JS Asset URLs: ${REWRITE_JS_ASSET_URLS}, Wait Time: ${WAIT_FOR_DYNAMIC_CONTENT}ms`);
        } catch (e) {
            log.error(`[Config Error] Could not read config.json: ${e.message}`);
        }
    }

    const browser = await puppeteer.launch({ 
        headless: true,
        args: [
            '--no-sandbox',
            '--disable-setuid-sandbox',
            '--disable-dev-shm-usage',
            '--disable-accelerated-2d-canvas',
            '--disable-gpu'
        ]
    });
    const page = await browser.newPage();
    await page.setViewport(VIEWPORTS[0]);

    const urlContentTypeMap = new Map();
    const savedCssFiles = new Set();
    const savedJsFiles = new Set();

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

        if (url.startsWith('data:') || status >= 400 || status === 302 || status === 304 || status === 204) {
            if (status >= 400) {
                const isFont = url.match(/\.(woff2?|ttf|otf|eot)$/i) || 
                              (contentType && contentType.match(/font|woff|ttf|otf/));
                if (isFont) {
                    log.warn(`Font ${status}: ${url}`);
                }
                downloadStats.missingFiles.add(url);
            }
            return;
        }

        try {
            const buffer = await response.buffer();

            if (!buffer || buffer.length === 0) {
                downloadStats.missingFiles.add(url);
                return;
            }

            urlContentTypeMap.set(cleanUrlKey(url), contentType);

            const localPath = urlToLocalPath(url, contentType);
            if (!localPath) return;

            const result = await safeDownload(url, localPath, contentType);
            
            if (result.success && (contentType.toLowerCase().includes('css') || url.split('?')[0].endsWith('.css'))) {
                savedCssFiles.add({ localPath, originalUrl: url });
            }
            if (result.success && (contentType.toLowerCase().includes('javascript') || /\.js$/i.test(url.split('?')[0]))) {
                savedJsFiles.add({ localPath, originalUrl: url });
            }
        } catch (err) {
            // log.warn(`Download error: ${url} - ${err.message}`);
            downloadStats.missingFiles.add(url);
        }
    });

    log.info(`\nNavigating to ${TARGET_URL}...`);
    const initialResponse = await page.goto(TARGET_URL, { 
        waitUntil: 'networkidle2', 
        timeout: 60000 
    });

    let finalHtml;

    if (EVALUATE_HTML) {
        // Wait for dynamic content to load
        await waitForDynamicContent(page, WAIT_FOR_DYNAMIC_CONTENT);
        
        // Now evaluate different viewports
        for (const vp of VIEWPORTS) {
            if (!vp.use) continue;
            log.info(`\nEvaluating layout for ${vp.name} (${vp.width}x${vp.height})...`);
            await page.setViewport({ 
                width: vp.width, 
                height: vp.height, 
                isMobile: vp.isMobile || false, 
                hasTouch: vp.hasTouch || false 
            });
            
            // Remove lazy loading attributes
            await page.evaluate(() => {
                document.querySelectorAll('img[loading="lazy"], iframe[loading="lazy"]').forEach(el => {
                    el.removeAttribute('loading');
                });
                window.scrollTo(0, 0);
            });
            
            // Scroll to load lazy content
            await autoScroll(page, `Scrolling layout (${vp.name})`);
            
            // Wait a bit for layout to settle
            await new Promise(resolve => setTimeout(resolve, 1000));
        }

        // Return to desktop viewport
        await page.setViewport(VIEWPORTS[0]);
        await page.evaluate(() => window.scrollTo(0, 0));

        log.info("\nCapturing fully evaluated HTML...");
        
        // One final check for stability
        await page.evaluate(() => {
            return new Promise((resolve) => {
                // Check if there are any pending network requests
                if (window.performance && window.performance.getEntriesByType) {
                    const pendingRequests = window.performance.getEntriesByType('resource')
                        .filter(entry => !entry.responseEnd);
                    if (pendingRequests.length === 0) {
                        resolve();
                        return;
                    }
                }
                // Give it a final moment
                setTimeout(resolve, 1000);
            });
        });
        
        // Capture the final HTML with all dynamic content
        if (USE_SHADOW_ROOTS) {
            log.info("Capturing HTML with shadow roots + adopted stylesheets inlined...");
            finalHtml = await captureHTMLWithShadowRoots(page);
        } else {
            finalHtml = await page.evaluate(() => {
                return document.documentElement.outerHTML;
            });
        }

    } else {
        if (USE_SHADOW_ROOTS) {
            // Shadow roots only exist on the live, JS-executed page, so even when
            // EVALUATE_HTML is off we still need to pull the HTML from the page
            // context (rather than the raw pre-execution response body) to see them.
            log.info("Capturing HTML with shadow roots + adopted stylesheets inlined (pre full evaluation)...");
            finalHtml = await captureHTMLWithShadowRoots(page);
        } else {
            log.info("Capturing raw source HTML (pre-execution)...");
            finalHtml = await initialResponse.text();
        }
    }


    let rawCombinedCss = '';
        if (COMBINE_ALL_STYLES) {
            log.info("\nCombining all page styles into a single stylesheet...");
            try {
                rawCombinedCss = await collectAllStylesAsHTML(page);
            } catch (err) {
                log.error(`Failed to collect page styles: ${err.message}`);
            }
        }

    
    const $ = cheerio.load(finalHtml, {
        // Preserve the original HTML structure
        xmlMode: false,
        decodeEntities: false
    });

    if ($('meta[charset]').length === 0) $('head').prepend('<meta charset="utf-8">');
    else $('meta[charset]').attr('charset', 'utf-8');


    if (COMBINE_ALL_STYLES) {
            log.section("Processing and saving combined-styles.css");

            // Step 1: Strip existing style tags and external stylesheet link tags
            // (but leave <style> tags that live inside a declarative shadow root's
            // <template shadowrootmode="..."> alone — those are scoped to that
            // shadow tree and combining them into the global stylesheet would
            // both break their encapsulation and remove them from the shadow DOM.)
            $('style').each((i, el) => {
                if ($(el).closest('template[shadowrootmode]').length === 0) {
                    $(el).remove();
                }
            });
            $('link[rel="stylesheet"]').each((i, el) => {
                if ($(el).closest('template[shadowrootmode]').length === 0) {
                    $(el).remove();
                }
            });

            // Step 2: Process url() references in the collected CSS and download assets
            if (rawCombinedCss) {
                let processedCss = rawCombinedCss;
                const cssUrlRegex = /url\(\s*['"]?([^'")]+)['"]?\s*\)/g;
                const matches = [...rawCombinedCss.matchAll(cssUrlRegex)];

                for (const match of matches) {
                    const originalUrl = match[1];

                    if (!originalUrl || originalUrl.startsWith('data:') || originalUrl.startsWith('#')) {
                        continue;
                    }

                    try {
                        const absoluteUrl = new URL(originalUrl, TARGET_URL).href;

                        if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) {
                            continue;
                        }

                        const registryKey = cleanUrlKey(absoluteUrl);
                        let knownContentType = urlContentTypeMap.get(registryKey) || '';

                        let localRelativePath = getOrCreateAssetPath(absoluteUrl, knownContentType);
                        let absoluteAssetPath = path.join(OUTPUT_DIR, localRelativePath);

                        // Download asset if not already downloaded
                        if (!fs.existsSync(absoluteAssetPath)) {
                            const result = await safeDownload(absoluteUrl, absoluteAssetPath, knownContentType);
                            if (result.success) {
                                knownContentType = result.contentType || '';
                                urlContentTypeMap.set(registryKey, knownContentType);
                            }
                        }

                        localRelativePath = getOrCreateAssetPath(absoluteUrl, knownContentType);
                        absoluteAssetPath = path.join(OUTPUT_DIR, localRelativePath);

                        // Calculate path relative to /css/ combined-styles.css
                        const cssDirectory = path.join(OUTPUT_DIR, 'css');
                        let relativeToCss = path.relative(cssDirectory, absoluteAssetPath).replace(/\\/g, '/');

                        if (!relativeToCss.startsWith('.')) {
                            relativeToCss = './' + relativeToCss;
                        }

                        processedCss = processedCss.replace(match[0], `url("${relativeToCss}")`);

                    } catch (e) {
                        log.error(`Combined CSS URL error: ${originalUrl} - ${e.message}`);
                    }
                }

                // Step 3: Write to css/combined-styles.css
                const combinedCssPath = path.join(OUTPUT_DIR, 'css', 'combined-styles.css');
                fs.mkdirSync(path.dirname(combinedCssPath), { recursive: true });
                fs.writeFileSync(combinedCssPath, processedCss, 'utf-8');
            }

            // Step 4: Inject the link to index.html
            $('head').append('<link rel="stylesheet" href="css/combined-styles.css">');

        } else {
            $('style').each((index, element) => {
                const originalCss = $(element).text();
                const updatedCss = rewriteCssUrls(
                    originalCss,
                    TARGET_URL
                );
                $(element).text(updatedCss);
            });

            $('[style]').each((index, element) => {
                const originalInlineStyle = $(element).attr('style');

                if (!originalInlineStyle) return;

                const updatedInlineStyle =
                    rewriteCssUrls(
                        originalInlineStyle,
                        TARGET_URL
                    );

                $(element).attr(
                    'style',
                    updatedInlineStyle
                );
            });

            if (savedCssFiles.size > 0) {
                log.section(`Processing ${savedCssFiles.size} standalone CSS file(s) for asset links`);
                const cssBar = createProgressBar('CSS files', savedCssFiles.size);

                for (const cssFile of savedCssFiles) {

                    if (!fs.existsSync(cssFile.localPath)) {
                        cssBar.step(path.basename(cssFile.localPath));
                        continue;
                    }

                    cssBar.step(path.basename(cssFile.localPath));


                    try {
                        let cssContent = fs.readFileSync(
                            cssFile.localPath,
                            'utf-8'
                        );

                        const cssUrlRegex =
                            /url\(\s*['"]?([^'")]+)['"]?\s*\)/g;

                        const matches = [
                            ...cssContent.matchAll(cssUrlRegex)
                        ];

                        for (const match of matches) {
                            const originalUrl = match[1];

                            if (
                                !originalUrl ||
                                originalUrl.startsWith('data:') ||
                                originalUrl.startsWith('#')
                            ) {
                                continue;
                            }

                            try {
                                /*
                                 * Resolve CSS URLs against the ORIGINAL remote CSS URL.
                                 */
                                const absoluteUrl =
                                    new URL(
                                        originalUrl,
                                        cssFile.originalUrl
                                    ).href;

                                if (
                                    ignoredPatterns.some(
                                        regex => regex.test(absoluteUrl)
                                    )
                                ) {
                                    continue;
                                }

                                const registryKey =
                                    cleanUrlKey(absoluteUrl);

                                let knownContentType =
                                    urlContentTypeMap.get(
                                        registryKey
                                    ) || '';

                                /*
                                 * Get the ONE canonical filename.
                                 */
                                let localRelativePath =
                                    getOrCreateAssetPath(
                                        absoluteUrl,
                                        knownContentType
                                    );

                                let absoluteAssetPath =
                                    path.join(
                                        OUTPUT_DIR,
                                        localRelativePath
                                    );

                                /*
                                 * If the asset isn't already downloaded,
                                 * download it using the SAME canonical path.
                                 */
                                if (!fs.existsSync(absoluteAssetPath)) {
                                    const result =
                                        await safeDownload(
                                            absoluteUrl,
                                            absoluteAssetPath,
                                            knownContentType
                                        );

                                    if (result.success) {
                                        knownContentType =
                                            result.contentType || '';

                                        urlContentTypeMap.set(
                                            registryKey,
                                            knownContentType
                                        );

                                        /*
                                         * Content type may tell us a better extension.
                                         * But do NOT generate a second filename here.
                                         */
                                    }
                                }

                                /*
                                 * Re-read the canonical mapping.
                                 */
                                localRelativePath =
                                    getOrCreateAssetPath(
                                        absoluteUrl,
                                        knownContentType
                                    );

                                absoluteAssetPath =
                                    path.join(
                                        OUTPUT_DIR,
                                        localRelativePath
                                    );

                                /*
                                 * Calculate path relative to the CSS file.
                                 */
                                const cssDirectory =
                                    path.dirname(
                                        cssFile.localPath
                                    );

                                let relativeToCss =
                                    path.relative(
                                        cssDirectory,
                                        absoluteAssetPath
                                    ).replace(/\\/g, '/');

                                if (
                                    !relativeToCss.startsWith('.')
                                ) {
                                    relativeToCss =
                                        './' + relativeToCss;
                                }

                                const replacement =
                                    `url("${relativeToCss}")`;

                                /*
                                 * Replace exactly this occurrence.
                                 */
                                cssContent =
                                    cssContent.replace(
                                        match[0],
                                        replacement
                                    );

                            } catch (e) {
                                log.error(
                                    `CSS URL processing failed: ${originalUrl} - ${e.message}`
                                );
                            }
                        }

                        fs.writeFileSync(
                            cssFile.localPath,
                            cssContent,
                            'utf-8'
                        );

                    } catch (e) {
                        log.error(
                            `CSS processing error: ${cssFile.localPath} - ${e.message}`
                        );
                    }
                }
                cssBar.stop();
            }
        }

    // Fix up hardcoded absolute/site-root asset paths baked into downloaded JS
    // bundles (e.g. CSS-in-JS strings like background: url('/assets/x.svg')).
    // These live outside any <style>/<link> tag cheerio can see, so they need
    // their own pass regardless of whether COMBINE_ALL_STYLES is on.
    if (REWRITE_JS_ASSET_URLS && savedJsFiles.size > 0) {
        log.section(`Processing ${savedJsFiles.size} standalone JS file(s) for embedded asset links`);
        const jsBar = createProgressBar('JS files', savedJsFiles.size);
        for (const jsFile of savedJsFiles) {
            if (!fs.existsSync(jsFile.localPath)) return;

            jsBar.step(path.basename(jsFile.localPath));
            await rewriteEmbeddedAssetUrls(jsFile, urlContentTypeMap, { includeBareStringPaths: true });
        }
        jsBar.stop();
    }

    if (REMOVE_ALL_SCRIPTS) {
        log.info("\nPurging ALL script tags from target HTML...");
        $('script').remove();
        $('*').each((i, el) => {
            for (const attr in el.attribs) {
                if (attr.startsWith('on')) $(el).removeAttr(attr);
            }
        });
    } else if (excludedScriptPatterns.length > 0) {
        $('script').each((index, element) => {
            const src = $(element).attr('src') || '';
            const inlineText = $(element).text() || '';
            if (excludedScriptPatterns.some(regex => regex.test(src)) || excludedScriptPatterns.some(regex => regex.test(inlineText))) {
                $(element).remove();
            }
        });

        const rawExcludePatterns = configData.excludeScripts || [];
        
        const dynamicBlockerScript = `
        <script id="dynamic-script-blocker">
            (function() {
                const excludedScriptPatterns = ${JSON.stringify(rawExcludePatterns)};
                function isBlocked(src) {
                    if (!src) return false;
                    return excludedScriptPatterns.some(pattern => {
                        const regex = new RegExp(pattern.replace(/\\*/g, '.*'));
                        return regex.test(src);
                    });
                }

                const originalCreateElement = document.createElement;
                document.createElement = function(tagName) {
                    const el = originalCreateElement.call(document, tagName);
                    if (tagName.toLowerCase() === 'script') {
                        Object.defineProperty(el, 'src', {
                            set: function(val) {
                                if (isBlocked(val)) {
                                    console.warn('[Scraper Blocker] Prevented dynamic script injection:', val);
                                    this.setAttribute('data-blocked-src', val);
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

                const originalAppendChild = Node.prototype.appendChild;
                Node.prototype.appendChild = function(node) {
                    if (node.tagName === 'SCRIPT' && isBlocked(node.src || node.getAttribute('src'))) {
                        console.warn('[Scraper Blocker] Prevented appending script:', node.src || node.getAttribute('src'));
                        return node;
                    }
                    return originalAppendChild.call(this, node);
                };

                const originalInsertBefore = Node.prototype.insertBefore;
                Node.prototype.insertBefore = function(node, referenceNode) {
                    if (node.tagName === 'SCRIPT' && isBlocked(node.src || node.getAttribute('src'))) {
                        console.warn('[Scraper Blocker] Prevented inserting script:', node.src || node.getAttribute('src'));
                        return node; 
                    }
                    return originalInsertBefore.call(this, node, referenceNode);
                };
                const originalWrite = document.write;
                document.write = function(html) {
                    if (typeof html === 'string') {
                        const isBlockedWrite = excludedScriptPatterns.some(pattern => {
                            const regex = new RegExp(pattern.replace(/\\*/g, '.*'));
                            return regex.test(html);
                        });
                        
                        if (isBlockedWrite) {
                            console.warn('[Scraper Blocker] Prevented document.write from injecting blocked script:', html);
                            return;
                        }
                    }
                    return originalWrite.call(document, html);
                };
            })();
        </script>`;

        $('head').prepend(dynamicBlockerScript);
    }

    log.info("\nStripping tags: " + strippedTags.join(", ") + (COMMENT_STRIPPED_TAGS ? ' (comment mode) ' : ''));
    for(const tag of strippedTags) {
        if (COMMENT_STRIPPED_TAGS) {
            // Comment out the tag instead of removing it
            $(`${tag}`).each(function() {
                const $el = $(this);
                const outerHtml = $el.prop('outerHTML');
                // Replace with HTML comment
                $el.replaceWith(`<!-- ${outerHtml} -->`);
            });
        } else {
            // Remove tags normally
            $(`${tag}`).remove();
        }
    }

    log.info("\nStripping attributes: " + strippedAttributes.join(", ") + (DISABLE_STRIPPED_ATTRIBUTES ? ' (disable mode) ' : ''));
    for(const attr of strippedAttributes) {
        if (DISABLE_STRIPPED_ATTRIBUTES) {
            // Add prefix to disable the attribute instead of removing it
            $(`*[${attr}]`).each(function() {
                const $el = $(this);
                const value = $el.attr(attr);
                $el.removeAttr(attr);
                // Add disabled version with prefix
                $el.attr(`__disabled__${attr}`, value || '');
            });
        } else {
            // Remove attributes normally
            $(`*[${attr}]`).removeAttr(attr);
        }
    }

    if (!STRIP_SRCSETS) {
        log.info("\nEvaluating and downloading responsive images (srcset)...");
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
                            /*
                             * Download to memory first only to discover the MIME type.
                             * safeDownload() requires a path, so don't use it for this.
                             */
                            const result =
                                await downloadWithRetry(absoluteUrl);

                            if (result && result.buffer?.length > 0) {
                                knownContentType =
                                    result.contentType || '';

                                urlContentTypeMap.set(
                                    registryKey,
                                    knownContentType
                                );

                                const localRelativePath =
                                    getOrCreateAssetPath(
                                        absoluteUrl,
                                        knownContentType
                                    );

                                const localPath =
                                    path.join(
                                        OUTPUT_DIR,
                                        localRelativePath
                                    );

                                fs.mkdirSync(
                                    path.dirname(localPath),
                                    { recursive: true }
                                );

                                fs.writeFileSync(
                                    localPath,
                                    result.buffer
                                );
                            }

                        } catch (fetchErr) {
                            log.warn(
                                `srcset download failed: ${absoluteUrl} - ${fetchErr.message}`
                            );
                        }
                    }

                    const localRelativePath =
                        getOrCreateAssetPath(
                            absoluteUrl,
                            knownContentType
                        );

                    newCandidates.push(descriptor ? `${localRelativePath} ${descriptor}` : localRelativePath);
                } catch (e) {
                    newCandidates.push(candidate);
                }
            }
            element.attr('srcset', newCandidates.join(', '));
        }
    }

    // Embed styles in head
    if (EMBED_STYLE_HEAD) {
        let styleContent = '';
        let stylePath = path.join(__dirname, EMBED_STYLE_HEAD);
        
        // Check if it's a file path or raw code
        if (fs.existsSync(stylePath)) {
            // It's a file - read it
            styleContent = fs.readFileSync(stylePath, 'utf-8');
            log.success(`Embedded style in head from file: ${EMBED_STYLE_HEAD}`);
        } else {
            // Treat as raw CSS code
            styleContent = EMBED_STYLE_HEAD;
            log.success(`Embedded raw style in head`);
        }
        
        const styleTag = `<style>\n${styleContent}\n</style>`;
        $('head').append(styleTag);
    }    

    // Embed script in head
    if (EMBED_SCRIPT_HEAD) {
        let scriptContent = '';
        let scriptPath = path.join(__dirname, EMBED_SCRIPT_HEAD);
        
        // Check if it's a file path or raw code
        if (fs.existsSync(scriptPath)) {
            // It's a file - read it
            scriptContent = fs.readFileSync(scriptPath, 'utf-8');
            log.success(`Embedded script in head from file: ${EMBED_SCRIPT_HEAD}`);
        } else {
            // Treat as raw JavaScript code
            scriptContent = EMBED_SCRIPT_HEAD;
            log.success(`Embedded raw script in head`);
        }
        
        const scriptTag = `<script>\n${scriptContent}\n</script>`;
        $('head').append(scriptTag);
    }

    // Embed script at body end
    if (EMBED_SCRIPT_BODY_END) {
        let scriptContent = '';
        let scriptPath = path.join(__dirname, EMBED_SCRIPT_BODY_END);
        
        // Check if it's a file path or raw code
        if (fs.existsSync(scriptPath)) {
            // It's a file - read it
            scriptContent = fs.readFileSync(scriptPath, 'utf-8');
            log.success(`Embedded script at body end from file: ${EMBED_SCRIPT_BODY_END}`);
        } else {
            // Treat as raw JavaScript code
            scriptContent = EMBED_SCRIPT_BODY_END;
            log.success(`Embedded raw script at body end`);
        }
        
        const scriptTag = `<script>\n${scriptContent}\n</script>`;
        $('body').append(scriptTag);
    }

    const resourcesToRewrite = [
        { selector: '*[src]', attr: 'src' },
        { selector: '*[href]', attr: 'href' }
    ];

    log.section("Running asset link processing");
    for (const { selector, attr } of resourcesToRewrite) {
        const elements = $(selector).toArray();
        for (const el of elements) {
            const element = $(el);
            let originalValue = element.attr(attr);
            if (!originalValue || originalValue.startsWith('data:')) continue;
            if (el.name === 'a') continue;
            if (attr === 'href' && (originalValue.startsWith('#') || originalValue.startsWith('javascript:'))) continue;

            try {
                const absoluteUrl = new URL(originalValue, TARGET_URL).href;
                if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) continue;

                const registryKey = cleanUrlKey(absoluteUrl);
                let knownContentType = urlContentTypeMap.get(registryKey) || '';

                if (!knownContentType && ['img', 'source', 'link', 'script'].includes(el.name)) {
                    const localPath = urlToLocalPath(absoluteUrl);
                    if (localPath) {
                        const result = await safeDownload(absoluteUrl, localPath);
                        if (result.success) {
                            knownContentType = result.contentType;
                            urlContentTypeMap.set(registryKey, knownContentType);
                        }
                    }
                }

                const localRelativePath = getOrCreateAssetPath(
                    absoluteUrl,
                    knownContentType
                );
                element.attr(attr, localRelativePath);
            } catch (e) {}
        }
    }

    log.section("Scanning inline scripts for hidden dynamic assets");
        
    const inlineScripts = $('script:not([src])').toArray();
    for (const el of inlineScripts) {
        const element = $(el);
        let content = element.html() || '';
        let modified = false;
        
        const regex = /(?:src|href)\s*=\s*(?:\\)*['"]([^'"]+?)(?:\\)*['"]/gi;
        const matches = [...content.matchAll(regex)];

        for (const match of matches) {
            const originalUrl = match[1];
            const cleanUrl = originalUrl.replace(/\\\//g, '/');

            if (!cleanUrl || cleanUrl.startsWith('data:') || cleanUrl.startsWith('#') || cleanUrl.startsWith('javascript:')) {
                continue;
            }

            try {
                const absoluteUrl = new URL(cleanUrl, TARGET_URL).href;
                if (ignoredPatterns.some(regex => regex.test(absoluteUrl))) continue;

                const registryKey = cleanUrlKey(absoluteUrl);
                let knownContentType = urlContentTypeMap.get(registryKey) || '';

                if (!knownContentType) {
                    const localPath = urlToLocalPath(absoluteUrl);
                    if (localPath) {
                        const result = await safeDownload(absoluteUrl, localPath);
                        if (result.success) {
                            knownContentType = result.contentType;
                            urlContentTypeMap.set(registryKey, knownContentType);
                        }
                    }
                }

                const localRelativePath = getOrCreateAssetPath(
                    absoluteUrl,
                    knownContentType
                );
                content = content.split(originalUrl).join(localRelativePath);
                modified = true;
            } catch (e) {}
        }

        if (modified) {
            element.text(content);
        }
    }

    const optimizedHtml = $.html({ decodeEntities: false });

    log.info("\nSaving index.html layout file...");
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
                log.warn(`Removing 0-byte file: ${filePath}`);
                try { fs.unlinkSync(filePath); } catch (e) {}
            }
        }
    }

    removeEmptyFiles(OUTPUT_DIR);

    writeErrorLog();

    if (downloadStatus) downloadStatus.stop();

    log.title('DOWNLOAD SUMMARY');
    log.success(`Total files processed: ${downloadStats.totalFiles}`);
    log.success(`Successfully downloaded: ${downloadStats.downloaded}`);
    (downloadStats.failed > 0 ? log.warn : log.info)(`Failed downloads: ${downloadStats.failed}`);
    log.info(`Skipped (ignored patterns): ${downloadStats.skipped}`);
    
    if (downloadStats.missingFiles.size > 0) {
        log.section('MISSING FILES (404 or download errors)');
        const missingArray = Array.from(downloadStats.missingFiles);
        const fonts = missingArray.filter(url => url.match(/\.(woff2?|ttf|otf|eot)$/i));
        const images = missingArray.filter(url => url.match(/\.(jpg|jpeg|png|gif|webp|svg|ico)$/i));
        const css = missingArray.filter(url => url.match(/\.css$/i));
        const js = missingArray.filter(url => url.match(/\.js$/i));
        const other = missingArray.filter(url => 
            !fonts.includes(url) && !images.includes(url) && !css.includes(url) && !js.includes(url)
        );

        const printGroup = (label, urls) => {
            if (urls.length === 0) return;
            log.warn(`  ${label} (${urls.length}):`);
            urls.slice(0, 5).forEach(url => log.dim(`    - ${url}`));
            if (urls.length > 5) log.dim(`    ... and ${urls.length - 5} more`);
        };

        printGroup('Fonts', fonts);
        printGroup('Images', images);
        printGroup('CSS', css);
        printGroup('JavaScript', js);
        printGroup('Other', other);
    }
    
    if (downloadStats.errors.length > 0) {
        log.section('ERROR LOG (first 10)');
        downloadStats.errors.slice(0, 10).forEach(error => log.dim(`  - ${error}`));
        if (downloadStats.errors.length > 10) {
            log.dim(`  ... and ${downloadStats.errors.length - 10} more errors`);
        }
    }

    log.info('============================================');
    log.success(`Finished! Saved output path: ${rootHtmlPath}`);
    log.info(`Output directory: ${OUTPUT_DIR}`);
    log.info('============================================');

}

mainPrompts()
    .then(() => exitCleanly(0))
    .catch((err) => {
        log.error(`Fatal error: ${err.message}`);
        exitCleanly(1);
    });