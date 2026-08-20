import termkit from 'terminal-kit';

const term = termkit.terminal;

/* ------------------------------------------------------------------ */
/*  Clean process exit                                                 */
/* ------------------------------------------------------------------ */

// terminal-kit puts the terminal into raw mode (no echo, no line
// buffering) while grabbing input for prompts. If that grab isn't
// explicitly released, node.js will hang after the script "finishes"
// (blinking cursor, invisible typing) and Ctrl+C stops working because
// raw mode disables the OS-level SIGINT signal. This restores the
// terminal and force-exits after a short delay, as recommended by the
// terminal-kit docs.
function exitCleanly(code = 0) {
    term.grabInput(false);
    term.hideCursor(false);
    term.styleReset();
    setTimeout(() => process.exit(code), 100);
}

// Safety net: Ctrl+C is swallowed by raw mode instead of generating a
// real SIGINT, so we watch for it ourselves and always exit cleanly.
term.on('key', (name) => {
    if (name === 'CTRL_C') {
        term('\n');
        exitCleanly(130);
    }
});

/* ------------------------------------------------------------------ */
/*  Colored logging (replacement for console.log/warn/error)          */
/* ------------------------------------------------------------------ */

// Every log function returns to a fresh line first, in case a progress
// bar or status line is currently occupying the current line. It also
// erases anything left over on that line (e.g. a longer status line
// like "Downloading assets ... (total seen: 3)"), otherwise leftover
// characters from the old line can remain visible after shorter text
// is written on top of it.
function freshLine() {
    term.column(1);
    term.eraseLineAfter();
}

const log = {
    // General informational output (was: console.log)
    info(msg = '') {
        freshLine();
        term.white(msg + '\n');
    },

    // Success output (was: console.log with a prefix)
    success(msg = '') {
        freshLine();
        term.green(msg + '\n');
    },

    // Warnings (was: console.warn, or console.log with a prefix)
    warn(msg = '') {
        freshLine();
        term.yellow(msg + '\n');
    },

    // Errors (was: console.error)
    error(msg = '') {
        freshLine();
        term.red(msg + '\n');
    },

    // Muted/secondary detail line
    dim(msg = '') {
        freshLine();
        term.gray(msg + '\n');
    },

    // Section header, e.g. "--- Running asset link processing ---"
    section(msg = '') {
        freshLine();
        term('\n');
        term.cyan.bold(msg + '\n');
    },

    // Big banner-style title
    title(msg = '') {
        freshLine();
        term('\n');
        term.bgGreen.bold(`  ${msg}  `)('\n');
    }
};

/* ------------------------------------------------------------------ */
/*  Prompts (replacement for readline questions)                      */
/* ------------------------------------------------------------------ */

/**
 * Free-text input with an optional default value.
 * Mirrors the old `rl.question(...)` behaviour but with a nicer prompt.
 */
async function askText(promptText, defaultValue = '') {
    freshLine();
    term.cyan(promptText);
    if (defaultValue) term.gray(`(default: ${defaultValue}) `);

    const result = await term.inputField({ default: defaultValue }).promise;
    term('\n');
    return (result || '').trim();
}

/**
 * Repeats the URL prompt until a non-empty value is entered, then
 * normalizes it to include a protocol.
 */
async function askUrl(promptText = 'Enter website URL: ') {
    let value = '';
    while (!value) {
        value = await askText(promptText);
        if (!value) log.warn('Please enter a URL.');
    }
    if (!value.startsWith('http://') && !value.startsWith('https://')) {
        value = 'https://' + value;
    }
    return value;
}

/**
 * Arrow-key / y-n selectable Yes/No menu, replacing the old
 * "type yes or no" text prompt.
 */
async function askYesNo(promptText, defaultValue = false) {
    freshLine();
    term.cyan(promptText + ' ');
    const result = await term.yesOrNo({
        yes: ['y', 'ENTER'],
        no: ['n'],
        echoYes: 'Yes',
        echoNo: 'No'
    }).promise;
    term('\n');
    return typeof result === 'boolean' ? result : defaultValue;
}

/**
 * Arrow-key selectable single-choice menu.
 * items: array of strings.
 * Returns the selected string.
 */
async function askMenu(promptText, items) {
    freshLine();
    term.cyan(promptText + '\n');
    const response = await term.singleColumnMenu(items).promise;
    term('\n');
    return response.selectedText;
}

/* ------------------------------------------------------------------ */
/*  Progress bars                                                      */
/* ------------------------------------------------------------------ */

/**
 * Creates a determinate progress bar (used when the total item count
 * is known ahead of time, e.g. processing N saved CSS/JS files).
 *
 * Usage:
 *   const bar = createProgressBar('Processing CSS files', total);
 *   bar.step('style.css');   // advances by 1 and updates the label
 *   bar.stop();
 */
function createProgressBar(title, total) {
    if (total <= 0) {
        return { step() {}, stop() {} };
    }

    freshLine();
    let current = 0;
    const controller = term.progressBar({
        width: 100,
        title,
        eta: true,
        percent: true,
        items: total
    });

    return {
        step(label = '') {
            current++;
            controller.startItem(label || `${current}/${total}`);
            controller.itemDone(label || `${current}/${total}`);
        },
        stop() {
            // terminal-kit throttles/coalesces progress-bar redraws, so a
            // loop that finishes very quickly (few items, short delays)
            // can call step() a couple of times and then stop() before
            // the bar has ever actually repainted past its initial 0%
            // frame. Force a final full-bar render before stopping so we
            // never commit a half-drawn frame to the terminal history.
            try { controller.update(1); } catch (e) {}
            controller.stop();
            term('\n');
        }
    };
}

/**
 * Live single-line status counter for the asset download loop, where
 * the total number of assets isn't known ahead of time (they're
 * discovered incrementally). Replaces the old printAtSameLine() call.
 *
 * Usage:
 *   const status = createDownloadStatus();
 *   status.update(downloadStats);   // call after every safeDownload()
 *   status.stop();
 */
function createDownloadStatus() {
    return {
        update(stats) {
            freshLine();
            term.eraseLineAfter();
            term(' ')
                .cyan('Downloading assets ')
                .green(`ok:${stats.downloaded} `)
                .yellow(`skip:${stats.skipped} `)
                .red(`fail:${stats.failed} `)
                .gray(`(total seen: ${stats.totalFiles})`);
        },
        stop() {
            term('\n');
        }
    };
}

/**
 * Creates a percentage-based progress bar for operations where progress
 * is a continuous ratio rather than a discrete item count (e.g. how far
 * down the page a scroll pass has reached). Call update(fraction) with
 * a value between 0 and 1.
 *
 * Usage:
 *   const bar = createPercentBar('Scrolling page');
 *   bar.update(0.5);
 *   bar.stop();
 */
function createPercentBar(title) {
    freshLine();
    const controller = term.progressBar({
        width: 60,
        title,
        percent: true,
        eta: false
    });

    return {
        update(fraction) {
            controller.update(Math.max(0, Math.min(1, fraction)));
        },
        stop() {
            // Same throttled-redraw safety net as createProgressBar: make
            // sure the bar has actually rendered its 100% frame before
            // committing the line with a trailing newline.
            try { controller.update(1); } catch (e) {}
            controller.stop();
            term('\n');
        }
    };
}

export { term, log, askText, askUrl, askYesNo, askMenu, createProgressBar, createPercentBar, createDownloadStatus, exitCleanly };