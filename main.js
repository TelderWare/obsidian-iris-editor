'use strict';

const obsidian = require('obsidian');

// Hoisted regex constants — avoids re-creating on every call
const RE_HEADING = /^#{1,6}\s/;
const RE_WORD = /\S+/g;
const RE_LINK = /!?\[[^\]]*\]\([^)]*\)/g;
const RE_TAG = /(?<![&\w])#[\w/-]+/g;
const RE_TRAILING_PUNCT = /[.,;:!?)]+$/;
const RE_SINGLE_LETTER = /^[a-zA-Z]$/;
const RE_PURE_NUMBER = /^\d+$/;
const RE_CODE_FENCE = /^[ \t]*```/;
const RE_WORD_CHAR = /[\w\u00C0-\u024F]/;
const RE_LEADING_FORMAT = /^[*_~=]+/;
const RE_TRAILING_FORMAT = /[*_~=]+$/;
const RE_WIKILINK_TOKEN = /^\[\[([^\]|]+)(?:\|([^\]]+))?\]\]$/;
const RE_BARE_URL = /https?:\/\/[^\s<>\[\]]+/g;
const RE_ANGLE_URL = /<https?:\/\/[^>]+>/g;
const RE_URL_TRAIL = /[.,;:!?'")\]]+$/;
const RE_IS_URL = /^https?:\/\/\S+$/;
const RE_ORDERED_ITEM = /^(\s*)\d+\.\s/;
const RE_TASK_ITEM = /^(\s*)- \[([ xX])\]\s/;
const RE_DATE_SLASH = /(\d{1,2})\/(\d{1,2})\/(\d{2,4})$/;
const ABBREVS = new Set(['e.g', 'i.e', 'etc', 'vs', 'Dr', 'Mr', 'Mrs', 'Ms', 'Prof', 'Jr', 'Sr', 'St', 'Inc', 'Ltd', 'Co', 'Corp', 'al', 'fig', 'eq', 'no', 'vol', 'dept', 'govt', 'approx', 'est', 'ref', 'max', 'min', 'avg']);

const DEFAULT_SHORTCUTS = '# Arrows\n-> = \u2192\n<- = \u2190\n=> = \u21D2\n\\to = \u2192\n\\gets = \u2190\n\\rightarrow = \u2192\n\\leftarrow = \u2190\n\\Rightarrow = \u21D2\n\\Leftarrow = \u21D0\n\\Leftrightarrow = \u21D4\n\\leftrightarrow = \u2194\n\\uparrow = \u2191\n\\downarrow = \u2193\n\\mapsto = \u21A6\n\\nearrow = \u2197\n\\searrow = \u2198\n# Greek lowercase\nalpha = \u03B1\nbeta = \u03B2\ngamma = \u03B3\ndelta = \u03B4\nepsilon = \u03B5\nvarepsilon = \u03B5\nzeta = \u03B6\neta = \u03B7\ntheta = \u03B8\nvartheta = \u03D1\niota = \u03B9\nkappa = \u03BA\nlambda = \u03BB\nmu = \u03BC\nnu = \u03BD\nxi = \u03BE\npi = \u03C0\nrho = \u03C1\nsigma = \u03C3\nvarsigma = \u03C2\ntau = \u03C4\nupsilon = \u03C5\nphi = \u03C6\nvarphi = \u03C6\nchi = \u03C7\npsi = \u03C8\nomega = \u03C9\n# Greek uppercase\nGamma = \u0393\nDelta = \u0394\nTheta = \u0398\nLambda = \u039B\nXi = \u039E\nPi = \u03A0\nSigma = \u03A3\nUpsilon = \u03A5\nPhi = \u03A6\nPsi = \u03A8\nOmega = \u03A9\n# Math operators\n\\pm = \u00B1\n\\mp = \u2213\n\\times = \u00D7\n\\div = \u00F7\n\\cdot = \u00B7\n\\sqrt = \u221A\n\\infty = \u221E\n\\partial = \u2202\n\\nabla = \u2207\n\\sum = \u2211\n\\prod = \u220F\n\\int = \u222B\n\\oint = \u222E\n\\oplus = \u2295\n\\otimes = \u2297\n# Relations\n\\leq = \u2264\n\\le = \u2264\n\\geq = \u2265\n\\ge = \u2265\n\\neq = \u2260\n\\ne = \u2260\n\\approx = \u2248\n\\equiv = \u2261\n\\sim = \u223C\n\\simeq = \u2243\n\\cong = \u2245\n\\propto = \u221D\n\\ll = \u226A\n\\gg = \u226B\n# Set theory and logic\n\\in = \u2208\n\\notin = \u2209\n\\subset = \u2282\n\\supset = \u2283\n\\subseteq = \u2286\n\\supseteq = \u2287\n\\cup = \u222A\n\\cap = \u2229\n\\emptyset = \u2205\n\\forall = \u2200\n\\exists = \u2203\n\\neg = \u00AC\n\\land = \u2227\n\\lor = \u2228\n\\vdash = \u22A2\n\\top = \u22A4\n\\bot = \u22A5\n# Miscellaneous\n\\degree = \u00B0\n\\deg = \u00B0\n\\dagger = \u2020\n\\ddagger = \u2021\n\\bullet = \u2022\n\\circ = \u2218\n\\star = \u22C6\n\\langle = \u27E8\n\\rangle = \u27E9\n\\ldots = \u2026\n\\hbar = \u210F\n\\ell = \u2113\n\\aleph = \u2135\n# Typography\n(c) = \u00A9\n(r) = \u00AE\n(tm) = \u2122\n# Pure deletes\n%% iris:content %% = ';

function escapeRegex(s) {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

class IrisEditorPlugin extends obsidian.Plugin {
  async onload() {
    await this.loadSettings();
    this._replacing = false;
    this._editPassCount = 0;
    this._editPassResetTimer = null;
    this._pendingLinks = [];
    this._debounceTimer = null;
    this._refreshTimer = null;
    this._lastPollCursor = null;
    this._compiledIgnoreCache = null;
    this._ignoreFilterSource = null;
    this._contextCache = null;
    this._shortcutMap = new Map();
    this._sortedShortcuts = [];

    this.noteNameMap = new Map();
    this.firstWords = new Set();
    this.refreshNoteNames();
    this.parseShortcuts();

    this.registerEvent(this.app.vault.on('create', () => this.debouncedRefresh()));
    this.registerEvent(this.app.vault.on('delete', () => this.debouncedRefresh()));
    this.registerEvent(this.app.vault.on('rename', () => this.debouncedRefresh()));
    this.registerEvent(this.app.metadataCache.on('changed', () => this.debouncedRefresh()));

    this.addSettingTab(new IrisEditorSettingTab(this.app, this));

    // On edit: detect matches near cursor, apply far ones immediately
    this.registerEvent(
      this.app.workspace.on('editor-change', (editor) => {
        if (this._replacing) return;
        // Detect rapid edit cycles (rules fighting each other)
        this._editPassCount++;
        if (this._editPassResetTimer) clearTimeout(this._editPassResetTimer);
        this._editPassResetTimer = setTimeout(() => { this._editPassCount = 0; }, 200);
        if (this._editPassCount > 6) return;
        this._contextCache = null;
        if (!this.isFileInScope(this.app.workspace.getActiveFile())) return;
        this.applyShortcuts(editor);
        this.applyDateFormatting(editor);
        this.applyChemFormulas(editor);
        this.applyAutoCapitalize(editor);
        this.applySpellOutNumbers(editor);
        this.applyMultiplicationSign(editor);

        this.ensureBlankBeforeHeadings(editor);
        this.renumberOrderedLists(editor);
        this.sortTaskLists(editor);
        this.collapseBlankLines(editor);
        this.applyPureDeletes(editor);
        this.applyFarLinks(editor);
        this.detectNearCursor(editor);
      })
    );

    // On paste: wrap selected text with pasted URL
    this.registerEvent(
      this.app.workspace.on('editor-paste', (evt, editor) => {
        if (!this.pasteUrlAsLink) return;
        if (!this.isFileInScope(this.app.workspace.getActiveFile())) return;
        const clip = evt.clipboardData?.getData('text/plain')?.trim();
        if (!clip || !RE_IS_URL.test(clip)) return;
        const sel = editor.getSelection();
        if (sel) {
          evt.preventDefault();
          editor.replaceSelection('[' + sel + '](' + clip + ')');
        }
      })
    );

    // On Ctrl/Cmd+S: renumber, sort, then full scan
    this.addCommand({
      id: 'full-scan',
      name: 'Full scan for links',
      hotkeys: [{ modifiers: ['Mod'], key: 's' }],
      editorCallback: (editor) => {
        if (!this.isFileInScope(this.app.workspace.getActiveFile())) return;
        this.fullScan(editor);
      },
    });

    // Full scan on file open
    this.registerEvent(
      this.app.workspace.on('file-open', () => {
        if (!this.isFileInScope(this.app.workspace.getActiveFile())) return;
        const view = this.app.workspace.getActiveViewOfType(obsidian.MarkdownView);
        if (view) this.fullScan(view.editor);
      })
    );

    // Poll for cursor movement (arrow keys, clicks) to run formatting passes
    this.registerInterval(
      window.setInterval(() => {
        if (this._replacing) return;
        const view = this.app.workspace.getActiveViewOfType(obsidian.MarkdownView);
        if (!view) return;
        // Skip if cursor hasn't moved since last poll
        const cursor = view.editor.getCursor();
        if (this._lastPollCursor &&
            this._lastPollCursor.line === cursor.line &&
            this._lastPollCursor.ch === cursor.ch) return;
        this._lastPollCursor = { line: cursor.line, ch: cursor.ch };
        if (!this.isFileInScope(this.app.workspace.getActiveFile())) return;
        const editor = view.editor;
        this.ensureBlankBeforeHeadings(editor);
        this.renumberOrderedLists(editor);
        this.sortTaskLists(editor);
        this.collapseBlankLines(editor);
        this.applyPureDeletes(editor);
        this.applyFarLinks(editor);
        this.detectNearCursor(editor);
      }, 200)
    );
  }

  async loadSettings() {
    const data = await this.loadData();
    this.autoLink = data?.autoLink !== undefined ? data.autoLink : true;
    this.wrapBareUrls = data?.wrapBareUrls !== undefined ? data.wrapBareUrls : true;
    this.pasteUrlAsLink = data?.pasteUrlAsLink !== undefined ? data.pasteUrlAsLink : true;
    this.renumberLists = data?.renumberLists !== undefined ? data.renumberLists : true;
    this.sortTasks = data?.sortTasks !== undefined ? data.sortTasks : true;
    this.chemFormulas = data?.chemFormulas !== undefined ? data.chemFormulas : true;
    this.autoCapitalize = data?.autoCapitalize !== undefined ? data.autoCapitalize : true;
    this.spellOutNumbers = data?.spellOutNumbers !== undefined ? data.spellOutNumbers : true;
    this.multiplicationSign = data?.multiplicationSign !== undefined ? data.multiplicationSign : true;
    this.blankBeforeHeadings = data?.blankBeforeHeadings !== undefined ? data.blankBeforeHeadings : true;

    this.limitNewlines = data?.limitNewlines !== undefined ? data.limitNewlines : true;
    this.maxBlankLines = data?.maxBlankLines !== undefined ? data.maxBlankLines : 1;
    this.shortcuts = data?.shortcuts !== undefined ? data.shortcuts : true;
    this.shortcutList = data?.shortcutList !== undefined ? data.shortcutList : DEFAULT_SHORTCUTS;
    this.folder = data?.folder || '';
    this.linkFrom = data?.linkFrom || '';
    this.excludeToFolder = data?.excludeToFolder || '';
    this.excludeFromFolder = data?.excludeFromFolder || '';
    this.linkShortNames = data?.linkShortNames !== undefined ? data.linkShortNames : true;
    this.extraAliasKeys = data?.extraAliasKeys !== undefined ? data.extraAliasKeys : 'aliases2';
    this.autoFormatDates = data?.autoFormatDates !== undefined ? data.autoFormatDates : true;
    this.dateInputUS = data?.dateInputUS !== undefined ? data.dateInputUS : true;
    this.dateOutputFormat = data?.dateOutputFormat || 'DD/MM/YYYY';
  }

  async saveSettings() {
    await this.saveData({
      autoLink: this.autoLink,
      wrapBareUrls: this.wrapBareUrls,
      pasteUrlAsLink: this.pasteUrlAsLink,
      renumberLists: this.renumberLists,
      sortTasks: this.sortTasks,
      chemFormulas: this.chemFormulas,
      autoCapitalize: this.autoCapitalize,
      spellOutNumbers: this.spellOutNumbers,
      multiplicationSign: this.multiplicationSign,
      blankBeforeHeadings: this.blankBeforeHeadings,

      limitNewlines: this.limitNewlines,
      maxBlankLines: this.maxBlankLines,
      shortcuts: this.shortcuts,
      shortcutList: this.shortcutList,
      folder: this.folder,
      linkFrom: this.linkFrom,
      excludeToFolder: this.excludeToFolder,
      excludeFromFolder: this.excludeFromFolder,
      linkShortNames: this.linkShortNames,
      extraAliasKeys: this.extraAliasKeys,
      autoFormatDates: this.autoFormatDates,
      dateInputUS: this.dateInputUS,
      dateOutputFormat: this.dateOutputFormat,
    });
    // Re-apply transformations to active document
    const view = this.app.workspace.getActiveViewOfType(obsidian.MarkdownView);
    if (view && this.isFileInScope(this.app.workspace.getActiveFile())) {
      this.applyPureDeletes(view.editor);
      this.fullScan(view.editor);
    }
  }

  isFileInScope(file) {
    if (!file) return false;
    if (this.linkFrom && !file.path.startsWith(this.linkFrom + '/')) return false;
    if (this.excludeFromFolder && file.path.startsWith(this.excludeFromFolder + '/')) return false;
    if (this.isVaultIgnored(file.path)) return false;
    return true;
  }

  // Check if a path matches Obsidian's "Excluded files" (Settings > Files & Links)
  isVaultIgnored(filePath) {
    const filters = this.app.vault.config?.userIgnoreFilters;
    if (!filters || !filters.length) return false;

    // Rebuild compiled cache when the filter list reference changes
    if (this._ignoreFilterSource !== filters) {
      this._ignoreFilterSource = filters;
      this._compiledIgnoreCache = [];
      for (const f of filters) {
        if (f.startsWith('/') && f.endsWith('/')) {
          const pattern = f.slice(1, -1);
          if (pattern.length > 200) continue; // skip excessively long patterns (ReDoS risk)
          try { this._compiledIgnoreCache.push({ type: 'regex', regex: new RegExp(pattern) }); }
          catch (e) { /* invalid regex, skip */ }
        } else {
          this._compiledIgnoreCache.push({ type: 'prefix', value: f });
        }
      }
    }

    for (const entry of this._compiledIgnoreCache) {
      if (entry.type === 'regex' && entry.regex.test(filePath)) return true;
      if (entry.type === 'prefix' && filePath.startsWith(entry.value)) return true;
    }
    return false;
  }

  debouncedRefresh() {
    if (this._refreshTimer) clearTimeout(this._refreshTimer);
    this._refreshTimer = setTimeout(() => this.refreshNoteNames(), 500);
  }

  refreshNoteNames() {
    this.noteNameMap = new Map();
    this.firstWords = new Set();
    const prefix = this.folder ? this.folder + '/' : '';
    const excludePrefix = this.excludeToFolder ? this.excludeToFolder + '/' : '';

    // Build alias key list from standard keys + user-configured extras
    const aliasKeys = ['aliases', 'alias'];
    if (this.extraAliasKeys) {
      for (const k of this.extraAliasKeys.split(',')) {
        const trimmed = k.trim();
        if (trimmed && !aliasKeys.includes(trimmed)) aliasKeys.push(trimmed);
      }
    }

    const addFirstWord = (lower) => {
      const fw = lower.split(' ')[0];
      this.firstWords.add(fw);
      const stripped = fw.replace(RE_TRAILING_PUNCT, '');
      if (stripped !== fw) this.firstWords.add(stripped);
    };

    for (const file of this.app.vault.getMarkdownFiles()) {
      if (prefix && !file.path.startsWith(prefix)) continue;
      if (excludePrefix && file.path.startsWith(excludePrefix)) continue;
      if (this.isVaultIgnored(file.path)) continue;
      const basename = file.basename;
      const lower = basename.toLowerCase();
      // First-write-wins: if two files share a lowercased name, keep the first
      if (!this.noteNameMap.has(lower)) {
        this.noteNameMap.set(lower, basename);
      }
      addFirstWord(lower);

      // Also index aliases from frontmatter
      const cache = this.app.metadataCache.getFileCache(file);
      const fm = cache && cache.frontmatter;
      if (fm) {
        for (const key of aliasKeys) {
          let raw = fm[key];
          if (!raw) continue;
          const list = Array.isArray(raw) ? raw
            : typeof raw === 'string' ? raw.split(',').map(s => s.trim())
            : [];
          for (const a of list) {
            if (typeof a !== 'string' || !a.trim()) continue;
            const aliasLower = a.trim().toLowerCase();
            if (!this.noteNameMap.has(aliasLower)) {
              this.noteNameMap.set(aliasLower, basename);
            }
            addFirstWord(aliasLower);
          }
        }
      }
    }
  }

  // Rebuild boundary cache: stores frontmatter end line and code fence toggle lines
  _rebuildContextCache(editor) {
    const lineCount = editor.lineCount();
    let fmEnd = -1;
    const codeFences = [];

    let inFrontmatter = false;
    for (let i = 0; i < lineCount; i++) {
      const line = editor.getLine(i);
      if (i === 0 && line === '---') { inFrontmatter = true; continue; }
      if (inFrontmatter) {
        if (line === '---') { fmEnd = i; inFrontmatter = false; }
        continue;
      }
      if (RE_CODE_FENCE.test(line)) codeFences.push(i);
    }

    this._contextCache = { lineCount, fmEnd, codeFences, inFrontmatter };
  }

  // Check if a line is inside frontmatter or a code block (cached)
  getLineContext(editor, targetLine) {
    if (!this._contextCache || this._contextCache.lineCount !== editor.lineCount()) {
      this._rebuildContextCache(editor);
    }
    const cache = this._contextCache;

    // Inside frontmatter (line 0 is ---, targetLine before closing ---)
    if (cache.fmEnd >= 0 && targetLine <= cache.fmEnd) return { skip: true };
    // Unclosed frontmatter
    if (cache.inFrontmatter) return { skip: true };

    // Count code fences before targetLine to determine if inside a code block
    let inCode = false;
    for (const fenceLine of cache.codeFences) {
      if (fenceLine >= targetLine) break;
      inCode = !inCode;
    }
    // If targetLine is itself a fence line, it's a boundary — skip it
    if (cache.codeFences.includes(targetLine)) return { skip: true };

    return { skip: inCode };
  }

  // Detect matches on the cursor line and store as pending
  detectNearCursor(editor) {
    const cursor = editor.getCursor();
    const lineNum = cursor.line;
    const line = editor.getLine(lineNum);
    const activeFile = this.app.workspace.getActiveFile();

    // Clear stale pending links on the edited line
    this._pendingLinks = this._pendingLinks.filter(p => p.line !== lineNum);

    // Skip if line is in frontmatter, code block, or is a heading
    if (RE_HEADING.test(line)) return;
    const ctx = this.getLineContext(editor, lineNum);
    if (ctx.skip) return;

    // Find new matches on this line
    const matches = [];
    this.findAllMatchesOnLine(line, lineNum, activeFile, matches);
    this._pendingLinks.push(...matches);
  }

  // Full document scan — chunked to avoid blocking UI
  fullScan(editor) {
    if (this._replacing) return;

    const activeFile = this.app.workspace.getActiveFile();
    const lineCount = editor.lineCount();
    const pending = [];
    const CHUNK = 200;

    let inCodeBlock = false;
    let inFrontmatter = false;
    let startLine = 0;

    const processChunk = () => {
      const end = Math.min(startLine + CHUNK, lineCount);

      for (let lineNum = startLine; lineNum < end; lineNum++) {
        const line = editor.getLine(lineNum);

        if (lineNum === 0 && line === '---') { inFrontmatter = true; continue; }
        if (inFrontmatter) { if (line === '---') inFrontmatter = false; continue; }
        if (RE_CODE_FENCE.test(line)) { inCodeBlock = !inCodeBlock; continue; }
        if (inCodeBlock) continue;

        this.findAllMatchesOnLine(line, lineNum, activeFile, pending);
      }

      startLine = end;

      if (startLine < lineCount) {
        setTimeout(processChunk, 0);
      } else {
        this._pendingLinks = pending;
        this.applyPureDeletes(editor);
        this.applyFarLinks(editor);
      }
    };

    processChunk();
  }

  // Apply pending links that are no longer adjacent to the cursor (batched as single undo step)
  applyFarLinks(editor) {
    if (this._replacing || this._pendingLinks.length === 0) return;

    const cursor = editor.getCursor();
    const toApply = [];
    const toKeep = [];

    for (const p of this._pendingLinks) {
      if (p.line !== cursor.line || cursor.ch < p.start || cursor.ch > p.end) {
        toApply.push(p);
      } else {
        toKeep.push(p);
      }
    }

    if (toApply.length === 0) return;

    this._pendingLinks = toKeep;

    // Build validated changes for a single transaction
    const changes = [];
    for (const r of toApply) {
      const line = editor.getLine(r.line);

      if (r.type === 'url') {
        if (!line || line.substring(r.start, r.end) !== r.url) continue;
        if (r.start > 0 && line[r.start - 1] === '<') continue;
        changes.push({
          from: { line: r.line, ch: r.start },
          to: { line: r.line, ch: r.end },
          text: '<' + r.url + '>',
        });
      } else {
          // Auto-linking
          const verifyText = r.originalText || r.typed;
          if (!line || line.substring(r.start, r.end) !== verifyText) continue;
          if ((r.start > 0 && RE_WORD_CHAR.test(line[r.start - 1])) ||
              (r.end < line.length && RE_WORD_CHAR.test(line[r.end]))) continue;

          const isEmbed = r.start === 0 && r.end === line.length;
          const inner = r.name === r.typed
            ? '[[' + r.typed + ']]'
            : '[[' + r.name + '|' + r.typed + ']]';
          const linkText = isEmbed ? '!' + inner : inner;
          changes.push({
            from: { line: r.line, ch: r.start },
            to: { line: r.line, ch: r.end },
            text: linkText,
          });
        }
    }

    if (changes.length === 0) return;

    this._replacing = true;
    try {
      editor.transaction({ changes });
    } finally {
      this._replacing = false;
    }
  }

  // Dispatch to active feature detectors
  findAllMatchesOnLine(line, lineNum, activeFile, matches) {
    if (this.autoLink) this.findNoteLinksOnLine(line, lineNum, activeFile, matches);
    if (this.wrapBareUrls) this.findBareUrlsOnLine(line, lineNum, matches);
  }

  // Find note name matches on a line
  findNoteLinksOnLine(line, lineNum, activeFile, matches) {
    if (RE_HEADING.test(line)) return;

    // Build list of ranges to exclude: markdown links, images, tags
    const excludeRanges = [];
    let ex;
    RE_LINK.lastIndex = 0;
    while ((ex = RE_LINK.exec(line)) !== null) {
      excludeRanges.push([ex.index, ex.index + ex[0].length]);
    }
    RE_TAG.lastIndex = 0;
    while ((ex = RE_TAG.exec(line)) !== null) {
      excludeRanges.push([ex.index, ex.index + ex[0].length]);
    }

    // Tokenize, stripping trailing punctuation for matching
    const tokens = [];
    RE_WORD.lastIndex = 0;
    let m;
    while ((m = RE_WORD.exec(line)) !== null) {
      const text = m[0];
      const start = m.index;

      // Check if this token is an exact wiki link [[target]] or [[target|display]]
      const wikiMatch = text.match(RE_WIKILINK_TOKEN);
      if (wikiMatch) {
        tokens.push({
          text: wikiMatch[2] || wikiMatch[1],  // Display text (after |), or target if no pipe
          start: start,
          end: start + text.length,
          isWikiLink: true,
        });
        continue;
      }

      const stripped = text.replace(RE_TRAILING_PUNCT, '');

      // Strip inline markdown formatting (bold, italic, highlight, strikethrough)
      let innerStart = 0;
      let innerEnd = stripped.length;
      const leadFmt = stripped.match(RE_LEADING_FORMAT);
      if (leadFmt) innerStart = leadFmt[0].length;
      if (innerStart < innerEnd) {
        const trailFmt = stripped.substring(innerStart).match(RE_TRAILING_FORMAT);
        if (trailFmt) innerEnd = stripped.length - trailFmt[0].length;
      }
      if (innerStart >= innerEnd) continue; // pure formatting, no text

      tokens.push({
        text: stripped.substring(innerStart, innerEnd),
        start: start + innerStart,
        end: start + innerEnd,
      });
    }

    let i = 0;
    while (i < tokens.length) {
      if (!this.firstWords.has(tokens[i].text.toLowerCase())) { i++; continue; }

      let bestMatch = null;
      let bestTyped = null;
      let bestStart = -1;
      let bestEnd = -1;
      let bestLen = 0;
      let bestHasWiki = false;

      let candidateLower = '';
      let candidateTyped = '';
      let hasWikiInSpan = false;
      for (let len = 1; len <= 5 && i + len <= tokens.length; len++) {
        if (tokens[i + len - 1].isWikiLink) hasWikiInSpan = true;
        if (len === 1) {
          candidateLower = tokens[i].text.toLowerCase();
          candidateTyped = tokens[i].text;
        } else {
          candidateLower += ' ' + tokens[i + len - 1].text.toLowerCase();
          candidateTyped += ' ' + tokens[i + len - 1].text;
        }
        const actualText = line.substring(tokens[i].start, tokens[i + len - 1].end);
        const normalizedActual = actualText.replace(/ {2,}/g, ' ');
        let noteName = this.noteNameMap.get(candidateLower);
        let typed = candidateTyped;
        // Reject stripped match if actual line text differs (skip for wiki link spans — brackets alter text)
        if (noteName && !hasWikiInSpan && normalizedActual !== candidateTyped) noteName = null;
        // Try raw line text for names containing punctuation (skip for wiki link spans)
        if (!noteName && !hasWikiInSpan) {
          noteName = this.noteNameMap.get(normalizedActual.toLowerCase());
          if (noteName) typed = actualText;
        }
        if (noteName) {
          bestMatch = noteName;
          bestTyped = typed;
          bestStart = tokens[i].start;
          bestEnd = tokens[i + len - 1].end;
          bestLen = len;
          bestHasWiki = hasWikiInSpan;
        }
      }

      if (!bestMatch) { i++; continue; }
      // Skip if match is just a single existing wiki link (already linked)
      if (bestLen === 1 && tokens[i].isWikiLink) { i++; continue; }

      if (!this.linkShortNames && (RE_SINGLE_LETTER.test(bestMatch) || RE_PURE_NUMBER.test(bestMatch))) { i += bestLen; continue; }
      if (activeFile && activeFile.basename.toLowerCase() === bestMatch.toLowerCase()) { i += bestLen; continue; }

      // Skip if inside an excluded range (markdown link, image, tag)
      let inExcluded = false;
      for (const [exStart, exEnd] of excludeRanges) {
        if (bestStart >= exStart && bestEnd <= exEnd) { inExcluded = true; break; }
      }
      if (inExcluded) { i += bestLen; continue; }

      const before = line.substring(0, bestStart);
      const after = line.substring(bestEnd);
      if (before.endsWith('[[') && after.startsWith(']]')) { i += bestLen; continue; }
      const lastOpen = before.lastIndexOf('[[');
      const lastClose = before.lastIndexOf(']]');
      if (lastOpen > lastClose) { i += bestLen; continue; }

      const backticks = (before.match(/`/g) || []).length;
      if (backticks % 2 !== 0) { i += bestLen; continue; }

      // Skip if match is part of a larger word (e.g. "RNA" inside "mRNA", "ATP" inside "ATPase")
      if ((bestStart > 0 && RE_WORD_CHAR.test(line[bestStart - 1])) ||
          (bestEnd < line.length && RE_WORD_CHAR.test(line[bestEnd]))) { i += bestLen; continue; }

      const match = { type: 'autolink', line: lineNum, start: bestStart, end: bestEnd, name: bestMatch, typed: bestTyped };
      if (bestHasWiki) match.originalText = line.substring(bestStart, bestEnd);
      matches.push(match);
      i += bestLen;
    }
  }

  // Find bare URLs on a line that aren't already wrapped
  findBareUrlsOnLine(line, lineNum, matches) {
    if (RE_HEADING.test(line)) return;

    // Build exclude ranges: markdown links, angle-bracket URLs, wiki links
    const excludeRanges = [];
    let ex;
    RE_LINK.lastIndex = 0;
    while ((ex = RE_LINK.exec(line)) !== null) {
      excludeRanges.push([ex.index, ex.index + ex[0].length]);
    }
    RE_ANGLE_URL.lastIndex = 0;
    while ((ex = RE_ANGLE_URL.exec(line)) !== null) {
      excludeRanges.push([ex.index, ex.index + ex[0].length]);
    }
    // Wiki link ranges
    let wi = 0;
    while ((wi = line.indexOf('[[', wi)) !== -1) {
      const ci = line.indexOf(']]', wi + 2);
      if (ci !== -1) { excludeRanges.push([wi, ci + 2]); wi = ci + 2; }
      else break;
    }

    RE_BARE_URL.lastIndex = 0;
    let m;
    while ((m = RE_BARE_URL.exec(line)) !== null) {
      let url = m[0];
      const start = m.index;

      // Strip trailing punctuation likely not part of the URL
      url = url.replace(RE_URL_TRAIL, '');
      if (url.length <= 8) continue; // just protocol with nothing after
      const end = start + url.length;

      // Check excluded ranges
      let inExcluded = false;
      for (const [es, ee] of excludeRanges) {
        if (start >= es && end <= ee) { inExcluded = true; break; }
      }
      if (inExcluded) continue;

      // Already in angle brackets
      if (start > 0 && line[start - 1] === '<') continue;

      // Inside inline code
      const before = line.substring(0, start);
      if ((before.match(/`/g) || []).length % 2 !== 0) continue;

      matches.push({ type: 'url', line: lineNum, start, end, url });
    }
  }

  // Renumber ordered lists sequentially
  renumberOrderedLists(editor) {
    if (!this.renumberLists) return;
    const lineCount = editor.lineCount();
    let inCodeBlock = false;
    let inFrontmatter = false;
    let i = 0;

    this._replacing = true;
    try {
      while (i < lineCount) {
        const line = editor.getLine(i);

        if (i === 0 && line === '---') { inFrontmatter = true; i++; continue; }
        if (inFrontmatter) { if (line === '---') inFrontmatter = false; i++; continue; }
        if (RE_CODE_FENCE.test(line)) { inCodeBlock = !inCodeBlock; i++; continue; }
        if (inCodeBlock) { i++; continue; }

        const m = line.match(RE_ORDERED_ITEM);
        if (!m) { i++; continue; }

        // Found start of an ordered list block at this indent level
        const indent = m[1];
        const indentPattern = new RegExp('^' + escapeRegex(indent) + '\\d+\\.\\s');
        let num = 1;

        while (i < lineCount) {
          const l = editor.getLine(i);
          if (indentPattern.test(l)) {
            const newLine = l.replace(/^(\s*)\d+\./, '$1' + num + '.');
            if (newLine !== l) {
              editor.replaceRange(newLine, { line: i, ch: 0 }, { line: i, ch: l.length });
            }
            num++;
            i++;
          } else if (l.trim() === '') {
            // Skip blank lines if the next non-blank line continues the list
            let peek = i + 1;
            while (peek < lineCount && editor.getLine(peek).trim() === '') peek++;
            if (peek < lineCount && indentPattern.test(editor.getLine(peek))) {
              i++;
            } else {
              break;
            }
          } else {
            break;
          }
        }
      }
    } finally {
      this._replacing = false;
    }
  }

  // Sort task lists: completed items first
  sortTaskLists(editor) {
    if (!this.sortTasks) return;
    const lineCount = editor.lineCount();
    let inCodeBlock = false;
    let inFrontmatter = false;
    let i = 0;

    this._replacing = true;
    try {
      while (i < lineCount) {
        const line = editor.getLine(i);

        if (i === 0 && line === '---') { inFrontmatter = true; i++; continue; }
        if (inFrontmatter) { if (line === '---') inFrontmatter = false; i++; continue; }
        if (RE_CODE_FENCE.test(line)) { inCodeBlock = !inCodeBlock; i++; continue; }
        if (inCodeBlock) { i++; continue; }

        const tm = line.match(RE_TASK_ITEM);
        if (!tm) { i++; continue; }

        // Collect task groups at this indent level (each group = task line + sub-lines)
        const baseIndent = tm[1];
        const blockStart = i;
        const groups = [];

        while (i < lineCount) {
          const l = editor.getLine(i);
          const taskMatch = l.match(RE_TASK_ITEM);
          if (!taskMatch || taskMatch[1] !== baseIndent) break;

          const group = { lines: [l], done: taskMatch[2] !== ' ' };
          i++;
          // Collect sub-lines (more indented than base)
          while (i < lineCount) {
            const sub = editor.getLine(i);
            if (sub.trim() === '') break;
            const subIndent = sub.match(/^(\s*)/)[1];
            if (subIndent.length <= baseIndent.length) break;
            group.lines.push(sub);
            i++;
          }
          groups.push(group);
        }

        if (groups.length <= 1) continue;

        // Sort: completed first, preserve relative order within each category (stable sort)
        const sorted = [...groups].sort((a, b) => {
          if (a.done === b.done) return 0;
          return a.done ? -1 : 1;
        });

        const origLines = groups.flatMap(g => g.lines);
        const sortedLines = sorted.flatMap(g => g.lines);

        let changed = false;
        for (let k = 0; k < origLines.length; k++) {
          if (origLines[k] !== sortedLines[k]) { changed = true; break; }
        }

        if (changed) {
          const blockEnd = blockStart + origLines.length - 1;
          // Save cursor and scroll position to prevent editor jump
          const cursor = editor.getCursor();
          const scrollInfo = editor.getScrollInfo();
          // If cursor is inside this block, figure out where it should land
          let newCursorLine = null;
          if (cursor.line >= blockStart && cursor.line <= blockEnd) {
            // Find which line within origLines the cursor is on
            const offsetInBlock = cursor.line - blockStart;
            const cursorOrigLine = origLines[offsetInBlock];
            // Find that same line in sortedLines
            const newOffset = sortedLines.indexOf(cursorOrigLine);
            if (newOffset !== -1) {
              newCursorLine = blockStart + newOffset;
            }
          }
          editor.replaceRange(
            sortedLines.join('\n'),
            { line: blockStart, ch: 0 },
            { line: blockEnd, ch: editor.getLine(blockEnd).length }
          );
          // Restore cursor position
          if (newCursorLine !== null) {
            editor.setCursor({ line: newCursorLine, ch: cursor.ch });
          } else {
            editor.setCursor(cursor);
          }
          // Restore scroll position
          editor.scrollTo(scrollInfo.left, scrollInfo.top);
        }
      }
    } finally {
      this._replacing = false;
    }
  }

  // Collapse runs of multiple spaces and blank lines (skip near cursor)
  collapseBlankLines(editor) {
    if (!this.limitNewlines) return;
    const max = this.maxBlankLines;
    const cursor = editor.getCursor();
    const cursorLine = cursor.line;
    let lineCount = editor.lineCount();
    let inCodeBlock = false;
    let inFrontmatter = false;

    this._replacing = true;
    try {
      // Remove leading blank lines (after frontmatter if present)
      let bodyStart = 0;
      if (lineCount > 0 && editor.getLine(0) === '---') {
        bodyStart = 1;
        while (bodyStart < lineCount && editor.getLine(bodyStart) !== '---') bodyStart++;
        if (bodyStart < lineCount) bodyStart++; // skip closing ---
      }
      while (bodyStart < lineCount && editor.getLine(bodyStart).trim() === '' && bodyStart !== cursorLine) {
        editor.replaceRange('', { line: bodyStart, ch: 0 }, { line: Math.min(bodyStart + 1, lineCount), ch: 0 });
        lineCount = editor.lineCount();
      }

      let i = 0;
      while (i < lineCount) {
        const line = editor.getLine(i);

        if (i === 0 && line === '---') { inFrontmatter = true; i++; continue; }
        if (inFrontmatter) { if (line === '---') inFrontmatter = false; i++; continue; }
        if (RE_CODE_FENCE.test(line)) { inCodeBlock = !inCodeBlock; i++; continue; }
        if (inCodeBlock) { i++; continue; }

        // Remove empty bullet points on non-cursor lines
        if (i !== cursorLine && /^\s*[-*+]\s*$/.test(line)) {
          editor.replaceRange('', { line: i, ch: 0 }, { line: Math.min(i + 1, lineCount), ch: 0 });
          lineCount = editor.lineCount();
          continue;
        }

        // Fix double space after checkbox to single space
        if (i !== cursorLine && /^\s*- \[[ xX]\] {2,}/.test(line)) {
          const fixed = line.replace(/^(\s*- \[[ xX]\]) {2,}/, '$1 ');
          editor.replaceRange(fixed, { line: i, ch: 0 }, { line: i, ch: line.length });
        }

        // Strip leading spaces on non-cursor lines (skip lists, blockquotes, indented content)
        if (i !== cursorLine && /^ +/.test(line) && !/^\s*[-*+]\s/.test(line) && !/^\s*\d+\.\s/.test(line) && !/^\s*>/.test(line)) {
          const trimmed = line.replace(/^ +/, '');
          editor.replaceRange(trimmed, { line: i, ch: 0 }, { line: i, ch: line.length });
        }

        // Collapse multi-spaces on non-cursor lines
        if (i !== cursorLine) {
          const current = editor.getLine(i);
          if (/ {2,}/.test(current)) {
            const collapsed = current.replace(/ {2,}/g, ' ');
            if (collapsed !== current) {
              editor.replaceRange(collapsed, { line: i, ch: 0 }, { line: i, ch: current.length });
            }
          }
        }

        if (line.trim() !== '') { i++; continue; }

        // Count consecutive blank lines
        const blankStart = i;
        while (i < lineCount && editor.getLine(i).trim() === '') i++;
        const blankEnd = i;
        const blankCount = blankEnd - blankStart;

        // Skip trailing blank runs when cursor is in or past them (let user add space at end)
        if (blankEnd >= lineCount && cursorLine >= blankStart) { break; }

        // No blank lines between a heading and its content (but keep one if next line is also a heading and blankBeforeHeadings is on)
        const afterHeading = blankStart > 0 && RE_HEADING.test(editor.getLine(blankStart - 1));
        const beforeHeading = blankEnd < lineCount && RE_HEADING.test(editor.getLine(blankEnd));
        const effective = afterHeading ? (beforeHeading && this.blankBeforeHeadings ? Math.min(max, 1) : 0) : max;

        if (blankCount > effective) {
          const keepEnd = blankStart + effective;
          const deleteEnd = blankStart + blankCount;
          editor.replaceRange(
            '',
            { line: keepEnd, ch: 0 },
            { line: deleteEnd, ch: 0 }
          );
          lineCount = editor.lineCount();
          // If cursor was inside the deleted range, move it to the last kept blank line
          if (cursorLine >= keepEnd && cursorLine < deleteEnd) {
            const dest = effective > 0 ? keepEnd - 1 : keepEnd;
            editor.setCursor({ line: dest, ch: 0 });
          }
          i -= (blankCount - effective);
        }
      }

      // Remove trailing blank lines at end of document (skip if cursor is at/past the last content line)
      const lc = editor.lineCount();
      let last = lc - 1;
      while (last > 0 && editor.getLine(last).trim() === '') last--;
      if (last + 1 < lc && cursorLine <= last) {
        editor.replaceRange('', { line: last, ch: editor.getLine(last).length }, { line: lc - 1, ch: editor.getLine(lc - 1).length });
      }
    } finally {
      this._replacing = false;
    }
  }

  // Remove pure-delete patterns from non-cursor lines
  applyPureDeletes(editor) {
    if (!this.shortcuts || this._sortedShortcuts.length === 0) return;
    const deletes = this._sortedShortcuts.filter(([, r]) => r === '');
    if (deletes.length === 0) return;
    const cursor = editor.getCursor();
    const cursorLine = cursor.line;
    const lineCount = editor.lineCount();
    let inCodeBlock = false;
    let inFrontmatter = false;

    this._replacing = true;
    try {
      let i = 0;
      while (i < lineCount) {
        const line = editor.getLine(i);

        if (i === 0 && line === '---') { inFrontmatter = true; i++; continue; }
        if (inFrontmatter) { if (line === '---') inFrontmatter = false; i++; continue; }
        if (RE_CODE_FENCE.test(line)) { inCodeBlock = !inCodeBlock; i++; continue; }
        if (inCodeBlock) { i++; continue; }
        if (i === cursorLine) { i++; continue; }

        let modified = line;
        for (const [pattern] of deletes) {
          while (modified.includes(pattern)) {
            modified = modified.split(pattern).join('');
          }
        }

        if (modified !== line) {
          if (modified.trim() === '') {
            editor.replaceRange('', { line: i, ch: 0 }, { line: Math.min(i + 1, editor.lineCount()), ch: 0 });
            continue;
          } else {
            editor.replaceRange(modified, { line: i, ch: 0 }, { line: i, ch: line.length });
          }
        }

        i++;
      }
    } finally {
      this._replacing = false;
    }
  }

  // Detect chemical formula patterns and convert digits/charges to sub/superscript
  applyChemFormulas(editor) {
    if (!this.chemFormulas) return;
    const cursor = editor.getCursor();
    const line = editor.getLine(cursor.line);
    const ch = cursor.ch;
    if (ch < 2) return;

    const trigger = line[ch - 1];
    if (!/[\s.,;:!?)\]}]/.test(trigger)) return;

    const ctx = this.getLineContext(editor, cursor.line);
    if (ctx.skip) return;

    const beforeAll = line.substring(0, ch - 1);
    if ((beforeAll.match(/`/g) || []).length % 2 !== 0) return;

    // Extract preceding word (including parens and +/-)
    const wordMatch = beforeAll.match(/([A-Za-z0-9()+-]+)$/);
    if (!wordMatch) return;
    const word = wordMatch[1];
    const wordStart = ch - 1 - word.length;

    // Must start with uppercase, contain [A-Za-z0-9()+-], have a digit or trailing charge
    if (!/^[A-Z][a-zA-Z0-9()+-]*$/.test(word)) return;
    if (!/\d/.test(word) && !/[+-]$/.test(word)) return;
    // Reject 3+ consecutive lowercase (likely a regular word, e.g. "Figure1")
    if (/[a-z]{3}/.test(word)) return;

    const converted = this.formatChemFormula(word);
    if (converted === word) return;

    this._replacing = true;
    try {
      editor.replaceRange(
        converted + trigger,
        { line: cursor.line, ch: wordStart },
        { line: cursor.line, ch: ch }
      );
    } finally {
      this._replacing = false;
    }
  }

  formatChemFormula(word) {
    const SUB = { '0':'\u2080','1':'\u2081','2':'\u2082','3':'\u2083','4':'\u2084','5':'\u2085','6':'\u2086','7':'\u2087','8':'\u2088','9':'\u2089' };
    const SUP = { '0':'\u2070','1':'\u00B9','2':'\u00B2','3':'\u00B3','4':'\u2074','5':'\u2075','6':'\u2076','7':'\u2077','8':'\u2078','9':'\u2079','+':'\u207A','-':'\u207B' };

    // Separate trailing charge (digits + sign) from formula body
    const chargeMatch = word.match(/(\d*[+-])$/);
    let body, charge;
    if (chargeMatch) {
      charge = chargeMatch[1];
      body = word.substring(0, word.length - charge.length);
    } else {
      body = word;
      charge = '';
    }

    let result = '';
    for (const ch of body) result += SUB[ch] || ch;
    for (const ch of charge) result += SUP[ch] || ch;
    return result;
  }

  // Auto-format dates to configured output format when a delimiter is typed after them
  applyDateFormatting(editor) {
    if (!this.autoFormatDates) return;
    const cursor = editor.getCursor();
    const line = editor.getLine(cursor.line);
    const ch = cursor.ch;
    if (ch < 6) return;

    const trigger = line[ch - 1];
    if (!/[\s.,;:!?)\]}]/.test(trigger)) return;

    const ctx = this.getLineContext(editor, cursor.line);
    if (ctx.skip) return;

    const before = line.substring(0, ch - 1);
    if ((before.match(/`/g) || []).length % 2 !== 0) return;

    let month, day, year, matchStart;

    // Try slash-separated: 3/30/2026 or 30/3/2026
    const slashMatch = before.match(RE_DATE_SLASH);
    if (slashMatch) {
      const a = parseInt(slashMatch[1], 10);
      const b = parseInt(slashMatch[2], 10);
      year = parseInt(slashMatch[3], 10);
      if (year < 100) {
        const century = Math.floor(new Date().getFullYear() / 100) * 100;
        const candidate = century + year;
        // Pick whichever century puts the year closest to now
        const now = new Date().getFullYear();
        if (Math.abs(candidate - now) > Math.abs(candidate - 100 - now)) year = candidate - 100;
        else if (Math.abs(candidate - now) > Math.abs(candidate + 100 - now)) year = candidate + 100;
        else year = candidate;
      }
      if (this.dateInputUS) { month = a; day = b; }
      else { day = a; month = b; }
      matchStart = before.length - slashMatch[0].length;
    }

    if (month === undefined) return;
    if (month < 1 || month > 12 || day < 1 || day > 31) return;
    if (year < 1900 || year > 2100) return;

    const dd = String(day).padStart(2, '0');
    const mm = String(month).padStart(2, '0');
    const yyyy = String(year);
    const formatted = this.dateOutputFormat
      .replace('DD', dd).replace('MM', mm).replace('YYYY', yyyy);
    if (before.substring(matchStart) === formatted) return; // already formatted

    // Prevent re-formatting: if the matched text already fits the output format pattern, skip
    if (!this._dateOutputRe || this._dateOutputFmt !== this.dateOutputFormat) {
      this._dateOutputFmt = this.dateOutputFormat;
      const pattern = escapeRegex(this.dateOutputFormat)
        .replace('DD', '\\d{2}').replace('MM', '\\d{2}').replace('YYYY', '\\d{4}');
      this._dateOutputRe = new RegExp('^' + pattern + '$');
    }
    if (this._dateOutputRe.test(before.substring(matchStart))) return;

    this._replacing = true;
    try {
      editor.replaceRange(
        formatted + trigger,
        { line: cursor.line, ch: matchStart },
        { line: cursor.line, ch: ch }
      );
    } finally {
      this._replacing = false;
    }
  }

  // Parse shortcut list into a map, sorted longest-first for greedy matching
  parseShortcuts() {
    this._shortcutMap = new Map();
    if (!this.shortcutList) { this._sortedShortcuts = []; return; }
    for (const line of this.shortcutList.split('\n')) {
      const trimmed = line.trim();
      if (!trimmed || trimmed.startsWith('#')) continue;
      let idx = trimmed.indexOf(' = ');
      if (idx <= 0 && trimmed.endsWith(' =')) idx = trimmed.length - 2;
      if (idx <= 0) continue;
      const shortcut = trimmed.substring(0, idx);
      const replacement = idx + 3 <= trimmed.length ? trimmed.substring(idx + 3) : '';
      if (shortcut) this._shortcutMap.set(shortcut, replacement);
    }
    this._sortedShortcuts = [...this._shortcutMap.entries()].sort((a, b) => b[0].length - a[0].length);
  }

  // Replace shortcut text when a delimiter is typed after it
  applyShortcuts(editor) {
    if (!this.shortcuts || this._sortedShortcuts.length === 0) return;
    const cursor = editor.getCursor();
    const line = editor.getLine(cursor.line);
    const ch = cursor.ch;
    if (ch < 2) return;

    // Only trigger on delimiter characters
    const trigger = line[ch - 1];
    if (!/[\s.,;:!?)\]}]/.test(trigger)) return;

    // Skip if in frontmatter or code block
    const ctx = this.getLineContext(editor, cursor.line);
    if (ctx.skip) return;

    // Skip if inside inline code
    const beforeAll = line.substring(0, ch - 1);
    if ((beforeAll.match(/`/g) || []).length % 2 !== 0) return;

    for (const [shortcut, replacement] of this._sortedShortcuts) {
      if (ch - 1 < shortcut.length) continue;
      const start = ch - 1 - shortcut.length;
      if (line.substring(start, ch - 1) !== shortcut) continue;

      // Word boundary: don't replace inside words (e.g. don't match "btw" inside "abtw")
      if (start > 0 && /\w/.test(line[start - 1]) && /\w/.test(shortcut[0])) continue;

      this._replacing = true;
      try {
        editor.replaceRange(
          replacement ? replacement + trigger : '',
          { line: cursor.line, ch: start },
          { line: cursor.line, ch: ch }
        );
      } finally {
        this._replacing = false;
      }
      return;
    }
  }

  // Auto-capitalize first letter of sentences
  applyAutoCapitalize(editor) {
    if (!this.autoCapitalize) return;
    const cursor = editor.getCursor();
    const line = editor.getLine(cursor.line);
    const ch = cursor.ch;
    if (ch < 1) return;

    const typed = line[ch - 1];
    // Only trigger when a lowercase letter is typed
    if (!/[a-z]/.test(typed)) return;

    const ctx = this.getLineContext(editor, cursor.line);
    if (ctx.skip) return;

    const before = line.substring(0, ch - 1);
    // Skip inside inline code
    if ((before.match(/`/g) || []).length % 2 !== 0) return;

    // Capitalize after: sentence-ending punctuation + space(s), or start of line (after optional list markers)
    const afterPunct = /[.!?]\s+$/.test(before);
    const shouldCapitalize =
      afterPunct ||
      /^\s*$/.test(before) ||
      /^#{1,6}\s+$/.test(before) ||
      /^\s*[-*+]\s+$/.test(before) ||
      /^\s*\d+\.\s+$/.test(before) ||
      /^\s*- \[[ xX]\]\s+$/.test(before);

    if (!shouldCapitalize) return;

    // Skip capitalizing after common abbreviations (e.g., Dr., vs., etc.)
    if (afterPunct) {
      const wordBefore = before.trimEnd().match(/(\S+)$/);
      if (wordBefore) {
        const raw = wordBefore[1].replace(/[.!?]+$/, '');
        if (ABBREVS.has(raw)) return;
      }
    }

    this._replacing = true;
    try {
      editor.transaction({
        changes: [{
          from: { line: cursor.line, ch: ch - 1 },
          to: { line: cursor.line, ch: ch },
          text: typed.toUpperCase(),
        }],
      });
    } finally {
      this._replacing = false;
    }
  }

  // Spell out single-digit numbers (0-9) as words
  applySpellOutNumbers(editor) {
    if (!this.spellOutNumbers) return;
    const cursor = editor.getCursor();
    const line = editor.getLine(cursor.line);
    const ch = cursor.ch;
    if (ch < 2) return;

    // Only trigger on delimiter characters
    const trigger = line[ch - 1];
    if (!/[\s.,;:!?)\]}]/.test(trigger)) return;

    const ctx = this.getLineContext(editor, cursor.line);
    if (ctx.skip) return;

    const before = line.substring(0, ch - 1);
    // Skip inside inline code
    if ((before.match(/`/g) || []).length % 2 !== 0) return;

    // Match a standalone number (1-2 digits) at the end
    const m = before.match(/(^|[^\da-zA-Z])(\d{1,2})$/);
    if (!m) return;

    const num = parseInt(m[2], 10);
    if (num > 20) return;

    const numStr = m[2];
    const numStart = ch - 1 - numStr.length;

    const WORDS = [
      'zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine',
      'ten', 'eleven', 'twelve', 'thirteen', 'fourteen', 'fifteen', 'sixteen', 'seventeen',
      'eighteen', 'nineteen', 'twenty'
    ];
    const word = WORDS[num];

    this._replacing = true;
    try {
      editor.replaceRange(
        word,
        { line: cursor.line, ch: numStart },
        { line: cursor.line, ch: numStart + numStr.length }
      );
    } finally {
      this._replacing = false;
    }
  }

  // Replace x between numbers with multiplication sign ×
  applyMultiplicationSign(editor) {
    if (!this.multiplicationSign) return;
    const cursor = editor.getCursor();
    const line = editor.getLine(cursor.line);
    const ch = cursor.ch;
    if (ch < 3) return;

    const typed = line[ch - 1];
    // Trigger when a digit is typed after <number>x
    if (!/\d/.test(typed)) return;

    const ctx = this.getLineContext(editor, cursor.line);
    if (ctx.skip) return;

    const before = line.substring(0, ch - 1);
    // Skip inside inline code
    if ((before.match(/`/g) || []).length % 2 !== 0) return;

    // Match <digits>x at end of before
    if (!/\d[xX]$/.test(before)) return;

    const xPos = ch - 2;

    this._replacing = true;
    try {
      editor.replaceRange(
        '\u00D7',
        { line: cursor.line, ch: xPos },
        { line: cursor.line, ch: xPos + 1 }
      );
    } finally {
      this._replacing = false;
    }
  }

  // Insert a blank line before headings that don't have one (skip near cursor)
  ensureBlankBeforeHeadings(editor) {
    if (!this.blankBeforeHeadings) return;
    const cursorLine = editor.getCursor().line;
    const lineCount = editor.lineCount();
    let inCodeBlock = false;
    let inFrontmatter = false;

    this._replacing = true;
    try {
      let i = 0;
      let seenBodyContent = false;
      while (i < lineCount) {
        const line = editor.getLine(i);

        if (i === 0 && line === '---') { inFrontmatter = true; i++; continue; }
        if (inFrontmatter) { if (line === '---') inFrontmatter = false; i++; continue; }
        if (RE_CODE_FENCE.test(line)) { inCodeBlock = !inCodeBlock; i++; continue; }
        if (inCodeBlock) { i++; continue; }

        if (RE_HEADING.test(line) && seenBodyContent) {
          const prev = editor.getLine(i - 1);
          // Skip if already blank, or cursor is on this line or adjacent
          if (prev.trim() !== '' && i !== cursorLine && i - 1 !== cursorLine) {
            editor.replaceRange('\n', { line: i, ch: 0 }, { line: i, ch: 0 });
            i++; // account for inserted line
          }
        }

        if (line.trim() !== '') seenBodyContent = true;

        i++;
      }
    } finally {
      this._replacing = false;
    }
  }

  onunload() {
    if (this._debounceTimer) clearTimeout(this._debounceTimer);
    if (this._refreshTimer) clearTimeout(this._refreshTimer);
  }
}

class IrisEditorSettingTab extends obsidian.PluginSettingTab {
  constructor(app, plugin) {
    super(app, plugin);
    this.plugin = plugin;
  }

  display() {
    const { containerEl } = this;
    containerEl.empty();

    // --- Features ---

    new obsidian.Setting(containerEl).setName('Auto-edits').setHeading();

    new obsidian.Setting(containerEl)
      .setName('Auto-link note names')
      .setDesc('Automatically wrap matching note names in [[wiki links]] as you type.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.autoLink)
        .onChange(async (value) => {
          this.plugin.autoLink = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Wrap bare URLs')
      .setDesc('Wrap unlinked URLs in angle brackets: <https://\u2026>')
      .addToggle(toggle => toggle
        .setValue(this.plugin.wrapBareUrls)
        .onChange(async (value) => {
          this.plugin.wrapBareUrls = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Paste URL as link')
      .setDesc('When pasting a URL with text selected, create [selection](url).')
      .addToggle(toggle => toggle
        .setValue(this.plugin.pasteUrlAsLink)
        .onChange(async (value) => {
          this.plugin.pasteUrlAsLink = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Renumber ordered lists')
      .setDesc('Fix ordered list numbering as you type.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.renumberLists)
        .onChange(async (value) => {
          this.plugin.renumberLists = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Sort task lists')
      .setDesc('Move completed tasks before incomplete ones as you type.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.sortTasks)
        .onChange(async (value) => {
          this.plugin.sortTasks = value;
          await this.plugin.saveSettings();
        })
      );

    const blankLinesSetting = new obsidian.Setting(containerEl)
      .setName('Limit blank lines')
      .setDesc('Collapse consecutive blank lines as you type.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.limitNewlines)
        .onChange(async (value) => {
          this.plugin.limitNewlines = value;
          await this.plugin.saveSettings();
          maxBlankSetting.settingEl.style.display = value ? '' : 'none';
        })
      );

    const maxBlankSetting = new obsidian.Setting(containerEl)
      .setName('Maximum blank lines')
      .setDesc('Maximum consecutive blank lines to keep.')
      .addText(text => text
        .setPlaceholder('1')
        .setValue(String(this.plugin.maxBlankLines))
        .onChange(async (value) => {
          const n = parseInt(value, 10);
          if (!isNaN(n) && n >= 0) {
            this.plugin.maxBlankLines = n;
            await this.plugin.saveSettings();
          }
        })
      );
    maxBlankSetting.settingEl.style.display = this.plugin.limitNewlines ? '' : 'none';

    // --- Formatting ---

    new obsidian.Setting(containerEl).setName('Formatting').setHeading();

    new obsidian.Setting(containerEl)
      .setName('Format chemical formulae')
      .setDesc('Auto-convert digits to subscripts and charges to superscripts (H2O \u2192 H\u2082O, Ca2+ \u2192 Ca\u00B2\u207A).')
      .addToggle(toggle => toggle
        .setValue(this.plugin.chemFormulas)
        .onChange(async (value) => {
          this.plugin.chemFormulas = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Auto-capitalize sentences')
      .setDesc('Capitalize the first letter after sentence-ending punctuation or at the start of lines.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.autoCapitalize)
        .onChange(async (value) => {
          this.plugin.autoCapitalize = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Spell out numbers up to 20')
      .setDesc('Replace numbers 0\u201320 with their word form when followed by a space or punctuation.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.spellOutNumbers)
        .onChange(async (value) => {
          this.plugin.spellOutNumbers = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Multiplication sign')
      .setDesc('Replace x between numbers with \u00D7 (e.g., 3x5 \u2192 3\u00D75).')
      .addToggle(toggle => toggle
        .setValue(this.plugin.multiplicationSign)
        .onChange(async (value) => {
          this.plugin.multiplicationSign = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Blank line before headings')
      .setDesc('Insert a blank line before headings that don\u2019t have one.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.blankBeforeHeadings)
        .onChange(async (value) => {
          this.plugin.blankBeforeHeadings = value;
          await this.plugin.saveSettings();
        })
      );


    const toggleDateDeps = (value) => {
      dateInputSetting.settingEl.style.display = value ? '' : 'none';
      dateOutputSetting.settingEl.style.display = value ? '' : 'none';
    };

    new obsidian.Setting(containerEl)
      .setName('Auto-format dates')
      .setDesc('Normalize dates to a consistent format as you type.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.autoFormatDates)
        .onChange(async (value) => {
          this.plugin.autoFormatDates = value;
          await this.plugin.saveSettings();
          toggleDateDeps(value);
        })
      );

    const dateInputSetting = new obsidian.Setting(containerEl)
      .setName('Date input format')
      .setDesc('How to interpret slash-separated dates (e.g. 3/5/2026).')
      .addDropdown(dropdown => dropdown
        .addOption('us', 'US: MM/DD/YYYY')
        .addOption('eu', 'EU: DD/MM/YYYY')
        .setValue(this.plugin.dateInputUS ? 'us' : 'eu')
        .onChange(async (value) => {
          this.plugin.dateInputUS = value === 'us';
          await this.plugin.saveSettings();
        })
      );

    const dateOutputSetting = new obsidian.Setting(containerEl)
      .setName('Date output format')
      .setDesc('Format for the normalized date.')
      .addDropdown(dropdown => dropdown
        .addOption('DD/MM/YYYY', 'DD/MM/YYYY')
        .addOption('MM/DD/YYYY', 'MM/DD/YYYY')
        .addOption('YYYY-MM-DD', 'YYYY-MM-DD')
        .addOption('DD-MM-YYYY', 'DD-MM-YYYY')
        .addOption('DD.MM.YYYY', 'DD.MM.YYYY')
        .setValue(this.plugin.dateOutputFormat)
        .onChange(async (value) => {
          this.plugin.dateOutputFormat = value;
          await this.plugin.saveSettings();
        })
      );
    toggleDateDeps(this.plugin.autoFormatDates);

    const toggleShortcutDeps = (value) => {
      this._shortcutPreviewEl.style.display = value ? '' : 'none';
      editShortcutsSetting.settingEl.style.display = value ? '' : 'none';
    };

    new obsidian.Setting(containerEl)
      .setName('Text shortcuts')
      .setDesc('Replace typed strings with substitutions (triggers on space/punctuation).')
      .addToggle(toggle => toggle
        .setValue(this.plugin.shortcuts)
        .onChange(async (value) => {
          this.plugin.shortcuts = value;
          await this.plugin.saveSettings();
          toggleShortcutDeps(value);
        })
      );

    // Shortcut categories preview
    this._shortcutPreviewEl = containerEl.createDiv({ cls: 'iris-shortcut-categories' });
    this.renderShortcutPreview();

    const editShortcutsSetting = new obsidian.Setting(containerEl)
      .setName('Edit shortcuts')
      .setDesc('One per line: shortcut = replacement. Lines starting with # are category headers.')
      .addTextArea(text => {
        this._shortcutTextArea = text;
        text.inputEl.rows = 8;
        text.inputEl.cols = 30;
        text
          .setValue(this.plugin.shortcutList)
          .onChange(async (value) => {
            this.plugin.shortcutList = value;
            this.plugin.parseShortcuts();
            await this.plugin.saveSettings();
            this.renderShortcutPreview();
          });
      })
      .addButton(button => button
        .setButtonText('Reset to defaults')
        .onClick(async () => {
          if (!confirm('Reset all shortcuts to defaults? Custom shortcuts will be lost.')) return;
          this.plugin.shortcutList = DEFAULT_SHORTCUTS;
          this.plugin.parseShortcuts();
          await this.plugin.saveSettings();
          if (this._shortcutTextArea) this._shortcutTextArea.setValue(DEFAULT_SHORTCUTS);
          this.renderShortcutPreview();
        })
      );
    toggleShortcutDeps(this.plugin.shortcuts);

    new obsidian.Setting(containerEl).setName('Auto-linking options').setHeading();


    new obsidian.Setting(containerEl)
      .setName('Link to folder')
      .setDesc('Only use notes inside this folder as link targets. Leave empty for all notes.')
      .addText(text => text
        .setPlaceholder('e.g. Glossary')
        .setValue(this.plugin.folder)
        .onChange(async (value) => {
          this.plugin.folder = value.trim();
          await this.plugin.saveSettings();
          this.plugin.refreshNoteNames();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Link from folder')
      .setDesc('Only autolink inside files in this folder. Leave empty for all files.')
      .addText(text => text
        .setPlaceholder('e.g. Notes')
        .setValue(this.plugin.linkFrom)
        .onChange(async (value) => {
          this.plugin.linkFrom = value.trim();
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName("Don't link to folder")
      .setDesc('Exclude notes in this folder from being link targets.')
      .addText(text => text
        .setPlaceholder('e.g. Templates')
        .setValue(this.plugin.excludeToFolder)
        .onChange(async (value) => {
          this.plugin.excludeToFolder = value.trim();
          await this.plugin.saveSettings();
          this.plugin.refreshNoteNames();
        })
      );

    new obsidian.Setting(containerEl)
      .setName("Don't link from folder")
      .setDesc('Never autolink inside files in this folder.')
      .addText(text => text
        .setPlaceholder('e.g. Archive')
        .setValue(this.plugin.excludeFromFolder)
        .onChange(async (value) => {
          this.plugin.excludeFromFolder = value.trim();
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Link short names')
      .setDesc('Allow linking single-character (e.g. "I", "X") and pure-number (e.g. "5") note names.')
      .addToggle(toggle => toggle
        .setValue(this.plugin.linkShortNames)
        .onChange(async (value) => {
          this.plugin.linkShortNames = value;
          await this.plugin.saveSettings();
        })
      );

    new obsidian.Setting(containerEl)
      .setName('Extra alias keys')
      .setDesc('Additional frontmatter keys to check for aliases (comma-separated).')
      .addText(text => text
        .setPlaceholder('e.g. aliases2, abbreviations')
        .setValue(this.plugin.extraAliasKeys)
        .onChange(async (value) => {
          this.plugin.extraAliasKeys = value.trim();
          await this.plugin.saveSettings();
          this.plugin.refreshNoteNames();
        })
      );
  }

  renderShortcutPreview() {
    const el = this._shortcutPreviewEl;
    if (!el) return;
    el.empty();

    const categories = [];
    let current = { name: 'Uncategorized', items: [] };

    for (const line of (this.plugin.shortcutList || '').split('\n')) {
      const trimmed = line.trim();
      if (!trimmed) continue;
      if (trimmed.startsWith('#')) {
        if (current.items.length > 0 || categories.length > 0) categories.push(current);
        current = { name: trimmed.substring(1).trim(), items: [] };
        continue;
      }
      let idx = trimmed.indexOf(' = ');
      if (idx <= 0 && trimmed.endsWith(' =')) idx = trimmed.length - 2;
      if (idx > 0) {
        current.items.push({
          shortcut: trimmed.substring(0, idx),
          replacement: idx + 3 <= trimmed.length ? trimmed.substring(idx + 3) : '',
        });
      }
    }
    if (current.items.length > 0) categories.push(current);

    for (const cat of categories) {
      const details = el.createEl('details', { cls: 'iris-shortcut-group' });
      details.createEl('summary', { text: cat.name + ' (' + cat.items.length + ')' });
      const table = details.createEl('table', { cls: 'iris-shortcut-table' });
      for (const item of cat.items) {
        const row = table.createEl('tr');
        row.createEl('td', { text: item.shortcut, cls: 'iris-shortcut-key' });
        row.createEl('td', { text: '\u2192' });
        row.createEl('td', { text: item.replacement, cls: 'iris-shortcut-value' });
      }
    }
  }
}

module.exports = IrisEditorPlugin;
