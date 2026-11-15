/* ==========================================================================
   SUDOKU ENGINE & STATE MANAGEMENT (SUDOKU SIMBA)
   ========================================================================== */
let board = [];
let solution = [];
let initialBoard = [];
let notes = [];
let undoStack = [];
let redoStack = [];

let selectedCell = null;
let isNotesMode = false;
let isPaused = false;
let isGameOver = false;

let difficulty = 'medium';
let gameMode = 'classic';
let mistakes = 0;
const MAX_MISTAKES = 3;
let score = 0;
let hintsRemaining = 3;
let secondsElapsed = 0;
let countdownLimit = 0;
let timerInterval = null;

let settings = {
    theme: 'paper',
    errorCap: true,
    autoUndoError: false,
    highlight: true,
    hideUsed: true,
    smartHint: true,
    sound: true
};

let stats = {
    gamesPlayed: 0,
    gamesWon: 0,
    bestTime: { easy: null, medium: null, hard: null, expert: null },
    dailyCompleted: []
};

const DIFFICULTY_LABELS = {
    easy: 'سهل',
    medium: 'متوسط',
    hard: 'صعب',
    expert: 'خبير',
    daily: 'التحدي اليومي',
    custom: 'تحديّ الخاص',
    speed: 'تحدي الزمن'
};

const CLUES_COUNT = {
    easy: 42,
    medium: 35,
    hard: 28,
    expert: 23
};

/* ==========================================================================
   SOUND SYNTHESIZER
   ========================================================================== */
let synth = null;
function playSound(type) {
    if (!settings.sound) return;
    try {
        if (!synth) {
            synth = new Tone.PolySynth(Tone.Synth).toDestination();
            synth.volume.value = -10;
        }
        if (Tone.context.state !== 'running') Tone.start();

        const now = Tone.now();
        if (type === 'tap') synth.triggerAttackRelease('C5', '32n', now);
        else if (type === 'place') synth.triggerAttackRelease('E5', '16n', now);
        else if (type === 'note') synth.triggerAttackRelease('G4', '32n', now);
        else if (type === 'error') synth.triggerAttackRelease(['C3', 'Db3'], '8n', now);
        else if (type === 'complete') synth.triggerAttackRelease(['C5', 'E5', 'G5', 'B5'], '8n', now);
        else if (type === 'win') {
            synth.triggerAttackRelease('C5', '8n', now);
            synth.triggerAttackRelease('E5', '8n', now + 0.12);
            synth.triggerAttackRelease('G5', '8n', now + 0.24);
            synth.triggerAttackRelease('C6', '4n', now + 0.36);
        }
    } catch (e) {}
}

/* ==========================================================================
   SUDOKU GENERATOR & SOLVER ALGORITHM
   ========================================================================== */
function generateSolvedBoard(seedRng = Math.random) {
    const grid = Array.from({ length: 9 }, () => Array(9).fill(0));

    function isValid(g, row, col, num) {
        for (let x = 0; x < 9; x++) {
            if (g[row][x] === num || g[x][col] === num) return false;
        }
        const startRow = row - (row % 3);
        const startCol = col - (col % 3);
        for (let i = 0; i < 3; i++) {
            for (let j = 0; j < 3; j++) {
                if (g[i + startRow][j + startCol] === num) return false;
            }
        }
        return true;
    }

    function fillGrid(g) {
        for (let row = 0; row < 9; row++) {
            for (let col = 0; col < 9; col++) {
                if (g[row][col] === 0) {
                    const nums = [1, 2, 3, 4, 5, 6, 7, 8, 9];
                    for (let i = nums.length - 1; i > 0; i--) {
                        const j = Math.floor(seedRng() * (i + 1));
                        [nums[i], nums[j]] = [nums[j], nums[i]];
                    }
                    for (let num of nums) {
                        if (isValid(g, row, col, num)) {
                            g[row][col] = num;
                            if (fillGrid(g)) return true;
                            g[row][col] = 0;
                        }
                    }
                    return false;
                }
            }
        }
        return true;
    }

    fillGrid(grid);
    return grid;
}

function solveBoard(inputGrid) {
    const g = inputGrid.map(row => [...row]);
    function isValid(row, col, num) {
        for (let x = 0; x < 9; x++) {
            if (g[row][x] === num || g[x][col] === num) return false;
        }
        const sr = row - (row % 3), sc = col - (col % 3);
        for (let i = 0; i < 3; i++)
            for (let j = 0; j < 3; j++)
                if (g[sr + i][sc + j] === num) return false;
        return true;
    }
    function solve() {
        for (let r = 0; r < 9; r++) {
            for (let c = 0; c < 9; c++) {
                if (g[r][c] === 0) {
                    for (let n = 1; n <= 9; n++) {
                        if (isValid(r, c, n)) {
                            g[r][c] = n;
                            if (solve()) return true;
                            g[r][c] = 0;
                        }
                    }
                    return false;
                }
            }
        }
        return true;
    }
    return solve() ? g : null;
}

function createPuzzle(diff, seedRng = Math.random) {
    const solved = generateSolvedBoard(seedRng);
    const puzzle = solved.map(row => [...row]);
    const clues = CLUES_COUNT[diff] || 35;
    let cellsToRemove = 81 - clues;

    const positions = [];
    for (let r = 0; r < 9; r++) {
        for (let c = 0; c < 9; c++) {
            positions.push([r, c]);
        }
    }
    for (let i = positions.length - 1; i > 0; i--) {
        const j = Math.floor(seedRng() * (i + 1));
        [positions[i], positions[j]] = [positions[j], positions[i]];
    }

    for (let [r, c] of positions) {
        if (cellsToRemove <= 0) break;
        puzzle[r][c] = 0;
        cellsToRemove--;
    }

    return { puzzle, solution: solved };
}

/* ==========================================================================
   GAME INITIALIZATION & MODES
   ========================================================================== */
function startNewGame(diff = 'medium', mode = 'classic') {
    difficulty = diff;
    gameMode = mode;
    const { puzzle, solution: sol } = createPuzzle(diff);

    setupBoardState(puzzle, sol);
    closeModal('homeModal');
    saveGameState();
}

function startDailyChallenge() {
    const today = new Date();
    const seed = today.getFullYear() * 10000 + (today.getMonth() + 1) * 100 + today.getDate();
    let s = seed;
    const seededRng = () => {
        s = Math.sin(s) * 10000;
        return s - Math.floor(s);
    };

    difficulty = 'hard';
    gameMode = 'daily';
    const { puzzle, solution: sol } = createPuzzle('hard', seededRng);
    setupBoardState(puzzle, sol);
    closeModal('homeModal');
    saveGameState();
}

function openMyChallengeBuilder() {
    closeModal('homeModal');
    openModal('myChallengeModal');
}

function startSpeedChallenge() {
    difficulty = 'easy';
    gameMode = 'speed';
    countdownLimit = 180;
    const { puzzle, solution: sol } = createPuzzle('easy');
    setupBoardState(puzzle, sol);
    closeModal('myChallengeModal');
    saveGameState();
}

function setupBoardState(puzzle, sol) {
    initialBoard = puzzle.map(r => [...r]);
    board = puzzle.map(r => [...r]);
    solution = sol.map(r => [...r]);
    notes = Array.from({ length: 9 }, () => Array.from({ length: 9 }, () => new Set()));

    undoStack = [];
    redoStack = [];
    selectedCell = null;
    mistakes = 0;
    score = 0;
    hintsRemaining = 3;
    secondsElapsed = 0;
    isPaused = false;
    isGameOver = false;

    document.getElementById('pauseOverlay').classList.add('hidden');
    document.getElementById('pauseIcon').className = 'fas fa-pause text-xs';
    hideSmartBanner();
    updateUIHeaders();
    renderGrid();
    renderNumpad();
    startTimer();
}

/* ==========================================================================
   RENDERING ENGINE
   ========================================================================== */
function renderGrid() {
    const gridEl = document.getElementById('sudokuGrid');
    gridEl.innerHTML = '';

    const selVal = selectedCell ? board[selectedCell.r][selectedCell.c] : null;

    for (let r = 0; r < 9; r++) {
        for (let c = 0; c < 9; c++) {
            const cell = document.createElement('div');
            cell.className = 'sudoku-cell num-font text-xl sm:text-2xl';
            cell.dataset.r = r;
            cell.dataset.c = c;

            const val = board[r][c];
            const isFixed = initialBoard[r][c] !== 0;

            if (selectedCell) {
                const isSameCell = selectedCell.r === r && selectedCell.c === c;
                const isSameRowOrCol = selectedCell.r === r || selectedCell.c === c;
                const isSameBox = Math.floor(selectedCell.r / 3) === Math.floor(r / 3) &&
                                  Math.floor(selectedCell.c / 3) === Math.floor(c / 3);

                if (isSameCell) {
                    cell.classList.add('cell-selected');
                } else if (settings.highlight) {
                    if (selVal !== 0 && val === selVal) {
                        cell.classList.add('cell-same-num');
                    } else if (isSameRowOrCol || isSameBox) {
                        cell.classList.add('cell-related');
                    }
                }
            }

            if (val !== 0) {
                cell.textContent = val;
                if (isFixed) {
                    cell.classList.add('cell-fixed');
                } else {
                    cell.classList.add('cell-user');
                    if (val !== solution[r][c]) {
                        cell.classList.add('cell-error');
                    }
                }
            } else if (notes[r][c].size > 0) {
                const notesContainer = document.createElement('div');
                notesContainer.className = 'notes-grid';
                for (let n = 1; n <= 9; n++) {
                    const noteSpan = document.createElement('span');
                    noteSpan.className = 'note-item num-font';
                    if (notes[r][c].has(n)) {
                        noteSpan.textContent = n;
                        if (selVal === n && settings.highlight) {
                            noteSpan.classList.add('note-highlight');
                        }
                    }
                    notesContainer.appendChild(noteSpan);
                }
                cell.appendChild(notesContainer);
            }

            cell.addEventListener('click', () => selectCell(r, c));
            gridEl.appendChild(cell);
        }
    }
}

function renderNumpad() {
    const numpadEl = document.getElementById('numpad');
    numpadEl.innerHTML = '';

    const counts = Array(10).fill(0);
    for (let r = 0; r < 9; r++) {
        for (let c = 0; c < 9; c++) {
            const v = board[r][c];
            if (v !== 0 && v === solution[r][c]) {
                counts[v]++;
            }
        }
    }

    for (let n = 1; n <= 9; n++) {
        const remaining = 9 - counts[n];
        const btn = document.createElement('button');
        btn.className = 'flex flex-col items-center justify-center py-2 sm:py-2.5 rounded-xl card-surface shadow-sm hover:opacity-80 active:scale-95 transition';

        if (remaining <= 0 && settings.hideUsed) {
            btn.style.visibility = 'hidden';
        }

        btn.innerHTML = `
            <span class="num-font text-xl sm:text-2xl font-extrabold" style="color: var(--accent);">${n}</span>
            <span class="num-font text-[10px] font-bold" style="color: var(--text-secondary);">${remaining > 0 ? remaining : ''}</span>
        `;
        btn.addEventListener('click', () => handleNumberInput(n));
        numpadEl.appendChild(btn);
    }
}

function updateUIHeaders() {
    const label = gameMode === 'classic' ? DIFFICULTY_LABELS[difficulty] : DIFFICULTY_LABELS[gameMode];
    document.getElementById('modeBadge').textContent = `الوضع: ${label}`;

    const mistakesContainer = document.getElementById('mistakesContainer');
    mistakesContainer.style.display = 'flex';
    if (settings.errorCap) {
        document.getElementById('mistakesDisplay').textContent = `${mistakes}/${MAX_MISTAKES}`;
    } else {
        document.getElementById('mistakesDisplay').textContent = `${mistakes}`;
    }

    document.getElementById('scoreDisplay').textContent = score;
    document.getElementById('hintCountBadge').textContent = hintsRemaining;
}

/* ==========================================================================
   INTERACTION & GAMEPLAY MECHANICS
   ========================================================================== */
function selectCell(r, c) {
    if (isPaused || isGameOver) return;
    selectedCell = { r, c };
    playSound('tap');
    renderGrid();
    checkIntelligentHint(r, c);
}

function checkIntelligentHint(r, c) {
    if (!settings.smartHint || board[r][c] !== 0) {
        hideSmartBanner();
        return;
    }

    let rowEmpty = 0, colEmpty = 0, boxEmpty = 0;
    for (let i = 0; i < 9; i++) {
        if (board[r][i] === 0) rowEmpty++;
        if (board[i][c] === 0) colEmpty++;
    }
    const sr = r - (r % 3), sc = c - (c % 3);
    for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
            if (board[sr + i][sc + j] === 0) boxEmpty++;
        }
    }

    if (rowEmpty === 1 || colEmpty === 1 || boxEmpty === 1) {
        const area = rowEmpty === 1 ? 'هذا الصف' : (colEmpty === 1 ? 'هذا العمود' : 'هذا المربع 3×3');
        const ans = solution[r][c];
        showSmartBanner(`تلميح ذكي: هذه آخر خانة فارغة في ${area}! الرقم المفقود هو (${ans}).`);
    } else {
        hideSmartBanner();
    }
}

function showSmartBanner(text) {
    const banner = document.getElementById('smartBanner');
    document.getElementById('smartBannerText').textContent = text;
    banner.classList.remove('hidden');
}

function hideSmartBanner() {
    document.getElementById('smartBanner').classList.add('hidden');
}

function handleNumberInput(num) {
    if (!selectedCell || isPaused || isGameOver) return;
    const { r, c } = selectedCell;

    if (initialBoard[r][c] !== 0 || board[r][c] === solution[r][c]) return;

    pushHistory();

    if (isNotesMode) {
        if (board[r][c] !== 0) board[r][c] = 0;
        if (notes[r][c].has(num)) {
            notes[r][c].delete(num);
        } else {
            notes[r][c].add(num);
        }
        playSound('note');
        renderGrid();
        saveGameState();
        return;
    }

    board[r][c] = num;
    notes[r][c].clear();

    if (num === solution[r][c]) {
        playSound('place');
        score += 50;
        removeRelatedNotes(r, c, num);
        checkRowColBoxCompletion(r, c);
        hideSmartBanner();
        renderGrid();
        renderNumpad();
        updateUIHeaders();
        saveGameState();
        checkWinCondition();
    } else {
        playSound('error');
        mistakes++;
        score = Math.max(0, score - 25);
        updateUIHeaders();
        renderGrid();

        if (settings.autoUndoError) {
            setTimeout(() => {
                board[r][c] = 0;
                renderGrid();
                saveGameState();
            }, 450);
        } else {
            saveGameState();
        }

        if (settings.errorCap && mistakes >= MAX_MISTAKES) {
            triggerGameOver(false, 'لقد تجاوزت الحد المسموح به من الأخطاء (3/3)!');
        }
    }
}

function removeRelatedNotes(r, c, num) {
    for (let i = 0; i < 9; i++) {
        notes[r][i].delete(num);
        notes[i][c].delete(num);
    }
    const sr = r - (r % 3), sc = c - (c % 3);
    for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
            notes[sr + i][sc + j].delete(num);
        }
    }
}

function checkRowColBoxCompletion(r, c) {
    let rowDone = true, colDone = true, boxDone = true;
    for (let i = 0; i < 9; i++) {
        if (board[r][i] !== solution[r][i]) rowDone = false;
        if (board[i][c] !== solution[i][c]) colDone = false;
    }
    const sr = r - (r % 3), sc = c - (c % 3);
    for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
            if (board[sr + i][sc + j] !== solution[sr + i][sc + j]) boxDone = false;
        }
    }

    if (rowDone || colDone || boxDone) {
        playSound('complete');
        score += 100;
        const cells = document.querySelectorAll('.sudoku-cell');
        cells.forEach(cell => {
            const cr = parseInt(cell.dataset.r);
            const cc = parseInt(cell.dataset.c);
            const inBox = Math.floor(cr / 3) === Math.floor(r / 3) && Math.floor(cc / 3) === Math.floor(c / 3);
            if ((rowDone && cr === r) || (colDone && cc === c) || (boxDone && inBox)) {
                cell.classList.add('animate-flash');
            }
        });
    }
}

function eraseCell() {
    if (!selectedCell || isPaused || isGameOver) return;
    const { r, c } = selectedCell;
    if (initialBoard[r][c] !== 0 || board[r][c] === solution[r][c]) return;

    if (board[r][c] !== 0 || notes[r][c].size > 0) {
        pushHistory();
        board[r][c] = 0;
        notes[r][c].clear();
        playSound('tap');
        renderGrid();
        renderNumpad();
        saveGameState();
    }
}

function toggleNotesMode() {
    isNotesMode = !isNotesMode;
    const btn = document.getElementById('notesBtn');
    const badge = document.getElementById('notesBadge');
    if (isNotesMode) {
        badge.textContent = 'ON';
        badge.className = 'absolute top-1 left-1 text-[9px] px-1.5 py-0.2 rounded-full font-bold bg-blue-600 text-white';
        btn.style.borderColor = 'var(--accent)';
    } else {
        badge.textContent = 'OFF';
        badge.className = 'absolute top-1 left-1 text-[9px] px-1.5 py-0.2 rounded-full font-bold bg-slate-200 text-slate-700';
        btn.style.borderColor = 'var(--cell-border)';
    }
    playSound('tap');
}

function useHint() {
    if (isPaused || isGameOver) return;

    let target = selectedCell;
    if (!target || board[target.r][target.c] === solution[target.r][target.c]) {
        for (let r = 0; r < 9; r++) {
            for (let c = 0; c < 9; c++) {
                if (board[r][c] !== solution[r][c]) {
                    target = { r, c };
                    break;
                }
            }
            if (target && board[target.r][target.c] !== solution[target.r][target.c]) break;
        }
    }

    if (!target) return;

    if (hintsRemaining <= 0) {
        hintsRemaining = 1;
        showSmartBanner('تم منحك تلميحاً إضافياً مجانياً!');
    }

    hintsRemaining--;
    selectedCell = target;
    pushHistory();
    board[target.r][target.c] = solution[target.r][target.c];
    notes[target.r][target.c].clear();
    removeRelatedNotes(target.r, target.c, solution[target.r][target.c]);

    playSound('complete');
    updateUIHeaders();
    renderGrid();
    renderNumpad();
    saveGameState();
    checkWinCondition();
}

/* ==========================================================================
   UNDO / REDO SYSTEM
   ========================================================================== */
function cloneState() {
    return {
        board: board.map(r => [...r]),
        notes: notes.map(r => r.map(s => new Set(s)))
    };
}

function pushHistory() {
    undoStack.push(cloneState());
    redoStack = [];
}

function undo() {
    if (undoStack.length === 0 || isPaused || isGameOver) return;
    redoStack.push(cloneState());
    const prev = undoStack.pop();
    board = prev.board;
    notes = prev.notes;
    playSound('tap');
    renderGrid();
    renderNumpad();
    saveGameState();
}

function redo() {
    if (redoStack.length === 0 || isPaused || isGameOver) return;
    undoStack.push(cloneState());
    const next = redoStack.pop();
    board = next.board;
    notes = next.notes;
    playSound('tap');
    renderGrid();
    renderNumpad();
    saveGameState();
}

/* ==========================================================================
   TIMER, WIN & GAME OVER LOGIC
   ========================================================================== */
function startTimer() {
    clearInterval(timerInterval);
    timerInterval = setInterval(() => {
        if (!isPaused && !isGameOver) {
            secondsElapsed++;
            updateTimerDisplay();

            if (gameMode === 'speed' && secondsElapsed >= countdownLimit) {
                triggerGameOver(false, 'انتهى وقت تحدي السرعة (3 دقائق)!');
            }
        }
    }, 1000);
}

function updateTimerDisplay() {
    const displaySec = gameMode === 'speed' ? Math.max(0, countdownLimit - secondsElapsed) : secondsElapsed;
    const mins = String(Math.floor(displaySec / 60)).padStart(2, '0');
    const secs = String(displaySec % 60).padStart(2, '0');
    document.getElementById('timerDisplay').textContent = `${mins}:${secs}`;
}

function togglePause() {
    if (isGameOver) return;
    isPaused = !isPaused;
    const overlay = document.getElementById('pauseOverlay');
    const icon = document.getElementById('pauseIcon');
    if (isPaused) {
        overlay.classList.remove('hidden');
        icon.className = 'fas fa-play text-xs';
    } else {
        overlay.classList.add('hidden');
        icon.className = 'fas fa-pause text-xs';
    }
}

function checkWinCondition() {
    for (let r = 0; r < 9; r++) {
        for (let c = 0; c < 9; c++) {
            if (board[r][c] !== solution[r][c]) return;
        }
    }
    triggerGameOver(true);
}

function triggerGameOver(isWin, customMsg = '') {
    isGameOver = true;
    clearInterval(timerInterval);
    localStorage.removeItem('sudoku_simba_autosave');

    stats.gamesPlayed++;
    if (isWin) {
        playSound('win');
        stats.gamesWon++;
        if (['easy', 'medium', 'hard', 'expert'].includes(difficulty)) {
            const prevBest = stats.bestTime[difficulty];
            if (!prevBest || secondsElapsed < prevBest) {
                stats.bestTime[difficulty] = secondsElapsed;
            }
        }
        if (gameMode === 'daily') {
            const todayKey = new Date().toISOString().slice(0, 10);
            if (!stats.dailyCompleted.includes(todayKey)) {
                stats.dailyCompleted.push(todayKey);
            }
        }
    }
    saveStats();

    document.getElementById('endGameIcon').innerHTML = isWin
        ? `<img src="images/trophy.svg" alt="Win" class="w-16 h-16">`
        : `<img src="images/gameover.svg" alt="Game Over" class="w-16 h-16">`;
    document.getElementById('endGameTitle').textContent = isWin ? 'تهانينا! لقد فزت' : 'انتهت اللعبة';
    document.getElementById('endGameSubtitle').textContent = isWin
        ? 'أداء ذهني رائع! لقد حللت جميع الأرقام بدقة.'
        : customMsg;

    document.getElementById('endTime').textContent = document.getElementById('timerDisplay').textContent;
    document.getElementById('endScore').textContent = score;
    document.getElementById('endDiff').textContent = DIFFICULTY_LABELS[difficulty] || difficulty;

    const secondChanceBtn = document.getElementById('secondChanceBtn');
    if (!isWin && mistakes >= MAX_MISTAKES) {
        secondChanceBtn.classList.remove('hidden');
    } else {
        secondChanceBtn.classList.add('hidden');
    }

    openModal('endGameModal');
}

function useSecondChance() {
    mistakes = MAX_MISTAKES - 1;
    isGameOver = false;
    closeModal('endGameModal');
    updateUIHeaders();
    startTimer();
}

/* ==========================================================================
   SETTINGS, THEMES, AUTOSAVE & KEYBOARD CONTROLS
   ========================================================================== */
function setTheme(themeName) {
    settings.theme = themeName;
    document.documentElement.setAttribute('data-theme', themeName);
    saveSettings();
    closeModal('themeModal');
}

function toggleSetting(key) {
    settings[key] = !settings[key];
    saveSettings();
    updateUIHeaders();
    renderGrid();
    renderNumpad();
}

function syncSettingsUI() {
    document.documentElement.setAttribute('data-theme', settings.theme);
    document.getElementById('optErrorCap').checked = settings.errorCap;
    document.getElementById('optAutoUndoError').checked = settings.autoUndoError;
    document.getElementById('optHighlight').checked = settings.highlight;
    document.getElementById('optHideUsed').checked = settings.hideUsed;
    document.getElementById('optSmartHint').checked = settings.smartHint;
    document.getElementById('optSound').checked = settings.sound;
}

function saveSettings() {
    localStorage.setItem('sudoku_simba_settings', JSON.stringify(settings));
}

function saveStats() {
    localStorage.setItem('sudoku_simba_stats', JSON.stringify(stats));
}

function saveGameState() {
    if (isGameOver) return;
    const payload = {
        board,
        solution,
        initialBoard,
        notes: notes.map(r => r.map(s => Array.from(s))),
        difficulty,
        gameMode,
        mistakes,
        score,
        hintsRemaining,
        secondsElapsed,
        countdownLimit
    };
    localStorage.setItem('sudoku_simba_autosave', JSON.stringify(payload));
}

function loadSavedData() {
    try {
        const savedSettings = localStorage.getItem('sudoku_simba_settings');
        if (savedSettings) settings = { ...settings, ...JSON.parse(savedSettings) };

        const savedStats = localStorage.getItem('sudoku_simba_stats');
        if (savedStats) stats = { ...stats, ...JSON.parse(savedStats) };
    } catch (e) {}

    syncSettingsUI();

    try {
        const autosave = localStorage.getItem('sudoku_simba_autosave');
        if (autosave) {
            const data = JSON.parse(autosave);
            board = data.board;
            solution = data.solution;
            initialBoard = data.initialBoard;
            notes = data.notes.map(r => r.map(arr => new Set(arr)));
            difficulty = data.difficulty || 'medium';
            gameMode = data.gameMode || 'classic';
            mistakes = data.mistakes || 0;
            score = data.score || 0;
            hintsRemaining = data.hintsRemaining ?? 3;
            secondsElapsed = data.secondsElapsed || 0;
            countdownLimit = data.countdownLimit || 0;

            updateUIHeaders();
            updateTimerDisplay();
            renderGrid();
            renderNumpad();
            startTimer();
            return;
        }
    } catch (e) {}

    startNewGame('medium', 'classic');
}

function openModal(id) {
    if (id === 'statsModal') renderStatsModal();
    document.getElementById(id).classList.remove('hidden');
}

function closeModal(id) {
    document.getElementById(id).classList.add('hidden');
}

function renderStatsModal() {
    const winRate = stats.gamesPlayed > 0 ? Math.round((stats.gamesWon / stats.gamesPlayed) * 100) : 0;
    const formatT = (sec) => {
        if (!sec) return '--:--';
        return `${String(Math.floor(sec / 60)).padStart(2, '0')}:${String(sec % 60).padStart(2, '0')}`;
    };

    document.getElementById('statsContent').innerHTML = `
        <div class="p-3 rounded-xl" style="background-color: var(--bg-main);">
            <div class="text-xs" style="color: var(--text-secondary);">المباريات الملعوبة</div>
            <div class="text-xl font-extrabold num-font mt-1">${stats.gamesPlayed}</div>
        </div>
        <div class="p-3 rounded-xl" style="background-color: var(--bg-main);">
            <div class="text-xs" style="color: var(--text-secondary);">نسبة الفوز</div>
            <div class="text-xl font-extrabold num-font mt-1 text-emerald-600">${winRate}%</div>
        </div>
        <div class="p-3 rounded-xl" style="background-color: var(--bg-main);">
            <div class="text-xs" style="color: var(--text-secondary);">أفضل وقت (سهل / متوسط)</div>
            <div class="text-sm font-extrabold num-font mt-1">${formatT(stats.bestTime.easy)} / ${formatT(stats.bestTime.medium)}</div>
        </div>
        <div class="p-3 rounded-xl" style="background-color: var(--bg-main);">
            <div class="text-xs" style="color: var(--text-secondary);">أفضل وقت (صعب / خبير)</div>
            <div class="text-sm font-extrabold num-font mt-1">${formatT(stats.bestTime.hard)} / ${formatT(stats.bestTime.expert)}</div>
        </div>
    `;
    document.getElementById('dailyStreakText').textContent = `أكملت ${stats.dailyCompleted.length} تحديات يومية بنجاح.`;
}

document.addEventListener('keydown', (e) => {
    if (isPaused || isGameOver) return;
    if (e.key >= '1' && e.key <= '9') {
        handleNumberInput(parseInt(e.key, 10));
    } else if (e.key === 'Backspace' || e.key === 'Delete') {
        eraseCell();
    } else if (e.key.toLowerCase() === 'n') {
        toggleNotesMode();
    } else if (selectedCell && ['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.key)) {
        e.preventDefault();
        let { r, c } = selectedCell;
        if (e.key === 'ArrowUp') r = (r + 8) % 9;
        if (e.key === 'ArrowDown') r = (r + 1) % 9;
        if (e.key === 'ArrowLeft') c = (c + 8) % 9;
        if (e.key === 'ArrowRight') c = (c + 1) % 9;
        selectCell(r, c);
    }
});

window.onload = function () {
    const todayStr = new Date().toLocaleDateString('ar-EG', { day: 'numeric', month: 'long' });
    document.getElementById('dailyDateText').textContent = todayStr;
    loadSavedData();
};