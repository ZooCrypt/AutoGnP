/// <reference path="ace.d.ts" />
var enable_debug = false;

function log(s) {
    if (enable_debug) {
        console.log(s);
    }
}
var webSocket = new WebSocket("ws://127.0.0.1:9999/");

// editorProof has been processed up to this character
var firstUnlocked = 0;
var originalLockedText = "";

function lockedText() {
    return editorProof.getValue().substring(0, firstUnlocked);
}

var editorProof = ace.edit("editor-proof");
editorProof.setTheme("ace/theme/eclipse");
editorProof.setHighlightActiveLine(false);
editorProof.focus();

editorProof.getSession().getDocument().on("change", function (ev) {
    var lt = lockedText();
    log("lt: ''" + lt + "''");
    log("oldLt: ''" + originalLockedText + "''");
    if (lt == originalLockedText) {
        // console.log("changed, but locked unchanged");
    } else {
        // console.log("locked changed");
        // search for the last dot that is the common prefix of
        // old and new content of locked region
        var lastDot = 0;
        for (var i = 0; i < Math.min(lt.length, originalLockedText.length); i++) {
            if (lt.charAt(i) !== originalLockedText.charAt(i)) {
                break;
            }
            if (lt.charAt(i) == '.') {
                lastDot = i;
            }
        }
        var pos = editorProof.getCursorPosition();
        setFirstUnlocked(lastDot + 1);
        evalLocked();
        editorProof.moveCursorToPosition(pos);
    }
});

var editorGoal = ace.edit("editor-goal");
editorGoal.setTheme("ace/theme/eclipse");
editorGoal.setHighlightActiveLine(false);

// send json request to zoocrypt websocket server
function sendZoocrypt(m) {
    webSocket.send(JSON.stringify(m));
}

// Request proof script
webSocket.onopen = function (evt) {
    sendZoocrypt({ 'cmd': 'load', 'arg': '' });
};

// handle websocket answers
webSocket.onmessage = function (evt) {
    log(evt.data);
    var m = JSON.parse(evt.data);

    if (m.cmd == 'setGoal') {
        editorGoal.setValue(m.arg);
        editorGoal.clearSelection();
        // answer for load
    } else if (m.cmd == 'setProof') {
        editorProof.setValue(m.arg);
        editorProof.clearSelection();
        editorProof.scrollPageUp();
    }
};

var lastMarker;

function evalLocked() {
    var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
    editorProof.moveCursorToPosition(pos);
    editorProof.clearSelection();
    var Range = ace.require('ace/range').Range;
    if (lastMarker) {
        editorProof.getSession().removeMarker(lastMarker);
    }
    ;
    lastMarker = editorProof.getSession().addMarker(new Range(0, 0, pos.row, pos.column), 'locked', 'word', false);
    if (lockedText() !== "") {
        sendZoocrypt({ 'cmd': 'eval', 'arg': lockedText() });
    }
}

function setFirstUnlocked(i) {
    firstUnlocked = i;
    originalLockedText = lockedText();
}

function evalNext() {
    var nextDot = editorProof.getValue().indexOf(".", firstUnlocked);
    if (nextDot > firstUnlocked) {
        setFirstUnlocked(nextDot + 1);
        evalLocked();
    }
}

function evalPrev() {
    var prevDot = editorProof.getValue().lastIndexOf(".", Math.max(0, firstUnlocked - 2));
    if (prevDot == -1) {
        setFirstUnlocked(0);
    } else {
        setFirstUnlocked(prevDot + 1);
    }
    evalLocked();
}

// Add commands bindings
editorProof.commands.addCommand({
    name: 'saveFile',
    bindKey: {
        win: 'Ctrl-S',
        mac: 'Command-S',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        sendZoocrypt({ 'cmd': 'save', 'arg': editorProof.getValue() });
    }
});

editorProof.commands.addCommand({
    name: 'evalNext',
    bindKey: {
        win: 'Ctrl-Enter',
        mac: 'Ctrl-Enter',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        evalNext();
    }
});

editorProof.commands.addCommand({
    name: 'evalPrev',
    bindKey: {
        win: 'Ctrl-Backspace',
        mac: 'Ctrl-Backspace',
        sender: 'editor|cli'
    },
    exec: function (env, args, request) {
        evalPrev();
    }
});
//# sourceMappingURL=zoocrypt.js.map
