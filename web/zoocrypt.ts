/// <reference path="ace.d.ts" />
/// <reference path="jquery.d.ts" />

/* ******************************************************************/
/* Debug logging                                                    */
/* ******************************************************************/
var enable_debug = true;

function log(s) {
  if (enable_debug) {
    console.log(s);
  }
}

/* ******************************************************************/
/* Websocket connection                                             */
/* ******************************************************************/
var wsServer = window.location.hostname ? window.location.hostname : "127.0.0.1";
var webSocket = new WebSocket("ws://" + wsServer + ":9999/");

// send json request to zoocrypt websocket server
function sendZoocrypt(m) {
  webSocket.send(JSON.stringify(m));
}

/* ******************************************************************/
/* Locking in proof editor                                          */
/* ******************************************************************/

// editorProof has been processed up to this character
var firstUnlocked : number  = 0;
// the text from the timepoint where the locking was enabled
var originalLockedText : string = "";
// the last locking marker, used for removal
var lastMarker;


function lockedText() : string {
  return editorProof.getValue().substring(0, firstUnlocked);
}

var editorProof = ace.edit("editor-proof");
editorProof.setTheme("ace/theme/eclipse");
editorProof.setHighlightActiveLine(false);
editorProof.focus();

editorProof.getSession().getDocument().on("change", function(ev) {
    var lt = lockedText();
    //log("lt: ''" + lt + "''");
    //log("oldLt: ''" + originalLockedText + "''");
    if (lt == originalLockedText) {
      // console.log("changed, but locked unchanged");
    } else {
      // console.log("locked changed");
      // search for the last dot that is the common prefix of
      // old and new content of locked region
      var lastDot = 0;
      for (var i=0; i < Math.min(lt.length, originalLockedText.length); i++) {
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
  }
)

/* ******************************************************************/
/* Goal and message editor and resizing                             */
/* ******************************************************************/

var editorGoal = ace.edit("editor-goal");
editorGoal.setTheme("ace/theme/eclipse");
editorGoal.setHighlightActiveLine(false);

var editorMessage = ace.edit("editor-message");
editorMessage.setTheme("ace/theme/eclipse");
editorMessage.setHighlightActiveLine(false);

// resize windows
function resizeAce() : void {
  $('#editor-proof').height($(window).height() - 50);
  $('#editor-proof').width($(window).width()/2 - 50);

  $('#editor-goal').height(($(window).height() - 50) * 0.7);
  $('#editor-goal').width($(window).width()/2 - 50);

  $('#editor-message').height(($(window).height() - 50) * 0.3);
  $('#editor-message').width($(window).width()/2 - 50);

};
//listen for changes
$(window).resize(resizeAce);
//set initially
resizeAce();


/* ******************************************************************/
/* Websocket event handling                                         */
/* ******************************************************************/

// Request proof script
webSocket.onopen = function (evt) {
  sendZoocrypt({'cmd':'load','arg':''});
}

// handle websocket answers
webSocket.onmessage = function (evt) {
  log(evt.data);
  var m = JSON.parse(evt.data);
  // answer for eval
  if (m.cmd == 'setGoal') {
    editorGoal.setValue(m.arg);
    editorGoal.clearSelection();
    editorMessage.setValue("We just received a new goal.");
    editorMessage.clearSelection();
  // answer for load
  } else if (m.cmd == 'setProof') {
    editorProof.setValue(m.arg);
    editorProof.clearSelection();
    editorProof.scrollPageUp();
    editorMessage.setValue("We just set the proof!");
    editorMessage.clearSelection();
  } else if (m.cmd == "error") {
    editorMessage.setValue("Error: "+ m.arg);
    editorMessage.clearSelection();
  }
}


/* ******************************************************************/
/* Evaluate parts of buffer                                         */
/* ******************************************************************/

function evalLocked() {
  var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked,0);
  editorProof.moveCursorToPosition(pos);
  editorProof.clearSelection();
  var Range = ace.require('ace/range').Range;
  if (lastMarker) { editorProof.getSession().removeMarker(lastMarker); };
  lastMarker = editorProof.getSession().addMarker(new Range(0,0,pos.row,pos.column),'locked','word',false);
  if (lockedText() !== "") {
    sendZoocrypt({'cmd':'eval','arg':lockedText()});
  }
}

function setFirstUnlocked(i : number) {
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
  var prevDot = editorProof.getValue().lastIndexOf(".", Math.max(0,firstUnlocked - 2));
  if (prevDot == -1) {
    setFirstUnlocked(0);
  } else {
    setFirstUnlocked(prevDot + 1);
  }
  evalLocked();
}

/* ******************************************************************/
/* Add command bindings buffer                                      */
/* ******************************************************************/

editorProof.commands.addCommand({
  name: 'saveFile',
  bindKey: {
    win: 'Ctrl-S',
    mac: 'Command-S',
    sender: 'editor|cli'
  },
  exec: function(env, args, request) {
    sendZoocrypt({'cmd':'save', 'arg':editorProof.getValue()});
  }
});

editorProof.commands.addCommand({
  name: 'evalNext',
  bindKey: {
    win: 'Ctrl-Enter',
    mac: 'Ctrl-Enter',
    sender: 'editor|cli'
  },
  exec: function(env, args, request) {
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
  exec: function(env, args, request) {
    evalPrev();
  }
});