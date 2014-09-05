/// <reference path="zoocrypt.ts" />

declare var renderToolbar
declare var renderOpenDialog

/* ******************************************************************/
/* webSocket event loop                                             */
/* ******************************************************************/

webSocket.onmessage = function (evt) {
  log(evt.data);
  var m : Reply = JSON.parse(evt.data);
  // answer for eval
  if (m.cmd == 'setGoal') {
    var dbg = (<any>m).debug;
    if (dbg != "") { console.debug(dbg); }
    setFirstUnlocked(m.ok_upto);
    markLocked('locked');
    editorGoal.setValue(m.arg);
    editorGoal.clearSelection();
    var pos = editorGoal.getSession().getDocument().indexToPosition(0,0);
    editorGoal.moveCursorToPosition(pos);
    if (m.err) {
      editorMessage.setValue(m.err);
    } else {
      editorMessage.setValue(m.msgs.length > 0 ? m.msgs[m.msgs.length - 1] : "No message received.");
    }
    editorMessage.clearSelection();
  // answer for list files
  } else if (m.cmd == 'setFiles') {
    files = <any>(m.arg);
    renderOpenDialog(files);

  // answer for load
  } else if (m.cmd == 'setProof') {
    currentFile = (<any>m).filename;
    renderToolbar(currentFile);
    editorProof.setValue(m.arg);
    editorProof.clearSelection();
    editorProof.scrollPageUp();
    editorMessage.setValue("Proofscript loaded.");
    editorMessage.clearSelection();
    var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked,0);
    editorProof.moveCursorToPosition(pos);
  // answers for save
  } else if (m.cmd == "saveOK") {
    editorMessage.setValue("Proofscript saved.");
    editorMessage.clearSelection();
  } else if (m.cmd == "saveFAILED") {
    editorMessage.setValue("Save of proofscript failed.");
    editorMessage.clearSelection();
  }
};
