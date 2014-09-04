/// <reference path="zoocrypt.ts" />

declare var renderToolbar
declare var renderFileSelector

/* ******************************************************************/
/* Set handlers for buttons                                         */
/* ******************************************************************/

$('#btn-open').click(openDialog);
$('#btn-cancel-open').click(closeDialog);

$('#btn-save').click(saveBuffer);
$('#btn-eval-next').click(evalNext);
$('#btn-eval-upto').click(evalCursor);
$('#btn-eval-undo').click(evalPrev);

/* ******************************************************************/
/* webSocket event loop                                             */
/* ******************************************************************/

// handle websocket answers
webSocket.onmessage = function (evt) {
  log(evt.data);
  var m : Reply = JSON.parse(evt.data);
  // answer for eval
  if (m.cmd == 'setGoal') {
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
    renderFileSelector(files);

    // var source   = $("#file-button-template").html();
    // var template = Handlebars.compile(source);

    //var h = "";
    //for(var i = 0; i < files.length; i++) {
    //  h = h + template({file: files[i]});
    //}
    //$("#file-buttons").html(h)
    //var fcs = $('.file-choice');
    //var len = fcs.length;
    //for (var i = 0; i < len; i++) {
    //  var fn = fcs[i].textContent;
    //  fcs[i].onclick = function() {
    //    var j = (<any>(arguments.callee)).j;
    //    var fname = $('.file-choice')[j].textContent;
    //    loadBuffer(fname);
    //    closeDialog();
    //  };
    //  (<any>(fcs[i].onclick)).j = i;
    //}

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
