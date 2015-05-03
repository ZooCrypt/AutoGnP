/// <reference path="zoocrypt.ts" />
/* ******************************************************************/
/* webSocket event loop                                             */
/* ******************************************************************/
webSocket.onmessage = function (evt) {
    log(evt.data);
    console.log(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n");
    var m = JSON.parse(evt.data);
    // answer for eval
    if (m.cmd == 'setGoal') {
        var dbg = m.debug;
        if (dbg != "") {
            console.log(dbg);
        }
        setFirstUnlocked(m.ok_upto);
        markLocked('locked');
        editorGoal.setValue(m.arg);
        editorGoal.clearSelection();
        var pos = editorGoal.getSession().getDocument().indexToPosition(0, 0);
        editorGoal.moveCursorToPosition(pos);
        if (m.err) {
            editorMessage.setValue(m.err);
        }
        else {
            editorMessage.setValue(m.msgs.length > 0 ? m.msgs[m.msgs.length - 1] : "No message received.");
        }
        editorMessage.clearSelection();
    }
    else if (m.cmd == 'setDebug') {
        editorMessage.setValue(m.arg);
        editorMessage.clearSelection();
    }
    else if (m.cmd == 'setFiles') {
        files = (m.arg);
        renderOpenDialog(files);
    }
    else if (m.cmd == 'setProof') {
        currentFile = m.filename;
        renderToolbar(currentFile);
        editorProof.setValue(m.arg);
        editorProof.clearSelection();
        editorProof.scrollPageUp();
        editorMessage.setValue("Proofscript loaded.");
        editorMessage.clearSelection();
        var pos = editorProof.getSession().getDocument().indexToPosition(firstUnlocked, 0);
        editorProof.moveCursorToPosition(pos);
    }
    else if (m.cmd == "saveOK") {
        editorMessage.setValue("Proofscript saved.");
        editorMessage.clearSelection();
    }
    else if (m.cmd == "saveFAILED") {
        editorMessage.setValue("Save of proofscript failed.");
        editorMessage.clearSelection();
    }
};
