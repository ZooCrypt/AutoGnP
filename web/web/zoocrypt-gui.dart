library ace.example.keybindings;

import 'dart:html';
import 'dart:math';
import 'dart:convert';
import 'package:ace/ace.dart' as ace;

// editor window for proof
ace.Editor editorProof;

// editor window for goal
ace.Editor editorGoal;

// number of first unprocessed character
int processedUpto = 0;

// id of last marker 
int lastMarker;

WebSocket webSocket;

main() {
  // var webSocket = new WebSocket("ws://echo.websocket.org");
  webSocket = new WebSocket('ws://127.0.0.1:9999/');
  
  editorProof = ace.edit(querySelector('#editor-proof'))
      ..theme = new ace.Theme.named('xcode');

  editorGoal = ace.edit(querySelector('#editor-goal'))
      ..readOnly = true
      ..theme = new ace.Theme.named('xcode');
  
  // create buttons for proof commands
  createCommandButtons();

  // create buttons for key bindings
  for (String name in ace.KeyboardHandler.BINDINGS) {
    _createButton(new ace.KeyboardHandler.named(name), 
        name == ace.KeyboardHandler.DEFAULT ? 'Ace default' : name);
  }
  
  window.onKeyDown.listen((KeyboardEvent ev) {
      var kev = new KeyEvent.wrap(ev);
      if (kev.ctrlKey) {
        if (kev.keyCode == KeyCode.ENTER) {
          print(ev.toString());
          nextCommand(null);
        } else if (kev.keyCode == KeyCode.BACKSPACE) {
          prevCommand(null);
        }  
      }
  });
}

String sendZooCrypt(Map m) {
  String s = JSON.encode(m);
  webSocket.sendString(s);
}

String lockedText() {
  return editorProof.value.substring(0, processedUpto); 
}

void highlightLocked() {
  ace.Point cpos = editorProof.session.document.indexToPosition(processedUpto);
  if (lastMarker != null) {
    editorProof.session.removeMarker(lastMarker);
  };
  lastMarker =
    editorProof.session.addMarker(new ace.Range(0,0,cpos.row,cpos.column),
                                  'warning', 'text', false);
}

void nextCommand(_) {
  // move the cursor to the next '.' starting from processedUpto
  String s = editorProof.value;
  int i = s.indexOf('.', processedUpto);
  if (i != -1) {
    processedUpto = i + 1;
    print("Next: ${processedUpto}");
    ace.Point cpos = editorProof.session.document.indexToPosition(processedUpto);
    editorProof.navigateTo(cpos.row, cpos.column);
  } else {
    print("Next: no next command");
  }
  sendZooCrypt({'cmd':'eval', 'arg':lockedText()});
  highlightLocked();
}

void prevCommand(_) {
  // move the cursor to the previous '.' starting from processedUpto
  String s = editorProof.value;
  int i = s.lastIndexOf('.', max(processedUpto - 2,0));
  if (i != -1) {
    processedUpto = i + 1;
  } else {
    print("Previous: setting to 0.");
    processedUpto = 0;
  }
  print("Previous: ${processedUpto}");
  ace.Point cpos = editorProof.session.document.indexToPosition(processedUpto);
  editorProof.navigateTo(cpos.row, cpos.column);
  sendZooCrypt({'cmd':'eval', 'arg':lockedText()});
  highlightLocked();
}

void createCommandButtons() {
  
  var prevButton = new ButtonElement()
      ..text = "Previous"
      ..onClick.listen(prevCommand);
  querySelector('#buttons-commands').children.add(prevButton);
  
  var nextButton = new ButtonElement()
      ..text = "Next"
      ..onClick.listen(nextCommand);
  querySelector('#buttons-commands').children.add(nextButton);
  
  var loadButton = new ButtonElement()
  ..text = "Load"
  ..onClick.listen((_) {
    sendZooCrypt({'cmd':'load', 'arg':''});
  });
  querySelector('#buttons-commands').children.add(loadButton);

  var saveButton = new ButtonElement()
  ..text = "Save"
  ..onClick.listen((_) {
    sendZooCrypt({'cmd':'save', 'arg':editorProof.value});
  });
  querySelector('#buttons-commands').children.add(saveButton);
  
  webSocket.onMessage.listen((MessageEvent e) {
    print("Received: ``${e.data}''");
    Map reply = JSON.decode(e.data);
    if (reply['cmd'] == 'setGoal') {
      editorGoal.setValue(reply['arg']);
      editorGoal.clearSelection(); 
    } else if (reply['cmd'] == 'setProof') {
        print("setProof\n");
        editorProof.setValue(reply['arg']);
        editorProof.clearSelection(); 
    } else {
      print("Reply ignored");
    }
  }); 

  webSocket.onOpen.listen((_) {
    sendZooCrypt({'cmd':'load', 'arg':''});
  });
  
  //var restartButton = new ButtonElement()
  //..text = "Restart"
  //..onClick.listen((_) {
  //    webSocket.sendString(editorProof.value);
  //  });
  // querySelector('#buttons-commands').children.add(restartButton);
}

void _createButton(ace.KeyboardHandler handler, String name) {
  var parent = querySelector('#buttons-bindings');
  var button = new ButtonElement()
      ..text = name
      ..onClick.listen((_) {
        editorProof.keyBinding.keyboardHandler = handler;
        querySelector('#label-bindings').text = name;
      });

  parent.children.add(button);
}
