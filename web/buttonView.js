/** @jsx React.DOM */

var Toolbar = React.createClass({displayName: 'Toolbar',
  getInitialState: function() {
    // this is static and does not change
    return { ctrl: navigator.appVersion.indexOf('Mac') != -1 ? "Cmd" : "Ctrl" }
  },
  render: function() {
    var fn = this.props.curFile;
    var ctrl = this.state.ctrl;
    return (
      React.DOM.div({className: "btn-toolbar"}, 
        React.DOM.button({className: "btn btn-primary btn-default", id: "btn-open", onclick: ""}, "Open file"), 
        React.DOM.button({className: "btn btn-primary btn-default", id: "btn-save"}, "Save (", ctrl, "-s)"), 
        React.DOM.button({className: "btn btn-primary btn-default", id: "btn-eval-next"}, "Eval next (Ctrl-n)"), 
        React.DOM.button({className: "btn btn-primary btn-default", id: "btn-eval-upto"}, "Eval up to cursor (Ctrl-return)"), 
        React.DOM.button({className: "btn btn-primary btn-default", id: "btn-eval-undo"}, "Undo eval (Ctrl-p)"), 
        React.DOM.span({style: {paddingLeft: "10px"}}, "Editing ", fn==""?"<none>":fn)
      ));
  }});

var FileButton = React.createClass({displayName: 'FileButton',
  render: function() {
    var file = this.props.file;
    var hclick = function () {
      loadBuffer(file);
      closeDialog();
    };
    return React.DOM.button({type: "button", className: "btn btn-default file-choice", 
                   onClick: hclick}, file);
  }
});

var FileSelector = React.createClass({displayName: 'FileSelector',
 render: function() {
     var files = this.props.files;
     return (
      React.DOM.div({className: "btn-group-vertical", style: {paddingBottom: "10px"}}, 
         files.map(function (fn) { return FileButton({file: fn}) })
      ));
 }
});

function renderToolbar(fn) {
  React.renderComponent(
    Toolbar({curFile: fn})
    , document.getElementById('toolbar-buttons')
  );
}

function renderFileSelector(files) {
  React.renderComponent(
    FileSelector({files: files})
    , document.getElementById('file-buttons')
  );
}

renderToolbar("");
renderFileSelector(["a"]);
