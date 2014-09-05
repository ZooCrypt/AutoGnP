/** @jsx React.DOM */

/* ******************************************************************/
/* Open Dialog                                                      */
/* ******************************************************************/

var FileButton = React.createClass({displayName: 'FileButton',
  render: function() {
    var file = this.props.file;
    var closeDialog = this.props.closeDialog;
    var hclick = function () {
      loadBuffer(file);
      closeDialog();
    };
    return React.DOM.button({type: "button", className: "btn btn-default", onClick: hclick}, file);
  }
});

var FileButtons = React.createClass({displayName: 'FileButtons',
 render: function() {
     var closeDialog = this.props.closeDialog;
     var files = this.props.files;
     return (
      React.DOM.div({className: "btn-group-vertical", style: {paddingBottom: "10px"}}, 
         files.map(function (fn) { return FileButton({key: fn, file: fn, closeDialog: closeDialog}) })
      ));
 }
});

var OpenDialog = React.createClass({displayName: 'OpenDialog',
 render: function() {
   var files = this.props.files;
   var closeDialog = (function(_this) {
     return (
       function() {
         $(_this.getDOMNode()).modal("hide");
       })
   })(this);
   
   return (
     React.DOM.div({id: "open-file-modal", className: "modal"}, 
       React.DOM.div({className: "modal-dialog"}, 
         React.DOM.div({className: "modal-content"}, 
           React.DOM.div({className: "modal-header", style: {textAlign: "center"}}, 
             React.DOM.h3({className: "modal-title"}, "Open file")
           ), 
           React.DOM.div({className: "modal-body", style: {textAlign: "center"}}, 
             FileButtons({files: files, closeDialog: closeDialog})
           ), 
           React.DOM.div({className: "modal-footer"}, 
             React.DOM.div({className: "btn-group"}, 
               React.DOM.button({type: "button", className: "btn btn-primary btn-default", 
                  onClick: closeDialog}, "Cancel")
             )
           )
         )
       )
     ));
 }
});

function renderOpenDialog(files) {
  React.renderComponent(
    OpenDialog({files: files})
    , document.getElementById('open-dialog')
  );
}

renderOpenDialog(["a"]);

/* ******************************************************************/
/* Toolbar                                                          */
/* ******************************************************************/

var Toolbar = React.createClass({displayName: 'Toolbar',
  getInitialState: function() {
    // this is static and does not change
    return { ctrl: navigator.appVersion.indexOf('Mac') != -1 ? "Cmd" : "Ctrl" }
  },
  render: function() {

    var fn = this.props.curFile;

    var ctrl = this.state.ctrl;

    var openDialog = function() {
      $("#open-file-modal").modal('show');
    };

    return (
      React.DOM.div({className: "btn-toolbar"}, 
        React.DOM.button({className: "btn btn-primary btn-default", onClick: openDialog}, "Open file"), 
        React.DOM.button({className: "btn btn-primary btn-default", onClick: saveBuffer}, "Save (", ctrl, "-s)"), 
        React.DOM.button({className: "btn btn-primary btn-default", onClick: evalNext}, "Eval next (Ctrl-n)"), 
        React.DOM.button({className: "btn btn-primary btn-default", onClick: evalCursor}, "Eval up to cursor (Ctrl-return)"), 
        React.DOM.button({className: "btn btn-primary btn-default", onClick: evalPrev}, "Undo eval (Ctrl-p)"), 
        React.DOM.span({style: {paddingLeft: "10px"}}, "Editing ", fn==""?"<none>":fn)
      ));
  }});

function renderToolbar(fn) {
  React.renderComponent(
    Toolbar({curFile: fn})
    , document.getElementById('toolbar-buttons')
  );
}

renderToolbar("");
