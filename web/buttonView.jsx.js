/** @jsx React.DOM */

/* ******************************************************************/
/* Open Dialog                                                      */
/* ******************************************************************/

var FileButton = React.createClass({
  render: function() {
    var file = this.props.file;
    var closeDialog = this.props.closeDialog;
    var hclick = function () {
      loadBuffer(file);
      closeDialog();
    };
    return <button type="button" className="btn btn-default" style={{textAlign: "left"}} onClick={hclick}>{file}</button>;
  }
});

var FileButtons = React.createClass({
 render: function() {
     var closeDialog = this.props.closeDialog;
     var files = this.props.files;
     return (
      <div className="btn-group-vertical" style={{paddingBottom: "10px"}}>
         {files.map(function (fn) { return <FileButton key={fn} file={fn} closeDialog={closeDialog}/> })}
      </div>);extr
 }
});

var OpenDialog = React.createClass({
 render: function() {
   var files = this.props.files;
   var closeDialog = (function(_this) {
     return (
       function() {
         $(_this.getDOMNode()).modal("hide");
       })
   })(this);
   
   return (
     <div id="open-file-modal" className="modal">
       <div className="modal-dialog">
         <div className="modal-content">
           <div className="modal-header" style={{textAlign: "center"}}>
             <h3 className="modal-title">Open file</h3>
           </div>
           <div className="modal-body" style={{textAlign: "center"}}>
             <FileButtons files={files} closeDialog={closeDialog}/>
           </div>
           <div className="modal-footer">
             <div className="btn-group">
               <button type="button" className="btn btn-primary btn-default"
                  onClick={closeDialog}>Cancel</button>
             </div>
           </div>
         </div>
       </div>
     </div>);
 }
});

function renderOpenDialog(files) {
  React.renderComponent(
    <OpenDialog files={files}/>
  , document.getElementById('open-dialog')
  );
}

renderOpenDialog(["no files available"]);

var NewDialog = React.createClass({
  getInitialState: function() {
    return {filename: 'test.zc'};
  },

  handleChange: function(event) {
    this.setState({filename: event.target.value});
  },

 render: function() {
   var closeDialog = (function(_this) {
     return (
       function() {
         $(_this.getDOMNode()).modal("hide");
       })
   })(this);

   var openFile = (function(_this) {
     return (
       function() {
         loadBuffer(_this.state.filename);
         closeDialog();
       })
   })(this);

   var filename = this.state.filename;
   return (
     <div id="new-file-modal" className="modal">
       <div className="modal-dialog">
         <div className="modal-content">
           <div className="modal-header" style={{textAlign: "center"}}>
             <h3 className="modal-title">Visit New File</h3>
           </div>
           <div className="modal-body" style={{textAlign: "center"}}>
              <input type="test" value={filename} onChange={this.handleChange}/>
           </div>
           <div className="modal-footer">
             <div className="btn-group">
               <button type="button" className="btn btn-primary btn-default"
                  onClick={closeDialog}>Cancel</button>
               <button type="button" className="btn btn-primary btn-default"
                  onClick={openFile}>Open</button>
             </div>
           </div>
         </div>
       </div>
     </div>);
 }
});

function renderNewDialog() {
  React.renderComponent(
    <NewDialog/>
  , document.getElementById('new-dialog')
  );
}

renderNewDialog();

/* ******************************************************************/
/* Toolbar                                                          */
/* ******************************************************************/

var Toolbar = React.createClass({
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

    var newDialog = function() {
      $("#new-file-modal").modal('show');
    };

    return (
      <div className="btn-toolbar">
        <button className="btn btn-primary btn-default" onClick={openDialog}>Open file</button>
        <button className="btn btn-primary btn-default" onClick={newDialog}>New file</button>
        <button className="btn btn-primary btn-default" onClick={saveBuffer}>Save ({ctrl}-s)</button>
        <button className="btn btn-primary btn-default" onClick={evalNext}>Eval next (Ctrl-n)</button>
        <button className="btn btn-primary btn-default" onClick={evalCursor}>Eval up to cursor (Ctrl-return)</button>
        <button className="btn btn-primary btn-default" onClick={evalPrev}>Undo eval (Ctrl-p)</button>
        <span style={{paddingLeft: "10px"}}>Editing {fn==""?"<none>":fn}</span>
      </div>);
  }});

function renderToolbar(fn) {
  React.renderComponent(
    <Toolbar curFile={fn}/>
    , document.getElementById('toolbar-buttons')
  );
}

renderToolbar("");
