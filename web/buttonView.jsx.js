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
      </div>);
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

renderOpenDialog(["a"]);

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

    return (
      <div className="btn-toolbar">
        <button className="btn btn-primary btn-default" onClick={openDialog}>Open file</button>
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
