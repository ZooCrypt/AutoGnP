/** @jsx React.DOM */

var Toolbar = React.createClass({
  getInitialState: function() {
    // this is static and does not change
    return { ctrl: navigator.appVersion.indexOf('Mac') != -1 ? "Cmd" : "Ctrl" }
  },
  render: function() {
    var fn = this.props.curFile;
    var ctrl = this.state.ctrl;
    return (
      <div className="btn-toolbar">
        <button className="btn btn-primary btn-default" id="btn-open" onclick="">Open file</button>
        <button className="btn btn-primary btn-default" id="btn-save">Save ({ctrl}-s)</button>
        <button className="btn btn-primary btn-default" id="btn-eval-next">Eval next (Ctrl-n)</button>
        <button className="btn btn-primary btn-default" id="btn-eval-upto">Eval up to cursor (Ctrl-return)</button>
        <button className="btn btn-primary btn-default" id="btn-eval-undo">Undo eval (Ctrl-p)</button>
        <span style={{paddingLeft: "10px"}}>Editing {fn==""?"<none>":fn}</span>
      </div>);
  }});

var FileButton = React.createClass({
  render: function() {
    var file = this.props.file;
    var hclick = function () {
      loadBuffer(file);
      closeDialog();
    };
    return <button type="button" className="btn btn-default file-choice"
                   onClick={hclick}>{file}</button>;
  }
});

var FileSelector = React.createClass({
 render: function() {
     var files = this.props.files;
     return (
      <div className="btn-group-vertical" style={{paddingBottom: "10px"}}>
         {files.map(function (fn) { return <FileButton file={fn}/> })}
      </div>);
 }
});

function renderToolbar(fn) {
  React.renderComponent(
    <Toolbar curFile={fn}/>
    , document.getElementById('toolbar-buttons')
  );
}

function renderFileSelector(files) {
  React.renderComponent(
    <FileSelector files={files}/>
    , document.getElementById('file-buttons')
  );
}

renderToolbar("");
renderFileSelector(["a"]);
