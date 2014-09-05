/** @jsx React.DOM */

var Editors = React.createClass({
  render: function() {
    return (
      <div className="row">
        <div className="col-md-12">
          <table>
            <tbody>
              <tr>
                <td>
                  <div className="editor" id="editor-proof"></div>
                </td>
                <td>
                  <div className="editor" id="editor-goal"></div>
                  <div className="editor" id="editor-message"></div>
                </td>
              </tr>
            </tbody>
          </table>
        </div>
      </div>)
  }
});

function renderEditors() {
  React.renderComponent(
      <Editors/>
    , document.getElementById('content')
  );
}


renderEditors();
