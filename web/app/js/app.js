'use strict';

// Declare app level module which depends on filters, and services
angular.module('zoocrypt', ['zoocrypt.filters', 'zoocrypt.services', 'zoocrypt.directives', 'ui.bootstrap']).
  config(['$routeProvider', function($routeProvider) {
    $routeProvider.when('', {templateUrl: 'partials/start.html'});
    $routeProvider.when('/proof/:proofId', {templateUrl: 'partials/proof.html'});
    $routeProvider.when('/help', {templateUrl: 'partials/help.html'});
    $routeProvider.otherwise({redirectTo: ''});
  }]);

function range(start, end) {
  var l = [];
  for (var i = start; i <= end; i++) {
      l.push(i);
  }
  return l;
}

function table_prf(prf, hide_norm) {

  var prf = angular.copy(prf); // we don't want to modify the actual $scope.proof object

  function rows(prf) {
    var nadd = (hide_norm === true && prf.rule == "Sub(norm)") ? 0 : 1;
    return Math.max(0,_.max(_.map(prf.prems,rows))) + nadd;
  };

  function colspan(prf) {
    if (!prf.prems.length) { return 1;
    } else {
      return _.reduce(_.map(prf.prems,colspan),
                            function(acc, x){ return acc + x + 1; }, 0) - 1;
    };
  };

  var rown = rows(prf);
  var rowa = new Array(rown);


  function aux(prf, row, path) {
    if (!(row in rowa)) {
      rowa[row] = new Array();
    };
    // hide applications of norm rule
    if (prf.rule == "Sub(norm)" && hide_norm === true) {
      var child = prf.prems[0];
      prf.rule = child.rule;
      prf.judgement = child.judgement;
      prf.prems = child.prems;
      path = path + ((path == "") ? "" : ",") + 0;
    };
    if (prf.rule) {
      rowa[row].push({ "type" : "judgement", "colspan" : colspan(prf), "judgement" : prf.judgement});
      rowa[row].push({ "type" : "rule_name", "rule" : prf.rule, "colspan" : "1", "path" : path});
    } else {
      // \nabla placeholder
      rowa[row].push({ "type" : "nabla", "judgement" : prf.judgement, "colspan" : "1"})
      rowa[row].push({ "type" : "padding", "colspan" : "1"});
    };
    if (prf.prems.length) {
      for (var j = 0; j < prf.prems.length; ++j) {
        aux(prf.prems[j], row+1, path + ((path == "") ? "" : ",") + j );
      }
    } else {
      /* We have to pad the rows above */
      for (var i = row + 1 ; i < rown; ++i) {
        if (!(i in rowa)) {
          rowa[i] = new Array();
        }
        rowa[i].push({ "type" : "padding", "colspan" : "2"});
      }
    }
  }
  aux(prf, 0, "");
  return (rowa.reverse());
};

// FIXME: ocsigen does not seem to support "application/json" POST content,
// only "application/x-www-form-urlencoded"
function request(name, arg) {
  var req = JSON.stringify({"req_name" : name, "req_arg" : arg}, null, 4);
  return $.param({"cmd" : req});
};
