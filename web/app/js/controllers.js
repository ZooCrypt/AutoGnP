'use strict';

/* Controllers */


function Start($scope, $location, $http) {
  $http.defaults.headers.post["Content-Type"] = "application/x-www-form-urlencoded";

  $scope.err = {};

  // predefined schemes
  $scope.oaep = {
    "name" : "OAEP",
    "msg_decl" : "k1",
    "rvar_decls" : "r : k3",
    "hash_decls" : "G : k3 -> k1 + k2;\nH : k1 + k2 -> k3",
    "perm_decls" : "f : k1 + k2 + k3",
    "cipher" : "f(G(r) + (m_b | (0^k2)) |\n  H(G(r) + (m_b | (0^k2))) + r)"
  };

  $scope.zaep = {
    "name" : "ZAEP",
    "msg_decl" : "k2",
    "rvar_decls" : "r : k1",
    "hash_decls" : "H : k1 -> k2",
    "perm_decls" : "f : k1 + k2",
    "cipher" : "f(r | H(r) + m_b)"    
  };

  $scope.pss = {
    "name" : "PSS-E",
    "msg_decl" : "k1",
    "rvar_decls" : "r : k2",
    "hash_decls" : "H : k1 + k2 -> k3;\nG : k3 -> k1 + k2",
    "perm_decls" : "f : k3 + k1 + k2",
    "cipher" : "f(H(m_b | r) |\n G( H(m_b|r)) + (m_b |r))"
  };

  $scope.br93 = {
    "name" : "BR93",
    "msg_decl" : "k2",
    "rvar_decls" : "r : k1",
    "hash_decls" : "H : k1 -> k2",
    "perm_decls" : "f : k1",
    "cipher" : "f(r) | H(r) + m_b"    
  }

  $scope.empty_scheme = {
    "name" : "",
    "msg_decl" : "",
    "rvar_decls" : "",
    "hash_decls" : "",
    "perm_decls" : "",
    "cipher" : ""
  };


  $scope.predefined_schemes = {
    " OAEP"  : $scope.oaep, 
    " ZAEP"  : $scope.zaep,
    " PSS-E" : $scope.pss,
    " BR93" : $scope.br93,
    "Reset" : $scope.empty_scheme // leading space ensures Reset comes last
  };

  $scope.scheme = $scope.empty_scheme;

  $scope.fillIn = function () {
    if ($scope.selected) {
      $scope.scheme = $scope.predefined_schemes[$scope.selected];
      $scope.selected = "";
    }; 
  };

  $scope.selected_scheme = "";
  
  $scope.prove = function() {
    var params = request("start", $scope.scheme);
    $http.post('jq/request', params).success(function(data) {
        if (data.res_type == "Error") {
          $scope.err = {};
          $scope.err[data.res_val.field] = data.res_val.message;
          // alert("Start.prove, error: "+data.res_val.field+"   "+data.res_val.message);
        } else if (data.res_type == "InternalError") {
          alert("Start.prove, internal error: "+data.res_val);
        } else if (data.res_type == "Ok") {
           $location.path("/proof/"+data.res_val);
        }
      }).
      error(function(err) { alert("Request failed: "+err); });
  };
};



function Proof($scope, $routeParams, $http, $location) {
  $http.defaults.headers.post["Content-Type"] = "application/x-www-form-urlencoded";

  $scope.s = {};
  $scope.s.cmd = "";

  $scope.s.history = "";

  $scope.s.selected_cmd = "";

  $scope.s.expert_mode = false;

  $scope.s.nexpr = "";

  $scope.s.apply_ctxt_result;

  $scope.s.applicable_rules = [];

  $scope.s.proofId = parseInt($routeParams.proofId);

  $scope.s.cmd_rnd_ctxt = "*";

  $scope.s.cmd_ow_c1 = "*";

  $scope.s.cmd_ow_c2 = "*";

  $scope.s.auto_norm = true;

  var successHandler = function(name, realSuccess) {
    return function(data) {
      if (data.res_type == "Error") {
        $scope.s.err = {};
        $scope.s.err[data.res_val.field] = data.res_val.message;
      } else if (data.res_type == "InternalError") {
         alert("Start."+name+", internal error: "+data.res_val);
         $location.path("");
      } else if (data.res_type == "Ok") {
        $scope.s.err = {};
        realSuccess(data) 
      }
    }
  }

  $scope.s.updateApplicable = function() {
    if ($scope.s.goal_idx === null) {
      $scope.s.applicable_rules = [];
    } else {
      $scope.s.goal_ai = $scope.s.goals_ai[$scope.s.goal_idx];
      var goals_ai = $scope.s.goal_ai
      $scope.s.applicable_rules =
        [].concat( goals_ai.ind ? ["ind"] : [],
                   goals_ai.rvars_event_only.length > 0 ? ["rnd"] : [],
                   goals_ai.perms_rvars.length > 0 ? ["ow"] : [],
                   goals_ai.hashes.length > 0 ? ["fail1", "fail2"] : [],
                   Object.keys(goals_ai.rvars_xor).length > 0 ? ["opt"] : [],
                   goals_ai.rvars.length > 1 ? ["merge"] : [],
                   goals_ai.rvars_non_basic.length > 0 ? ["split"] : [],
                   goals_ai.conjs.length > 0 ? ["conj"] : [],
                   !goals_ai.nf ? ["norm"] : []
                 );  
    };
  };
  
  $scope.s.updateProofTree = function() {
    $scope.s.proof_arr = table_prf($scope.s.proof.prems[0], $scope.s.auto_norm);
  };

  $scope.s.skip_bits = function() {
    var ty_list = $scope.s.cmd_ow_perm.perm_ty;
    console.log("skip_bits: " + ty_list);
    var res = Array();
    if (ty_list) {
      res.push('0');
      for (var i = 0; i < ty_list.length - 1; ++i) {
        res.push(i ==0 ? ty_list[i] : (res[i] + '+' + ty_list[i]));
      }
    } 
    return res;
  };

  $scope.s.take_bits = function() {
    var ty_list = $scope.s.cmd_ow_perm.perm_ty;
    var skipped = $scope.s.cmd_ow_l;
    console.log("take_bits: " + ty_list + " " + skipped);
    if (ty_list && skipped) {
      var nskipped = skipped == "0" ? 0 : skipped.split("+").length;
      var rtys = ty_list.slice(nskipped);
      if (rtys.length > 0) {
        var res = Array();
        res.push(rtys[0]);
        for (var i = 0; i < rtys.length - 1; ++i) {
          res.push(res[i] + '+' + rtys[i+1]);
        }
        return res;
      }
    }
    return [];
  };

  var getProof = function() {
    var params = request("get_proof",
                         { "proofId" : $scope.s.proofId });
    $http.post('jq/request', params).
      success(successHandler("getProof", function(data) {
        $scope.s.err = {};
        $scope.s.history    = data.res_val.history;
        $scope.s.proof      = data.res_val.proof;
        $scope.s.goals      = data.res_val.goals;
        $scope.s.goal_idxs  = range(0, $scope.s.goals.length - 1);
        $scope.s.fresh_rvar = data.res_val.fresh_rvar;
        $scope.s.tscheme    = data.res_val.tscheme;
        $scope.s.bound      = data.res_val.bound;
        $scope.s.bound_spd  = data.res_val.bound_spd;         
        //$scope.s.proof_arr  = table_prf($scope.s.proof.prems[0], $scope.s.auto_norm);
        if (!($scope.s.goal_idx in $scope.s.goal_idxs)) {
          if ($scope.s.goals.length == 0) {
            $scope.s.goal_idx = null;
          } else {
            $scope.s.goal_idx = 0;
          }
        }
        $scope.s.goals_ai = data.res_val.goals_ai;
        $scope.s.updateApplicable();
        $scope.s.updateProofTree();
      })).
        error(function(err) { alert("Request failed: "+err); });
  };

  $scope.s.apply = function() {
    var loc;

    if ($scope.s.cmd.indexOf("@") == -1 && $scope.s.goal_idx !== 0) {
      loc = function(cmd) { return "("+cmd+") @ "+ $scope.s.goal_idx };
    } else { 
      loc = function(cmd) { return cmd };
    };
    
    var params = request("apply_proof",
                   { "cmd" : loc($scope.s.cmd), "proofId": $scope.s.proofId });
    
    $http.post('jq/request', params).
      success(successHandler("apply",function(data) {
        $location.path("/proof/"+data.res_val);
      })).
      error(function(err) { alert("Request failed: "+err); });
  };

  $scope.s.admit = function(path) {
    $scope.s.cmd = "admit @ ("+path+")";
    $scope.s.apply();
  };

  $scope.s.update_cmd = function () {
    var snorm = $scope.s.auto_norm ? "; norm" : "";
    switch ($scope.s.cmd_rule) {
      case "fail1":
        if ($scope.s.cmd_fail1_hash === undefined && $scope.s.goal_ai.hashes.length == 1) {
          $scope.s.cmd_fail1_hash = $scope.s.goal_ai.hashes[0];
        }
        $scope.s.cmd = "fail1 (" + $scope.s.cmd_fail1_hash + ") (r" + $scope.s.fresh_rvar + ")";
        break;

      case "fail2":
        if ($scope.s.cmd_fail2_hash === undefined && $scope.s.goal_ai.hashes.length == 1) {
          $scope.s.cmd_fail2_hash = $scope.s.goal_ai.hashes[0];
        }
        $scope.s.cmd = "fail2 (" + $scope.s.cmd_fail2_hash + ") (r" + $scope.s.fresh_rvar + ")";
        break;

      case "opt":
        if ($scope.s.cmd_opt_rvar === undefined && Object.keys($scope.s.goal_ai.rvars_xor).length == 1) {
          $scope.s.cmd_opt_rvar = Object.keys($scope.s.goal_ai.rvars_xor)[0];
        }
        if ($scope.s.goal_ai.rvars_xor[$scope.s.cmd_opt_rvar] !== undefined && 
            $scope.s.goal_ai.rvars_xor[$scope.s.cmd_opt_rvar].length > 0) {
          $scope.s.cmd_opt_expr = $scope.s.goal_ai.rvars_xor[$scope.s.cmd_opt_rvar];
        }
        $scope.s.cmd = "opt ("+ $scope.s.cmd_opt_rvar +") (" + $scope.s.cmd_opt_expr + ")" + snorm;
        break;

      case "norm":
        $scope.s.cmd = "norm";
        break;

      case "conj":
        $scope.s.cmd = "conj "+$scope.s.cmd_conj_idx;
        break;

      case "rnd":
        if ($scope.s.cmd_rnd_rvar === undefined && $scope.s.goal_ai.rvars_event_only.length == 1) {
          $scope.s.cmd_rnd_rvar = $scope.s.goal_ai.rvars_event_only[0];
        }
        $scope.s.cmd = "rnd (" + $scope.s.cmd_rnd_rvar + ") ( " + $scope.s.cmd_rnd_ctxt + " )";
        break;

      case "merge":
        $scope.s.cmd = "merge (" + $scope.s.cmd_merge_r1 + ") ( " + $scope.s.cmd_merge_r2 + " ) ( r" + $scope.s.fresh_rvar + ")" + snorm;
        break;

      case "split":
        if ($scope.s.cmd_split_rvar === undefined && $scope.s.goal_ai.rvars_non_basic.length == 1) {
          $scope.s.cmd_split_rvar = $scope.s.goal_ai.rvars_non_basic[0];
        }
        $scope.s.cmd = "split (" + $scope.s.cmd_split_rvar + ") ( "+ $scope.s.cmd_split_type
                       + ") ( r" + $scope.s.fresh_rvar + " ) ( r" + ($scope.s.fresh_rvar + 1) + ")" + snorm;
        break;

      case "ow":
        if ($scope.s.cmd_ow_perm === undefined && $scope.s.goal_ai.perms_rvars.length == 1) {
          $scope.s.cmd_ow_perm = $scope.s.goal_ai.perms_rvars[0];
        }
        if ($scope.s.cmd_ow_l === undefined && $scope.s.skip_bits().length == 1) {
          $scope.s.cmd_ow_l = $scope.s.skip_bits()[0];
        }
        if ($scope.s.cmd_ow_m === undefined && $scope.s.take_bits().length == 1) {
          $scope.s.cmd_ow_m = $scope.s.take_bits()[0];
        }
        if ($scope.s.cmd_ow_perm) {
          $scope.s.cmd = "ow (" + $scope.s.cmd_ow_perm.perm + ") ( "+ $scope.s.cmd_ow_perm.rvar
                         + ") ( " + $scope.s.cmd_ow_l + " ) ( " + $scope.s.cmd_ow_m + ")"
                         + " ( " + $scope.s.cmd_ow_perm.other_rvars + " ) ( " + $scope.s.cmd_ow_c1
                         + " ) ( " + $scope.s.cmd_ow_c2 + ")";
        }
        break;
      case "ind":
        $scope.s.cmd = "ind";
        break;
    }
  };

  $scope.s.norm = function(e) {
    var params = request("norm_expr",
                         { "proofId": $scope.s.proofId,
                           "nexpr" : e });
    
    $http.post('jq/request', params).
      success(successHandler("norm_expr", function(data) {
        $scope.s.norm_result = data.res_val;
      })).
      error(function(err) { alert("Request failed: "+err); });
  };

  $scope.s.applyCtxt = function(hide_errors,k,c) {
    var params = request("apply_ctxt",
                         { "proofId": $scope.s.proofId,
                           "context" : c,
                           "known" : k });
    
    $http.post('jq/request', params).
      success(successHandler("applyCtxt", function(data) {
          $scope.s.apply_ctxt_result = data.res_val;
      })).
      error(function(err) { alert("Request failed: "+err); });
  };

  $scope.s.ow_context1 = function(other_rvars) {
    var smsg = $scope.s.goal_ai.msg_occ ? " | m_b" : "";
    var sother_rvars = other_rvars ? (" | " + other_rvars) : "";
    return ($scope.s.goal_ai.queried_msgs + sother_rvars + smsg)
  };

  $scope.s.ow_context2 = function(other_rvars) {
    if ($scope.s.cmd_ow_perm) {
      var smsg = $scope.s.goal_ai.msg_occ ? " | m_b" : "";
      var sother_rvars = other_rvars ? (" | " + other_rvars) : "";
      return $scope.s.cmd_ow_perm.perm+"("+$scope.s.cmd_ow_perm.rvar+")" + sother_rvars + smsg;
    }
  };
   

  getProof();
};
