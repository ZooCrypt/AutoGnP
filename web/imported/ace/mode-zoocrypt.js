/* ***** BEGIN LICENSE BLOCK *****
 * Distributed under the BSD license:
 *
 * Copyright (c) 2010, Ajax.org B.V.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of Ajax.org B.V. nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL AJAX.ORG B.V. BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * ***** END LICENSE BLOCK ***** */

// adapted from ocaml mode

ace.define('ace/mode/zoocrypt', ['require', 'exports', 'module' , 'ace/lib/oop', 'ace/mode/text', 'ace/tokenizer', 'ace/mode/ocaml_highlight_rules', 'ace/mode/matching_brace_outdent', 'ace/range'], function(require, exports, module) {


  var oop = require("../lib/oop");
  var TextMode = require("./text").Mode;
  var Tokenizer = require("../tokenizer").Tokenizer;
  var ZoocryptHighlightRules = require("./zoocrypt_highlight_rules").ZoocryptHighlightRules;
  var MatchingBraceOutdent = require("./matching_brace_outdent").MatchingBraceOutdent;
  var Range = require("../range").Range;

  var Mode = function() {
    this.HighlightRules = ZoocryptHighlightRules;

    this.$outdent   = new MatchingBraceOutdent();
  };
  oop.inherits(Mode, TextMode);

  var indenter = /(?:[({[=:]|[-=]>|\b(?:else|try|with))\s*$/;

  (function() {

    this.toggleCommentLines = function(state, doc, startRow, endRow) {
      var i, line;
      var outdent = true;
      var re = /^\s*\(\*(.*)\*\)/;

      for (i=startRow; i<= endRow; i++) {
        if (!re.test(doc.getLine(i))) {
          outdent = false;
          break;
        }
      }

      var range = new Range(0, 0, 0, 0);
      for (i=startRow; i<= endRow; i++) {
        line = doc.getLine(i);
        range.start.row  = i;
        range.end.row    = i;
        range.end.column = line.length;

        doc.replace(range, outdent ? line.match(re)[1] : "(*" + line + "*)");
      }
    };

    this.getNextLineIndent = function(state, line, tab) {
      var indent = this.$getIndent(line);
      var tokens = this.getTokenizer().getLineTokens(line, state).tokens;

      if (!(tokens.length && tokens[tokens.length - 1].type === 'comment') &&
        state === 'start' && indenter.test(line))
        indent += tab;
      return indent;
    };

    this.checkOutdent = function(state, line, input) {
      return this.$outdent.checkOutdent(line, input);
    };

    this.autoOutdent = function(state, doc, row) {
      this.$outdent.autoOutdent(doc, row);
    };

  }).call(Mode.prototype);

  exports.Mode = Mode;
});

ace.define('ace/mode/zoocrypt_highlight_rules', ['require', 'exports', 'module' , 'ace/lib/oop', 'ace/mode/text_highlight_rules'], function(require, exports, module) {


  var oop = require("../lib/oop");
  var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;

  var ZoocryptHighlightRules = function() {

    var keywords = (
      "assumption|adversary|oracle|prove|bilinear|rrewrite_oracle|rnorm_nounfold|"  +
        "rnorm|rnorm_unknown|rlet_abstract|rswap|rindep|last|radd_test|admit|" +
        "rrandom|rrandom_oracle|rnorm_unkown|let|random|rbad|rctxt_ev|extract|rexcept|" +
        "rlet_unfold"
      );

    var builtinConstants = ("true|false|Fq");

    var builtinFunctions = (
      "Bool|Fq|true|false"
      );

    var keywordMapper = this.createKeywordMapper({
      "variable.language": "this",
      "keyword": keywords,
      "constant.language": builtinConstants,
      "support.function": builtinFunctions
    }, "identifier");

    var decimalInteger = "(?:(?:[1-9]\\d*)|(?:0))";
    var octInteger = "(?:0[oO]?[0-7]+)";
    var hexInteger = "(?:0[xX][\\dA-Fa-f]+)";
    var binInteger = "(?:0[bB][01]+)";
    var integer = "(?:" + decimalInteger + "|" + octInteger + "|" + hexInteger + "|" + binInteger + ")";

    var exponent = "(?:[eE][+-]?\\d+)";
    var fraction = "(?:\\.\\d+)";
    var intPart = "(?:\\d+)";
    var pointFloat = "(?:(?:" + intPart + "?" + fraction + ")|(?:" + intPart + "\\.))";
    var exponentFloat = "(?:(?:" + pointFloat + "|" +  intPart + ")" + exponent + ")";
    var floatNumber = "(?:" + exponentFloat + "|" + pointFloat + ")";

    this.$rules = {
      "start" : [
        {
          token : "comment",
          regex : '\\(\\*.*?\\*\\)\\s*?$'
        },
        {
          token : "comment",
          regex : '\\(\\*.*',
          next : "comment"
        },
        {
          token : "string", // single line
          regex : '["](?:(?:\\\\.)|(?:[^"\\\\]))*?["]'
        },
        {
          token : "string", // single char
          regex : "'.'"
        },
        {
          token : "string", // " string
          regex : '"',
          next  : "qstring"
        },
        {
          token : "constant.numeric", // imaginary
          regex : "(?:" + floatNumber + "|\\d+)[jJ]\\b"
        },
        {
          token : "constant.numeric", // float
          regex : floatNumber
        },
        {
          token : "constant.numeric", // integer
          regex : integer + "\\b"
        },
        {
          token : keywordMapper,
          regex : "[a-zA-Z_$][a-zA-Z0-9_$]*\\b"
        },
        {
          token : "keyword.operator",
          regex : "\\+\\.|\\-\\.|\\*\\.|\\/\\.|#|;;|\\+|\\-|\\*|\\*\\*\\/|\\/\\/|%|<<|>>|&|\\||\\^|~|<|>|<=|=>|==|!=|<>|<-|="
        },
        {
          token : "paren.lparen",
          regex : "[[({]"
        },
        {
          token : "paren.rparen",
          regex : "[\\])}]"
        },
        {
          token : "text",
          regex : "\\s+"
        }
      ],
      "comment" : [
        {
          token : "comment", // closing comment
          regex : ".*?\\*\\)",
          next : "start"
        },
        {
          token : "comment", // comment spanning whole line
          regex : ".+"
        }
      ],

      "qstring" : [
        {
          token : "string",
          regex : '"',
          next : "start"
        }, {
          token : "string",
          regex : '.+'
        }
      ]
    };
  };

  oop.inherits(ZoocryptHighlightRules, TextHighlightRules);

  exports.ZoocryptHighlightRules = ZoocryptHighlightRules;
});

ace.define('ace/mode/matching_brace_outdent', ['require', 'exports', 'module' , 'ace/range'], function(require, exports, module) {


  var Range = require("../range").Range;

  var MatchingBraceOutdent = function() {};

  (function() {

    this.checkOutdent = function(line, input) {
      if (! /^\s+$/.test(line))
        return false;

      return /^\s*\}/.test(input);
    };

    this.autoOutdent = function(doc, row) {
      var line = doc.getLine(row);
      var match = line.match(/^(\s*\})/);

      if (!match) return 0;

      var column = match[1].length;
      var openBracePos = doc.findMatchingBracket({row: row, column: column});

      if (!openBracePos || openBracePos.row == row) return 0;

      var indent = this.$getIndent(doc.getLine(openBracePos.row));
      doc.replace(new Range(row, 0, row, column-1), indent);
    };

    this.$getIndent = function(line) {
      return line.match(/^\s*/)[0];
    };

  }).call(MatchingBraceOutdent.prototype);

  exports.MatchingBraceOutdent = MatchingBraceOutdent;
});
