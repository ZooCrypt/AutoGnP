;; This file was adapted from EasyCrypt (proofgeneral/easycrypt-syntax.el)

(require 'proof-syntax)
(require 'autognp-keywords)
(require 'autognp-hooks)

(defconst autognp-id "[A-Za-z_]+")

(defconst autognp-terminal-string    ".")
(defconst autognp-command-end-regexp "[^\\.]\\.\\(\\s \\|\n\\|$\\)")

(defconst autognp-keywords-proof-goal nil) ;; '("bound_adv" "bound_dist" "bound_succ"))
(defconst autognp-keywords-proof-save nil) ;; '("save" "qed"))

(defconst autognp-non-undoables-regexp "^pragma\\b")

(defconst autognp-keywords-code-open  '("{"))
(defconst autognp-keywords-code-close '("}")) 
(defconst autognp-keywords-code-end   '(";"))

(defvar autognp-other-symbols "\\(\\.\\.\\|\\[\\]\\)")

(defvar autognp-operator-char-1 "=\\|<\\|>\\|~")
(defvar autognp-operator-char-2 "\\+\\|\\-")
(defvar autognp-operator-char-3 "\\*\\|/\\|%")
(defvar autognp-operator-char-4 "!\\|\\$\\|&\\|\\?\\|@\\|\\^\\|:\\||\\|#")

(defvar autognp-operator-char-1234
  (concat "\\(" autognp-operator-char-1
          "\\|" autognp-operator-char-2
		  "\\|" autognp-operator-char-3
		  "\\|" autognp-operator-char-4
          "\\)"))

(defconst autognp-proof-save-regexp
  (concat "^\\(" (proof-ids-to-regexp autognp-keywords-proof-save) "\\)\\b"))

(defconst autognp-goal-command-regexp
  (concat "^\\(?:local\\s-+\\)?\\(?:" (proof-ids-to-regexp autognp-keywords-proof-goal) "\\)"
          "\\s-+\\(?:nosmt\\s-+\\)?\\(\\sw+\\)"))

(defun autognp-save-command-p (span str)
  "Decide whether argument is a [save|qed] command or not"
  (let ((txt (or (span-property span 'cmd) "")))
       (proof-string-match-safe autognp-proof-save-regexp txt)))

(defun autognp-goal-command-p (span)
  "Is SPAN a goal start?"
  ;; We support atomic undo, even inside proof scripts.
  nil)


(defun autognp-init-output-syntax-table ()
  "Set appropriate values for syntax table for AutoGnP output."
  (modify-syntax-entry ?,   " ")
  (modify-syntax-entry ?\'  "_")
  (modify-syntax-entry ?_   "_")

  ;; For comments
  (modify-syntax-entry ?\* ". 23") 

  ;; For blocks
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")
  (modify-syntax-entry ?\{ "(}")
  (modify-syntax-entry ?\} "){")
  (modify-syntax-entry ?\[ "(]")
  (modify-syntax-entry ?\] ")["))

;; ----- regular expressions

(defvar autognp-error-regexp "^\\[error-[0-9]+-[0-9]+\\]\\|^anomaly"
  "A regexp indicating that the AutoGnP process has identified an error.")

(defvar autognp-shell-proof-completed-regexp "No remaining goals"
  "*Regular expression indicating that the proof has been completed.")

(defconst autognp-any-command-regexp
  ;; allow terminator to be considered as command start:
  ;; FIXME: really needs change in generic function to take account of this,
  ;; since the end character of a command is not the start
  (concat "\\(\\s(\\|\\s)\\|\\sw\\|\\s \\|\\s_\\)*="  ;match assignments
          "\\|;;\\|;\\|" 
          (proof-ids-to-regexp autognp-global-keywords))
  "Regexp matching any AutoGnP command start or the terminator character.")

(defconst autognp-keywords-indent-open
  (append (append '("local") autognp-keywords-proof-goal)
          autognp-keywords-code-open))

(defconst autognp-keywords-indent-close
  (append autognp-keywords-proof-save
          autognp-keywords-code-close))

(defconst autognp-keywords-indent-enclose
  (append autognp-keywords-code-open
          autognp-keywords-code-close
          autognp-keywords-code-end
          autognp-keywords-proof-goal
          autognp-keywords-proof-save))

; Regular expression for indentation
(defconst autognp-indent-any-regexp
  (proof-regexp-alt autognp-any-command-regexp "\\s(" "\\s)"))
    
(defconst autognp-indent-enclose-regexp
  (proof-regexp-alt (proof-ids-to-regexp autognp-keywords-indent-enclose) "\\s)"))

(defconst autognp-indent-open-regexp
  (proof-regexp-alt (proof-ids-to-regexp autognp-keywords-indent-open) "\\s("))

(defconst autognp-indent-close-regexp
  (proof-regexp-alt (proof-ids-to-regexp autognp-keywords-indent-close) "\\s)"))

(defface autognp-tactics-closing-face
  (proof-face-specs
   (:foreground "red")
   (:foreground "red")
   ())
  "Face for names of closing tactics in proof scripts."
  :group 'proof-faces)

(defface autognp-tactics-dangerous-face
  (proof-face-specs
   (:background "red")
   (:background "red")
   ())
  "Face for names of dangerous tactics in proof scripts."
  :group 'proof-faces)

(defface autognp-tactics-tacticals-face
  (proof-face-specs
   (:foreground "dark green")
   (:foreground "dark green")
   ())
  "Face for names of tacticals in proof scripts."
  :group 'proof-faces)

(defconst autognp-tactics-closing-face   'autognp-tactics-closing-face)
(defconst autognp-tactics-dangerous-face 'autognp-tactics-dangerous-face)
(defconst autognp-tactics-tacticals-face 'autognp-tactics-tacticals-face)

(defvar autognp-font-lock-keywords
  (list
    (cons (proof-ids-to-regexp autognp-global-keywords)    'font-lock-keyword-face)
    (cons (proof-ids-to-regexp autognp-tactic-keywords)    'proof-tactics-name-face)
    (cons (proof-ids-to-regexp autognp-tactical-keywords)  'autognp-tactics-tacticals-face)
    (cons (proof-ids-to-regexp autognp-bytac-keywords)     'autognp-tactics-closing-face)
    (cons (proof-ids-to-regexp autognp-dangerous-keywords) 'autognp-tactics-dangerous-face)
    (cons (proof-ids-to-regexp autognp-prog-keywords)      'font-lock-keyword-face)
    (cons (concat autognp-operator-char-1234 "+")          'font-lock-type-face)
    (cons autognp-other-symbols                            'font-lock-type-face)))

(defun autognp-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."
  (modify-syntax-entry ?\$ ".")
  (modify-syntax-entry ?\/ ".")
  (modify-syntax-entry ?\\ ".")
  (modify-syntax-entry ?+  ".")
  (modify-syntax-entry ?-  ".")
  (modify-syntax-entry ?=  ".")
  (modify-syntax-entry ?%  ".")
  (modify-syntax-entry ?<  ".")
  (modify-syntax-entry ?>  ".")
  (modify-syntax-entry ?\& ".")
  (modify-syntax-entry ?_  "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\. ".")
  (modify-syntax-entry ?\* ". 23n")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(provide 'autognp-syntax)
