;; This file was adapted from EasyCrypt (proofgeneral/easycrypt.el)

(require 'proof)
(require 'autognp-syntax)
(require 'autognp-hooks)
(require 'autognp-abbrev)

(add-to-list 'hs-special-modes-alist
  '(autognp-mode "{" "}" "/[*/]" nil nil))

(defcustom autognp-prog-name "autognp -emacs"
  "*Name of program to run Autognp."
  :type  'file
  :group 'autognp)

(defcustom autognp-web-page
  "http://www.github.com/ZooCrypt/AutoGnP"
  "URL of web page for AutoGnP."
  :type  'string
  :group 'autognp-config)

;; --------------------------------------------------------------------
;; Generic mode

(defun autognp-encode-cmd (filename start end string)
  "encode command for AutoGnP"
  (replace-regexp-in-string "\n" "\\\\<^newline>" string))

(defun autognp-config ()
  "Configure Proof General scripting for Autognp."
  (autognp-init-output-syntax-table)
  
  (setq  proof-terminal-string                 autognp-terminal-string)
  (setq  proof-script-command-end-regexp       autognp-command-end-regexp)

  (setq  proof-script-comment-start            "(*"
         proof-script-comment-end              "*)")
  
  ;; For undo
  (setq  proof-find-and-forget-fn              'autognp-find-and-forget
         proof-completed-proof-behaviour       nil
         proof-non-undoables-regexp            autognp-non-undoables-regexp
         proof-shell-restart-cmd               nil)

  (set (make-local-variable 'comment-quote-nested) nil)

  ;; For func-menu and finding goal...save regions
  (setq  proof-save-command-regexp             autognp-proof-save-regexp
         proof-really-save-command-p           'autognp-save-command-p
         proof-save-with-hole-regexp           nil
         proof-goal-command-p                  'autognp-goal-command-p
         proof-goal-with-hole-regexp           autognp-goal-command-regexp
         proof-goal-with-hole-result           1)

  (setq  proof-goal-command                    "lemma %s: ."
         proof-save-command                    "qed.")
  
  (setq  proof-prog-name                       autognp-prog-name
         proof-assistant-home-page             autognp-web-page)

  ; Options
  (setq  proof-three-window-enable             t
         proof-three-window-mode-policy        (quote hybrid)
         proof-auto-multiple-files             t)

  ; Setting indents 
  (set   (make-local-variable 'indent-tabs-mode) nil)
  (setq  proof-indent-enclose-offset   (- proof-indent)
         proof-indent-open-offset     0
         proof-indent-close-offset    0
         proof-indent-any-regexp      autognp-indent-any-regexp
         proof-indent-enclose-regexp  autognp-indent-enclose-regexp
         proof-indent-open-regexp     autognp-indent-open-regexp
         proof-indent-close-regexp    autognp-indent-close-regexp)

  ; Ask for the current goal
  (setq proof-showproof-command "pragma noop. ") ;; FIXME

  (autognp-init-syntax-table)
  ;; we can cope with nested comments
  (set (make-local-variable 'comment-quote-nested) nil)

  (setq proof-script-preprocess 'autognp-encode-cmd)

  (setq  proof-script-font-lock-keywords
         autognp-font-lock-keywords))

(defun autognp-shell-config ()
  "Configure Proof General shell for AutoGnP."
  (autognp-init-output-syntax-table)
  (setq  proof-shell-auto-terminate-commands    autognp-terminal-string)
  (setq  proof-shell-eager-annotation-start     "^\\[W\\] *")
  (setq  proof-shell-strip-crs-from-input       nil)
  (setq  proof-shell-annotated-prompt-regexp    "^\\[[0-9]+\\]>")
  (setq  proof-shell-clear-goals-regexp         autognp-shell-proof-completed-regexp)
  (setq  proof-shell-proof-completed-regexp     autognp-shell-proof-completed-regexp)
  (setq  proof-shell-error-regexp               autognp-error-regexp)
  (setq  proof-shell-truncate-before-error      nil)
  (setq  proof-shell-start-goals-regexp         "^Current")
  (setq  proof-shell-end-goals-regexp           nil)  ; up to next prompt
  (setq  proof-shell-font-lock-keywords         autognp-font-lock-keywords))

;; --------------------------------------------------------------------
;; Derived modes

(define-derived-mode autognp-mode proof-mode
  "AutoGnP script" nil
  (autognp-config)
  (proof-config-done))

(define-derived-mode autognp-shell-mode proof-shell-mode
  "AutoGnP shell" nil
  (autognp-shell-config)
  (proof-shell-config-done))

(define-derived-mode autognp-response-mode proof-response-mode
  "AutoGnP response" nil
  (autognp-init-output-syntax-table)
  (setq  proof-response-font-lock-keywords 
         autognp-font-lock-keywords)
  (proof-response-config-done))

(define-derived-mode autognp-goals-mode proof-goals-mode
  "AutoGnP goals" nil
  (autognp-init-output-syntax-table)
  (setq  proof-goals-font-lock-keywords 
         autognp-font-lock-keywords)
  (proof-goals-config-done))

(defun autognp-get-last-error-location () 
  "Remove [error] in the error message and extract the position
  and length of the error "
  (proof-with-current-buffer-if-exists proof-response-buffer

     (goto-char (point-max))
     (when (re-search-backward "\\[error-\\([0-9]+\\)-\\([0-9]+\\)\\]" nil t)
        (let* ((inhibit-read-only t)
               (pos1 (string-to-number (match-string 1)))
               (pos2 (string-to-number (match-string 2)))
               (len (- pos2 pos1)))

              (delete-region (match-beginning 0) (match-end 0))
              (list pos1 len)))))

(defun autognp-advance-until-command ()
   (while (proof-looking-at "\\s-") (forward-char 1)))

(defun autognp-highlight-error ()
  "Use 'autognp-get-last-error-location' to know the position
  of the error and then highlight in the script buffer"
  (proof-with-current-buffer-if-exists proof-script-buffer
    (let ((mtch (autognp-get-last-error-location)))
        (when mtch
          (let ((pos (car mtch))
                  (lgth (cadr mtch)))
          (if (eq (proof-unprocessed-begin) (point-min))
                (goto-char (proof-unprocessed-begin))
                (goto-char (+ (proof-unprocessed-begin) 1)))
            (autognp-advance-until-command)
             (goto-char (+ (point) pos))
             (span-make-self-removing-span
               (point) (+ (point) lgth)
               'face 'proof-script-highlight-error-face))))))

(defun autognp-highlight-error-hook ()
  (autognp-highlight-error))

(defun autognp-redisplay-hook ()
  (autognp-redisplay))

(add-hook 'proof-shell-handle-error-or-interrupt-hook
          'autognp-highlight-error-hook t)

;; --------------------------------------------------------------------
;; 3-window pane layout hack
(add-hook
  'proof-activate-scripting-hook
  '(lambda () (when proof-three-window-enable (proof-layout-windows))))

;; --------------------------------------------------------------------
(provide 'autognp)
