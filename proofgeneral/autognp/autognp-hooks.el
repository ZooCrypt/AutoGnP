;; This file was adapted from EasyCrypt (proofgeneral/easycrypt-hooks.el)

(require 'span)
(require 'proof)

(defvar autognp-last-but-one-statenum 0)

;; Function for set or get the information in the span
(defsubst autognp-get-span-statenum (span)
  "Return the state number of the SPAN."
  (span-property span 'statenum))

(defsubst autognp-set-span-statenum (span val)
  "Set the state number of the SPAN to VAL."
  (span-set-property span 'statenum val))

(defsubst proof-last-locked-span ()
  (with-current-buffer proof-script-buffer
  (span-at (- (proof-unprocessed-begin) 1) 'type)))

(defun autognp-last-prompt-info (s)
  "Extract the information from prompt."
  (let ((lastprompt (or s (error "no prompt"))))
     (when (string-match "\\[\\([0-9]+\\)\\]" lastprompt)
           (string-to-number (match-string 1 lastprompt)))))

(defun autognp-last-prompt-info-safe ()
  "Take from `proof-shell-last-prompt' the last information in the prompt."
  (autognp-last-prompt-info proof-shell-last-prompt))

(defun autognp-set-state-infos ()
  "Set information necessary for backtracking."
  (if proof-shell-last-prompt
     ;; sp       = last locked span, which we want to fill with prompt infos
     ;; statenum = statenum of the very last prompt
     (let ((sp       (if proof-script-buffer (proof-last-locked-span)))
           (statenum (or (autognp-last-prompt-info-safe) 0)))

       (unless (or (not sp) (autognp-get-span-statenum sp))
         (autognp-set-span-statenum sp autognp-last-but-one-statenum))
       (setq autognp-last-but-one-statenum statenum))))

(add-hook 'proof-state-change-hook 'autognp-set-state-infos)

(defun autognp-find-and-forget (span)
  (let ((span-staten (autognp-get-span-statenum span)))
       (list (format "undo %s." (int-to-string span-staten)))))

(provide 'autognp-hooks)
