;; This file was adapted from EasyCrypt (proofgeneral/easycrypt-abbrevs.el)

(require 'proof)
(require 'autognp-syntax)

(defpgdefault menu-entries
  '(
    ["Use Three Panes" proof-three-window-toggle
      :style    toggle
      :active   (not proof-multiple-frames-enable)
      :selected proof-three-window-enable
      :help     "Use three panes"]
))

(provide 'autognp-abbrev)
