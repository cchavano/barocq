(defun match-symbol (X) (apply 'concat (list "\\<" X "\\>")))

(defconst barocq-font-lock-defaults
(let ((keywords '("let" "type" "module" "record" "decl" "defn" "if" "then" "else" "in" "as"))
        (types '("str" "u8" "u16" "u32" "u64" "i8" "i16" "i32" "i64")))
    `(((,(match-symbol (rx-to-string `(: (or ,@keywords)))) 0 font-lock-keyword-face)
       ("\\([[:word:]]+\\)\s*(" 1 font-lock-function-name-face)
       (,(match-symbol (rx-to-string `(: (or ,@types)))) 0 font-lock-type-face)))))


(require 'ocp-indent)

(defun barocq-mode ()
"barocq mode"
(interactive)
(setq mode-name "barocq")
(setq-local indent-line-function  #'ocp-indent-line)
(set-syntax-table (make-syntax-table))
(progn
;; clear the comment syntax of standard syntax table
(modify-syntax-entry ?# ".")
(modify-syntax-entry ?\n ".")
(modify-syntax-entry ?_ "w")
(modify-syntax-entry ?\("()1n")
(modify-syntax-entry ?\) ")(4n")
(modify-syntax-entry ?* ". 23n")
(setq font-lock-defaults barocq-font-lock-defaults)
(font-lock-fontify-buffer)))


