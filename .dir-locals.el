((coq-mode . ((eval .
  (let ((root (replace-regexp-in-string "^/\\(\\(ssh\\|docker\\):[^:|]+[:|]\\)+" ""
                (file-name-directory
                  (let ((d (dir-locals-find-file ".")))
                    (if (stringp d) d (car d)))))))
    (set (make-local-variable 'coq-prog-args) (list
      "-emacs-U" "-R" (expand-file-name "src/coq" root) "SpaceSearch")))))))
