((coq-mode . ((eval . (set (make-local-variable 'coq-prog-args)
                        (list "-emacs-U" "-R" 
                          (replace-regexp-in-string "^/docker:[^:]+:" ""
                            (expand-file-name 
                              "src/coq"
                                (file-name-directory
                                  (let ((d (dir-locals-find-file ".")))
                                    (if (stringp d) d (car d))))))
                            "SpaceSearch"))))))

