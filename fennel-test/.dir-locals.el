;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((fennel-mode . ((eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis) (group word-start "assert-eq" word-end)) 1 'font-lock-keyword-face))))
                 (eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis) (group word-start "assert-ne" word-end)) 1 'font-lock-keyword-face))))
                 (eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis) (group word-start "assert-is" word-end)) 1 'font-lock-keyword-face))))
                 (eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis) (group word-start "assert-not" word-end)) 1 'font-lock-keyword-face))))
                 (eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis) (group word-start "deftest" word-end)) 1 'font-lock-keyword-face))))
                 (eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis)
                                                                      word-start "deftest" word-end
                                                                      (1+ space)
                                                                      (group (1+ (or (syntax word) (syntax symbol) "-" "_"))))
                                                                 1 'font-lock-function-name-face))))
                 (eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis) (group word-start "testing" word-end)) 1 'font-lock-keyword-face))))
                 (eval . (font-lock-add-keywords 'fennel-mode `((,(rx (syntax open-parenthesis) (group word-start "use-fixtures" word-end)) 1 'font-lock-keyword-face))))
                 (eval . (put 'deftest 'fennel-indent-function 'defun))
                 (eval . (put 'testing 'fennel-indent-function 'defun)))))
