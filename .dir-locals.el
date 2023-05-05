;;; Directory Local Variables            -*- no-byte-compile: t -*-
;;; For more information see (info "(emacs) Directory Variables")

((nil . ((project-compilation-mode . fennel-compilation-mode)))
 (fennel-mode . ((eval . (put 'go 'fennel-indent-function 0))
                 (eval . (put 'go-loop 'fennel-indent-function 1)))))
