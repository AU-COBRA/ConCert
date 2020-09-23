(require 'package)
(setq package-enable-at-startup nil)
(add-to-list 'package-archives
             '("melpa" . "https://melpa.org/packages/"))

(package-initialize)

;; Bootstrap use-package
(unless (package-installed-p 'use-package)
    (package-refresh-contents)
    (package-install 'use-package))

(use-package proof-general
  :no-require t
  :ensure t)
