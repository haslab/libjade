((easycrypt-mode .
  ((eval .
    (cl-flet ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
      (setq easycrypt-load-path `(,(pre ".")))
      (setq easycrypt-prog-args  `("-emacs", "-pp-width", "120",
				   "-I", (concat "JExtract:" (pre "extracted/default"))
				   "-R", (pre ".")
				   )
	    )
      )
    ))
))
