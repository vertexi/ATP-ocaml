(lang dune 3.18)

(name ocamlplay)

(generate_opam_files true)

(map_workspace_root false)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name ocamlplay)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune camlp5)
 (allow_empty)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
