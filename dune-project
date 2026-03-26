(lang dune 3.21)

(subst disabled)

(using coq 0.8)

(warnings (deprecated_coq_lang disabled))

(using menhir 2.1)

(name bits-rocq)

(generate_opam_files true)

(source
 (github henrytill/bits-rocq))

(authors "Henry Till <henrytill@gmail.com>")

(maintainers "Henry Till <henrytill@gmail.com>")

(package
 (name bits-rocq)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  menhir
  (coq
   (>= 9.0.0))
  coq-equations
  coq-mathcomp-boot
  coq-mathcomp-order
  coq-menhirlib
  (ppx_deriving
   (and
    :with-test
    (>= 6.0.3)))
  (ppx_import
   (and
    :with-test
    (>= 1.11.0)))
  (alcotest
   (and
    :with-test
    (>= 1.7.0))))
 (tags
  (topics "to describe" your project)))
