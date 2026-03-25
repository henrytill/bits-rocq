(lang dune 3.21)

(subst disabled)

(using rocq 0.11)

(using menhir 3.0)

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
  (rocq-prover
   (>= 9.0.0))
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
