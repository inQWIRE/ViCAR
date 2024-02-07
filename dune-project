(lang dune 2.8)
(name coq-vicar)
(version 0.1.0)
(using coq 0.2)

(generate_opam_files true)

(license MIT)
(authors "inQWIRE")
(maintainers "inQWIRE Developers")
(source (github inQWIRE/ViCaR))

(package
 (name coq-vicar)
 (synopsis "Coq library reasoning about categorical string diagrams")
 (description "\| inQWIRE's ViCaR is a library for reasoning about
              "\|  categorical string diagrams
 )

 (depends
   (coq (>= 8.12))))
