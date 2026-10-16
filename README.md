# Portable boot files for the Racket flhypot primitive branch

Generated from the vendored Chez sources in samth/racket commit
758453b8e6 on branch cs-flhypot-primitive. These files include the flhypot library/C entries grouped with the other
floating-point operations. They are intended for the matching experimental
Racket branch, whose Makefile fetches this branch as its PB bootstrap.

Regenerated with `make -j 2 re.boot SCHEME=<native-scheme>` and used with
a matching PB kernel. These indices differ from the earlier
flhypot-primitive-pb branch.

The standalone Chez implementation is on samth/ChezScheme branch
flhypot-primitive; its tracked boot files are regenerated separately from
that repository's source.
