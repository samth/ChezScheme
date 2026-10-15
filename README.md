# Portable boot files for the Racket flhypot primitive branch

Generated from the vendored Chez sources in samth/racket commit
74d4f8c493 on branch cs-flhypot-primitive. These files include the appended
flhypot library/C entries. They are intended for the matching experimental
Racket branch, whose Makefile fetches this branch as its PB bootstrap.

Regenerated with `make -j 1 re.boot SCHEME=<native-scheme>`, then rebuilt to
a fixed point with `make -j 1`. Chez fl/cfl tests pass on this PB build.

The standalone Chez implementation is on samth/ChezScheme branch
flhypot-primitive; its tracked boot files are regenerated separately from
that repository's source.
