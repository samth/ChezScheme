# Explicit CI session keys; ordinary defaults restored

The automatic-default experiment has been removed. `configure`,
`makefiles/lib.zuo` and `BUILDING` match the upstream baseline. The existing
`--sessionkey=...` option retains its per-action formula; `auto` is again just an
ordinary explicitly supplied string. Normal builds do not set a session key.
The audited C/configuration/library/output dependency fixes are preserved.

The narrowed CI prototype is in `samth/racket`, branch
`prototype/ci-boot-session-key`: a CI-only Zuo helper derives a key from Chez,
PB, compiler and build inputs, and an opt-in adapter forwards it to the existing
Chez option. It does not change this checkout's runtime/default behavior.

`tools/build-key-probe.py` verifies no default override and the exact upstream
explicit-key formula. `tools/reproducible-boot-probe.py` now requires
`--sessionkey=...` and compares explicitly seeded builds with builds passing no
option. Its former automatic-mode options have been removed.

Earlier automatic-default boot manifests are historical evidence only. The
current CI prototype carries paired seeded/default boot evidence and normal
Racket PB-to-native bootstrap evidence. `prototype-evidence/dependency-fixes.json`
retains the standalone dependency regression results. Use fresh output directories
when changing key policy, as required by the upstream explicit-key option.
