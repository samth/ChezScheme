# Automatic reproducible boot identities: prototype

Based on upstream `68a0bc5e` (which already includes PR #1079's optional
`--sessionkey=` machinery). Configure now defaults to `--sessionkey=auto`.
No runtime-wide gensym policy is changed. Passing `--sessionkey=` opts out;
explicit custom keys retain the previous behavior.

Automatic keys include a digest of Scheme/compiler source trees, the actual
compiler executable, action script, startup inputs, host machine/arguments,
and the existing per-action/output scope. They are computed only by build
drivers. Source hashing avoids assigning the same unit namespace to changed
source. The entire source context is conservative, and this does not promise
identical output between incremental and clean builds or across build paths.
This is a prototype to evaluate automatic naming, not a general FASL normalizer
or artifact cache. Do not use a single global fixed gensym prefix.

## Measured on Linux x86-64, 2026-11-06

Two fresh bootquick builds with automatic keys produced **8/8 byte-identical**
boot/header files. Two with `--sessionkey=` produced 6/8 identical files;
`petite.boot` and `scheme.boot` differed. Each used the same source root, build
root and native bootstrap host. Automatic runs took 17.72 and 16.78 seconds;
opt-out runs took 21.94 and 21.32 seconds. These single-run timings overlap
other local work and are not a controlled overhead estimate or CI speedup.

The normal PB-to-native build also completed successfully using the checked-in
PB boots, without first generating native boots using the external host.
A native compiler built from the automatic boot group passed arithmetic/hash
smoke checks. Independent executions generated different ordinary gensym
unique names, confirming that application naming remains random.

Reproduce the boot comparison with Python 3 and an existing native Chez:

```sh
python3 tools/reproducible-boot-probe.py \
  --zuo /absolute/path/to/zuo \
  --host-scheme '/absolute/native/scheme -B /absolute/native/petite.boot -B /absolute/native/scheme.boot'
```

The script retains command exit statuses, full logs and SHA-256 manifests in a
new evidence directory. It never modifies the source checkout. Other platforms,
profiled builds, and configurations need broader evaluation. A separately
pushed Racket branch mirrors this in its **bundled** Chez sources; updating this
checkout alone does not change Racket's build.

The fast build-key probe also checks stable keys, invalidation after source,
script or action changes, empty-key opt-out, and the exact legacy custom-key
preimage: `python3 tools/build-key-probe.py --zuo /absolute/path/to/zuo`.
Compact command/status/timing and boot hash evidence is in
`prototype-evidence/boot-results.json`. Complete logs remain in the local
investigation workspace.
