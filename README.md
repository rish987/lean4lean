# Lean-for-Lean

This is a fork of [lean4lean](https://github.com/digama0/lean4lean) adapted for use with [lean4less](https://github.com/rish987/lean4lean).

## Building

Install [Lean and elan](https://lean-lang.org/lean4/doc/quickstart.html) and run:

```
lake build
```

## Running

After `lake build lean4lean`, the executable will be in `.lake/build/bin/lean4lean`. Because it requires some environment variables to be set for search paths which are provided by lake, you should evaluate it like `lake env .lake/build/bin/lean4lean`.

> `lean4lean [--fresh] [--verbose] [--compare] [--search-path path] [--no-proof-irrel] [--no-klr] [MOD]`

* `MOD`: a required lean module name to load the environment for typechecking, like `Init.Classical`.
* `--fresh`: Only valid when a `MOD` is provided. In this mode, the module and all its imports will be rebuilt from scratch, checking all dependencies of the module. The behavior without the flag is to only check the module itself, assuming all imports are correct.
* `--search-path` (`-s`): Set search path directory
* `--no-proof-irrel` (`-npi`): Disable proof irrelevance
* `--no-klike-red` (`-nklr`): Disable k-like reduction

For example, to typecheck the output of Lean4Less after elimination proof irrelevance and K-like reduction:
```
 $ (cd ~/projects/mathlib4/ && lake env ~/projects/lean4lean/.lake/build/bin/lean4lean -nklr -npi --fresh -s out Mathlib.Data.Real.Basic)

```
