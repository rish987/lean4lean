# Kernel reduction is not strongly normalizing (well-founded recursion / `Acc`)

This note documents a concrete, reproducible instance of the well-known fact that
**Lean's definitional reduction is not strongly normalizing**, witnessed through
this kernel reimplementation, and explains why the kernel is nonetheless safe in
practice. The reproducer is [`../EagerSNF.lean`](../EagerSNF.lean).

## TL;DR

`Nat.modCore` is defined by well-founded recursion. For a **symbolic** argument
`Nat.modCore (Nat.succ n) m` (with `n m : Nat` free variables):

* **Lazy `whnf`** (what the kernel actually uses) **terminates** — it stops at the
  stuck `Decidable.rec`/`dite` that decides the recursion guard `m ≤ n.succ`,
  which cannot reduce on a symbolic `n`.
* **Eager / strong reduction** (force `whnf` everywhere, under binders and into
  both branches) **diverges**.

So the term has a weak-head normal form but **no strong normal form**. The kernel
avoids the loop purely by being lazy; it never forces the divergent subterm.

## What actually diverges

Running the eager reducer with a 1.5M-step budget on `Nat.modCore (Nat.succ n) m`
(see `EagerSNF.lean`) blows the budget, and the visited nodes are dominated by:

```
Nat.rec  ≈ 48,600
PProd    ≈ 54,800
Acc.rec firings ≈ 0
```

The divergence is **not** an infinite `Acc.rec`-on-`Acc.intro` chain. `Acc.rec`
fires only a couple of times to expose the `dite`. The runaway is the
**unbounded expansion of the well-foundedness / accessibility _proof_** that
`WellFounded.fix` carries: Lean builds it with `Nat.rec` plus the `Nat.below`
course-of-values tower (`PProd`/`PUnit`), and for a symbolic argument that proof
is an infinitely deep structure. Forcing it under its binders re-expands the
`Nat.rec`/`below`/`PProd` structure forever.

The literal case `Nat.modCore 100 7` terminates (it reduces to `2`) with **0**
`Nat.rec`/`PProd` nodes of this kind — the concrete recursion bottoms out.

## Why the kernel is safe anyway

* `whnf` is weak-head: it returns at the stuck `Decidable.rec` without entering
  either branch, so the recursive call (and the proof it carries) is never forced.
* `isDefEq` compares lazily and closes equal subterms by congruence / pointer
  sharing, so it never needs to normalize the proof either. (Type-checking the
  `Nat.mod`/`Nat.modCore` equation lemmas is fast for this reason.)

Eager strong normalization is simply never performed by the kernel.

## How to reproduce

```
lake env lean EagerSNF.lean
```

Expected output (step counts are machine-dependent):

```
>>> eager-reduce Nat.modCore 100 7  [literal] ...
    terminated: 227987 whnf steps  (Nat.rec=0, PProd=0)
>>> eager-reduce Nat.modCore (Nat.succ n) m  [symbolic] ...
    DIVERGES (budget hit): 1500053 whnf steps  (Nat.rec=48606, PProd=54828)
```

The reducer (`force`) calls the kernel's own `whnf` at every subterm position
(head, arguments, under λ/∀ binders, into all branches). It does not rebuild
terms (it reduces only for effect), so no ill-typed intermediates are produced;
a genuine non-terminating loop is therefore not an artifact of the harness.

## Context

This was isolated while debugging [lean2dk](https://github.com/rish987/lean2dk)
(a Lean→Dedukti translator). Dedukti's untyped, rewrite-driven conversion
(`are_convertible`) reduces under binders and into both branches of a stuck
eliminator when the two sides don't match cheaply, so it is forced into exactly
this divergent region and loops — whereas Lean's lazy `isDefEq` stays out of it.
The fix belongs on the translator/conversion side (preserve sharing so the cheap
congruence shortcut fires, or keep conversion lazy at stuck eliminators), not in
making the recursor "better behaved": there is no strong normal form to reach.
