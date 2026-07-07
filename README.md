# Polynomial Hilbert-Schmidt Stability of the Lamplighter Group

This repository contains a Lean 4 formalization of the main theorem from
Alon Dogon and Thomas Vidick's paper *Polynomial Hilbert-Schmidt stability of
the lamplighter group*.

The exported theorem is:

```lean
LamplighterStability.lamplighter_HS_stability
```

It states that there exist universal constants `C, c > 0` such that every
pair of finite-dimensional unitaries `A, T` satisfying the prescribed
approximate order-two and orbit-commutator hypotheses can be perturbed, in
normalized Hilbert-Schmidt norm, to genuine unitaries `A'`, `T'` with
`A'^2 = 1` and a commuting orbit.

The file `statement_comparison.md` contains a complete statement of the theorem in latex and a point-by-point comparison with the statement in Lean. 

## Build

This project uses Lean `v4.28.0` and Mathlib `v4.28.0`.

```bash
lake exe cache get
lake build
```

## Axiom Audit

After building, run:

```lean
import RequestProject
#print axioms LamplighterStability.lamplighter_HS_stability
```

Expected output:

```text
[propext, Classical.choice, Quot.sound]
```

## Comparator

The statement-only comparator challenge is maintained in the companion public
repository:

```text
https://github.com/vidick/lamplighter-comparator
```

There, `Challenge.lean` imports only Mathlib and states the theorem, while
`Solution.lean` bridges the challenge statement to this repository's exported
theorem.
