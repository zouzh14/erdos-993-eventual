# Erdos 993: Eventual Forest Unimodality

This Lean 4 package formalizes eventual weak unimodality of the independence
polynomial of every finite forest.

## Main theorem

```lean
Erdos993.Forest.eventual_forest_unimodality :
  ∃ orderThreshold : ℕ,
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G.IsAcyclic → orderThreshold ≤ Fintype.card V →
        Erdos993.Forest.WeaklyUnimodal
          (Erdos993.Forest.independenceCoefficients G)
```

The theorem has no mathematical interface hypotheses. It assembles the proved
Appendix C.7 first-recovery-scale interface, Appendix D.1 macroscopic
contribution interface, and the actual occupation-balance interface.

This is an eventual theorem: the threshold is existential and noncomputable,
and forests below it are not covered. The package therefore does not formalize
the full all-orders Erdos 993 conjecture.

## Use

For the narrow public entry point:

```lean
import Erdos993.Eventual

#check Erdos993.Forest.eventual_forest_unimodality
```

`import Erdos993` remains the umbrella import for the complete formalization.
The root file keeps the conventional Lean module name `Erdos993.lean`; filenames
with spaces are deliberately avoided.

## Build

The pinned environment is Lean `v4.29.0` with Mathlib revision
`8a178386ffc0f5fef0b77738bb5449d50efeea95`.

```bash
lake update
lake build Erdos993
```

The distributed source tree excludes `.lake` and all ORIA3 runtime data.

`SHA256SUMS` authenticates every distributed file except the checksum manifest
itself.
