# Eventual unimodality of independence polynomials of finite forests

This repository contains a preprint and a Lean 4 formalization of eventual
unimodality for independence polynomials of finite forests. It gives a
partial result toward Erdos Problem 993.

This project grew out of personal curiosity. Its mathematical claims are
supported by a Lean 4 formalization, but they have not yet been independently
validated by a professional mathematician. The development and checking of
the proof relied heavily on LLM-based research systems. I acted as the steward
of the project throughout: I interacted continually with the systems while
learning the relevant mathematics, examined the overall proof routes, and
repeatedly decided when the exploration should change direction. Almost all
of the detailed lemma proofs and computational verification, however, were
carried out with LLMs.

Beyond the result itself, I hope this work can be observed as a case of
sustained collaboration between a human and LLM-based research systems. The
proof was produced primarily by LLMs, but it did not arise without a
mathematical history. Its principal precedents are briefly identified in the
Introduction: the original conjecture, partial monotonicity results for
independent-set sequences, hard-core recursions on rooted trees, and the
martingale and local-limit methods used in the proof. Those earlier lines of
work deserve substantive credit for the path by which the proof was reached.

The research process did not jump directly to the final argument. It explored
many possible approaches, progressively extending results from special classes
to more general settings and drawing on a wider range of existing mathematics
along the way. Some of the
intermediate lemmas and sources that shaped this progression no longer appear
directly in the final proof. Such contributions are easy for an LLM workflow
to flatten or forget, even in a proof produced by GPT-5.6 Pro. I believe
that this broader lineage is an important part of assigning credit in
LLM-based mathematical research. The agent system I designed retained a
detailed record of the process, and a separate account of the human--LLM
interaction and the intermediate development of the proof is in preparation.

## Main result

For a finite forest `F`, write

```text
I_F(x) = sum_k i_k(F) x^k,
```

where `i_k(F)` is the number of independent vertex sets of cardinality `k`.
The manuscript proves that there is an integer `N_0` such that the coefficient
sequence of `I_F` is unimodal whenever `F` has at least `N_0` vertices. In
particular, the conclusion holds for every sufficiently large connected tree.

The result does **not** settle the all-orders form of Erdos Problem 993. The
threshold is existential and noncomputable in the present proof, and finitely
many smaller orders remain untreated.

## Contents

- [`paper/eventual_forest_unimodality.pdf`](eventual_forest_unimodality.pdf)
  is the version of record for this release.
- [`paper/eventual_forest_unimodality.md`](paper/eventual_forest_unimodality.md)
  is its Markdown source.
- [`lean/`](lean/) contains the Lean 4 formalization.
- [`paper/supplementary/h_drg_actual_rooted_trees.md`](paper/supplementary/h_drg_actual_rooted_trees.md)
  records a separate supplementary theorem developed during the project. It is
  not a dependency of the main proof.

## Lean formalization

The public theorem is:

```lean
Erdos993.Forest.eventual_forest_unimodality :
  ∃ orderThreshold : ℕ,
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G.IsAcyclic → orderThreshold ≤ Fintype.card V →
        Erdos993.Forest.WeaklyUnimodal
          (Erdos993.Forest.independenceCoefficients G)
```

The package pins Lean `v4.29.0` version. To build it:

```bash
cd lean
lake build Erdos993
```

See [`lean/README.md`](lean/README.md) for the formal statement, dependency
information, and build instructions.

## Research status and disclosure

This is a preprint and has not undergone independent review by professional
mathematicians. The roles of the LLM systems and of human supervision are
described above and in the disclosure included in the manuscript. As the named
author, I take responsibility for the claims, citations, and presentation I
am making public.

## Citation

Citation metadata are provided in [`CITATION.cff`](CITATION.cff). Until a DOI
or archival identifier is assigned, the repository release URL identifies this
version:

```bibtex
@misc{zou2026eventual,
  author       = {Ziheng Zou},
  title        = {Eventual unimodality of independence polynomials of finite forests},
  year         = {2026},
  howpublished = {Preprint},
  url          = {https://github.com/zouzh14/erdos-993-eventual}
}
```

## License

The manuscript and other paper materials are licensed under CC BY 4.0. The
original Lean source is licensed under Apache-2.0. See [`LICENSE`](LICENSE).
