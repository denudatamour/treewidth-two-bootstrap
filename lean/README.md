# Lean proofs for *From theta graphs to quadratic time in graph bootstrap percolation*

Haimin Zhou · Independent Researcher · haiminzhou.1@gmail.com

This Lean 4 project accompanies preprint v1.0. It uses ordinary synchronous graph bootstrap percolation. A round adds all missing edges witnessed by an injective copy of the fixed rule with one edge deleted. The largest stabilization time is taken over all simple starting graphs on a given number of vertices. [Read the preprint](https://github.com/denudatamour/treewidth-two-bootstrap/releases/tag/preprint-v1.0)

| Result | Lean source |
| --- | --- |
| Theorem I.1. Every fixed three-arm theta with lengths at least two has linear maximum running time. | [`theorem_I_1`](Bootstrap/DegreeTwoTheorem.lean) |
| For three arm lengths at least two, the theta self-closure is a clique if the parities are mixed. If all three lengths have the same parity and at least two lengths differ, the closure is complete bipartite on the natural colour classes. Three equal lengths leave the original graph stable. | [`self_closure_classification`](Bootstrap/ThetaClosureClassification.lean) |
| Theorem II.1. If every edge of a connected rule has a degree-two endpoint, maximum running time is at most linear. The bound is sharp when the minimum degree is at least two and the maximum degree is at least three. | [`theorem_II_1`](Bootstrap/DegreeTwoTheorem.lean) |
| Lemma II.2 and Corollary II.3. Degree-two vertices propagate adjacency along a route. A degree-two extension can take a rule of treewidth two beyond linear time. | [`lemma_II_2`](Bootstrap/CompleteRoute.lean) · [`corollary_forward`](Bootstrap/ExtensionOperation.lean) |
| Theorem III.1. One fixed 2-connected rule of treewidth two on 166,464 vertices has quadratic maximum running time. Its connected starting graphs for periods `p,q ≥ 3` stabilize in exactly `⌊lcm(p,q)/2⌋` rounds. | [`theorem_III_1`](Bootstrap/Counterexample.lean) |
| Appendix A. Subdividing every edge of a finite connected loopless multigraph once gives a rule with a linear time bound. For a base graph with at least two vertices, the displayed budget counts distinct newly born edges for each choice of witnesses. | [`once_subdivision_linear`](Bootstrap/SubdivisionLinear.lean) · [`displayed_edge_budget`](Bootstrap/AppendixEdgeBudget.lean) |
| Two is the least treewidth at which a fixed connected rule can have quadratic maximum running time. | [`minimum_quadratic_treewidth`](Bootstrap/MinimumQuadraticWidth.lean) |

## Reproduce the checks

With Lean's toolchain manager Elan installed, run the following commands in the directory containing `lean-toolchain`. This is the `lean/` directory in the repository. The toolchain file selects Lean 4.19.0. The Lake manifest pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and records its dependencies. The first command fetches an optional build cache.

```sh
lake exe cache get
lake build
lake env lean --run ReplayAudit.lean
```

The build starts from [Bootstrap.lean](Bootstrap.lean). The [replay program](ReplayAudit.lean) checks each module's safe declarations against its direct imports and reports their transitive axioms. The v037 source check covered 120 project modules and 3,577 safe declarations. The compiler produced a further 1,218 implementation declarations marked unsafe or partial. The proofs use only `Classical.choice`, `propext` and `Quot.sound`. [Counts by module](verification/modules.tsv)

To compare the distributed files with their recorded SHA-256 digests, run `sha256sum -c SHA256SUMS` in the same directory. [File checksums](SHA256SUMS)

This research was conducted with AI assistance.
