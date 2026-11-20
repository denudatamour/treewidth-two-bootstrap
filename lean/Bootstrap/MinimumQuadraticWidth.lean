import Bootstrap.WidthOneDegenerate
import Bootstrap.TreeSparseEmbedding
import Bootstrap.Counterexample

namespace Bootstrap.Preprint

/-- Finite connected rules with a quadratic maximum running time, grouped by
the upper bound on their ordinary treewidth. -/
def ConnectedQuadraticWidth (k : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (H : SimpleGraph V),
    H.Connected ∧ TreeSemantics.WidthLE H k ∧ HasQuadraticOrder H

/-- Width at most one gives linear maximum running time on arbitrary labelled hosts.
This also covers disconnected rules and rules of order zero, one or two. -/
theorem width_one_linear {V : Type*} [Fintype V] {H : SimpleGraph V}
    (width : TreeSemantics.WidthLE H 1) : HasLinearUpper H :=
  TreeLinear.linear_of_degenerate H (TreeLinear.oneDegenerate_of_width_one width)

private theorem width_mono {V : Type*} {H : SimpleGraph V} {k l : ℕ}
    (hk : TreeSemantics.WidthLE H k) (le : k≤l) : TreeSemantics.WidthLE H l := by
  obtain ⟨J,inst,⟨D⟩⟩ := hk
  exact ⟨J,inst,⟨⟨D.tree,D.isTree,D.bag,fun i => (D.width i).trans (by omega),
    D.vertex,D.edge,D.running⟩⟩⟩

/-- Two is exactly the least treewidth at which a fixed finite connected rule
can have quadratic-order maximum stabilization time. -/
theorem minimum_quadratic_treewidth : IsLeast {k : ℕ | ConnectedQuadraticWidth k} 2 := by
  constructor
  · exact ⟨RuleVertex,inferInstance,MarkedSimulation.ordinaryRule,RuleConnectivity.source_connected,
      ordinary_treewidth_two.1,ordinary_quadratic⟩
  · rintro k ⟨V,inst,H,_,width,hq⟩
    letI := inst
    by_contra! small
    have upper : HasLinearUpper H := width_one_linear (width_mono width (by omega : k≤1))
    exact quadratic_excludes_linear H hq upper

end Bootstrap.Preprint

#print axioms Bootstrap.Preprint.width_one_linear
#print axioms Bootstrap.Preprint.minimum_quadratic_treewidth
