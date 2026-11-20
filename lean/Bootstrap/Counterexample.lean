import Bootstrap.BoundedHosts
import Bootstrap.RuleEdgeCount
import Bootstrap.RuleConnectivity
import Bootstrap.SourceWidth
import Bootstrap.TreeSemantics

/-! The published Theorem III.1, with all properties witnessed by one rule. -/
namespace Bootstrap.Preprint

open scoped Classical
set_option maxRecDepth 8000

open MarkedSimulation RuleStructure

abbrev RuleVertex := Localization.HostVertex sourceCode

/-- The index graph is a genuine tree and each occurrence set induces a connected graph. -/
theorem ordinary_treewidth_two :
    TreeSemantics.WidthLE ordinaryRule 2 ∧ ¬TreeSemantics.WidthLE ordinaryRule 1 := by
  classical
  obtain ⟨x,y,z,xy,xz,yz⟩ := SourceBags.source_triangle
  exact ⟨TreeSemantics.of_parent_bags SourceBags.source_width_at_most_two,
    TreeSemantics.triangle_forbids_width_one _ xy xz yz⟩

/-- The single ordinary rule, its ordinary hosts and the bounded-degree all-orders statement. -/
theorem theorem_III_1 :
    Fintype.card RuleVertex = 166464 ∧ ordinaryRule.edgeFinset.card = 332894 ∧
    ordinaryRule.Connected ∧ (∀ z : RuleVertex, (ordinaryRule.induce {x | x ≠ z}).Connected) ∧
    ordinaryRule.minDegree = 2 ∧
    (TreeSemantics.WidthLE ordinaryRule 2 ∧ ¬TreeSemantics.WidthLE ordinaryRule 1) ∧
    (∀ p q : ℕ, 3 ≤ p → 3 ≤ q →
      Fintype.card (OrdinaryVertex (Fin p) (Fin q)) = 69360*(p+q) ∧
      (initial p q).Connected ∧ BoundedDegree (initial p q) 14016 ∧
      stabilizationTime ordinaryRule (initial p q) = p.lcm q / 2) ∧
    HasQuadraticOrder ordinaryRule ∧ ¬HasLinearUpper ordinaryRule ∧
    (∀ n ≥ 624240, n*n ≤ ((277440*277440)*2) * boundedMaxTime ordinaryRule 14016 n) ∧
    (∀ n, boundedMaxTime ordinaryRule 14016 n ≤ n*n) := by
  refine ⟨source_order, RuleEdgeCount.source_edge_count, RuleConnectivity.source_connected,
    RuleConnectivity.source_deleted_connected, source_minDegree, ordinary_treewidth_two, ?_,
    ordinary_quadratic, ordinary_not_linear, bounded_quadratic⟩
  intro p q hp hq
  exact ⟨host_order p q, initial_connected (by omega) (by omega), initial_maxDegree_le
    (by omega) (by omega), ordinary_time hp hq⟩

/-- Direct negation of the universal treewidth-two linear upper bound, including connected rules. -/
theorem counterexample :
    ∃ H : SimpleGraph RuleVertex, H.Connected ∧ TreeSemantics.WidthLE H 2 ∧
      ¬TreeSemantics.WidthLE H 1 ∧ ¬ HasLinearUpper H :=
  ⟨ordinaryRule, RuleConnectivity.source_connected, ordinary_treewidth_two.1,
    ordinary_treewidth_two.2, ordinary_not_linear⟩

end Bootstrap.Preprint

#print axioms Bootstrap.Preprint.ordinary_treewidth_two
#print axioms Bootstrap.Preprint.theorem_III_1
#print axioms Bootstrap.Preprint.counterexample
