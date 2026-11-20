import Bootstrap.DegreeTwoTheorem
import Bootstrap.CounterexampleDetails
import Bootstrap.ExtensionOperation
import Bootstrap.ThetaBags
import Bootstrap.ThetaConnectivity
import Bootstrap.QuantitativeLongRoute
import Bootstrap.VertexCover

/-! Entrypoint for the three parts and Appendix A of the published preprint. -/
namespace Bootstrap.Preprint

open Theta

/-- The preliminary width assertion for every multi-arm graph (including every three-arm theta). -/
theorem theta_treewidth_two {k : ℕ} (m : Fin k → ℕ) (hk : 2 ≤ k) :
    TreeSemantics.WidthLE (Theta.graph m) 2 ∧ ¬TreeSemantics.WidthLE (Theta.graph m) 1 := by
  classical
  exact ⟨Theta.standard_width_two m,
    Suppression.forbids_standard_width_one (Theta.twoConnected m hk) (Theta.parent_width_two m)⟩

end Bootstrap.Preprint

#print axioms Bootstrap.Theta.theorem_I_1
#print axioms Bootstrap.Theta.theta_family_order
#print axioms Bootstrap.DegreeTwo.theorem_II_1
#print axioms Bootstrap.DegreeTwo.lemma_II_2
#print axioms Bootstrap.Suppression.corollary_forward
#print axioms Bootstrap.Preprint.theorem_III_1
#print axioms Bootstrap.Subdivision.once_subdivision_linear
#print axioms Bootstrap.Preprint.theta_treewidth_two
