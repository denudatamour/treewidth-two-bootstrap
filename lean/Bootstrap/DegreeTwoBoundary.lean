import Bootstrap.FMSLinearLower
import Bootstrap.ThetaRules

namespace Bootstrap

variable {W : Type*}

/-- A rule with no edges has stabilization time zero at every host order. -/
theorem maxTime_edgeless (n : ℕ) : maxTime (⊥ : SimpleGraph W) n = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply (maxTime_le_iff _ _ _).mpr
  intro G
  have fixed : run (⊥ : SimpleGraph W) G 0 = run (⊥ : SimpleGraph W) G (0+1) :=
    (step_empty_rule G).symm
  exact Nat.find_min' (stable_exists _ _) fixed

/-- Includes both an empty rule and a one-vertex rule. -/
theorem maxTime_subsingleton_rule [Subsingleton W] (H : SimpleGraph W) (n : ℕ) :
    maxTime H n = 0 := by
  have eq : H = ⊥ := by
    ext i j
    rw [Subsingleton.elim i j]
    simp
  rw [eq,maxTime_edgeless]

theorem maxTime_empty_host (H : SimpleGraph W) : maxTime H 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using maxTime_le_choose H 0

namespace DegreeTwo

/-- The exact lower-bound assumptions stated in Theorem II.1. -/
theorem linear_lower_of_extremes [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (minimum : 2 ≤ H.minDegree) (maximum : 3 ≤ H.maxDegree) : HasLinearLower H := by
  letI : Nonempty W := conn.nonempty
  obtain ⟨w,maximal⟩ := H.exists_maximal_degree_vertex
  exact FMS.linear_lower_of_edge_cover H conn cover (fun i => minimum.trans (H.minDegree_le_degree i))
    ⟨w,maximum.trans maximal.le⟩

end DegreeTwo

namespace Theta

/-- Every family member has a positive linear lower bound at all sufficiently large host orders. -/
theorem theta_family_lower {k : ℕ} (lengths : Fin k → ℕ) (hk : 3 ≤ k) :
    HasLinearLower (rule lengths) := by
  obtain ⟨conn,cover,minimum,maximum⟩ := rule_class lengths hk
  exact DegreeTwo.linear_lower_of_extremes _ conn cover minimum.ge (hk.trans maximum.ge)

theorem theta_three_lower (a b c : ℕ) : HasLinearLower (rule (threeLengths a b c)) :=
  theta_family_lower _ (by decide)

end Theta
end Bootstrap

#print axioms Bootstrap.maxTime_subsingleton_rule
#print axioms Bootstrap.maxTime_empty_host
#print axioms Bootstrap.DegreeTwo.linear_lower_of_extremes
#print axioms Bootstrap.Theta.theta_family_lower
