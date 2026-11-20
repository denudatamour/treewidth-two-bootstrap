import Bootstrap.DegreeTwoBoundary
import Bootstrap.ShortRule
import Bootstrap.LongRouteLinear

/-! The upper and matching lower clauses of Theorem II.1, and their
application to every fixed multiple-arm rule in Theorem I.1. -/
namespace Bootstrap

variable {W : Type*}

namespace DegreeTwo

/-- Covers all finite connected simple rules in which every edge meets a
degree-two vertex. In fact, the upper bound holds at every host order. -/
theorem linear_all_orders [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2) :
    ∃ K : ℕ, ∀ n, maxTime H n ≤ K*n := by
  classical
  by_cases long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2
  · exact long_rule_linear H conn cover long
  · exact Subdivision.short_rule_linear H conn cover long

/-- Theorem II.1 with its published degree hypotheses and ordinary maximum
stabilization time on every sufficiently large host order. -/
theorem theorem_II_1 [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2) :
    HasLinearUpper H ∧ (2 ≤ H.minDegree → 3 ≤ H.maxDegree → HasLinearOrder H) := by
  obtain ⟨K,bound⟩ := linear_all_orders H conn cover
  have upper : HasLinearUpper H := ⟨K,0,fun n _ => bound n⟩
  exact ⟨upper,fun minimum maximum => ⟨linear_lower_of_extremes H conn cover minimum maximum,upper⟩⟩

end DegreeTwo

namespace Theta

/-- Multiple-arm corollary, including an equality certifying that the
concrete simple graph represents the prescribed arm lengths. -/
theorem theta_family_order {k : ℕ} (lengths : Fin k → ℕ) (hk : 3 ≤ k)
    (hl : ∀ i, 2 ≤ lengths i) :
    (∀ i, lengths i - 2 + 2 = lengths i) ∧ HasLinearOrder (rule lengths) := by
  obtain ⟨conn,cover,minimum,maximum⟩ := rule_class lengths hk
  exact ⟨arm_length lengths hl,(DegreeTwo.theorem_II_1 _ conn cover).2 minimum.ge
    (hk.trans maximum.ge)⟩

/-- Theorem I.1 for three prescribed path lengths at least two. -/
theorem theorem_I_1 (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    HasLinearOrder (rule (threeLengths a b c)) := by
  apply (theta_family_order (threeLengths a b c) (by decide) ?_).2
  intro i
  unfold threeLengths
  split
  · exact ha
  · split
    · exact hb
    · exact hc

end Theta
end Bootstrap

#print axioms Bootstrap.DegreeTwo.linear_all_orders
#print axioms Bootstrap.DegreeTwo.theorem_II_1
#print axioms Bootstrap.Theta.theta_family_order
#print axioms Bootstrap.Theta.theorem_I_1
