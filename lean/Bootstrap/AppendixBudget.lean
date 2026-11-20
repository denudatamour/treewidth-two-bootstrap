import Bootstrap.SubdivisionLedger
import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Bootstrap.Subdivision

variable {C E V : Type*}

/-- The shortest paths give the radius bound with exactly the diameter used in Appendix A. -/
theorem radius_diam [Fintype C] (D : Data C E) (conn : D.baseGraph.Connected) (s : C) :
    RadiusAt D s D.baseGraph.diam := by
  letI : Nonempty C := conn.nonempty
  intro c
  obtain ⟨p,hp⟩ := conn.exists_walk_length_eq_dist s c
  exact ⟨p,hp.le.trans (SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp conn))⟩

/-- The individual fees of the displayed final budget, with a real merger trace.
Each element of the charged set records a distinct round with an actual low-degree birth. -/
theorem displayed_budget [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (conn : D.baseGraph.Connected) (G : SimpleGraph V) :
    ∃ (J : ℕ) (P : Finset ℕ),
      MergeTrace D G (Bootstrap.stabilizationTime D.rule G) D.baseGraph.diam 0 singletons J ∧
      J ≤ Fintype.card V - 1 ∧
      (∀ t, t ∈ P ↔ t < Bootstrap.stabilizationTime D.rule G ∧ LowAt D.rule G (threshold C E) t) ∧
      P.card ≤ (threshold C E-1)*Fintype.card V ∧
      Bootstrap.stabilizationTime D.rule G ≤
        (D.baseGraph.diam+1)*J+2*(J+1)+J+internalBudget C*J+3*P.card := by
  obtain ⟨J,P,trace,count,low,cap,tm⟩ := accounted_time D e₀ G _ (radius_diam D conn)
  refine ⟨J,P,trace,count,low,by simpa only [Nat.mul_comm (threshold C E-1)] using cap,?_⟩
  calc
    _ ≤ J*(D.baseGraph.diam+4+internalBudget C)+2+3*P.card := tm
    _ = _ := by simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one,
        Nat.mul_comm J D.baseGraph.diam,Nat.mul_comm J (internalBudget C)]; omega

end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.displayed_budget
