import Bootstrap.Asymptotics
import Bootstrap.RuleStructure
import Bootstrap.MarkedSimulation

/-! Unconditional ordinary running-time conclusions for the single rule in the preprint. -/
namespace Bootstrap

open MarkedSimulation RuleStructure

theorem hasTwoNeighbours_of_minDegree [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h : 2 ≤ H.minDegree) : HasTwoNeighbours H := by
  intro w
  have hd : 1 < (H.neighborFinset w).card := h.trans (H.minDegree_le_degree w)
  obtain ⟨i,hi,j,hj,hne⟩ := Finset.one_lt_card.mp hd
  exact ⟨i,j,hne,(SimpleGraph.mem_neighborFinset H w i).mp hi,
    (SimpleGraph.mem_neighborFinset H w j).mp hj⟩

theorem ordinary_time {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    stabilizationTime ordinaryRule (initial p q) = p.lcm q / 2 :=
  stabilizationTime_eq_of_first _ _ _ (ordinary_fixed_iff hp hq)

theorem ordinary_family (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : SimpleGraph (Fin (familyOrder k)), familyTime k = stabilizationTime ordinaryRule G := by
  classical
  let V := OrdinaryVertex (Fin k) (Fin (k+1))
  have card : Fintype.card V = familyOrder k := by
    rw [host_order]; unfold familyOrder; omega
  let e : V ≃ Fin (familyOrder k) := Fintype.equivFinOfCardEq card
  let G := initial k (k+1)
  let G' := G.comap e.symm
  have h := stabilizationTime_relabel ordinaryRule G G' e (by
    intro x y
    change G.Adj (e.symm (e x)) (e.symm (e y)) ↔ G.Adj x y
    simp)
  exact ⟨G', (consecutive_period k).symm.trans
    ((ordinary_time hk (show 3 ≤ k+1 by omega)).symm.trans h)⟩

theorem ordinary_quadratic : HasQuadraticOrder ordinaryRule := by
  classical
  apply quadratic_of_family ordinaryRule (hasTwoNeighbours_of_minDegree ordinaryRule source_minDegree.ge)
  intro k hk
  obtain ⟨G,h⟩ := ordinary_family k hk
  exact ⟨G,h.le⟩

theorem ordinary_not_linear : ¬ HasLinearUpper ordinaryRule :=
  quadratic_excludes_linear ordinaryRule ordinary_quadratic

end Bootstrap

#print axioms Bootstrap.ordinary_time
#print axioms Bootstrap.ordinary_family
#print axioms Bootstrap.ordinary_quadratic
#print axioms Bootstrap.ordinary_not_linear
