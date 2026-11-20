import Bootstrap.Counterexample
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Ring

namespace Bootstrap.Preprint

open Localization MarkedSimulation

/-- Equation (5) as an exact identity over the natural numbers. -/
theorem family_order_time (k : ℕ) :
    familyOrder (k+1) = familyOrder k + 138720 ∧
      familyTime k = ((familyOrder k / 69360)^2 - 1)/8 := by
  constructor
  · unfold familyOrder; omega
  · have e : 2 * familyTime k = k*(k+1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd
    have poly : (2*k+1)^2 = 4*(k*(k+1)) + 1 := by ring
    have c : familyOrder k / 69360 = 2*k+1 := by unfold familyOrder; omega
    rw [c,poly,←e]
    omega

/-- Within each source block the first three core vertices span a triangle. -/
private theorem triangle_in_block (d : Block TypedRound.Role) :
    ∃ a b c : RuleVertex, owner a = d ∧ owner b = d ∧ owner c = d ∧
      ordinaryRule.Adj a b ∧ ordinaryRule.Adj a c ∧ ordinaryRule.Adj b c := by
  let a := hubIdx sourceCode d 0
  let b := hubIdx sourceCode d 1
  let c : Fin (blockSize sourceCode d) := ⟨2,blockSize_three _ _⟩
  refine ⟨.core d a,.core d b,.core d c,rfl,rfl,rfl,Or.inl (.book d a b ?_),
    Or.inl (.book d a c ?_),Or.inl (.book d b c ?_)⟩
  all_goals
    refine ⟨fun h => ?_,Or.inl ?_⟩
    · have h' := congrArg Fin.val h
      dsimp [a,b,c,hubIdx] at h'
      omega
    · dsimp [a,b,hubIdx]
      decide

/-- The final observation of Part III for the constructed rule, for every possible deleted edge. -/
theorem triangle_after_deleting (x y : RuleVertex) :
    let D := ordinaryRule.deleteEdges {s(x,y)}
    ∃ a b c : RuleVertex, D.Adj a b ∧ D.Adj a c ∧ D.Adj b c := by
  let r : TypedRound.Role := .inl (.endpoint false)
  have chooseBlock : ∃ d : Block TypedRound.Role, d ≠ owner x := by
    cases eq : owner x with
    | primary i => exact ⟨.secondary r,by simp⟩
    | secondary i => exact ⟨.primary r,by simp⟩
  obtain ⟨d,hd⟩ := chooseBlock
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := triangle_in_block d
  have keep {i j : RuleVertex} (hi : owner i = d) (hj : owner j = d) (adj : ordinaryRule.Adj i j) :
      (ordinaryRule.deleteEdges {s(x,y)}).Adj i j := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨adj,?_⟩
    intro eq
    have pair : s(i,j) = s(x,y) := eq
    rcases Sym2.eq_iff.mp pair with ⟨ix,_⟩ | ⟨_,jx⟩
    · exact hd (hi.symm.trans (congrArg owner ix))
    · exact hd (hj.symm.trans (congrArg owner jx))
  exact ⟨a,b,c,keep ha hb hab,keep ha hc hac,keep hb hc hbc⟩

end Bootstrap.Preprint

#print axioms Bootstrap.Preprint.family_order_time
#print axioms Bootstrap.Preprint.triangle_after_deleting
