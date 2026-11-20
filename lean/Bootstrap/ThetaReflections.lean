import Bootstrap.ThetaCycleChart
import Bootstrap.TerminalSymmetry

namespace Bootstrap.Theta

open scoped Classical
variable {k : ℕ}

def reflected {n : ℕ} (c x : Fin n) : Fin n := c+c-x

private theorem reflect_twice {n : ℕ} [NeZero n] (c x : Fin n) : reflected c (reflected c x)=x := sub_sub_cancel _ _

noncomputable def cyclePerm (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j)
    (T : Equiv.Perm (Fin (perimeter m i j))) : Equiv.Perm (Vertex m) := by
  let lift (p : Equiv.Perm (Fin (perimeter m i j))) := cycleMap m i j p
  have cancel (p q : Equiv.Perm (Fin (perimeter m i j))) (inv : ∀v,p (q v)=v) (x : Vertex m) :
      lift p (lift q x) = x := by
    by_cases on' : OnCycle i j x
    · have rep := pt_coord m ij x on'
      conv_lhs => rw [←rep]
      rw [show lift q (cyclePt m i j _) = _ from cycleMap_pt m ij q _,show lift p (cyclePt m i j _) = _ from cycleMap_pt m ij p _,inv,rep]
    · change cycleMap m i j p (cycleMap m i j q x)=x
      rw [cycleMap_off m i j q on',cycleMap_off m i j p on']
  exact ⟨lift T,lift T.symm,cancel _ _ T.left_inv,cancel _ _ T.right_inv⟩

noncomputable def reflection (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (b : Bool) :
    Equiv.Perm (Vertex m) := cyclePerm m ij
      (Function.Involutive.toPerm _ (reflect_twice (vertexCoord m i j (pole m b))))

theorem reflection_pt (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (b : Bool) (z : Fin (perimeter m i j)) :
    reflection m ij b (cyclePt m i j z) =
      cyclePt m i j (reflected (vertexCoord m i j (pole m b)) z) := cycleMap_pt m ij _ z

theorem reflection_off (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (b : Bool)
    {x : Vertex m} (off : ¬OnCycle i j x) : reflection m ij b x=x := cycleMap_off m i j _ off

theorem reflection_fixes_pole (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (b : Bool) :
    reflection m ij b (pole m b) = pole m b := by
  have on' : OnCycle i j (pole m b) := trivial
  have rep := pt_coord m ij (pole m b) on'
  conv_lhs => rw [←rep]
  rw [reflection_pt,reflected,add_sub_cancel_right,rep]

theorem rotation_pt (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (z : Fin (perimeter m i j)) :
    (reflection m ij true * reflection m ij false) (cyclePt m i j z) =
      cyclePt m i j (z+vertexCoord m i j (pole m true)+vertexCoord m i j (pole m true)) := by
  rw [Equiv.Perm.mul_apply,reflection_pt,reflection_pt]
  apply congrArg (cyclePt m i j)
  change _ + _ - (0+0-z) = _
  simp only [zero_add,zero_sub,sub_neg_eq_add]; ac_rfl

private theorem reflect_consecutive (m : Fin k → ℕ) (i j : Fin k) (c : Fin (perimeter m i j))
    {x y : Fin (perimeter m i j)} (edge : consecutive m i j x y) :
    consecutive m i j (reflected c x) (reflected c y) := by
  rcases edge with h|h
  · right; rw [←h]; unfold reflected; rw [sub_add_eq_sub_sub,sub_add_cancel]
  · left; rw [←h]; unfold reflected; rw [sub_add_eq_sub_sub,sub_add_cancel]

def armEnd (m : Fin k → ℕ) (i : Fin k) : Bool → Vertex m
  | false => inner m i 0
  | true => inner m i (Fin.last (m i))

theorem pole_arm_end (m : Fin k → ℕ) (i : Fin k) (b : Bool) : (graph m).Adj (pole m b) (armEnd m i b) := by
  cases b <;> rfl

private theorem crossings (m : Fin k → ℕ) (i j t : Fin k)
    (third : ∀ a, a≠i → a≠j → a=t) {x y : Vertex m}
    (on' : OnCycle i j x) (off : ¬OnCycle i j y) (edge : (graph m).Adj x y) :
    ∃ b, x=pole m b ∧ y=armEnd m t b := by
  rcases y with b|⟨a,d⟩
  · exact False.elim (off trivial)
  have at' := third a (fun h => off (Or.inl h)) (fun h => off (Or.inr h))
  subst a
  rcases x with b|⟨s,z⟩
  · refine ⟨b,rfl,?_⟩
    cases b <;> apply congrArg (inner m t) <;> apply Fin.ext <;> exact edge
  · have e : s=t := edge.1
    subst s
    exact False.elim (off on')

/-- Any cycle reflection about a pole changes at most the one old edge at
the other end of the third arm, so it preserves the final self-closure. -/
theorem reflection_terminal (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (t : Fin k)
    (third : ∀ a, a≠i → a≠j → a=t) (b : Bool) :
    ∀ x y, (terminalGraph (graph m) (graph m)).Adj (reflection m ij b x) (reflection m ij b y) ↔
      (terminalGraph (graph m) (graph m)).Adj x y := by
  classical
  let u := pole m (!b)
  let v := armEnd m t (!b)
  apply self_near_perm _ _ (pole_arm_end m t (!b))
  have mix {x y : Vertex m} (on' : OnCycle i j x) (off : ¬OnCycle i j y) (e : (graph m).Adj x y)
      (avoid : ¬(x=u ∧ y=v)) : (graph m).Adj (reflection m ij b x) (reflection m ij b y) := by
    obtain ⟨q,rfl,hy⟩ := crossings m i j t third on' off e
    have same : q=b := by
      by_contra ne
      have alt : q= !b := by cases b <;> cases q <;> simp_all
      exact avoid ⟨congrArg (pole m) alt,hy.trans (congrArg (armEnd m t) alt)⟩
    subst q
    rwa [reflection_fixes_pole,reflection_off m ij b off]
  intro x y edge avoid
  by_cases xc : OnCycle i j x <;> by_cases yc : OnCycle i j y
  · have h := reflect_consecutive m i j (vertexCoord m i j (pole m b)) (consecutive_of_adj m ij xc yc edge)
    have repx := pt_coord m ij x xc
    have repy := pt_coord m ij y yc
    have up := adj_of_consecutive m i j _ _ h
    change (graph m).Adj (cycleMap m i j _ x) (cycleMap m i j _ y)
    rw [cycleMap,if_pos xc,cycleMap,if_pos yc]
    exact up
  · exact mix xc yc edge (fun h => avoid (Or.inl h))
  · exact (graph m).symm (mix yc xc ((graph m).symm edge) (fun h => avoid (Or.inr h.symm)))
  · rwa [reflection_off m ij b xc,reflection_off m ij b yc]

end Bootstrap.Theta

#print axioms Bootstrap.Theta.rotation_pt
#print axioms Bootstrap.Theta.reflection_terminal
