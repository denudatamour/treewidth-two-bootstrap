import Bootstrap.NonbipLinear

/-! The parity double cover bounds the odd closed walk by twice the rule order minus one. -/
namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

private def parityCover (H : SimpleGraph W) : SimpleGraph (W × Bool) where
  Adj x y := H.Adj x.1 y.1 ∧ x.2 ≠ y.2
  symm := fun _ _ e => ⟨H.symm e.1,e.2.symm⟩
  loopless := fun _ e => e.2 rfl

private def projectCover (H : SimpleGraph W) : parityCover H →g H where
  toFun := Prod.fst
  map_rel' := fun e => e.1

private def parityEnd (n : ℕ) (c : Bool) := if n%2=0 then c else !c

private theorem parity_succ (n : ℕ) (c : Bool) : parityEnd n (!c) = parityEnd (n+1) c := by
  by_cases even : n%2=0
  · have odd : (n+1)%2 ≠ 0 := by omega
    simp [parityEnd,even,odd]
  · have odd : (n+1)%2 = 0 := by omega
    simp [parityEnd,even,odd]

private theorem lifts (H : SimpleGraph W) {x y : W} (p : H.Walk x y) (c : Bool) :
    (parityCover H).Reachable (x,c) (y,parityEnd p.length c) := by
  induction p generalizing c with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z e tail ih =>
    have step' : (parityCover H).Adj (x,c) (y,!c) := ⟨e,by change c ≠ !c; cases c <;> decide⟩
    have path := step'.reachable.trans (ih (!c))
    simpa only [SimpleGraph.Walk.length_cons,←parity_succ] using path

private theorem end_color (H : SimpleGraph W) {x y : W × Bool} (p : (parityCover H).Walk x y) :
    y.2 = parityEnd p.length x.2 := by
  induction p with
  | nil => rfl
  | @cons x y z e tail ih =>
    have h : y.2 = !x.2 := by
      obtain ⟨_,ne⟩ := e
      cases a : x.2 <;> cases b : y.2 <;> simp_all
    rw [SimpleGraph.Walk.length_cons,←parity_succ,←h]
    exact ih

theorem odd_walk_length_bound [Fintype W] (H : SimpleGraph W) (conn : H.Connected)
    (nb : ¬ProperBoolColor H) (v : W) :
    ∃ walk : H.Walk v v, walk.length%2=1 ∧ walk.length ≤ 2*Fintype.card W-1 := by
  classical
  obtain ⟨_,odd⟩ := bounded_odd_walks H conn nb
  obtain ⟨walk,ho,_⟩ := odd v
  have reach : (parityCover H).Reachable (v,false) (v,true) := by simpa [parityEnd,ho] using lifts H walk false
  obtain ⟨path,short⟩ := reach.exists_isPath
  have end' := end_color H path
  have par : path.length % 2 = 1 := by
    by_contra! no
    have e : path.length % 2=0 := by omega
    simp [parityEnd,e] at end'
  have size := short.length_lt
  simp only [Fintype.card_prod,Fintype.card_bool] at size
  refine ⟨path.map (projectCover H),?_,?_⟩ <;> rw [SimpleGraph.Walk.length_map]
  · exact par
  · omega

theorem nonbip_clock_explicit [Fintype W] [Fintype V] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i=2 ∨ H.degree j=2)
    (long : ∃ i j,H.Adj i j ∧ H.degree i=2 ∧ H.degree j=2) (nb : ¬ProperBoolColor H) :
    stabilizationTime H G ≤ ((3*Fintype.card W-1)+(2*Fintype.card W+2*(2*Fintype.card W-1)+11)+2)*Fintype.card V := by
  classical
  obtain ⟨i,j,_,d,_⟩ := id long
  obtain ⟨l,r,N⟩ := (hasTwo_iff_degree H i).mpr d
  exact clique_clock H G N _ _ (high_nonbip H G conn root cover long _ (odd_walk_length_bound H conn nb))

/-- All distinct neighbours whose edge is born while x is still below J in
the completed round. This includes every edge that can be charged to x. -/
noncomputable def paidNeighbours [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (x : V) (J t : ℕ) : Finset V :=
  Finset.univ.filter fun y => ∃ k < t, ¬(run H G k).Adj x y ∧
    (run H G (k+1)).Adj x y ∧ (run H G (k+1)).degree x < J

theorem paidNeighbours_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (x : V) (J t : ℕ) : (paidNeighbours H G x J t).card ≤ J-1 := by
  classical
  induction t with
  | zero => simp [paidNeighbours]
  | succ t ih =>
    by_cases high : J ≤ (run H G (t+1)).degree x
    · apply le_trans (Finset.card_le_card _) ih
      intro y hy
      obtain ⟨k,ht,old,born,small⟩ := (Finset.mem_filter.mp hy).2
      have before : k<t := by
        by_contra! after
        have eq : k=t := by omega
        subst k
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,before,old,born,small⟩
    · have sub : paidNeighbours H G x J (t+1) ⊆ (run H G (t+1)).neighborFinset x := by
        intro y hy
        obtain ⟨k,ht,_,born,_⟩ := (Finset.mem_filter.mp hy).2
        exact ((run H G (t+1)).mem_neighborFinset x y).mpr (time_mono H G (by omega : k+1 ≤ t+1) born)
      have bound : (paidNeighbours H G x J (t+1)).card ≤ (run H G (t+1)).degree x := Finset.card_le_card sub
      omega

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.paidNeighbours_bound
#print axioms Bootstrap.DegreeTwo.odd_walk_length_bound
#print axioms Bootstrap.DegreeTwo.nonbip_clock_explicit
