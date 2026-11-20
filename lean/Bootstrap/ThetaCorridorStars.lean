import Bootstrap.ThetaCorridorExchange

namespace Bootstrap.Theta.Corridor

private def fromSlot (c : Bool) : ℕ := if c then 2 else 1
private def toSlot (c : Bool) : ℕ := if c then 2 else 0

/-- Every even interior depth lies in the transposition class of the left pole. -/
theorem even_depth_exchange (r : Fin 3 → ℕ) {d : ℕ} (hd : 3≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (col : c=true → ∀ i, r i%2=1) (inc : segmentGraph r d c ≤ F r d)
    (arm : Fin 3) (room : (if c then 3 else 2)≤r arm) :
    ∀ j, 0<j → j<d → j%2=0 → ∀ s : Slot r,
      Exchange (F r d) (pole (M r d) false) (inside r d c s j) := by
  let m := M r d
  let u := pole m false
  have ju : Junction r d false u := rfl
  have room' : span c d ≤ m arm+2 := by
    rw [actual_length r (by omega) pos]
    cases c <;> exact Nat.mul_le_mul_right d room
  have sFits : fromSlot c < r arm := by cases c <;> simp [fromSlot] at * <;> omega
  have tFits : toSlot c < r arm := by cases c <;> simp [toSlot] at * <;> omega
  let s : Slot r := ⟨arm,⟨fromSlot c,sFits⟩⟩
  let t : Slot r := ⟨arm,⟨toSlot c,tFits⟩⟩
  let p := twist m arm c d hd room'
  let atArm := point m arm
  have stable := twist_preserves r arm c d hd room' inc
  have start (j : ℕ) : atArm (fromSlot c*d+j)=inside r d c s j := by
    cases c <;> simp [atArm,m,inside,orient,s,fromSlot]
  have shift (j : ℕ) (hj : j≤d-3) :
      p (atArm (fromSlot c*d+j))=inside r d c t (j+2) := by
    have cap : fromSlot c*d+j ≤ m arm+2 := by
      cases c <;> simp [fromSlot,span] at room' ⊢ <;> omega
    rw [show p (atArm (fromSlot c*d+j)) = point m arm (twistIndex c d (fromSlot c*d+j)) by
      simpa using twist_point m arm c d hd room' arm (fromSlot c*d+j) cap]
    unfold inside
    apply congrArg (point m arm)
    cases c <;> simp [fromSlot,toSlot,t,orient,twistIndex] <;> split_ifs <;> omega
  obtain ⟨b,joint,tag⟩ := point_junction_tag r (show 2≤d by omega) pos c col arm (fromSlot c) sFits.le
  have initial : Exchange (F r d) u (atArm (fromSlot c*d)) := by
    apply junction_exchange r (by omega) pos c col inc ju joint
    intro ct
    subst c
    exact (tag rfl).symm
  have push (j : ℕ) (hj : j≤d-3) (old : Exchange (F r d) u (atArm (fromSlot c*d+j))) (a : Slot r) :
      Exchange (F r d) u (inside r d c a (j+2)) := by
    have new := Exchange.conjugate p stable old
    rw [show p u=u from rfl,shift j hj] at new
    exact transfer_depth r (by omega) pos c false col (by simp) inc ju t a (by omega) (by omega) new
  intro j
  induction j using Nat.strong_induction_on with
  | h j earlier =>
    intro lo hi even a
    by_cases two : j=2
    · subst j
      exact push 0 (by omega) (by simpa using initial) a
    · have smaller := earlier (j-2) (by omega) (by omega) (by omega) (by omega) s
      rw [←start] at smaller
      have next := push (j-2) (by omega) smaller a
      rwa [show j-2+2=j by omega] at next

/-- At even scale the two types of junctions join the same transposition class. -/
theorem colored_poles_exchange (r : Fin 3 → ℕ) {d : ℕ} (hd : 3≤d) (pos : ∀ i, 0<r i)
    (odd : ∀ i, r i%2=1) (inc : segmentGraph r d true ≤ F r d)
    (arm : Fin 3) (room : 3≤r arm) (even : d%2=0) :
    Exchange (F r d) (pole (M r d) false) (pole (M r d) true) := by
  let m := M r d
  have room' : span true d ≤ m arm+2 := by
    rw [actual_length r (by omega) pos]
    exact Nat.mul_le_mul_right d room
  let w := point m arm d
  have wTag : Junction r d true w := by
    have f := scaled_junction r (by omega : 0<d) arm 1 (by change 1*d ≤ m arm+2; change 3*d ≤ m arm+2 at room'; omega)
    simpa using f
  have right := junction_exchange r (by omega) pos true (fun _ => odd) inc
    (show Junction r d true (pole m true) from rfl) wTag (fun _ => rfl)
  let p := twist m arm true d hd room'
  let s : Slot r := ⟨arm,⟨1,by omega⟩⟩
  have cap : d ≤ m arm+2 := by change 3*d ≤ m arm+2 at room'; omega
  have whereW : p w=inside r d true s (d-2) := by
    rw [show p w=point m arm (twistIndex true d d) by simpa using twist_point m arm true d hd room' arm d cap]
    unfold inside
    apply congrArg (point m arm)
    simp [s,orient,twistIndex] <;> split_ifs <;> omega
  have moved := Exchange.conjugate p (twist_preserves r arm true d hd room' inc) right
  rw [show p (pole m true)=pole m true from rfl,whereW] at moved
  exact (even_depth_exchange r hd pos true (fun _ => odd) inc arm room (d-2) (by omega) (by omega)
    (by omega) s).trans moved.symm

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.even_depth_exchange
#print axioms Bootstrap.Theta.Corridor.colored_poles_exchange
