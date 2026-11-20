import Bootstrap.ThetaCorridorSegments
import Bootstrap.TerminalExchange

namespace Bootstrap.Theta.Corridor

private theorem joint_unique {r : Fin 3 → ℕ} {d : ℕ} {a b : Bool} {x : V r d}
    (ja : Junction r d a x) (jb : Junction r d b x) : a=b := by
  rcases x with z|⟨i,j⟩
  · exact ja.trans jb.symm
  · exact ja.2.trans jb.2.symm

theorem junction_exchange (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (col : c=true → ∀ i, r i%2=1) (inc : segmentGraph r d c ≤ F r d)
    {x y : V r d} {a b : Bool} (jx : Junction r d a x) (jy : Junction r d b y)
    (allowed : c=true → a=b) : Exchange (F r d) x y := by
  apply segment_symmetry r hd pos c false col (by simp) (Equiv.swap x y) id _ _ inc
  · intro z k hk
    by_cases zx : z=x
    · subst z
      rw [Equiv.swap_apply_left]
      exact ⟨b,jy,fun h => (allowed h).symm.trans (joint_unique jx hk)⟩
    by_cases zy : z=y
    · subst z
      rw [Equiv.swap_apply_right]
      exact ⟨a,jx,fun h => (allowed h).trans (joint_unique jy hk)⟩
    · rw [Equiv.swap_apply_of_ne_of_ne zx zy]
      exact ⟨k,hk,fun _ => rfl⟩
  · intro s j lo hi
    let dep : Depth d := ⟨j,lo,hi⟩
    have away {v : V r d} {b : Bool} (h : Junction r d b v) : inside r d c s j ≠ v := by
      intro same
      exact inside_not_joint r hd pos c s dep b (same.symm ▸ h)
    rw [Equiv.swap_apply_of_ne_of_ne (away jx) (away jy)]
    rfl

private def depthAction (rev : Bool) (d : ℕ) : Equiv.Perm (Depth d) where
  toFun j := ⟨flipDepth rev d j,by cases rev <;> simp [flipDepth] <;> have := j.2 <;> omega⟩
  invFun j := ⟨flipDepth rev d j,by cases rev <;> simp [flipDepth] <;> have := j.2 <;> omega⟩
  left_inv j := Subtype.ext (by cases rev <;> simp [flipDepth] <;> have := j.2 <;> omega)
  right_inv j := Subtype.ext (by cases rev <;> simp [flipDepth] <;> have := j.2 <;> omega)

theorem transfer_depth (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c rev : Bool) (col : c=true → ∀ i, r i%2=1) (allowed : c=true → rev=false)
    (inc : segmentGraph r d c ≤ F r d) {u : V r d} {b : Bool} (ju : Junction r d b u)
    (s t : Slot r) {j : ℕ} (lo : 0<j) (hi : j<d)
    (old : Exchange (F r d) u (inside r d c s j)) :
    Exchange (F r d) u (inside r d c t (flipDepth rev d j)) := by
  let e := chart r hd pos c
  let move := Equiv.swap s t
  let onForms : Equiv.Perm (Forms r d) := Equiv.sumCongr (Equiv.refl _)
    (Equiv.prodCongr move (depthAction rev d))
  let p := (e.symm.trans onForms).trans e
  have carry (x : Forms r d) : p (e x)=e (onForms x) := by simp [p]
  have fixed {x : V r d} {i : Bool} (hx : Junction r d i x) : p x=x :=
    carry (.inl ⟨x,i,hx⟩)
  have internal (a : Slot r) (k : ℕ) (l : 0<k) (h : k<d) :
      p (inside r d c a k)=inside r d c (move a) (flipDepth rev d k) :=
    carry (.inr (a,⟨k,l,h⟩))
  have pres := segment_symmetry r hd pos c rev col allowed p move
    (fun x a h => ⟨a,(fixed h).symm ▸ h,fun _ => rfl⟩) internal inc
  have changed := Exchange.conjugate p pres old
  rw [fixed ju,internal s j lo hi,show move s=t from Equiv.swap_apply_left ..] at changed
  exact changed

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.junction_exchange
#print axioms Bootstrap.Theta.Corridor.transfer_depth
