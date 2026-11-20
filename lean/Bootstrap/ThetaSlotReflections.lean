import Bootstrap.ThetaSignedClasses
import Bootstrap.ThetaCorridorChart
import Mathlib.Tactic.Ring

namespace Bootstrap.Theta.Corridor

open scoped Classical

theorem scaled_perimeter (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (i j : Fin 3) : perimeter (M r d) i j=(r i+r j)*d := by
  simp [perimeter,armSize,actual_length r hd pos,Nat.add_mul]

private theorem inside_first (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (i j : Fin 3) (k : Fin (r i)) {t : ℕ} (lo : 0<t) (hi : t<d) :
    intPt (M r d) i j ((k.val:ℤ)*d+t) = inside r d false ⟨i,k⟩ t := by
  have bounds := inside_bound r hd pos (s:=⟨i,k⟩) lo hi
  change _=armPt _ i (k.val*d+t)
  rw [←Int.natCast_mul,←Int.natCast_add,intPt_first _ _ _ _ bounds.2.le]

private theorem inside_second (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (i j : Fin 3) (k : Fin (r j)) {t : ℕ} (lo : 0<t) (hi : t<d) :
    intPt (M r d) i j (-((k.val:ℤ)*d+t)) = inside r d false ⟨j,k⟩ t := by
  have bounds := inside_bound r hd pos (s:=⟨j,k⟩) lo hi
  change _=armPt _ j (k.val*d+t)
  rw [←Int.natCast_mul,←Int.natCast_add,intPt_second _ _ _ _ bounds.2.le]

/-- Every signed segment coordinate on a two-arm cycle represents one physical
slot, with a fixed choice of orientation for all its interior points. -/
theorem cycle_slot (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    {i j : Fin 3} (ij : i≠j) (K : ℤ) :
    ∃ s : Slot r, ∃ rev : Bool, ∀ t : ℕ, 0<t → t<d →
      intPt (M r d) i j (K*(d:ℤ)+t) = inside r d false s (if rev then d-t else t) := by
  let n := r i+r j
  have np : 0<n := by dsimp [n];have := pos i;omega
  let k := (K%(n:ℤ)).toNat
  have ck : (k:ℤ)=K%(n:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have small : k<n := by have := Int.emod_lt_of_pos K (show (0:ℤ)<n by omega);omega
  have per := scaled_perimeter r hd pos i j
  change perimeter (M r d) i j=n*d at per
  have base : K-(k:ℤ)=(n:ℤ)*(K/(n:ℤ)) := by have := Int.emod_add_ediv K n;omega
  have reduce (t : ℕ) : intPt (M r d) i j (K*(d:ℤ)+t)=intPt (M r d) i j ((k:ℤ)*d+t) := by
    apply (intPt_mod_iff _ ij _ _).mpr
    refine ⟨K/(n:ℤ),?_⟩
    rw [per,Nat.cast_mul]
    calc
      _ = (K-(k:ℤ))*(d:ℤ) := by ring
      _ = _ := by rw [base];ring
  by_cases left : k<r i
  · refine ⟨⟨i,⟨k,left⟩⟩,false,fun t lo hi => (reduce t).trans ?_⟩
    exact inside_first r hd pos i j ⟨k,left⟩ lo hi
  let b := n-k-1
  have bs : b<r j := by dsimp [n,b] at *;omega
  have add : (k:ℤ)+b+1=n := by dsimp [b];omega
  refine ⟨⟨j,⟨b,bs⟩⟩,true,fun t lo hi => (reduce t).trans ?_⟩
  have flipped := inside_second r hd pos i j ⟨b,bs⟩ (t:=d-t) (by omega) (by omega)
  refine Eq.trans ?_ flipped
  apply (intPt_mod_iff _ ij _ _).mpr
  refine ⟨1,?_⟩
  change (k:ℤ)*d+t-(-((b:ℤ)*d+↑(d-t)))=↑(perimeter (M r d) i j)*1
  rw [Nat.cast_sub hi.le,per,Nat.cast_mul,←add];ring

def tipDepth (d : ℕ) (side : Bool) := if side then d-1 else 1
def tip (r : Fin 3 → ℕ) (d : ℕ) (s : Slot r) (side : Bool) :=
  inside r d false s (tipDepth d side)
def tipFlip (rev side : Bool) := if rev then !side else side

theorem flip_tip (d : ℕ) (hd : 2≤d) (b : Bool) : d-tipDepth d b=tipDepth d (!b) := by
  cases b <;> simp [tipDepth] <;> omega

private theorem tip_bounds (d : ℕ) (hd : 2≤d) (b : Bool) : 0<tipDepth d b ∧ tipDepth d b<d := by
  cases b <;> simp [tipDepth] <;> omega

theorem tips_determine_slot (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    {s t : Slot r} {a b : Bool} (eq : tip r d s a=tip r d t b) : s=t := by
  let l (c : Bool) : Depth d := ⟨tipDepth d c,tip_bounds d hd c⟩
  have e : chart r hd pos false (.inr (s,l a))=chart r hd pos false (.inr (t,l b)) := eq
  exact congrArg Prod.fst (Sum.inr.inj ((chart r hd pos false).injective e))

private theorem reflect_as (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    {i j : Fin 3} (ij : i≠j) (b : Bool) (z : ℤ) :
    reflection (M r d) ij b (intPt (M r d) i j z) =
      intPt (M r d) i j ((if b then 2*(r i:ℤ) else 0)*d-z) := by
  cases b
  · simpa using false_reflect_int (M r d) ij z
  · rw [true_reflect_int];congr 1
    change -z+2*(↑(M r d i+2):ℤ)=_ 
    rw [actual_length r hd pos,Nat.cast_mul];simp;ring

theorem reflection_sends_slot (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    {i j : Fin 3} (ij : i≠j) (b : Bool) (s : Slot r) :
    ∃ t : Slot r, ∃ rev : Bool, ∀ a,
      reflection (M r d) ij b (tip r d s a)=tip r d t (tipFlip rev a) := by
  obtain ⟨l,k⟩ := s
  let C : ℤ := if b then 2*(r i:ℤ) else 0
  by_cases atI : l=i
  · subst l
    obtain ⟨s,rev,changeDepth⟩ := cycle_slot r hd pos ij (C-(k.val:ℤ)-1)
    refine ⟨s,!rev,?_⟩
    intro a
    obtain ⟨lo,hi⟩ := tip_bounds d hd a
    rw [tip,←inside_first r hd pos i j k lo hi,reflect_as r hd pos ij]
    have e : C*(d:ℤ)-((k.val:ℤ)*d+tipDepth d a)=(C-(k.val:ℤ)-1)*d+(↑(d-tipDepth d a):ℤ) := by
      rw [Nat.cast_sub hi.le];ring
    rw [e,changeDepth _ (by omega) (by omega),flip_tip d hd a]
    cases rev <;> cases a <;> simp [tip,tipFlip,tipDepth] <;> congr 1 <;> omega
  by_cases atJ : l=j
  · subst l
    obtain ⟨s,rev,changeDepth⟩ := cycle_slot r hd pos ij (C+(k.val:ℤ))
    refine ⟨s,rev,?_⟩
    intro a
    obtain ⟨lo,hi⟩ := tip_bounds d hd a
    rw [tip,←inside_second r hd pos i j k lo hi,reflect_as r hd pos ij]
    have e : C*(d:ℤ)-(-((k.val:ℤ)*d+tipDepth d a))=(C+(k.val:ℤ))*d+tipDepth d a := by ring
    rw [e,changeDepth _ lo hi]
    cases rev <;> cases a <;> simp [tip,tipFlip,tipDepth] <;> congr 1 <;> omega
  refine ⟨⟨l,k⟩,false,?_⟩
  intro a
  apply reflection_off
  have ⟨lo,hi⟩ := tip_bounds d hd a
  have bounds := inside_bound r hd pos (s:=⟨l,k⟩) lo hi
  change ¬OnCycle i j (point (M r d) l (k.val*d+tipDepth d a))
  rw [point_interior _ bounds.1 bounds.2]
  exact fun h => h.elim atI atJ

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.cycle_slot
#print axioms Bootstrap.Theta.Corridor.reflection_sends_slot
