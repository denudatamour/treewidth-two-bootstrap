import Bootstrap.ThetaIntegerChart
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Ring.Int.Defs

namespace Bootstrap.Theta

open scoped Classical

def graphSymmetries {V : Type*} (G : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {p | ∀ x y, G.Adj (p x) (p y) ↔ G.Adj x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun hp hq x y => (hp _ _).trans (hq x y)
  inv_mem' := by
    intro p hp x y
    simpa only [Equiv.Perm.inv_apply_self,Equiv.Perm.apply_inv_self] using (hp (p⁻¹ x) (p⁻¹ y)).symm

def reflectionGroup (m : Fin 3 → ℕ) : Subgroup (Equiv.Perm (Vertex m)) :=
  Subgroup.closure {p | ∃ (i j : Fin 3) (ij : i≠j) (b : Bool), p=reflection m ij b}

theorem reflection_mem (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) (b : Bool) :
    reflection m ij b ∈ reflectionGroup m := Subgroup.subset_closure ⟨i,j,ij,b,rfl⟩

theorem reflectionGroup_terminal (m : Fin 3 → ℕ) :
    reflectionGroup m ≤ graphSymmetries (terminalGraph (graph m) (graph m)) := by
  apply (Subgroup.closure_le _).mpr
  rintro p ⟨i,j,ij,b,rfl⟩
  have other : ∀ i j : Fin 3, i≠j → ∃ t : Fin 3, i≠t ∧ j≠t := by decide
  obtain ⟨t,it,jt⟩ := other i j ij
  exact reflection_terminal m ij t (third_of_ne ij it jt) b

def translations (m : Fin 3 → ℕ) (i j : Fin 3) : AddSubgroup ℤ where
  carrier := {v | ∃ p : Equiv.Perm (Vertex m), p ∈ reflectionGroup m ∧
    (∀ z : ℤ,p (intPt m i j z)=intPt m i j (z+v)) ∧ ∀ w, ¬OnCycle i j w → p w=w}
  zero_mem' := ⟨1,(reflectionGroup m).one_mem,fun _ => by simp,fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨p,hp,actP,fixP⟩ ⟨q,hq,actQ,fixQ⟩
    refine ⟨q*p,(reflectionGroup m).mul_mem hq hp,?_,?_⟩
    · intro z; rw [Equiv.Perm.mul_apply,actP,actQ,add_assoc]
    · intro w hw; rw [Equiv.Perm.mul_apply,fixP w hw,fixQ w hw]
  neg_mem' := by
    rintro a ⟨p,hp,act,fix⟩
    refine ⟨p⁻¹,(reflectionGroup m).inv_mem hp,?_,?_⟩
    · intro z
      apply p.injective
      rw [Equiv.Perm.apply_inv_self,act]
      simp
    · intro w hw
      apply p.injective
      rw [Equiv.Perm.apply_inv_self,fix w hw]

theorem rotation_mem (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) :
    (2*(armSize m i:ℤ)) ∈ translations m i j := by
  refine ⟨reflection m ij true * reflection m ij false,
    (reflectionGroup m).mul_mem (reflection_mem m ij true) (reflection_mem m ij false),rotate_int m ij,?_⟩
  intro w hw
  rw [Equiv.Perm.mul_apply,reflection_off m ij false hw,reflection_off m ij true hw]

theorem period_mem (m : Fin 3 → ℕ) (i j : Fin 3) :
    (perimeter m i j:ℤ) ∈ translations m i j :=
  ⟨1,(reflectionGroup m).one_mem,fun z => (intPt_period m i j z).symm,fun _ _ => rfl⟩

theorem gcd_rotation (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) :
    ((2*armSize m i).gcd (perimeter m i j) : ℤ) ∈ translations m i j := by
  let a := 2*armSize m i
  let n := perimeter m i j
  let D := translations m i j
  have ha : (a:ℤ) ∈ D := by simpa only [a,Int.ofNat_mul,Int.ofNat_eq_coe] using rotation_mem m ij
  have hn : (n:ℤ) ∈ D := period_mem m i j
  have ah := D.zsmul_mem ha (a.gcdA n)
  have nh := D.zsmul_mem hn (a.gcdB n)
  have both := D.add_mem ah nh
  change (a.gcd n : ℤ) ∈ D
  rw [Nat.gcd_eq_gcd_ab]
  change (a.gcdA n)*(a:ℤ)+(a.gcdB n)*(n:ℤ) ∈ D at both
  simpa only [Int.mul_comm (Nat.gcdA a n),Int.mul_comm (Nat.gcdB a n)] using both

theorem translation_of_dvd (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) {t : ℤ}
    (div : ((2*armSize m i).gcd (perimeter m i j) : ℤ) ∣ t) :
    ∃ p : Equiv.Perm (Vertex m), p∈reflectionGroup m ∧
      (∀ z : ℤ,p (intPt m i j z)=intPt m i j (z+t)) ∧ ∀ w, ¬OnCycle i j w → p w=w := by
  obtain ⟨q,rfl⟩ := div
  have h := (translations m i j).zsmul_mem (gcd_rotation m ij) q
  change q * _ ∈ translations m i j at h
  rw [Int.mul_comm q] at h
  exact h

end Bootstrap.Theta

#print axioms Bootstrap.Theta.gcd_rotation
#print axioms Bootstrap.Theta.reflectionGroup_terminal
