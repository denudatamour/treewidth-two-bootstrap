import Bootstrap.ThetaIntegerChart
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Ring.Int.Defs

namespace Bootstrap.Theta

open scoped Classical

theorem indexZ_zero_iff {n : ℕ} [NeZero n] (z : ℤ) : indexZ n z=0 ↔ (n:ℤ) ∣ z := by
  have pos : (0:ℤ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have per (q : ℤ) : indexZ n ((n:ℤ)*q)=0 := by
    unfold indexZ
    rw [Int.mul_comm,mul_zsmul]
    change q • indexZ n (n:ℤ)=0
    rw [indexZ_length,zsmul_zero]
  constructor
  · intro h
    let r := z%(n:ℤ)
    have bounds : 0 ≤ r ∧ r < n := ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ pos⟩
    have repr : z=r+(n:ℤ)*(z/n) := (Int.emod_add_ediv _ _).symm
    have loc : indexZ n r=0 := by
      calc
        indexZ n r = indexZ n (r+(n:ℤ)*(z/n)) := by rw [indexZ_add,per,add_zero]
        _ = 0 := repr ▸ h
    have cr : (r.toNat:ℤ)=r := Int.toNat_of_nonneg bounds.1
    have rn : r.toNat<n := by omega
    have v := congrArg Fin.val loc
    rw [←cr,indexZ_nat,Fin.val_natCast,Nat.mod_eq_of_lt rn,Fin.val_zero] at v
    refine ⟨z/n,?_⟩
    omega
  · rintro ⟨q,rfl⟩
    exact per q

theorem indexZ_eq_iff {n : ℕ} [NeZero n] (x y : ℤ) :
    indexZ n x=indexZ n y ↔ (n:ℤ) ∣ x-y := by
  rw [←indexZ_zero_iff]
  change x • (1 : Fin n) = y • 1 ↔ (x-y) • 1=0
  rw [sub_zsmul,←sub_eq_add_neg,sub_eq_zero]

theorem intPt_mod_iff (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) (x y : ℤ) :
    intPt m i j x=intPt m i j y ↔ (perimeter m i j:ℤ) ∣ x-y := by
  rw [←indexZ_eq_iff]
  constructor
  · intro eq
    simpa only [intPt,coord_pt m ij] using congrArg (vertexCoord m i j) eq
  · exact congrArg (cyclePt m i j)

theorem intPt_injective_interval (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j)
    {x y : ℕ} (hx : x<perimeter m i j) (hy : y<perimeter m i j)
    (eq : intPt m i j (x:ℤ)=intPt m i j (y:ℤ)) : x=y := by
  have h := congrArg (fun z => (vertexCoord m i j z).val) eq
  simpa only [intPt,coord_pt m ij,indexZ_nat,Fin.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using h

end Bootstrap.Theta

#print axioms Bootstrap.Theta.intPt_mod_iff
