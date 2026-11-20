import Bootstrap.ThetaSignedClasses
import Bootstrap.ThetaCorridorChart
import Bootstrap.PrimitiveOrbitReduction

namespace Bootstrap.Theta.Corridor

def reducedMod (r : Fin 3 → ℕ) := (2*r 0).gcd ((r 0+r 1).gcd (r 0+r 2))

theorem scale_modulus (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i) :
    orbitMod (M r d)=reducedMod r*d := by
  simp only [orbitMod,perimeter,armSize,actual_length r hd pos,←Nat.add_mul,←Nat.mul_assoc,Nat.gcd_mul_right,reducedMod]

theorem mixed_modulus (r : Fin 3 → ℕ) (prim : (r 0).gcd ((r 1).gcd (r 2))=1)
    (pos : ∀i,0<r i) (mix : ∃i j,r i%2≠r j%2) : reducedMod r=1 := by
  by_cases h : r 0%2≠r 2%2
  · exact Contraction.primitive_mixed_modulus _ _ _ (pos _) prim h
  have opp : r 0%2≠r 1%2 := by
    intro e
    obtain ⟨i,j,ne⟩ := mix
    have all (v : Fin 3) : r v%2=r 0%2 := by
      by_cases a : v=0
      · rw [a]
      by_cases b : v=1
      · rw [b,e]
      have eq := third_of_ne (show (0:Fin 3)≠1 by decide) (show (0:Fin 3)≠2 by decide) (by decide) v a b
      rw [eq];omega
    exact ne ((all i).trans (all j).symm)
  have p : (r 0).gcd ((r 2).gcd (r 1))=1 := by rwa [Nat.gcd_comm (r 2)]
  simpa only [reducedMod,Nat.gcd_comm (r 0+r 2)] using Contraction.primitive_mixed_modulus _ _ _ (pos _) p opp

theorem odd_modulus (r : Fin 3 → ℕ) (prim : (r 0).gcd ((r 1).gcd (r 2))=1)
    (odd : ∀i,r i%2=1) : reducedMod r=2 := by
  apply Nat.dvd_antisymm (Contraction.primitive_modulus_dvd_two _ _ _ prim)
  apply Nat.dvd_gcd (dvd_mul_right _ _)
  exact Nat.dvd_gcd (by have := odd 0;have := odd 1;omega) (by have := odd 0;have := odd 2;omega)

theorem signed_zero_nat (n z : ℕ) : SignedClass n z 0 ↔ z%n=0 := by
  simp only [SignedClass,neg_zero,or_self,Int.modEq_zero_iff_dvd,Int.natCast_dvd_natCast,Nat.dvd_iff_mod_eq_zero]

theorem signed_positive_nat (n z t : ℕ) (ht : 0<t) (small : t<n) :
    SignedClass n z t ↔ z%n=t ∨ z%n=n-t := by
  have neg : (-(t:ℤ)) ≡ (↑(n-t):ℤ) [ZMOD (n:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [Nat.cast_sub small.le]
    exact ⟨1,by omega⟩
  have alter : (z:ℤ) ≡ -(t:ℤ) [ZMOD (n:ℤ)] ↔ (z:ℤ) ≡ (↑(n-t):ℤ) [ZMOD (n:ℤ)] :=
    ⟨fun h => h.trans neg,fun h => h.trans neg.symm⟩
  unfold SignedClass
  rw [alter,Int.natCast_modEq_iff,Int.natCast_modEq_iff]
  dsimp only [Nat.ModEq]
  rw [Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (show n-t<n by omega)]

def jointResidue (d : ℕ) (b : Bool) : ℕ := if b then d else 0
def portResidue (d : ℕ) (b : Bool) : ℕ := if b then d-1 else 1

private theorem raw_joint (d z : ℕ) (hd : 2≤d) (b : Bool) :
    (z%d=0 ∧ b=decide (z/d%2=1)) ↔ SignedClass (↑(2*d)) z (jointResidue d b) := by
  have form : z%(2*d) = z%d+d*(z/d%2) := by rw [Nat.mul_comm 2 d,Nat.mod_mul]
  have bound := Nat.mod_lt z (by omega : 0<d)
  have jd := signed_positive_nat (2*d) z d (by omega) (by omega)
  have jz := signed_zero_nat (2*d) z
  rcases Nat.mod_two_eq_zero_or_one (z/d) with c|c <;>
    cases b <;> simp only [jointResidue,Bool.false_eq_true,if_false,if_true,Nat.cast_zero,c,
      Nat.mul_zero,Nat.mul_one,Nat.add_zero] at form ⊢ <;> first
      | (rw [jz];simp <;> omega)
      | (rw [jd];simp <;> omega)

private theorem raw_port (d z : ℕ) (hd : 2≤d) (b : Bool) :
    ((z%d=1 ∧ b=decide (z/d%2=1)) ∨ (z%d+1=d ∧ b= !(decide (z/d%2=1)))) ↔
      SignedClass (↑(2*d)) z (portResidue d b) := by
  have form : z%(2*d) = z%d+d*(z/d%2) := by rw [Nat.mul_comm 2 d,Nat.mod_mul]
  have bound := Nat.mod_lt z (by omega : 0<d)
  have pi := signed_positive_nat (2*d) z 1 (by decide) (by omega)
  have pj := signed_positive_nat (2*d) z (d-1) (by omega) (by omega)
  rcases Nat.mod_two_eq_zero_or_one (z/d) with c|c <;>
    cases b <;> simp only [portResidue,Bool.false_eq_true,if_false,if_true,c,
      Nat.mul_zero,Nat.mul_one,Nat.add_zero] at form ⊢ <;> first
      | (rw [pi];simp <;> omega)
      | (rw [pj];simp <;> omega)

theorem junction_class (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (odd : ∀i,r i%2=1) (mod : orbitMod (M r d)=2*d) (b : Bool) (x : V r d) :
    Junction r d b x ↔ depthClass (M r d) (jointResidue d b) x := by
  unfold depthClass
  rw [mod,←raw_joint d _ hd b]
  rcases x with t|⟨i,j⟩
  · cases t
    · simp [Junction,naturalDepth]
    · simp [Junction,naturalDepth,armSize,actual_length r hd pos,Nat.mul_div_cancel _ (by omega : 0<d),odd 0]
  · rfl

theorem port_class (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (mod : orbitMod (M r d)=2*d) (b : Bool) (x : V r d) :
    Port r d b x ↔ depthClass (M r d) (portResidue d b) x := by
  unfold depthClass
  rw [mod,←raw_port d _ hd b]
  rcases x with t|⟨i,j⟩
  · cases t <;> simp [Port,naturalDepth,armSize,actual_length r hd pos] <;> omega
  · rfl

theorem junctions_class (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (mod : orbitMod (M r d)=d) (x : V r d) :
    (∃ b,Junction r d b x) ↔ depthClass (M r d) 0 x := by
  unfold depthClass
  rw [mod,signed_zero_nat]
  rcases x with t|⟨i,j⟩
  · cases t <;> simp [Junction,naturalDepth,armSize,actual_length r hd pos]
  · simp [Junction,naturalDepth]

theorem ports_class (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (mod : orbitMod (M r d)=d) (x : V r d) :
    (∃ b,Port r d b x) ↔ depthClass (M r d) 1 x := by
  unfold depthClass
  rw [mod,show (1:ℤ)=((1:ℕ):ℤ) by rfl,signed_positive_nat d _ 1 (by decide) (by omega)]
  rcases x with t|⟨i,j⟩
  · cases t <;> simp [Port,naturalDepth,armSize,actual_length r hd pos] <;> omega
  · change (∃ b : Bool, (((j.val+1)%d=1 ∧ b=_) ∨ ((j.val+1)%d+1=d ∧ b=_))) ↔ _
    constructor
    · rintro ⟨_,⟨h,_⟩|⟨h,_⟩⟩
      · exact Or.inl h
      · exact Or.inr (by change (j.val+1)%d=d-1;omega)
    · rintro (h|h)
      · exact ⟨_,Or.inl ⟨h,rfl⟩⟩
      · exact ⟨_,Or.inr ⟨by change (j.val+1)%d=d-1 at h;omega,rfl⟩⟩

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.ports_class
#print axioms Bootstrap.Theta.Corridor.port_class
