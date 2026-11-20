import Bootstrap.PrimitiveFromSeeds
import Bootstrap.ThetaVertexOrbits
import Bootstrap.ThetaExternalSeeds

namespace Bootstrap.Theta.Contraction

open scoped Classical

theorem reflection_motions (m : Fin 3 → Nat) : Motions m (reflectionGroup m) := by
  constructor
  · intro i j ij d div
    exact translation_of_dvd m ij (by exact_mod_cast div)
  · intro i j ij
    exact ⟨reflection m ij false,reflection_mem m ij false,false_reflect_int m ij⟩

/-- Primitive arm lengths force the signed orbit modulus to divide two. -/
theorem primitive_modulus_dvd_two (a b c : Nat) (prim : a.gcd (b.gcd c) = 1) :
    (2*a).gcd ((a+b).gcd (a+c)) ∣ 2 := by
  let q := (2*a).gcd ((a+b).gcd (a+c))
  have qa : q ∣ 2*a := Nat.gcd_dvd_left _ _
  have add : q ∣ (a+b).gcd (a+c) := Nat.gcd_dvd_right _ _
  have extract (x : Nat) (h : q ∣ a+x) : q ∣ 2*x := by
    have sub := Nat.dvd_sub (dvd_mul_of_dvd_right h 2) qa
    simpa only [show 2*(a+x)-2*a=2*x by omega] using sub
  have qb := extract b (add.trans (Nat.gcd_dvd_left _ _))
  have qc := extract c (add.trans (Nat.gcd_dvd_right _ _))
  have d := Nat.dvd_gcd qa (Nat.dvd_gcd qb qc)
  rwa [Nat.gcd_mul_left,Nat.gcd_mul_left,prim,Nat.mul_one] at d

theorem primitive_mixed_modulus (a b c : Nat) (apos : 0 < a)
    (prim : a.gcd (b.gcd c) = 1) (opp : a%2 ≠ c%2) :
    (2*a).gcd ((a+b).gcd (a+c)) = 1 := by
  let q := (2*a).gcd ((a+b).gcd (a+c))
  have le : q ≤ 2 := Nat.le_of_dvd (by decide) (primitive_modulus_dvd_two a b c prim)
  have pos : 0 < q := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (by decide) apos)
  have dv : q ∣ a+c := (Nat.gcd_dvd_right (2*a) ((a+b).gcd (a+c))).trans (Nat.gcd_dvd_right _ _)
  change q = 1
  by_contra bad
  have q₂ : q = 2 := by omega
  rw [q₂] at dv
  have := Nat.dvd_iff_mod_eq_zero.mp dv
  omega

private theorem color_arm (m : Fin 3 → Nat) (odd : ∀ i, armSize m i % 2 = 1)
    (i : Fin 3) (d : Nat) (dle : d ≤ armSize m i) :
    naturalColor m 1 (armPt m i d) = decide (d%2=1) := by
  have lt : d < perimeter m i i := by dsimp [perimeter,armSize] at *;omega
  have c := color_natPoint m i i odd d lt
  change naturalColor m 1 (intPt m i i d) = _ at c
  rwa [intPt_first m i i d dle] at c

theorem primitive_color_transitive (m : Fin 3 → Nat) {a b c : Fin 3}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (prim : (armSize m a).gcd ((armSize m b).gcd (armSize m c)) = 1)
    (odd : ∀ i, armSize m i % 2 = 1) (x y : Vertex m)
    (same : naturalColor m 1 x = naturalColor m 1 y) : reflectionRelated m x y := by
  obtain ⟨i,d,hd,rfl⟩ := arm_representation m x
  obtain ⟨j,e,he,rfl⟩ := arm_representation m y
  rw [color_arm m odd i d hd,color_arm m odd j e he] at same
  have prop := decide_eq_decide.mp same
  have par : d%2=e%2 := by omega
  have pz : (d:Int)%2=(e:Int)%2 := by exact_mod_cast par
  have div2 : (2:Int) ∣ (d:Int)-e := ⟨(d:Int)/2-(e:Int)/2,by omega⟩
  have dv := primitive_modulus_dvd_two _ _ _ prim
  let g := (2*armSize m a).gcd ((perimeter m a b).gcd (perimeter m a c))
  change g ∣ 2 at dv
  have di : (g:Int) ∣ (2:Int) := by exact_mod_cast dv
  exact related_of_dvd m ab ac bc i j d e hd he (Or.inl (di.trans div2))

/-- The mixed terminal-graph contraction in the case not covered by a coprime pair. -/
theorem primitive_mixed_after_seed (m : Fin 3 → Nat) {a b c : Fin 3}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (prim : (armSize m a).gcd ((armSize m b).gcd (armSize m c)) = 1)
    (notAB : 1 < (armSize m a).gcd (armSize m b)) (notAC : 1 < (armSize m a).gcd (armSize m c))
    (pa : armSize m a % 2 ≠ armSize m c % 2) (pb : armSize m b % 2 ≠ armSize m c % 2)
    (seed : ∀ z : Int, (thetaClosure m).Adj (armPt m a 1) (intPt m b c z)) :
    thetaClosure m = ⊤ := by
  apply mixed_from_seed m ab ac bc (reflectionGroup m) (reflection_motions m) _
    (fun _ hp => preserves_of_mem m hp) _ (by simpa only [Nat.gcd_assoc] using prim) notAB notAC pa pb seed
  exact transitive_when_one m ab ac bc (primitive_mixed_modulus _ _ _ (by simp [armSize]) prim pa)

/-- The all-odd terminal-graph contraction in the case not covered by a coprime pair. -/
theorem primitive_odd_after_seed (m : Fin 3 → Nat) {a b c : Fin 3}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (prim : (armSize m a).gcd ((armSize m b).gcd (armSize m c)) = 1)
    (notAB : 1 < (armSize m a).gcd (armSize m b)) (notAC : 1 < (armSize m a).gcd (armSize m c))
    (notBC : 1 < (armSize m b).gcd (armSize m c)) (order : armSize m c < armSize m b)
    (odd : ∀ i, armSize m i % 2 = 1)
    (seed : ∀ z : Int, z%2=0 → (thetaClosure m).Adj (armPt m a 1) (intPt m b c z)) :
    thetaClosure m = completeBetween (naturalColor m 1) :=
  odd_from_seed m ab ac bc (reflectionGroup m) (reflection_motions m) _ (fun _ hp => preserves_of_mem m hp)
    (initial_le_terminal _ _) (terminal_le_natural m (by decide) 1 odd)
    (primitive_color_transitive m ab ac bc prim odd) (by simpa only [Nat.gcd_assoc] using prim)
    notAB notAC notBC order odd seed

end Bootstrap.Theta.Contraction

#print axioms Bootstrap.Theta.Contraction.primitive_mixed_after_seed
#print axioms Bootstrap.Theta.Contraction.primitive_odd_after_seed
