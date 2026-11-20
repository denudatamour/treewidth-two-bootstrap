import Bootstrap.PrimitiveContraction
import Bootstrap.ThetaIntegerChart
import Bootstrap.ThetaSelfBipartite

namespace Bootstrap.Theta.Contraction

open scoped Classical
variable {k : Nat}

def natPoint (m : Fin k → Nat) (a c : Fin k) (t : Nat) := intPt m a c (t : Int)

theorem chart_inj (m : Fin k → Nat) {a c : Fin k} (ac : a ≠ c) (u v : Nat)
    (ul : u < perimeter m a c) (vl : v < perimeter m a c)
    (eq : natPoint m a c u = natPoint m a c v) : u = v := by
  have h := congrArg (vertexCoord m a c) eq
  simp only [natPoint,intPt,coord_pt m ac,indexZ_nat] at h
  have val := congrArg Fin.val h
  simpa only [Fin.val_natCast,Nat.mod_eq_of_lt ul,Nat.mod_eq_of_lt vl] using val

theorem strip_off (m : Fin 3 → Nat) {a b c : Fin 3} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (w : Vertex m) : w ∈ strip (natPoint m a c) 1 (armSize m a) ↔ ¬OnCycle b c w := by
  constructor
  · intro h
    obtain ⟨t,t₀,ta,rfl⟩ := mem_strip.mp h
    change ¬OnCycle b c (intPt m a c t)
    rw [intPt_first m a c t ta.le]
    simp only [armPt,show t ≠ 0 by omega,if_false,dif_pos ta,inner,OnCycle]
    exact fun eq => eq.elim ab ac
  · intro off
    rcases w with z | ⟨i,j⟩
    · exact (off trivial).elim
    · have ib : i ≠ b := fun h => off (Or.inl h)
      have ic : i ≠ c := fun h => off (Or.inr h)
      have ia := third_of_ne bc ab.symm ac.symm i ib ic
      subst i
      have lt : j.val+1 < armSize m a := by dsimp [armSize];have := j.isLt;omega
      exact mem_strip.mpr ⟨j.val+1,by omega,lt,(intPt_first _ _ _ _ lt.le).trans (armPt_inner ..)⟩

private theorem on_rep (m : Fin k → Nat) {b c : Fin k} (bc : b ≠ c) (w : Vertex m)
    (on' : OnCycle b c w) : ∃ z : Int, intPt m b c z = w := by
  let t := vertexCoord m b c w
  exact ⟨t.val,by rw [intPt,indexZ_val];exact pt_coord m bc w on'⟩

private theorem inner_orbit_inj (m : Fin k → Nat) {b c : Fin k} (bc : b ≠ c)
    {f d : Nat} (pos : 0 < d) (fits : f*d < perimeter m b c) (z : Int) :
    Function.Injective (fun t : Fin (f+1) => intPt m b c (z + ((t.val*d : Nat) : Int))) := by
  intro i j eq
  have e := congrArg (vertexCoord m b c) eq
  simp only [intPt,coord_pt m bc,indexZ_add] at e
  have e' := add_left_cancel e
  rw [indexZ_nat,indexZ_nat] at e'
  have inbounds (t : Fin (f+1)) : t.val*d < perimeter m b c :=
    (Nat.mul_le_mul_right d (by have := t.isLt;omega)).trans_lt fits
  have ev := congrArg Fin.val e'
  rw [Fin.val_natCast,Fin.val_natCast,Nat.mod_eq_of_lt (inbounds i),Nat.mod_eq_of_lt (inbounds j)] at ev
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right pos ev)

/-- A genuine rotation on the outside two-arm cycle produces f+1 distinct missing
neighbours. No assumption on an unknown graph orbit length is needed. -/
theorem outside_rotation (m : Fin 3 → Nat) {a b c : Fin 3}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (Q : SimpleGraph (Vertex m)) (f d : Nat)
    (pos : 0 < d) (fits : f*d < perimeter m b c) (β : Q ≃g Q)
    (moves : ∀ z : Int, β (intPt m b c z) = intPt m b c (z+d))
    (fixes : ∀ w, ¬OnCycle b c w → β w = w) :
    OutsideOrbit Q (strip (natPoint m a c) 1 (armSize m a)) f := by
  intro u hu w edge away
  have fu := fixes u ((strip_off m ab ac bc u).mp hu)
  have ow : OnCycle b c w := by
    by_contra bad
    exact away ((strip_off m ab ac bc w).mpr bad)
  obtain ⟨z,rfl⟩ := on_rep m bc w ow
  have all (t : Nat) : Q.Adj u (intPt m b c (z + ((t*d : Nat) : Int))) := by
    induction t with
    | zero => simpa using edge
    | succ t ih =>
      have h := β.map_adj_iff.mpr ih
      rw [fu,moves] at h
      simpa only [Nat.succ_mul,Nat.cast_add,add_assoc] using h
  refine ⟨⟨_,inner_orbit_inj m bc pos fits z⟩,?_⟩
  intro i
  refine ⟨all i.val,?_⟩
  intro inside
  exact ((strip_off m ab ac bc _).mp inside) (cyclePt_on ..)

/-- On an odd-length theta each natural cycle coordinate has its usual parity. -/
theorem color_natPoint (m : Fin k → Nat) (a c : Fin k) (odd : ∀ i, armSize m i % 2 = 1)
    (t : Nat) (ht : t < perimeter m a c) :
    naturalColor m 1 (natPoint m a c t) = decide (t%2=1) := by
  have val : (indexZ (perimeter m a c) (t:Int)).val=t := by
    rw [indexZ_nat,Fin.val_natCast,Nat.mod_eq_of_lt ht]
  have even : perimeter m a c % 2 = 0 := by
    have h1 := odd a;have h2 := odd c; dsimp [perimeter];omega
  unfold natPoint intPt cyclePt
  simp only [val]
  split
  · rename_i z
    simp [z,naturalColor,pole]
  · split
    · rename_i e
      simp [e,odd,naturalColor,pole]
    · split
      · change decide ((t-1+1)%2=1) = decide (t%2=1)
        congr 2
        omega
      · change decide ((perimeter m a c-t-1+1)%2=1) = decide (t%2=1)
        have e : (perimeter m a c-t-1+1)%2=t%2 := by omega
        rw [e]

theorem odd_thin (m : Fin k → Nat) (a c : Fin k) (odd : ∀ i, armSize m i % 2 = 1)
    (Q : SimpleGraph (Vertex m)) (cross : ∀ z w, Q.Adj z w → naturalColor m 1 z ≠ naturalColor m 1 w)
    (f : Nat) : Thin Q (natPoint m a c) (perimeter m a c) (2*f) f := by
  refine Or.inr ⟨rfl,?_⟩
  intro z i j hi hj ei ej
  have d₁ := cross _ _ ei
  have d₂ := cross _ _ ej
  rw [color_natPoint m a c odd i hi] at d₁
  rw [color_natPoint m a c odd j hj] at d₂
  have unique (x y z : Bool) (xy : x ≠ y) (xz : x ≠ z) : y = z := by
    cases x <;> cases y <;> cases z <;> simp_all
  have eq := decide_eq_decide.mp (unique _ _ _ d₁ d₂)
  omega

end Bootstrap.Theta.Contraction

#print axioms Bootstrap.Theta.Contraction.outside_rotation
#print axioms Bootstrap.Theta.Contraction.odd_thin
