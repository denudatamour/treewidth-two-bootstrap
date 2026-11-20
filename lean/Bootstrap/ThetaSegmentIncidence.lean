import Bootstrap.ThetaSegmentResidues
import Bootstrap.ThetaCorridorCounts
import Mathlib.Algebra.BigOperators.Fin

namespace Bootstrap.Theta.Corridor

open scoped Classical

private theorem card_instances {X : Type*} (i j : Fintype X) : @Fintype.card X i = @Fintype.card X j := by
  rw [Subsingleton.elim i j]

theorem principal_depth (m : Fin 3 → ℕ) (z : ℕ) (hz : z≤armSize m 0) :
    naturalDepth m 0 (armPt m 0 z)=z := by
  by_cases zero : z=0
  · subst z;rw [armPt_zero];rfl
  by_cases last : z=armSize m 0
  · rw [last,armPt_last];rfl
  have lt : z<armSize m 0 := by omega
  change naturalDepth m 0 (if z=0 then _ else if l : z<armSize m 0 then _ else _) = z
  simp only [if_neg zero,dif_pos lt,naturalDepth,inner]
  omega

theorem segment_le_of_cross (r : Fin 3 → ℕ) (d : ℕ) (c : Bool)
    (h : ∀ a b x y,Junction r d a x → Port r d b y → (c=true → a=b) → (F r d).Adj x y) :
    segmentGraph r d c ≤ F r d := by
  rintro x y (e|⟨_,q⟩)
  · exact initial_le_terminal _ _ e
  rcases q with ⟨a,b,hx,hy,col⟩|⟨a,b,hy,hx,col⟩
  · exact h a b x y hx hy col
  · exact (F r d).symm (h a b y x hy hx col)

private theorem half_coprime (q : ℕ) (odd : q%2=1) : ((q-1)/2).Coprime q := by
  apply Nat.eq_one_of_dvd_one
  let g := ((q-1)/2).gcd q
  have dvd₁ : g∣(q-1)/2 := Nat.gcd_dvd_left _ _
  have dvd₂ : g∣q := Nat.gcd_dvd_right _ _
  have h := Nat.dvd_sub dvd₂ (dvd_mul_of_dvd_right dvd₁ 2)
  rwa [show q-2*((q-1)/2)=1 by omega] at h

private theorem pred_coprime (q : ℕ) (pos : 0<q) : (q-1).Coprime q := by
  apply Nat.eq_one_of_dvd_one
  have h := Nat.dvd_sub (Nat.gcd_dvd_right (q-1) q) (Nat.gcd_dvd_left (q-1) q)
  rwa [show q-(q-1)=1 by omega] at h

/-- All actual endpoint--port incidences when the reduced lengths are odd,
including scale two where both port types are the same class. -/
theorem colored_segment_lower (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (prim : (r 0).gcd ((r 1).gcd (r 2))=1) (odd : ∀i,r i%2=1) :
    segmentGraph r d true ≤ F r d := by
  have mod : orbitMod (M r d)=2*d := by rw [scale_modulus r hd pos,odd_modulus r prim odd]
  have qOdd : (∑ i,r i)%2=1 := by simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero];change (r 0+(r 1+r 2))%2=1;have := odd 0;have := odd 1;have := odd 2;omega
  apply segment_le_of_cross
  intro a b x y hx hy col
  obtain rfl := col rfl
  have fa := junction_class r hd pos odd mod a
  have fb := port_class r hd pos mod a
  apply complete_class_incidence (M r d) _ _ _ _ fa fb _ _ x y hx hy
  · rw [card_junction r hd pos odd a,card_port r hd pos a]
    exact half_coprime _ qOdd
  · let M' := M r d
    have room : d≤armSize M' 0 := by
      change d≤M r d 0+2
      rw [actual_length r hd pos]
      exact Nat.le_mul_of_pos_left _ (pos 0)
    have cu : jointResidue d a≤d := by cases a <;> simp [jointResidue]
    have cv : portResidue d a≤d := by cases a <;> simp [portResidue] <;> omega
    refine ⟨armPt M' 0 (jointResidue d a),armPt M' 0 (portResidue d a), (fa _).mpr ?_,(fb _).mpr ?_,?_⟩
    · unfold depthClass
      rw [principal_depth M' _ (cu.trans room)]
      exact Or.inl Int.ModEq.rfl
    · unfold depthClass
      rw [principal_depth M' _ (cv.trans room)]
      exact Or.inl Int.ModEq.rfl
    · apply initial_le_terminal
      cases a
      · exact point_edge M' 0 (z:=0) (by change 0<armSize M' 0;omega)
      · have e := point_edge M' 0 (z:=d-1) (by change d-1<armSize M' 0;omega)
        rw [Nat.sub_add_cancel (by omega : 1≤d)] at e
        exact (graph M').symm e

private theorem port_two_eq (r : Fin 3 → ℕ) (x : V r 2) :
    (∃ b,Port r 2 b x) ↔ Port r 2 false x := by
  rcases x with b|⟨i,j⟩
  · simp [Port]
  · constructor
    · rintro ⟨b,⟨k,_⟩|⟨k,_⟩⟩ <;>
        cases h : decide (((j.val+1)/2)%2=1) <;>
        first | exact Or.inl ⟨by omega,h.symm⟩ | exact Or.inr ⟨by omega,by rw [h];rfl⟩
    · exact fun h => ⟨false,h⟩

private theorem uncolored_lower_of_coprime (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (mod : orbitMod (M r d)=d)
    (cop : (Fintype.card (Joint r d)).Coprime (Fintype.card {x : V r d // ∃b,Port r d b x})) :
    segmentGraph r d false ≤ F r d := by
  apply segment_le_of_cross
  intro a b x y hx hy _
  have joint := junctions_class r hd pos mod
  have port := ports_class r hd pos mod
  apply complete_class_incidence (M r d) _ _ _ _ joint port _ _ x y ⟨a,hx⟩ ⟨b,hy⟩
  · convert cop using 1 <;> apply card_instances
  refine ⟨pole _ false,armPt _ 0 1,⟨false,rfl⟩,(port _).mpr ?_,(thetaClosure _).symm (pole_first _ 0)⟩
  unfold depthClass
  rw [principal_depth _ 1 (by simp [armSize])]
  exact Or.inl Int.ModEq.rfl

theorem mixed_segment_lower_even_count (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (prim : (r 0).gcd ((r 1).gcd (r 2))=1) (mix : ∃i j,r i%2≠r j%2)
    (enough : d=2 ∨ (∑ i,r i)%2=0) : segmentGraph r d false ≤ F r d := by
  have mod : orbitMod (M r d)=d := by rw [scale_modulus r hd pos,mixed_modulus r prim pos mix,one_mul]
  apply uncolored_lower_of_coprime r hd pos mod
  let q := ∑ i,r i
  have qp : 0<q := by dsimp [q];simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero];have := pos 0;omega
  have cop := pred_coprime q qp
  rw [card_junctions r hd pos]
  by_cases h : d=2
  · subst d
    have eq := Fintype.card_congr (Equiv.subtypeEquivRight (port_two_eq r))
    rw [eq,card_port r (by decide) pos false];exact cop
  · rw [card_ports r (by omega) pos]
    have qe : q%2=0 := enough.resolve_left h
    have t : Odd (q-1) := Nat.odd_iff.mpr (by omega)
    exact t.coprime_two_right.mul_right cop

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.colored_segment_lower
#print axioms Bootstrap.Theta.Corridor.mixed_segment_lower_even_count
