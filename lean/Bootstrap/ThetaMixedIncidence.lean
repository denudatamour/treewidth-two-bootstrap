import Bootstrap.ThetaSlotActions
import Bootstrap.ThetaSegmentIncidence

namespace Bootstrap.Theta.Corridor

open scoped Classical

private def slotInc (r : Fin 3 → ℕ) (d : ℕ) (both : Bool) (x : V r d) (s : Slot r) : Prop :=
  if both then ∀ v,IsTip r d s v → (F r d).Adj x v
  else ∃ v,IsTip r d s v ∧ (F r d).Adj x v

private theorem slotInc_equiv (r : Fin 3 → ℕ) {d : ℕ} (both : Bool) (p : Equiv.Perm (V r d))
    (hp : p∈reflectionGroup (M r d)) (f : Equiv.Perm (Slot r))
    (hf : ∀v s,IsTip r d (f s) (p v) ↔ IsTip r d s v) (x : V r d) (s : Slot r) :
    slotInc r d both (p x) (f s) ↔ slotInc r d both x s := by
  have edge (v : V r d) : (F r d).Adj (p x) (p v) ↔ (F r d).Adj x v := preserves_of_mem _ hp _ _
  cases both
  · constructor
    · rintro ⟨w,hw,he⟩
      obtain ⟨v,rfl⟩ := p.surjective w
      exact ⟨v,(hf _ _).mp hw,(edge _).mp he⟩
    · rintro ⟨v,hv,he⟩
      exact ⟨p v,(hf _ _).mpr hv,(edge _).mpr he⟩
  · constructor
    · intro h v hv
      exact (edge _).mp (h _ ((hf _ _).mpr hv))
    · intro h w hw
      obtain ⟨v,rfl⟩ := p.surjective w
      exact (edge _).mpr (h _ ((hf _ _).mp hw))

private theorem slotInc_full (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (mod : orbitMod (M r d)=d) (both : Bool)
    (hit : ∃ (x : Joint r d) (s : Slot r),slotInc r d both x.val s) :
    ∀ (x : Joint r d) (s : Slot r),slotInc r d both x.val s := by
  let q := ∑ i,r i
  have qp : 0<q := by dsimp [q];simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero];have := pos 0;omega
  have cop : (Fintype.card (Joint r d)).Coprime (Fintype.card (Slot r)) := by
    rw [card_junctions r hd pos]
    simp only [Slot,Fintype.card_sigma,Fintype.card_fin]
    apply Nat.eq_one_of_dvd_one
    have h := Nat.dvd_sub (Nat.gcd_dvd_right (q-1) q) (Nat.gcd_dvd_left (q-1) q)
    rwa [show q-(q-1)=1 by omega] at h
  let J := junctions_class r hd pos mod
  let P := ports_class r hd pos mod
  have act : ∀p : Equiv.Perm (V r d), p∈reflectionGroup (M r d) →
        ∃f : Equiv.Perm (Slot r),∀v s, IsTip r d (f s) (p v) ↔ IsTip r d s v :=
    fun _ hp => group_on_slots r hd pos hp
  let onJ (p : Equiv.Perm (V r d)) (hp : p∈reflectionGroup (M r d)) : Equiv.Perm (Joint r d) :=
    p.subtypeEquiv (fun x => (J x).trans ((group_preserves_class _ 0 hp x).symm.trans (J (p x)).symm))
  apply ThetaIncidence.full_of_transitive (fun (x : Joint r d) (s : Slot r) => slotInc r d both x.val s) cop hit
  · intro x y
    obtain ⟨p,hp,eq⟩ := (reflectionRelated_iff_signed ..).mpr
      (((J x.val).mp x.2).trans ((J y.val).mp y.2).symm)
    obtain ⟨f,hf⟩ := act p hp
    refine ⟨f,fun s => ?_⟩
    rw [←eq];exact (slotInc_equiv r both p hp f hf x.val s).symm
  · intro s t
    have tagged (u : Slot r) : depthClass (M r d) 1 (tip r d u false) :=
      (P _).mp ((port_iff_tip r hd pos _).mpr ⟨u,false,rfl⟩)
    obtain ⟨p,hp,eq⟩ := (reflectionRelated_iff_signed ..).mpr ((tagged s).trans (tagged t).symm)
    obtain ⟨f,hf⟩ := act p hp
    have hold := (hf (tip r d s false) s).mpr ⟨false,rfl⟩
    rw [eq] at hold
    have ft : f s=t := tip_unique r hd pos hold ⟨false,rfl⟩
    refine ⟨onJ p hp,fun x => ?_⟩
    change slotInc r d both x.val s ↔ slotInc r d both (p x.val) t
    rw [←ft];exact (slotInc_equiv r both p hp f hf x.val s).symm

set_option maxHeartbeats 1200000 in
/-- For mixed reduced parity, a polar reflection that reverses both tips
of one segment forces complete junction--port incidence in the actual closure. -/
theorem mixed_lower_of_middle (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀i,0<r i)
    (prim : (r 0).gcd ((r 1).gcd (r 2))=1) (mix : ∃i j,r i%2≠r j%2)
    (middle : ∃ s : Slot r,∃ p : Equiv.Perm (V r d), p∈reflectionGroup (M r d) ∧
      p (pole (M r d) false)=pole (M r d) false ∧
      p (inside r d false s 1)=inside r d false s (d-1) ∧
      p (inside r d false s (d-1))=inside r d false s 1) :
    segmentGraph r d false ≤ F r d := by
  have mod : orbitMod (M r d)=d := by rw [scale_modulus r hd pos,mixed_modulus r prim pos mix,one_mul]
  let left : Joint r d := ⟨pole _ false,false,rfl⟩
  let slot : Slot r := ⟨0,⟨0,pos 0⟩⟩
  have first : tip r d slot false=armPt (M r d) 0 1 := by
    simp only [tip,slot,inside,tipDepth,Bool.false_eq_true,if_false,Nat.zero_mul,Nat.zero_add,orient,false_and]
    rfl
  have some : ∀ (x : Joint r d) (s : Slot r),slotInc r d false x.val s := by
    apply slotInc_full r hd pos mod false
    refine ⟨left,slot,tip r d slot false,⟨false,rfl⟩,?_⟩
    rw [first]
    exact (F r d).symm (pole_first _ 0)
  obtain ⟨s,p,hp,fix,sw,ws⟩ := middle
  have e := some left s
  obtain ⟨_,⟨a,rfl⟩,edge⟩ := e
  have both : (F r d).Adj left.val (tip r d s false) ∧ (F r d).Adj left.val (tip r d s true) := by
    have moved := (preserves_of_mem _ hp _ _).mpr edge
    change p left.val=left.val at fix
    rw [fix] at moved
    cases a
    · change (F r d).Adj left.val (p (inside r d false s 1)) at moved
      rw [sw] at moved
      exact ⟨edge,moved⟩
    · change (F r d).Adj left.val (p (inside r d false s (d-1))) at moved
      rw [ws] at moved
      exact ⟨moved,edge⟩
  have all : ∀ (x : Joint r d) (t : Slot r),slotInc r d true x.val t := by
    apply slotInc_full r hd pos mod true
    refine ⟨left,s,?_⟩
    rintro v ⟨b,rfl⟩
    cases b
    · exact both.1
    · exact both.2
  apply segment_le_of_cross
  intro a b x y hx hy _
  obtain ⟨t,ht⟩ := (port_iff_tip r hd pos y).mp ⟨b,hy⟩
  exact all ⟨x,a,hx⟩ t y ht

end Bootstrap.Theta.Corridor
#print axioms Bootstrap.Theta.Corridor.mixed_lower_of_middle
