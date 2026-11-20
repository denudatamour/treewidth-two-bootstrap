import Bootstrap.ThetaSlotReflections
import Bootstrap.ThetaCorridorSegments

namespace Bootstrap.Theta.Corridor

open scoped Classical

def IsTip (r : Fin 3 → ℕ) (d : ℕ) (s : Slot r) (v : V r d) := ∃ a,v=tip r d s a

theorem tip_unique (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i,0<r i)
    {u v : Slot r} {x : V r d} (h : IsTip r d u x) (g : IsTip r d v x) : u=v := by
  obtain ⟨a,h⟩ := h
  obtain ⟨b,g⟩ := g
  exact tips_determine_slot r hd pos (h.symm.trans g)

theorem port_iff_tip (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i,0<r i)
    (x : V r d) : (∃ b,Port r d b x) ↔ ∃s,IsTip r d s x := by
  constructor
  · rintro ⟨b,hb⟩
    rcases x with b'|⟨i,j⟩
    · exact False.elim hb
    let z := j.val+1
    let k := z/d
    have small : k<r i := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<d)).mpr
      rw [←actual_length r hd pos]
      have := j.isLt;dsimp [z];omega
    let s : Slot r := ⟨i,⟨k,small⟩⟩
    have rep : k*d+z%d=z := Nat.div_add_mod' _ _
    rcases hb with ⟨one,_⟩|⟨last,_⟩
    · refine ⟨s,false,?_⟩
      change z%d=1 at one
      change inner _ i j=point _ i (k*d+1)
      rw [←one,rep];exact (point_inner ..).symm
    · refine ⟨s,true,?_⟩
      change z%d+1=d at last
      change inner _ i j=point _ i (k*d+(d-1))
      rw [show d-1=z%d by omega,rep];exact (point_inner ..).symm
  · rintro ⟨s,a,rfl⟩
    obtain ⟨b,h,_⟩ := port_of_side r hd pos false s (tipDepth d a) a rfl
    exact ⟨b,h⟩

def slotGroup (r : Fin 3 → ℕ) (d : ℕ) : Subgroup (Equiv.Perm (V r d)) where
  carrier := {p | ∃ f : Equiv.Perm (Slot r), ∀ v s,IsTip r d (f s) (p v) ↔ IsTip r d s v}
  one_mem' := ⟨1,fun _ _ => Iff.rfl⟩
  mul_mem' := by
    rintro p q ⟨f,h⟩ ⟨g,k⟩
    exact ⟨f*g,fun v s => (h (q v) (g s)).trans (k v s)⟩
  inv_mem' := by
    rintro p ⟨f,h⟩
    exact ⟨f⁻¹,fun v s => by simpa only [Equiv.Perm.apply_inv_self] using (h (p⁻¹ v) (f⁻¹ s)).symm⟩

private theorem flip_twice (a b : Bool) : tipFlip a (tipFlip a b)=b := by cases a <;> cases b <;> rfl

theorem group_on_slots (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i,0<r i) :
    reflectionGroup (M r d) ≤ slotGroup r d := by
  apply (Subgroup.closure_le _).mpr
  rintro p ⟨i,j,ij,b,rfl⟩
  let p := reflection (M r d) ij b
  choose f rev act using reflection_sends_slot r hd pos ij b
  have inj : Function.Injective f := by
    intro s t eq
    let c := tipFlip (rev t) (tipFlip (rev s) false)
    have e : p (tip r d s false)=p (tip r d t c) := by
      change reflection _ ij b _=reflection _ ij b _
      rw [act,act,eq,show tipFlip (rev t) c=tipFlip (rev s) false from flip_twice ..]
    exact tips_determine_slot r hd pos (p.injective e)
  let q := Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨q,fun v s => ?_⟩
  constructor
  · rintro ⟨c,h⟩
    refine ⟨tipFlip (rev s) c,p.injective ?_⟩
    change reflection _ ij b v=reflection _ ij b _
    rw [act,flip_twice];exact h
  · rintro ⟨c,rfl⟩
    exact ⟨tipFlip (rev s) c,act s c⟩

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.port_iff_tip
#print axioms Bootstrap.Theta.Corridor.group_on_slots
