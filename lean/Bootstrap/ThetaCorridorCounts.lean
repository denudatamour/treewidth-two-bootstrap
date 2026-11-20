import Bootstrap.ThetaCorridorChart
import Bootstrap.ThetaColourBalance
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Bootstrap.Theta.Corridor
open scoped Classical

private def depthEquiv (d : ℕ) : Depth d ≃ Fin (d-1) where
  toFun j := ⟨j.val-1,by have := j.2; omega⟩
  invFun k := ⟨k.val+1,by have := k.isLt; omega⟩
  left_inv j := Subtype.ext (by have := j.2; change j.val-1+1=j.val; omega)
  right_inv k := Fin.ext (by change k.val+1-1=k.val; omega)

theorem card_junctions (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i) :
    Fintype.card {x : V r d // ∃ b, Junction r d b x} = (∑ i, r i)-1 := by
  classical
  letI : Fintype (Depth d) := Fintype.ofEquiv _ (depthEquiv d).symm
  have depth : Fintype.card (Depth d)=d-1 := (Fintype.card_congr (depthEquiv d)).trans (Fintype.card_fin _)
  have count := Fintype.card_congr (chart r hd pos false)
  change Fintype.card (Joint r d ⊕ (Slot r × Depth d)) =
    Fintype.card (Bool ⊕ (Σ i, Fin (M r d i+1))) at count
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_sigma,Fintype.card_fin,
    Fintype.card_bool,depth] at count
  have terms : (∑ i, (M r d i+1))+3=(∑ i, r i)*d := by
    calc
      _ = ∑ i, ((M r d i+1)+1) := by simp [Finset.sum_add_distrib]
      _ = ∑ i, r i*d := Finset.sum_congr rfl fun i _ => actual_length r hd pos i
      _ = _ := by rw [Finset.sum_mul]
  have reduce : d-1+1=d := by omega
  have arith := congrArg (fun x : ℕ => (∑ i, r i)*x) reduce
  simp only [Nat.mul_add,Nat.mul_one] at arith
  change Fintype.card (Joint r d) = _
  omega

private def side (b : Bool) (d : ℕ) := if b then d-1 else 1

private theorem distinct_kinds (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) {x : V r d} {a b : Bool}
    (joint : Junction r d a x) (port : Port r d b x) : False := by
  rcases x with z|⟨i,j⟩
  · exact port
  · obtain ⟨j₀,_⟩ := joint
    rcases port with ⟨one,_⟩|⟨last,_⟩ <;> omega

private theorem port_inside_iff (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (s : Slot r) (j : Depth d) (b : Bool) :
    Port r d b (inside r d true s j) ↔ j.val=side b d := by
  let u := orient true d s.2.val j.val
  obtain ⟨lo,hi⟩ := orient_range true (k:=s.2.val) j.2.1 j.2.2
  have bounds := inside_bound r hd pos s lo hi
  unfold inside
  rw [point_interior _ bounds.1 bounds.2]
  change (((s.2.val*d+u-1+1)%d=1 ∧ b=decide (((s.2.val*d+u-1+1)/d)%2=1)) ∨
    ((s.2.val*d+u-1+1)%d+1=d ∧ b=!(decide (((s.2.val*d+u-1+1)/d)%2=1)))) ↔ _
  rw [Nat.sub_add_cancel bounds.1,(divmod (k:=s.2.val) (by omega : 0<d) hi).1,
    (divmod (k:=s.2.val) (by omega : 0<d) hi).2]
  have := j.2.1
  have := j.2.2
  by_cases odd : s.2.val%2=1 <;> cases b <;> simp [odd,u,orient,side] <;> omega

theorem card_port (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i) (b : Bool) :
    Fintype.card {x : V r d // Port r d b x} = ∑ i, r i := by
  classical
  let j : Depth d := ⟨side b d,by cases b <;> simp [side] <;> omega⟩
  let f (s : Slot r) : {x : V r d // Port r d b x} :=
    ⟨inside r d true s j,(port_inside_iff r hd pos s j b).mpr rfl⟩
  have inj : Function.Injective f := by
    intro s t eq
    have h : chart r hd pos true (.inr (s,j))=chart r hd pos true (.inr (t,j)) := congrArg Subtype.val eq
    exact congrArg Prod.fst (Sum.inr.inj ((chart r hd pos true).injective h))
  have sur : Function.Surjective f := by
    rintro ⟨v,hv⟩
    obtain ⟨u,rfl⟩ := (chart r hd pos true).surjective v
    rcases u with a|⟨s,k⟩
    · obtain ⟨c,hc⟩ := a.2
      exact (distinct_kinds r hd hc hv).elim
    · have eq : k=j := Subtype.ext ((port_inside_iff r hd pos s k b).mp hv)
      subst k
      exact ⟨s,rfl⟩
  have h := (Fintype.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)).symm
  simpa [Slot,Fintype.card_sigma] using h

private theorem bool_union {X : Type*} [Fintype X] (p : Bool → X → Prop)
    (apart : ∀ x, p false x → p true x → False) :
    Fintype.card {x // ∃ b, p b x} = Fintype.card {x // p false x}+Fintype.card {x // p true x} := by
  have eq : {x // ∃ b, p b x} ≃ {x // p false x ∨ p true x} :=
    Equiv.subtypeEquivRight fun _ => Bool.exists_bool
  calc
    _ = _ := Fintype.card_congr eq
    _ = _ := Fintype.card_subtype_or_disjoint _ _ (disjoint_iff_inf_le.mpr fun x h => apart x h.1 h.2)

theorem card_ports (r : Fin 3 → ℕ) {d : ℕ} (hd : 3≤d) (pos : ∀ i, 0<r i) :
    Fintype.card {x : V r d // ∃ b, Port r d b x} = 2*(∑ i, r i) := by
  rw [bool_union (Port r d),card_port r (by omega) pos,card_port r (by omega) pos,Nat.two_mul]
  intro x
  rcases x with z|⟨i,j⟩
  · exact False.elim
  · rintro (⟨h,e⟩|⟨h,e⟩) (⟨k,f⟩|⟨k,f⟩) <;> first | exact Bool.false_ne_true (e.trans f.symm) | omega

private theorem reverse_joint (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (odd : ∀ i, r i%2=1) {b : Bool} {x : V r d} (h : Junction r d b x) :
    Junction r d (!b) (reversePosition (M r d) x) := by
  rcases x with z|⟨i,j⟩
  · change b=z at h
    subst b
    rfl
  · obtain ⟨multiple,rfl⟩ := h
    let n := j.val+1
    let k := n/d
    have mul : k*d=n := by
      have e := Nat.div_add_mod n d
      change n%d=0 at multiple
      rw [multiple,Nat.add_zero,Nat.mul_comm] at e
      exact e
    have lim : n<r i*d := by rw [←actual_length r hd pos]; have := j.isLt; dsimp [n]; omega
    have kl : k<r i := (Nat.mul_lt_mul_right (by omega : 0<d)).mp (mul ▸ lim)
    have a : j.rev.val+1 = (r i-k)*d := by
      rw [Nat.sub_mul,mul,←actual_length r hd pos,Fin.val_rev]
      have := j.isLt
      dsimp [n]
      omega
    change (j.rev.val+1)%d=0 ∧ (!(decide (k%2=1)))=decide (((j.rev.val+1)/d)%2=1)
    rw [a,Nat.mul_mod_left,Nat.mul_div_cancel _ (by omega : 0<d)]
    have := odd i
    by_cases par : k%2=1 <;> simp [par] <;> omega

theorem card_junction (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (odd : ∀ i, r i%2=1) (b : Bool) :
    Fintype.card {x : V r d // Junction r d b x} = ((∑ i, r i)-1)/2 := by
  classical
  let j (a : Bool) := {x : V r d // Junction r d a x}
  let rev (a : Bool) (x : j a) : j (!a) := ⟨_,reverse_joint r hd pos odd x.2⟩
  let bij : j false ≃ j true :=
    ⟨rev false,rev true,fun x => Subtype.ext (reverse_twice _ _),fun x => Subtype.ext (reverse_twice _ _)⟩
  let same := Fintype.card_congr bij
  have apart (x : V r d) (h : Junction r d false x) (k : Junction r d true x) : False := by
    rcases x with z|⟨i,j⟩
    · exact Bool.false_ne_true (h.trans k.symm)
    · exact Bool.false_ne_true (h.2.trans k.2.symm)
  have tot := (bool_union (Junction r d) apart).symm.trans (card_junctions r hd pos)
  change Fintype.card (j false)+Fintype.card (j true)=(∑ i, r i)-1 at tot
  cases b <;> change Fintype.card (j _) = _ <;> omega

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.card_junctions
#print axioms Bootstrap.Theta.Corridor.card_port
#print axioms Bootstrap.Theta.Corridor.card_ports
#print axioms Bootstrap.Theta.Corridor.card_junction
