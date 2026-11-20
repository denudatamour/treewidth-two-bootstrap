import Bootstrap.ThetaCorridor

namespace Bootstrap.Theta.Corridor

abbrev Slot (r : Fin 3 → ℕ) := Σ i, Fin (r i)
abbrev Depth (d : ℕ) := {j : ℕ // 0<j ∧ j<d}
abbrev Joint (r : Fin 3 → ℕ) (d : ℕ) := {x : V r d // ∃ b, Junction r d b x}
abbrev Forms (r : Fin 3 → ℕ) (d : ℕ) := Joint r d ⊕ (Slot r × Depth d)

def orient (c : Bool) (d k j : ℕ) : ℕ := if c=true ∧ k%2=1 then d-j else j

theorem orient_range (c : Bool) {d k j : ℕ} (lo : 0<j) (hi : j<d) :
    0<orient c d k j ∧ orient c d k j<d := by unfold orient; split <;> omega

theorem orient_twice (c : Bool) {d k j : ℕ} (lo : j≤d) :
    orient c d k (orient c d k j)=j := by unfold orient; split <;> omega

theorem actual_length (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i) (i : Fin 3) :
    M r d i+2=r i*d := by
  apply Nat.sub_add_cancel
  exact hd.trans (Nat.le_mul_of_pos_left _ (pos i))

def inside (r : Fin 3 → ℕ) (d : ℕ) (c : Bool) (s : Slot r) (j : ℕ) : V r d :=
  point (M r d) s.1 (s.2.val*d+orient c d s.2.val j)

theorem inside_bound (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (s : Slot r) {j : ℕ} (lo : 0<j) (hi : j<d) :
    0<s.2.val*d+j ∧ s.2.val*d+j<M r d s.1+2 := by
  rw [actual_length r hd pos]
  have lim := Nat.mul_le_mul_right d (show s.2.val+1 ≤ r s.1 from s.2.isLt)
  rw [Nat.add_mul,Nat.one_mul] at lim
  omega

theorem divmod {d k j : ℕ} (hd : 0<d) (hi : j<d) :
    (k*d+j)/d = k ∧ (k*d+j)%d = j := by
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ hd,Nat.div_eq_of_lt hi,Nat.zero_add]
  · rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hi]

def armTag {r : Fin 3 → ℕ} {d : ℕ} : V r d → Option (Fin 3)
  | .inl _ => none
  | .inr p => some p.1

def indexTag {r : Fin 3 → ℕ} {d : ℕ} : V r d → ℕ
  | .inl _ => 0
  | .inr p => p.2.val+1

private theorem inside_info (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (s : Slot r) (j : Depth d) :
    armTag (inside r d c s j.val)=some s.1 ∧
    indexTag (inside r d c s j.val)=s.2.val*d+orient c d s.2.val j.val ∧
    ∀ b, ¬Junction r d b (inside r d c s j.val) := by
  obtain ⟨l,h⟩ := orient_range c (k:=s.2.val) j.2.1 j.2.2
  have lim := inside_bound r hd pos s l h
  unfold inside
  rw [point_interior _ lim.1 lim.2]
  refine ⟨rfl,Nat.sub_add_cancel lim.1,?_⟩
  intro b hJ
  have rem := hJ.1
  change (s.2.val*d+orient c d s.2.val j.val-1+1)%d=0 at rem
  rw [Nat.sub_add_cancel lim.1,(divmod (k:=s.2.val) (by omega) h).2] at rem
  omega

def realize (r : Fin 3 → ℕ) (d : ℕ) (c : Bool) : Forms r d → V r d
  | .inl v => v.val
  | .inr (s,j) => inside r d c s j.val

private theorem inside_inj (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) {s t : Slot r} {j l : Depth d}
    (eq : inside r d c s j.val = inside r d c t l.val) : (s,j)=(t,l) := by
  obtain ⟨st,sn,_⟩ := inside_info r hd pos c s j
  obtain ⟨tt,tn,_⟩ := inside_info r hd pos c t l
  have arms := Option.some.inj (st.symm.trans ((congrArg armTag eq).trans tt))
  have coord := sn.symm.trans ((congrArg indexTag eq).trans tn)
  have lo := orient_range c (k:=s.2.val) j.2.1 j.2.2
  have lo' := orient_range c (k:=t.2.val) l.2.1 l.2.2
  have qr := divmod (k:=s.2.val) (by omega : 0<d) lo.2
  have qr' := divmod (k:=t.2.val) (by omega : 0<d) lo'.2
  have kk := qr.1.symm.trans ((congrArg (fun z : ℕ => z/d) coord).trans qr'.1)
  have ij := qr.2.symm.trans ((congrArg (fun z : ℕ => z%d) coord).trans qr'.2)
  have se : s=t := by
    obtain ⟨a,b⟩ := s
    obtain ⟨e,f⟩ := t
    change a=e at arms
    subst e
    exact congrArg (Sigma.mk a) (Fin.ext kk)
  subst t
  apply congrArg (fun q : Depth d => (s,q))
  apply Subtype.ext
  exact (orient_twice c j.2.2.le (k:=s.2.val)).symm.trans
    ((congrArg (orient c d s.2.val) ij).trans (orient_twice c l.2.2.le))

/-- Coordinates for every physical vertex as a junction or an oriented
internal point of exactly one segment. Surjectivity includes both poles. -/
noncomputable def chart (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) : Forms r d ≃ V r d := by
  classical
  apply Equiv.ofBijective (realize r d c)
  constructor
  · rintro (u|⟨s,j⟩) (v|⟨t,l⟩) eq
    · exact congrArg Sum.inl (Subtype.ext eq)
    · obtain ⟨b,h⟩ := u.2
      change u.val = inside r d c t l.val at eq
      exact False.elim ((inside_info r hd pos c t l).2.2 b (eq ▸ h))
    · obtain ⟨b,h⟩ := v.2
      change inside r d c s j.val=v.val at eq
      exact False.elim ((inside_info r hd pos c s j).2.2 b (eq.symm ▸ h))
    · exact congrArg Sum.inr (inside_inj r hd pos c eq)
  · rintro (b|⟨i,j⟩)
    · exact ⟨.inl ⟨pole _ b,b,rfl⟩,rfl⟩
    let z := j.val+1
    by_cases same : z%d=0
    · exact ⟨.inl ⟨inner _ i j,decide (z/d%2=1),same,rfl⟩,rfl⟩
    let b := z/d
    have lt : b<r i := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<d)).mpr
      rw [← actual_length r hd pos]
      dsimp [z]
      have := j.isLt
      omega
    let s : Slot r := ⟨i,⟨b,lt⟩⟩
    have rem := Nat.mod_lt z (show 0<d by omega)
    let dep : Depth d := ⟨orient c d b (z%d),orient_range c (by omega) rem⟩
    refine ⟨.inr (s,dep),?_⟩
    change point (M r d) i (b*d+orient c d b (orient c d b (z%d))) = _
    rw [orient_twice c rem.le,Nat.mul_comm b d]
    change point (M r d) i (d*(z/d)+z%d) = _
    rw [Nat.div_add_mod]
    exact point_inner _ _ _

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.chart
