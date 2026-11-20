import Bootstrap.ThetaCorridorTwist

namespace Bootstrap.Theta.Corridor

private def coordinate {k : ℕ} (m : Fin k → ℕ) (i : Fin k) : Vertex m → ℕ
  | .inl false => 0
  | .inl true => m i+2
  | .inr ⟨_,j⟩ => j.val+1

private theorem recover_coordinate {k : ℕ} (m : Fin k → ℕ) (i : Fin k) {z : ℕ}
    (h : z ≤ m i+2) : coordinate m i (point m i z) = z := by
  by_cases zero : z=0
  · subst z
    rfl
  by_cases last : z=m i+2
  · subst z
    rw [point_end]
    rfl
  rw [point_interior m (by omega) (by omega : z<m i+2)]
  change z-1+1=z
  omega

theorem point_ne_of_depth_ne {k : ℕ} (m : Fin k → ℕ) (i : Fin k) {a b : ℕ}
    (ha : a ≤ m i+2) (hb : b ≤ m i+2) (ne : a ≠ b) : point m i a ≠ point m i b := by
  intro eq
  exact ne ((recover_coordinate m i ha).symm.trans ((congrArg (coordinate m i) eq).trans
    (recover_coordinate m i hb)))

theorem scaled_junction (r : Fin 3 → ℕ) {d : ℕ} (hd : 0<d) (i : Fin 3) (b : ℕ)
    (bound : b*d ≤ M r d i+2) :
    Junction r d (if b*d=M r d i+2 then true else decide (b%2=1)) (point (M r d) i (b*d)) := by
  by_cases last : b*d=M r d i+2
  · rw [if_pos last,last,point_end]
    rfl
  rw [if_neg last]
  by_cases zero : b=0
  · subst b
    simp only [Nat.zero_mul,point_zero]
    rfl
  have pos : 0<b*d := Nat.mul_pos (by omega) hd
  rw [point_interior _ pos (by omega)]
  change (b*d-1+1)%d=0 ∧ decide (b%2=1)=decide (((b*d-1+1)/d)%2=1)
  rw [Nat.sub_add_cancel pos,Nat.mul_mod_left,Nat.mul_div_cancel _ hd]
  exact ⟨rfl,rfl⟩

private theorem at_port (r : Fin 3 → ℕ) {d : ℕ} (hd : 0<d) (i : Fin 3) (b j : ℕ)
    (pos : 0<j) (low : j<d) (within : b*d+j<M r d i+2) :
    (j=1 → Port r d (decide (b%2=1)) (point (M r d) i (b*d+j))) ∧
      (j+1=d → Port r d (!(decide (b%2=1))) (point (M r d) i (b*d+j))) := by
  have high : 0<b*d+j := by omega
  rw [point_interior _ high within]
  have rem : (b*d+j)%d=j := by rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt low]
  have quo : (b*d+j)/d=b := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hd,Nat.div_eq_of_lt low,Nat.zero_add]
  constructor
  · intro hj
    apply Or.inl
    change (b*d+j-1+1)%d=1 ∧ decide (b%2=1)=decide (((b*d+j-1+1)/d)%2=1)
    rw [Nat.sub_add_cancel high,rem,quo,hj]
    exact ⟨rfl,rfl⟩
  · intro hj
    apply Or.inr
    change (b*d+j-1+1)%d+1=d ∧ (!(decide (b%2=1)))=(!(decide (((b*d+j-1+1)/d)%2=1)))
    rw [Nat.sub_add_cancel high,rem,quo,hj]
    exact ⟨rfl,rfl⟩

private theorem raw_neighbours (c : Bool) {d z : ℕ} (hd : 3 ≤ d) (away : z ≠ d-2) :
    let a := twistIndex c d z
    let b := twistIndex c d (z+1)
    (a+1=b ∨ b+1=a) ∨
      (c=false ∧ a=0 ∧ b=2*d-1) ∨
      (c=false ∧ a=d+1 ∧ b=2*d) ∨
      (c=true ∧ a=3*d-1 ∧ b=d) ∨
      (c=true ∧ a=d-1 ∧ b=3*d) := by
  dsimp only
  cases c <;> simp only [twistIndex,Bool.false_eq_true,if_false,if_true,Bool.true_eq_false,
    false_and,true_and,false_or,or_false] <;> split_ifs <;> omega

private theorem twist_le (c : Bool) {d z L : ℕ} (hd : 3≤d) (room : span c d≤L) (hz : z≤L) :
    twistIndex c d z ≤ L := by
  cases c <;> simp only [span,twistIndex,Bool.false_eq_true,if_false,if_true] at room ⊢ <;>
    split_ifs <;> omega

end Bootstrap.Theta.Corridor

namespace Bootstrap.Theta.Corridor

private theorem mapped_step (r : Fin 3 → ℕ) (arm : Fin 3) (c : Bool) (d : ℕ)
    (hd : 3≤d) (room : span c d ≤ M r d arm+2) {z : ℕ} (hz : z < M r d arm+2)
    (away : z ≠ d-2) : (segmentGraph r d c).Adj
      (point (M r d) arm (twistIndex c d z)) (point (M r d) arm (twistIndex c d (z+1))) := by
  let m := M r d
  let L := m arm+2
  let pt := point m arm
  have leftBound : twistIndex c d z ≤ m arm+2 := twist_le c hd room hz.le
  have rightBound : twistIndex c d (z+1) ≤ m arm+2 := twist_le c hd room (show z+1 ≤ M r d arm+2 by omega)
  have join (x y : ℕ) (cx cy : Bool) (bx : x≤L) (by' : y≤L) (ne : x ≠ y)
      (jx : Junction r d cx (pt x)) (py : Port r d cy (pt y)) (tag : c=true → cx=cy) :
      (segmentGraph r d c).Adj (pt x) (pt y) :=
    Or.inr ⟨point_ne_of_depth_ne m arm bx by' ne,Or.inl ⟨cx,cy,jx,py,tag⟩⟩
  rcases raw_neighbours c hd away with (near|near)|⟨cc,e₁,e₂⟩|⟨cc,e₁,e₂⟩|⟨cc,e₁,e₂⟩|⟨cc,e₁,e₂⟩
  · exact Or.inl (near ▸ point_edge m arm (by omega))
  · exact Or.inl ((H r d).symm (near ▸ point_edge m arm (by omega)))
  · subst c
    change 2*d ≤ L at room
    rw [e₁,e₂]
    have p := (at_port r (by omega : 0<d) arm 1 (d-1) (by omega) (by omega) (by dsimp [L,m] at room; omega)).2 (by omega)
    rw [show 1*d+(d-1)=2*d-1 by omega] at p
    exact join 0 _ false false (by omega) (by omega) (by omega) rfl p (by simp)
  · subst c
    change 2*d ≤ L at room
    rw [e₁,e₂]
    have p := (at_port r (by omega : 0<d) arm 1 1 (by omega) (by omega) (by dsimp [L,m] at room; omega)).1 rfl
    rw [Nat.one_mul] at p
    apply (segmentGraph r d false).symm
    exact join _ _ _ true room (by omega) (by omega) (scaled_junction r (by omega) arm 2 room) p (by simp)
  · subst c
    change 3*d ≤ L at room
    rw [e₁,e₂]
    have p := (at_port r (by omega : 0<d) arm 2 (d-1) (by omega) (by omega) (by dsimp [L,m] at room; omega)).2 (by omega)
    rw [show 2*d+(d-1)=3*d-1 by omega] at p
    have j := scaled_junction r (by omega : 0<d) arm 1 (by dsimp [L,m] at room; omega)
    simp only [Nat.one_mul] at j
    have j' : Junction r d true (pt d) := by simpa using j
    exact (segmentGraph r d true).symm (join _ _ true true (by omega) (by omega) (by omega) j' p (by simp))
  · subst c
    change 3*d ≤ L at room
    rw [e₁,e₂]
    have p := (at_port r (by omega : 0<d) arm 0 (d-1) (by omega) (by omega) (by dsimp [L,m] at room; omega)).2 (by omega)
    simp only [Nat.zero_mul,Nat.zero_add] at p
    have j := scaled_junction r (by omega : 0<d) arm 3 room
    have j' : Junction r d true (pt (3*d)) := by simpa using j
    exact (segmentGraph r d true).symm (join _ _ true true room (by omega) (by omega) j' p (by simp))

/-- The full permuted theta requires exactly one candidate edge beyond the
segment graph. Completing that edge in the terminal graph makes the actual
permutation an automorphism of the terminal graph. -/
theorem twist_preserves (r : Fin 3 → ℕ) (arm : Fin 3) (c : Bool) (d : ℕ)
    (hd : 3≤d) (room : span c d ≤ M r d arm+2) (inc : segmentGraph r d c ≤ F r d) :
    let p := twist (M r d) arm c d hd room
    ∀ x y, (F r d).Adj (p x) (p y) ↔ (F r d).Adj x y := by
  let m := M r d
  let p := twist m arm c d hd room
  let u := point m arm (d-2)
  let v := point m arm (d-2+1)
  have room2 : 2*d ≤ m arm+2 := by cases c <;> simp [span] at room <;> dsimp [m] <;> omega
  have exceptional : (H r d).Adj u v := point_edge m arm (by omega)
  apply terminal_near_perm (H r d) p exceptional
  intro x y edge missed
  have forward (i : Fin 3) (z : ℕ) (hz : z < m i+2)
      (guard : ¬(point m i z=u ∧ point m i (z+1)=v)) :
      (segmentGraph r d c).Adj (p (point m i z)) (p (point m i (z+1))) := by
    dsimp only [p]
    rw [twist_point _ _ _ _ _ _ _ _ hz.le,twist_point _ _ _ _ _ _ _ _ hz]
    by_cases ia : i=arm
    · subst i
      simp only [if_pos rfl]
      apply mapped_step r arm c d hd room hz
      rintro rfl
      exact guard ⟨rfl,rfl⟩
    · simp only [if_neg ia]
      exact Or.inl (point_edge m i hz)
  obtain ⟨i,z,hz,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := edge_coordinates m edge
  · exact inc (forward i z hz (fun h => missed (Or.inl h)))
  · exact inc ((segmentGraph r d c).symm (forward i z hz (fun h => missed (Or.inr ⟨h.2,h.1⟩))))

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.twist_preserves
