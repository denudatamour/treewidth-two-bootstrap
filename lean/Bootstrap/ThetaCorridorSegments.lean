import Bootstrap.ThetaCorridorChart
import Bootstrap.ThetaCorridorSpanning

namespace Bootstrap.Theta.Corridor

theorem inside_span (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (s : Slot r) {j : ℕ} (h₀ : 0<j) (h₁ : j<d) :
    0<s.2.val*d+j ∧ s.2.val*d+j<M r d s.1+2 := by
  rw [actual_length r hd pos]
  have cap := Nat.mul_le_mul_right d (show s.2.val+1 ≤ r s.1 from s.2.isLt)
  rw [Nat.add_mul,Nat.one_mul] at cap
  omega

theorem inside_not_joint (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (s : Slot r) (j : Depth d) (b : Bool) : ¬Junction r d b (inside r d c s j) :=
by
  intro same
  let u : Joint r d := ⟨_,b,same⟩
  have eq : chart r hd pos c (.inl u)=chart r hd pos c (.inr (s,j)) := rfl
  exact Sum.inl_ne_inr ((chart r hd pos c).injective eq)

@[simp] theorem chart_joint (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (u : Joint r d) : chart r hd pos c (.inl u) = u.val := rfl

@[simp] theorem chart_inside (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (s : Slot r) (j : Depth d) :
    chart r hd pos c (.inr (s,j)) = inside r d c s j := rfl

theorem chart_into (r : Fin 3 → ℕ) {d : ℕ} (c : Bool) (s : Slot r) (j : ℕ) (hj : j≤d) :
    point (M r d) s.1 (s.2.val*d+j) = inside r d c s (orient c d s.2.val j) := by
  unfold inside
  rw [orient_twice c hj]

def flipDepth (rev : Bool) (d j : ℕ) := if rev then d-j else j

private theorem raw_ports (r : Fin 3 → ℕ) {d : ℕ} (hd : 0<d) (i : Fin 3) (b j : ℕ)
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


theorem port_of_side (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (s : Slot r) (j : ℕ) (endSide : Bool)
    (atEnd : j=if endSide then d-1 else 1) :
    ∃ b, Port r d b (inside r d c s j) ∧ (c=true → b=endSide) := by
  have dep : 0<j ∧ j<d := by cases endSide <;> simp_all <;> omega
  obtain ⟨min,max⟩ := orient_range c (k:=s.2.val) dep.1 dep.2
  let z := orient c d s.2.val j
  have lim := inside_span r hd pos s min max
  have pa := raw_ports r (by omega : 0<d) s.1 s.2.val z min max lim.2
  let tag := decide (s.2.val%2=1)
  by_cases odd : s.2.val%2=1
  · cases c <;> cases endSide
    · exact ⟨true,by simpa [odd] using pa.1 (by simp_all [z,orient]),by simp⟩
    · exact ⟨false,by simpa [odd] using pa.2 (by simp_all [z,orient] <;> omega),by simp⟩
    · exact ⟨false,by simpa [odd] using pa.2 (by simp_all [z,orient] <;> omega),by simp⟩
    · exact ⟨true,by simpa [odd] using pa.1 (by simp_all [z,orient] <;> omega),by simp⟩
  · cases c <;> cases endSide
    · exact ⟨false,by simpa [odd] using pa.1 (by simp_all [z,orient]),by simp⟩
    · exact ⟨true,by simpa [odd] using pa.2 (by simp_all [z,orient] <;> omega),by simp⟩
    · exact ⟨false,by simpa [odd] using pa.1 (by simp_all [z,orient]),by simp⟩
    · exact ⟨true,by simpa [odd] using pa.2 (by simp_all [z,orient] <;> omega),by simp⟩

theorem point_junction_tag (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (col : c=true → ∀ i, (r i)%2=1) (i : Fin 3) (k : ℕ) (within : k≤r i) :
    ∃ b, Junction r d b (point (M r d) i (k*d)) ∧ (c=true → b=decide (k%2=1)) := by
  have lim : k*d ≤ M r d i+2 := by rw [actual_length r hd pos]; exact Nat.mul_le_mul_right _ within
  refine ⟨_,scaled_junction r (by omega) i k lim,?_⟩
  intro cc
  split
  · rename_i atRight
    rw [actual_length r hd pos] at atRight
    have eq : k=r i := Nat.eq_of_mul_eq_mul_right (by omega : 0<d) atRight
    simp [eq,col cc i]
  · rfl

end Bootstrap.Theta.Corridor

namespace Bootstrap.Theta.Corridor

private def sideDepth (d : ℕ) (e : Bool) := if e then d-1 else 1

private theorem side_range {d : ℕ} (hd : 2≤d) (e : Bool) :
    0<sideDepth d e ∧ sideDepth d e<d := by cases e <;> simp [sideDepth] <;> omega

private theorem side_image (c rev e : Bool) {d k : ℕ} (hd : 2≤d) (allowed : c=true → rev=false) :
    ∃ f : Bool, flipDepth rev d (orient c d k (sideDepth d e))=sideDepth d f ∧
      (c=true → f=decide ((k+(if e then 1 else 0))%2=1)) := by
  by_cases hk : k%2=1
  · have next : (k+1)%2=0 := by omega
    cases c <;> cases rev <;> cases e <;> simp_all [sideDepth,flipDepth,orient,Bool.exists_bool] <;> omega
  · have next : (k+1)%2=1 := by omega
    cases c <;> cases rev <;> cases e <;> simp_all [sideDepth,flipDepth,orient,Bool.exists_bool] <;> omega

private theorem flip_range (rev : Bool) {d j : ℕ} (h₀ : 0<j) (h₁ : j<d) :
    0 < flipDepth rev d j ∧ flipDepth rev d j < d := by cases rev <;> simp [flipDepth] <;> omega

private def Consecutive (i j : ℕ) : Prop := i+1=j ∨ j+1=i

private theorem flip_near (rev : Bool) {d j l : ℕ} (h₁ : j≤d) (h₂ : l≤d) (n : Consecutive j l) :
    Consecutive (flipDepth rev d j) (flipDepth rev d l) := by
  cases rev <;> unfold Consecutive flipDepth at * <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega

private theorem orient_near (c : Bool) {d b j l : ℕ} (h₁ : j≤d) (h₂ : l≤d) (n : Consecutive j l) :
    Consecutive (orient c d b j) (orient c d b l) := by
  unfold orient Consecutive at *
  split <;> omega

private theorem inside_near (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (s : Slot r) {j l : ℕ} (hj : 0<j ∧ j<d) (hl : 0<l ∧ l<d)
    (n : Consecutive j l) : (H r d).Adj (inside r d c s j) (inside r d c s l) := by
  have ja := orient_range c (k:=s.2.val) hj.1 hj.2
  have la := orient_range c (k:=s.2.val) hl.1 hl.2
  have jbound := (inside_span r hd pos s ja.1 ja.2).2
  have lbound := (inside_span r hd pos s la.1 la.2).2
  rcases orient_near c (b:=s.2.val) hj.2.le hl.2.le n with h|h
  · unfold inside
    rw [←h,←Nat.add_assoc]
    exact point_edge _ _ jbound
  · unfold inside
    rw [←h,←Nat.add_assoc]
    exact (H r d).symm (point_edge _ _ lbound)

/-- This criterion verifies permutations of complete segments and junctions
directly on the original theta edges. -/
theorem segment_symmetry (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c rev : Bool) (col : c=true → ∀ i, (r i)%2=1) (allowed : c=true → rev=false)
    (p : Equiv.Perm (V r d)) (move : Slot r → Slot r)
    (joints : ∀ x b, Junction r d b x → ∃ a, Junction r d a (p x) ∧ (c=true → a=b))
    (internals : ∀ s j, 0<j → j<d →
      p (inside r d c s j)=inside r d c (move s) (flipDepth rev d j))
    (inc : segmentGraph r d c ≤ F r d) :
    ∀ x y, (F r d).Adj (p x) (p y) ↔ (F r d).Adj x y := by
  let m := M r d
  have mapped (s : Slot r) (j : ℕ) (lo : 0<j) (hi : j<d) :
      p (point m s.1 (s.2.val*d+j)) = inside r d c (move s) (flipDepth rev d (orient c d s.2.val j)) := by
    rw [chart_into r c s j hi.le]
    exact internals _ _ (orient_range c lo hi).1 (orient_range c lo hi).2
  have ends (s : Slot r) (e : Bool) :
      (segmentGraph r d c).Adj (p (point m s.1 ((s.2.val+(if e then 1 else 0))*d)))
        (p (point m s.1 (s.2.val*d+sideDepth d e))) := by
    have lim : s.2.val+(if e then 1 else 0) ≤ r s.1 := by cases e <;> simp <;> have := s.2.isLt <;> omega
    obtain ⟨b,joint,cb⟩ := point_junction_tag r hd pos c col s.1 _ lim
    obtain ⟨a,moved,ca⟩ := joints _ _ joint
    have h := side_range hd e
    have o := orient_range c (k:=s.2.val) h.1 h.2
    have v := flip_range rev o.1 o.2
    obtain ⟨f,place,cf⟩ := side_image c rev e hd allowed (k:=s.2.val)
    obtain ⟨tag,req,agree⟩ := port_of_side r hd pos c (move s) _ f place
    rw [mapped s _ h.1 h.2]
    apply Or.inr
    refine ⟨?_,Or.inl ⟨a,tag,moved,req,fun ct => ?_⟩⟩
    · intro eq
      let j : Depth d := ⟨_,v⟩
      exact inside_not_joint r hd pos c (move s) j a (eq ▸ moved)
    · exact (ca ct).trans ((cb ct).trans ((cf ct).symm.trans (agree ct).symm))
  have along (i : Fin 3) (z : ℕ) (hz : z < m i+2) :
      (segmentGraph r d c).Adj (p (point m i z)) (p (point m i (z+1))) := by
    let k := z/d
    let j := z%d
    have jlim : j<d := Nat.mod_lt _ (by omega)
    have klim : k<r i := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      rwa [←actual_length r hd pos]
    let s : Slot r := ⟨i,⟨k,klim⟩⟩
    have coord : k*d+j=z := by dsimp [k,j]; rw [Nat.mul_comm,Nat.div_add_mod]
    by_cases zero : j=0
    · have step := ends s false
      change (segmentGraph r d c).Adj (p (point m i ((k+0)*d))) (p (point m i (k*d+1))) at step
      have val : k*d=z := by omega
      simpa only [Nat.add_zero,val] using step
    by_cases last : j+1=d
    · have step := (segmentGraph r d c).symm (ends s true)
      change (segmentGraph r d c).Adj (p (point m i (k*d+(d-1)))) (p (point m i ((k+1)*d))) at step
      have val : k*d+(d-1)=z := by omega
      have next : (k+1)*d=z+1 := by rw [Nat.add_mul,Nat.one_mul]; omega
      rwa [val,next] at step
    have ip : 0<j := by omega
    have jp : j+1<d := by omega
    have ih := orient_range c (k:=k) ip jlim
    have jh := orient_range c (k:=k) (Nat.zero_lt_succ j) jp
    have old : Consecutive j (j+1) := Or.inl rfl
    have nn := flip_near rev ih.2.le jh.2.le (orient_near c (b:=k) jlim.le jp.le old)
    have e := inside_near r hd pos c (move s) (flip_range rev ih.1 ih.2)
      (flip_range rev jh.1 jh.2) nn
    apply Or.inl
    have next : k*d+(j+1)=z+1 := by omega
    have lhs : p (point m i z) = inside r d c (move s) (flipDepth rev d (orient c d k j)) := by
      rw [←coord]; exact mapped s j ip jlim
    have rhs : p (point m i (z+1)) = inside r d c (move s) (flipDepth rev d (orient c d k (j+1))) := by
      rw [←next]; exact mapped s (j+1) (by omega) jp
    rw [lhs,rhs]
    exact e
  apply terminal_perm
  intro x y e
  obtain ⟨i,z,h,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := edge_coordinates m e
  · exact inc (along i z h)
  · exact (F r d).symm (inc (along i z h))

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.segment_symmetry