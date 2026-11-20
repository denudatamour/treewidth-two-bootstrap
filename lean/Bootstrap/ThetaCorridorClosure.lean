import Bootstrap.ThetaCorridorStars
import Bootstrap.ThetaCorridorScaleTwo

namespace Bootstrap.Theta.Corridor

private theorem complete_of_stars (m : Fin 3 → ℕ) (d : ℕ)
    (same : ∀ i, (m i+2)%2=d%2)
    (stars : ∀ x, naturalColor m d x=false →
      Exchange (terminalGraph (graph m) (graph m)) (pole m false) x) :
    terminalGraph (graph m) (graph m) = completeBetween (naturalColor m d) := by
  let G := terminalGraph (graph m) (graph m)
  apply le_antisymm (terminal_le_natural m (by decide) d same)
  have cross (x y : Vertex m) (hx : naturalColor m d x=false) (hy : naturalColor m d y=true) :
      G.Adj x y := by
    obtain ⟨a,_,ya,_,_⟩ := Suppression.two_neighbors (twoConnected m (by decide)) y
    have opp := natural_proper m d same ya
    change naturalColor m d y ≠ naturalColor m d a at opp
    rw [hy] at opp
    have ca : naturalColor m d a=false := by cases h : naturalColor m d a <;> simp_all
    apply Exchange.neighbour ((stars a ca).symm.trans (stars x hx)) (initial_le_terminal _ _ ya.symm)
    exact fun eq => Bool.false_ne_true (hx.symm.trans (eq ▸ hy))
  intro x y e
  change naturalColor m d x ≠ naturalColor m d y at e
  cases hx : naturalColor m d x <;> cases hy : naturalColor m d y
  · exact False.elim (e (hx.trans hy.symm))
  · exact cross x y hx hy
  · exact (cross y x hy hx).symm
  · exact False.elim (e (hx.trans hy.symm))

private theorem interior_color (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (bip : c=true ∨ d%2=0) (s : Slot r) (j : Depth d) :
    naturalColor (M r d) d (inside r d c s j)=decide (j.val%2=1) := by
  have h := orient_range c (k:=s.2.val) j.2.1 j.2.2
  have z := inside_bound r hd pos s h.1 h.2
  unfold inside
  rw [point_interior _ z.1 z.2]
  change decide ((s.2.val*d+orient c d s.2.val j.val-1+1)%2=1)=_
  rw [Nat.sub_add_cancel z.1,Nat.add_mod,Nat.mul_mod]
  have lo := j.2.1
  have hi := j.2.2
  by_cases sk : s.2.val%2=1
  · cases c
    · have de : d%2=0 := bip.resolve_left (by decide)
      simp [orient,de]
    · simp [orient,sk]
      omega
  · have zero : s.2.val%2=0 := by omega
    simp [orient,sk,zero]

private theorem even_of_right_joint (r : Fin 3 → ℕ) {d : ℕ} {x : V r d}
    (j : Junction r d true x) (h : naturalColor (M r d) d x=false) : d%2=0 := by
  rcases x with b|⟨i,k⟩
  · change true=b at j
    subst b
    have bad : ¬d%2=1 := of_decide_eq_false h
    omega
  · obtain ⟨rem,tag⟩ := j
    have parity := of_decide_eq_true tag.symm
    have col : ¬(k.val+1)%2=1 := of_decide_eq_false h
    have eq := Nat.div_add_mod (k.val+1) d
    rw [rem,Nat.add_zero] at eq
    have e := congrArg (fun n : ℕ => n%2) eq
    change (d*((k.val+1)/d))%2=(k.val+1)%2 at e
    rw [Nat.mul_mod,parity,Nat.mul_one,Nat.mod_mod] at e
    omega

theorem bipartite_of_segment (r : Fin 3 → ℕ) {d : ℕ} (hd : 3≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (col : c=true → ∀ i, r i%2=1) (bip : c=true ∨ d%2=0)
    (inc : segmentGraph r d c ≤ F r d) (arm : Fin 3) (room : (if c then 3 else 2)≤r arm) :
    F r d = completeBetween (naturalColor (M r d) d) := by
  let m := M r d
  have same (i : Fin 3) : (m i+2)%2=d%2 := by
    rw [actual_length r (by omega) pos,Nat.mul_mod]
    rcases bip with ct|de
    · rw [col ct i,Nat.one_mul,Nat.mod_mod]
    · simp [de]
  apply complete_of_stars m d same
  intro x hx
  obtain ⟨v,rfl⟩ := (chart r (show 2≤d by omega) pos c).surjective x
  rcases v with u|⟨s,j⟩
  · obtain ⟨b,h⟩ := u.2
    by_cases exactTag : c=true → false=b
    · exact junction_exchange r (by omega) pos c col inc (show Junction r d false (pole m false) from rfl) h exactTag
    · cases c <;> cases b <;> simp at exactTag
      have even := even_of_right_joint r h hx
      exact (colored_poles_exchange r hd pos (col rfl) inc arm room even).trans
        (junction_exchange r (by omega) pos true col inc (show Junction r d true (pole m true) from rfl) h (fun _ => rfl))
  · change naturalColor m d (inside r d c s j)=false at hx
    rw [interior_color r (by omega) pos c bip s j] at hx
    have parity := of_decide_eq_false hx
    exact even_depth_exchange r hd pos c col inc arm room j j.2.1 j.2.2 (by omega) s

theorem nonbipartite_of_segment (r : Fin 3 → ℕ) {d : ℕ} (hd : 3≤d) (pos : ∀ i, 0<r i)
    (odd : d%2=1) (inc : segmentGraph r d false ≤ F r d) (arm : Fin 3) (room : 2≤r arm) :
    F r d = ⊤ := by
  let m := M r d
  let u := pole m false
  have ju : Junction r d false u := rfl
  have edge := initial_le_terminal (H r d) (H r d) (point_edge m arm (z:=0) (by omega))
  apply Exchange.all_pairs u _ edge
  intro x
  obtain ⟨v,rfl⟩ := (chart r (show 2≤d by omega) pos false).surjective x
  rcases v with a|⟨s,j⟩
  · obtain ⟨b,h⟩ := a.2
    exact junction_exchange r (by omega) pos false (by simp) inc ju h (by simp)
  · change Exchange (F r d) u (inside r d false s j)
    have lo := j.2.1
    have hi := j.2.2
    by_cases par : j.val%2=0
    · exact even_depth_exchange r hd pos false (by simp) inc arm room j lo hi par s
    · have old := even_depth_exchange r hd pos false (by simp) inc arm room (d-j.val) (by omega) (by omega)
          (by omega) s
      have next := transfer_depth r (by omega) pos false true (by simp) (by simp) inc ju s s
        (by omega) (by omega) old
      simpa only [flipDepth,if_true,Nat.sub_sub_self hi.le] using next

end Bootstrap.Theta.Corridor

namespace Bootstrap.Theta.Corridor

/-- All nonprimitive scales from the inclusion of the actual segment graph. -/
theorem self_closure_of_segment (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i, 0<r i)
    (c : Bool) (col : c=true → ∀ i, r i%2=1) (inc : segmentGraph r d c ≤ F r d)
    (long : ∃ i, 1<r i) :
    F r d = if c=true ∨ d%2=0 then completeBetween (naturalColor (M r d) d) else ⊤ := by
  by_cases two : d=2
  · subst d
    simpa using scale_two_complete r pos c inc
  obtain ⟨arm,h⟩ := long
  have room : (if c then 3 else 2) ≤ r arm := by
    cases c
    · exact h
    · have := col rfl arm
      simp
      omega
  by_cases bip : c=true ∨ d%2=0
  · rw [if_pos bip]
    exact bipartite_of_segment r (by omega) pos c col bip inc arm room
  · rw [if_neg bip]
    have cf : c=false := by cases c <;> simp_all
    subst c
    exact nonbipartite_of_segment r (by omega) pos (by omega) inc arm h

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.bipartite_of_segment
#print axioms Bootstrap.Theta.Corridor.nonbipartite_of_segment
#print axioms Bootstrap.Theta.Corridor.self_closure_of_segment
