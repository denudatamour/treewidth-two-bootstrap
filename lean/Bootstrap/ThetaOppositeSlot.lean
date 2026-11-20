import Bootstrap.ThetaSlotReflections

namespace Bootstrap.Theta.Corridor

/-- On a cycle with an odd number of segments, reflection about its left pole
fixes the opposite segment and exchanges its two actual ports. -/
theorem opposite_slot_swap (r : Fin 3 → ℕ) {d : ℕ} (hd : 2≤d) (pos : ∀ i,0<r i)
    (mix : ∃ i j, r i%2 ≠ r j%2) :
    ∃ s : Slot r, ∃ p : Equiv.Perm (V r d), p∈reflectionGroup (M r d) ∧
      p (pole (M r d) false)=pole (M r d) false ∧
      p (inside r d false s 1)=inside r d false s (d-1) ∧
      p (inside r d false s (d-1))=inside r d false s 1 := by
  obtain ⟨i,j,opp⟩ := mix
  have ij : i≠j := fun h => opp (h ▸ rfl)
  let n := r i+r j
  let K : ℤ := ((n/2 : ℕ) : ℤ)
  have mid : (n:ℤ)=2*K+1 := by dsimp [n,K] at *; omega
  let m := M r d
  let p := reflection m ij false
  let X (t : ℕ) := intPt m i j (K*(d:ℤ)+t)
  have per : (perimeter m i j : ℤ)=(2*K+1)*d := by
    rw [scaled_perimeter r hd pos,Nat.cast_mul]
    exact congrArg (fun z : ℤ => z*(d:ℤ)) mid
  have swaps (t : ℕ) (lo : t≤d) : p (X t)=X (d-t) := by
    dsimp only [p,X]
    rw [false_reflect_int]
    have eq : -(K*(d:ℤ)+t)+perimeter m i j=K*(d:ℤ)+↑(d-t) := by
      rw [per,Nat.cast_sub lo]
      ring
    rw [←eq,intPt_period]
  obtain ⟨s,rev,chart⟩ := cycle_slot r hd pos ij K
  refine ⟨s,p,reflection_mem m ij false,reflection_fixes_pole m ij false,?_⟩
  have low := chart 1 (by decide) (by omega)
  have far := chart (d-1) (by omega) (by omega)
  change X 1=_ at low
  change X (d-1)=_ at far
  have h1 := swaps 1 (by omega)
  have h2 := swaps (d-1) (by omega)
  have cancel : d-(d-1)=1 := by omega
  rw [cancel] at h2
  rw [low,far] at h1
  rw [low,far] at h2
  cases rev <;> simp only [Bool.false_eq_true,if_false,if_true,cancel] at h1 h2
  · exact ⟨h1,h2⟩
  · exact ⟨h2,h1⟩

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.opposite_slot_swap
