import Bootstrap.ThetaTranslationGroup

namespace Bootstrap.Theta

open scoped Classical

noncomputable abbrev thetaClosure (m : Fin 3 → ℕ) := terminalGraph (graph m) (graph m)

theorem preserves_of_mem (m : Fin 3 → ℕ) {p : Equiv.Perm (Vertex m)} (hp : p∈reflectionGroup m)
    (x y : Vertex m) : (thetaClosure m).Adj (p x) (p y) ↔ (thetaClosure m).Adj x y :=
  reflectionGroup_terminal m hp x y

theorem intPt_zero (m : Fin 3 → ℕ) (i j : Fin 3) : intPt m i j 0=pole m false := by
  simpa using (intPt_first m i j 0 (Nat.zero_le _)).trans (armPt_zero m i)

theorem first_ident (m : Fin 3 → ℕ) (i : Fin 3) : armPt m i 1=inner m i 0 :=
  armPt_inner m i 0

theorem first_off (m : Fin 3 → ℕ) {i j t : Fin 3} (ti : t≠i) (tj : t≠j) :
    ¬OnCycle i j (armPt m t 1) := by
  rw [first_ident]
  exact fun h => h.elim ti tj

theorem pole_first (m : Fin 3 → ℕ) (i : Fin 3) : (thetaClosure m).Adj (armPt m i 1) (pole m false) := by
  rw [first_ident]
  exact initial_le_terminal (graph m) (graph m) (show (graph m).Adj (inner m i 0) (pole m false) from rfl)

theorem reflect_exchange (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) :
    reflection m ij false (armPt m j 1)=armPt m i 1 := by
  have fi := intPt_first m i j 1 (show 1≤armSize m i by dsimp [armSize];omega)
  have se := intPt_second m i j 1 (show 1≤armSize m j by dsimp [armSize];omega)
  rw [←se,false_reflect_int,neg_neg]
  exact fi

theorem reflect_fixes_short (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (ti : t≠i) (tj : t≠j)
    {d : ℕ} (dsmall : d<armSize m t) : reflection m ij false (armPt m t d)=armPt m t d := by
  by_cases zero : d=0
  · subst d; rw [armPt_zero,reflection_fixes_pole]
  · have hh : ¬OnCycle i j (armPt m t d) := by
      simp only [armPt,if_neg zero,dif_pos dsmall]
      exact fun h => h.elim ti tj
    exact reflection_off m ij false hh

/-- Translate the edge incident to the third arm's first vertex, then reflect
to the first arm while fixing the interior of the second arm. -/
theorem seed_multiple (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    {d : ℕ} (hd : d<armSize m j) (div : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ (d:ℤ)) :
    (thetaClosure m).Adj (armPt m i 1) (armPt m j d) := by
  have neg : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ -(d:ℤ) := by
    obtain ⟨u,hu⟩ := div
    exact ⟨-u,by rw [Int.mul_neg,←hu]⟩
  obtain ⟨p,hp,act,fix⟩ := translation_of_dvd m ij neg
  have dm := act 0
  rw [intPt_zero,zero_add,intPt_second m i j d hd.le] at dm
  have h := (preserves_of_mem m hp _ _).mpr (pole_first m t)
  rw [fix _ (first_off m it.symm jt.symm),dm] at h
  have h' := (preserves_of_mem m (reflection_mem m it false) _ _).mpr h
  rwa [reflect_exchange,reflect_fixes_short m it ij.symm jt hd] at h'

/-- Complete all signed translates of an available seed by the periods of
the second two-arm cycle, while fixing the first interior vertex of the first arm. -/
theorem seed_grid (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    {d : ℕ} (hd : d<armSize m j) (div : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ (d:ℤ))
    (z : ℤ) (cover : ((2*armSize m j).gcd (perimeter m j t):ℤ) ∣ z-(d:ℤ) ∨
                     ((2*armSize m j).gcd (perimeter m j t):ℤ) ∣ z+(d:ℤ)) :
    (thetaClosure m).Adj (armPt m i 1) (intPt m j t z) := by
  have h : (thetaClosure m).Adj (armPt m i 1) (intPt m j t (d:ℤ)) := by
    rw [intPt_first m j t d hd.le]
    exact seed_multiple m ij it jt hd div
  have off := first_off m ij it
  have advance (v : ℤ) (seed : (thetaClosure m).Adj (armPt m i 1) (intPt m j t v))
      (dh : ((2*armSize m j).gcd (perimeter m j t):ℤ) ∣ z-v) :
      (thetaClosure m).Adj (armPt m i 1) (intPt m j t z) := by
    obtain ⟨p,hp,act,fix⟩ := translation_of_dvd m jt dh
    have move := (preserves_of_mem m hp _ _).mpr seed
    rwa [fix _ off,act,show v+(z-v)=z by omega] at move
  rcases cover with plus|minus
  · exact advance _ h plus
  · have ref := (preserves_of_mem m (reflection_mem m jt false) _ _).mpr h
    rw [reflection_off m jt false off,false_reflect_int] at ref
    exact advance _ ref (by simpa using minus)

end Bootstrap.Theta

#print axioms Bootstrap.Theta.seed_multiple
#print axioms Bootstrap.Theta.seed_grid
