import Bootstrap.PrimitiveOrbitReduction
import Bootstrap.ThetaPrimitiveSeeds
import Bootstrap.ThetaCoprimeClosure


namespace Bootstrap.Theta

open Contraction

def Primitive (m : Fin 3 → Nat) : Prop :=
  (armSize m 0).gcd ((armSize m 1).gcd (armSize m 2)) = 1

def MixedParity (m : Fin 3 → Nat) : Prop :=
  ∃ i j, armSize m i % 2 ≠ armSize m j % 2

def NoCoprimePair (m : Fin 3 → Nat) : Prop :=
  ∀ i j, i ≠ j → ¬(armSize m i).Coprime (armSize m j)

theorem primitive_reorder (m : Fin 3 → Nat) (prim : Primitive m) {i j t : Fin 3}
    (ij : i ≠ j) (it : i ≠ t) (jt : j ≠ t) :
    (armSize m i).gcd ((armSize m j).gcd (armSize m t)) = 1 := by
  let g := (armSize m i).gcd ((armSize m j).gcd (armSize m t))
  have all (v : Fin 3) : g ∣ armSize m v := by
    by_cases e : v = i
    · subst v
      exact Nat.gcd_dvd_left _ _
    by_cases e' : v = j
    · subst v
      exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    · have at' := third_of_ne ij it jt v e e'
      subst v
      exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  apply Nat.eq_one_of_dvd_one
  have d := Nat.dvd_gcd (all 0) (Nat.dvd_gcd (all 1) (all 2))
  change (armSize m 0).gcd ((armSize m 1).gcd (armSize m 2)) = 1 at prim
  rwa [prim] at d

theorem third_arm {i j : Fin 3} (ij : i ≠ j) : ∃ t : Fin 3, i ≠ t ∧ j ≠ t := by
  classical
  by_contra! no
  have full : ({i,j} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    by_cases h : i = t
    · simp [h]
    · have h' := no t h
      simp [h']
  have e := congrArg Finset.card full
  simp [ij] at e

private theorem divisors_large (m : Fin 3 → Nat) (no : NoCoprimePair m)
    {i j : Fin 3} (ij : i ≠ j) : 1 < (armSize m i).gcd (armSize m j) := by
  have p := Nat.gcd_pos_of_pos_left (armSize m j) (show 0 < armSize m i by simp [armSize])
  have h := no i j ij
  change (armSize m i).gcd (armSize m j) ≠ 1 at h
  omega

theorem mixed_arms (m : Fin 3 → Nat) (mixed : MixedParity m) :
    ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      armSize m a % 2 ≠ armSize m c % 2 ∧ armSize m b % 2 ≠ armSize m c % 2 := by
  obtain ⟨i,j,diff⟩ := mixed
  have ij : i ≠ j := by rintro rfl;exact diff rfl
  obtain ⟨t,it,jt⟩ := third_arm ij
  by_cases h : armSize m t % 2 = armSize m i % 2
  · exact ⟨i,t,j,it,ij,jt.symm,diff,fun e => diff (h.symm.trans e)⟩
  · exact ⟨j,t,i,jt,ij.symm,it.symm,diff.symm,h⟩

private theorem all_odd_pole (m : Fin 3 → ℕ) {i j t : Fin 3}
    (ij : i≠j) (it : i≠t) (jt : j≠t) (ord : armSize m i≤armSize m j)
    (cop : (armSize m i).Coprime (armSize m j)) (odd : ∀ a,armSize m a%2=1)
    (v : Vertex m) (col : naturalColor m 1 v=true) : (thetaClosure m).Adj (pole m false) v := by
  have two := pair_eq_two _ _ cop (odd i) (odd j)
  change (2*armSize m i).gcd (perimeter m i j)=2 at two
  have even' : perimeter m i j%2=0 := by have := odd i;have := odd j;dsimp [perimeter];omega
  by_cases on' : OnCycle i j v
  · let z := vertexCoord m i j v
    have rep : cyclePt m i j z=v := pt_coord m ij v on'
    have typed : natPoint m i j z.val=v := (congrArg (cyclePt m i j) (indexZ_val _ z)).trans rep
    have colour := color_natPoint m i j odd z.val z.isLt
    rw [typed,col] at colour
    have parity : z.val%2=1 := of_decide_eq_true colour.symm
    rw [←typed,←intPt_zero m i j]
    exact cycle_parity_int m ij it jt ord two even' (by omega)
  rcases v with b|⟨u,w⟩
  · exact False.elim (on' trivial)
  have eq := third_of_ne ij it jt u (fun e => on' (Or.inl e)) (fun e => on' (Or.inr e))
  subst u
  have oddW : (w.val+1)%2=1 := of_decide_eq_true col
  obtain ⟨k,hk,pt⟩ := right_even_depth m (odd j)
  let g := (2*armSize m i).gcd (perimeter m i t)
  have dv : 2∣g := Nat.dvd_gcd (dvd_mul_right _ _) (by
    have := odd i;have := odd t;dsimp [perimeter];omega)
  have ge : g%2=0 := Nat.dvd_iff_mod_eq_zero.mp dv
  have gs : g≤2*armSize m i := Nat.le_of_dvd (by simp [armSize]) (Nat.gcd_dvd_left _ _)
  have e := opposite_interval m ij it jt ord two even' k (-((w.val+1:ℕ):ℤ))
    (Or.inr ⟨ge,gs,by omega⟩)
  rw [intPt_second m i t _ (by have := w.isLt;dsimp [armSize];omega),armPt_inner] at e
  exact outside_to_pole m ij it jt two w (pt ▸ e)

/-- An odd coprime pair fills the natural bipartite self-closure. -/
theorem coprime_all_odd (m : Fin 3 → ℕ) {i j t : Fin 3}
    (ij : i≠j) (it : i≠t) (jt : j≠t) (ord : armSize m i≤armSize m j)
    (cop : (armSize m i).Coprime (armSize m j)) (odd : ∀ a,armSize m a%2=1) :
    thetaClosure m = completeBetween (naturalColor m 1) := by
  apply le_antisymm (terminal_le_natural m (by decide) 1 odd)
  have prim := (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left (armSize m j) (armSize m t)) cop).gcd_eq_one
  have cross (x y : Vertex m) (hx : naturalColor m 1 x=false) (hy : naturalColor m 1 y=true) :
      (thetaClosure m).Adj x y := by
    obtain ⟨p,hp,px⟩ := primitive_color_transitive m ij it jt prim odd (pole m false) x hx.symm
    have inv := (reflectionGroup m).inv_mem hp
    have hv : naturalColor m 1 (p⁻¹ y)=true := (group_preserves_color m 1 odd inv y).trans hy
    have h := (preserves_of_mem m hp _ _).mpr (all_odd_pole m ij it jt ord cop odd _ hv)
    rwa [px,Equiv.Perm.apply_inv_self] at h
  intro x y adj
  change naturalColor m 1 x ≠ naturalColor m 1 y at adj
  cases hx : naturalColor m 1 x <;> cases hy : naturalColor m 1 y
  · exact False.elim (adj (hx.trans hy.symm))
  · exact cross x y hx hy
  · exact (thetaClosure m).symm (cross y x hy hx)
  · exact False.elim (adj (hx.trans hy.symm))

private theorem ordered_coprime_pair (m : Fin 3 → ℕ) (existsPair : ¬ NoCoprimePair m) :
    ∃ i j t : Fin 3, i≠j ∧ i≠t ∧ j≠t ∧ armSize m i≤armSize m j ∧ (armSize m i).Coprime (armSize m j) := by
  classical
  unfold NoCoprimePair at existsPair
  push_neg at existsPair
  obtain ⟨i,j,ij,cop⟩ := existsPair
  obtain ⟨t,it,jt⟩ := third_arm ij
  rcases le_total (armSize m i) (armSize m j) with h|h
  · exact ⟨i,j,t,ij,it,jt,h,cop⟩
  · exact ⟨j,i,t,ij.symm,jt,it,h,cop.symm⟩

theorem primitive_mixed_closure (m : Fin 3 → ℕ) (prim : Primitive m) (mixed : MixedParity m) :
    thetaClosure m=⊤ := by
  classical
  by_cases no : NoCoprimePair m
  · obtain ⟨a,b,c,ab,ac,bc,pa,pb⟩ := mixed_arms m mixed
    have p := primitive_reorder m prim ab ac bc
    exact primitive_mixed_after_seed m ab ac bc p (divisors_large m no ab) (divisors_large m no ac)
      pa pb (primitive_seed_mixed m ab ac bc p pb)
  obtain ⟨i,j,t,ij,it,jt,ord,cop⟩ := ordered_coprime_pair m no
  by_cases diff : armSize m i%2 ≠ armSize m j%2
  · exact coprime_opposite_complete m ij it jt ord cop diff
  have oi : armSize m i%2=1 := by
    by_contra h
    have dvd : 2∣(armSize m i).gcd (armSize m j) := Nat.dvd_gcd (by omega) (by omega)
    rw [cop.gcd_eq_one] at dvd
    omega
  have oj : armSize m j%2=1 := by omega
  have et : armSize m t%2=0 := by
    by_contra bad
    have all (v : Fin 3) : armSize m v%2=1 := by
      by_cases a : v=i
      · exact a ▸ oi
      by_cases b : v=j
      · exact b ▸ oj
      have vt := third_of_ne ij it jt v a b
      rw [vt];omega
    obtain ⟨x,y,ne⟩ := mixed
    exact ne ((all x).trans (all y).symm)
  exact coprime_odd_complete m ij it jt ord cop oi oj et

theorem primitive_odd_closure (m : Fin 3 → ℕ) (prim : Primitive m) (odd : ∀ i,armSize m i%2=1) :
    thetaClosure m=completeBetween (naturalColor m 1) := by
  classical
  by_cases no : NoCoprimePair m
  · have more (a b c : Fin 3) (ab : a≠b) (ac : a≠c) (bc : b≠c) (h : armSize m c<armSize m b) :
        thetaClosure m=completeBetween (naturalColor m 1) := by
      have p := primitive_reorder m prim ab ac bc
      exact primitive_odd_after_seed m ab ac bc p (divisors_large m no ab) (divisors_large m no ac)
        (divisors_large m no bc) h odd (primitive_seed_odd m ab ac bc p (odd a) (odd b) (odd c))
    have ne : armSize m 1≠armSize m 2 := by
      intro e
      have p := primitive_reorder m prim (show (0:Fin 3)≠1 by decide) (show (0:Fin 3)≠2 by decide) (by decide)
      rw [←e,Nat.gcd_self] at p
      exact no 0 1 (by decide) p
    rcases lt_or_gt_of_ne ne with h|h
    · exact more 0 2 1 (by decide) (by decide) (by decide) h
    · exact more 0 1 2 (by decide) (by decide) (by decide) h
  obtain ⟨i,j,t,ij,it,jt,ord,cop⟩ := ordered_coprime_pair m no
  exact coprime_all_odd m ij it jt ord cop odd

end Bootstrap.Theta

#print axioms Bootstrap.Theta.coprime_all_odd
#print axioms Bootstrap.Theta.primitive_mixed_closure
#print axioms Bootstrap.Theta.primitive_odd_closure
