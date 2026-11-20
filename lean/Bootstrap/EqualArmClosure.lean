import Bootstrap.EqualArmWitness
import Bootstrap.TerminalSymmetry

namespace Bootstrap.Theta.EqualArms

variable {m : Nat}

private theorem first_reverse (m : Nat) (b : Bool) (i : Fin 3) :
    oriented m (!b) i 1 = oriented m b i (L m-1) := by
  have e := oriented_reverse m b i (L m-1) (Nat.sub_le ..)
  rwa [show L m -(L m-1) = 1 by unfold L;omega] at e

private theorem label_inj {f : V m ↪ V m} {b c : Bool} (a : Fin 3 → Fin 3)
    (h : ∀ i, f (oriented m b i 1) = oriented m c (a i) 1) : Function.Injective a := by
  intro i j eq
  apply oriented_arm_inj m b (by decide : 0 < 1) (by unfold L;omega)
  exact f.injective ((h i).trans ((congrArg (fun q => oriented m c q 1) eq).trans (h j).symm))

/-- The missing edge of a near-copy already exists in the equal-arm host. -/
theorem gap_adj {f : V m ↪ V m} {d : Fin 3} {g : Nat} (hg : g < L m) (good : Good f d g) :
    (H m).Adj (f (point m d g)) (f (point m d (g+1))) := by
  classical
  obtain ⟨c,left,right⟩ := poles hg good
  let r := L m-(g+1)
  have rb : r ≤ L m := Nat.sub_le ..
  have gapr : gap m true g = r := by change L m - 1 - g = L m-(g+1); omega
  have lp (t : Nat) (ht : t < g) :=
    good.direction hg false d t (by omega) (Or.inr (Nat.ne_of_lt ht))
  have rp (t : Nat) (ht : t < r) :=
    good.direction hg true d t (by omega) (Or.inr (by rw [gapr]; omega))
  have endpos {a : Fin 3} (eq : f (oriented m true d r) = oriented m (!c) a r) :
      f (point m d (g+1)) = oriented m c a (g+1) := by
    have es := oriented_reverse m false d (g+1) (by omega)
    have et := oriented_reverse m c a (g+1) (by omega)
    exact (congrArg f es).symm.trans (eq.trans et)
  by_cases zero : g = 0
  · have pos : 0 < r := by dsimp [r,L]; omega
    obtain ⟨a,ha⟩ := choose_trace (n:=r) pos rb right rp
    have next := endpos (ha r le_rfl)
    rw [next,zero,point_zero,left]
    simpa only [oriented_zero] using (oriented_edge m c a 0 (by unfold L;omega))
  by_cases last : r = 0
  · obtain ⟨a,ha⟩ := choose_trace (n:=g) (by omega) hg.le left lp
    have first : f (point m d g) = oriented m c a g := ha g le_rfl
    have last' : g+1 = L m := by dsimp [r] at last; omega
    rw [first,last',point_last,right]
    have e := oriented_edge m c a g hg
    rwa [last',oriented_last] at e
  have srcL (i : Fin 3) : ∃ a, f (oriented m false i 1) = oriented m c a 1 := by
    have e := good.direction hg false i 0 (by unfold L;omega) (Or.inr (by change 0 ≠ g;omega))
    rw [oriented_zero,left] at e
    exact pole_neighbor m c e
  have srcR (i : Fin 3) : ∃ a, f (oriented m true i 1) = oriented m (!c) a 1 := by
    have e := good.direction hg true i 0 (by unfold L;omega) (Or.inr (by rw [gapr]; omega))
    rw [oriented_zero,right] at e
    exact pole_neighbor m (!c) e
  choose a ha using srcL
  choose b hb using srcR
  have agree (i : Fin 3) (hi : i ≠ d) : a i = b i := by
    have full := trace m f false c i (a i) (L m) le_rfl left (ha i)
      (fun t ht => good.direction hg false i t ht (Or.inl hi))
    have ea := full (L m-1) (Nat.sub_le ..)
    have eb := hb i
    rw [show oriented m true i 1 = oriented m false i (L m-1) from first_reverse m false i,
      first_reverse m c (b i)] at eb
    exact oriented_arm_inj m c (by unfold L;omega : 0 < L m - 1) (by unfold L;omega) (ea.symm.trans eb)
  have same : a d = b d := by
    obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp (label_inj b hb)) (a d)
    by_cases eq : j = d
    · subst j
      exact hj.symm
    · exact (eq ((label_inj a ha) ((agree j eq).trans hj))).elim
  have one : f (point m d g) = oriented m c (a d) g :=
    trace m f false c d (a d) g hg.le left (ha d) lp g le_rfl
  have two := endpos (trace m f true (!c) d (b d) r rb right (hb d) rp r le_rfl)
  rw [one,two,←same]
  exact oriented_edge m c (a d) g hg

theorem step_self (m : Nat) : step (H m) (H m) = H m := by
  apply le_antisymm _ (le_step _ _)
  intro x y edge
  rcases edge with h | w
  · exact h
  · obtain ⟨f,d,g,hg,good,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := witness_gap w
    · exact gap_adj hg good
    · exact (gap_adj hg good).symm

theorem run_self (m t : Nat) : run (H m) (H m) t = H m := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ,ih,step_self]

theorem stabilization_zero (m : Nat) : stabilizationTime (H m) (H m) = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min' (stable_exists _ _)
  rw [run_self,run_self]

theorem terminal_self (m : Nat) : terminalGraph (H m) (H m) = H m := run_self _ _

/-- At length two there is one private vertex per arm, yielding the published K₂,₃ example. -/
def shortest_iso : H 0 ≃g completeBipartiteGraph Bool (Fin 3) where
  toFun
    | .inl b => .inl b
    | .inr ⟨i,_⟩ => .inr i
  invFun
    | .inl b => .inl b
    | .inr i => .inr ⟨i,0⟩
  left_inv := by
    rintro (b | ⟨i,j⟩)
    · rfl
    · have e : j = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
      subst j
      rfl
  right_inv := by rintro (b | i) <;> rfl
  map_rel_iff' := by
    rintro (b | ⟨i,j⟩) (c | ⟨a,t⟩)
    · change (true = true ∧ false = true ∨ false = true ∧ true = true) ↔ False
      decide
    · have e : t = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
      subst t
      cases b <;> exact ⟨fun _ => rfl,fun _ => Or.inl ⟨rfl,rfl⟩⟩
    · have e : j = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
      subst j
      cases c <;> exact ⟨fun _ => rfl,fun _ => Or.inr ⟨rfl,rfl⟩⟩
    · have e : j = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
      have e' : t = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
      subst j
      subst t
      change (_ ∧ _ ∨ _ ∧ _) ↔ (i = a ∧ ((0:Nat)+1 = 0 ∨ 0+1=0))
      simp

end Bootstrap.Theta.EqualArms

namespace Bootstrap.Theta

/-- The equal-length clause of the theta self-closure classification, for the
ordinary rule and its actual stabilization time. -/
theorem equal_length_self_closure (ℓ : Nat) :
    let H := rule (threeLengths ℓ ℓ ℓ)
    terminalGraph H H = H := by
  dsimp only
  have eq : threeLengths ℓ ℓ ℓ = fun _ => ℓ := funext (by intro i; simp [threeLengths])
  rw [eq]
  exact EqualArms.terminal_self _

end Bootstrap.Theta

#print axioms Bootstrap.Theta.EqualArms.gap_adj
#print axioms Bootstrap.Theta.EqualArms.step_self
#print axioms Bootstrap.Theta.equal_length_self_closure
