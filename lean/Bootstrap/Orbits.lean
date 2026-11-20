/-
Author: Haimin Zhou. Local internal-review formalization pilot.
-/
import Bootstrap.Process

namespace Bootstrap

variable {V W : Type*}

abbrev UEdge (V : Type*) := {e : Sym2 V // ¬e.IsDiag}

def edgeSMul (Γ : Subgroup (Equiv.Perm V)) (g : Γ) (e : UEdge V) : UEdge V :=
  ⟨e.val.map g.val, fun h => e.property ((Sym2.isDiag_map g.val.injective).mp h)⟩

instance edgeAction (Γ : Subgroup (Equiv.Perm V)) : MulAction Γ (UEdge V) where
  smul := edgeSMul Γ
  one_smul := by
    intro e
    apply Subtype.ext
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y => rfl
  mul_smul := by
    intro g h e
    apply Subtype.ext
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y => rfl

def edgePresent (G : SimpleGraph V) (e : UEdge V) : Prop := e.val ∈ G.edgeSet

theorem invariant_edge (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V)
    (hG : Invariant Γ G) (g : Γ) (e : UEdge V) :
    edgePresent G (g • e) ↔ edgePresent G e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y => exact hG g x y

def Orbit (Γ : Subgroup (Equiv.Perm V)) := Quotient (MulAction.orbitRel Γ (UEdge V))

def orbitOf (Γ : Subgroup (Equiv.Perm V)) (e : UEdge V) : Orbit Γ :=
  Quotient.mk _ e

noncomputable instance orbitFintype [Fintype V] (Γ : Subgroup (Equiv.Perm V)) :
    Fintype (Orbit Γ) := by
  classical
  exact Quotient.fintype (MulAction.orbitRel Γ (UEdge V))

def orbitPresent (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (o : Orbit Γ) : Prop :=
  ∃ e, orbitOf Γ e = o ∧ edgePresent G e

theorem orbitPresent_mk (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V)
    (hG : Invariant Γ G) (e : UEdge V) :
    orbitPresent Γ G (orbitOf Γ e) ↔ edgePresent G e := by
  constructor
  · rintro ⟨f, hf, he⟩
    have hr : (MulAction.orbitRel Γ (UEdge V)).r f e := Quotient.exact hf
    change ∃ g : Γ, g • e = f at hr
    rcases hr with ⟨g, rfl⟩
    exact (invariant_edge Γ G hG g e).mp he
  · intro he
    exact ⟨e, rfl, he⟩

noncomputable def presentOrbits [Fintype V] (Γ : Subgroup (Equiv.Perm V))
    (G : SimpleGraph V) : Finset (Orbit Γ) := by
  classical
  exact Finset.univ.filter (orbitPresent Γ G)

noncomputable def missingOrbits [Fintype V] (Γ : Subgroup (Equiv.Perm V))
    (G : SimpleGraph V) : Finset (Orbit Γ) := by
  classical
  exact Finset.univ \ presentOrbits Γ G

theorem edgePresent_mono {G G' : SimpleGraph V} (h : G ≤ G') (e : UEdge V) :
    edgePresent G e → edgePresent G' e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    intro hp
    exact h hp

theorem presentOrbits_mono [Fintype V] (Γ : Subgroup (Equiv.Perm V))
    {G G' : SimpleGraph V} (h : G ≤ G') : presentOrbits Γ G ⊆ presentOrbits Γ G' := by
  classical
  intro o ho
  simp only [presentOrbits, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
  rcases ho with ⟨e, he, hp⟩
  exact ⟨e, he, edgePresent_mono h e hp⟩

theorem graph_eq_of_presentOrbits_eq [Fintype V] (Γ : Subgroup (Equiv.Perm V))
    (G G' : SimpleGraph V) (hG : Invariant Γ G) (hG' : Invariant Γ G')
    (heq : presentOrbits Γ G = presentOrbits Γ G') : G = G' := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  · let e : UEdge V := ⟨s(x,y), hxy⟩
    have hm := congrArg (fun s : Finset (Orbit Γ) => orbitOf Γ e ∈ s) heq
    have hi : orbitPresent Γ G (orbitOf Γ e) ↔ orbitPresent Γ G' (orbitOf Γ e) := by
      simpa only [presentOrbits, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Iff.of_eq hm)
    exact (orbitPresent_mk Γ G hG e).symm.trans (hi.trans (orbitPresent_mk Γ G' hG' e))

theorem missingOrbits_antitone [Fintype V] (Γ : Subgroup (Equiv.Perm V))
    {G G' : SimpleGraph V} (h : G ≤ G') : missingOrbits Γ G' ⊆ missingOrbits Γ G := by
  classical
  intro o ho
  simp only [missingOrbits, Finset.mem_sdiff, Finset.mem_univ, true_and] at ho ⊢
  exact fun hp => ho (presentOrbits_mono Γ h hp)

theorem missing_card_decreases [Fintype V] (H : SimpleGraph W)
    (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (hG : Invariant Γ G)
    (hne : step H G ≠ G) :
    (missingOrbits Γ (step H G)).card < (missingOrbits Γ G).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨missingOrbits_antitone Γ (le_step H G), ?_⟩
  intro heq
  apply hne
  apply graph_eq_of_presentOrbits_eq Γ (step H G) G (invariant_step H Γ G hG) hG
  ext o
  have hm := congrArg (fun s : Finset (Orbit Γ) => o ∈ s) heq
  have hi := Iff.of_eq hm
  simp only [missingOrbits, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
  tauto

theorem run_shift (H : SimpleGraph W) (G : SimpleGraph V) (n : ℕ) :
    run H G (n+1) = run H (step H G) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step H (run H G (n+1)) = step H (run H (step H G) n)
    exact congrArg (step H) ih

theorem exists_stable_le_missing [Fintype V] (H : SimpleGraph W)
    (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (hG : Invariant Γ G) :
    ∃ t ≤ (missingOrbits Γ G).card, run H G t = run H G (t+1) := by
  classical
  generalize hm : (missingOrbits Γ G).card = m
  induction m using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hfix : step H G = G
    · exact ⟨0, Nat.zero_le _, hfix.symm⟩
    · have hdec := missing_card_decreases H Γ G hG hfix
      rw [hm] at hdec
      obtain ⟨t, ht, hstable⟩ := ih _ hdec (step H G) (invariant_step H Γ G hG) rfl
      refine ⟨t+1, by omega, ?_⟩
      simpa only [run_shift] using hstable

theorem added_edge_whole_orbit (H : SimpleGraph W)
    (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (hG : Invariant Γ G)
    (e : UEdge V) (hnew : edgePresent (step H G) e) (hold : ¬ edgePresent G e)
    (g : Γ) : edgePresent (step H G) (g • e) ∧ ¬ edgePresent G (g • e) := by
  constructor
  · exact (invariant_edge Γ (step H G) (invariant_step H Γ G hG) g e).mpr hnew
  · intro he
    exact hold ((invariant_edge Γ G hG g e).mp he)

theorem invariant_bot (G : SimpleGraph V) : Invariant (⊥ : Subgroup (Equiv.Perm V)) G := by
  intro g x y
  have hg : g.val = 1 := Subgroup.mem_bot.mp g.property
  simp [hg]

theorem stable_exists [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    ∃ t, run H G t = run H G (t+1) := by
  obtain ⟨t, _, ht⟩ := exists_stable_le_missing H ⊥ G (invariant_bot G)
  exact ⟨t, ht⟩

noncomputable def stabilizationTime [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find (stable_exists H G)

theorem stabilizationTime_spec [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    run H G (stabilizationTime H G) = run H G (stabilizationTime H G + 1) := by
  classical
  exact Nat.find_spec (stable_exists H G)

theorem stabilizationTime_le_missing [Fintype V] (H : SimpleGraph W)
    (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (hG : Invariant Γ G) :
    stabilizationTime H G ≤ (missingOrbits Γ G).card := by
  classical
  obtain ⟨t, ht, hfix⟩ := exists_stable_le_missing H Γ G hG
  exact le_trans (Nat.find_min' (stable_exists H G) hfix) ht

theorem run_add (H : SimpleGraph W) (G : SimpleGraph V) (s t : ℕ) :
    run H G (s+t) = run H (run H G s) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Nat.add_succ, run_succ, ih]

theorem exists_stable_after [Fintype V] (H : SimpleGraph W)
    (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (hG : Invariant Γ G) (s : ℕ) :
    ∃ t ≤ (missingOrbits Γ (run H G s)).card,
      run H G (s+t) = run H G (s+t+1) := by
  obtain ⟨t, ht, hfix⟩ := exists_stable_le_missing H Γ (run H G s) (invariant_run H Γ G hG s)
  refine ⟨t, ht, ?_⟩
  simpa only [Nat.add_assoc, run_add] using hfix

theorem exists_stable_after_current_symmetry [Fintype V] (H : SimpleGraph W)
    (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (s : ℕ)
    (hG : Invariant Γ (run H G s)) :
    ∃ t ≤ (missingOrbits Γ (run H G s)).card,
      run H G (s+t) = run H G (s+t+1) := by
  obtain ⟨t, ht, hfix⟩ := exists_stable_le_missing H Γ (run H G s) hG
  refine ⟨t, ht, ?_⟩
  simpa only [Nat.add_assoc, run_add] using hfix

theorem stabilizationTime_le_from_current [Fintype V] (H : SimpleGraph W)
    (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) (s : ℕ)
    (hG : Invariant Γ (run H G s)) :
    stabilizationTime H G ≤ s + (missingOrbits Γ (run H G s)).card := by
  classical
  obtain ⟨t, ht, hfix⟩ := exists_stable_after_current_symmetry H Γ G s hG
  exact le_trans (Nat.find_min' (stable_exists H G) hfix) (Nat.add_le_add_left ht s)

end Bootstrap

#print axioms Bootstrap.orbitPresent_mk
#print axioms Bootstrap.missing_card_decreases
#print axioms Bootstrap.exists_stable_le_missing
#print axioms Bootstrap.added_edge_whole_orbit
#print axioms Bootstrap.stabilizationTime_le_missing
#print axioms Bootstrap.exists_stable_after
#print axioms Bootstrap.exists_stable_after_current_symmetry
#print axioms Bootstrap.stabilizationTime_le_from_current
