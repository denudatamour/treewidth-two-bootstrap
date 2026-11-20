import Bootstrap.CliqueClock

/-! Closed cuts and induced components for a properly coloured rule without a
one-monochromatic-edge colouring. -/
namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

def ClosedCut (G : SimpleGraph V) (S : Set V) := ∀ i j, G.Adj i j → (i ∈ S ↔ j ∈ S)

private theorem xor_same {a b i j : Bool} (ab : a ≠ b) (ij : i ≠ j) :
    (a != i) = (b != j) := by cases a <;> cases b <;> cases i <;> cases j <;> simp_all

private theorem xor_diff {a b i : Bool} (ab : a ≠ b) :
    (a != i) ≠ (b != i) := by cases a <;> cases b <;> cases i <;> simp_all

private theorem cut_constant (H : SimpleGraph W) (conn : H.Connected)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H)
    (s : W → Bool) {u v : W} (e : H.Adj u v)
    (outside : ∀ i j, H.Adj i j → ¬((i=u ∧ j=v) ∨ (i=v ∧ j=u)) → s i=s j) :
    ∀ i, s i=s u := by
  classical
  have tgt : s u=s v := by
    by_contra diff
    apply no
    refine ⟨fun i => c i != s i,u,v,e,xor_same (proper u v e) diff,?_⟩
    intro i j edge eq
    by_contra away
    have same := outside i j edge away
    have ne := xor_diff (i := s i) (proper i j edge)
    exact ne (by simpa only [←same] using eq)
  have every (i j : W) (edge : H.Adj i j) : s i=s j := by
    by_cases exc : (i=u ∧ j=v) ∨ (i=v ∧ j=u)
    · rcases exc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact tgt
      · exact tgt.symm
    · exact outside i j edge exc
  intro i
  have path := (H.reachable_iff_reflTransGen u i).mp (conn u i)
  induction path with
  | refl => rfl
  | tail _ ij ih => exact (every _ _ ij).symm.trans ih

private theorem roles_in_cut (H : SimpleGraph W) (conn : H.Connected)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H)
    (G : SimpleGraph V) (S : Set V) (cut : ClosedCut G S)
    (f : W ↪ V) {u v : W} (e : H.Adj u v)
    (hr : ∀ i j, H.Adj i j → ¬((i=u ∧ j=v) ∨ (i=v ∧ j=u)) → G.Adj (f i) (f j)) :
    ∀ i, f i ∈ S ↔ f u ∈ S := by
  classical
  let s (i : W) := decide (f i ∈ S)
  have all := cut_constant H conn c proper no s e
    (fun i j ij away => decide_eq_decide.mpr (cut _ _ (hr i j ij away)))
  exact fun i => decide_eq_decide.mp (all i)

theorem closed_cut_step (H : SimpleGraph W) (conn : H.Connected)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H)
    (G : SimpleGraph V) (S : Set V) (cut : ClosedCut G S) : ClosedCut (step H G) S := by
  intro x y born
  rcases born with old|⟨u,v,f,e,rfl,rfl,hr⟩
  · exact cut _ _ old
  · exact (roles_in_cut H conn c proper no G S cut f e hr v).symm

theorem cut_induced_step (H : SimpleGraph W) (conn : H.Connected)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H)
    (G : SimpleGraph V) (S : Set V) (cut : ClosedCut G S) :
    (step H G).induce S = step H (G.induce S) := by
  ext x y
  constructor
  · rintro (old|⟨u,v,f,e,hx,hy,hr⟩)
    · exact Or.inl old
    · have all := roles_in_cut H conn c proper no G S cut f e hr
      have xu : f u ∈ S := hx.symm ▸ x.property
      let g : W ↪ S := ⟨fun i => ⟨f i,(all i).mpr xu⟩,fun i j eq => f.injective (congrArg Subtype.val eq)⟩
      exact Or.inr ⟨u,v,g,e,Subtype.ext hx,Subtype.ext hy,hr⟩
  · rintro (old|⟨u,v,f,e,hx,hy,hr⟩)
    · exact Or.inl old
    · exact Or.inr ⟨u,v,f.trans (Function.Embedding.subtype _),e,
        congrArg Subtype.val hx,congrArg Subtype.val hy,hr⟩

theorem local_component_run (H : SimpleGraph W) (conn : H.Connected)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H)
    (G : SimpleGraph V) (S : Set V) (cut : ClosedCut G S) (t : ℕ) :
    ClosedCut (run H G t) S ∧ (run H G t).induce S = run H (G.induce S) t := by
  induction t with
  | zero => exact ⟨cut,rfl⟩
  | succ t ih =>
    exact ⟨closed_cut_step H conn c proper no _ S ih.1, (cut_induced_step H conn c proper no _ S ih.1).trans (congrArg (step H) ih.2)⟩

theorem equality_after_stable [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) {t : ℕ}
    (ht : stabilizationTime H G ≤ t) : run H G t = run H G (t+1) := by
  induction ht with
  | refl => exact stabilizationTime_spec H G
  | step _ ih => exact congrArg (step H) ih

/-- Bound all components at the same time, then deduce the statement on the original host. -/
theorem stable_of_components [Fintype V] (H : SimpleGraph W) (conn : H.Connected)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H)
    (G : SimpleGraph V) (t : ℕ)
    (all : ∀ A : G.ConnectedComponent, stabilizationTime H (G.induce A.supp) ≤ t) :
    stabilizationTime H G ≤ t := by
  classical
  apply Nat.find_min' (stable_exists H G)
  apply le_antisymm (run_le_succ H G t)
  intro x y e
  let A := G.connectedComponentMk x
  have cut : ClosedCut G A.supp := fun _ _ adj => A.mem_supp_congr_adj adj
  have before := local_component_run H conn c proper no G A.supp cut t
  have after := local_component_run H conn c proper no G A.supp cut (t+1)
  have hx : x ∈ A.supp := rfl
  have hy : y ∈ A.supp := (after.1 _ _ e).mp hx
  let a : A.supp := ⟨x,hx⟩
  let b : A.supp := ⟨y,hy⟩
  have atNew : ((run H G (t+1)).induce A.supp).Adj a b := e
  change ((run H G t).induce A.supp).Adj a b
  rw [before.2,equality_after_stable H _ (all A),←after.2]
  exact atNew

/-- If the old host respects a proper cut, a same-shore birth would itself
pull back a one-monochromatic-edge colouring of the rule. -/
theorem proper_step (H : SimpleGraph W) (no : ¬OneMonochrome H) (G : SimpleGraph V) (c : V → Bool)
    (proper : ∀ i j, G.Adj i j → c i ≠ c j) : ∀ i j, (step H G).Adj i j → c i ≠ c j := by
  intro x y born eq
  rcases born with old|⟨u,v,f,e,rfl,rfl,hr⟩
  · exact proper _ _ old eq
  · apply no
    refine ⟨fun i => c (f i),u,v,e,eq,?_⟩
    intro i j ij same
    exact by_contra (fun away => proper _ _ (hr i j ij away) same)

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.local_component_run
#print axioms Bootstrap.DegreeTwo.stable_of_components
