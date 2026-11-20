import Bootstrap.DegreeTwoTransfer
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Bootstrap.Subdivision

variable {C E V : Type*}

/-- Distinct edge indices may have the same unordered pair of ends. -/
structure Data (C E : Type*) where
  left : E → C
  right : E → C
  proper : ∀ e, left e ≠ right e

def Data.ends (D : Data C E) (c : C) (e : E) : Prop := c = D.left e ∨ c = D.right e

def Data.rule (D : Data C E) : SimpleGraph (C ⊕ E) where
  Adj
    | .inl _, .inl _ => False
    | .inr _, .inr _ => False
    | .inl c, .inr e => D.ends c e
    | .inr e, .inl c => D.ends c e
  symm := by
    intro i j
    cases i <;> cases j <;> exact id
  loopless := by
    intro i
    cases i <;> exact id

private theorem embed_one {α β : Type*} [Fintype α] [Fintype β] (a : α) (x : β)
    (size : Fintype.card α ≤ Fintype.card β) : ∃ f : α ↪ β, f a = x := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le size
  exact ⟨f.trans (Equiv.swap (f a) x).toEmbedding,Equiv.swap_apply_left _ _⟩

private theorem embed_two {α β : Type*} [Fintype α] [Fintype β] (a b : α) (x y : β)
    (ab : a ≠ b) (xy : x ≠ y) (size : Fintype.card α ≤ Fintype.card β) :
    ∃ f : α ↪ β, f a = x ∧ f b = y := by
  classical
  obtain ⟨f,fa⟩ := embed_one a x size
  have bx : x ≠ f b := fun eq => ab (f.injective (fa.trans eq))
  refine ⟨f.trans (Equiv.swap (f b) y).toEmbedding,?_,Equiv.swap_apply_left _ _⟩
  change Equiv.swap (f b) y (f a) = x
  rw [fa, Equiv.swap_apply_of_ne_of_ne bx xy]

private def values {α : Type*} {s : Finset V} (f : α ↪ ↥s) : α ↪ V :=
  ⟨fun a => (f a).1,fun _ _ h => f.injective (Subtype.ext h)⟩

private def sumEmbedding (fc : C ↪ V) (fe : E ↪ V) (apart : ∀ c e, fc c ≠ fe e) : C ⊕ E ↪ V :=
  ⟨Sum.elim fc fe,by
    intro a b eq
    cases a with
    | inl c =>
      cases b with
      | inl c' => exact congrArg Sum.inl (fc.injective eq)
      | inr d => exact False.elim (apart c d eq)
    | inr e =>
      cases b with
      | inl c => exact False.elim (apart c e eq.symm)
      | inr e' => exact congrArg Sum.inr (fe.injective eq)⟩

/-- A vertex in a certifying set is joined to all other vertices of the block.
The certifying set and the block may intersect. -/
def Certified (G : SimpleGraph V) (B T : Finset V) : Prop :=
  ∀ z ∈ T, ∀ b ∈ B, z ≠ b → G.Adj z b

private theorem choose_positions [Fintype C] [Fintype E] (D : Data C E) (e₀ : E)
    (B T : Finset V) (x y z : V) (bx : x ∈ B) (by_ : y ∈ B)
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (nb : Fintype.card C ≤ B.card) (nt : Fintype.card C + Fintype.card E ≤ T.card)
    (free : z ∉ B ∨ Fintype.card C < B.card) :
    ∃ (fc : C ↪ V) (fe : E ↪ V), fc (D.left e₀) = x ∧ fc (D.right e₀) = y ∧ fe e₀ = z ∧
      (∀ c, fc c ∈ B) ∧ (∀ e, e ≠ e₀ → fe e ∈ T) ∧ ∀ c e, fc c ≠ fe e := by
  classical
  let avail := B.erase z
  have av (v : V) : v ∈ avail ↔ v ≠ z ∧ v ∈ B := Finset.mem_erase
  have size : Fintype.card C ≤ avail.card := by
    by_cases h : z ∈ B
    · have more := free.resolve_left (fun hn => hn h)
      unfold avail
      rw [Finset.card_erase_of_mem h]
      omega
    · simpa [avail,Finset.erase_eq_of_not_mem h] using nb
  obtain ⟨fb,fl,fr⟩ := embed_two (D.left e₀) (D.right e₀)
    (⟨x,(av x).mpr ⟨xz,bx⟩⟩ : avail) (⟨y,(av y).mpr ⟨yz,by_⟩⟩ : avail) (D.proper e₀)
    (fun h => xy (congrArg Subtype.val h)) (by simpa using size)
  let fc := values fb
  have mem (c : C) : fc c ∈ avail := (fb c).2
  let used := Finset.univ.map fc
  have used_card : used.card = Fintype.card C := by simp [used]
  have fc_used (c : C) : fc c ∈ used := Finset.mem_map.mpr ⟨c, Finset.mem_univ _, rfl⟩
  have zfree : z ∉ used := by
    intro h
    obtain ⟨c,_,e⟩ := Finset.mem_map.mp h
    exact ((av _).mp (mem c)).1 e
  let allowed := insert z (T \ used)
  have room₀ : T.card ≤ (T \ used).card + used.card := Finset.card_le_card_sdiff_add_card
  have room₁ : (T \ used).card ≤ allowed.card := Finset.card_le_card (Finset.subset_insert _ _)
  obtain ⟨fm,fz⟩ := embed_one e₀ (⟨z,Finset.mem_insert_self _ _⟩ : allowed)
    (by simp only [Fintype.card_coe]; omega)
  let fe := values fm
  have hit : fe e₀ = z := congrArg Subtype.val fz
  have feasible (e : E) : fe e = z ∨ (fe e ∈ T ∧ fe e ∉ used) := by
    have h : fe e ∈ allowed := (fm e).2
    simpa only [allowed, Finset.mem_insert, Finset.mem_sdiff] using h
  refine ⟨fc,fe,congrArg Subtype.val fl,congrArg Subtype.val fr,hit,
    fun c => ((av _).mp (mem c)).2,?_,?_⟩
  · intro e hn
    rcases feasible e with h | h
    · exact False.elim (hn (fe.injective (h.trans hit.symm)))
    · exact h.1
  · intro c e eq
    have present : fe e ∈ used := eq ▸ fc_used c
    rcases feasible e with h | h
    · exact zfree (h ▸ present)
    · exact h.2 present

/-- Appendix A, one ordinary round of block transfer for the once-subdivision
of an arbitrary loopless multigraph. Every target uses the same old graph. -/
theorem block_transfer [Fintype C] [Fintype E] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (B T : Finset V) (cert : Certified G B T)
    (nb : Fintype.card C ≤ B.card) (nt : Fintype.card C + Fintype.card E ≤ T.card)
    {x y z : V} (bx : x ∈ B) (by_ : y ∈ B) (xy : x ≠ y) (yz : y ≠ z)
    (contact : G.Adj z x) (free : z ∉ B ∨ Fintype.card C < B.card) :
    (step D.rule G).Adj z y := by
  have xz : x ≠ z := by
    intro e
    exact G.loopless z (e ▸ contact)
  obtain ⟨fc,fe,fl,fr,fz,inside,mid,apart⟩ :=
    choose_positions D e₀ B T x y z bx by_ xy xz yz nb nt free
  let g := sumEmbedding fc fe apart
  have contacts (c : C) (d : E) (e : D.ends c d) (hn : ¬ (c = D.right e₀ ∧ d = e₀)) :
      G.Adj (fc c) (fe d) := by
    by_cases de : d = e₀
    · subst d
      rcases e with h | h
      · rw [h,fl,fz]
        exact G.symm contact
      · exact False.elim (hn ⟨h,rfl⟩)
    · exact G.symm (cert (fe d) (mid d de) (fc c) (inside c) (apart c d).symm)
  refine Or.inr ⟨Sum.inr e₀,Sum.inl (D.right e₀),g,Or.inr rfl,fz,fr,?_⟩
  intro i j e hn
  cases i with
  | inl c =>
    cases j with
    | inl c' => exact False.elim e
    | inr d =>
      exact contacts c d e (fun h => hn (Or.inr ⟨congrArg Sum.inl h.1,congrArg Sum.inr h.2⟩))
  | inr d =>
    cases j with
    | inl c =>
      exact G.symm (contacts c d e (fun h => hn (Or.inl ⟨congrArg Sum.inr h.2,congrArg Sum.inl h.1⟩)))
    | inr d' => exact False.elim e

/-- Singletons are the initial blocks; all later blocks carry a common
certifying set and the two size inequalities. -/
def Block [Fintype C] [Fintype E] (_D : Data C E) (G : SimpleGraph V) (B : Finset V) : Prop :=
  (∀ x ∈ B, ∀ y ∈ B, x = y) ∨
  ∃ T, Fintype.card C ≤ B.card ∧ Fintype.card C + Fintype.card E ≤ T.card ∧ Certified G B T

theorem block_mono [Fintype C] [Fintype E] {D : Data C E} {G J : SimpleGraph V} {B : Finset V}
    (grow : G ≤ J) (h : Block D G B) : Block D J B := by
  rcases h with single | ⟨T,nb,nt,cert⟩
  · exact Or.inl single
  · exact Or.inr ⟨T,nb,nt,fun z hz v hv ne => grow (cert z hz v hv ne)⟩

theorem spread [Fintype C] [Fintype E] (D : Data C E) (e₀ : E) (G : SimpleGraph V)
    {B : Finset V} (h : Block D G B) {x z : V} (bx : x ∈ B) (contact : G.Adj z x)
    (free : z ∉ B ∨ Fintype.card C < B.card) :
    ∀ y ∈ B, y ≠ z → (step D.rule G).Adj z y := by
  classical
  intro y by_ yz
  by_cases eq : x=y
  · rw [←eq]
    exact Or.inl contact
  · rcases h with single | ⟨T,nb,nt,cert⟩
    · exact False.elim (eq (single x bx y by_))
    · exact block_transfer D e₀ G B T cert nb nt bx by_ eq yz contact free

/-- First contact between distinct blocks fills their full rectangle within
two rounds, independently of the other witnesses in those rounds. -/
theorem rectangle_two [Fintype C] [Fintype E] (D : Data C E) (e₀ : E) (G : SimpleGraph V)
    (t : ℕ) {A B : Finset V} (a_block : Block D (run D.rule G t) A)
    (b_block : Block D (run D.rule G t) B) (dis : Disjoint A B)
    {x y : V} (ax : x ∈ A) (by_ : y ∈ B) (contact : (run D.rule G t).Adj x y) :
    ∀ a ∈ A, ∀ b ∈ B, (run D.rule G (t+1+1)).Adj a b := by
  intro a ha b hb
  have ya : y ∉ A := fun hy => Finset.disjoint_left.mp dis hy by_
  have anb : a ∉ B := Finset.disjoint_left.mp dis ha
  have ay : a ≠ y := fun eq => anb (eq.symm ▸ by_)
  have ab : b ≠ a := fun eq => anb (eq ▸ hb)
  have old := spread D e₀ _ a_block ax ((run D.rule G t).symm contact) (Or.inl ya) a ha ay
  exact spread D e₀ _ (block_mono (run_le_succ D.rule G t) b_block) by_
    ((run D.rule G (t+1)).symm old) (Or.inl anb) b hb ab

/-- The first internal contact in a block of order greater than the number
of base roles fills that block within a further two rounds. -/
theorem internal_two [Fintype C] [Fintype E] (D : Data C E) (e₀ : E) (G : SimpleGraph V)
    (t : ℕ) {A : Finset V} (h : Block D (run D.rule G t) A) (large : Fintype.card C < A.card)
    {x y : V} (ax : x ∈ A) (ay : y ∈ A) (contact : (run D.rule G t).Adj x y) :
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (run D.rule G (t+1+1)).Adj a b := by
  classical
  have star := spread D e₀ _ h ay contact (Or.inr large)
  intro a ha b hb ab
  by_cases eq : a=x
  · subst a
    exact run_le_succ D.rule G (t+1) (star b hb ab.symm)
  · have old := (run D.rule G (t+1)).symm (star a ha eq)
    exact spread D e₀ _ (block_mono (run_le_succ D.rule G t) h) ax old (Or.inr large) b hb ab.symm

end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.block_transfer
#print axioms Bootstrap.Subdivision.rectangle_two
#print axioms Bootstrap.Subdivision.internal_two
