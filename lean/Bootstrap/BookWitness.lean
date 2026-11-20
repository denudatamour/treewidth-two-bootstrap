import Bootstrap.Localization

namespace Bootstrap.Localization

variable {S V I : Type*}

/-- The two possible orientations of the single removed source edge. -/
def Missing (u v a b : S) : Prop := (a = u ∧ b = v) ∨ (a = v ∧ b = u)

def MapsExcept (H : SimpleGraph S) (G : SimpleGraph V) (u v : S) (f : S ↪ V) : Prop :=
  ∀ a b, H.Adj a b → ¬Missing u v a b → G.Adj (f a) (f b)

private theorem skip_one {n : Nat} {P : Fin (n+1) → Prop}
    (h : ∀ i j, P i → P j → i = j) :
    ∃ e : Fin n ↪ Fin (n+1), ∀ i, ¬P (e i) := by
  classical
  by_cases hex : ∃ j, P j
  · obtain ⟨j, hj⟩ := hex
    exact ⟨Fin.succAboveEmb j, fun i hp => Fin.succAbove_ne j i (h _ j hp hj)⟩
  · exact ⟨Fin.castSuccEmb, fun i hi => hex ⟨_, hi⟩⟩

/-- Of 103 distinct pages adjacent to both ends, at least 102 survive one edge deletion. -/
theorem common_after_deletion {H : SimpleGraph S} {G : SimpleGraph V} {u v a b : S}
    {f : S ↪ V} (hf : MapsExcept H G u v f) {n : Nat}
    (hc : DistinctCommon H (n+1) a b) : DistinctCommon G n (f a) (f b) := by
  obtain ⟨w, hw⟩ := hc
  let Bad (i : Fin (n+1)) := Missing u v a (w i) ∨ Missing u v b (w i)
  have one : ∀ i j, Bad i → Bad j → i = j := by
    intro i j hi hj
    apply w.injective
    have hi₁ := (H.mem_commonNeighbors.mp (hw i)).1.ne
    have hi₂ := (H.mem_commonNeighbors.mp (hw i)).2.ne
    have hj₁ := (H.mem_commonNeighbors.mp (hw j)).1.ne
    have hj₂ := (H.mem_commonNeighbors.mp (hw j)).2.ne
    simp only [Bad, Missing] at hi hj
    rcases hi with (⟨e₁, e₂⟩ | ⟨e₁, e₂⟩) | (⟨e₁, e₂⟩ | ⟨e₁, e₂⟩) <;>
      rcases hj with (⟨e₃, e₄⟩ | ⟨e₃, e₄⟩) | (⟨e₃, e₄⟩ | ⟨e₃, e₄⟩) <;> simp_all
  obtain ⟨e, he⟩ := skip_one one
  refine ⟨(e.trans w).trans f, fun i => ?_⟩
  exact ⟨hf a _ (hw _).1 (fun h => he i (Or.inl h)),
    hf b _ (hw _).2 (fun h => he i (Or.inr h))⟩

theorem owner_unique (size pages : I → Nat) {i j : I} {x : Vertex size pages}
    (hi : x ∈ clique size pages i) (hj : x ∈ clique size pages j) : i = j := by
  obtain ⟨a, rfl⟩ := (mem_clique size pages).mp hi
  obtain ⟨b, e⟩ := (mem_clique size pages).mp hj
  cases e
  rfl

def Together (size pages : I → Nat) (x y : Vertex size pages) : Prop :=
  ∃ i, x ∈ clique size pages i ∧ y ∈ clique size pages i

private theorem together_trans {size pages : I → Nat} {x y z : Vertex size pages}
    (h : Together size pages x y) (h' : Together size pages y z) : Together size pages x z := by
  obtain ⟨i, hx, hy⟩ := h
  obtain ⟨j, hy', hz⟩ := h'
  obtain rfl := owner_unique _ _ hy hy'
  exact ⟨i, hx, hz⟩

def CoreEdge {n : Nat} (a b : Fin n) : Prop :=
  a ≠ b ∧ (a.val < 2 ∨ b.val < 2)

/-- The book core on positions 0,...,s-1, with its two hubs 0,1 and assigned common pages. -/
structure BookIn (H : SimpleGraph S) (n : Nat) where
  three_le : 3 ≤ n
  core : Fin n ↪ S
  thick : ∀ i j, CoreEdge i j →
    H.Adj (core i) (core j) ∧ DistinctCommon H 103 (core i) (core j)

theorem surviving_core_edge_local {H : SimpleGraph S} {F : SimpleGraph I} {ty : I → Fin 10}
    (hF : TriangleFree F) {u v : S} {f : S ↪ HostVertex ty}
    (hf : MapsExcept H (host F ty) u v f) {n : Nat} (B : BookIn H n) {i j : Fin n}
    (he : CoreEdge i j) (hs : ¬Missing u v (B.core i) (B.core j)) :
    Together (blockSize ty) (pageCount ty) (f (B.core i)) (f (B.core j)) := by
  obtain ⟨hold, hp⟩ := B.thick i j he
  exact host_large_common_internal F ty hF (hf _ _ hold hs) (common_after_deletion hf hp)

private theorem deleted_equal {u v a b c d : S} (h : Missing u v a b)
    (h' : Missing u v c d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases h with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;>
    rcases h' with ⟨e₃, e₄⟩ | ⟨e₃, e₄⟩ <;> simp_all

private theorem other_right {u v a b c : S} (hne : b ≠ c) (h : Missing u v a b) :
    ¬Missing u v a c := by
  intro h'
  rcases deleted_equal h h' with he | he
  · exact hne he.2
  · exact hne (he.2.trans he.1)

private theorem other_left {u v a b c : S} (hne : a ≠ c) (h : Missing u v a b) :
    ¬Missing u v c b := by
  intro h'
  rcases deleted_equal h h' with he | he
  · exact hne he.1
  · exact hne (he.1.trans he.2)

private theorem in_together {size pages : I → Nat} {x y : Vertex size pages} {i : I}
    (hx : x ∈ clique size pages i) (ht : Together size pages x y) :
    y ∈ clique size pages i := by
  obtain ⟨j, hx', hy⟩ := ht
  obtain rfl := owner_unique _ _ hx hx'
  exact hy

/-- The two hubs, with a third core vertex as detour, keep the entire core in one clique. -/
theorem book_localized {H : SimpleGraph S} {F : SimpleGraph I} {ty : I → Fin 10}
    (hF : TriangleFree F) {u v : S} {f : S ↪ HostVertex ty}
    (hf : MapsExcept H (host F ty) u v f) {n : Nat} (B : BookIn H n) :
    ∃ i, ∀ j, f (B.core j) ∈ clique (blockSize ty) (pageCount ty) i := by
  have hn := B.three_le
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨1, by omega⟩
  let r : Fin n := ⟨2, by omega⟩
  have hp : p.val < 2 := by change (0 : Nat) < 2; decide
  have hq : q.val < 2 := by change (1 : Nat) < 2; decide
  have hpq : p ≠ q := fun h => by have := congrArg Fin.val h; simp [p, q] at this
  have hpr : p ≠ r := fun h => by have := congrArg Fin.val h; simp [p, r] at this
  have hqr : q ≠ r := fun h => by have := congrArg Fin.val h; simp [q, r] at this
  have step (i j : Fin n) := @surviving_core_edge_local _ _ H F ty hF u v f hf n B i j
  have pair : Together (blockSize ty) (pageCount ty) (f (B.core p)) (f (B.core q)) := by
    by_cases h : Missing u v (B.core p) (B.core q)
    · have h₁ := other_right (B.core.injective.ne hqr) h
      have h₂ := other_left (B.core.injective.ne hpr) h
      exact together_trans (step p r ⟨hpr, Or.inl hp⟩ h₁)
        (step r q ⟨hqr.symm, Or.inr hq⟩ h₂)
    · exact step p q ⟨hpq, Or.inl hp⟩ h
  obtain ⟨i, hpi, hqi⟩ := pair
  refine ⟨i, ?_⟩
  intro x
  by_cases ex : x = p
  · simpa [ex] using hpi
  by_cases ey : x = q
  · simpa [ey] using hqi
  by_cases h : Missing u v (B.core p) (B.core x)
  · have hx := other_left (B.core.injective.ne hpq) h
    exact in_together hqi (step q x ⟨Ne.symm ey, Or.inl hq⟩ hx)
  · exact in_together hpi (step p x ⟨Ne.symm ex, Or.inl hp⟩ h)

def coreImage {H : SimpleGraph S} {n : Nat} (B : BookIn H n) (f : S ↪ V) : Finset V :=
  Finset.univ.map (B.core.trans f)

private theorem mem_coreImage {H : SimpleGraph S} {n : Nat} (B : BookIn H n) (f : S ↪ V)
    (i : Fin n) : f (B.core i) ∈ coreImage B f := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- From an ordinary witness on a source containing the two books and their matching, every
core image fills its designated clique at a single host role of the precise source type. -/
theorem localize_book_pair {H : SimpleGraph S} {F : SimpleGraph I} {ty : I → Fin 10}
    (hF : TriangleFree F) {u v : S} {f : S ↪ HostVertex ty} (hf : MapsExcept H (host F ty) u v f)
    (c : Fin 10) (A : BookIn H (20 + c.val)) (B : BookIn H (50 - c.val))
    (dis : ∀ i j, A.core i ≠ B.core j)
    {a₀ a₁ : Fin (20 + c.val)} {b₀ b₁ : Fin (50 - c.val)} (ha : a₀ ≠ a₁)
    (m₀ : H.Adj (A.core a₀) (B.core b₀)) (m₁ : H.Adj (A.core a₁) (B.core b₁)) :
    ∃ i, ty i = c ∧ coreImage A f = clique (blockSize ty) (pageCount ty) (.primary i) ∧
      coreImage B f = clique (blockSize ty) (pageCount ty) (.secondary i) := by
  classical
  obtain ⟨a, hA⟩ := book_localized hF hf A
  obtain ⟨b, hB⟩ := book_localized hF hf B
  have hp : coreImage A f ⊆ clique (blockSize ty) (pageCount ty) a := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hA i
  have hq : coreImage B f ⊆ clique (blockSize ty) (pageCount ty) b := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hB i
  have hd : Disjoint (coreImage A f) (coreImage B f) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨j, _, e⟩ := Finset.mem_map.mp hz'
    exact dis i j (f.injective e.symm)
  have edge (i j) (e : H.Adj (A.core i) (B.core j)) (s : ¬Missing u v (A.core i) (B.core j)) :
      ∃ x ∈ coreImage A f, ∃ y ∈ coreImage B f, (host F ty).Adj x y :=
    ⟨_, mem_coreImage A f i, _, mem_coreImage B f j, hf _ _ e s⟩
  have hm : ∃ x ∈ coreImage A f, ∃ y ∈ coreImage B f, (host F ty).Adj x y := by
    by_cases h : Missing u v (A.core a₀) (B.core b₀)
    · apply edge a₁ b₁ m₁
      intro h'
      rcases deleted_equal h h' with he | he
      · exact ha (A.core.injective he.1)
      · exact dis a₀ b₁ he.1
    · exact edge a₀ b₀ m₀ h
  obtain ⟨i, he, _, _, h₁, h₂⟩ := localize_pair F ty c (by simp [coreImage])
    (by simp [coreImage]) hd hp hq hm
  exact ⟨i, he, h₁, h₂⟩

theorem internal_adj (G : SimpleGraph I) (size pages : I → Nat) {i : I} {x y : Vertex size pages}
    (hx : x ∈ clique size pages i) (hy : y ∈ clique size pages i) (he : x ≠ y) :
    (physical G size pages).Adj x y := by
  obtain ⟨a, rfl⟩ := (mem_clique _ _).mp hx
  obtain ⟨b, rfl⟩ := (mem_clique _ _).mp hy
  exact ⟨he, Or.inl rfl⟩

theorem linked_adj (G : SimpleGraph I) (size pages : I → Nat) {i j : I} {x y : Vertex size pages}
    (hg : G.Adj i j) (hx : x ∈ clique size pages i) (hy : y ∈ clique size pages j) :
    (physical G size pages).Adj x y := by
  have hne : x ≠ y := fun e => hg.ne (owner_unique _ _ (e ▸ hx) hy)
  obtain ⟨a, rfl⟩ := (mem_clique _ _).mp hx
  obtain ⟨b, rfl⟩ := (mem_clique _ _).mp hy
  exact ⟨hne, Or.inr hg⟩

/-- The surviving contact of a page with a book edge's other end forces the missing contact. -/
theorem replace_clique_contact (G : SimpleGraph I) (size pages : I → Nat)
    {i : I} {x y z : Vertex size pages} (hx : x ∈ clique size pages i)
    (hy : y ∈ clique size pages i) (hadj : (physical G size pages).Adj x z) (hne : y ≠ z) :
    (physical G size pages).Adj y z := by
  obtain ⟨a, rfl⟩ := (mem_clique _ _).mp hx
  obtain ⟨b, rfl⟩ := (mem_clique _ _).mp hy
  cases z with
  | page _ _ => exact hadj
  | core _ _ => exact ⟨hne, hadj.2⟩

theorem host_primary_adj_iff {F : SimpleGraph I} {ty : I → Fin 10} {i j : I} (hij : i ≠ j)
    {x y : HostVertex ty} (hx : x ∈ clique (blockSize ty) (pageCount ty) (.primary i))
    (hy : y ∈ clique (blockSize ty) (pageCount ty) (.primary j)) :
    (host F ty).Adj x y ↔ F.Adj i j := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (mem_clique _ _).mp hx
    obtain ⟨b, rfl⟩ := (mem_clique _ _).mp hy
    exact h.2.resolve_left (fun he => hij (Block.primary.inj he))
  · intro h
    exact linked_adj (designated F) _ _ (i := .primary i) (j := .primary j) h hx hy

end Bootstrap.Localization

#print axioms Bootstrap.Localization.common_after_deletion
#print axioms Bootstrap.Localization.book_localized
#print axioms Bootstrap.Localization.localize_book_pair
#print axioms Bootstrap.Localization.replace_clique_contact
#print axioms Bootstrap.Localization.host_primary_adj_iff
