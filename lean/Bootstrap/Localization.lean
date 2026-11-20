import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace Bootstrap.Localization

variable {I : Type*}

def TriangleFree (G : SimpleGraph I) : Prop :=
  ∀ ⦃i j k : I⦄, G.Adj i j → G.Adj i k → G.Adj j k → False

inductive Block (I : Type*) where
  | primary (i : I)
  | secondary (i : I)

def designated (F : SimpleGraph I) : SimpleGraph (Block I) where
  Adj
    | .primary i, .primary j => F.Adj i j
    | .primary i, .secondary j => i = j
    | .secondary i, .primary j => i = j
    | .secondary _, .secondary _ => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact F.symm h
    · exact h.symm
    · exact h.symm
    · exact h
  loopless := by
    intro x h
    cases x
    · exact F.irrefl h
    · exact h

theorem designated_triangleFree {F : SimpleGraph I} (hf : TriangleFree F) :
    TriangleFree (designated F) := by
  intro i j k hij hik hjk
  cases i <;> cases j <;> cases k <;> simp_all [designated, TriangleFree]
  exact hf hij hik hjk

inductive Vertex (size pages : I → Nat) where
  | core (i : I) (a : Fin (size i))
  | page (i : I) (a : Fin (pages i))

variable (G : SimpleGraph I) (size pages : I → Nat)

def physical : SimpleGraph (Vertex size pages) where
  Adj
    | .core i a, .core j b =>
        (Vertex.core i a : Vertex size pages) ≠ .core j b ∧ (i = j ∨ G.Adj i j)
    | .core i _, .page j _ => i = j
    | .page i _, .core j _ => i = j
    | .page _ _, .page _ _ => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact ⟨Ne.symm h.1, h.2.elim (fun e => Or.inl e.symm) (fun e => Or.inr (G.symm e))⟩
    · exact h.symm
    · exact h.symm
    · exact h
  loopless := by
    intro x h
    cases x
    · exact h.1 rfl
    · exact h

def coreEmbedding (i : I) : Fin (size i) ↪ Vertex size pages where
  toFun := Vertex.core i
  inj' := by intro a b h; cases h; rfl

def clique (i : I) : Finset (Vertex size pages) :=
  Finset.univ.map (coreEmbedding size pages i)

@[simp] theorem card_clique (i : I) : (clique size pages i).card = size i := by
  simp [clique]

theorem mem_clique {i : I} {x : Vertex size pages} :
    x ∈ clique size pages i ↔ ∃ a : Fin (size i), Vertex.core i a = x := by
  simp [clique, coreEmbedding]

theorem core_mem (i : I) (a : Fin (size i)) :
    Vertex.core i a ∈ clique size pages i := (mem_clique size pages).mpr ⟨a, rfl⟩

theorem common_cross {i j : I} (hi : i ≠ j) (a : Fin (size i)) (b : Fin (size j))
    (hxy : (physical G size pages).Adj (.core i a) (.core j b)) (hf : TriangleFree G)
    {z} (hx : (physical G size pages).Adj (.core i a) z)
    (hy : (physical G size pages).Adj (.core j b) z) :
    z ∈ clique size pages i ∨ z ∈ clique size pages j := by
  cases z with
  | page k e => exact False.elim (hi (hx.trans hy.symm))
  | core k c =>
    by_cases h : i = k
    · subst k; exact Or.inl (core_mem _ _ _ _)
    · by_cases h' : j = k
      · subst k; exact Or.inr (core_mem _ _ _ _)
      · exact False.elim (hf (hxy.2.resolve_left hi) (hx.2.resolve_left h) (hy.2.resolve_left h'))

theorem neighbor_page {i : I} (a : Fin (pages i)) {z}
    (h : (physical G size pages).Adj (.page i a) z) :
    z ∈ clique size pages i := by
  cases z with
  | page _ _ => exact False.elim h
  | core j c =>
    change i = j at h
    subst j
    exact core_mem _ _ _ _

def DistinctCommon {V : Type*} (H : SimpleGraph V) (N : Nat) (x y : V) : Prop :=
  ∃ w : Fin N ↪ V, ∀ k, w k ∈ H.commonNeighbors x y

private theorem card_le_target {V : Type*} {N : Nat} (w : Fin N ↪ V) (s : Finset V)
    (h : ∀ k, w k ∈ s) : N ≤ s.card := by
  have hs : Finset.univ.map w ⊆ s := by
    intro z hz
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hz
    exact h k
  simpa using Finset.card_le_card hs

theorem page_common_bound {i : I} (a : Fin (pages i)) (y : Vertex size pages)
    (hxy : (physical G size pages).Adj (.page i a) y)
    {N : Nat} (hc : DistinctCommon (physical G size pages) N (.page i a) y) :
    N ≤ size i - 1 := by
  classical
  obtain ⟨w, hw⟩ := hc
  have hy := neighbor_page G size pages a hxy
  have hb := card_le_target w ((clique size pages i).erase y) (fun k =>
    Finset.mem_erase.mpr ⟨(@SimpleGraph.Adj.ne _ (physical G size pages) _ _ (hw k).2).symm, neighbor_page G size pages a (hw k).1⟩)
  simpa only [Finset.card_erase_of_mem hy, card_clique] using hb

theorem cross_common_bound {i j : I} (hij : i ≠ j) (a : Fin (size i)) (b : Fin (size j))
    (hxy : (physical G size pages).Adj (.core i a) (.core j b)) (hf : TriangleFree G)
    {N : Nat} (hc : DistinctCommon (physical G size pages) N (.core i a) (.core j b)) :
    N ≤ size i + size j - 2 := by
  classical
  obtain ⟨w, hw⟩ := hc
  let s := clique size pages i ∪ clique size pages j
  let x : Vertex size pages := .core i a
  let y : Vertex size pages := .core j b
  have hx : x ∈ s := Finset.mem_union_left _ (core_mem _ _ _ _)
  have hy : y ∈ s.erase x :=
    Finset.mem_erase.mpr ⟨hxy.ne.symm, Finset.mem_union_right _ (core_mem _ _ _ _)⟩
  have hb := card_le_target w ((s.erase x).erase y) (fun k =>
    Finset.mem_erase.mpr ⟨(@SimpleGraph.Adj.ne _ (physical G size pages) _ _ (hw k).2).symm, Finset.mem_erase.mpr
      ⟨(@SimpleGraph.Adj.ne _ (physical G size pages) _ _ (hw k).1).symm, Finset.mem_union.mpr
        (common_cross G size pages hij a b hxy hf (hw k).1 (hw k).2)⟩⟩)
  rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx] at hb
  have hu : s.card ≤ size i + size j := by
    simpa only [s, card_clique] using Finset.card_union_le (clique size pages i) (clique size pages j)
  omega

theorem distinctCommon_symm {V : Type*} {H : SimpleGraph V} {N : Nat} {x y : V}
    (h : DistinctCommon H N x y) : DistinctCommon H N y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, fun k => ⟨(hw k).2, (hw k).1⟩⟩

theorem large_common_internal (hs : ∀ i, size i ≤ 50) (hf : TriangleFree G)
    {x y : Vertex size pages} (hxy : (physical G size pages).Adj x y)
    (hc : DistinctCommon (physical G size pages) 102 x y) :
    ∃ i, x ∈ clique size pages i ∧ y ∈ clique size pages i := by
  cases x with
  | page i a =>
    have h := page_common_bound G size pages a _ hxy hc
    have := hs i
    omega
  | core i a =>
    cases y with
    | page j b =>
      have h := page_common_bound G size pages b _ ((physical G size pages).symm hxy)
        (distinctCommon_symm hc)
      have := hs j
      omega
    | core j b =>
      by_cases h : i = j
      · subst j
        exact ⟨i, core_mem _ _ _ _, core_mem _ _ _ _⟩
      · have hbound := cross_common_bound G size pages h a b hxy hf hc
        have hi := hs i
        have hj := hs j
        omega

def blockSize (ty : I → Fin 10) : Block I → Nat
  | .primary i => 20 + (ty i).val
  | .secondary i => 50 - (ty i).val

def pageCount (ty : I → Fin 10) (b : Block I) : Nat :=
  103 * (2 * blockSize ty b - 3)

abbrev HostVertex (ty : I → Fin 10) := Vertex (blockSize ty) (pageCount ty)

def host (F : SimpleGraph I) (ty : I → Fin 10) : SimpleGraph (HostVertex ty) :=
  physical (designated F) (blockSize ty) (pageCount ty)

theorem blockSize_le (ty : I → Fin 10) (b : Block I) : blockSize ty b ≤ 50 := by
  cases b with
  | primary i => change 20 + (ty i).val ≤ 50; have := (ty i).isLt; omega
  | secondary i => exact Nat.sub_le _ _

theorem host_large_common_internal (F : SimpleGraph I) (ty : I → Fin 10)
    (hf : TriangleFree F) {x y : HostVertex ty}
    (hxy : (host F ty).Adj x y) (hc : DistinctCommon (host F ty) 102 x y) :
    ∃ b, x ∈ clique (blockSize ty) (pageCount ty) b ∧ y ∈ clique (blockSize ty) (pageCount ty) b :=
  large_common_internal _ _ _ (blockSize_le ty) (designated_triangleFree hf) hxy hc

/-- Capacity and the surviving matching edge determine and fill both designated cliques. -/
theorem localize_pair (F : SimpleGraph I) (ty : I → Fin 10) (c : Fin 10)
    {P Q : Finset (HostVertex ty)} {A B : Block I}
    (hp : P.card = 20 + c.val) (hq : Q.card = 50 - c.val) (hd : Disjoint P Q)
    (hP : P ⊆ clique (blockSize ty) (pageCount ty) A)
    (hQ : Q ⊆ clique (blockSize ty) (pageCount ty) B)
    (hm : ∃ x ∈ P, ∃ y ∈ Q, (host F ty).Adj x y) :
    ∃ i : I, ty i = c ∧ A = .primary i ∧ B = .secondary i ∧
      P = clique (blockSize ty) (pageCount ty) (.primary i) ∧
      Q = clique (blockSize ty) (pageCount ty) (.secondary i) := by
  classical
  have hps := Finset.card_le_card hP
  have hqs := Finset.card_le_card hQ
  rw [hp, card_clique] at hps
  rw [hq, card_clique] at hqs
  have hne : A ≠ B := by
    intro h
    subst B
    have hs := Finset.card_le_card (Finset.union_subset hP hQ)
    rw [Finset.card_union_of_disjoint hd, hp, hq, card_clique] at hs
    have hb := blockSize_le ty A
    have ht := c.isLt
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := hm
  obtain ⟨a, rfl⟩ := (mem_clique _ _).mp (hP hx)
  obtain ⟨b, rfl⟩ := (mem_clique _ _).mp (hQ hy)
  have hab : (designated F).Adj A B := hxy.2.resolve_left hne
  have hc := c.isLt
  cases B with
  | primary i =>
    change 50 - c.val ≤ 20 + (ty i).val at hqs
    have := (ty i).isLt
    omega
  | secondary j =>
    cases A with
    | secondary i => exact False.elim hab
    | primary i =>
      change i = j at hab
      subst j
      change 20 + c.val ≤ 20 + (ty i).val at hps
      change 50 - c.val ≤ 50 - (ty i).val at hqs
      have hti := (ty i).isLt
      have he : ty i = c := Fin.ext (by omega)
      refine ⟨i, he, rfl, rfl, ?_, ?_⟩
      · apply Finset.eq_of_subset_of_card_le hP
        simp [card_clique, blockSize, hp, he]
      · apply Finset.eq_of_subset_of_card_le hQ
        simp [card_clique, blockSize, hq, he]

end Bootstrap.Localization

#print axioms Bootstrap.Localization.designated_triangleFree
#print axioms Bootstrap.Localization.page_common_bound
#print axioms Bootstrap.Localization.cross_common_bound
#print axioms Bootstrap.Localization.host_large_common_internal
#print axioms Bootstrap.Localization.localize_pair
