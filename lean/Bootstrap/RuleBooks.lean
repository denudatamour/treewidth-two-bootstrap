import Bootstrap.BookWitness

namespace Bootstrap.Localization

variable {R I : Type*}

theorem blockSize_three (c : R → Fin 10) (b : Block R) : 3 ≤ blockSize c b := by
  cases b with
  | primary i => change 3 ≤ 20 + (c i).val; omega
  | secondary i => change 3 ≤ 50 - (c i).val; have := (c i).isLt; omega

def hubIdx (c : R → Fin 10) (b : Block R) (k : Fin 2) : Fin (blockSize c b) :=
  ⟨k.val, by have := blockSize_three c b; have := k.isLt; omega⟩

def portIdx (c : R → Fin 10) (r : R) (k : Fin 2) : Fin (blockSize c (.primary r)) :=
  hubIdx c (.primary r) k

def portPoint (c : R → Fin 10) (port : R → R → Fin 2) (r s : R) : HostVertex c :=
  .core (.primary r) (portIdx c r (port r s))

/-- Edges 0,...,s-2 are the fan at 0 and the remaining edges are the fan at 1. -/
def pageLo (c : R → Fin 10) (b : Block R) (k : Fin (pageCount c b)) : Fin (blockSize c b) :=
  ⟨if k.val / 103 < blockSize c b - 1 then 0 else 1, by
    have := blockSize_three c b
    split <;> omega⟩

def pageHi (c : R → Fin 10) (b : Block R) (k : Fin (pageCount c b)) : Fin (blockSize c b) :=
  ⟨if k.val / 103 < blockSize c b - 1 then k.val / 103 + 1
    else k.val / 103 - (blockSize c b - 1) + 2, by
    have h := k.isLt
    change k.val < 103 * (2 * blockSize c b - 3) at h
    have := blockSize_three c b
    split <;> omega⟩

theorem pageLo_lt_hi (c : R → Fin 10) (b : Block R) (k : Fin (pageCount c b)) :
    (pageLo c b k).val < (pageHi c b k).val := by
  simp only [pageLo, pageHi]
  split <;> omega

inductive Arc (L : SimpleGraph R) (code : R → Fin 10) (port : R → R → Fin 2) :
    HostVertex code → HostVertex code → Prop
  | book (b : Block R) (a d : Fin (blockSize code b)) (h : CoreEdge a d) :
      Arc L code port (.core b a) (.core b d)
  | pageLeft (b : Block R) (k : Fin (pageCount code b)) :
      Arc L code port (.page b k) (.core b (pageLo code b k))
  | pageRight (b : Block R) (k : Fin (pageCount code b)) :
      Arc L code port (.page b k) (.core b (pageHi code b k))
  | matching (r : R) (k : Fin 2) :
      Arc L code port (.core (.primary r) (hubIdx code (.primary r) k))
        (.core (.secondary r) (hubIdx code (.secondary r) k))
  | logical (r s : R) (h : L.Adj r s) :
      Arc L code port (portPoint code port r s) (portPoint code port s r)

def owner {size pages : I → Nat} : Vertex size pages → I
  | .core b _ => b
  | .page b _ => b

theorem Arc.ne {L : SimpleGraph R} {c : R → Fin 10} {port : R → R → Fin 2}
    {x y : HostVertex c} (h : Arc L c port x y) : x ≠ y := by
  cases h with
  | book b a d e => exact (coreEmbedding _ _ b).injective.ne e.1
  | pageLeft b k => intro h; cases h
  | pageRight b k => intro h; cases h
  | matching r k => intro h; cases h
  | logical r s e =>
    intro h
    exact e.ne (Block.primary.inj (congrArg owner h))

def rule (L : SimpleGraph R) (code : R → Fin 10) (port : R → R → Fin 2) :
    SimpleGraph (HostVertex code) where
  Adj x y := Arc L code port x y ∨ Arc L code port y x
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h.elim (fun e => e.ne rfl) (fun e => e.ne rfl)

private def edgeNumber (s lo hi : Nat) : Nat :=
  if lo = 0 then hi - 1 else (s - 1) + (hi - 2)

private def makePage (c : R → Fin 10) (b : Block R) (a d : Fin (blockSize c b))
    (_ha : a.val < 2) (had : a.val < d.val) (k : Fin 103) : Fin (pageCount c b) :=
  ⟨103 * edgeNumber (blockSize c b) a.val d.val + k.val, by
    change 103 * edgeNumber _ _ _ + _ < 103 * (2 * blockSize c b - 3)
    have := d.isLt
    have := k.isLt
    have := blockSize_three c b
    unfold edgeNumber
    split <;> omega⟩

private theorem makePage_div (c : R → Fin 10) (b : Block R) (a d : Fin (blockSize c b))
    (ha : a.val < 2) (had : a.val < d.val) (k : Fin 103) :
    (makePage c b a d ha had k).val / 103 = edgeNumber (blockSize c b) a.val d.val := by
  change (103 * edgeNumber _ _ _ + k.val) / 103 = _
  have := k.isLt
  omega

private theorem makePage_lo (c : R → Fin 10) (b : Block R) (a d : Fin (blockSize c b))
    (ha : a.val < 2) (had : a.val < d.val) (k : Fin 103) :
    pageLo c b (makePage c b a d ha had k) = a := by
  apply Fin.ext
  change (if _ / 103 < _ then 0 else 1) = a.val
  rw [makePage_div]
  have ht := d.isLt
  have hs := blockSize_three c b
  by_cases hz : a.val = 0 <;> simp only [edgeNumber, hz, if_true, if_false]
  all_goals split <;> omega

private theorem makePage_hi (c : R → Fin 10) (b : Block R) (a d : Fin (blockSize c b))
    (ha : a.val < 2) (had : a.val < d.val) (k : Fin 103) :
    pageHi c b (makePage c b a d ha had k) = d := by
  apply Fin.ext
  change (if _ / 103 < _ then _ / 103 + 1 else _ / 103 - _ + 2) = d.val
  simp only [makePage_div]
  have ht := d.isLt
  have hs := blockSize_three c b
  by_cases hz : a.val = 0 <;> simp only [edgeNumber, hz, if_true, if_false]
  all_goals split <;> omega

private def slot {size pages : I → Nat} : Vertex size pages → Nat
  | .core _ j => j.val
  | .page _ j => j.val

private def assignedPages (c : R → Fin 10) (b : Block R) (a d : Fin (blockSize c b))
    (ha : a.val < 2) (had : a.val < d.val) : Fin 103 ↪ HostVertex c where
  toFun k := .page b (makePage c b a d ha had k)
  inj' := by
    intro i j h
    have he := congrArg slot h
    change 103 * edgeNumber _ _ _ + i.val = 103 * edgeNumber _ _ _ + j.val at he
    exact Fin.ext (by omega)

private theorem book_thick_ordered (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2)
    (b : Block R) (a d : Fin (blockSize c b)) (ha : a.val < 2) (had : a.val < d.val) :
    DistinctCommon (rule L c port) 103 (.core b a) (.core b d) := by
  refine ⟨assignedPages c b a d ha had, fun k => ?_⟩
  let p := makePage c b a d ha had k
  have lo : pageLo c b p = a := makePage_lo c b a d ha had k
  have hi : pageHi c b p = d := makePage_hi c b a d ha had k
  have h₁ : Arc L c port (.page b p) (.core b (pageLo c b p)) := .pageLeft b p
  have h₂ : Arc L c port (.page b p) (.core b (pageHi c b p)) := .pageRight b p
  rw [lo] at h₁
  rw [hi] at h₂
  exact ⟨Or.inr h₁, Or.inr h₂⟩

def ruleBook (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2) (b : Block R) :
    BookIn (rule L c port) (blockSize c b) where
  three_le := blockSize_three c b
  core := coreEmbedding (blockSize c) (pageCount c) b
  thick := by
    intro a d e
    refine ⟨Or.inl (.book b a d e), ?_⟩
    have hn : a.val ≠ d.val := fun h => e.1 (Fin.ext h)
    by_cases had : a.val < d.val
    · apply book_thick_ordered L c port b a d _ had
      rcases e.2 with h | h <;> omega
    · apply distinctCommon_symm
      apply book_thick_ordered L c port b d a _ (by omega)
      rcases e.2 with h | h <;> omega

private theorem mapped_core {V : Type*} (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2)
    (b : Block R) (f : HostVertex c ↪ V) :
    coreImage (ruleBook L c port b) f = (clique (blockSize c) (pageCount c) b).map f := by
  simp only [coreImage, clique, Finset.map_map]
  rfl

theorem localize_rule_role (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2)
    {F : SimpleGraph I} {ty : I → Fin 10} (hF : TriangleFree F)
    {u v : HostVertex c} {f : HostVertex c ↪ HostVertex ty}
    (hf : MapsExcept (rule L c port) (host F ty) u v f) (r : R) :
    ∃ i, ty i = c r ∧
      (clique (blockSize c) (pageCount c) (.primary r)).map f =
        clique (blockSize ty) (pageCount ty) (.primary i) ∧
      (clique (blockSize c) (pageCount c) (.secondary r)).map f =
        clique (blockSize ty) (pageCount ty) (.secondary i) := by
  let A := ruleBook L c port (.primary r)
  let B := ruleBook L c port (.secondary r)
  have dis : ∀ a b, A.core a ≠ B.core b := by intro a b h; cases h
  have ha : hubIdx c (.primary r) 0 ≠ hubIdx c (.primary r) 1 := by
    intro e
    have he : (0 : Nat) = 1 := congrArg Fin.val e
    omega
  have hm (k : Fin 2) : (rule L c port).Adj (A.core (hubIdx c (.primary r) k))
      (B.core (hubIdx c (.secondary r) k)) := Or.inl (.matching r k)
  obtain ⟨i, he, hA, hB⟩ := localize_book_pair hF hf (c r) A B dis ha (hm 0) (hm 1)
  exact ⟨i, he, (mapped_core L c port (.primary r) f).symm.trans hA,
    (mapped_core L c port (.secondary r) f).symm.trans hB⟩

/-- Entire source roles occupy different host roles in every ordinary one-deletion embedding. -/
theorem localize_rule (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2)
    {F : SimpleGraph I} {ty : I → Fin 10} (hF : TriangleFree F)
    {u v : HostVertex c} {f : HostVertex c ↪ HostVertex ty}
    (hf : MapsExcept (rule L c port) (host F ty) u v f) :
    ∃ g : R ↪ I, ∀ r, ty (g r) = c r ∧
      (clique (blockSize c) (pageCount c) (.primary r)).map f =
        clique (blockSize ty) (pageCount ty) (.primary (g r)) ∧
      (clique (blockSize c) (pageCount c) (.secondary r)).map f =
        clique (blockSize ty) (pageCount ty) (.secondary (g r)) := by
  classical
  choose g hty hP hQ using fun r => localize_rule_role L c port hF hf r
  have hg : Function.Injective g := by
    intro r s hrs
    let x : HostVertex c := .core (.primary r) (hubIdx c (.primary r) 0)
    have hx : x ∈ clique (blockSize c) (pageCount c) (.primary r) := core_mem _ _ _ _
    have hy : f x ∈ (clique (blockSize c) (pageCount c) (.primary s)).map f := by
      rw [hP s, ← hrs, ← hP r]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := Finset.mem_map.mp hy
    have eyx := f.injective e
    subst y
    exact Block.primary.inj (owner_unique _ _ hx hy)
  exact ⟨⟨g, hg⟩, fun r => ⟨hty r, hP r, hQ r⟩⟩

end Bootstrap.Localization

#print axioms Bootstrap.Localization.ruleBook
#print axioms Bootstrap.Localization.localize_rule_role
#print axioms Bootstrap.Localization.localize_rule
