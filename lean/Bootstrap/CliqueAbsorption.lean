import Bootstrap.HighBirth
import Mathlib.GroupTheory.Perm.Basic

namespace Bootstrap.DegreeTwo

open scoped Classical

variable {W V : Type*}

/-- Use two prescribed roles at prescribed distinct places while keeping the whole source injective. -/
theorem embed_pair_in [Fintype W] (S : Finset V) (room : Fintype.card W ≤ S.card)
    {a b : W} (ab : a ≠ b) {x y : V} (xs : x ∈ S) (ys : y ∈ S) (xy : x ≠ y) :
    ∃ f : W ↪ V, f a = x ∧ f b = y ∧ ∀ i, f i ∈ S := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (by simpa : Fintype.card W ≤ Fintype.card S)
  let p : S := ⟨x,xs⟩
  let q : S := ⟨y,ys⟩
  let g := f.trans (Equiv.swap (f a) p).toEmbedding
  have ga : g a = p := Equiv.swap_apply_left _ _
  have pg : p ≠ g b := fun h => ab (g.injective (ga.trans h))
  have pq : p ≠ q := fun h => xy (congrArg Subtype.val h)
  let k := g.trans (Equiv.swap (g b) q).toEmbedding
  have ka : k a = p := by
    change Equiv.swap (g b) q (g a) = p
    rw [ga,Equiv.swap_apply_of_ne_of_ne pg pq]
  have kb : k b = q := Equiv.swap_apply_left _ _
  exact ⟨⟨fun i => (k i).1,fun _ _ h => k.injective (Subtype.ext h)⟩,
    congrArg Subtype.val ka,congrArg Subtype.val kb,fun i => (k i).2⟩

def CliqueOn (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → G.Adj x y

theorem CliqueOn.mono {G D : SimpleGraph V} {S : Finset V} (h : CliqueOn G S) (hd : G ≤ D) :
    CliqueOn D S := fun _ a _ b ne => hd (h a b ne)

theorem clique_absorbs_contact [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    {a l r : W} (N : TwoNeighbours H a l r) (S : Finset V) (room : Fintype.card W ≤ S.card)
    (full : CliqueOn G S) {z x y : V} (free : z ∉ S) (xs : x ∈ S) (ys : y ∈ S)
    (contact : G.Adj z x) : (step H G).Adj z y := by
  classical
  by_cases same : x = y
  · exact same ▸ Or.inl contact
  obtain ⟨f,fl,fr,inside⟩ := embed_pair_in S room N.distinct xs ys same
  have copy : FullCopy H G f := fun i j ij => full (inside i) (inside j) (f.injective.ne ij.ne)
  have outside : Outside f z := fun i e => free (e ▸ inside i)
  have h := one_step H G f copy N z outside (fl.symm ▸ contact)
  exact fr ▸ h

/-- Given a clique and two vertices complete to it, the endpoints of any rule edge
can be moved to those two vertices. -/
theorem clique_fills_external_pair [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    {u v : W} (edge : H.Adj u v) (S : Finset V) (room : Fintype.card W ≤ S.card)
    (full : CliqueOn G S) {x y : V} (xs : x ∉ S) (ys : y ∉ S) (xy : x ≠ y)
    (xn : ∀ z ∈ S, G.Adj x z) (yn : ∀ z ∈ S, G.Adj y z) : (step H G).Adj x y := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (by simpa : Fintype.card W ≤ Fintype.card S)
  let base : W ↪ V := ⟨fun i => (f i).1,fun _ _ h => f.injective (Subtype.ext h)⟩
  have inside (i : W) : base i ∈ S := (f i).2
  have xf : Outside base x := fun i eq => xs (eq ▸ inside i)
  have yf : Outside base y := fun i eq => ys (eq ▸ inside i)
  let g := putTwo base u v x y xf yf xy
  have gu : g u = x := putTwo_left _ _ _ _ _ _ _ _ edge.ne
  have gv : g v = y := putTwo_right _ _ _ _ _ _ _ _
  have whereAt (i : W) : g i ∈ S ∨ i = u ∨ i = v := by
    by_cases iu : i=u
    · exact Or.inr (Or.inl iu)
    by_cases iv : i=v
    · exact Or.inr (Or.inr iv)
    · exact Or.inl ((putTwo_away _ _ _ _ _ _ _ _ iu iv).symm ▸ inside i)
  refine Or.inr ⟨u,v,g,edge,gu,gv,?_⟩
  intro i j ij hn
  rcases whereAt i with hi|rfl|rfl <;> rcases whereAt j with hj|rfl|rfl
  · exact full hi hj (g.injective.ne ij.ne)
  · rw [gu]; exact G.symm (xn _ hi)
  · rw [gv]; exact G.symm (yn _ hi)
  · rw [gu]; exact xn _ hj
  · exact False.elim (H.irrefl ij)
  · exact False.elim (hn (Or.inl ⟨rfl,rfl⟩))
  · rw [gv]; exact yn _ hj
  · exact False.elim (hn (Or.inr ⟨rfl,rfl⟩))
  · exact False.elim (H.irrefl ij)

/-- The union of all old cliques touching S is a clique two rounds later. In fact only
one old neighbour in S for each external vertex of U is necessary. -/
theorem absorbs_touching [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    {a l r : W} (N : TwoNeighbours H a l r) (S U : Finset V) (room : Fintype.card W ≤ S.card)
    (full : CliqueOn G S) (contact : ∀ z ∈ U, z ∉ S → ∃ s ∈ S, G.Adj z s) :
    CliqueOn (step H (step H G)) U := by
  classical
  have all (z : V) (hz : z ∈ U) (zout : z ∉ S) : ∀ k ∈ S, (step H G).Adj z k := by
    obtain ⟨s,hs,adj⟩ := contact z hz zout
    exact fun k hk => clique_absorbs_contact H G N S room full zout hs hk adj
  intro x hx y hy hxy
  by_cases xs : x ∈ S
  · by_cases ys : y ∈ S
    · exact Or.inl (Or.inl (full xs ys hxy))
    · exact Or.inl ((step H G).symm (all y hy ys x xs))
  · by_cases ys : y ∈ S
    · exact Or.inl (all x hx xs y ys)
    · exact clique_fills_external_pair H (step H G) N.left S room (full.mono (le_step H G))
        xs ys hxy (all _ hx xs) (all _ hy ys)

def OneMonochrome (H : SimpleGraph W) : Prop := ∃ (col : W → Bool) (u v : W),
  H.Adj u v ∧ col u = col v ∧ ∀ i j, H.Adj i j → col i = col j →
     (i=u ∧ j=v) ∨ (i=v ∧ j=u)

private theorem fill_shore [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (mono : OneMonochrome H) (P Q : Finset V) (pr : Fintype.card W ≤ P.card)
    (qr : Fintype.card W ≤ Q.card) (apart : Disjoint P Q) (cross : Joined G P Q) :
    CliqueOn (step H G) P := by
  classical
  obtain ⟨color,u,v,e,same,only⟩ := mono
  intro x hx y hy hxy
  obtain ⟨fp,fu,fv,inside⟩ := embed_pair_in P pr e.ne hx hy hxy
  obtain ⟨fq⟩ := Function.Embedding.nonempty_of_card_le (by simpa : Fintype.card W ≤ Fintype.card Q)
  let val (i : W) : V := if color i = color u then fp i else (fq i).val
  have xv (i : W) (h : color i = color u) : val i = fp i := if_pos h
  have yv (i : W) (h : color i ≠ color u) : val i = (fq i).val := if_neg h
  have apart' (i j : W) : fp i ≠ (fq j).val :=
    fun he => (Finset.disjoint_left.mp apart) (inside i) (he.symm ▸ (fq j).property)
  have inj : Function.Injective val := by
    intro i j h
    by_cases hi : color i = color u <;> by_cases hj : color j = color u
    · rw [xv i hi,xv j hj] at h; exact fp.injective h
    · rw [xv i hi,yv j hj] at h; exact False.elim (apart' i j h)
    · rw [yv i hi,xv j hj] at h; exact False.elim (apart' j i h.symm)
    · rw [yv i hi,yv j hj] at h; exact fq.injective (Subtype.ext h)
  let g : W ↪ V := ⟨val,inj⟩
  refine Or.inr ⟨u,v,g,e,(xv u rfl).trans fu,(xv v same.symm).trans fv,?_⟩
  intro i j ij hn
  change G.Adj (val i) (val j)
  have diff : color i ≠ color j := fun h => hn (only _ _ ij h)
  by_cases hi : color i = color u <;> by_cases hj : color j = color u
  · exact False.elim (diff (hi.trans hj.symm))
  · rw [xv i hi,yv j hj]; exact cross _ (inside i) _ (fq j).property
  · rw [yv i hi,xv j hj]; exact G.symm (cross _ (inside j) _ (fq i).property)
  · have same' : color i = color j := by
      cases ei : color i <;> cases ej : color j <;> cases eu : color u <;> simp_all
    exact False.elim (diff same')

theorem one_monochrome_clique [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (mono : OneMonochrome H) (P Q : Finset V) (pr : Fintype.card W ≤ P.card)
    (qr : Fintype.card W ≤ Q.card) (apart : Disjoint P Q) (cross : Joined G P Q) :
    CliqueOn (step H G) (P ∪ Q) := by
  classical
  have rev : Joined G Q P := fun q hq p hp => G.symm (cross p hp q hq)
  intro x hx y hy ne
  rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
  · exact fill_shore H G mono P Q pr qr apart cross hx hy ne
  · exact Or.inl (cross x hx y hy)
  · exact Or.inl (rev x hx y hy)
  · exact fill_shore H G mono Q P qr pr apart.symm rev hx hy ne

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.absorbs_touching
#print axioms Bootstrap.DegreeTwo.one_monochrome_clique
