import Bootstrap.SubdivisionMerge
import Mathlib.Data.Finset.Max

namespace Bootstrap.Subdivision

open DegreeTwo
variable {W C E V L : Type*}

private theorem completed_copy (H : SimpleGraph W) (J : SimpleGraph V) (f : W ↪ V) {u v : W}
    (edge : H.Adj u v)
    (old : ∀ i j, H.Adj i j → ¬ ((i=u ∧ j=v) ∨ (i=v ∧ j=u)) → J.Adj (f i) (f j)) :
    FullCopy H (step H J) f := by
  classical
  have target : (step H J).Adj (f u) (f v) := Or.inr ⟨u,v,f,edge,rfl,rfl,old⟩
  intro i j e
  by_cases hit : (i=u ∧ j=v) ∨ (i=v ∧ j=u)
  · rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact target
    · exact (step H J).symm target
  · exact Or.inl (old i j e hit)

private theorem oriented_seed (D : Data C E) (J : SimpleGraph V) (f : C ⊕ E ↪ V)
    (c : C) (e : E) (edge : D.ends c e)
    (old : ∀ i j, D.rule.Adj i j →
      ¬ ((i=.inl c ∧ j=.inr e) ∨ (i=.inr e ∧ j=.inl c)) → J.Adj (f i) (f j)) :
    ∃ c', c' ≠ c ∧ FullCopy D.rule (step D.rule J) f ∧ J.Adj (f (.inl c')) (f (.inr e)) := by
  have full := completed_copy D.rule J f (u := Sum.inl c) (v := Sum.inr e) edge old
  have other (c' : C) (ne : c' ≠ c) (req : D.ends c' e) : J.Adj (f (.inl c')) (f (.inr e)) := by
    apply old (Sum.inl c') (Sum.inr e) req
    rintro (⟨eq,_⟩|⟨eq,_⟩)
    · exact ne (Sum.inl.inj eq)
    · cases eq
  rcases edge with eq | eq
  · subst c
    exact ⟨D.right e,(D.proper e).symm,full,other _ (D.proper e).symm (Or.inr rfl)⟩
  · subst c
    exact ⟨D.left e,D.proper e,full,other _ (D.proper e) (Or.inl rfl)⟩

/-- A new subdivision edge has an identified base endpoint, and the midpoint
was already joined to the image of its other base neighbour. -/
theorem birth_witness (D : Data C E) (J : SimpleGraph V) {x y : V}
    (birth : (step D.rule J).Adj x y) (absent : ¬ J.Adj x y) :
    ∃ (f : C ⊕ E ↪ V) (c c' : C) (e : E), c' ≠ c ∧ FullCopy D.rule (step D.rule J) f ∧
      J.Adj (f (.inl c')) (f (.inr e)) ∧
      ((f (.inl c) = x ∧ f (.inr e) = y) ∨ (f (.inr e) = x ∧ f (.inl c) = y)) := by
  rcases birth with h | ⟨u,v,f,edge,ux,vy,old⟩
  · exact False.elim (absent h)
  · cases u with
    | inl c =>
      cases v with
      | inl d => exact False.elim edge
      | inr e =>
        obtain ⟨c',ne,full,original⟩ := oriented_seed D J f c e edge old
        exact ⟨f,c,c',e,ne,full,original,Or.inl ⟨ux,vy⟩⟩
    | inr e =>
      cases v with
      | inr d => exact False.elim edge
      | inl c =>
        obtain ⟨c',ne,full,original⟩ := oriented_seed D J f c e edge (by
          intro i j h hn
          apply old i j h
          intro pair
          exact hn pair.symm)
        exact ⟨f,c,c',e,ne,full,original,Or.inr ⟨ux,vy⟩⟩

def Trigger [Fintype V] (D : Data C E) (J : SimpleGraph V) (label : V → L) (K : ℕ) : Prop :=
  ∃ f : C ⊕ E ↪ V, FullCopy D.rule J f ∧
    (∃ c c' : C, label (f (.inl c)) ≠ label (f (.inl c'))) ∧
    ∃ c : C, K ≤ hostDegree J (f (.inl c))

/-- If first contact does not trigger a merger, its actual base endpoint
has degree below K in the completed round. -/
theorem first_contact_low [Fintype V] (D : Data C E) (J : SimpleGraph V) (label : V → L)
    (K : ℕ) (quiet : ¬ Trigger D (step D.rule J) label K) {x y : V}
    (birth : (step D.rule J).Adj x y)
    (first : ∀ a b, label a = label x → label b = label y → ¬ J.Adj a b) :
    hostDegree (step D.rule J) x < K ∨ hostDegree (step D.rule J) y < K := by
  classical
  obtain ⟨f,c,c',e,_,full,original,order⟩ := birth_witness D J birth (first x y rfl rfl)
  have split : label (f (.inl c)) ≠ label (f (.inl c')) := by
    intro eq
    rcases order with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact first _ _ (eq.symm.trans (congrArg label hx)) (congrArg label hy) original
    · exact first _ _ (congrArg label hx) (eq.symm.trans (congrArg label hy)) (J.symm original)
  have low : hostDegree (step D.rule J) (f (.inl c)) < K := by
    by_contra h
    exact quiet ⟨f,full,⟨c,c',split⟩,c,Nat.le_of_not_gt h⟩
  rcases order with ⟨hx,_⟩ | ⟨_,hy⟩
  · exact Or.inl (hx ▸ low)
  · exact Or.inr (hy ▸ low)

def Born (H : SimpleGraph W) (G : SimpleGraph V) (t : ℕ) (x y : V) : Prop :=
  (run H G (t+1)).Adj x y ∧ ¬ (run H G t).Adj x y

theorem birth_time_unique {H : SimpleGraph W} {G : SimpleGraph V} {i j : ℕ} {x y : V}
    (a : Born H G i x y) (b : Born H G j x y) : i = j := by
  rcases Nat.lt_trichotomy i j with lt | eq | gt
  · exact False.elim (b.2 (time_mono H G (by omega : i+1 ≤ j) a.1))
  · exact eq
  · exact False.elim (a.2 (time_mono H G (by omega : j+1 ≤ i) b.1))

def Eligible [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K : ℕ) (v w : V) : Prop :=
  ∃ t, (run H G t).Adj v w ∧ hostDegree (run H G t) v < K

noncomputable def lowSet [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K : ℕ)
    (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (Eligible H G K v)

theorem mem_lowSet [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V} {K : ℕ} {v w : V} :
    w ∈ lowSet H G K v ↔ Eligible H G K v w := by
  classical
  simp [lowSet]

/-- All neighbours ever chargeable to a fixed endpoint already occur
together in a completed round in which its degree is below the threshold. -/
theorem lowSet_card [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K : ℕ) (v : V) :
    (lowSet H G K v).card ≤ K-1 := by
  classical
  let S := lowSet H G K v
  let time := fun w => if h : Eligible H G K v w then Nat.find h else 0
  have valid (w : V) (h : w ∈ S) :
      (run H G (time w)).Adj v w ∧ hostDegree (run H G (time w)) v < K := by
    have ok := mem_lowSet.mp h
    simpa only [time,dif_pos ok] using Nat.find_spec ok
  by_cases nonempty : S.Nonempty
  · obtain ⟨w,hw,latest⟩ := S.exists_max_image time nonempty
    have sub : S ⊆ (run H G (time w)).neighborFinset v := by
      intro z hz
      exact ((run H G (time w)).mem_neighborFinset v z).mpr
        (time_mono H G (latest z hz) (valid z hz).1)
    have bound := Finset.card_le_card sub
    have eq : ((run H G (time w)).neighborFinset v).card = hostDegree (run H G (time w)) v := rfl
    have low := (valid w hw).2
    change S.card ≤ K-1
    omega
  · change S.card ≤ K-1
    rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
    simp

/-- Charge any finite set of actual nonempty rounds using one newly born
oriented edge per round. The number paid for is at most (K-1) times host order. -/
theorem paid_rounds [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K : ℕ)
    (I : Finset ℕ) (pay : ℕ → V × V)
    (valid : ∀ t ∈ I, Born H G t (pay t).1 (pay t).2 ∧ hostDegree (run H G (t+1)) (pay t).1 < K) :
    I.card ≤ Fintype.card V * (K-1) := by
  classical
  let S := lowSet H G K
  let enc (v : V) : ↥(S v) ↪ Fin (K-1) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [S] using lowSet_card H G K v))
  let packed : (Σ v, ↥(S v)) ↪ V × Fin (K-1) := ⟨fun p => (p.1,enc p.1 p.2),by
    rintro ⟨v,w⟩ ⟨v',w'⟩ h
    have same : v=v' := congrArg Prod.fst h
    subst v'
    have rest : enc v w = enc v w' := congrArg Prod.snd h
    exact congrArg (Sigma.mk v) ((enc v).injective rest)⟩
  have member (i : ↥I) : (pay i).2 ∈ S (pay i).1 := by
    obtain ⟨newEdge,low⟩ := valid i i.2
    exact mem_lowSet.mpr ⟨i.1+1,newEdge.1,low⟩
  let tag : ↥I ↪ (Σ v, ↥(S v)) := ⟨fun i => ⟨(pay i).1,⟨(pay i).2,member i⟩⟩,by
    intro i j eq
    have same : pay i = pay j := congrArg (fun p : Σ v, ↥(S v) => (p.1,p.2.1)) eq
    have first := (valid i i.2).1
    rw [same] at first
    exact Subtype.ext (birth_time_unique first (valid j j.2).1)⟩
  simpa using Fintype.card_le_of_embedding (tag.trans packed)

/-- A collection of w-round windows pays for at most w times the number
of distinct starting indices, even when some of the windows overlap. -/
theorem window_card (events times : Finset ℕ) (w : ℕ)
    (cover : ∀ t ∈ times, ∃ e ∈ events, e ≤ t ∧ t < e+w) : times.card ≤ events.card*w := by
  classical
  let cells := events.product (Finset.range w)
  let add := fun p : ℕ × ℕ => p.1+p.2
  have sub : times ⊆ cells.image add := by
    intro t ht
    obtain ⟨e,he,le,lt⟩ := cover t ht
    apply Finset.mem_image.mpr
    refine ⟨(e,t-e),Finset.mem_product.mpr ⟨he,Finset.mem_range.mpr (by omega)⟩,?_⟩
    dsimp [add]
    omega
  calc
    times.card ≤ (cells.image add).card := Finset.card_le_card sub
    _ ≤ cells.card := Finset.card_image_le
    _ = events.card*w := by simp [cells]

end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.birth_witness
#print axioms Bootstrap.Subdivision.first_contact_low
#print axioms Bootstrap.Subdivision.paid_rounds
#print axioms Bootstrap.Subdivision.window_card
