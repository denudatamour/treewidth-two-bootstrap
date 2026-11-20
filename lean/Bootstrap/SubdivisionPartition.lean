import Bootstrap.SubdivisionAccounting

namespace Bootstrap.Subdivision

open DegreeTwo
variable {C E V : Type*}

structure Partition [Fintype C] [Fintype E] (D : Data C E) (J : SimpleGraph V)
    (P : Finset (Finset V)) : Prop where
  cover : ∀ x, ∃ A ∈ P, x ∈ A
  apart : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B
  live : ∀ A ∈ P, A.Nonempty
  certified : ∀ A ∈ P, Block D J A

theorem Partition.mono [Fintype C] [Fintype E] {D : Data C E} {G J : SimpleGraph V}
    {P : Finset (Finset V)} (h : Partition D G P) (grow : G ≤ J) : Partition D J P :=
  ⟨h.cover,h.apart,h.live,fun A ha => block_mono grow (h.certified A ha)⟩

noncomputable def blockOf (P : Finset (Finset V)) (x : V) : Finset V := by
  classical
  exact if h : ∃ A ∈ P, x ∈ A then Classical.choose h else ∅

theorem Partition.spec [Fintype C] [Fintype E] {D : Data C E} {J : SimpleGraph V}
    {P : Finset (Finset V)} (part : Partition D J P) (x : V) :
    blockOf P x ∈ P ∧ x ∈ blockOf P x := by
  classical
  have h := part.cover x
  simpa only [blockOf,dif_pos h] using Classical.choose_spec h

theorem Partition.label_eq [Fintype C] [Fintype E] {D : Data C E} {J : SimpleGraph V}
    {P : Finset (Finset V)} (part : Partition D J P) {A : Finset V} {x : V}
    (ha : A ∈ P) (hx : x ∈ A) : blockOf P x = A := by
  classical
  have hs := part.spec x
  by_contra ne
  exact Finset.disjoint_left.mp (part.apart _ hs.1 A ha ne) hs.2 hx

def threshold (C E : Type*) [Fintype C] [Fintype E] : ℕ :=
  2*(Fintype.card C + Fintype.card E) + Fintype.card C * Fintype.card C - 1

/-- At a trigger time the current partition really loses a block.
Exactly one union is inserted, and every other surviving block was old. -/
theorem perform_merger [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (t r : ℕ) (radius : ∀ s, RadiusAt D s r)
    (P : Finset (Finset V)) (part : Partition D (run D.rule G t) P)
    (trigger : Trigger D (run D.rule G t) (blockOf P) (threshold C E)) :
    ∃ (Q : Finset (Finset V)) (U : Finset V),
      Partition D (run D.rule G (t+r+1)) Q ∧ Q.card < P.card ∧
      U ∈ Q ∧ (∀ B ∈ Q, B ∈ P ∨ B = U) := by
  classical
  obtain ⟨f,hf,⟨c,d,split⟩,s,high⟩ := trigger
  let F := P.filter (fun A => ∃ b : C, f (.inl b) ∈ A)
  let U := blockUnion F
  let keep := P \ F
  let Q := insert U keep
  have Fsub : F ⊆ P := Finset.filter_subset _ _
  have touches (A : Finset V) (hA : A ∈ F) : ∃ b : C, f (.inl b) ∈ A := (Finset.mem_filter.mp hA).2
  have each (b : C) : blockOf P (f (.inl b)) ∈ F := by
    have valid := part.spec (f (.inl b))
    exact Finset.mem_filter.mpr ⟨valid.1,b,valid.2⟩
  have cover (b : C) : ∃ A ∈ F, f (.inl b) ∈ A := ⟨_,each b,(part.spec _).2⟩
  obtain ⟨T,nb,nt,cert⟩ := merge_touched D e₀ G t r f hf s (radius s) F
    (fun A ha => part.certified A (Fsub ha))
    (fun A ha B hb => part.apart A (Fsub ha) B (Fsub hb)) touches cover high
  have union_block : Block D (run D.rule G (t+r+1)) U := Or.inr ⟨T,nb,nt,cert⟩
  have nonempty : U.Nonempty := ⟨f (.inl s), Finset.mem_biUnion.mpr
    ⟨_,each s,(part.spec _).2⟩⟩
  have dis (A : Finset V) (hA : A ∈ keep) : Disjoint U A := by
    obtain ⟨aP,aF⟩ := Finset.mem_sdiff.mp hA
    apply Finset.disjoint_left.mpr
    intro x xu xa
    obtain ⟨B,bF,xb⟩ := Finset.mem_biUnion.mp xu
    have ne : B ≠ A := fun e => aF (e ▸ bF)
    exact Finset.disjoint_left.mp (part.apart B (Fsub bF) A aP ne) xb xa
  have new_partition : Partition D (run D.rule G (t+r+1)) Q := by
    constructor
    · intro x
      obtain ⟨A,aP,xa⟩ := part.cover x
      by_cases aF : A ∈ F
      · exact ⟨U,Finset.mem_insert_self _ _,Finset.mem_biUnion.mpr ⟨A,aF,xa⟩⟩
      · exact ⟨A,Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨aP,aF⟩),xa⟩
    · intro A ha B hb ne
      rcases Finset.mem_insert.mp ha with rfl | aK
      · rcases Finset.mem_insert.mp hb with h | bK
        · exact False.elim (ne h.symm)
        · exact dis B bK
      · rcases Finset.mem_insert.mp hb with rfl | bK
        · exact (dis A aK).symm
        · exact part.apart A (Finset.mem_sdiff.mp aK).1 B (Finset.mem_sdiff.mp bK).1 ne
    · intro A ha
      rcases Finset.mem_insert.mp ha with rfl | aK
      · exact nonempty
      · exact part.live A (Finset.mem_sdiff.mp aK).1
    · intro A ha
      rcases Finset.mem_insert.mp ha with rfl | aK
      · exact union_block
      · exact block_mono (time_mono D.rule G (by omega : t ≤ t+r+1))
          (part.certified A (Finset.mem_sdiff.mp aK).1)
  have two : 1 < F.card := Finset.one_lt_card.mpr ⟨_,each c,_,each d,split⟩
  have splitCard : keep.card + F.card = P.card := Finset.card_sdiff_add_card_eq_card Fsub
  have add : Q.card ≤ keep.card+1 := Finset.card_insert_le _ _
  refine ⟨Q,U,new_partition,by omega,Finset.mem_insert_self _ _,?_⟩
  intro B hB
  rcases Finset.mem_insert.mp hB with h | h
  · exact Or.inr h
  · exact Or.inl (Finset.mem_sdiff.mp h).1

noncomputable def singletons [Fintype V] : Finset (Finset V) := by
  classical
  exact Finset.univ.image (fun x : V => {x})

theorem singletons_card [Fintype V] : (singletons (V := V)).card = Fintype.card V := by
  classical
  simp [singletons,Finset.card_image_of_injective, Function.Injective]

theorem singleton_partition [Fintype V] [Fintype C] [Fintype E] (D : Data C E)
    (G : SimpleGraph V) : Partition D G (singletons (V := V)) := by
  classical
  have mem (x : V) : {x} ∈ (singletons (V := V)) := Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  constructor
  · exact fun x => ⟨{x},mem x,Finset.mem_singleton_self _⟩
  · intro A hA B hB ne
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hB
    apply Finset.disjoint_left.mpr
    intro z zx zy
    exact ne (congrArg (fun v : V => ({v} : Finset V))
      ((Finset.mem_singleton.mp zx).symm.trans (Finset.mem_singleton.mp zy)))
  · intro A hA
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨x,Finset.mem_singleton_self _⟩
  · intro A hA
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hA
    exact Or.inl (fun a ha b hb => (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)

end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.perform_merger
#print axioms Bootstrap.Subdivision.singleton_partition
