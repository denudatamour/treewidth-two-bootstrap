import Bootstrap.AppendixEdgeCharges
import Bootstrap.SubdivisionLedger

namespace Bootstrap.Subdivision.Appendix
open DegreeTwo
open scoped Classical
variable {C E V : Type*}

/-- The triggered copy determines exactly the blocks replaced by their union. -/
def Merged [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (G : SimpleGraph V)
    (P Q : Finset (Finset V)) (U : Finset V) : Prop :=
  ∃ f : C ⊕ E ↪ V, FullCopy D.rule G f ∧
    (∃ c c' : C, blockOf P (f (.inl c)) ≠ blockOf P (f (.inl c'))) ∧
    (∃ c : C, threshold C E ≤ hostDegree G (f (.inl c))) ∧
    let touched := P.filter (fun A => ∃ b : C, f (.inl b) ∈ A)
    U=blockUnion touched ∧ Q=insert U (P \ touched)

theorem Merged.facts [Fintype C] [Fintype E] [Fintype V] {D : Data C E} {G : SimpleGraph V}
    {P Q : Finset (Finset V)} {U : Finset V} (h : Merged D G P Q U) :
    Trigger D G (blockOf P) (threshold C E) ∧ U ∈ Q ∧ ∀ B∈Q, B∈P ∨ B=U := by
  obtain ⟨f,h,c,k,_,rfl⟩ := h
  refine ⟨⟨f,h,c,k⟩,Finset.mem_insert_self ..,?_⟩
  intro B mem
  rcases Finset.mem_insert.mp mem with here|old
  · exact Or.inr here
  · exact Or.inl (Finset.mem_sdiff.mp old).1

private theorem perform_exact [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (t r : ℕ) (radius : ∀ s, RadiusAt D s r)
    (P : Finset (Finset V)) (part : Partition D (run D.rule G t) P)
    (trigger : Trigger D (run D.rule G t) (blockOf P) (threshold C E)) :
    ∃ (Q : Finset (Finset V)) (U : Finset V),
      Partition D (run D.rule G (t+r+1)) Q ∧ Q.card < P.card ∧
      Merged D (run D.rule G t) P Q U := by
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
  exact ⟨Q,U,new_partition,by omega,f,hf,⟨c,d,split⟩,⟨s,high⟩,rfl,rfl⟩

/-- A trace records all, and only, the nontriggering waiting intervals.
Every merge uses the union prescribed by an actual triggering copy. -/
inductive Schedule [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (G : SimpleGraph V)
    (T r : ℕ) : ℕ → Finset (Finset V) → ℕ → List (Waiting V) → Prop where
  | stop {s P}
      (quiet : ∀ i, s≤i → i<T → ¬Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E)) :
      Schedule D G T r s P 0 [⟨s,T,P⟩]
  | merge {s P j Q U J tail} (start : s≤j) (before : j<T)
      (first : ∀ i, s≤i → i<j → ¬Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E))
      (operation : Merged D (run D.rule G (j+1)) P Q U)
      (newPart : Partition D (run D.rule G (j+1+r+1)) Q) (less : Q.card<P.card)
      (next : Schedule D G T r (j+1+r+1) Q J tail) :
      Schedule D G T r s P (J+1) (⟨s,j,P⟩::tail)

namespace Schedule
variable [Fintype C] [Fintype E] [Fintype V] {D : Data C E} {G : SimpleGraph V}
  {T r s J : ℕ} {P : Finset (Finset V)} {L : List (Waiting V)}

theorem quiet (trace : Schedule D G T r s P J L) : Quiet D G L := by
  induction trace with
  | stop endQuiet =>
    intro I hI
    simp only [List.mem_singleton] at hI
    subst I
    exact endQuiet
  | merge st before first op newPart less next ih =>
    intro I hI
    rcases List.mem_cons.mp hI with rfl|rest
    · exact first
    · exact ih I rest

theorem merger_trace (trace : Schedule D G T r s P J L) : MergeTrace D G T r s P J := by
  induction trace with
  | stop h => exact .stop h
  | merge st before first op newPart less next ih =>
    obtain ⟨hit,inQ,old⟩ := op.facts
    exact .merge st before first hit newPart less inQ old ih

theorem count (trace : Schedule D G T r s P J L) : J≤P.card-1 ∧ L.length=J+1 := by
  induction trace with
  | stop h => simp
  | merge st before first op newPart less next ih =>
    have pos := Finset.card_pos.mpr ⟨_,op.facts.2.1⟩
    simp only [List.length_cons]
    omega

end Schedule

theorem make_schedule [Fintype C] [Fintype E] [Fintype V]
    (D : Data C E) (e₀ : E) (G : SimpleGraph V) (T r : ℕ) (radius : ∀ v, RadiusAt D v r)
    (s : ℕ) (P : Finset (Finset V)) (part : Partition D (run D.rule G s) P) :
    ∃ J L, Schedule D G T r s P J L := by
  classical
  generalize card : P.card=n
  induction n using Nat.strong_induction_on generalizing s P with
  | h n ih =>
    by_cases fires : ∃ j, s≤j ∧ j<T ∧ Trigger D (run D.rule G (j+1)) (blockOf P) (threshold C E)
    · let j := Nat.find fires
      obtain ⟨st,before,hit⟩ : s≤j ∧ j<T ∧ Trigger D (run D.rule G (j+1)) (blockOf P) (threshold C E) :=
        Nat.find_spec fires
      have first (i : ℕ) (lo : s≤i) (hi : i<j) :
          ¬Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E) :=
        fun tr => Nat.find_min fires hi ⟨lo,by omega,tr⟩
      obtain ⟨Q,U,newPart,less,op⟩ := perform_exact D e₀ G (j+1) r radius P
        (part.mono (time_mono D.rule G (by omega : s≤j+1))) hit
      obtain ⟨J,L,tail⟩ := ih Q.card (by omega) _ Q newPart rfl
      exact ⟨J+1,_,.merge st before first op newPart less tail⟩
    · exact ⟨0,_,.stop (fun i lo hi tr => fires ⟨i,lo,hi,tr⟩)⟩

end Bootstrap.Subdivision.Appendix

#print axioms Bootstrap.Subdivision.Appendix.make_schedule
#print axioms Bootstrap.Subdivision.Appendix.Schedule.merger_trace
