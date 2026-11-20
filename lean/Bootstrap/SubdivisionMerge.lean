import Bootstrap.SubdivisionBlock
import Bootstrap.ConnectedDegreeTwo

namespace Bootstrap.Subdivision

open DegreeTwo
variable {C E V : Type*}

def Data.baseGraph (D : Data C E) : SimpleGraph C where
  Adj x y := ∃ e, (x=D.left e ∧ y=D.right e) ∨ (y=D.left e ∧ x=D.right e)
  symm := by
    rintro x y ⟨e,h⟩
    exact ⟨e,h.symm⟩
  loopless := by
    rintro x ⟨e,⟨l,r⟩ | ⟨l,r⟩⟩ <;> exact D.proper e (l.symm.trans r)

theorem midpoint (D : Data C E) (e : E) :
    TwoNeighbours D.rule (Sum.inr e) (Sum.inl (D.left e)) (Sum.inl (D.right e)) := by
  refine ⟨Or.inl rfl,Or.inr rfl,(fun h => D.proper e (Sum.inl.inj h)),?_⟩
  intro j h
  cases j with
  | inl c =>
    rcases h with h | h
    · exact Or.inl (congrArg Sum.inl h)
    · exact Or.inr (congrArg Sum.inl h)
  | inr d => exact False.elim h

theorem chain_on_base (D : Data C E) {a b : C} (p : D.baseGraph.Walk a b) :
    Chain D.rule p.length (Sum.inl a) (Sum.inl b) := by
  induction p with
  | nil => rfl
  | @cons u v w e p ih =>
    obtain ⟨d,⟨hu,hv⟩ | ⟨hv,hu⟩⟩ := e
    · have N : TwoNeighbours D.rule (Sum.inr d) (Sum.inl u) (Sum.inl v) := by
        rw [hu,hv]
        exact midpoint D d
      have first : Chain D.rule 1 (Sum.inl u) (Sum.inl v) := ⟨Sum.inl u, Sum.inr d, rfl, N⟩
      simpa [SimpleGraph.Walk.length,Nat.add_comm] using chain_append first ih
    · have N : TwoNeighbours D.rule (Sum.inr d) (Sum.inl u) (Sum.inl v) := by
        rw [hu,hv]
        exact (midpoint D d).reverse
      have first : Chain D.rule 1 (Sum.inl u) (Sum.inl v) := ⟨Sum.inl u, Sum.inr d, rfl, N⟩
      simpa [SimpleGraph.Walk.length,Nat.add_comm] using chain_append first ih

noncomputable def hostDegree [Fintype V] (J : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (J.neighborFinset v).card

theorem hostDegree_eq [Fintype V] (J : SimpleGraph V) [DecidableRel J.Adj] (v : V) :
    hostDegree J v = J.degree v := by
  classical
  unfold hostDegree SimpleGraph.degree
  congr 1
  ext u
  simp

/-- A high degree at a vertex of a full copy supplies the specified number
of neighbours outside the copy. The loopless graph improves the subtraction
from the copy's order to its order minus one. -/
theorem many_outside {W : Type*} [Fintype W] [Fintype V] (J : SimpleGraph V)
    (f : W ↪ V) (i : W) (want : ℕ)
    (high : Fintype.card W + want - 1 ≤ hostDegree J (f i)) :
    ∃ Z : Finset V, want ≤ Z.card ∧ ∀ z ∈ Z, Outside f z ∧ J.Adj z (f i) := by
  classical
  let nb := J.neighborFinset (f i)
  let occupied := Finset.univ.map f
  have occ : occupied.card = Fintype.card W := by simp [occupied]
  have ino : f i ∈ occupied := Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have no : f i ∉ nb := by simp [nb]
  have count : nb.card = hostDegree J (f i) := rfl
  have sub : nb ∩ occupied ⊆ occupied.erase (f i) := by
    intro z hz
    obtain ⟨hn,ho⟩ := Finset.mem_inter.mp hz
    exact Finset.mem_erase.mpr ⟨fun h => no (h ▸ hn),ho⟩
  have bound := Finset.card_le_card sub
  have drop := Finset.card_erase_add_one ino
  have balance := Finset.card_sdiff_add_card_inter nb occupied
  refine ⟨nb \ occupied,by omega,?_⟩
  intro z hz
  obtain ⟨hnb,hout⟩ := Finset.mem_sdiff.mp hz
  exact ⟨fun k eq => hout (Finset.mem_map.mpr ⟨k,Finset.mem_univ _,eq⟩),
    J.symm ((J.mem_neighborFinset _ _).mp hnb)⟩

private theorem touched_card [Fintype C] {F : Finset (Finset V)} (f : C → V)
    (touch : ∀ A ∈ F, ∃ c, f c ∈ A) (sep : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) :
    F.card ≤ Fintype.card C := by
  classical
  let select : ↥F → C := fun A => Classical.choose (touch A.1 A.2)
  have mem (A : ↥F) : f (select A) ∈ A.1 := Classical.choose_spec (touch A.1 A.2)
  let pick : ↥F ↪ C := ⟨select,by
    intro A B eq
    apply Subtype.ext
    by_contra h
    have dis := sep A.1 A.2 B.1 B.2 h
    exact Finset.disjoint_left.mp dis (mem A) (eq.symm ▸ mem B)⟩
  simpa using Fintype.card_le_of_embedding pick

private theorem small_union [Fintype C] [DecidableEq V] {F : Finset (Finset V)}
    (bound : F.card ≤ Fintype.card C) :
    ((F.filter (fun B => B.card = Fintype.card C)).biUnion id).card ≤
      Fintype.card C * Fintype.card C := by
  classical
  let small := F.filter (fun B => B.card = Fintype.card C)
  have counts : (∑ B ∈ small, B.card) = ∑ _B ∈ small, Fintype.card C := by
    apply Finset.sum_congr rfl
    intro B hB
    exact (Finset.mem_filter.mp hB).2
  have sub : small.card ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
  calc
    (small.biUnion id).card ≤ ∑ B ∈ small, B.card := Finset.card_biUnion_le
    _ = small.card * Fintype.card C := by rw [counts,Finset.sum_const,Nat.nsmul_eq_mul]
    _ ≤ Fintype.card C * Fintype.card C := Nat.mul_le_mul_right _ (le_trans sub bound)

noncomputable def blockUnion (F : Finset (Finset V)) : Finset V := by
  classical
  exact F.biUnion id

def RadiusAt (D : Data C E) (s : C) (r : ℕ) : Prop :=
  ∀ c, ∃ p : D.baseGraph.Walk s c, p.length ≤ r

theorem radius_of_connected [Fintype C] (D : Data C E) (conn : D.baseGraph.Connected) (s : C) :
    RadiusAt D s (Fintype.card C - 1) := by
  intro c
  obtain ⟨p,hp⟩ := conn.exists_isPath s c
  have len := hp.length_lt
  exact ⟨p,by omega⟩

/-- The high-degree trigger produces a certified union of *all* touched
blocks after at most r+1 ordinary rounds. A certifying neighbour inside a
large block is retained. Small blocks can remove at most c squared
neighbours in total. -/
theorem merge_touched [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (t r : ℕ) (f : C ⊕ E ↪ V) (hf : FullCopy D.rule (run D.rule G t) f)
    (s : C) (radius : RadiusAt D s r) (F : Finset (Finset V))
    (blocks : ∀ A ∈ F, Block D (run D.rule G t) A)
    (sep : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (touch : ∀ A ∈ F, ∃ c : C, f (Sum.inl c) ∈ A)
    (cover : ∀ c : C, ∃ A ∈ F, f (Sum.inl c) ∈ A)
    (high : 2*(Fintype.card C + Fintype.card E) + Fintype.card C * Fintype.card C - 1 ≤
      hostDegree (run D.rule G t) (f (Sum.inl s))) :
    ∃ T : Finset V, Fintype.card C ≤ (blockUnion F).card ∧
      Fintype.card C + Fintype.card E ≤ T.card ∧
      Certified (run D.rule G (t+r+1)) (blockUnion F) T := by
  classical
  let cnum := Fintype.card C
  let h := Fintype.card C + Fintype.card E
  have high' : Fintype.card (C ⊕ E) + (h+cnum*cnum) - 1 ≤ hostDegree (run D.rule G t) (f (.inl s)) := by
    rw [Fintype.card_sum]
    dsimp [cnum,h]
    omega
  obtain ⟨Z,hZ,zdata⟩ := many_outside _ f (.inl s) (h+cnum*cnum) high'
  have fcard := touched_card (fun c : C => f (.inl c)) touch sep
  let small := F.filter (fun A => A.card = cnum)
  let bad := small.biUnion id
  have badsize : bad.card ≤ cnum*cnum := small_union fcard
  have leftover : Z.card ≤ (Z \ bad).card + bad.card := Finset.card_le_card_sdiff_add_card
  have marked (z : V) (hz : z ∈ Z) (c : C) : (run D.rule G (t+r)).Adj z (f (.inl c)) := by
    obtain ⟨p,len⟩ := radius c
    have old := zdata z hz
    exact time_mono D.rule G (by omega : t+p.length ≤ t+r)
      (along_chain D.rule G f t hf (chain_on_base D p) z old.1 old.2)
  let baseImgs : C ↪ V := ⟨fun c => f (.inl c),fun _ _ e => Sum.inl.inj (f.injective e)⟩
  have inUnion : Finset.univ.map baseImgs ⊆ blockUnion F := by
    intro x hx
    obtain ⟨c,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨A,hA,ca⟩ := cover c
    exact Finset.mem_biUnion.mpr ⟨A,hA,ca⟩
  have baseSize := Finset.card_le_card inUnion
  refine ⟨Z \ bad, by simpa using baseSize, show h ≤ (Z \ bad).card by omega, ?_⟩
  intro z hz v hv zv
  obtain ⟨inZ,notBad⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨A,hA,va⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨c,ca⟩ := touch A hA
  have hblock := blocks A hA
  have free : z ∉ A ∨ cnum < A.card := by
    by_cases za : z ∈ A
    · right
      have diff : A.card ≠ cnum := by
        intro e
        exact notBad (Finset.mem_biUnion.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,e⟩,za⟩)
      rcases hblock with single | ⟨T,nb,_,_⟩
      · exact False.elim ((zdata z inZ).1 (.inl c) (single _ ca _ za))
      · change cnum ≤ A.card at nb
        omega
    · exact Or.inl za
  exact spread D e₀ _ (block_mono (time_mono D.rule G (by omega : t ≤ t+r)) hblock)
    ca (marked z inZ c) free v va zv.symm

end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.midpoint
#print axioms Bootstrap.Subdivision.many_outside
#print axioms Bootstrap.Subdivision.radius_of_connected
#print axioms Bootstrap.Subdivision.merge_touched
