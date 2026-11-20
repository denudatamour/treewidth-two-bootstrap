import Bootstrap.OrdinaryTime
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum

namespace Bootstrap.VertexCover

variable {W V C D : Type*}

/-- The permutations which preserve every fibre of a vertex label. -/
def fibreGroup {L : Type*} (f : V → L) : Subgroup (Equiv.Perm V) where
  carrier := {g | ∀ x, f (g x) = f x}
  one_mem' := fun _ => rfl
  mul_mem' := fun ha hb x => (ha _).trans (hb x)
  inv_mem' := fun {g} hg x => by simpa using (hg (g.symm x)).symm

private theorem swap_preserves {L : Type*} (f : V → L) [DecidableEq V]
    {a b : V} (same : f a = f b) (x : V) : f (Equiv.swap a b x) = f x := by
  by_cases ha : x=a
  · subst x
    simpa using same.symm
  by_cases hb : x=b
  · subst x
    simpa using same
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

private theorem orbit_pair {L : Type*} (f : V → L) {a b c d : V}
    (ab : a ≠ b) (cd : c ≠ d) (ac : f a = f c) (bd : f b = f d) :
    orbitOf (fibreGroup f) ⟨s(a,b),ab⟩ = orbitOf (fibreGroup f) ⟨s(c,d),cd⟩ := by
  classical
  let p := Equiv.swap a c
  let q := Equiv.swap (p b) d
  have pa : p a = c := Equiv.swap_apply_left _ _
  have cb : c ≠ p b := fun he => ab (p.injective (pa.trans he))
  have pb : f (p b) = f d := (swap_preserves f ac b).trans bd
  let g : fibreGroup f :=
    ⟨p.trans q,fun x => (swap_preserves f pb (p x)).trans (swap_preserves f ac x)⟩
  have ga : g.val a = c := by
    change Equiv.swap (p b) d (p a) = c
    rw [pa,Equiv.swap_apply_of_ne_of_ne cb cd]
  have gb : g.val b = d := Equiv.swap_apply_left _ _
  symm
  apply Quotient.sound
  refine ⟨g,?_⟩
  apply Subtype.ext
  change s(g.val a,g.val b) = s(c,d)
  rw [ga,gb]

private def decode : UEdge (C ⊕ D) ⊕ D → Sym2 (C ⊕ D)
  | .inl edge => edge.val
  | .inr d => s(.inr d,.inr d)

/-- Two distinct labels give an unordered pair; a repeated label can only
be one of the unrestricted fibres on the right. -/
theorem orbit_count [Fintype V] [Fintype C] [Fintype D] (f : V → C ⊕ D)
    (left_unique : ∀ c x y, f x = .inl c → f y = .inl c → x=y) :
    Fintype.card (Orbit (fibreGroup f)) ≤ (Fintype.card C + Fintype.card D).choose 2 + Fintype.card D := by
  classical
  let K := UEdge (C ⊕ D) ⊕ D
  have encode (x y : V) (ne : x ≠ y) : ∃ k : K, decode k = s(f x,f y) := by
    by_cases same : f x = f y
    · cases fx : f x with
      | inl c => exact False.elim (ne (left_unique c x y fx (same.symm.trans fx)))
      | inr d => exact ⟨.inr d,by rw [← same,fx]; rfl⟩
    · exact ⟨.inl ⟨s(f x,f y),same⟩,rfl⟩
  have representative (o : Orbit (fibreGroup f)) :
      ∃ k : K, ∃ x y : V, ∃ ne : x ≠ y,
        orbitOf (fibreGroup f) ⟨s(x,y),ne⟩ = o ∧ decode k = s(f x,f y) := by
    obtain ⟨⟨e,valid⟩,rfl⟩ := Quotient.exists_rep o
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨k,hk⟩ := encode x y valid
      exact ⟨k,x,y,valid,rfl,hk⟩
  choose key x y ne ho decoded using representative
  have inj : Function.Injective key := by
    intro i j same
    have eq : s(f (x i),f (y i)) = s(f (x j),f (y j)) :=
      (decoded i).symm.trans ((congrArg decode same).trans (decoded j))
    rw [← ho i,← ho j]
    rcases Sym2.eq_iff.mp eq with ⟨hx,hy⟩|⟨hx,hy⟩
    · exact orbit_pair f (ne i) (ne j) hx hy
    · have eq' := orbit_pair f (ne i) (ne j).symm hx hy
      exact eq'.trans (congrArg (orbitOf (fibreGroup f)) (Subtype.ext Sym2.eq_swap))
  have card := Fintype.card_le_of_injective key inj
  simpa only [K,Fintype.card_sum,Sym2.card_subtype_not_diag] using card


/-- Members of the cover get personal labels; each outside vertex is labelled
by the set of cover vertices that it sees. -/
noncomputable def coverLabel (G : SimpleGraph V) (S : Finset V) (x : V) :
    (↥S ⊕ Finset ↥S) := by
  classical
  exact if hx : x ∈ S then .inl ⟨x,hx⟩ else
    .inr (Finset.univ.filter fun i : ↥S => G.Adj x i.val)

private def labelAdj (G : SimpleGraph V) (S : Finset V) :
    (↥S ⊕ Finset ↥S) → (↥S ⊕ Finset ↥S) → Prop
  | .inl x,.inl y => G.Adj x.val y.val
  | .inl x,.inr B => x ∈ B
  | .inr B,.inl x => x ∈ B
  | .inr _,.inr _ => False

private theorem label_represents (G : SimpleGraph V) (S : Finset V)
    (cover : ∀ x y, G.Adj x y → x ∈ S ∨ y ∈ S) (x y : V) :
    G.Adj x y ↔ labelAdj G S (coverLabel G S x) (coverLabel G S y) := by
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp [labelAdj,coverLabel,hx,hy]
  · simpa [labelAdj,coverLabel,hx,hy] using G.adj_comm (u:=x) (v:=y)
  · simp [labelAdj,coverLabel,hx,hy]
  · simpa [labelAdj,coverLabel,hx,hy] using
      (show ¬ G.Adj x y from fun h => (cover _ _ h).elim hx hy)

private theorem cover_unique (G : SimpleGraph V) (S : Finset V) (c : ↥S) (x : V)
    (hc : coverLabel G S x = .inl c) : x=c.val := by
  classical
  by_cases hx : x ∈ S
  · simp only [coverLabel,dif_pos hx,Sum.inl.injEq] at hc
    exact congrArg Subtype.val hc
  · simp [coverLabel,hx] at hc

/-- A cover of size s leaves at most choose(s+2^s,2)+2^s rounds, uniformly
in the total host order and the rule. -/
theorem bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V)
    (cover : ∀ x y, G.Adj x y → x ∈ S ∨ y ∈ S) :
    stabilizationTime H G ≤ (S.card + 2^S.card).choose 2 + 2^S.card := by
  classical
  let f := coverLabel G S
  let Γ := fibreGroup f
  have inv : Invariant Γ G := by
    intro g x y
    rw [label_represents G S cover (g.val x) (g.val y),label_represents G S cover x y]
    change labelAdj G S (f (g.val x)) (f (g.val y)) ↔ labelAdj G S (f x) (f y)
    rw [g.property x,g.property y]
  have count := orbit_count f (fun c x y hx hy =>
    (cover_unique G S c x hx).trans (cover_unique G S c y hy).symm)
  calc
    stabilizationTime H G ≤ (missingOrbits Γ G).card := stabilizationTime_le_missing H Γ G inv
    _ ≤ Fintype.card (Orbit Γ) := Finset.card_le_univ _
    _ ≤ _ := by simpa only [Fintype.card_coe,Fintype.card_finset] using count

/-- Applies the same bound at any intermediate round of the original process. -/
theorem remaining [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (t : ℕ) (S : Finset V)
    (cover : ∀ x y, (run H G t).Adj x y → x ∈ S ∨ y ∈ S) :
    stabilizationTime H G ≤ t + ((S.card + 2^S.card).choose 2 + 2^S.card) := by
  classical
  let k := stabilizationTime H (run H G t)
  have fixed : run H G (t+k) = run H G (t+k+1) := by
    rw [show t+k+1=t+(k+1) by omega,run_add,run_add]
    exact stabilizationTime_spec H (run H G t)
  exact (Nat.find_min' (stable_exists H G) fixed).trans (Nat.add_le_add_left (bound H _ S cover) t)

end Bootstrap.VertexCover

#print axioms Bootstrap.VertexCover.bound
#print axioms Bootstrap.VertexCover.remaining

#print axioms Bootstrap.VertexCover.orbit_count
