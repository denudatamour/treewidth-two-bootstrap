import Bootstrap.TerminalSymmetry

namespace Bootstrap

variable {V : Type*}

/-- A single transposition preserving the whole graph while fixing every
other vertex. The relation is an equivalence relation. -/
def Exchange [DecidableEq V] (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ a b, G.Adj (Equiv.swap x y a) (Equiv.swap x y b) ↔ G.Adj a b

namespace Exchange
variable [DecidableEq V] {G : SimpleGraph V} {x y z : V}

theorem refl (x : V) : Exchange G x x := by simp [Exchange]
theorem symm (h : Exchange G x y) : Exchange G y x := by
  simpa only [Exchange,Equiv.swap_comm y x] using h

theorem conjugate (p : Equiv.Perm V) (pres : ∀ a b, G.Adj (p a) (p b) ↔ G.Adj a b)
    (h : Exchange G x y) : Exchange G (p x) (p y) := by
  intro a b
  obtain ⟨a,rfl⟩ := p.surjective a
  obtain ⟨b,rfl⟩ := p.surjective b
  rw [p.injective.swap_apply,p.injective.swap_apply,pres,pres,h]

theorem trans (xy : Exchange G x y) (yz : Exchange G y z) : Exchange G x z := by
  by_cases xz : x=z
  · exact xz ▸ refl _
  by_cases yx : y=x
  · exact yx ▸ yz
  by_cases zy : z=y
  · exact zy ▸ xy
  have h := conjugate (Equiv.swap x y) xy yz
  simpa only [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne (Ne.symm xz) zy] using h

theorem neighbour {a b t : V} (h : Exchange G a b) (at' : G.Adj a t) (bt : b ≠ t) : G.Adj b t := by
  have next := (h a t).mpr at'
  rwa [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne at'.ne.symm bt.symm] at next

/-- Full symmetry of one class fixes its complement pointwise and spreads
every old neighbour across that class. -/
theorem complete_to (P : V → Prop) (base : V)
    (stars : ∀ a, P a → Exchange G base a) {b : V} (other : ¬P b)
    (contact : ∃ a, P a ∧ G.Adj a b) : ∀ a, P a → G.Adj a b := by
  obtain ⟨p,pp,edge⟩ := contact
  intro a pa
  exact neighbour (trans (stars p pp).symm (stars a pa)) edge (fun e => other (e ▸ pa))

theorem all_pairs (base : V) (stars : ∀ a, Exchange G base a) {p q : V} (edge : G.Adj p q) :
    G = ⊤ := by
  apply le_antisymm le_top
  intro x y ne
  change x ≠ y at ne
  have any (a b : V) : Exchange G a b := trans (stars a).symm (stars b)
  by_cases xq : x=q
  · subst x
    exact (neighbour (any p y) edge ne.symm).symm
  · have xf := neighbour (any p x) edge xq
    exact (neighbour (any q y) xf.symm ne.symm).symm

end Exchange
end Bootstrap

#print axioms Bootstrap.Exchange.all_pairs
