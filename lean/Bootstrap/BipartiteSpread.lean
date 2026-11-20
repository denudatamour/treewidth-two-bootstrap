import Bootstrap.CliqueAbsorption

/-! Ordinary bipartite witnesses for recruiting a vertex and flipping two adjacent
degree-two roles. All label maps are injections on the full source. -/
namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

private theorem same_bool {a b c : Bool} (ab : a ≠ b) (ac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem into_finset [Fintype W] (P : Finset V) (room : Fintype.card W ≤ P.card) :
    ∃ p : W ↪ V, ∀ i, p i ∈ P := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_coe] using room : Fintype.card W ≤ Fintype.card P)
  exact ⟨e.trans (Function.Embedding.subtype _),fun i => (e i).property⟩

private theorem combine_labels (p q : W ↪ V) (apart : ∀ i j, p i ≠ q j) (useP : W → Prop) :
    ∃ f : W ↪ V, (∀ i, useP i → f i = p i) ∧ (∀ i, ¬useP i → f i = q i) := by
  classical
  let val (i : W) := if useP i then p i else q i
  have left (i : W) (h : useP i) : val i = p i := if_pos h
  have right (i : W) (h : ¬useP i) : val i = q i := if_neg h
  refine ⟨⟨val,?_⟩,left,right⟩
  intro i j eq
  by_cases hi : useP i <;> by_cases hj : useP j
  · rw [left i hi,left j hj] at eq; exact p.injective eq
  · rw [left i hi,right j hj] at eq; exact False.elim (apart i j eq)
  · rw [right i hi,left j hj] at eq; exact False.elim (apart j i eq.symm)
  · rw [right i hi,right j hj] at eq; exact q.injective eq

/-- Both shores have room for the whole rule. -/
structure Biclique [Fintype W] (G : SimpleGraph V) where
  P : Finset V
  Q : Finset V
  roomP : Fintype.card W ≤ P.card
  roomQ : Fintype.card W ≤ Q.card
  apart : Disjoint P Q
  cross : Joined G P Q

def Biclique.swap [Fintype W] {G : SimpleGraph V} (B : Biclique (W := W) G) : Biclique (W := W) G :=
  ⟨B.Q,B.P,B.roomQ,B.roomP,B.apart.symm,fun q hq p hp => G.symm (B.cross p hp q hq)⟩

private theorem disjoint_labels {P Q : Finset V} (apart : Disjoint P Q) (p q : W ↪ V)
    (hp : ∀ i, p i ∈ P) (hq : ∀ i, q i ∈ Q) (i j : W) : p i ≠ q j :=
  fun eq => (Finset.disjoint_left.mp apart) (hp i) (eq.symm ▸ hq j)

theorem recruit_shore [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) {a l r : W} (N : TwoNeighbours H a l r)
    (B : Biclique (W := W) G) {z u : V} (za : z ∉ B.P) (zb : z ∉ B.Q)
    (inP : u ∈ B.P) (contact : G.Adj z u) : ∀ v ∈ B.P, (step H G).Adj z v := by
  classical
  intro v hv
  by_cases same : u = v
  · exact same ▸ Or.inl contact
  obtain ⟨p,pl,pr,pin⟩ := embed_pair_in B.P B.roomP N.distinct inP hv same
  obtain ⟨q,qin⟩ := into_finset (W := W) B.Q B.roomQ
  obtain ⟨f,left,right⟩ := combine_labels p q (disjoint_labels B.apart p q pin qin) (fun i => c i=c l)
  have fl := (left l rfl).trans pl
  have fr := (left r (same_bool (proper a r N.right) (proper a l N.left))).trans pr
  have copy : FullCopy H G f := by
    intro i j e
    have diff := proper i j e
    by_cases hi : c i = c l <;> by_cases hj : c j = c l
    · exact False.elim (diff (hi.trans hj.symm))
    · rw [left i hi,right j hj]; exact B.cross _ (pin i) _ (qin j)
    · rw [right i hi,left j hj]; exact G.symm (B.cross _ (pin j) _ (qin i))
    · exact False.elim (diff (same_bool (Ne.symm hi) (Ne.symm hj)))
  have out : Outside f z := by
    intro i eq
    by_cases hi : c i = c l
    · rw [left i hi] at eq; exact za (eq ▸ pin i)
    · rw [right i hi] at eq; exact zb (eq ▸ qin i)
  exact fr ▸ one_step H G f copy N z out (fl.symm ▸ contact)

/-- After swapping the adjacent degree-two roles, the only monochromatic
edges are a-l and b-r, one in each class. -/
private theorem two_internal_coloring (H : SimpleGraph W) (c : W → Bool)
    (proper : ∀ i j, H.Adj i j → c i ≠ c j) {a b l r : W}
    (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r) :
    ∃ chooseP : W → Prop, chooseP a ∧ chooseP l ∧ ¬chooseP b ∧ ¬chooseP r ∧
      (∀ i j, H.Adj i j → chooseP i → chooseP j → (i=a ∧ j=l) ∨ (i=l ∧ j=a)) ∧
      (∀ i j, H.Adj i j → ¬chooseP i → ¬chooseP j → (i=b ∧ j=r) ∨ (i=r ∧ j=b)) := by
  classical
  have ab : a ≠ b := A.right.ne
  have ca : c a ≠ c b := proper _ _ A.right
  have cl : c l = c b := same_bool (proper _ _ A.left) ca
  have cr : c r = c a := same_bool (proper _ _ B.right) ca.symm
  let chooseP (i : W) := i=a ∨ i≠b ∧ c i=c b
  have pa : chooseP a := Or.inl rfl
  have pl : chooseP l := Or.inr ⟨A.distinct,cl⟩
  have qb : ¬chooseP b := by simp [chooseP,ab.symm]
  have qr : ¬chooseP r := by simp [chooseP,B.distinct.symm,cr,ca]
  refine ⟨chooseP,pa,pl,qb,qr,?_,?_⟩
  · intro i j e pi pj
    by_cases ia : i=a
    · subst i
      exact Or.inl ⟨rfl,(A.only j e).resolve_right (fun eq => qb (eq ▸ pj))⟩
    by_cases ja : j=a
    · subst j
      exact Or.inr ⟨(A.only i (H.symm e)).resolve_right (fun eq => qb (eq ▸ pi)),rfl⟩
    exact False.elim (proper _ _ e (((pi.resolve_left ia).2).trans ((pj.resolve_left ja).2).symm))
  · intro i j e qi qj
    by_cases ib : i=b
    · subst i
      exact Or.inl ⟨rfl,(B.only j e).resolve_left (fun eq => qj (eq.symm ▸ pa))⟩
    by_cases jb : j=b
    · subst j
      exact Or.inr ⟨(B.only i (H.symm e)).resolve_left (fun eq => qi (eq.symm ▸ pa)),rfl⟩
    have ci : c i ≠ c b := fun eq => qi (Or.inr ⟨ib,eq⟩)
    have cj : c j ≠ c b := fun eq => qj (Or.inr ⟨jb,eq⟩)
    exact False.elim (proper _ _ e (same_bool ci.symm cj.symm))

theorem fill_opposite [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) {a b l r : W}
    (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r) (S : Biclique (W := W) G)
    {x y : V} (xp : x ∈ S.P) (yp : y ∈ S.P) (inside : G.Adj x y) :
    CliqueOn (step H G) S.Q := by
  classical
  obtain ⟨U,ua,ul,ub,ur,onlyP,onlyQ⟩ := two_internal_coloring H c proper A B
  intro z hz w hw ne
  obtain ⟨p,pa,pl,pin⟩ := embed_pair_in S.P S.roomP A.left.ne xp yp inside.ne
  obtain ⟨q,qb,qr,qin⟩ := embed_pair_in S.Q S.roomQ B.right.ne hz hw ne
  obtain ⟨f,left,right⟩ := combine_labels p q (disjoint_labels S.apart p q pin qin) U
  refine Or.inr ⟨b,r,f,B.right,(right b ub).trans qb,(right r ur).trans qr,?_⟩
  intro i j e avoid
  by_cases iu : U i <;> by_cases ju : U j
  · rw [left i iu,left j ju]
    rcases onlyP i j e iu ju with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa only [pa,pl] using inside
    · simpa only [pa,pl] using G.symm inside
  · rw [left i iu,right j ju]; exact S.cross _ (pin i) _ (qin j)
  · rw [right i iu,left j ju]; exact G.symm (S.cross _ (pin j) _ (qin i))
  · exact False.elim (avoid (onlyQ _ _ e iu ju))

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.recruit_shore
#print axioms Bootstrap.DegreeTwo.fill_opposite
