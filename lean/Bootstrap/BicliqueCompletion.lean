import Bootstrap.BipartiteSpread
import Bootstrap.BipartiteComponents

namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

def Biclique.later [Fintype W] {G D : SimpleGraph V} (B : Biclique (W := W) G) (inc : G ≤ D) :
    Biclique (W := W) D := ⟨B.P,B.Q,B.roomP,B.roomQ,B.apart,fun p hp q hq => inc (B.cross p hp q hq)⟩

private theorem exits [Fintype V] (G : SimpleGraph V) (conn : G.Connected) (S : Finset V)
    (source : S.Nonempty) (incomplete : S ≠ Finset.univ) :
    ∃ z ∉ S, ∃ u ∈ S, G.Adj z u := by
  classical
  by_contra no
  obtain ⟨x,hx⟩ := source
  apply incomplete
  apply Finset.eq_univ_of_forall
  intro y
  have path := (G.reachable_iff_reflTransGen x y).mp (conn x y)
  induction path with
  | refl => exact hx
  | tail _ e ih => exact by_contra (fun away => no ⟨_,away,_,ih,G.symm e⟩)

private theorem add_one [Fintype W] [Fintype V] (H : SimpleGraph W) (G C : SimpleGraph V)
    (conn : C.Connected) (init : C ≤ G) (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j)
    {a l r : W} (N : TwoNeighbours H a l r) (B : Biclique (W := W) G)
    (incomplete : B.P ∪ B.Q ≠ Finset.univ) :
    ∃ D : Biclique (W := W) (step H G), (B.P ∪ B.Q).card + 1 ≤ (D.P ∪ D.Q).card := by
  classical
  have pos := Fintype.card_pos_iff.mpr (⟨a⟩ : Nonempty W)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (pos.trans_le B.roomP)
  obtain ⟨z,away,u,hu,contact⟩ := exits C conn (B.P ∪ B.Q) ⟨x,Finset.mem_union_left _ hx⟩ incomplete
  have za : z ∉ B.P := fun hz => away (Finset.mem_union_left _ hz)
  have zb : z ∉ B.Q := fun hz => away (Finset.mem_union_right _ hz)
  have put (S : Biclique (W := W) G) (za : z ∉ S.P) (zb : z ∉ S.Q) (uP : u ∈ S.P) :
      ∃ D : Biclique (W := W) (step H G), (S.P ∪ S.Q).card+1 ≤ (D.P ∪ D.Q).card := by
    have apart : Disjoint S.P (insert z S.Q) := by
      apply Finset.disjoint_left.mpr
      intro v hv h
      rcases Finset.mem_insert.mp h with rfl|h
      · exact za hv
      · exact Finset.disjoint_left.mp S.apart hv h
    have join : Joined (step H G) S.P (↑(insert z S.Q) : Set V) := by
      intro i hi j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact (step H G).symm (recruit_shore H G c proper N S za zb uP (init contact) i hi)
      · exact Or.inl (S.cross i hi j hj)
    let D : Biclique (W := W) (step H G) := ⟨S.P,insert z S.Q,S.roomP,
      S.roomQ.trans (Finset.card_le_card (Finset.subset_insert _ _)),apart,join⟩
    refine ⟨D,?_⟩
    change (S.P ∪ S.Q).card+1 ≤ (S.P ∪ insert z S.Q).card
    rw [Finset.card_union_of_disjoint S.apart,Finset.card_union_of_disjoint apart,
      Finset.card_insert_of_not_mem zb]
    omega
  rcases Finset.mem_union.mp hu with p|q
  · exact put B za zb p
  · obtain ⟨D,hd⟩ := put B.swap zb za q
    exact ⟨D,by simpa only [Biclique.swap,Finset.union_comm B.Q B.P] using hd⟩

theorem biclique_spans [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (conn : G.Connected) (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j)
    {a l r : W} (N : TwoNeighbours H a l r) (t k : ℕ) (B : Biclique (W := W) (run H G t))
    (budget : Fintype.card V ≤ (B.P ∪ B.Q).card + k) :
    ∃ D : Biclique (W := W) (run H G (t+k)), D.P ∪ D.Q = Finset.univ := by
  classical
  induction k generalizing t with
  | zero =>
    have size := Finset.card_le_univ (B.P ∪ B.Q)
    exact ⟨B,Finset.eq_univ_of_card _ (by omega)⟩
  | succ k ih =>
    by_cases all : B.P ∪ B.Q = Finset.univ
    · exact ⟨B.later (time_mono H G (by omega)),all⟩
    obtain ⟨D,more⟩ := add_one H (run H G t) G conn (time_mono H G (by omega : 0 ≤ t)) c proper N B all
    have next := ih (t+1) D (by omega)
    rwa [show t+(k+1)=(t+1)+k by omega]

private theorem stable_inside [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (t : ℕ)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) {a b l r : W}
    (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r) (S : Biclique (W := W) (run H G t))
    (span : S.P ∪ S.Q = Finset.univ) {x y : V} (px : x ∈ S.P) (py : y ∈ S.P) (inside : (run H G t).Adj x y) :
    stabilizationTime H G ≤ t+2 := by
  classical
  have next := run_le_succ H G t
  have qfull : CliqueOn (run H G (t+1)) S.Q := fill_opposite H _ c proper A B S px py inside
  have hsize := Fintype.one_lt_card_iff.mpr (⟨a,b,A.right.ne⟩ : ∃ i j : W, i ≠ j)
  obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp (hsize.trans_le S.roomQ)
  have pfull : CliqueOn (run H G (t+2)) S.P :=
    fill_opposite H _ c proper A B (S.swap.later next) hu hv (qfull hu hv ne)
  have all (z : V) : z ∈ S.P ∨ z ∈ S.Q := Finset.mem_union.mp (span.symm ▸ Finset.mem_univ z)
  have inc := time_mono H G (by omega : t ≤ t+2)
  apply Nat.find_min' (stable_exists H G)
  apply le_antisymm (run_le_succ H G (t+2))
  intro i j edge
  rcases all i with pi|qi <;> rcases all j with pj|qj
  · exact pfull pi pj edge.ne
  · exact inc (S.cross _ pi _ qj)
  · exact inc ((run H G t).symm (S.cross _ pj _ qi))
  · exact Or.inl (qfull qi qj edge.ne)

theorem spanning_stable [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (t : ℕ)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H)
    {a b l r : W} (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r)
    (S : Biclique (W := W) (run H G t)) (span : S.P ∪ S.Q = Finset.univ) :
    stabilizationTime H G ≤ t+2 := by
  classical
  by_cases ip : ∃ x ∈ S.P, ∃ y ∈ S.P, (run H G t).Adj x y
  · obtain ⟨x,hx,y,hy,edge⟩ := ip
    exact stable_inside H G t c proper A B S span hx hy edge
  by_cases iq : ∃ x ∈ S.Q, ∃ y ∈ S.Q, (run H G t).Adj x y
  · obtain ⟨x,hx,y,hy,edge⟩ := iq
    exact stable_inside H G t c proper A B S.swap (by simpa only [Biclique.swap,Finset.union_comm S.Q S.P] using span) hx hy edge
  have all (z : V) : z ∈ S.P ∨ z ∈ S.Q := Finset.mem_union.mp (span.symm ▸ Finset.mem_univ z)
  let col (z : V) := decide (z ∈ S.P)
  have cut (i j : V) (e : (run H G t).Adj i j) : col i ≠ col j := by
    intro same
    have eq : i∈S.P ↔ j∈S.P := decide_eq_decide.mp same
    by_cases pi : i∈S.P
    · exact ip ⟨i,pi,j,eq.mp pi,e⟩
    · exact iq ⟨i,(all i).resolve_left pi,j,(all j).resolve_left (fun h => pi (eq.mpr h)),e⟩
  have preserve := proper_step H no (run H G t) col cut
  have fix : run H G t = run H G (t+1) := by
    apply le_antisymm (run_le_succ H G t)
    intro i j e
    have diff := preserve i j e
    by_cases pi : i ∈ S.P <;> by_cases pj : j ∈ S.P
    · exact False.elim (diff (by simp [col,pi,pj]))
    · exact S.cross _ pi _ ((all j).resolve_left pj)
    · exact (run H G t).symm (S.cross _ pj _ ((all i).resolve_left pi))
    · exact False.elim (diff (by simp [col,pi,pj]))
  exact (Nat.find_min' (stable_exists H G) fix).trans (by omega)

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.biclique_spans
#print axioms Bootstrap.DegreeTwo.spanning_stable
