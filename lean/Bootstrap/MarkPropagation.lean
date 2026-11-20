import Bootstrap.CliqueAbsorption

/-! Replace all but one neighbour of a marked role, retaining an injective ordinary witness. -/
namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

structure Shores [Fintype W] (f : W ↪ V) where
  P : Finset V
  Q : Finset V
  roomP : Fintype.card W ≤ P.card
  roomQ : Fintype.card W ≤ Q.card
  outsideP : ∀ p ∈ P, Outside f p
  outsideQ : ∀ q ∈ Q, Outside f q
  apart : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q

def Shores.flip [Fintype W] {f : W ↪ V} (s : Shores f) : Shores f :=
  ⟨s.Q,s.P,s.roomQ,s.roomP,s.outsideQ,s.outsideP,fun q hq p hp => (s.apart p hp q hq).symm⟩

def Shores.done [Fintype W] {f : W ↪ V} (s : Shores f) (G : SimpleGraph V) :=
  CliqueOn G s.P ∨ CliqueOn G s.Q

theorem Shores.done_mono [Fintype W] {f : W ↪ V} {s : Shores f} {G D : SimpleGraph V}
    (h : s.done G) (inc : G ≤ D) : s.done D :=
  h.elim (fun hp => Or.inl (hp.mono inc)) (fun hq => Or.inr (hq.mono inc))

theorem Shores.flip_done [Fintype W] {f : W ↪ V} (s : Shores f) (G : SimpleGraph V) :
    s.flip.done G ↔ s.done G := or_comm

theorem mark_mono {G D : SimpleGraph V} {f : W ↪ V} {P : Set V} {v : W}
    (mark : Marked G f P v) (inc : G ≤ D) : Marked D f P v := fun p hp => inc (mark p hp)

theorem join_mono {G D : SimpleGraph V} {P Q : Set V} (join : Joined G P Q) (inc : G ≤ D) :
    Joined D P Q := fun p hp q hq => inc (join p hp q hq)

theorem join_flip {G : SimpleGraph V} {P Q : Set V} (join : Joined G P Q) :
    Joined G Q P := fun q hq p hp => G.symm (join p hp q hq)

private theorem independent_neighbours [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (f : W ↪ V) (s : Shores f) (full : FullCopy H G f) (cross : Joined G s.P s.Q)
    {v : W} (ng : ∀ r, H.Adj v r → HasTwo H r) (mark : Marked G f s.P v)
    (ind : ∀ r j, H.Adj v r → H.Adj v j → ¬H.Adj r j) {w : W} (vw : H.Adj v w) :
    Marked (step H (step H G)) f s.Q w := by
  classical
  intro q hq
  obtain ⟨inP⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card W ≤ Fintype.card s.P by simpa using s.roomP)
  let move (i : W) := H.Adj v i ∧ i ≠ w
  let toPark (i : W) : V := if move i then (inP i).val else f i
  have mem (i : W) : (inP i).val ∈ s.P := (inP i).property
  have pi (i : W) (hi : move i) : toPark i = (inP i).val := if_pos hi
  have pf (i : W) (hi : ¬move i) : toPark i = f i := if_neg hi
  have pinj : Function.Injective toPark := by
    intro i j e
    by_cases hi : move i <;> by_cases hj : move j
    · rw [pi i hi,pi j hj] at e; exact inP.injective (Subtype.ext e)
    · rw [pi i hi,pf j hj] at e; exact False.elim (s.outsideP _ (mem i) j e.symm)
    · rw [pf i hi,pi j hj] at e; exact False.elim (s.outsideP _ (mem j) i e)
    · rw [pf i hi,pf j hj] at e; exact f.injective e
  let park : W ↪ V := ⟨toPark,pinj⟩
  have fresh : Outside park q := by
    intro i
    change toPark i ≠ q
    by_cases hi : move i
    · rw [pi i hi]; exact s.apart _ (mem i) _ hq
    · rw [pf i hi]; exact s.outsideQ q hq i
  let g := putRole park v q fresh
  have gv : g v = q := putRole_here _ _ _ _
  have gp (i : W) (hi : move i) : g i = (inP i).val :=
    (putRole_away park v q fresh hi.1.ne.symm).trans (pi i hi)
  have gf (i : W) (iv : i ≠ v) (hi : ¬move i) : g i = f i :=
    (putRole_away park v q fresh iv).trans (pf i hi)
  have gw : g w = f w := gf w vw.ne.symm (fun h => h.2 rfl)
  have leg (j : W) (vj : H.Adj v j) (jw : j ≠ w) : (step H G).Adj (g v) (g j) := by
    rw [gv,gp j ⟨vj,jw⟩]
    exact Or.inl (G.symm (cross _ (mem j) q hq))
  have arm (i j : W) (mi : move i) (jv : j ≠ v) (ij : H.Adj i j) :
      (step H G).Adj (g i) (g j) := by
    have fixed : ¬move j := fun h => ind i j mi.1 h.1 ij
    rw [gp i mi,gf j jv fixed]
    have N := (ng i mi.1).pair (H.symm mi.1) ij jv.symm
    exact one_step H G f full N _ (s.outsideP _ (mem i)) (mark _ (mem i))
  refine Or.inr ⟨v,w,g,vw,gv,gw,?_⟩
  intro i j ij avoid
  by_cases iv : i=v
  · subst i
    exact leg j ij (fun e => avoid (Or.inl ⟨rfl,e⟩))
  by_cases jv : j=v
  · subst j
    exact (step H G).symm (leg i (H.symm ij) (fun e => avoid (Or.inr ⟨e,rfl⟩)))
  by_cases mi : move i
  · exact arm i j mi jv ij
  by_cases mj : move j
  · exact (step H G).symm (arm j i mj iv (H.symm ij))
  rw [gf i iv mi,gf j jv mj]
  exact Or.inl (full i j ij)

/-- A marked role whose neighbours all have degree two either makes a shore
a clique or transfers the opposite mark to every neighbour within two rounds. -/
theorem neighbours_change_mark [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (f : W ↪ V) (s : Shores f) (full : FullCopy H G f) (cross : Joined G s.P s.Q)
    {v : W} (ng : ∀ r, H.Adj v r → HasTwo H r) (mark : Marked G f s.P v) :
    s.done (step H (step H G)) ∨ ∀ w, H.Adj v w → Marked (step H (step H G)) f s.Q w := by
  classical
  by_cases ex : ∃ r j, H.Adj v r ∧ H.Adj v j ∧ H.Adj r j
  · obtain ⟨r,j,vr,vj,rj⟩ := ex
    left; left
    intro p hp q hq ne
    have A := (ng r vr).pair (H.symm vr) rj vj.ne
    have B := (ng j vj).pair (H.symm rj) (H.symm vj) vr.ne.symm
    exact Or.inl (two_middle H G f full A B p q (s.outsideP p hp) (s.outsideP q hq) ne (mark p hp) (mark q hq))
  · right
    exact fun _ e => independent_neighbours H G f s full cross ng mark
      (fun r j vr vj rj => ex ⟨r,j,vr,vj,rj⟩) e

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.neighbours_change_mark
