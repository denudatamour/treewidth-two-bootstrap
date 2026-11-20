import Bootstrap.MarkPropagation

namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

def ProperBoolColor (H : SimpleGraph W) :=
  ∃ c : W → Bool, ∀ i j, H.Adj i j → c i ≠ c j

theorem bounded_odd_walks [Fintype W] (H : SimpleGraph W) (conn : H.Connected)
    (nonbip : ¬ProperBoolColor H) :
    ∃ K : ℕ, ∀ v, ∃ walk : H.Walk v v, walk.length % 2 = 1 ∧ walk.length ≤ K := by
  classical
  have loops (v : W) : ∃ walk : H.Walk v v, walk.length % 2 = 1 := by
    by_contra no
    apply nonbip
    let path (i : W) := Classical.choice (conn v i)
    let color (i : W) : Bool := decide ((path i).length % 2 = 1)
    refine ⟨color,?_⟩
    intro i j e same
    apply no
    have eq : (path i).length % 2 = (path j).length % 2 := by
      have iff' : (path i).length % 2 = 1 ↔ (path j).length % 2 = 1 := decide_eq_decide.mp same
      omega
    refine ⟨((path i).concat e).append (path j).reverse,?_⟩
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_reverse]
    omega
  choose walk odd using loops
  exact ⟨Finset.univ.sup (fun v => (walk v).length),fun v =>
    ⟨walk v,odd v,Finset.le_sup (s := Finset.univ) (f := fun z => (walk z).length) (Finset.mem_univ v)⟩⟩

private def endShore [Fintype W] {f : W ↪ V} (s : Shores f) (n : ℕ) : Finset V :=
  if n % 2 = 0 then s.P else s.Q

private theorem swap_end [Fintype W] {f : W ↪ V} (s : Shores f) (n : ℕ) :
    endShore s.flip n = endShore s (n+1) := by
  by_cases h : n % 2 = 0
  · have hh : (n+1)%2 ≠ 0 := by omega
    simp [endShore,h,hh,Shores.flip]
  · have hh : (n+1)%2 = 0 := by omega
    simp [endShore,h,hh,Shores.flip]

private theorem onward [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (f : W ↪ V) (s : Shores f) (full : FullCopy H G f)
    (cross : Joined G s.P s.Q) (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    {v w prev : W} (before : H.Adj v prev) (next : H.Adj v w)
    (mark : Marked G f s.P v) (back : Marked G f s.Q prev) :
    s.done (step H (step H G)) ∨ Marked (step H (step H G)) f s.Q w := by
  by_cases two : H.degree v = 2
  · right
    by_cases same : prev = w
    · subst w
      exact fun q hq => Or.inl (Or.inl (back q hq))
    have N := ((hasTwo_iff_degree H v).mpr two).pair before next same
    exact fun q hq => Or.inl (one_step H G f full N q (s.outsideQ q hq) (back q hq))
  have ng (r : W) (e : H.Adj v r) : HasTwo H r := (hasTwo_iff_degree H r).mpr ((cover v r e).resolve_left two)
  rcases neighbours_change_mark H G f s full cross ng mark with d|all
  · exact Or.inl d
  · exact Or.inr (all w next)

private theorem along_walk [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (f : W ↪ V) (s : Shores f) (t : ℕ)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    {v z : W} (walk : H.Walk v z) (prev : W) (before : H.Adj v prev)
    (copy : FullCopy H (run H G t) f) (cross : Joined (run H G t) s.P s.Q)
    (mark : Marked (run H G t) f s.P v) (back : Marked (run H G t) f s.Q prev) :
    s.done (run H G (t+2*walk.length)) ∨
      Marked (run H G (t+2*walk.length)) f (endShore s walk.length) z := by
  induction walk generalizing t s prev with
  | nil => right; simpa [endShore] using mark
  | @cons v w z edge tail ih =>
    have advance := onward H (run H G t) f s copy cross cover before edge mark back
    have time : t+2+2*tail.length = t+2*(SimpleGraph.Walk.cons edge tail).length := by
      simp only [SimpleGraph.Walk.length_cons]; omega
    rw [← time]
    rcases advance with done'|forward
    · left
      exact Shores.done_mono (G := run H G (t+2)) done' (time_mono H G (by omega))
    · have inc := time_mono H G (by omega : t ≤ t+2)
      have go := ih s.flip (t+2) v (H.symm edge) (full_later (by omega : t ≤ t+2) copy)
        (join_flip (join_mono cross inc)) forward (mark_mono mark inc)
      rcases go with done'|mark'
      · exact Or.inl ((s.flip_done _).mp done')
      · right
        simpa only [SimpleGraph.Walk.length_cons,← swap_end] using mark'

theorem base_has_two_neighbours [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    {v : W} (base : v ∈ standardBases H root) : ∀ w, H.Adj v w → HasTwo H w := by
  classical
  intro w e
  apply (hasTwo_iff_degree H w).mpr
  by_cases ex : ∃ i, H.degree i ≠ 2
  · have vi : H.degree v ≠ 2 := by simpa only [standardBases,if_pos ex,Set.mem_setOf_eq] using base
    exact (cover v w e).resolve_left vi
  · exact by_contra (fun hw => ex ⟨w,hw⟩)

/-- Alternating marks around an odd closed walk, followed by the first three
edges on the actual long route. The walk may revisit vertices and may backtrack. -/
theorem odd_walk_makes_clique [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (f : W ↪ V) (s : Shores f) (t : ℕ) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2) {l : W}
    (route : CompleteLongRoute H (standardBases H root) l) (walk : H.Walk l l)
    (odd : walk.length % 2 = 1) (copy : FullCopy H (run H G t) f)
    (cross : Joined (run H G t) s.P s.Q) (mark : Marked (run H G t) f s.P l) :
    s.done (run H G (t+2*walk.length+6)) := by
  obtain ⟨n,x,hn,_,h0,hl,_,_,path,_⟩ := route
  have A := path 0 (by omega)
  have B := path 1 (by omega)
  change TwoNeighbours H (x 1) (x 0) (x 2) at A
  change TwoNeighbours H (x 2) (x 1) (x 3) at B
  subst l
  let k := t+2+2*walk.length
  have e := H.symm A.left
  have ng := base_has_two_neighbours H root cover hl
  have inc (i j : ℕ) (h : i ≤ j) := time_mono H G h
  have forward := neighbours_change_mark H (run H G t) f s copy cross ng mark
  rcases forward with done'|all
  · exact Shores.done_mono (G := run H G (t+2)) done' (inc _ _ (by omega))
  have go := along_walk H G f s (t+2) cover walk (x 1) e (full_later (by omega : t ≤ t+2) copy)
    (join_mono cross (inc _ _ (by omega))) (mark_mono mark (inc _ _ (by omega))) (all _ e)
  rcases go with done'|qmark
  · exact Shores.done_mono done' (inc _ _ (by omega))
  have atQ : Marked (run H G k) f s.Q (x 0) := by simpa [endShore,odd,k] using qmark
  have incK : t ≤ k := by dsimp [k]; omega
  have turn := neighbours_change_mark H (run H G k) f s.flip (full_later incK copy)
    (join_flip (join_mono cross (inc _ _ incK))) ng atQ
  rcases turn with done'|all
  · exact Shores.done_mono (G := run H G (k+2)) ((s.flip_done _).mp done') (inc _ _ (by dsimp [k]; omega))
  have p1 : Marked (run H G (k+2)) f s.P (x 1) := all _ e
  have p3 : Marked (run H G (k+3)) f s.P (x 3) := fun p hp =>
    one_step H _ f (full_later (by omega : t ≤ k+2) copy) B p (s.outsideP p hp) (p1 p hp)
  have old := inc t (k+3) (by omega)
  have result : CliqueOn (run H G (k+4)) s.P := fun _ hp _ hq ne =>
    two_middle H _ f (full_later (by omega : t ≤ k+3) copy) A B _ _ (s.outsideP _ hp)
      (s.outsideP _ hq) ne (old (mark _ hp)) (p3 _ hq)
  exact Or.inl (result.mono (inc _ _ (by dsimp [k]; omega)))

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.bounded_odd_walks
#print axioms Bootstrap.DegreeTwo.odd_walk_makes_clique
