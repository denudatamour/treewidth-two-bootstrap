import Bootstrap.OddWalkMarks
import Bootstrap.CliqueClock

namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

private theorem finish_shores [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    {a l r : W} (N : TwoNeighbours H a l r) (f : W ↪ V) (s : Shores f) (pos : 0 < Fintype.card W)
    (cross : Joined G s.P s.Q) (done' : s.done G) : CliqueOn (step H (step H G)) (s.P ∪ s.Q) := by
  classical
  have once (p q : Finset V) (room : Fintype.card W ≤ p.card) (join : Joined G p q) (cl : CliqueOn G p) :
      CliqueOn (step H (step H G)) (p ∪ q) := by
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (pos.trans_le room)
    apply absorbs_touching H G N p (p ∪ q) room cl
    intro z hz away
    have hzq := (Finset.mem_union.mp hz).resolve_left away
    exact ⟨u,hu,G.symm (join u hu z hzq)⟩
  rcases done' with p|q
  · exact once _ _ s.roomP cross p
  · simpa only [Finset.union_comm] using once _ _ s.roomQ (join_flip cross) q

theorem high_nonbip [Fintype W] [Fintype V] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2) (K : ℕ)
    (odd : ∀ v, ∃ walk : H.Walk v v, walk.length % 2 = 1 ∧ walk.length ≤ K) :
    HighClique H G (3*Fintype.card W-1) (2*Fintype.card W+2*K+11) := by
  classical
  intro t x y old born dx dy
  obtain ⟨f,u,v,p,uv,fx,fy,copy,_,_,_,joined,b,route,take⟩ := high_birth_seed H G conn root cover long t born old dx dy
  let s : Shores f := ⟨p.left,p.right,p.card_left.ge,p.card_right.ge,p.out_left,p.out_right,p.apart⟩
  let base := t+1+2*Fintype.card W
  let stop := base+2*K+6
  have inc (i j : ℕ) (h : i ≤ j) := time_mono H G h
  have cross : Joined (run H G base) s.P s.Q := fun i hi j hj =>
    joined i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
  obtain ⟨walk,wo,short⟩ := odd b
  have full : FullCopy H (run H G base) f := full_later (by dsimp [base]; omega) copy
  have d : s.done (run H G (base+2*walk.length+6)) := by
    rcases take with m|m
    · exact odd_walk_makes_clique H G f s base root cover route walk wo full cross m
    · exact (s.flip_done _).mp (odd_walk_makes_clique H G f s.flip base root cover route walk wo full (join_flip cross) m)
  have ds := Shores.done_mono d (inc _ stop (by dsimp [stop]; omega))
  obtain ⟨i,j,_,di,_⟩ := id long
  obtain ⟨l,r,N⟩ := (hasTwo_iff_degree H i).mpr di
  have pos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨root⟩
  let S := s.P ∪ s.Q
  have cS : CliqueOn (run H G (stop+2)) S :=
    finish_shores H (run H G stop) N f s pos (join_mono cross (inc _ _ (by dsimp [stop]; omega))) ds
  let U := insert x (insert y S)
  have room : Fintype.card W ≤ S.card := s.roomP.trans (Finset.card_le_card Finset.subset_union_left)
  have roomU : Fintype.card W ≤ U.card := room.trans (Finset.card_le_card (fun z hz =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)))
  refine ⟨U,roomU,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_⟩
  have ct (z : V) (hz : z ∈ U) (out : z ∉ S) : ∃ w ∈ S, (run H G (stop+2)).Adj z w := by
    have atBirth := inc (t+1) (stop+2) (by dsimp [stop,base]; omega)
    rcases Finset.mem_insert.mp hz with rfl|hz
    · obtain ⟨w,hw⟩ := Finset.card_pos.mp (pos.trans_le s.roomP)
      exact ⟨w,Finset.mem_union_left s.Q hw,atBirth (fx ▸ (run H G (t+1)).symm (p.mark_left w hw))⟩
    · rcases Finset.mem_insert.mp hz with rfl|hz
      · obtain ⟨w,hw⟩ := Finset.card_pos.mp (pos.trans_le s.roomQ)
        exact ⟨w,Finset.mem_union_right s.P hw,atBirth (fy ▸ (run H G (t+1)).symm (p.mark_right w hw))⟩
      · exact False.elim (out hz)
  have complete : CliqueOn (run H G (stop+4)) U := absorbs_touching H (run H G (stop+2)) N S U room cS ct
  exact complete.mono (inc _ _ (by dsimp [stop,base]; omega))

/-- The long-route bound for every finite connected non-bipartite source. -/
theorem nonbip_long_linear [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    (nonbip : ¬ ProperBoolColor H) : HasLinearUpper H := by
  classical
  obtain ⟨K,odd⟩ := bounded_odd_walks H conn nonbip
  obtain ⟨i,j,_,di,_⟩ := id long
  obtain ⟨l,r,N⟩ := (hasTwo_iff_degree H i).mpr di
  refine ⟨(3*Fintype.card W-1)+(2*Fintype.card W+2*K+11)+2,0,?_⟩
  intro n _
  apply (maxTime_le_iff H n _).mpr
  intro G
  simpa only [Fintype.card_fin] using clique_clock H G N _ _ (high_nonbip H G conn root cover long K odd)

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.nonbip_long_linear
