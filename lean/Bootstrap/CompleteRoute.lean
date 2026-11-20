import Bootstrap.ConnectedDegreeTwo

namespace Bootstrap.DegreeTwo

variable {W V : Type*}

/-- A route between base vertices, allowing the last to equal the first.
Every other role is a distinct non-base role of degree exactly two. -/
def CompleteLongRoute [Fintype W] (H : SimpleGraph W) (base : Set W) (l : W) : Prop :=
  ∃ (n : ℕ) (x : ℕ → W), 3 ≤ n ∧ n ≤ Fintype.card W ∧ x 0 = l ∧ l ∈ base ∧ x n ∈ base ∧
    (∀ i, 0 < i → i < n → x i ∉ base) ∧ Route H x n ∧
    ∀ i j, i < n → j < n → x i = x j → i = j

private structure OpenRoute (H : SimpleGraph W) (base : Set W) (x : ℕ → W) (n : ℕ) : Prop where
  length_ge : 2 ≤ n
  base_start : x 0 ∈ base
  off_base : ∀ i, 0 < i → i ≤ n → x i ∉ base
  separate : ∀ i j, i ≤ n → j ≤ n → x i = x j → i = j
  interior : Route H x n

private theorem open_card [Fintype W] {H : SimpleGraph W} {base : Set W} {x : ℕ → W} {n : ℕ}
    (p : OpenRoute H base x n) : n+1 ≤ Fintype.card W := by
  let f : Fin (n+1) ↪ W :=
    ⟨fun i => x i, fun i j h => Fin.ext (p.separate i j (by omega) (by omega) h)⟩
  simpa using Fintype.card_le_of_embedding f

private theorem open_advance [Fintype W] {H : SimpleGraph W} {base : Set W}
    (deg : ∀ z ∉ base, HasTwo H z) {x : ℕ → W} {n : ℕ} (p : OpenRoute H base x n) :
    CompleteLongRoute H base (x 0) ∨ ∃ y : ℕ → W, OpenRoute H base y (n+1) ∧ y 0 = x 0 := by
  classical
  have low := p.length_ge
  have prev := p.interior (n-2) (by omega)
  have e₁ : n-2+1 = n-1 := by omega
  have e₂ : n-2+2 = n := by omega
  rw [e₁,e₂] at prev
  obtain ⟨w,N⟩ := (deg (x n) (p.off_base n (by omega) le_rfl)).other (H.symm prev.right)
  let y := fun i => if i = n+1 then w else x i
  have first (i : ℕ) (hi : i ≤ n) : y i = x i := by
    have ne : i ≠ n+1 := by omega
    simp [y,ne]
  have last : y (n+1) = w := by simp [y]
  have route : Route H y (n+1) := by
    intro i hi
    by_cases old : i+2 ≤ n
    · rw [first (i+1) (by omega), first i (by omega), first (i+2) old]
      exact p.interior i old
    · have c₁ : i+1 = n := by omega
      have c₂ : i+2 = n+1 := by omega
      rw [c₁,c₂,first n le_rfl,last,first i (by omega),show i=n-1 by omega]
      exact N
  have distinct_old (i j : ℕ) (hi : i < n+1) (hj : j < n+1) (eq : y i = y j) : i = j := by
    have hi' : i ≤ n := by omega
    have hj' : j ≤ n := by omega
    rw [first i hi',first j hj'] at eq
    exact p.separate i j hi' hj' eq
  by_cases wb : w ∈ base
  · left
    refine ⟨n+1,y,by omega,open_card p,first 0 (by omega),p.base_start,last ▸ wb,?_,route,distinct_old⟩
    intro i hi hi'
    rw [first i (by omega)]
    exact p.off_base i hi (by omega)
  · right
    have fresh (i : ℕ) (hi : i ≤ n) : x i ≠ w := by
      intro eq
      by_cases iz : i = 0
      · subst i
        exact wb (eq ▸ p.base_start)
      by_cases ie : i = n
      · subst i
        exact H.loopless w (eq ▸ N.right)
      by_cases ilast : i = n-1
      · subst i
        exact N.distinct eq
      have T := p.interior (i-1) (by omega)
      have mid : i-1+1=i := by omega
      have nxt : i-1+2=i+1 := by omega
      rw [mid,nxt] at T
      have adj : H.Adj (x i) (x n) := eq.symm ▸ H.symm N.right
      rcases T.only (x n) adj with e | e
      · have := p.separate n (i-1) le_rfl (by omega) e
        omega
      · have := p.separate n (i+1) le_rfl (by omega) e
        omega
    refine ⟨y,⟨by omega,(first 0 (by omega)).symm ▸ p.base_start,?_,?_,route⟩,first 0 (by omega)⟩
    · intro i hi hi'
      by_cases e : i = n+1
      · rw [e,last]
        exact wb
      · rw [first i (by omega)]
        exact p.off_base _ hi (by omega)
    · intro i j hi hj he
      by_cases ie : i=n+1
      · by_cases je : j=n+1
        · omega
        · rw [ie,last,first j (by omega)] at he
          exact (fresh j (by omega) he.symm).elim
      · by_cases je : j=n+1
        · rw [je,last,first i (by omega)] at he
          exact (fresh i (by omega) he).elim
        · exact distinct_old i j (by omega) (by omega) he

private theorem open_finishes [Fintype W] {H : SimpleGraph W} {base : Set W}
    (deg : ∀ z ∉ base, HasTwo H z) (k : ℕ) {n : ℕ} {x : ℕ → W}
    (p : OpenRoute H base x n) (budget : Fintype.card W ≤ n+1+k) :
    CompleteLongRoute H base (x 0) := by
  induction k generalizing n x with
  | zero =>
    rcases open_advance deg p with yes | ⟨y,q,_⟩
    · exact yes
    · have := open_card q
      omega
  | succ k ih =>
    rcases open_advance deg p with yes | ⟨y,q,h0⟩
    · exact yes
    · rw [←h0]
      exact ih q (by omega)

theorem longStart_finishes [Fintype W] {H : SimpleGraph W} {base : Set W} {l : W}
    (deg : ∀ z ∉ base, HasTwo H z) (start : LongStart H base l) : CompleteLongRoute H base l := by
  classical
  obtain ⟨bl,a,b,r,ia,ib,A,B⟩ := start
  let x : ℕ → W := fun i => if i=0 then l else if i=1 then a else b
  have la : l ≠ a := fun e => ia (e ▸ bl)
  have lb : l ≠ b := fun e => ib (e ▸ bl)
  have ab : a ≠ b := fun e => H.loopless b (e ▸ A.right)
  have partial' : OpenRoute H base x 2 := by
    refine ⟨by omega,by simpa [x] using bl,?_,?_,?_⟩
    · intro i i0 i2
      rcases (by omega : i=1 ∨ i=2) with rfl | rfl
      · simpa [x] using ia
      · simpa [x] using ib
    · intro i j hi hj eq
      rcases (by omega : i=0 ∨ i=1 ∨ i=2) with rfl | rfl | rfl <;>
        rcases (by omega : j=0 ∨ j=1 ∨ j=2) with rfl | rfl | rfl <;>
        simp_all [x,Ne.symm la,Ne.symm lb,Ne.symm ab]
    · intro i hi
      have i0 : i=0 := by omega
      subst i
      simpa [x] using A
  simpa [x] using open_finishes deg (Fintype.card W) partial' (by omega)

theorem off_standard_hasTwo [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (root : W) :
    ∀ z ∉ standardBases H root, HasTwo H z := by
  classical
  intro z hz
  apply (hasTwo_iff_degree H z).mpr
  by_contra bad
  have ex : ∃ w, H.degree w ≠ 2 := ⟨z,bad⟩
  apply hz
  simpa only [standardBases,if_pos ex,Set.mem_setOf_eq] using bad

/-- An explicitly existing long route supplies the long-route hypothesis in
the manuscript, with no location information about the selected rule edge. -/
theorem degree_two_edge_of_long_route [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    {base : Set W} {l : W} (long : CompleteLongRoute H base l) :
    ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2 := by
  obtain ⟨n,x,hn,_,_,_,_,_,route,_⟩ := long
  have A := route 0 (by omega)
  have B := route 1 (by omega)
  exact ⟨x 1,x 2,A.right,(hasTwo_iff_degree H _).mp ⟨_,_,A⟩,
    (hasTwo_iff_degree H _).mp ⟨_,_,B⟩⟩

/-- Complete statement of Lemma II.2. Both ends of the oriented long route
are base vertices, its interior is simple, and the two ends may coincide. -/
theorem lemma_II_2 [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (f : W ↪ V) (t : ℕ) (hf : FullCopy H (run H G t) f)
    (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    {x y : W} (edge : H.Adj x y) (P Q : Set V) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P x) (mq : Marked (run H G t) f Q y) :
    Joined (run H G (t+2*Fintype.card W)) P Q ∧
    ∃ l, CompleteLongRoute H (standardBases H root) l ∧
      (Marked (run H G (t+2*Fintype.card W)) f P l ∨ Marked (run H G (t+2*Fintype.card W)) f Q l) := by
  obtain ⟨cross,l,live,mark⟩ := two_sets_of_neighbours_connected H G f t hf conn root cover long
    edge P Q hP hQ hp hq hdis mp mq
  exact ⟨cross,l,longStart_finishes (off_standard_hasTwo H root) live,mark⟩

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.longStart_finishes
#print axioms Bootstrap.DegreeTwo.lemma_II_2
