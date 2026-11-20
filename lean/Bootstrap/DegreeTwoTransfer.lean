import Bootstrap.Process

namespace Bootstrap
namespace DegreeTwo

variable {W V : Type*}

/-- An injectively labelled non-induced copy of the entire rule. -/
def FullCopy (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V) : Prop :=
  ∀ i j, H.Adj i j → G.Adj (f i) (f j)

def Outside (f : W ↪ V) (z : V) : Prop := ∀ i, f i ≠ z

/-- The two distinct neighbours exhaust the neighbourhood of the role. -/
structure TwoNeighbours (H : SimpleGraph W) (a l r : W) : Prop where
  left : H.Adj a l
  right : H.Adj a r
  distinct : l ≠ r
  only : ∀ j, H.Adj a j → j = l ∨ j = r

noncomputable def putRole (f : W ↪ V) (a : W) (z : V) (hz : Outside f z) : W ↪ V := by
  classical
  refine ⟨fun i => if i = a then z else f i, ?_⟩
  intro i j hij
  by_cases hi : i = a <;> by_cases hj : j = a
  · exact hi.trans hj.symm
  · exact False.elim (hz j (by simpa only [if_pos hi, if_neg hj] using hij.symm))
  · exact False.elim (hz i (by simpa only [if_neg hi, if_pos hj] using hij))
  · exact f.injective (by simpa only [if_neg hi, if_neg hj] using hij)

@[simp] theorem putRole_here (f : W ↪ V) (a : W) (z : V) (hz : Outside f z) :
    putRole f a z hz a = z := by
  classical
  simp [putRole]

theorem putRole_away (f : W ↪ V) (a : W) (z : V) (hz : Outside f z) {i : W}
    (hi : i ≠ a) : putRole f a z hz i = f i := by
  classical
  simp [putRole, hi]

theorem outside_putRole (f : W ↪ V) (a : W) (p q : V) (hp : Outside f p)
    (hq : Outside f q) (hpq : p ≠ q) : Outside (putRole f a p hp) q := by
  intro i
  by_cases hi : i = a
  · subst i
    rw [putRole_here]
    exact hpq
  · rw [putRole_away f a p hp hi]
    exact hq i

noncomputable def putTwo (f : W ↪ V) (a b : W) (p q : V)
    (hp : Outside f p) (hq : Outside f q) (hpq : p ≠ q) : W ↪ V :=
  putRole (putRole f a p hp) b q (outside_putRole f a p q hp hq hpq)

theorem putTwo_left (f : W ↪ V) (a b : W) (p q : V) (hp : Outside f p)
    (hq : Outside f q) (hpq : p ≠ q) (hab : a ≠ b) : putTwo f a b p q hp hq hpq a = p := by
  unfold putTwo
  rw [putRole_away _ _ _ _ hab, putRole_here]

theorem putTwo_right (f : W ↪ V) (a b : W) (p q : V) (hp : Outside f p)
    (hq : Outside f q) (hpq : p ≠ q) : putTwo f a b p q hp hq hpq b = q := by
  unfold putTwo
  exact putRole_here _ _ _ _

theorem putTwo_away (f : W ↪ V) (a b : W) (p q : V) (hp : Outside f p)
    (hq : Outside f q) (hpq : p ≠ q) {i : W} (ha : i ≠ a) (hb : i ≠ b) :
    putTwo f a b p q hp hq hpq i = f i := by
  unfold putTwo
  rw [putRole_away _ _ _ _ hb, putRole_away _ _ _ _ ha]

private def Gap (G : SimpleGraph V) (x y i j : V) : Prop :=
  G.Adj i j ∨ ((i = x ∧ j = y) ∨ (i = y ∧ j = x))

private theorem gap_symm (G : SimpleGraph V) (x y : V) : Symmetric (Gap G x y) := by
  intro i j h
  rcases h with h | ⟨hi,hj⟩ | ⟨hi,hj⟩
  · exact Or.inl (G.symm h)
  · exact Or.inr (Or.inr ⟨hj,hi⟩)
  · exact Or.inr (Or.inl ⟨hj,hi⟩)

private theorem step_of_gap (H : SimpleGraph W) (G : SimpleGraph V) (g : W ↪ V)
    (u v : W) (x y : V) (huv : H.Adj u v) (hx : g u = x) (hy : g v = y)
    (hall : ∀ i j, H.Adj i j → Gap G x y (g i) (g j)) : (step H G).Adj x y := by
  refine Or.inr ⟨u, v, g, huv, hx, hy, ?_⟩
  intro i j e hn
  rcases hall i j e with old | ⟨hi,hj⟩ | ⟨hi,hj⟩
  · exact old
  · exact False.elim (hn (Or.inl ⟨g.injective (hi.trans hx.symm), g.injective (hj.trans hy.symm)⟩))
  · exact False.elim (hn (Or.inr ⟨g.injective (hi.trans hy.symm), g.injective (hj.trans hx.symm)⟩))

private theorem adj_ne {H : SimpleGraph W} {a b : W} (e : H.Adj a b) : a ≠ b := by
  rintro rfl
  exact H.loopless a e

private theorem one_maps (H : SimpleGraph W) (f g : W ↪ V) (a : W) (p : V)
    (here : g a = p) (away : ∀ i, i ≠ a → g i = f i)
    (R : V → V → Prop) (hsymm : Symmetric R)
    (hold : ∀ i j, H.Adj i j → R (f i) (f j))
    (hnew : ∀ j, H.Adj a j → R p (f j)) :
    ∀ i j, H.Adj i j → R (g i) (g j) := by
  have at_role (j : W) (e : H.Adj a j) : R (g a) (g j) := by
    rw [here, away j (adj_ne e).symm]
    exact hnew j e
  intro i j e
  by_cases hi : i = a
  · subst i
    exact at_role j e
  · by_cases hj : j = a
    · subst j
      exact hsymm (at_role i (H.symm e))
    · rw [away i hi, away j hj]
      exact hold i j e

/-- If all contacts at a new role image are present, the moved labelling is a full copy. -/
theorem putRole_full (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V)
    (hf : FullCopy H G f) (a : W) (p : V) (hp : Outside f p)
    (hnew : ∀ j, H.Adj a j → G.Adj p (f j)) : FullCopy H G (putRole f a p hp) :=
  one_maps H f (putRole f a p hp) a p (putRole_here _ _ _ _)
    (fun _ hi => putRole_away _ _ _ _ hi) G.Adj G.symm hf hnew

/-- Replace a degree-two role by an outside vertex with its first contact already present. -/
theorem one_step (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V)
    (hf : FullCopy H G f) {a l r : W} (N : TwoNeighbours H a l r)
    (z : V) (hz : Outside f z) (hleft : G.Adj z (f l)) :
    (step H G).Adj z (f r) := by
  let g := putRole f a z hz
  have here : g a = z := putRole_here _ _ _ _
  have away : ∀ i, i ≠ a → g i = f i := fun _ hi => putRole_away _ _ _ _ hi
  apply step_of_gap H G g a r z (f r) N.right here (away r (adj_ne N.right).symm)
  apply one_maps H f g a z here away (Gap G z (f r)) (gap_symm _ _ _)
    (fun i j e => Or.inl (hf i j e))
  intro j e
  rcases N.only j e with h | h
  · rw [h]
    exact Or.inl hleft
  · rw [h]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)

private theorem two_maps (H : SimpleGraph W) (f : W ↪ V) {a b l r : W}
    (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r) (p q : V)
    (hp : Outside f p) (hq : Outside f q) (hpq : p ≠ q)
    (R : V → V → Prop) (hsymm : Symmetric R)
    (hold : ∀ i j, H.Adj i j → R (f i) (f j))
    (hleft : R p (f l)) (hmid : R p q) (hright : R q (f r)) :
    ∀ i j, H.Adj i j → R (putTwo f a b p q hp hq hpq i) (putTwo f a b p q hp hq hpq j) := by
  let g := putTwo f a b p q hp hq hpq
  have ga : g a = p := putTwo_left _ _ _ _ _ _ _ _ (adj_ne A.right)
  have gb : g b = q := putTwo_right _ _ _ _ _ _ _ _
  have fix : ∀ i, i ≠ a → i ≠ b → g i = f i := fun _ ia ib => putTwo_away _ _ _ _ _ _ _ _ ia ib
  have on_a (j : W) (e : H.Adj a j) : R (g a) (g j) := by
    by_cases jb : j = b
    · rw [jb, ga, gb]
      exact hmid
    · have jl : j = l := (A.only j e).resolve_right jb
      rw [ga, fix j (adj_ne e).symm jb, jl]
      exact hleft
  have on_b (j : W) (e : H.Adj b j) : R (g b) (g j) := by
    by_cases ja : j = a
    · rw [ja, gb, ga]
      exact hsymm hmid
    · have jr : j = r := (B.only j e).resolve_left ja
      rw [gb, fix j ja (adj_ne e).symm, jr]
      exact hright
  intro i j e
  change R (g i) (g j)
  by_cases ia : i = a
  · subst i
    exact on_a j e
  · by_cases ib : i = b
    · subst i
      exact on_b j e
    · by_cases ja : j = a
      · subst j
        exact hsymm (on_a i (H.symm e))
      · by_cases jb : j = b
        · subst j
          exact hsymm (on_b i (H.symm e))
        · rw [fix i ia ib, fix j ja jb]
          exact hold i j e

/-- The two outer contacts complete the middle edge in one synchronous round.
The outer roles are allowed to agree. -/
theorem two_middle (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V)
    (hf : FullCopy H G f) {a b l r : W}
    (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r) (p q : V)
    (hp : Outside f p) (hq : Outside f q) (hpq : p ≠ q)
    (hleft : G.Adj p (f l)) (hright : G.Adj q (f r)) : (step H G).Adj p q := by
  apply step_of_gap H G (putTwo f a b p q hp hq hpq) a b p q A.right
    (putTwo_left _ _ _ _ _ _ _ _ (adj_ne A.right)) (putTwo_right _ _ _ _ _ _ _ _)
  exact two_maps H f A B p q hp hq hpq (Gap G p q) (gap_symm _ _ _)
    (fun i j e => Or.inl (hf i j e)) (Or.inl hleft) (Or.inr (Or.inl ⟨rfl,rfl⟩)) (Or.inl hright)

/-- The left and middle contacts complete the right-hand edge in one round,
including a length-three route returning to its starting role. -/
theorem two_right (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V)
    (hf : FullCopy H G f) {a b l r : W}
    (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r) (p q : V)
    (hp : Outside f p) (hq : Outside f q) (hpq : p ≠ q)
    (hleft : G.Adj p (f l)) (hmid : G.Adj p q) : (step H G).Adj q (f r) := by
  apply step_of_gap H G (putTwo f a b p q hp hq hpq) b r q (f r) B.right
    (putTwo_right _ _ _ _ _ _ _ _) (putTwo_away _ _ _ _ _ _ _ _ B.distinct.symm (adj_ne B.right).symm)
  exact two_maps H f A B p q hp hq hpq (Gap G q (f r)) (gap_symm _ _ _)
    (fun i j e => Or.inl (hf i j e)) (Or.inl hleft) (Or.inl hmid) (Or.inr (Or.inl ⟨rfl,rfl⟩))

/-- Exact number of two-edge moves, with the middle role of each move certified. -/
def Chain (H : SimpleGraph W) : ℕ → W → W → Prop
  | 0, u, v => u = v
  | k+1, u, v => ∃ w m, Chain H k u w ∧ TwoNeighbours H m w v

def Marked (G : SimpleGraph V) (f : W ↪ V) (P : Set V) (u : W) : Prop :=
  ∀ z ∈ P, G.Adj z (f u)

def Joined (G : SimpleGraph V) (P Q : Set V) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q

theorem time_mono (H : SimpleGraph W) (G : SimpleGraph V) {i j : ℕ} (h : i ≤ j) :
    run H G i ≤ run H G j := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact le_trans ih (run_le_succ H G _)

theorem full_later {H : SimpleGraph W} {G : SimpleGraph V} {f : W ↪ V} {i j : ℕ}
    (h : i ≤ j) (hf : FullCopy H (run H G i) f) : FullCopy H (run H G j) f :=
  fun u v e => time_mono H G h (hf u v e)

/-- Every outside vertex follows the same sequence independently in the indicated time. -/
theorem along_chain (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V) (t : ℕ)
    (hf : FullCopy H (run H G t) f) {k : ℕ} {u v : W} (hc : Chain H k u v)
    (z : V) (hz : Outside f z) (hstart : (run H G t).Adj z (f u)) :
    (run H G (t+k)).Adj z (f v) := by
  induction k generalizing v with
  | zero =>
    have he : u = v := hc
    subst v
    exact hstart
  | succ k ih =>
    obtain ⟨w, m, hpath, N⟩ := hc
    change (step H (run H G (t+k))).Adj z (f v)
    exact one_step H _ f (full_later (by omega : t ≤ t+k) hf) N z hz (ih hpath)

/-- Send two sets along possibly unequal length chains and form the full rectangle. -/
theorem rectangle_of_chains (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V) (t s : ℕ)
    (hf : FullCopy H (run H G t) f) {u v l a b r : W}
    (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r)
    {m n : ℕ} (cp : Chain H m u l) (cq : Chain H n v r) (hm : m ≤ s) (hn : n ≤ s)
    (P Q : Set V) (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P u) (mq : Marked (run H G t) f Q v) :
    Joined (run H G (t+s+1)) P Q ∧ Marked (run H G (t+s+1)) f P l := by
  have lp (p : V) (h : p ∈ P) : (run H G (t+s)).Adj p (f l) :=
    time_mono H G (by omega : t+m ≤ t+s) (along_chain H G f t hf cp p (hp p h) (mp p h))
  have rq (q : V) (h : q ∈ Q) : (run H G (t+s)).Adj q (f r) :=
    time_mono H G (by omega : t+n ≤ t+s) (along_chain H G f t hf cq q (hq q h) (mq q h))
  constructor
  · intro p h q h'
    exact two_middle H _ f (full_later (by omega : t ≤ t+s) hf) A B p q
      (hp p h) (hq q h') (hdis p h q h') (lp p h) (rq q h')
  · intro p h
    exact run_le_succ H G (t+s) (lp p h)

theorem TwoNeighbours.reverse {H : SimpleGraph W} {a l r : W}
    (N : TwoNeighbours H a l r) : TwoNeighbours H a r l := by
  refine ⟨N.right, N.left, N.distinct.symm, ?_⟩
  intro j e
  rcases N.only j e with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- A route is indexed up to its length. Endpoints may be the same on returning routes. -/
def Route (H : SimpleGraph W) (x : ℕ → W) (len : ℕ) : Prop :=
  ∀ i, i+2 ≤ len → TwoNeighbours H (x (i+1)) (x i) (x (i+2))

private theorem route_forward {H : SimpleGraph W} {x : ℕ → W} {len : ℕ}
    (route : Route H x len) (s k : ℕ) (fit : s+2*k ≤ len) :
    Chain H k (x s) (x (s+2*k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : s+2*(k+1) = (s+2*k)+2 := by omega
    refine ⟨x (s+2*k), x ((s+2*k)+1), ih (by omega), ?_⟩
    rw [e]
    exact route (s+2*k) (by omega)

private theorem route_backward {H : SimpleGraph W} {x : ℕ → W} {len : ℕ}
    (route : Route H x len) (s k : ℕ) (fit : s+2*k ≤ len) :
    Chain H k (x (s+2*k)) (x s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have e : (s+2)+2*k = s+2*(k+1) := by omega
    have prev := ih (s+2) (by omega)
    rw [e] at prev
    exact ⟨x (s+2), x (s+1), prev, (route s (by omega)).reverse⟩

theorem route_same_parity {H : SimpleGraph W} {x : ℕ → W} {len : ℕ}
    (route : Route H x len) (i j : ℕ) (hi : i ≤ len) (hj : j ≤ len)
    (par : i%2 = j%2) : ∃ k ≤ len, Chain H k (x i) (x j) := by
  by_cases ord : i ≤ j
  · let k := (j-i)/2
    have e : i+2*k = j := by dsimp [k]; omega
    have hc := route_forward route i k (by omega)
    rw [e] at hc
    exact ⟨k, by dsimp [k]; omega, hc⟩
  · let k := (i-j)/2
    have e : j+2*k = i := by dsimp [k]; omega
    have hc := route_backward route j k (by omega)
    rw [e] at hc
    exact ⟨k, by dsimp [k]; omega, hc⟩

/-- Long-route case of II.2, for any edge index. The end vertex receives the
appropriate shore whether the index is even or odd. -/
theorem long_route (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V)
    (t : ℕ) (hf : FullCopy H (run H G t) f) (x : ℕ → W) (len : ℕ)
    (route : Route H x len) (hlen : 3 ≤ len) (i : ℕ) (hi : i < len)
    (P Q : Set V) (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P (x i)) (mq : Marked (run H G t) f Q (x (i+1))) :
    Joined (run H G (t+len+1)) P Q ∧
      (Marked (run H G (t+len+1)) f P (x 0) ∨ Marked (run H G (t+len+1)) f Q (x 0)) := by
  have A := route 0 (by omega)
  have B := route 1 (by omega)
  by_cases even : i%2 = 0
  · obtain ⟨m,hm,cp⟩ := route_same_parity route i 0 (by omega) (by omega) (by omega)
    obtain ⟨n,hn,cq⟩ := route_same_parity route (i+1) 3 (by omega) (by omega) (by omega)
    obtain ⟨joined,mark⟩ := rectangle_of_chains H G f t len hf A B cp cq hm hn P Q hp hq hdis mp mq
    exact ⟨joined, Or.inl mark⟩
  · obtain ⟨m,hm,cp⟩ := route_same_parity route (i+1) 0 (by omega) (by omega) (by omega)
    obtain ⟨n,hn,cq⟩ := route_same_parity route i 3 (by omega) (by omega) (by omega)
    obtain ⟨joined,mark⟩ := rectangle_of_chains H G f t len hf A B cp cq hm hn Q P hq hp
      (fun q hq' p hp' => (hdis p hp' q hq').symm) mq mp
    exact ⟨fun p hp' q hq' => (run H G (t+len+1)).symm (joined q hq' p hp'), Or.inr mark⟩

theorem old_image_outside (f : W ↪ V) (a : W) (p : V) (hp : Outside f p) :
    Outside (putRole f a p hp) (f a) := by
  intro i
  by_cases h : i = a
  · subst i
    rw [putRole_here]
    exact (hp a).symm
  · rw [putRole_away _ _ _ _ h]
    exact fun e => h (f.injective e)

/-- Short-route case of II.2. The original midpoint is displaced, propagated
on the changed full copy, and then used with the untouched original copy.
The integer k bounds the short-route distance and is at least one. -/
theorem short_route (H : SimpleGraph W) (G : SimpleGraph V) (f : W ↪ V)
    (t : ℕ) (hf : FullCopy H (run H G t) f) {w u v l a b r : W}
    (S : TwoNeighbours H w u v) (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r)
    (hrw : r ≠ w) (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ k)
    (path : Chain H d u l) (P Q : Set V) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P u) (mq : Marked (run H G t) f Q w) :
    Joined (run H G (t+k+k+1+1)) P Q ∧ Marked (run H G (t+k+k+1+1)) f P l := by
  obtain ⟨p0, hp0⟩ := hP
  let g := putRole f w p0 (hp p0 hp0)
  have fix : ∀ i, i ≠ w → g i = f i := fun _ h => putRole_away _ _ _ _ h
  have hf1 : FullCopy H (run H G (t+k)) f := full_later (by omega : t ≤ t+k) hf
  have marked_l (p : V) (h : p ∈ P) : (run H G (t+k)).Adj p (f l) :=
    time_mono H G (by omega : t+d ≤ t+k) (along_chain H G f t hf path p (hp p h) (mp p h))
  have shifted_copy : FullCopy H (run H G (t+k)) g := by
    apply putRole_full H _ f hf1 w p0 (hp p0 hp0)
    intro j e
    rcases S.only j e with h | h
    · rw [h]
      exact time_mono H G (by omega : t ≤ t+k) (mp p0 hp0)
    · rw [h]
      exact time_mono H G (by omega : t+1 ≤ t+k) (one_step H _ f hf S p0 (hp p0 hp0) (mp p0 hp0))
  have old_out : Outside g (f w) := old_image_outside f w p0 (hp p0 hp0)
  have start_old : (run H G (t+k)).Adj (f w) (g u) := by
    rw [fix u (adj_ne S.left).symm]
    exact hf1 w u S.left
  have at_end : (run H G (t+k+k)).Adj (f w) (g l) :=
    time_mono H G (by omega : t+k+d ≤ t+k+k)
      (along_chain H G g (t+k) shifted_copy path (f w) old_out start_old)
  have right_contact (q : V) (h : q ∈ Q) : (run H G (t+k+k+1)).Adj q (f r) := by
    rw [← fix r hrw]
    exact two_right H _ g (full_later (by omega : t+k ≤ t+k+k) shifted_copy) A B (f w) q old_out
      (outside_putRole f w p0 q (hp p0 hp0) (hq q h) (hdis p0 hp0 q h)) (hq q h w)
      at_end ((run H G (t+k+k)).symm (time_mono H G (by omega : t ≤ t+k+k) (mq q h)))
  constructor
  · intro p hp' q hq'
    exact two_middle H _ f (full_later (by omega : t ≤ t+k+k+1) hf) A B p q
      (hp p hp') (hq q hq') (hdis p hp' q hq')
      (time_mono H G (by omega : t+k ≤ t+k+k+1) (marked_l p hp')) (right_contact q hq')
  · intro p h
    exact time_mono H G (by omega : t+k ≤ t+k+k+1+1) (marked_l p h)

/-- Combinatorial locations used by the two cases of II.2. This type records
which edge of a long route is given, or the short path of midpoint transfers
from a short edge to a long route. -/
inductive EdgeLocation (H : SimpleGraph W) (base : Set W) (h : ℕ) : W → W → Prop
  | long {x : ℕ → W} {len i : ℕ} (route : Route H x len) (large : 3 ≤ len)
      (size : len ≤ h) (start : x 0 ∈ base) (idx : i < len) :
      EdgeLocation H base h (x i) (x (i+1))
  | short {w u v l a b r : W} {k d : ℕ} (S : TwoNeighbours H w u v)
      (A : TwoNeighbours H a l b) (B : TwoNeighbours H b a r) (start : l ∈ base)
      (hrw : r ≠ w) (hk : 1 ≤ k) (size : k < h) (hd : d ≤ k)
      (path : Chain H d u l) : EdgeLocation H base h u w
  | reverse {x y : W} : EdgeLocation H base h x y → EdgeLocation H base h y x

/-- II.2 for an edge with its route data, with the numerical time bound and
the common-neighbour mark at a base role. -/
theorem two_sets_of_neighbours [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (f : W ↪ V) (t : ℕ) (hf : FullCopy H (run H G t) f) (base : Set W) {x y : W}
    (loc : EdgeLocation H base (Fintype.card W) x y)
    (P Q : Set V) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P x) (mq : Marked (run H G t) f Q y) :
    Joined (run H G (t+2*Fintype.card W)) P Q ∧
      ∃ l ∈ base, Marked (run H G (t+2*Fintype.card W)) f P l ∨
        Marked (run H G (t+2*Fintype.card W)) f Q l := by
  induction loc generalizing P Q with
  | @long z len i route large size start idx =>
    obtain ⟨cross,mark⟩ := long_route H G f t hf z len route large i idx P Q hp hq hdis mp mq
    have grow := time_mono H G (by omega : t+len+1 ≤ t+2*Fintype.card W)
    refine ⟨fun p hp' q hq' => grow (cross p hp' q hq'), z 0, start, ?_⟩
    rcases mark with mark | mark
    · exact Or.inl (fun p h => grow (mark p h))
    · exact Or.inr (fun q h => grow (mark q h))
  | @short w u v l a b r k d S A B start hrw hk size hd path =>
    obtain ⟨cross,mark⟩ := short_route H G f t hf S A B hrw k d hk hd path P Q hP hp hq hdis mp mq
    have grow := time_mono H G (by omega : t+k+k+1+1 ≤ t+2*Fintype.card W)
    exact ⟨fun p hp' q hq' => grow (cross p hp' q hq'), l, start, Or.inl (fun p h => grow (mark p h))⟩
  | reverse _ ih =>
    obtain ⟨cross,l,hl,mark⟩ := ih Q P hQ hP hq hp (fun q hq' p hp' => (hdis p hp' q hq').symm) mq mp
    exact ⟨fun p hp' q hq' => (run H G _).symm (cross q hq' p hp'), l, hl, mark.symm⟩

end DegreeTwo
end Bootstrap

#print axioms Bootstrap.DegreeTwo.putRole_full
#print axioms Bootstrap.DegreeTwo.one_step
#print axioms Bootstrap.DegreeTwo.two_middle
#print axioms Bootstrap.DegreeTwo.two_right
#print axioms Bootstrap.DegreeTwo.along_chain
#print axioms Bootstrap.DegreeTwo.long_route
#print axioms Bootstrap.DegreeTwo.short_route
#print axioms Bootstrap.DegreeTwo.two_sets_of_neighbours
