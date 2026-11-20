import Bootstrap.TypedRound
import Bootstrap.CyclicClock
import Bootstrap.Localization

/-! The actual typed graph trajectory, observed at its cross edges. -/
namespace TypedRound

open Bootstrap.CyclicClock (residue shift crossRun)

private theorem index_residue {n : ℕ} (hn : 0 < n) (i : Fin n) :
    residue n hn (i.val : ℤ) = i := by
  apply Fin.ext
  change ((i.val : ℤ) % (n : ℤ)).toNat = i.val
  have hi := i.isLt
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

private theorem next_residue {n : ℕ} (hn : 0 < n) (i : Fin n) :
    residue n hn ((i.val : ℤ) + 1) = nextIndex i := by
  have hi := i.isLt
  apply Fin.ext
  unfold nextIndex
  split
  · rename_i h
    change (((i.val : ℤ) + 1) % (n : ℤ)).toNat = i.val + 1
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · rename_i h
    change (((i.val : ℤ) + 1) % (n : ℤ)).toNat = 0
    have hlast : (i.val : ℤ) + 1 = n := by omega
    simp [hlast]

private theorem residue_comp {n : ℕ} (hn : 0 < n) (i s : ℤ) :
    residue n hn (((residue n hn i).val : ℤ) + s) = residue n hn (i+s) := by
  apply (Bootstrap.CyclicClock.residue_eq_iff _ _ _ _).mpr
  have hv : ((residue n hn i).val : ℤ) = i % (n : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [hv,Int.emod_add_emod]

private theorem shift_comp {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (u v : ℤ) (z : Fin p × Fin q) :
    shift p q hp hq v (shift p q hp hq u z) = shift p q hp hq (u+v) z := by
  rcases z with ⟨i,j⟩
  exact Prod.ext
    ((residue_comp hp ((i.val : ℤ)+u) v).trans (congrArg (residue p hp) (Int.add_assoc _ _ _)))
    ((residue_comp hq ((j.val : ℤ)+u) v).trans (congrArg (residue q hq) (Int.add_assoc _ _ _)))

private theorem shift_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (z : Fin p × Fin q) :
    shift p q hp hq 0 z = z := by
  rcases z with ⟨i,j⟩
  exact Prod.ext (by simpa [shift] using index_residue hp i)
    (by simpa [shift] using index_residue hq j)

private theorem shift_one {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (i : Fin p) (j : Fin q) :
    shift p q hp hq 1 (i,j) = (nextIndex i,nextIndex j) :=
  Prod.ext (next_residue hp i) (next_residue hq j)

/-- In grow, E at the successor is exactly the backward translate of E. -/
theorem grow_iff_clock {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (E : Fin p × Fin q → Prop) (i : Fin p) (j : Fin q) :
    grow nextIndex nextIndex (fun a b => E (a,b)) i j ↔
      Bootstrap.CyclicClock.step (shift p q hp hq 1) (shift p q hp hq (-1)) E (i,j) := by
  constructor
  · rintro (old | ⟨a,b,ha,hb,old⟩ | old)
    · exact Or.inl old
    · exact Or.inr (Or.inl ⟨(a,b),old,(shift_one hp hq a b).trans (Prod.ext ha hb)⟩)
    · refine Or.inr (Or.inr ⟨shift p q hp hq 1 (i,j),?_,?_⟩)
      · rwa [shift_one]
      · rw [shift_comp]
        exact shift_zero hp hq _
  · rintro (old | ⟨⟨a,b⟩,old,h⟩ | ⟨⟨a,b⟩,old,h⟩)
    · exact Or.inl old
    · rw [shift_one] at h
      exact Or.inr (Or.inl ⟨a,b,congrArg Prod.fst h,congrArg Prod.snd h,old⟩)
    · apply Or.inr; apply Or.inr
      have h' := congrArg (shift p q hp hq 1) h
      rw [shift_comp,show (-1 : ℤ) + 1 = 0 by decide,shift_zero,shift_one] at h'
      exact (congrArg E h').mp old

def graphRun {A B : Type*} (G : SimpleGraph (Host A B)) : ℕ → SimpleGraph (Host A B)
  | 0 => G
  | t+1 => step (graphRun G t)

def origin {p q : ℕ} (i : Fin p) (j : Fin q) : Prop := i.val = 0 ∧ j.val = 0

private theorem clock_origin {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (i : Fin p) (j : Fin q) : crossRun p q hp hq 0 (i,j) ↔ origin i j := by
  simp [Bootstrap.CyclicClock.crossRun,Bootstrap.CyclicClock.run,
    Bootstrap.CyclicClock.diagonal,Bootstrap.CyclicClock.residue,origin,Fin.ext_iff,eq_comm]

theorem graphRun_eq_clock {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (t : ℕ) :
    graphRun (host nextIndex nextIndex (@origin p q)) t =
      host nextIndex nextIndex (fun i j => crossRun p q (by omega) (by omega) t (i,j)) := by
  induction t with
  | zero =>
    apply congrArg (host nextIndex nextIndex)
    funext i j
    exact propext (clock_origin (by omega) (by omega) i j).symm
  | succ t ih =>
    change step (graphRun _ t) = _
    rw [ih,one_typed_round hp hq]
    apply congrArg (host nextIndex nextIndex)
    funext i j
    exact propext (grow_iff_clock (by omega) (by omega) _ i j)

theorem cross_edge_iff {A B : Type*} (sx : A → A) (sy : B → B) (E : A → B → Prop)
    (i : A) (j : B) : (host sx sy E).Adj (xEnd i) (yEnd j) ↔ E i j := by
  simp [host,fixedArc,Pair,xEnd,yEnd]

theorem host_injective {A B : Type*} (sx : A → A) (sy : B → B) :
    Function.Injective (host sx sy) := by
  intro E D he
  funext i j
  apply propext
  rw [← cross_edge_iff sx sy E i j,← cross_edge_iff sx sy D i j,he]

theorem typed_fixed_iff {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (t : ℕ) :
    graphRun (host nextIndex nextIndex (@origin p q)) t =
      graphRun (host nextIndex nextIndex (@origin p q)) (t+1) ↔ p.lcm q / 2 ≤ t := by
  rw [graphRun_eq_clock hp hq,graphRun_eq_clock hp hq]
  refine Iff.trans ?_ (Bootstrap.CyclicClock.crossRun_fixed_iff p q (by omega) (by omega) t)
  constructor
  · intro h
    have he := host_injective _ _ h
    funext z
    rcases z with ⟨i,j⟩
    exact congrFun (congrFun he i) j
  · intro h
    rw [h]

theorem typed_first_stable {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    IsLeast {t : ℕ | graphRun (host nextIndex nextIndex (@origin p q)) t =
      graphRun (host nextIndex nextIndex (@origin p q)) (t+1)} (p.lcm q / 2) :=
  ⟨(typed_fixed_iff hp hq _).mpr le_rfl,fun t ht => (typed_fixed_iff hp hq t).mp ht⟩

end TypedRound


/-! Triangle-freeness for every cross relation, as used to locate the book cores. -/
namespace TypedRound

variable {A B : Type*}

private theorem on_x {sx : A → A} {sy : B → B} {E : A → B → Prop} (a b : Kind × A) :
    (host sx sy E).Adj (.inl a) (.inl b) ↔ pathArc sx a b ∨ pathArc sx b a := by
  simp [host,fixedArc,Pair,xEnd,yEnd]

private theorem on_y {sx : A → A} {sy : B → B} {E : A → B → Prop} (a b : Kind × B) :
    (host sx sy E).Adj (.inr a) (.inr b) ↔ pathArc sy a b ∨ pathArc sy b a := by
  simp [host,fixedArc,Pair,xEnd,yEnd]

private theorem between {sx : A → A} {sy : B → B} {E : A → B → Prop}
    (a : Kind × A) (b : Kind × B) :
    (host sx sy E).Adj (.inl a) (.inr b) ↔ a.1 = .endpoint ∧ b.1 = .endpoint ∧ E a.2 b.2 := by
  rcases a with ⟨k,i⟩
  rcases b with ⟨l,j⟩
  cases k <;> cases l <;> simp [host,fixedArc,Pair,xEnd,yEnd]

private theorem no_track_triangle (s : A → A) (hs : ∀ i, i ≠ s i) (a b c : Kind × A)
    (ab : pathArc s a b ∨ pathArc s b a) (bc : pathArc s b c ∨ pathArc s c b)
    (ca : pathArc s c a ∨ pathArc s a c) : False := by
  rcases a with ⟨ka,i⟩
  rcases b with ⟨kb,j⟩
  rcases c with ⟨kc,l⟩
  cases ka <;> cases kb <;> cases kc <;> simp [pathArc] at ab bc ca
  · exact hs l (ca.trans (ab.trans bc.2)).symm
  · exact hs j (ab.trans (ca.trans bc.2)).symm
  · exact hs l (bc.trans (ab.trans ca.2)).symm
  · exact hs j (bc.trans (ca.trans ab.2)).symm
  · exact hs i (ab.trans (bc.trans ca.2)).symm
  · exact hs i (ca.trans (bc.trans ab.2)).symm

private theorem no_endpoint_edge (s : A → A) (a b : Kind × A)
    (ha : a.1 = .endpoint) (hb : b.1 = .endpoint)
    (e : pathArc s a b ∨ pathArc s b a) : False := by
  rcases a with ⟨k,i⟩
  rcases b with ⟨l,j⟩
  change k = .endpoint at ha
  change l = .endpoint at hb
  subst k; subst l
  exact e.elim id id

/-- The graph on the two cycles is triangle-free for every choice of cross edges. -/
theorem host_triangle_free {sx : A → A} {sy : B → B}
    (hx : ∀ i, i ≠ sx i) (hy : ∀ j, j ≠ sy j) (E : A → B → Prop)
    (a b c : Host A B) (ab : (host sx sy E).Adj a b)
    (bc : (host sx sy E).Adj b c) (ca : (host sx sy E).Adj c a) : False := by
  have symm := (host sx sy E).symm
  have twoX (u v : Kind × A) (z : Kind × B)
      (uv : (host sx sy E).Adj (.inl u) (.inl v))
      (uz : (host sx sy E).Adj (.inl u) (.inr z))
      (vz : (host sx sy E).Adj (.inl v) (.inr z)) : False :=
    no_endpoint_edge sx u v ((between _ _).mp uz).1 ((between _ _).mp vz).1 ((on_x _ _).mp uv)
  have twoY (u v : Kind × B) (z : Kind × A)
      (uv : (host sx sy E).Adj (.inr u) (.inr v))
      (zu : (host sx sy E).Adj (.inl z) (.inr u))
      (zv : (host sx sy E).Adj (.inl z) (.inr v)) : False :=
    no_endpoint_edge sy u v ((between _ _).mp zu).2.1 ((between _ _).mp zv).2.1 ((on_y _ _).mp uv)
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases c with
      | inl c => exact no_track_triangle sx hx a b c ((on_x _ _).mp ab) ((on_x _ _).mp bc) ((on_x _ _).mp ca)
      | inr c => exact twoX a b c ab (symm ca) bc
    | inr b =>
      cases c with
      | inl c => exact twoX c a b ca (symm bc) ab
      | inr c => exact twoY b c a bc ab (symm ca)
  | inr a =>
    cases b with
    | inl b =>
      cases c with
      | inl c => exact twoX b c a bc (symm ab) ca
      | inr c => exact twoY c a b ca bc (symm ab)
    | inr b =>
      cases c with
      | inl c => exact twoY a b c ab ca (symm bc)
      | inr c => exact no_track_triangle sy hy a b c ((on_y _ _).mp ab) ((on_y _ _).mp bc) ((on_y _ _).mp ca)

theorem triangleFree {sx : A → A} {sy : B → B}
    (hx : ∀ i, i ≠ sx i) (hy : ∀ j, j ≠ sy j) (E : A → B → Prop) :
    Bootstrap.Localization.TriangleFree (host sx sy E) := by
  intro a b c hab hac hbc
  exact host_triangle_free hx hy E a b c hab hbc ((host sx sy E).symm hac)

end TypedRound

#print axioms TypedRound.graphRun_eq_clock
#print axioms TypedRound.typed_first_stable
#print axioms TypedRound.triangleFree
