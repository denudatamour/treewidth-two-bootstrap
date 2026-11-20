import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.EquivFin
import Bootstrap.ConnectedDegreeTwo

/-! Neighborhood contraction on a short arm of a primitive theta graph.
All complements in this module are ordinary finite simple graphs. -/
namespace Bootstrap.Theta.Contraction

variable {X : Type*} [Fintype X] [DecidableEq X]

def strip (p : Nat → X) (l h : Nat) : Finset X := (Finset.Ico l h).image p

omit [Fintype X] in
theorem mem_strip {p : Nat → X} {l h : Nat} {x : X} :
    x ∈ strip p l h ↔ ∃ t, l ≤ t ∧ t < h ∧ p t = x := by
  simp [strip,Finset.mem_image,Finset.mem_Ico,and_assoc]

def Closed (Q : SimpleGraph X) (S : Finset X) := ∀ x y, Q.Adj x y → (x ∈ S ↔ y ∈ S)

/-- A neighbour outside S forces more than f distinct outside neighbours, for example
the first f+1 entries of its orbit under a permutation fixing the selected vertex. -/
def OutsideOrbit (Q : SimpleGraph X) (S : Finset X) (f : Nat) := ∀ z ∈ S, ∀ w,
  Q.Adj z w → w ∉ S → ∃ e : Fin (f+1) ↪ X, ∀ i, Q.Adj z (e i) ∧ e i ∉ S

/-- Length f, or length 2f in which all neighbours of a vertex have one coordinate parity. -/
def Thin (Q : SimpleGraph X) (p : Nat → X) (L s f : Nat) : Prop :=
  s = f ∨ (s = 2*f ∧ ∀ z i j, i < L → j < L →
    Q.Adj z (p i) → Q.Adj z (p j) → i % 2 = j % 2)

private theorem impossible_injection (f : Nat) (k : Fin (f+1) → Fin f)
    (inj : Function.Injective k) : False := by
  have h := Fintype.card_le_of_injective k inj
  simp only [Fintype.card_fin] at h
  omega

private theorem outside_free {Q : SimpleGraph X} {p : Nat → X} {L a s f l : Nat}
    {z : X} (hl : 1 ≤ l) (nl : a+s ≤ L) (hz : z ∈ strip p 1 a)
    (thin : Thin Q p L s f) (big : OutsideOrbit Q (strip p 1 a) f)
    (row : ∀ w, Q.Adj z w → w ∈ strip p l (a+s)) :
    ∀ w, Q.Adj z w → w ∈ strip p 1 a := by
  classical
  intro w zw
  by_contra bad
  obtain ⟨e,he⟩ := big z hz w zw bad
  choose j low high at' using (fun i => mem_strip.mp (row (e i) (he i).1))
  have lo (i : Fin (f+1)) : a ≤ j i := by
    by_contra! h
    exact (he i).2 (mem_strip.mpr ⟨j i,hl.trans (low i),h,at' i⟩)
  have inj : Function.Injective j := by
    intro i k eq
    exact e.injective ((at' i).symm.trans ((congrArg p eq).trans (at' k)))
  rcases thin with same | ⟨twice,par⟩
  · let k (i : Fin (f+1)) : Fin f := ⟨j i - a,by have := high i; have := lo i; omega⟩
    apply impossible_injection f k
    intro i r h
    have e : j i - a = j r - a := congrArg Fin.val h
    exact inj (by have := lo i; have := lo r; omega)
  · let k (i : Fin (f+1)) : Fin f := ⟨(j i - a)/2,by have := high i; have := lo i; omega⟩
    apply impossible_injection f k
    intro i r h
    have e : (j i - a)/2 = (j r - a)/2 := congrArg Fin.val h
    have color := par z (j i) (j r) ((high i).trans_le nl) ((high r).trans_le nl)
      ((at' i).symm ▸ (he i).1) ((at' r).symm ▸ (he r).1)
    exact inj (by have := lo i; have := lo r; omega)

/-- A regular graph on the chart, a shift, and one confined initial neighborhood
force the entire open arm to be closed under adjacency. The parameter K counts
shifts up to the last interval, where only f-1 vertices remain. -/
theorem closed_of_seed (Q : SimpleGraph X) [DecidableRel Q.Adj] (p : Nat → X)
    (L a s f K ρ : Nat) (hf : 2 ≤ f) (endAt : a = K*s + f) (noWrap : a+s ≤ L)
    (coords : ∀ u v, u < L → v < L → p u = p v → u = v)
    (σ : Q ≃g Q) (shift : ∀ u, u+s < L → σ (p u) = p (u+s))
    (reg : ∀ x, Q.degree x = ρ) (thin : Thin Q p L s f)
    (orbit : OutsideOrbit Q (strip p 1 a) f)
    (seed : ∀ y, Q.Adj (p 1) y → y ∈ strip p 1 a) : Closed Q (strip p 1 a) := by
  classical
  have rows (j : Nat) (hj : j ≤ K) :
      ∀ y, Q.Adj (p (j*s+1)) y → y ∈ strip p (j*s+1) a := by
    induction j with
    | zero => simpa only [Nat.zero_mul,Nat.zero_add] using seed
    | succ j ih =>
      have prev := ih (by omega)
      have bound : (j+1)*s+1 < a := by
        have h := Nat.mul_le_mul_right s hj
        omega
      have advance : (j+1)*s+1 = j*s+1+s := by rw [Nat.add_mul];omega
      have id : σ (p (j*s+1)) = p ((j+1)*s+1) := by
        rw [advance]
        exact shift _ (by omega)
      have hz : p ((j+1)*s+1) ∈ strip p 1 a := mem_strip.mpr ⟨_,by omega,bound,rfl⟩
      have expanded (y : X) (e : Q.Adj (p ((j+1)*s+1)) y) :
          y ∈ strip p ((j+1)*s+1) (a+s) := by
        obtain ⟨y,rfl⟩ := σ.surjective y
        have ee : Q.Adj (p (j*s+1)) y := σ.map_adj_iff.mp (id.symm ▸ e)
        obtain ⟨t,le,lt,pt⟩ := mem_strip.mp (prev y ee)
        refine mem_strip.mpr ⟨t+s,by omega,by omega,?_⟩
        exact (shift t (by omega)).symm.trans (congrArg σ pt)
      have inside := outside_free (z:=p ((j+1)*s+1)) (l:=(j+1)*s+1) (by omega)
        noWrap hz thin orbit expanded
      intro y e
      obtain ⟨t,lo,hi,pt⟩ := mem_strip.mp (expanded y e)
      obtain ⟨r,_,ra,pr⟩ := mem_strip.mp (inside y e)
      have eq := coords t r (by omega) (by omega) (pt.trans pr.symm)
      exact mem_strip.mpr ⟨t,lo,by omega,pt⟩
  have last := rows K le_rfl
  have small : Q.degree (p (K*s+1)) ≤ f-1 := by
    change (Q.neighborFinset _).card ≤ _
    calc
      _ ≤ (strip p (K*s+1) a).card := Finset.card_le_card (fun y hy =>
          last y ((Q.mem_neighborFinset _ _).mp hy))
      _ ≤ (Finset.Ico (K*s+1) a).card := Finset.card_image_le
      _ = f-1 := by rw [Nat.card_Ico];omega
  rw [reg] at small
  have stays (z : X) (hz : z ∈ strip p 1 a) (w : X) (zw : Q.Adj z w) :
      w ∈ strip p 1 a := by
    by_contra bad
    obtain ⟨e,he⟩ := orbit z hz w zw bad
    let inc (i : Fin (f+1)) : Q.neighborSet z := ⟨e i,(he i).1⟩
    have h := Fintype.card_le_of_injective inc (fun i j eq => e.injective (congrArg Subtype.val eq))
    rw [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree,reg] at h
    omega
  exact fun x y xy => ⟨fun hx => stays x hx y xy,fun hy => stays y hy x xy.symm⟩


omit [Fintype X] [DecidableEq X] in
private theorem shift_edge {Q : SimpleGraph X} {p : Nat → X} {L s : Nat}
    (σ : Q ≃g Q) (shift : ∀ u, u+s < L → σ (p u) = p (u+s))
    (u v k : Nat) (lu : u+k*s < L) (lv : v+k*s < L) (e : Q.Adj (p u) (p v)) :
    Q.Adj (p (u+k*s)) (p (v+k*s)) := by
  induction k with
  | zero => simpa using e
  | succ k ih =>
    rw [Nat.succ_mul] at lu lv ⊢
    have prev := ih (by omega) (by omega)
    have next := σ.map_adj_iff.mpr prev
    rw [shift _ (by omega),shift _ (by omega)] at next
    simpa only [Nat.add_assoc] using next

/-- The two boundary tests isolate the coordinate f. For a double-step shift,
the reflection followed by the shift fixes f and interchanges the two sides of f. -/
theorem empty_of_closed (Q : SimpleGraph X) [DecidableRel Q.Adj] (p : Nat → X)
    (L a s f K ρ : Nat) (hf : 2 ≤ f) (hk : 1 ≤ K) (endAt : a = K*s+f)
    (noWrap : a+s ≤ L) (coords : ∀ u v, u < L → v < L → p u = p v → u = v)
    (σ : Q ≃g Q) (shift : ∀ u, u+s < L → σ (p u) = p (u+s))
    (sides : s = f ∨ (s = 2*f ∧ ∃ τ : Q ≃g Q, ∀ i, i ≤ s → τ (p i) = p (s-i)))
    (reg : ∀ z, Q.degree z = ρ) (closed : Closed Q (strip p 1 a)) : Q = ⊥ := by
  classical
  have fs : f ≤ s := sides.elim (fun e => e ▸ le_rfl) (fun h => by rw [h.1];omega)
  have sk : s ≤ K*s := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right s hk
  have sf : p f ∈ strip p 1 a := mem_strip.mpr ⟨f,by omega,by omega,rfl⟩
  have ext : p a ∉ strip p 1 a := by
    intro h
    obtain ⟨u,_,ua,eu⟩ := mem_strip.mp h
    have := coords u a (by omega) (by omega) eu
    omega
  have interval (w : X) (fw : Q.Adj (p f) w) : ∃ j, f ≤ j ∧ j ≤ s ∧ p j = w := by
    obtain ⟨j,j₀,ja,pj⟩ := mem_strip.mp ((closed _ _ fw).mp sf)
    have ej : Q.Adj (p f) (p j) := pj ▸ fw
    have upper : j ≤ s := by
      by_contra! h
      have js : p (j-s) ∈ strip p 1 a := mem_strip.mpr ⟨_,by omega,by omega,rfl⟩
      have sj : σ (p (j-s)) = p j := by
        rw [shift _ (by omega),Nat.sub_add_cancel h.le]
      obtain ⟨v,hv⟩ := σ.surjective (p f)
      have raw : Q.Adj v (p (j-s)) := σ.map_adj_iff.mp (by rw [hv,sj]; exact ej)
      obtain ⟨u,u₀,ua,uv⟩ := mem_strip.mp ((closed _ _ raw).mpr js)
      have eq : p (u+s) = p f := (shift u (by omega)).symm.trans ((congrArg σ uv).trans hv)
      have := coords (u+s) f (by omega) (by omega) eq
      omega
    have lower : f ≤ j := by
      by_contra! h
      have moved := shift_edge σ shift f j K (by omega) (by omega) ej
      have target : p (j+K*s) ∈ strip p 1 a := mem_strip.mpr ⟨_,by omega,by omega,rfl⟩
      exact ext (by simpa only [show f+K*s=a by omega] using (closed _ _ moved).mpr target)
    exact ⟨j,lower,upper,pj⟩
  have lonely (w : X) (fw : Q.Adj (p f) w) : False := by
    obtain ⟨j,lo,hi,rfl⟩ := interval w fw
    rcases sides with h | ⟨s₂,τ,flip⟩
    · have eq : j = f := by omega
      exact fw.ne (congrArg p eq.symm)
    · have e := τ.map_adj_iff.mpr fw
      rw [flip _ fs,show s-f=f by omega,flip _ hi] at e
      obtain ⟨r,le,_,er⟩ := interval _ e
      have eq := coords r (s-j) (by omega) (by omega) er
      have jf : j = f := by omega
      exact fw.ne (congrArg p jf.symm)
  have hzero : Q.degree (p f) = 0 := by
    by_contra! pos
    obtain ⟨w,hw⟩ := (Q.degree_pos_iff_exists_adj (p f)).mp (Nat.pos_of_ne_zero pos)
    exact lonely w hw
  rw [reg] at hzero
  apply bot_unique
  intro u v uv
  have pos := (Q.degree_pos_iff_exists_adj u).mpr ⟨v,uv⟩
  rw [reg,hzero] at pos
  omega

end Bootstrap.Theta.Contraction

#print axioms Bootstrap.Theta.Contraction.closed_of_seed
#print axioms Bootstrap.Theta.Contraction.empty_of_closed
