import Bootstrap.CliqueAbsorption
import Bootstrap.Asymptotics

/-! Amortisation along the actual synchronous process. The minimum size of a
partition into cliques drops whenever a new containing clique absorbs its contacts. -/
namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

private theorem degree_mono [Fintype V] {G D : SimpleGraph V} (h : G ≤ D) (x : V) :
    G.degree x ≤ D.degree x := by
  apply Finset.card_le_card
  exact fun y hy => (D.mem_neighborFinset x y).mpr (h ((G.mem_neighborFinset _ _).mp hy))

private theorem degree_rises [Fintype V] {G D : SimpleGraph V} {x y : V} (h : G ≤ D)
    (old : ¬G.Adj x y) (new : D.Adj x y) : G.degree x < D.degree x := by
  apply Finset.card_lt_card
  refine ⟨?_,?_⟩
  · exact fun z hz => (D.mem_neighborFinset _ _).mpr (h ((G.mem_neighborFinset _ _).mp hz))
  · intro back
    exact old ((G.mem_neighborFinset x y).mp (back ((D.mem_neighborFinset x y).mpr new)))

private noncomputable def lowCells [Fintype V] (G : SimpleGraph V) (J : ℕ) : Finset (V × Fin J) :=
  Finset.univ.filter fun a => a.2.val < G.degree a.1

private theorem low_sub [Fintype V] {G D : SimpleGraph V} (h : G ≤ D) (J : ℕ) :
    lowCells G J ⊆ lowCells D J := by
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le (Finset.mem_filter.mp ha).2 (degree_mono h a.1)⟩

private theorem low_bounded [Fintype V] (G : SimpleGraph V) (J : ℕ) :
    (lowCells G J).card ≤ Fintype.card V * J := by
  simpa [Fintype.card_prod] using Finset.card_le_univ (lowCells G J)

private theorem low_rises [Fintype V] {G D : SimpleGraph V} {x y : V} (h : G ≤ D)
    (old : ¬G.Adj x y) (new : D.Adj x y) {J : ℕ} (low : D.degree x < J) :
    (lowCells G J).card < (lowCells D J).card := by
  have inc := degree_rises h old new
  let a : V × Fin J := (x,⟨G.degree x,by omega⟩)
  have aNew : a ∈ lowCells D J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩
  have aOld : a ∉ lowCells G J := fun ha => (Nat.lt_irrefl _) (Finset.mem_filter.mp ha).2
  exact Finset.card_lt_card ⟨low_sub h J,fun back => aOld (back aNew)⟩

def CliqueLabel (G : SimpleGraph V) (L : V → V) : Prop :=
  ∀ ⦃x y⦄, L x = L y → x ≠ y → G.Adj x y

private noncomputable def labels [Fintype V] (L : V → V) : Finset V := Finset.univ.image L

private theorem labels_exist [Fintype V] (G : SimpleGraph V) :
    ∃ k : ℕ, ∃ L : V → V, CliqueLabel G L ∧ (labels L).card = k :=
  ⟨_,id,(fun _ _ same ne => False.elim (ne same)),rfl⟩

noncomputable def blockCount [Fintype V] (G : SimpleGraph V) : ℕ := Nat.find (labels_exist G)

private theorem best [Fintype V] (G : SimpleGraph V) :
    ∃ L : V → V, CliqueLabel G L ∧ (labels L).card = blockCount G := Nat.find_spec (labels_exist G)

private theorem block_le [Fintype V] {G : SimpleGraph V} {L : V → V} (hv : CliqueLabel G L) :
    blockCount G ≤ (labels L).card := Nat.find_min' (labels_exist G) ⟨L,hv,rfl⟩

private theorem block_bounded [Fintype V] (G : SimpleGraph V) : blockCount G ≤ Fintype.card V := by
  obtain ⟨L,_,h⟩ := best G
  rw [← h]
  exact Finset.card_le_univ _

private theorem block_anti [Fintype V] {G D : SimpleGraph V} (h : G ≤ D) : blockCount D ≤ blockCount G := by
  obtain ⟨L,hv,hs⟩ := best G
  rw [← hs]; exact block_le (fun _ _ e ne => h (hv e ne))

private noncomputable def touching [Fintype V] (S : Finset V) (L : V → V) : Finset V :=
  Finset.univ.filter fun z => ∃ s ∈ S, L s = L z

private theorem touching_iff [Fintype V] (S : Finset V) (L : V → V) (z : V) :
    z ∈ touching S L ↔ ∃ s ∈ S, L s = L z := by simp [touching]

private theorem block_drops [Fintype V] {G D : SimpleGraph V} (increase : G ≤ D)
    (S : Finset V) {x y : V} (xs : x ∈ S) (ys : y ∈ S) (xy : x ≠ y) (old : ¬ G.Adj x y)
    (merged : ∀ L, CliqueLabel G L → CliqueOn D (touching S L)) : blockCount D < blockCount G := by
  classical
  obtain ⟨L,hvalid,hbest⟩ := best G
  let T := touching S L
  have tx : x ∈ T := (touching_iff _ _ _).mpr ⟨x,xs,rfl⟩
  have ty : y ∈ T := (touching_iff _ _ _).mpr ⟨y,ys,rfl⟩
  have same (a b : V) (hb : b ∈ T) (eq : L a = L b) : a ∈ T := by
    obtain ⟨s,hs,e⟩ := (touching_iff _ _ _).mp hb
    exact (touching_iff _ _ _).mpr ⟨s,hs,e.trans eq.symm⟩
  have diff : L x ≠ L y := fun e => old (hvalid e xy)
  let M (z : V) := if z ∈ T then L x else L z
  have ok : CliqueLabel D M := by
    intro a b he ne
    by_cases at' : a ∈ T <;> by_cases bt : b ∈ T
    · exact merged L hvalid at' bt ne
    · have eq : L x = L b := by simpa [M,at',bt] using he
      exact False.elim (bt (same b x tx eq.symm))
    · have eq : L a = L x := by simpa [M,at',bt] using he
      exact False.elim (at' (same a x tx eq))
    · exact increase (hvalid (by simpa [M,at',bt] using he) ne)
  have sub : labels M ⊆ (labels L).erase (L y) := by
    intro k hk
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hk
    by_cases hz : z ∈ T
    · exact Finset.mem_erase.mpr ⟨(by simpa [M,hz] using diff),
        (by simp [M,hz,labels])⟩
    · have neq : L z ≠ L y := fun eq => hz (same z y ty eq)
      exact Finset.mem_erase.mpr ⟨(by simpa [M,hz] using neq),
        (by simp [M,hz,labels])⟩
  have present : L y ∈ labels L := Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩
  have strict := Finset.card_lt_card (Finset.erase_ssubset present)
  exact (block_le ok).trans_lt ((Finset.card_le_card sub).trans_lt (hbest ▸ strict))

/-- Every double-high birth has a large containing clique by t+B, measured
from the old time t. Low degrees refer to its completion at t+1. -/
def HighClique [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (J B : ℕ) : Prop :=
  ∀ t x y, ¬ (run H G t).Adj x y → (run H G (t+1)).Adj x y →
    J ≤ (run H G (t+1)).degree x → J ≤ (run H G (t+1)).degree y →
    ∃ S : Finset V, Fintype.card W ≤ S.card ∧ x ∈ S ∧ y ∈ S ∧ CliqueOn (run H G (t+B)) S

private theorem high_drop [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {a l r : W} (N : TwoNeighbours H a l r) {J B : ℕ} (high : HighClique H G J B)
    {t : ℕ} {x y : V} (old : ¬(run H G t).Adj x y) (birth : (run H G (t+1)).Adj x y)
    (hx : J ≤ (run H G (t+1)).degree x) (hy : J ≤ (run H G (t+1)).degree y) :
    blockCount (run H G (t+(B+2))) < blockCount (run H G t) := by
  obtain ⟨S,hsize,xs,ys,cl⟩ := high t x y old birth hx hy
  apply block_drops (time_mono H G (by omega)) S xs ys birth.ne old
  intro L ok
  have contact (z : V) (hz : z ∈ touching S L) (out : z ∉ S) :
      ∃ s ∈ S, (run H G (t+B)).Adj z s := by
    obtain ⟨s,hs,e⟩ := (touching_iff _ _ _).mp hz
    exact ⟨s,hs,time_mono H G (by omega) (ok e.symm (fun h => out (h ▸ hs)))⟩
  simpa only [show t+(B+2)=t+B+1+1 by omega,run_succ] using
    absorbs_touching H (run H G (t+B)) N S (touching S L) hsize cl contact

theorem clique_clock [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {a l r : W} (N : TwoNeighbours H a l r) (J B : ℕ) (high : HighClique H G J B) :
    stabilizationTime H G ≤ (J+B+2) * Fintype.card V := by
  classical
  let n := Fintype.card V
  let c := B+2
  let low (t : ℕ) := (lowCells (run H G t) J).card
  let rank (t : ℕ) := blockCount (run H G t)
  let credit (t : ℕ) := (n*J-low t) + c * rank t
  have loBound t : low t ≤ n*J := low_bounded (run H G t) J
  have loMono {i j} (h : i ≤ j) : low i ≤ low j := Finset.card_le_card (low_sub (time_mono H G h) J)
  have rankAnti {i j} (h : i ≤ j) : rank j ≤ rank i := block_anti (time_mono H G h)
  have advance (t : ℕ) (active : ¬ run H G t = run H G (t+1)) :
      ∃ k : ℕ, 0 < k ∧ credit (t+k) + k ≤ credit t := by
    have ex : ∃ x y, (run H G (t+1)).Adj x y ∧ ¬ (run H G t).Adj x y := by
      by_contra! h
      apply active
      exact le_antisymm (run_le_succ H G t) (fun x y hxy => h x y hxy)
    obtain ⟨x,y,birth,old⟩ := ex
    have lowCharge (z w : V) (o : ¬(run H G t).Adj z w) (born : (run H G (t+1)).Adj z w)
        (small : (run H G (t+1)).degree z < J) :
        ∃ k : ℕ, 0 < k ∧ credit (t+k) + k ≤ credit t := by
      have grow : low t < low (t+1) := low_rises (run_le_succ H G t) o born small
      have cost := Nat.mul_le_mul_left c (rankAnti (by omega : t ≤ t+1))
      exact ⟨1,by omega,by dsimp only [credit]; have := loBound (t+1); omega⟩
    by_cases dx : J ≤ (run H G (t+1)).degree x
    · by_cases dy : J ≤ (run H G (t+1)).degree y
      · have drop : rank (t+c) < rank t := high_drop H G N high old birth dx dy
        have cost := Nat.mul_le_mul_left c (Nat.succ_le_of_lt drop)
        rw [Nat.mul_succ] at cost
        have lb := loMono (show t ≤ t+c by omega)
        refine ⟨c,by dsimp [c]; omega,?_⟩
        dsimp only [credit]
        omega
      · exact lowCharge y x (fun e => old ((run H G t).symm e)) ((run H G (t+1)).symm birth) (by omega)
    · exact lowCharge x y old birth (by omega)
  have all (t : ℕ) : stabilizationTime H G ≤ t+credit t := by
    generalize hk : credit t = k
    induction k using Nat.strong_induction_on generalizing t with
    | h k ih =>
      by_cases done : stabilizationTime H G ≤ t
      · omega
      have active : ¬ run H G t = run H G (t+1) := by
        intro fix
        exact done (Nat.find_min' (stable_exists H G) fix)
      obtain ⟨d,dp,less⟩ := advance t active
      have sk : credit (t+d) < k := by omega
      have later := ih _ sk (t+d) rfl
      omega
  have first := all 0
  have maxRank : rank 0 ≤ n := block_bounded _
  have bnd := Nat.mul_le_mul_left c maxRank
  have bound : credit 0 ≤ n*J + c*n := by dsimp only [credit]; omega
  calc
    stabilizationTime H G ≤ credit 0 := by simpa using first
    _ ≤ n*J + c*n := bound
    _ = (J+B+2)*Fintype.card V := by dsimp [n,c]; rw [Nat.mul_comm (Fintype.card V) J,← Nat.add_mul]; congr 1

theorem high_one_monochrome [Fintype W] [Fintype V] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    (mono : OneMonochrome H) : HighClique H G (3*Fintype.card W-1) (2*Fintype.card W+2) := by
  classical
  intro t x y old born dx dy
  obtain ⟨f,u,v,p,_,_,_,_,apart,pl,qr,cross,_⟩ := high_birth_seed H G conn root cover long t born old dx dy
  let L := insert y p.left
  let R := insert x p.right
  have rl : Fintype.card W ≤ L.card := by dsimp [L]; omega
  have rr : Fintype.card W ≤ R.card := by dsimp [R]; omega
  refine ⟨L ∪ R,rl.trans (Finset.card_le_card Finset.subset_union_left),
    Finset.mem_union_right L (Finset.mem_insert_self _ _),Finset.mem_union_left R (Finset.mem_insert_self _ _),?_⟩
  have cl := one_monochrome_clique H _ mono L R rl rr apart cross
  simpa only [show t+(2*Fintype.card W+2) = (t+1+2*Fintype.card W)+1 by omega,run_succ] using cl

theorem linear_of_one_monochrome [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    (mono : OneMonochrome H) : HasLinearUpper H := by
  classical
  obtain ⟨i,j,_,di,_⟩ := id long
  obtain ⟨l,r,N⟩ := (hasTwo_iff_degree H i).mpr di
  refine ⟨(3*Fintype.card W-1)+(2*Fintype.card W+2)+2,0,?_⟩
  intro n _
  apply (maxTime_le_iff H n _).mpr
  intro G
  simpa only [Fintype.card_fin] using
    clique_clock H G N _ _ (high_one_monochrome H G conn root cover long mono)

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.clique_clock
#print axioms Bootstrap.DegreeTwo.linear_of_one_monochrome
