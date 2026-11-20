import Bootstrap.ThetaRules
import Mathlib.Algebra.Group.Fin.Basic

namespace Bootstrap.Theta

open scoped Classical
variable {k : ℕ}

def armSize (m : Fin k → ℕ) (i : Fin k) := m i+2
def perimeter (m : Fin k → ℕ) (i j : Fin k) := armSize m i+armSize m j
instance perimeter_ne (m : Fin k → ℕ) (i j : Fin k) : NeZero (perimeter m i j) :=
  ⟨by simp [perimeter,armSize]⟩

def OnCycle {m : Fin k → ℕ} (i j : Fin k) : Vertex m → Prop
  | .inl _ => True
  | .inr ⟨k,_⟩ => k=i ∨ k=j

def cyclePt (m : Fin k → ℕ) (i j : Fin k) (z : Fin (perimeter m i j)) : Vertex m :=
  if h0 : z.val=0 then pole m false else
  if ha : z.val=armSize m i then pole m true else
  if h : z.val<armSize m i then inner m i ⟨z.val-1,by dsimp [armSize] at h; omega⟩
  else inner m j ⟨perimeter m i j-z.val-1,by
    have := z.isLt
    dsimp [perimeter,armSize] at *; omega⟩

def vertexCoord (m : Fin k → ℕ) (i j : Fin k) : Vertex m → Fin (perimeter m i j)
  | .inl false => 0
  | .inl true => ⟨armSize m i,by simp [perimeter,armSize]⟩
  | .inr ⟨a,d⟩ =>
    if h : a=i then ⟨d.val+1,by subst a; have := d.isLt; dsimp [perimeter,armSize]; omega⟩
    else if a=j then ⟨perimeter m i j-(d.val+1),by dsimp [perimeter,armSize]; omega⟩
    else 0

theorem cyclePt_on (m : Fin k → ℕ) (i j : Fin k) (x : Fin (perimeter m i j)) :
    OnCycle i j (cyclePt m i j x) := by
  unfold cyclePt
  split
  · trivial
  split
  · trivial
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem coord_pt (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (x : Fin (perimeter m i j)) :
    vertexCoord m i j (cyclePt m i j x) = x := by
  apply Fin.ext
  unfold cyclePt
  split
  · change 0 = x.val; omega
  split
  · change armSize m i = x.val; omega
  split
  · simp only [inner,vertexCoord,dif_pos rfl,dite_true,ite_true,Fin.val_mk]; omega
  · simp only [inner,vertexCoord,dif_neg ij.symm,if_pos rfl,dite_true,ite_true,Fin.val_mk]
    have := x.isLt
    omega

theorem pt_coord (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (x : Vertex m) (on' : OnCycle i j x) :
    cyclePt m i j (vertexCoord m i j x) = x := by
  rcases x with b|⟨a,d⟩
  · cases b
    · simp [vertexCoord,cyclePt,pole]
    · have pos : armSize m i ≠ 0 := by simp [armSize]
      simp [vertexCoord,cyclePt,pos,pole]
  · rcases on' with rfl|rfl
    · have h := d.isLt
      have lt : d.val+1<armSize m a := by dsimp [armSize]; omega
      simp only [vertexCoord,dif_pos rfl,cyclePt,Nat.succ_ne_zero,Fin.val_mk,dif_neg (Nat.ne_of_lt lt),dif_pos lt,
        Nat.add_sub_cancel,inner,dite_true,ite_true,dite_false]
    · have h := d.isLt
      have big : armSize m i < perimeter m i a-(d.val+1) := by dsimp [armSize,perimeter]; omega
      have non : perimeter m i a-(d.val+1) ≠ 0 := by omega
      simp only [vertexCoord,dif_neg ij.symm,if_pos rfl,cyclePt,Fin.val_mk,dif_neg non,
        dif_neg (Nat.ne_of_gt big),dif_neg (Nat.not_lt.mpr big.le),inner,dite_true,ite_true,dite_false]
      apply congrArg (fun z : Fin (m a+1) => (Sum.inr ⟨a,z⟩ : Vertex m))
      apply Fin.ext
      dsimp [perimeter,armSize] at *
      omega

/-- Transfer any map of the entire two-arm cycle, fixing off-cycle internal vertices. -/
noncomputable def cycleMap (m : Fin k → ℕ) (i j : Fin k) (T : Fin (perimeter m i j) → Fin (perimeter m i j))
    (v : Vertex m) : Vertex m :=
  if OnCycle i j v then cyclePt m i j (T (vertexCoord m i j v)) else v

theorem cycleMap_pt (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j)
    (T : Fin (perimeter m i j) → Fin (perimeter m i j)) (z : Fin (perimeter m i j)) :
    cycleMap m i j T (cyclePt m i j z) = cyclePt m i j (T z) := by
  simp only [cycleMap,if_pos (cyclePt_on ..),coord_pt m ij]

theorem cycleMap_off (m : Fin k → ℕ) (i j : Fin k)
    (T : Fin (perimeter m i j) → Fin (perimeter m i j)) {x : Vertex m} (off : ¬OnCycle i j x) :
    cycleMap m i j T x=x := if_neg off

def consecutive (m : Fin k → ℕ) (i j : Fin k) (x y : Fin (perimeter m i j)) : Prop :=
  x+1=y ∨ y+1=x

private def forwardNat (n x y : ℕ) := x+1=y ∨ x+1=n ∧ y=0

private theorem forward_iff (m : Fin k → ℕ) (i j : Fin k) (x y : Fin (perimeter m i j)) :
    x+1=y ↔ forwardNat (perimeter m i j) x.val y.val := by
  have one : (1 : Fin (perimeter m i j)).val = 1 := (Fin.val_one' _).trans (Nat.mod_eq_of_lt (by dsimp [perimeter,armSize]; omega))
  rw [Fin.ext_iff,Fin.val_add,one]
  unfold forwardNat
  have hx := x.isLt
  by_cases small : x.val+1<perimeter m i j
  · rw [Nat.mod_eq_of_lt small]; omega
  · have eq : x.val+1=perimeter m i j := by omega
    rw [eq,Nat.mod_self];omega

private theorem physical_forward (m : Fin k → ℕ) (i j : Fin k) (x y : Fin (perimeter m i j))
    (hxy : forwardNat (perimeter m i j) x.val y.val) : (graph m).Adj (cyclePt m i j x) (cyclePt m i j y) := by
  have hx := x.isLt
  have hy := y.isLt
  have positive : 2 ≤ armSize m i := by dsimp [armSize]; omega
  have ai : armSize m i = m i + 2 := rfl
  have n : perimeter m i j = m i+2+(m j+2) := rfl
  rcases hxy with succ'|⟨last',zero'⟩ <;>
    unfold cyclePt <;> split_ifs <;>
    first | (exfalso; omega) | (change _ ∧ (_ ∨ _); exact ⟨rfl,by dsimp only [Fin.val_mk]; omega⟩) | (change _ = _; dsimp only [Fin.val_mk]; omega)

theorem adj_of_consecutive (m : Fin k → ℕ) (i j : Fin k) (x y : Fin (perimeter m i j))
    (h : consecutive m i j x y) : (graph m).Adj (cyclePt m i j x) (cyclePt m i j y) := by
  rcases h with h|h
  · exact physical_forward m i j x y ((forward_iff ..).mp h)
  · exact (graph m).symm (physical_forward m i j y x ((forward_iff ..).mp h))

private theorem coord_touch (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j)
    (b : Bool) (a : Fin k) (d : Fin (m a+1)) (on' : a=i ∨ a=j)
    (edge : (graph m).Adj (pole m b) (inner m a d)) :
    consecutive m i j (vertexCoord m i j (pole m b)) (vertexCoord m i j (inner m a d)) := by
  unfold consecutive
  rw [forward_iff,forward_iff]
  have hd := d.isLt
  rcases on' with rfl|rfl <;> cases b
  all_goals first | (change d.val = 0 at edge) | (change d.val = m a at edge)
  all_goals simp only [pole,inner,vertexCoord,dif_pos rfl,dite_true,ite_true,dif_neg ij.symm,if_pos rfl,
    forwardNat,Fin.val_mk,Fin.val_zero,perimeter,armSize] <;> first | omega | (right; right; exact ⟨by rw [edge]; omega,trivial⟩)

theorem consecutive_of_adj (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) {x y : Vertex m}
    (xc : OnCycle i j x) (yc : OnCycle i j y) (e : (graph m).Adj x y) :
    consecutive m i j (vertexCoord m i j x) (vertexCoord m i j y) := by
  rcases x with b|⟨a,d⟩ <;> rcases y with c|⟨s,t⟩
  · exact e.elim
  · exact coord_touch m ij b s t yc e
  · exact (coord_touch m ij c a d xc ((graph m).symm e)).symm
  · obtain ⟨rfl,neigh⟩ := e
    have h := d.isLt
    have h' := t.isLt
    unfold consecutive
    rw [forward_iff,forward_iff]
    rcases xc with rfl|rfl <;>
      simp only [vertexCoord,dif_pos rfl,dite_true,ite_true,dif_neg ij.symm,if_pos rfl,
        forwardNat,Fin.val_mk,Fin.val_zero,perimeter,armSize] <;> omega

end Bootstrap.Theta

#print axioms Bootstrap.Theta.consecutive_of_adj
#print axioms Bootstrap.Theta.adj_of_consecutive
