import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

/-! Finite rooted tree decompositions, written in parent-before-child order.
Start with a root bag and attach each new bag to a previous parent. A vertex which already
occurs may enter the new bag only through its parent; this is the running-intersection
property when a finite tree is built by attaching leaves. Parent bags may have any number
of children. Repeated equal bag labels are harmless. -/
namespace Bootstrap.TreeBags

variable {V : Type*} [DecidableEq V]

def Occurs (F : Finset (Finset V)) (v : V) : Prop := ∃ b ∈ F, v ∈ b
def Together (F : Finset (Finset V)) (x y : V) : Prop := ∃ b ∈ F, x ∈ b ∧ y ∈ b

inductive Tree (k : ℕ) : Finset (Finset V) → Prop where
  | root (b : Finset V) (width : b.card ≤ k+1) : Tree k {b}
  | attach {F : Finset (Finset V)} (old : Tree k F) {p : Finset V} (parent : p ∈ F)
      (b : Finset V) (width : b.card ≤ k+1)
      (connected : ∀ v ∈ b, Occurs F v → v ∈ p) : Tree k (insert b F)

def WidthLE (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ F, Tree k F ∧ (∀ v, Occurs F v) ∧ ∀ x y, G.Adj x y → Together F x y

theorem bag_size {k : ℕ} {F : Finset (Finset V)} (T : Tree k F) {b : Finset V}
    (hb : b ∈ F) : b.card ≤ k+1 := by
  induction T with
  | root b₀ h =>
    have e := Finset.mem_singleton.mp hb
    exact e ▸ h
  | attach old hp l hl connect ih =>
    rcases Finset.mem_insert.mp hb with e | h
    · exact e ▸ hl
    · exact ih h

private theorem old_together {F : Finset (Finset V)} {p l : Finset V}
    (hp : p ∈ F) (glue : ∀ v ∈ l, Occurs F v → v ∈ p)
    {x y : V} (hx : Occurs F x) (hy : Occurs F y)
    (h : Together (insert l F) x y) : Together F x y := by
  obtain ⟨b,hb,bx,by'⟩ := h
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ⟨p,hp,glue x bx hx,glue y by' hy⟩
  · exact ⟨b,hb,bx,by'⟩

private theorem new_pair {F : Finset (Finset V)} {l : Finset V} {x y : V}
    (h : Together (insert l F) x y) (hx : ¬ Occurs F x) : x ∈ l ∧ y ∈ l := by
  obtain ⟨b,hb,bx,by'⟩ := h
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ⟨bx,by'⟩
  · exact (hx ⟨b,hb,bx⟩).elim

omit [DecidableEq V] in
theorem together_symm {F : Finset (Finset V)} {x y : V} (h : Together F x y) :
    Together F y x := by
  obtain ⟨b,hb,bx,by'⟩ := h
  exact ⟨b,hb,by',bx⟩

theorem triangle_bag {k : ℕ} {F : Finset (Finset V)} (T : Tree k F) (x y z : V)
    (hxy : Together F x y) (hxz : Together F x z) (hyz : Together F y z) :
    ∃ b ∈ F, x ∈ b ∧ y ∈ b ∧ z ∈ b := by
  induction T with
  | root b _ =>
    simp only [Together, Finset.mem_singleton, exists_eq_left] at hxy hxz
    exact ⟨b,Finset.mem_singleton_self _,hxy.1,hxy.2,hxz.2⟩
  | @attach F old p hp l hl glue ih =>
    by_cases xo : Occurs F x
    · by_cases yo : Occurs F y
      · by_cases zo : Occurs F z
        · obtain ⟨b,hb,bx,by',bz⟩ := ih (old_together hp glue xo yo hxy)
            (old_together hp glue xo zo hxz) (old_together hp glue yo zo hyz)
          exact ⟨b,Finset.mem_insert_of_mem hb,bx,by',bz⟩
        · have ⟨bz,bx⟩ := new_pair (together_symm hxz) zo
          exact ⟨l,Finset.mem_insert_self _ _,bx,(new_pair (together_symm hyz) zo).2,bz⟩
      · have ⟨by',bx⟩ := new_pair (together_symm hxy) yo
        exact ⟨l,Finset.mem_insert_self _ _,bx,by',(new_pair hyz yo).2⟩
    · have ⟨bx,by'⟩ := new_pair hxy xo
      exact ⟨l,Finset.mem_insert_self _ _,bx,by',(new_pair hxz xo).2⟩

theorem triangle_forbids_width_one (G : SimpleGraph V) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : ¬ WidthLE G 1 := by
  rintro ⟨F,T,_,edges⟩
  obtain ⟨b,hb,bx,by',bz⟩ := triangle_bag T x y z (edges _ _ hxy) (edges _ _ hxz) (edges _ _ hyz)
  have hs : ({x,y,z} : Finset V) ⊆ b := by simpa [Finset.insert_subset_iff] using ⟨bx,by',bz⟩
  have hn := Finset.card_le_card hs
  have hc : ({x,y,z} : Finset V).card = 3 := by simp [hxy.ne,hxz.ne,hyz.ne]
  have bound := bag_size T hb
  omega

/-- Attach a whole family of leaves to old parents. Different leaves can only share old vertices. -/
theorem attach_family {I : Type*} [DecidableEq I] {k : ℕ} {F : Finset (Finset V)}
    (T : Tree k F) (nodes : Finset I) (leaf parent : I → Finset V)
    (hp : ∀ i, parent i ∈ F) (hw : ∀ i, (leaf i).card ≤ k+1)
    (hold : ∀ i v, v ∈ leaf i → Occurs F v → v ∈ parent i)
    (overlap : ∀ i j, i ≠ j → ∀ v, v ∈ leaf i → v ∈ leaf j → Occurs F v) :
    Tree k (F ∪ nodes.image leaf) := by
  classical
  induction nodes using Finset.induction_on with
  | empty => simpa using T
  | @insert i s hi ih =>
    rw [Finset.image_insert, Finset.union_insert]
    apply Tree.attach ih (p := parent i) (Finset.mem_union_left _ (hp i)) _ (hw i)
    intro v hv prev
    apply hold i v hv
    obtain ⟨b,hb,vb⟩ := prev
    rcases Finset.mem_union.mp hb with hb | hb
    · exact ⟨b,hb,vb⟩
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
      exact overlap i j (by rintro rfl; exact hi hj) v hv vb

end Bootstrap.TreeBags

#print axioms Bootstrap.TreeBags.triangle_forbids_width_one
#print axioms Bootstrap.TreeBags.attach_family
