/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Perc.Lattice at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

/-!
# Site percolation on `ℤ^d`: basic lattice facts

Elementary facts about the notions of `HigherDimLFPP.Perc.Defs` (HA5 Details D6–D7):

* symmetry, the triangle inequality and monotonicity of `WithinInf`; `LAdj` and `SAdj` are
  symmetric, `LAdj x y ↔ y = x ± e_i` (`LAdj.exists_eq_add_single`), `LAdj → SAdj`;
* paths: monotonicity of `StepIn`-paths in the set, symmetry, membership of the endpoints;
* coordinate paths: two sites with `|x - y|_∞ ≤ 1` are joined by an L-path whose sites have every
  coordinate equal to that of `x` or of `y` (`reflTransGen_cube`), and a site is joined to the
  site obtained by changing one coordinate along the segment of values in between
  (`reflTransGen_update`);
* the exterior `Ext R F`: closure under L-steps outside `F`, and `Ext R F ∩ F = ∅` when `F` lies in
  the box `[-R, R]^d` and `d ≥ 1`.
-/

set_option autoImplicit false

open Relation

namespace HigherDimLFPP

namespace Perc

variable {d : ℕ}

/-! ### `ℓ^∞` balls -/

lemma withinInf_comm {r : ℤ} {x y : Zd d} : WithinInf r x y ↔ WithinInf r y x := by
  simp only [WithinInf, abs_sub_comm]

lemma WithinInf.symm {r : ℤ} {x y : Zd d} (h : WithinInf r x y) : WithinInf r y x :=
  withinInf_comm.mp h

lemma WithinInf.trans {a b : ℤ} {x y z : Zd d} (hxy : WithinInf a x y) (hyz : WithinInf b y z) :
    WithinInf (a + b) x z := fun i =>
  (abs_sub_le (x i) (y i) (z i)).trans (add_le_add (hxy i) (hyz i))

lemma WithinInf.mono {a b : ℤ} {x y : Zd d} (h : WithinInf a x y) (hab : a ≤ b) :
    WithinInf b x y := fun i => (h i).trans hab

lemma withinInf_refl {r : ℤ} (hr : 0 ≤ r) (x : Zd d) : WithinInf r x x := fun i => by
  simpa using hr

lemma withinInf_iff {r : ℤ} {x y : Zd d} : WithinInf r x y ↔ ∀ i, -r ≤ x i - y i ∧ x i - y i ≤ r := by
  simp only [WithinInf, abs_le]

/-! ### Unit vectors -/

lemma add_single_apply (x : Zd d) (i k : Fin d) (t : ℤ) :
    (x + Pi.single i t : Zd d) k = if k = i then x k + t else x k := by
  by_cases h : k = i
  · subst h; simp
  · simp [h]

lemma add_single_apply_self (x : Zd d) (i : Fin d) (t : ℤ) :
    (x + Pi.single i t : Zd d) i = x i + t := by
  simp

lemma add_single_apply_of_ne (x : Zd d) {i k : Fin d} (h : k ≠ i) (t : ℤ) :
    (x + Pi.single i t : Zd d) k = x k := by
  simp [h]

/-! ### Adjacency -/

lemma lAdj_comm {x y : Zd d} : LAdj x y ↔ LAdj y x := by
  simp only [LAdj, abs_sub_comm]

lemma LAdj.symm {x y : Zd d} (h : LAdj x y) : LAdj y x := lAdj_comm.mp h

lemma sAdj_comm {x y : Zd d} : SAdj x y ↔ SAdj y x := by
  simp only [SAdj, abs_sub_comm, ne_comm]

lemma SAdj.symm {x y : Zd d} (h : SAdj x y) : SAdj y x := sAdj_comm.mp h

lemma SAdj.ne {x y : Zd d} (h : SAdj x y) : x ≠ y := h.1

lemma SAdj.withinInf {x y : Zd d} (h : SAdj x y) : WithinInf 1 x y := h.2

lemma sAdj_of_withinInf {x y : Zd d} (hne : x ≠ y) (h : WithinInf 1 x y) : SAdj x y := ⟨hne, h⟩

/-- `x` and `x + e_i` are nearest neighbours. -/
lemma lAdj_add_single (x : Zd d) (i : Fin d) : LAdj x (x + Pi.single i 1) := by
  classical
  unfold LAdj
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma lAdj_add_single' (x : Zd d) (i : Fin d) : LAdj (x + Pi.single i 1) x :=
  (lAdj_add_single x i).symm

/-- Nearest neighbours differ by a unit vector. -/
lemma LAdj.exists_eq_add_single {x y : Zd d} (h : LAdj x y) :
    ∃ i, y = x + Pi.single i 1 ∨ x = y + Pi.single i 1 := by
  classical
  unfold LAdj at h
  have hnn : ∀ k ∈ (Finset.univ : Finset (Fin d)), 0 ≤ |x k - y k| := fun k _ => abs_nonneg _
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (Finset.univ : Finset (Fin d)), |x i - y i| ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at h
    exact zero_ne_one h
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => |x k - y k|) (Finset.mem_univ i)
  rw [h] at hsplit
  have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase i, |x k - y k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hi0 : 0 ≤ |x i - y i| := abs_nonneg _
  have hi1 : |x i - y i| = 1 := by omega
  have hrest0 : ∑ k ∈ Finset.univ.erase i, |x k - y k| = 0 := by omega
  have hk : ∀ k, k ≠ i → x k = y k := by
    intro k hk
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hnn k (Finset.mem_of_mem_erase hk))).mp
      hrest0 k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    rwa [abs_eq_zero, sub_eq_zero] at this
  refine ⟨i, ?_⟩
  rcases (abs_eq zero_le_one).mp hi1 with h1 | h1
  · right
    funext k
    rw [add_single_apply]
    split_ifs with hki
    · subst hki; omega
    · exact hk k hki
  · left
    funext k
    rw [add_single_apply]
    split_ifs with hki
    · subst hki; omega
    · exact (hk k hki).symm

lemma LAdj.withinInf {x y : Zd d} (h : LAdj x y) : WithinInf 1 x y := by
  intro k
  have := Finset.single_le_sum (f := fun k => |x k - y k|) (fun k _ => abs_nonneg _)
    (Finset.mem_univ k)
  unfold LAdj at h
  rw [h] at this
  exact this

lemma LAdj.ne {x y : Zd d} (h : LAdj x y) : x ≠ y := by
  rintro rfl
  simp [LAdj] at h

lemma LAdj.sAdj {x y : Zd d} (h : LAdj x y) : SAdj x y := ⟨h.ne, h.withinInf⟩

/-! ### Paths in a set -/

lemma StepIn.symm {S : Set (Zd d)} {adj : Zd d → Zd d → Prop} (hadj : ∀ x y, adj x y → adj y x)
    {x y : Zd d} (h : StepIn S adj x y) : StepIn S adj y x :=
  ⟨h.2.1, h.1, hadj _ _ h.2.2⟩

lemma reflTransGen_stepIn_symm {S : Set (Zd d)} {adj : Zd d → Zd d → Prop}
    (hadj : ∀ x y, adj x y → adj y x) {x y : Zd d} (h : ReflTransGen (StepIn S adj) x y) :
    ReflTransGen (StepIn S adj) y x := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (hbc.symm hadj) ih

lemma reflTransGen_lAdj_symm {S : Set (Zd d)} {x y : Zd d}
    (h : ReflTransGen (StepIn S LAdj) x y) : ReflTransGen (StepIn S LAdj) y x :=
  reflTransGen_stepIn_symm (fun _ _ h => h.symm) h

lemma reflTransGen_sAdj_symm {S : Set (Zd d)} {x y : Zd d}
    (h : ReflTransGen (StepIn S SAdj) x y) : ReflTransGen (StepIn S SAdj) y x :=
  reflTransGen_stepIn_symm (fun _ _ h => h.symm) h

lemma StepIn.mono {S T : Set (Zd d)} {adj : Zd d → Zd d → Prop} (hST : S ⊆ T) {x y : Zd d}
    (h : StepIn S adj x y) : StepIn T adj x y :=
  ⟨hST h.1, hST h.2.1, h.2.2⟩

lemma reflTransGen_stepIn_mono {S T : Set (Zd d)} {adj : Zd d → Zd d → Prop} (hST : S ⊆ T)
    {x y : Zd d} (h : ReflTransGen (StepIn S adj) x y) : ReflTransGen (StepIn T adj) x y :=
  ReflTransGen.mono (fun a b (hab : StepIn S adj a b) => hab.mono hST) x y h

lemma mem_of_reflTransGen_stepIn {S : Set (Zd d)} {adj : Zd d → Zd d → Prop} {x y : Zd d}
    (h : ReflTransGen (StepIn S adj) x y) (hx : x ∈ S) : y ∈ S := by
  induction h with
  | refl => exact hx
  | tail _ hbc _ => exact hbc.2.1

lemma mem_of_reflTransGen_stepIn' {S : Set (Zd d)} {adj : Zd d → Zd d → Prop} {x y : Zd d}
    (h : ReflTransGen (StepIn S adj) x y) (hy : y ∈ S) : x ∈ S := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hy
  | head hac _ _ => exact hac.1

/-- A one-step path. -/
lemma reflTransGen_single_stepIn {S : Set (Zd d)} {adj : Zd d → Zd d → Prop} {x y : Zd d}
    (hx : x ∈ S) (hy : y ∈ S) (h : adj x y) : ReflTransGen (StepIn S adj) x y :=
  ReflTransGen.single ⟨hx, hy, h⟩

/-! ### Coordinate paths -/

/-- The sites whose coordinates are, one by one, those of `x` or those of `y`. -/
def cube (x y : Zd d) : Set (Zd d) := {z | ∀ k, z k = x k ∨ z k = y k}

lemma left_mem_cube (x y : Zd d) : x ∈ cube x y := fun _ => Or.inl rfl

lemma right_mem_cube (x y : Zd d) : y ∈ cube x y := fun _ => Or.inr rfl

lemma withinInf_of_mem_cube {x y z : Zd d} (hxy : WithinInf 1 x y) (hz : z ∈ cube x y) :
    WithinInf 1 z x ∧ WithinInf 1 z y := by
  constructor
  · intro k
    rcases hz k with h | h
    · simp [h]
    · rw [h, abs_sub_comm]; exact hxy k
  · intro k
    rcases hz k with h | h
    · rw [h]; exact hxy k
    · simp [h]

/-- The `n`-th site of the coordinate path from `x` to `y`: coordinates of index `< n` from `y`, the
others from `x`. -/
def coordPath (x y : Zd d) (n : ℕ) : Zd d := fun k => if k.val < n then y k else x k

lemma coordPath_mem_cube (x y : Zd d) (n : ℕ) : coordPath x y n ∈ cube x y := by
  intro k
  unfold coordPath
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma coordPath_zero (x y : Zd d) : coordPath x y 0 = x := by
  funext k
  simp [coordPath]

lemma coordPath_of_le (x y : Zd d) {n : ℕ} (hn : d ≤ n) : coordPath x y n = y := by
  funext k
  have hk : k.val < n := lt_of_lt_of_le k.isLt hn
  simp only [coordPath, hk, ↓reduceIte]

/-- Two sites at `ℓ^∞`-distance `≤ 1` are joined by an L-path inside `cube x y`. -/
lemma reflTransGen_cube {x y : Zd d} (hxy : WithinInf 1 x y) :
    ReflTransGen (StepIn (cube x y) LAdj) x y := by
  classical
  have key : ∀ n : ℕ, ReflTransGen (StepIn (cube x y) LAdj) x (coordPath x y n) := by
    intro n
    induction n with
    | zero => rw [coordPath_zero]
    | succ n ih =>
      by_cases hn : n < d
      · set j : Fin d := ⟨n, hn⟩ with hj
        have hk : ∀ k : Fin d, k ≠ j → coordPath x y (n + 1) k = coordPath x y n k := by
          intro k hk
          have : k.val ≠ n := fun h => hk (Fin.ext h)
          simp only [coordPath]
          by_cases hlt : k.val < n
          · have h2 : k.val < n + 1 := by omega
            simp only [hlt, h2, ↓reduceIte]
          · have h2 : ¬ k.val < n + 1 := by omega
            simp only [hlt, h2, ↓reduceIte]
        have hjn : coordPath x y n j = x j := by simp [coordPath, hj]
        have hjn1 : coordPath x y (n + 1) j = y j := by simp [coordPath, hj]
        have hxyj := hxy j
        rw [abs_le] at hxyj
        by_cases heq : x j = y j
        · have : coordPath x y (n + 1) = coordPath x y n := by
            funext k
            by_cases hkj : k = j
            · subst hkj; rw [hjn, hjn1, heq]
            · exact hk k hkj
          rw [this]; exact ih
        · refine ih.tail ⟨coordPath_mem_cube x y n, coordPath_mem_cube x y (n + 1), ?_⟩
          rcases (show y j = x j + 1 ∨ x j = y j + 1 by omega) with h1 | h1
          · have : coordPath x y (n + 1) = coordPath x y n + Pi.single j 1 := by
              funext k
              rw [add_single_apply]
              split_ifs with hkj
              · subst hkj; rw [hjn, hjn1, h1]
              · exact hk k hkj
            rw [this]; exact lAdj_add_single _ _
          · have : coordPath x y n = coordPath x y (n + 1) + Pi.single j 1 := by
              funext k
              rw [add_single_apply]
              split_ifs with hkj
              · subst hkj; rw [hjn, hjn1, h1]
              · exact (hk k hkj).symm
            rw [this]; exact lAdj_add_single' _ _
      · have h1 : coordPath x y (n + 1) = coordPath x y n := by
          rw [coordPath_of_le x y (by omega), coordPath_of_le x y (by omega)]
        rw [h1]; exact ih
  have := key d
  rwa [coordPath_of_le x y le_rfl] at this

/-- Moving one coordinate: `x` is joined to `x + t e_i` (`t ≥ 0`) by an L-path through the sites
`x + s e_i`, `0 ≤ s ≤ t`. -/
lemma reflTransGen_add_single_nat {S : Set (Zd d)} (x : Zd d) (i : Fin d) (n : ℕ)
    (hS : ∀ s : ℕ, s ≤ n → x + Pi.single i (s : ℤ) ∈ S) :
    ReflTransGen (StepIn S LAdj) x (x + Pi.single i (n : ℤ)) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, Pi.single_zero, add_zero]
    exact ReflTransGen.refl
  | succ n ih =>
    refine (ih fun s hs => hS s (by omega)).tail ⟨hS n (by omega), hS (n + 1) le_rfl, ?_⟩
    have : x + Pi.single i ((n + 1 : ℕ) : ℤ) = (x + Pi.single i (n : ℤ)) + Pi.single i 1 := by
      rw [add_assoc, ← Pi.single_add]
      push_cast
      rfl
    rw [this]
    exact lAdj_add_single _ _

/-- Moving one coordinate down: `x` is joined to `x - t e_i` (`t ≥ 0`) through `x - s e_i`. -/
lemma reflTransGen_sub_single_nat {S : Set (Zd d)} (x : Zd d) (i : Fin d) (n : ℕ)
    (hS : ∀ s : ℕ, s ≤ n → x + Pi.single i (-(s : ℤ)) ∈ S) :
    ReflTransGen (StepIn S LAdj) x (x + Pi.single i (-(n : ℤ))) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, Pi.single_zero, add_zero]
    exact ReflTransGen.refl
  | succ n ih =>
    refine (ih fun s hs => hS s (by omega)).tail ⟨hS n (by omega), hS (n + 1) le_rfl, ?_⟩
    have : x + Pi.single i (-(n : ℤ)) = (x + Pi.single i (-((n + 1 : ℕ) : ℤ))) + Pi.single i 1 := by
      rw [add_assoc, ← Pi.single_add]
      push_cast
      congr 2
      ring
    rw [this]
    exact lAdj_add_single' _ _

/-- Moving one coordinate to an arbitrary value `t`, through the sites whose `i`-th coordinate lies
between `x i` and `t` and whose other coordinates are those of `x`. -/
lemma reflTransGen_update {S : Set (Zd d)} (x : Zd d) (i : Fin d) (t : ℤ)
    (hS : ∀ s : ℤ, min (x i) t ≤ s → s ≤ max (x i) t → Function.update x i s ∈ S) :
    ReflTransGen (StepIn S LAdj) x (Function.update x i t) := by
  have hupd : ∀ s : ℤ, Function.update x i (x i + s) = x + Pi.single i s := by
    intro s
    funext k
    rw [add_single_apply]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rcases le_total (x i) t with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = x i + n := ⟨(t - x i).toNat, by omega⟩
    rw [hn, hupd]
    refine reflTransGen_add_single_nat x i n fun s hs => ?_
    rw [← hupd]
    exact hS _ (by omega) (by omega)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = x i + -(n : ℤ) := ⟨(x i - t).toNat, by omega⟩
    rw [hn, hupd]
    refine reflTransGen_sub_single_nat x i n fun s hs => ?_
    rw [← hupd]
    exact hS _ (by omega) (by omega)

/-! ### The exterior of a set -/

/-- The base point `(R+1, …, R+1)` of `Ext R F`. -/
lemma base_notMem {R : ℤ} {F : Set (Zd d)} (hF : ∀ x ∈ F, WithinInf R x 0) (i : Fin d) :
    (fun _ => R + 1 : Zd d) ∉ F := by
  intro h
  have := hF _ h i
  simp only [Pi.zero_apply, sub_zero, abs_le] at this
  omega

/-- A site of `Ext R F` outside `F` (automatic when `F` lies in the box and `d ≥ 1`). -/
lemma notMem_of_mem_ext {R : ℤ} {F : Set (Zd d)} (hF : ∀ x ∈ F, WithinInf R x 0) (i : Fin d)
    {y : Zd d} (hy : y ∈ Ext R F) : y ∉ F := by
  intro hyF
  unfold Ext at hy
  rcases ReflTransGen.cases_head hy with h | ⟨c, hc, -⟩
  · exact base_notMem hF i (h ▸ hyF)
  · exact hc.1 hyF

/-- `Ext R F` is closed under L-steps outside `F`. -/
lemma mem_ext_of_lAdj {R : ℤ} {F : Set (Zd d)} {y z : Zd d} (hy : y ∉ F) (hz : z ∉ F)
    (hyz : LAdj y z) (hzE : z ∈ Ext R F) : y ∈ Ext R F :=
  ReflTransGen.head ⟨hy, hz, hyz⟩ hzE

/-- Every site of an L-path avoiding `F` that ends in `Ext R F` lies in `Ext R F`. -/
lemma mem_ext_of_reflTransGen {R : ℤ} {F : Set (Zd d)} {y z : Zd d}
    (h : ReflTransGen (StepIn Fᶜ LAdj) y z) (hz : z ∈ Ext R F) : y ∈ Ext R F :=
  h.trans hz

end Perc

end HigherDimLFPP
