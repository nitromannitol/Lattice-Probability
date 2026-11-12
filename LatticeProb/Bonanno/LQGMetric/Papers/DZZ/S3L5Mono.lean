/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5Mono at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7CountPsi
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1Geom

/-!
# DZZ (eq-280318b): `D'_{γ,δ'} ≥ D'_{γ,δ}` for `δ' ≤ δ` (P2-DZZ3F)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 919–923): "from the definition,
we have the following converse to (eq-280318): `D'_{γ,δ'}(u,v) ≥ D'_{γ,δ}(u,v)`".
DZZ give no further argument; own elementary proof (see DEVIATIONS): a box of mass `< δ²` lies
in a unique `δ`-cell, its first ancestor of mass `< δ²` (`cellAnc`); the `δ`-cells of two
neighbouring `δ'`-cells are equal or neighbours (the common segment lies in both), so a chain
of `δ'`-cells maps to a chain of `δ`-cells which is not longer.

* `exists_isCell_anc`, `cellAnc_spec`: the `δ`-cell containing a box of mass `< δ²`.
* `approxDist_mono`, `approxLGD_mono`, `approxLGDSet_mono`: (eq-280318b).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma anc_n_of_le {b : DyBox} {i : ℕ} (h : i ≤ b.n) : (b.anc i).n = i := min_eq_left h

/-- A box of mass `< δ²` has an ancestor which is a `δ`-cell (its first ancestor of mass `< δ²`). -/
lemma exists_isCell_anc {b : DyBox} (hb : m b < δ ^ 2) :
    ∃ i, i ≤ b.n ∧ IsCell m δ (b.anc i) := by
  classical
  have h0 : m (b.anc b.n) < δ ^ 2 := by rwa [anc_self le_rfl]
  have hP : ∃ i, m (b.anc i) < δ ^ 2 := ⟨b.n, h0⟩
  have hle : Nat.find hP ≤ b.n := Nat.find_min' hP h0
  refine ⟨Nat.find hP, hle, Nat.find_spec hP, fun i' hi' => ?_⟩
  rw [anc_n_of_le hle] at hi'
  rw [anc_anc b hi'.le]
  exact not_lt.1 (Nat.find_min hP hi')

open Classical in
/-- The `δ`-cell containing a box of mass `< δ²` (junk: the box itself otherwise). -/
def cellAnc (m : DyBox → ℝ) (δ : ℝ) (b : DyBox) : DyBox :=
  if h : ∃ i, i ≤ b.n ∧ IsCell m δ (b.anc i) then b.anc h.choose else b

lemma cellAnc_spec {b : DyBox} (hb : m b < δ ^ 2) :
    ∃ i, i ≤ b.n ∧ cellAnc m δ b = b.anc i ∧ IsCell m δ (cellAnc m δ b) := by
  have h := exists_isCell_anc (m := m) (δ := δ) hb
  unfold cellAnc
  rw [dif_pos h]
  exact ⟨h.choose, h.choose_spec.1, rfl, h.choose_spec.2⟩

lemma mem_anc {b : DyBox} {u : ℂ} (hu : b.Mem u) {i : ℕ} (hi : i ≤ b.n) : (b.anc i).Mem u := by
  refine ⟨hu.1, ?_⟩
  rw [anc_n_of_le hi, ← anc_boxAt hi, hu.2]

lemma closedBox_sub_cellAnc {b : DyBox} (hb : m b < δ ^ 2) :
    b.closedBox ⊆ (cellAnc m δ b).closedBox := by
  obtain ⟨i, -, he, -⟩ := cellAnc_spec (m := m) (δ := δ) hb
  rw [he]; exact closedBox_sub_anc b i

/-- Boxes containing two neighbouring boxes are equal or neighbours. -/
lemma eq_or_neighbour_of_sub {b₁ b₂ c₁ c₂ : DyBox} (h : Neighbour b₁ b₂)
    (h₁ : b₁.closedBox ⊆ c₁.closedBox) (h₂ : b₂.closedBox ⊆ c₂.closedBox) :
    c₁ = c₂ ∨ Neighbour c₁ c₂ := by
  by_cases he : c₁ = c₂
  · exact Or.inl he
  · exact Or.inr ⟨he, fun hs => h.2 (hs.anti (inter_subset_inter h₁ h₂))⟩

variable {Ω : Type*}

end DZZ
end LQGMetric
