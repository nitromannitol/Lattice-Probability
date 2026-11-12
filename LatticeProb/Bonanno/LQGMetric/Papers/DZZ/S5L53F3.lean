/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53F3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XAdj
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Lower

/-!
# DZZ Lemma 5.3, part 1, node 1: the interfaces `Λ_i` and the adapter to `hdes` (P2-DZZ53F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2393 ("`Λ_i = ∂𝖢_i ∩ ∂𝖢_{i+1}`")
and l. 2504–2530 (the desirable event).

* `l53Iface c i = 𝖢̄_i ∩ 𝖢̄_{i+1}` (`𝖢_j = c[j−1]`): for two distinct cells of `𝒱_δ` it lies on one
  side of `𝖢_i` (`l53_iface_ne_top`: `μH¹ < ∞`); for neighbours it contains a non-trivial segment
  (`l53_iface_pos`: `μH¹ > 0`). Own elementary proofs (the case split is that of `exists_door`,
  S3L13G4).
* `L53ChainDesirable`: the clauses of `l53DesirableEvent` (S5L53E2) for the interfaces of `c`
  (the interface to nodes 2–4).
* **`l53_mem_desirable`**: a cell chain of `𝒟₁` with length `≥ 2` satisfying
  `L53ChainDesirable` gives `ω ∈ l53DesirableEvent`; the length is `≥ 2` once
  `2δ^{C_Mc} < |u − v|` (cell size).
* **`l53_hdes_of_D1`**: the corrected `hdes` (S5L53F1, `dzzLem53Exp_dzzMuIn_of_desirable97`) for
  one pair from the bound on `𝒟₁ᶜ` and the bound on the bad event `l53Bad` of nodes 2–4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-! ### Segments -/

lemma l53_isometry_vline (a : ℝ) : Isometry fun t : ℝ => (⟨a, t⟩ : ℂ) :=
  Isometry.of_dist_eq fun x y => by
    rw [Complex.dist_eq, Real.dist_eq]
    have : (⟨a, x⟩ : ℂ) - ⟨a, y⟩ = ⟨0, x - y⟩ := Complex.ext (by simp) (by simp)
    rw [this, Complex.norm_eq_sqrt_sq_add_sq]
    simp [Real.sqrt_sq_eq_abs]

lemma l53_isometry_hline (b : ℝ) : Isometry fun t : ℝ => (⟨t, b⟩ : ℂ) :=
  Isometry.of_dist_eq fun x y => by
    rw [Complex.dist_eq, Real.dist_eq]
    have : (⟨x, b⟩ : ℂ) - ⟨y, b⟩ = ⟨x - y, 0⟩ := Complex.ext (by simp) (by simp)
    rw [this, Complex.norm_eq_sqrt_sq_add_sq]
    simp [Real.sqrt_sq_eq_abs]

lemma l53_vline_ne_top (a b c : ℝ) :
    μH[1] {z : ℂ | z.re = a ∧ b ≤ z.im ∧ z.im ≤ c} ≠ ⊤ := by
  have : {z : ℂ | z.re = a ∧ b ≤ z.im ∧ z.im ≤ c} = (fun t : ℝ => (⟨a, t⟩ : ℂ)) '' Icc b c := by
    ext z
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨z.im, ⟨h2, h3⟩, Complex.ext (by simp [h1]) (by simp)⟩, ?_⟩
    rintro ⟨t, ⟨h2, h3⟩, rfl⟩
    exact ⟨rfl, h2, h3⟩
  rw [this, (l53_isometry_vline a).hausdorffMeasure_image (Or.inl zero_le_one),
    MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

lemma l53_hline_ne_top (a b c : ℝ) :
    μH[1] {z : ℂ | z.im = a ∧ b ≤ z.re ∧ z.re ≤ c} ≠ ⊤ := by
  have : {z : ℂ | z.im = a ∧ b ≤ z.re ∧ z.re ≤ c} = (fun t : ℝ => (⟨t, a⟩ : ℂ)) '' Icc b c := by
    ext z
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨z.re, ⟨h2, h3⟩, Complex.ext (by simp) (by simp [h1])⟩, ?_⟩
    rintro ⟨t, ⟨h2, h3⟩, rfl⟩
    exact ⟨rfl, h2, h3⟩
  rw [this, (l53_isometry_hline a).hausdorffMeasure_image (Or.inl zero_le_one),
    MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

lemma l53_closedBox_convex (b : DyBox) : Convex ℝ b.closedBox := by
  have : b.closedBox = Complex.reLm ⁻¹' Icc (b.j * b.side) ((b.j + 1) * b.side) ∩
      Complex.imLm ⁻¹' Icc (b.k * b.side) ((b.k + 1) * b.side) := by
    ext z; simp [DyBox.closedBox, and_assoc]
  rw [this]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

/-! ### The interfaces -/

variable {m : DyBox → ℝ} {δ : ℝ}

/-- **`μH¹(𝖢̄ ∩ 𝖢̄') > 0`** for neighbours (it contains a non-trivial segment). -/
lemma l53_iface_pos {C C' : DyBox} (hN : Neighbour C C')
    (hfin : μH[1] (C.closedBox ∩ C'.closedBox) ≠ ⊤) :
    0 < (μH[1] : Measure ℂ).real (C.closedBox ∩ C'.closedBox) := by
  obtain ⟨-, hns⟩ := hN
  simp only [Set.Subsingleton, not_forall] at hns
  obtain ⟨z, hz, z', hz', hzz⟩ := hns
  have hseg : segment ℝ z z' ⊆ C.closedBox ∩ C'.closedBox :=
    ((l53_closedBox_convex C).inter (l53_closedBox_convex C')).segment_subset hz hz'
  have h1 : 0 < μH[1] (segment ℝ z z') := by
    rw [hausdorffMeasure_segment]; exact edist_pos.2 hzz
  exact ENNReal.toReal_pos (ne_of_gt (h1.trans_le (measure_mono hseg))) hfin

/-- `Λ_i = 𝖢̄_i ∩ 𝖢̄_{i+1}` with `𝖢_j = c[j−1]` (DZZ l. 2393). -/
def l53Iface (c : List DyBox) (i : ℕ) : Set ℂ :=
  (c.getD (i - 1) DyBox.root).closedBox ∩ (c.getD i DyBox.root).closedBox

end DZZ
end LQGMetric
