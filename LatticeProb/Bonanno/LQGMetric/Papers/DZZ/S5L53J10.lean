/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J9

/-!
# DZZ Lemma 5.3, node 3: boundary segments of the sub-box grid of a cell

The segment of `∂𝖢_i` carried by a boundary sub-box `𝖡` is `𝖡̄ ∩ ∂𝖢̄` (DZZ l. 1901–1903: "`∂𝖢_i`
is partitioned into `4K` segments … `𝖡^L` the unique box containing `L`"). Here:
* `l53_sub_subset`: every sub-box lies in `𝖢̄`;
* `l53_seg_subset_frontier`: `𝖡̄ ∩ ∂𝖢̄ ⊆ ∂𝖡̄` for any `𝖡̄ ⊆ 𝖢̄` (an interior point of `𝖡̄` is
  interior to `𝖢̄`), the input `hseg` of `l53_cell_desirable_prob`;
* `l53_sub_seg_le`: `μH¹(𝖡̄ ∩ ∂𝖢̄) ≤ 4 s_𝖢/K` (input `hσ` with `σ = 4 s_𝖢/K`);
* `l53_hopen_uniform`: the openness of `l53_zopen_dyBox` with uniform thresholds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric DyBox

lemma l53_side_mul_pow (C : DyBox) (k : ℕ) : (2 : ℝ)⁻¹ ^ (C.n + k) * 2 ^ k = C.side := by
  rw [DyBox.side, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]

/-- **The sub-boxes of `𝖢` lie in `𝖢̄`.** -/
lemma l53_sub_subset (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {z : ℤ × ℤ}
    (hz : z ∈ l53EvenBox N) : (l53Sub C k N z).closedBox ⊆ C.closedBox := by
  obtain ⟨hj, hk⟩ := l53_sub_jk C hK hz
  rw [mem_l53EvenBox] at hz
  obtain ⟨z1, z2, z3, z4⟩ := hz
  have hjR : ((l53Sub C k N z).j : ℝ) = 2 ^ k * C.j + N + z.1 := by exact_mod_cast hj
  have hkR : ((l53Sub C k N z).k : ℝ) = 2 ^ k * C.k + N + z.2 := by exact_mod_cast hk
  have hKR : (2 : ℝ) ^ k = 2 * N + 2 := by exact_mod_cast hK
  have z1R : -(N : ℝ) ≤ z.1 := by exact_mod_cast z1
  have z2R : (z.1 : ℝ) ≤ N + 1 := by exact_mod_cast z2
  have z3R : -(N : ℝ) ≤ z.2 := by exact_mod_cast z3
  have z4R : (z.2 : ℝ) ≤ N + 1 := by exact_mod_cast z4
  have ht := l53_side_mul_pow C k
  have t0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (C.n + k) := by positivity
  rintro w ⟨a1, a2, a3, a4⟩
  rw [l53_sub_side, hjR] at a1 a2
  rw [l53_sub_side, hkR] at a3 a4
  show C.j * C.side ≤ w.re ∧ w.re ≤ (C.j + 1) * C.side ∧
    C.k * C.side ≤ w.im ∧ w.im ≤ (C.k + 1) * C.side
  rw [← ht]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **`𝖡̄ ∩ ∂𝖢̄ ⊆ ∂𝖡̄`** for `𝖡̄ ⊆ 𝖢̄`. -/
lemma l53_seg_subset_frontier {B C : Set ℂ} (hBC : B ⊆ C) :
    B ∩ frontier C ⊆ frontier B := by
  rintro z ⟨hzB, hzC⟩
  refine ⟨subset_closure hzB, fun hint => ?_⟩
  exact hzC.2 (interior_mono hBC hint)

/-- **`μH¹(𝖡̄ ∩ ∂𝖢̄) ≤ 4 s_𝖢/K`** for a sub-box `𝖡` of `𝖢`. -/
lemma l53_sub_seg_le (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {z : ℤ × ℤ}
    (hz : z ∈ l53EvenBox N) :
    (μH[1] : Measure ℂ).real ((l53Sub C k N z).closedBox ∩ frontier C.closedBox) ≤
      4 * (2 : ℝ)⁻¹ ^ (C.n + k) := by
  have hsub := l53_seg_subset_frontier (l53_sub_subset C hK hz)
  have hle := (measure_mono hsub).trans (l53_sub_frontier_le C k N z)
  have hfin : 4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + k)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  simpa [Measure.real] using this

/-- **Uniform openness thresholds.** `l53_zopen_dyBox` (part 4) gives openness of a box with
the thresholds `a = b = κ μH¹(Bd)`; when `μH¹(Bd) ≤ u` (`u = 4 s_𝖢/K`, `l53_sub_frontier_le`) the
same box is open with the uniform thresholds `a = b = κ u` of `l53_cell_desirable_prob`. -/
lemma l53_hopen_uniform {α : Type*} [MeasurableSpace α] {ν : Measure α} {Bd : Set α}
    {R : α → α → Prop} {κ u : ℝ≥0∞} (hBd : ν Bd ≤ u)
    (h : ∀ Λ ⊆ Bd, κ * ν Bd ≤ ν Λ → ∃ z ∈ Λ, ν {z' ∈ Bd | ¬ R z z'} ≤ κ * ν Bd) :
    ∀ Λ ⊆ Bd, κ * u ≤ ν Λ → ∃ z ∈ Λ, ν {z' ∈ Bd | ¬ R z z'} ≤ κ * u := by
  intro Λ hΛ hb
  obtain ⟨z, hz, hza⟩ := h Λ hΛ ((by gcongr : κ * ν Bd ≤ κ * u).trans hb)
  exact ⟨z, hz, hza.trans (by gcongr)⟩

end LQGMetric.DZZ
