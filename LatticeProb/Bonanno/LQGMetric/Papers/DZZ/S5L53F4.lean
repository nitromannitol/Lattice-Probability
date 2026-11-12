/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53F4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F3

/-!
# DZZ Lemma 5.3, part 1, node 1: the adapter from `𝒟₁` to `hdes` (P2-DZZ53F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2504–2530.

* `L53ChainDesirable ν u v δ T T' c`: the `u`-, `v`- and `𝖢_i`-clauses of `l53DesirableEvent`
  (S5L53E2) for the interfaces `Λ_i = l53Iface c i` of the cell chain `c`. This is exactly what
  nodes 2–4 must produce.
* `l53_two_le_length`: on `cellSizeEvent`, a cell chain joining `u ≠ v` has `d ≥ 2` once
  `2δ^{C_Mc} < |u − v|`.
* **`l53_mem_desirable`**: a cell chain of `𝒟₁` with `L53ChainDesirable` lies in
  `l53DesirableEvent`.
* `l53Bad`: `𝒟₁` holds but no chain of `𝒟₁` is desirable (the event nodes 2–4 must bound).
* **`l53_hdes_of_D1`**: `P(𝒟₁ᶜ) ≤ e^{−L^{0.22}}` and `P(l53Bad) ≤ e^{−L^{0.22}}` give the
  pair-wise `hdes` of `dzzLem53Exp_dzzMuIn_of_desirable97` (S5L53F1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- **The desirability clauses** of `l53DesirableEvent` for the interfaces of `c` (DZZ
l. 2504–2522). -/
def L53ChainDesirable (ν : Measure ℂ) (u v : ℂ) (δ T T' : ℝ) (c : List DyBox) : Prop :=
  (∃ A ⊆ l53Iface c 1, MeasurableSet A ∧
      0.99 * (μH[1] : Measure ℂ).real (l53Iface c 1) ≤ (μH[1] : Measure ℂ).real A ∧
      ∀ x ∈ A, lgdLeExp ν δ T u x) ∧
    (∃ A ⊆ l53Iface c (c.length - 1),
      0.99 * (μH[1] : Measure ℂ).real (l53Iface c (c.length - 1)) ≤ (μH[1] : Measure ℂ).real A ∧
      ∀ x ∈ A, lgdLeExp ν δ T v x) ∧
    (∀ i, 2 ≤ i → i ≤ c.length - 1 → ∀ E ⊆ l53Iface c i,
      0.1 * (μH[1] : Measure ℂ).real (l53Iface c i) ≤ (μH[1] : Measure ℂ).real E →
      ∃ S ⊆ l53Iface c (i - 1),
        0.1 * (μH[1] : Measure ℂ).real (l53Iface c (i - 1)) ≤ (μH[1] : Measure ℂ).real S ∧
        ∀ x ∈ S, ∃ x' ∈ E, lgdLeExp ν δ T' x x')

variable {Ω : Type*} [MeasurableSpace Ω]

lemma l53_ev_sep (c : ℝ) (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, 2 * ((2 : ℝ)⁻¹ ^ k) ^ c < r := by
  set q : ℝ := (2 : ℝ)⁻¹ ^ c with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hc
  have he : ∀ k : ℕ, ((2 : ℝ)⁻¹ ^ k) ^ c = q ^ k := by
    intro k
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < r / 2))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ht
  refine ⟨k₀, fun k hk => ?_⟩
  have : q ^ k < r / 2 := hk₀ k hk
  rw [he]; linarith

end DZZ
end LQGMetric
