/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P317A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32

/-!
# DZZ Proposition 3.17: the reduction to the concentration of `D'` (P2-DZZ32G)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), Proposition 3.17 (`prop-concentration`, l. 1505–1517),
proof l. 1519–1652. DZZ l. 1526: "It is obvious from Proposition 3.2 and Corollary 3.3 that
(eq-concentration-1) is equivalent to the statement that with `c ι²`-high probability
(eq-concentration-approximate)"; l. 1627 the same for (eq-concentration-2) and
(eq-concentration-approximate-2). This file states the two inputs and the asymptotic helpers:

* **`DZZConcApprox`**: (eq-concentration-approximate) (l. 1528–1530) and
  (eq-concentration-approximate-2) (l. 1628–1630, probability `1 - e^{-Ω((log δ⁻¹)^{0.8})}`,
  l. 1647) for `D'_{γ,δ}` (`logApproxLGD`), for every `ξ`-admissible sequence (open: the Gaussian
  concentration argument of l. 1538–1651);
* **`DZZCrudeMoments`**: (eq-very-crude), (eq-very-crude-prime) (l. 849–857) for admissible pairs
  (open);
* `exists_delta_of_eventually`, `ev_rpow_le` (own elementary asymptotics).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(eq-concentration-approximate), (eq-concentration-approximate-2)** for `D'` (DZZ
l. 1528–1530, 1628–1630, 1647), uniformly over `ξ`-admissible sequences (open). -/
def DZZConcApprox (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    (∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2) fun δ =>
      {ω | |logApproxLGD γ W δ (A δ) (B δ) ω - ∫ ω', logApproxLGD γ W δ (A δ) (B δ) ω' ∂P| ≤
        ι * Real.log δ⁻¹}) ∧
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | |logApproxLGD γ W δ (A δ) (B δ) ω - ∫ ω', logApproxLGD γ W δ (A δ) (B δ) ω' ∂P| ≤
        Real.log δ⁻¹ ^ (0.94 : ℝ)}ᶜ ≤
        ENNReal.ofReal (Real.exp (-(c₂ * Real.log δ⁻¹ ^ (0.8 : ℝ))))

/-- a property of `L = log δ⁻¹` for large `L` holds for small `δ` -/
lemma exists_delta_of_eventually {p : ℝ → Prop} (h : ∀ᶠ L in atTop, p L) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, p (Real.log δ⁻¹) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 h
  refine ⟨Real.exp (-(max T 1)), Real.exp_pos _, fun δ hδ => hT _ ?_⟩
  have := Real.log_lt_log hδ.1 hδ.2
  rw [Real.log_exp] at this
  rw [Real.log_inv]
  linarith [le_max_left T 1]

/-- `b L^p ≤ a L^q` for large `L` when `p < q`, `a > 0` (own elementary proof). -/
lemma ev_rpow_le {p q a : ℝ} (hpq : p < q) (ha : 0 < a) (b : ℝ) :
    ∀ᶠ L : ℝ in atTop, b * L ^ p ≤ a * L ^ q := by
  have ht := tendsto_rpow_neg_atTop (sub_pos.2 hpq)
  have h1 : ∀ᶠ L : ℝ in atTop, L ^ (-(q - p)) < a / (|b| + 1) :=
    ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [h1, eventually_gt_atTop 0] with L hL hL0
  have e : L ^ p = L ^ q * L ^ (-(q - p)) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hq : 0 < L ^ q := Real.rpow_pos_of_pos hL0 q
  have hb1 : 0 < |b| + 1 := by positivity
  calc b * L ^ p ≤ |b| * L ^ p := mul_le_mul_of_nonneg_right (le_abs_self b)
        (Real.rpow_nonneg hL0.le p)
    _ = |b| * L ^ q * L ^ (-(q - p)) := by rw [e]; ring
    _ ≤ |b| * L ^ q * (a / (|b| + 1)) :=
        mul_le_mul_of_nonneg_left hL.le (by positivity)
    _ ≤ a * L ^ q := by
        rw [mul_div_assoc', div_le_iff₀ hb1]; nlinarith [abs_nonneg b]

/-- `δ^c = e^{-c log δ⁻¹}` -/
lemma rpow_eq_exp_log_inv {δ c : ℝ} (hδ : 0 < δ) : δ ^ c = Real.exp (-(c * Real.log δ⁻¹)) := by
  rw [Real.rpow_def_of_pos hδ, Real.log_inv]; ring_nf

end DZZ
end LQGMetric
