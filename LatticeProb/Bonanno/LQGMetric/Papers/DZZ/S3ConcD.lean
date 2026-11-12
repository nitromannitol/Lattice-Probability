/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcD at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcC

/-!
# `DZZConcApprox` from the Lipschitz inputs (P2-DZZCONC)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Proposition 3.17: (eq-concentration-approximate)
(l. 1528–1530) from (eq-upper-tail-deviation), (eq-lower-tail-deviation) and the mean–median
step (l. 1595–1613, "we adjust the value of `ι` appropriately": we use `ι/3`), and
(eq-concentration-approximate-2) (l. 1628–1630, probability `1 − e^{−Ω((log δ⁻¹)^{0.8})}`,
l. 1647) the same way (l. 1640–1651; "we will repeatedly use higher powers of `log δ⁻¹` to absorb
error terms", l. 1626).

* `lipData_tail`: `conc_of_lip` for the data `DZZLipData` (net mesh `η = 1`).
* **`dzzConcApprox_of`**: `DZZDistLip1 → DZZDistLip2 → DZZCrudeMoments → DZZConcApprox`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

/-- `conc_of_lip` for `DZZLipData`. -/
theorem lipData_tail : ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ)
    (σ ℓ τ ε : ℝ), 0 ≤ σ → 0 ≤ τ → DZZLipData P γ W δ A B σ ℓ τ ε →
    MemLp (logApproxLGD γ W δ A B) 2 P → ∀ V : ℝ, ∫ ω, logApproxLGD γ W δ A B ω ^ 2 ∂P ≤ V →
    ε ≤ 4⁻¹ → C * σ + 1 ≤ ℓ → ∀ M : ℝ, 0 < M →
    P.real {ω | 2 * τ + 3 * V / M +
        2 * M * (2 * ε + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2))) <
          |logApproxLGD γ W δ A B ω - ∫ ω', logApproxLGD γ W δ A B ω' ∂P|} ≤
      2 * ε + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2)) := by
  obtain ⟨C, hC1, hC⟩ := conc_of_lip.{u, 0}
  refine ⟨C, hC1, ?_⟩
  intro Ω _ P _ γ W δ A B σ ℓ τ ε hσ hτ hD hY V hV hε4 hℓ M hM
  obtain ⟨T, X, hX, h0, hvar, 𝒜, F, hYF, hε, hlip, n, t, hnet⟩ := hD
  exact hC P X hX h0 σ hσ hvar _ hY V hV 𝒜 F hYF ε hε ℓ τ hτ hlip 1 n t hnet hε4 hℓ M hM

/-- `exp (-(k L)) ≤ θ` for large `L` -/
lemma ev_exp_neg_le {k θ : ℝ} (hk : 0 < k) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop, exp (-(k * L)) ≤ θ := by
  have : Tendsto (fun L : ℝ => exp (-(k * L))) atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hk)
  exact (this.eventually (ge_mem_nhds hθ))

/-- `L^r e^{-b L^q} ≤ 1` for large `L` (mathlib `isLittleO_rpow_exp_pos_mul_atTop`). -/
lemma ev_rpow_mul_exp_le {r b q : ℝ} (hb : 0 < b) (hq : 0 < q) :
    ∀ᶠ L : ℝ in atTop, L ^ r * exp (-(b * L ^ q)) ≤ 1 := by
  have h := (isLittleO_rpow_exp_pos_mul_atTop (r / q) hb).comp_tendsto (tendsto_rpow_atTop hq)
  filter_upwards [h.bound one_pos, eventually_gt_atTop 0] with L hL hL0
  simp only [Function.comp, norm_eq_abs, one_mul] at hL
  have e : (L ^ q) ^ (r / q) = L ^ r := by
    rw [← Real.rpow_mul hL0.le]; congr 1; field_simp
  rw [e, abs_of_pos (Real.rpow_pos_of_pos hL0 r), abs_of_pos (exp_pos _)] at hL
  calc L ^ r * exp (-(b * L ^ q)) ≤ exp (b * L ^ q) * exp (-(b * L ^ q)) :=
        mul_le_mul_of_nonneg_right hL (exp_pos _).le
    _ = 1 := by rw [← exp_add]; simp

/-- the Gaussian exponent: `ℓ - g ≥ ℓ/2 ⇒ e^{-(ℓ-g)²/(2s)} ≤ e^{-ℓ²/(8s)}` -/
lemma exp_gauss_le {ℓ g s : ℝ} (hs : 0 < s) (hg : g ≤ ℓ / 2) (hg0 : 0 ≤ g) :
    exp (-(ℓ - g) ^ 2 / (2 * s)) ≤ exp (-(ℓ ^ 2 / (8 * s))) := by
  refine exp_le_exp.2 ?_
  have h1 : ℓ ^ 2 / 4 ≤ (ℓ - g) ^ 2 := by nlinarith
  rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma prob_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {S S' : Set Ω} {r : ℝ} (h : Sᶜ ⊆ S') (h' : P.real S' ≤ r) : P Sᶜ ≤ ENNReal.ofReal r :=
  (measure_mono h).trans (by rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal h')

/-- `√(K L) = √K L^{1/2}` -/
lemma sqrt_mul_eq_rpow {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) :
    √(K * L) = √K * L ^ (1 / 2 : ℝ) := by
  rw [Real.sqrt_mul hK, Real.sqrt_eq_rpow L]

/-- `b L^{1/2} + 1 ≤ a L` for large `L` (`a > 0`) -/
lemma ev_sqrt_add_le {p q a : ℝ} (hp : 0 < p) (hpq : p < q) (ha : 0 < a) (b : ℝ) :
    ∀ᶠ L : ℝ in atTop, b * L ^ p + 1 ≤ a * L ^ q := by
  filter_upwards [ev_rpow_le hpq (half_pos ha) b, ev_rpow_le (hp.trans hpq) (half_pos ha) 1,
    eventually_gt_atTop 0] with L h1 h2 hL
  rw [Real.rpow_zero, mul_one] at h2
  linarith

end DZZ
end LQGMetric
