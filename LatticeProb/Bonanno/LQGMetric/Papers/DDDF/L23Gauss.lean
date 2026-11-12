/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L23Gauss at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationVector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Variance of Lipschitz functions of Gaussian vectors (tool for DDDF Lemma 23)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1050–1055 (proof of `Lem:VarApriori`): for a
centered Gaussian vector `Y = A N` and `f` `ξ`-Lipschitz for the sup metric,
`Var f(Y) ≤ ξ² max_i Var Y_i`, "by the Gaussian concentration inequality of [DZZ18, Lemma 2.1],
applied as in [DD18, Lemma 5.8]".

* `GaussConc.variance_le_of_lipschitz`: `Var F(N) ≤ L²` for `L`-Lipschitz `F` of a standard
  Gaussian `N`. Derived from the sharp sub-Gaussian MGF bound `E e^{t(F − EF)} ≤ e^{t²L²/2}`
  (`GaussConc.mgf_le_of_lipschitz`, Tsirelson–Ibragimov–Sudakov; Adler–Taylor (2.1.13)) by the
  second-order expansion at `t = 0`: `e^y + e^{−y} ≥ 2 + y²` gives
  `t² Var F ≤ 2 (e^{t²L²/2} − 1) ≤ t² L² e^{t²L²/2}`, and `t → 0`.
* `GaussConc.variance_le_of_lipschitz_vector`: `Var g(X) ≤ K² σ²` for a centered Gaussian vector
  `X` with `σ² = max_i Var X_i` and `g` `K`-Lipschitz for the sup metric (`X = A N` in law with
  rows of norm `≤ σ`, `GaussConc.exists_gramVec_of_centered`, as in DDDF l. 1052).

The passage "Gaussian concentration ⇒ variance bound" is the standard second-order expansion of
the MGF (own elementary step, ≈ 40 lines; recorded in the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace LQGMetric
namespace GaussConc

/-- `2 + y² ≤ e^y + e^{−y}` -/
lemma two_add_sq_le_exp_add_exp_neg (y : ℝ) : 2 + y ^ 2 ≤ exp y + exp (-y) := by
  have key : ∀ y : ℝ, 0 ≤ y → 2 + y ^ 2 ≤ exp y + exp (-y) := by
    intro y hy
    have h1 : y / 2 ≤ sinh (y / 2) := Real.self_le_sinh_iff.2 (by linarith)
    have e1 : exp y = exp (y / 2) * exp (y / 2) := by rw [← Real.exp_add]; ring_nf
    have e2 : exp (-y) = exp (-(y / 2)) * exp (-(y / 2)) := by rw [← Real.exp_add]; ring_nf
    have e3 : exp (y / 2) * exp (-(y / 2)) = 1 := by rw [← Real.exp_add]; simp
    have hs : exp y + exp (-y) - 2 = (2 * sinh (y / 2)) ^ 2 := by
      rw [Real.sinh_eq, e1, e2]; nlinarith [e3]
    nlinarith [h1]
  rcases le_total 0 y with hy | hy
  · exact key y hy
  · have := key (-y) (by linarith); rw [neg_neg, neg_sq] at this; linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Gaussian Poincaré-type variance bound**: `Var F(N) ≤ L²` for `L`-Lipschitz `F` of a
standard Gaussian vector `N`. -/
theorem variance_le_of_lipschitz {F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    Var[F; stdGaussian E] ≤ (L : ℝ) ^ 2 := by
  set μ := stdGaussian E
  set m := ∫ y, F y ∂μ
  rw [variance_eq_integral hF.continuous.aemeasurable]
  set V := ∫ x, (F x - m) ^ 2 ∂μ
  have hbound : ∀ t : ℝ, 0 < t → V ≤ (L : ℝ) ^ 2 * exp (t ^ 2 * (L : ℝ) ^ 2 / 2) := by
    intro t ht
    have hi1 : Integrable (fun x => exp (t * (F x - m))) μ := integrable_exp_of_lipschitz hF t
    have hi2 : Integrable (fun x => exp (-t * (F x - m))) μ :=
      integrable_exp_of_lipschitz hF (-t)
    have hi12 : Integrable (fun x => exp (t * (F x - m)) + exp (-t * (F x - m))) μ := hi1.add hi2
    have hm1 : ∫ x, exp (t * (F x - m)) ∂μ ≤ exp (t ^ 2 * (L : ℝ) ^ 2 / 2) := by
      have := mgf_le_of_lipschitz hF t; rwa [mgf] at this
    have hm2 : ∫ x, exp (-t * (F x - m)) ∂μ ≤ exp ((-t) ^ 2 * (L : ℝ) ^ 2 / 2) := by
      have := mgf_le_of_lipschitz hF (-t); rwa [mgf] at this
    have hmono : ∫ x, t ^ 2 * (F x - m) ^ 2 ∂μ ≤
        ∫ x, (exp (t * (F x - m)) + exp (-t * (F x - m)) - 2) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
        (hi12.sub (integrable_const _)) (ae_of_all _ fun x => ?_)
      have := two_add_sq_le_exp_add_exp_neg (t * (F x - m))
      simp only [neg_mul] at this ⊢
      nlinarith
    rw [integral_const_mul, integral_sub hi12 (integrable_const _),
      integral_add hi1 hi2, integral_const] at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
    rw [neg_sq] at hm2
    set x := t ^ 2 * (L : ℝ) ^ 2 / 2 with hx
    have hx0 : 0 ≤ x := by positivity
    -- `e^x − 1 ≤ x e^x`
    have hexp : exp x - 1 ≤ x * exp x := by
      have h := Real.add_one_le_exp (-x)
      have h2 : exp (-x) * exp x = 1 := by rw [← Real.exp_add]; simp
      nlinarith [exp_pos x]
    have ht2 : 0 < t ^ 2 := by positivity
    have : t ^ 2 * V ≤ t ^ 2 * ((L : ℝ) ^ 2 * exp x) := by
      have h2x : 2 * x * exp x = t ^ 2 * ((L : ℝ) ^ 2 * exp x) := by rw [hx]; ring
      change t ^ 2 * V ≤ _ at hmono
      linarith
    exact le_of_mul_le_mul_left this ht2
  have hlim : Tendsto (fun t : ℝ => (L : ℝ) ^ 2 * exp (t ^ 2 * (L : ℝ) ^ 2 / 2)) (𝓝[>] 0)
      (𝓝 ((L : ℝ) ^ 2)) := by
    have hc : Continuous fun t : ℝ => (L : ℝ) ^ 2 * exp (t ^ 2 * (L : ℝ) ^ 2 / 2) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => hbound t ht)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}

/-- **Variance of a Lipschitz function of a centered Gaussian vector** (DDDF l. 1050–1055):
`Var g(X) ≤ K² σ²` if `g` is `K`-Lipschitz for the sup metric and `σ² = max_i Var X_i`. -/
theorem variance_le_of_lipschitz_vector (hX : HasGaussianLaw X P)
    (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ2 : σ ^ 2 = ⨆ i, Var[fun ω => X ω i; P]) {g : (Fin n → ℝ) → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    Var[fun ω => g (X ω); P] ≤ (K : ℝ) ^ 2 * σ ^ 2 := by
  obtain ⟨v, hv, hmap⟩ := exists_gramVec_of_centered hX h0
  have hvσ : ∀ i, ‖v i‖ ≤ ((⟨σ, hσ⟩ : ℝ≥0) : ℝ) := norm_le_of_sq_eq_iSup hv hσ hσ2
  have hgv := lipschitzWith_gramVec hvσ
  have hgm : Measurable (gramVec v) := hgv.continuous.measurable
  have e1 : Var[fun ω => g (X ω); P] = Var[g; P.map X] :=
    (variance_map hg.continuous.aemeasurable hX.aemeasurable).symm
  rw [e1, hmap, variance_map hg.continuous.aemeasurable hgm.aemeasurable]
  refine (variance_le_of_lipschitz (hg.comp hgv)).trans (le_of_eq ?_)
  change ((K : ℝ) * σ) ^ 2 = (K : ℝ) ^ 2 * σ ^ 2
  ring

end GaussConc
end LQGMetric
