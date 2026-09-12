/-
The Poisson (Bennett type) tail bound for a sum of independent nonnegative summands
bounded by `β`:

    P(∑ W_i ≥ s) ≤ (e μ / s)^{s/β} ,   μ ≥ ∑ E[W_i],  μ ≤ s .

The only analytic input is the convexity of the exponential on `[0, β]`: for `0 ≤ w ≤ β`,

    e^{λw} ≤ 1 + w (e^{λβ} - 1)/β ,

so that integrating against a nonnegative variable gives the moment generating function
bound `E[e^{λW}] ≤ exp(E[W](e^{λβ}-1)/β)`.  Independence turns the moment generating
function of the sum into a product, Chernoff's bound gives
`P(∑ W_i ≥ s) ≤ exp(-λ s + μ(e^{λβ}-1)/β)`, and the choice `λ = log(s/μ)/β` collapses the
exponent to `(s/β)(1 - log(s/μ))`.

Unlike Bernstein's inequality, which is governed by the variance, this bound keeps the
factor `(μ/s)^{s/β}`: it is what supplies a power of the truncated mean, and that power is
what the Fuk-Nagaev inequality needs from the middle block of a truncation.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- Convexity of the exponential on `[0, β]`: the exponential is below the chord. -/
theorem exp_mul_le_one_add_mul (β lam w : ℝ) (hβ : 0 < β) (hw0 : 0 ≤ w) (hwβ : w ≤ β) :
    Real.exp (lam * w) ≤ 1 + w * (Real.exp (lam * β) - 1) / β := by
  have hb : 0 ≤ w / β := div_nonneg hw0 hβ.le
  have ha : 0 ≤ 1 - w / β := by
    have : w / β ≤ 1 := (div_le_one hβ).mpr hwβ
    linarith
  have hab : (1 - w / β) + w / β = 1 := by ring
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (lam * β)) ha hb hab
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have hx : w / β * (lam * β) = lam * w := by
    field_simp
  rw [hx] at hconv
  refine hconv.trans (le_of_eq ?_)
  field_simp
  ring

/-- The moment generating function of a `[0, β]`-valued variable is controlled by its mean. -/
theorem mgf_le_of_nonneg_bounded {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → ℝ) (hint : Integrable W P)
    (β : ℝ) (hβ : 0 < β) (hW0 : ∀ᵐ ω ∂P, 0 ≤ W ω) (hWβ : ∀ᵐ ω ∂P, W ω ≤ β)
    (lam : ℝ) :
    mgf W P lam ≤ Real.exp ((∫ ω, W ω ∂P) * (Real.exp (lam * β) - 1) / β) := by
  have hmaj : Integrable (fun ω => 1 + W ω * (Real.exp (lam * β) - 1) / β) P :=
    (integrable_const 1).add ((hint.mul_const _).div_const _)
  have hbound : ∀ᵐ ω ∂P, Real.exp (lam * W ω) ≤ 1 + W ω * (Real.exp (lam * β) - 1) / β := by
    filter_upwards [hW0, hWβ] with ω h0 hb
    exact exp_mul_le_one_add_mul β lam (W ω) hβ h0 hb
  have hexpint : Integrable (fun ω => Real.exp (lam * W ω)) P := by
    refine Integrable.mono' hmaj ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
        hint.aestronglyMeasurable
    · filter_upwards [hbound] with ω hb
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hb
  have hle : ∫ ω, Real.exp (lam * W ω) ∂P
      ≤ ∫ ω, (1 + W ω * (Real.exp (lam * β) - 1) / β) ∂P :=
    integral_mono_ae hexpint hmaj hbound
  have hval : ∫ ω, (1 + W ω * (Real.exp (lam * β) - 1) / β) ∂P
      = 1 + (∫ ω, W ω ∂P) * (Real.exp (lam * β) - 1) / β := by
    rw [integral_add (integrable_const 1) ((hint.mul_const _).div_const _), integral_const,
      integral_div, integral_mul_const]
    simp
  have hexp := Real.add_one_le_exp ((∫ ω, W ω ∂P) * (Real.exp (lam * β) - 1) / β)
  rw [mgf]
  rw [hval] at hle
  linarith

/-- The value of the Chernoff exponent at `λ = log(s/μ)/β`. -/
theorem chernoff_poisson_value (β μ s : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (hs : μ ≤ s) :
    Real.exp (-(Real.log (s / μ) / β) * s
        + μ * (Real.exp ((Real.log (s / μ) / β) * β) - 1) / β)
      ≤ (Real.exp 1 * μ / s) ^ (s / β) := by
  have hs0 : 0 < s := lt_of_lt_of_le hμ hs
  have hratio : (0:ℝ) < s / μ := div_pos hs0 hμ
  have hcancel : (Real.log (s / μ) / β) * β = Real.log (s / μ) := div_mul_cancel₀ _ hβ.ne'
  rw [hcancel, Real.exp_log hratio]
  have hval : μ * (s / μ - 1) / β = (s - μ) / β := by
    field_simp
  rw [hval]
  have hrhs : (Real.exp 1 * μ / s) ^ (s / β)
      = Real.exp ((s / β) * (1 - Real.log (s / μ))) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    rw [Real.log_div (by positivity) hs0.ne', Real.log_mul (Real.exp_ne_zero 1) hμ.ne',
      Real.log_exp, Real.log_div hs0.ne' hμ.ne']
    ring
  rw [hrhs]
  refine Real.exp_le_exp.mpr ?_
  have hsb : (s - μ) / β ≤ s / β := by
    have hd : s / β - (s - μ) / β = μ / β := by
      field_simp
      ring
    have hp : (0:ℝ) ≤ μ / β := by positivity
    linarith
  have hexpand : -(Real.log (s / μ) / β) * s = -((s / β) * Real.log (s / μ)) := by ring
  rw [hexpand]
  nlinarith [hsb]

/-- Chernoff's bound for a sum of independent `[0, β]`-valued summands at a fixed `λ ≥ 0`. -/
theorem poisson_chernoff {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ι → Ω → ℝ) (hindep : iIndepFun W P)
    (hint : ∀ i, Integrable (W i) P) (β : ℝ) (hβ : 0 < β)
    (hW0 : ∀ i, ∀ᵐ ω ∂P, 0 ≤ W i ω) (hWβ : ∀ i, ∀ᵐ ω ∂P, W i ω ≤ β)
    (lam : ℝ) (hlam : 0 ≤ lam) (s : ℝ) :
    P {ω | s ≤ ∑ i, W i ω}
      ≤ ENNReal.ofReal (Real.exp (-lam * s
          + (∑ i, ∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β)) := by
  classical
  set S : Ω → ℝ := fun ω => ∑ i, W i ω with hS
  have hSint : Integrable S P := integrable_finsetSum _ fun i _ => hint i
  have hSb : ∀ᵐ ω ∂P, |S ω| ≤ (Fintype.card ι : ℝ) * β := by
    have hall0 : ∀ᵐ ω ∂P, ∀ i, 0 ≤ W i ω := ae_all_iff.mpr hW0
    have hallb : ∀ᵐ ω ∂P, ∀ i, W i ω ≤ β := ae_all_iff.mpr hWβ
    filter_upwards [hall0, hallb] with ω h0 hb
    have habs : |S ω| = S ω := abs_of_nonneg (Finset.sum_nonneg fun i _ => h0 i)
    rw [habs]
    calc S ω ≤ ∑ _i : ι, β := Finset.sum_le_sum fun i _ => hb i
      _ = (Fintype.card ι : ℝ) * β := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hSexp : Integrable (fun ω => Real.exp (lam * S ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * ((Fintype.card ι : ℝ) * β))))
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
        hSint.aestronglyMeasurable) ?_
    filter_upwards [hSb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : S ω ≤ (Fintype.card ι : ℝ) * β := (abs_le.mp hω).2
    nlinarith
  have hmgfsum : mgf S P lam = ∏ i, mgf (W i) P lam := by
    have h := hindep.mgf_sum₀ (t := lam) (fun i => (hint i).aemeasurable) Finset.univ
    have hfun : (∑ i ∈ Finset.univ, W i) = S := by
      funext ω
      rw [hS]
      simp
    rwa [hfun] at h
  have hfac : ∀ i : ι, mgf (W i) P lam
      ≤ Real.exp ((∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β) :=
    fun i => mgf_le_of_nonneg_bounded P (W i) (hint i) β hβ (hW0 i) (hWβ i) lam
  have hmgfnn : ∀ i : ι, 0 ≤ mgf (W i) P lam := by
    intro i
    rw [mgf]
    exact integral_nonneg fun ω => (Real.exp_pos _).le
  have hprod : ∏ i, mgf (W i) P lam
      ≤ Real.exp ((∑ i, ∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β) := by
    have h1 : ∏ i, mgf (W i) P lam
        ≤ ∏ i : ι, Real.exp ((∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β) :=
      Finset.prod_le_prod (fun i _ => hmgfnn i) (fun i _ => hfac i)
    refine h1.trans (le_of_eq ?_)
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_div, ← Finset.sum_mul]
  have hmgfle : mgf S P lam
      ≤ Real.exp ((∑ i, ∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β) := by
    rw [hmgfsum]; exact hprod
  have hchern := measure_ge_le_exp_mul_mgf (μ := P) (X := S) (t := lam) s hlam hSexp
  have hstep : P.real {ω | s ≤ S ω}
      ≤ Real.exp (-lam * s) * Real.exp ((∑ i, ∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β) :=
    hchern.trans (mul_le_mul_of_nonneg_left hmgfle (Real.exp_pos _).le)
  rw [← Real.exp_add] at hstep
  have hfin : P {ω | s ≤ S ω} ≠ ⊤ := measure_ne_top P _
  rw [measureReal_def, ← ENNReal.le_ofReal_iff_toReal_le hfin (Real.exp_pos _).le] at hstep
  exact hstep

/-- **The Poisson tail bound.**  For independent summands with values in `[0, β]` and total
mean at most `μ ≤ s`,

    P(∑ W_i ≥ s) ≤ (e μ / s) ^ (s / β) . -/
theorem poisson_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ι → Ω → ℝ) (hindep : iIndepFun W P)
    (hint : ∀ i, Integrable (W i) P) (β : ℝ) (hβ : 0 < β)
    (hW0 : ∀ i, ∀ᵐ ω ∂P, 0 ≤ W i ω) (hWβ : ∀ i, ∀ᵐ ω ∂P, W i ω ≤ β)
    (μ s : ℝ) (hμ : 0 < μ) (hmean : ∑ i, ∫ ω, W i ω ∂P ≤ μ) (hs : μ ≤ s) :
    P {ω | s ≤ ∑ i, W i ω} ≤ ENNReal.ofReal ((Real.exp 1 * μ / s) ^ (s / β)) := by
  set lam : ℝ := Real.log (s / μ) / β with hlamdef
  have hlam : 0 ≤ lam := div_nonneg (Real.log_nonneg ((one_le_div hμ).mpr hs)) hβ.le
  have h1 := poisson_chernoff P W hindep hint β hβ hW0 hWβ lam hlam s
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc : 0 ≤ Real.exp (lam * β) - 1 := by
    have h2 : (1:ℝ) ≤ Real.exp (lam * β) := Real.one_le_exp (by positivity)
    linarith
  have hmono : (∑ i, ∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β
      ≤ μ * (Real.exp (lam * β) - 1) / β := by
    gcongr
  calc Real.exp (-lam * s + (∑ i, ∫ ω, W i ω ∂P) * (Real.exp (lam * β) - 1) / β)
      ≤ Real.exp (-lam * s + μ * (Real.exp (lam * β) - 1) / β) :=
        Real.exp_le_exp.mpr (by linarith)
    _ ≤ (Real.exp 1 * μ / s) ^ (s / β) := chernoff_poisson_value β μ s hβ hμ hs

end LatticeProb
