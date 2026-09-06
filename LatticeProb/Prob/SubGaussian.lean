/-
Sub-Gaussian behaviour on a range of the parameter, which is what a variable
with only an exponential moment has and what Mathlib's
`ProbabilityTheory.HasSubgaussianMGF` does not provide: that predicate demands
the Gaussian bound for every `t`, while a variable with only an exponential
moment satisfies it only for `|t|` below a threshold.

The elementary input is the pointwise bound `e^u ≤ 1 + u + u² e^{|u|}`, valid for
every real `u`.  Mathlib has the Taylor estimate only on `|u| ≤ 1`
(`Real.abs_exp_sub_one_sub_id_le`), so it is proved here from
`Real.add_one_le_exp` alone, in two cases.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- `(1 - u) e^u ≤ 1` for every real `u`: the tangent-line bound at `-u`. -/
theorem one_sub_mul_exp_le (u : ℝ) : (1 - u) * Real.exp u ≤ 1 := by
  have hepos : 0 < Real.exp u := Real.exp_pos u
  have h := Real.add_one_le_exp (-u)
  have hmul : (-u + 1) * Real.exp u ≤ Real.exp (-u) * Real.exp u :=
    mul_le_mul_of_nonneg_right h hepos.le
  rw [← Real.exp_add] at hmul
  simp only [neg_add_cancel, Real.exp_zero] at hmul
  have hre : (1 - u) * Real.exp u = (-u + 1) * Real.exp u := by ring
  rw [hre]
  exact hmul

/-- `e^u ≤ 1 + u + u² e^{|u|}` for every real `u`. -/
theorem exp_le_one_add_add_sq (u : ℝ) : Real.exp u ≤ 1 + u + u ^ 2 * Real.exp |u| := by
  have hepos : 0 < Real.exp u := Real.exp_pos u
  have hkey := one_sub_mul_exp_le u
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    rcases le_or_gt 1 u with h1 | h1
    · have hsq : (1 : ℝ) ≤ u ^ 2 := by nlinarith
      nlinarith [hepos, hsq]
    · nlinarith [hepos, hkey]
  · rw [abs_of_neg hu]
    have hpos : (0 : ℝ) < 1 - u := by linarith
    have hone : (1 : ℝ) ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    have hprod : 0 ≤ (1 - u) * u ^ 2 * (Real.exp (-u) - 1) :=
      mul_nonneg (mul_nonneg hpos.le (sq_nonneg u)) (by linarith)
    nlinarith [hkey, hprod, hpos, sq_nonneg u, mul_nonneg hpos.le (sq_nonneg u)]

/-- `r² ≤ 4 e^{a r} / a²` for `r ≥ 0` and `a > 0`: a quadratic is dominated by an
exponential, with an explicit constant, from the tangent-line bound alone. -/
theorem sq_le_exp_mul (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 0 ≤ r) :
    r ^ 2 ≤ 4 / a ^ 2 * Real.exp (a * r) := by
  have h1 : 1 + a * r / 2 ≤ Real.exp (a * r / 2) := by
    have := Real.add_one_le_exp (a * r / 2)
    linarith
  have h2 : Real.exp (a * r / 2) ^ 2 = Real.exp (a * r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hnn : (0 : ℝ) ≤ 1 + a * r / 2 := by positivity
  have h3 : (a * r / 2) ^ 2 ≤ Real.exp (a * r) := by
    rw [← h2]
    nlinarith [h1, hnn]
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ha2]
  nlinarith [h3, ha2]

/-- The one-variable input to `lem:weighted-exp-conc`: a centred law with an
exponential moment has a Gaussian moment generating function on the range
`|s| ≤ θ₀/2`. -/
theorem integral_exp_mul_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ₀ K₀ : ℝ)
    (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hK : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hid : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) (s : ℝ) (hs : |s| ≤ θ₀ / 2) :
    ∫ z, Real.exp (s * z) ∂ν ≤ 1 + 16 / θ₀ ^ 2 * K₀ * s ^ 2 := by
  have hθ2 : (0 : ℝ) < θ₀ / 2 := by linarith
  have hpt : ∀ z : ℝ, Real.exp (s * z)
      ≤ 1 + s * z + s ^ 2 * (16 / θ₀ ^ 2) * Real.exp (θ₀ * |z|) := by
    intro z
    have hbase := exp_le_one_add_add_sq (s * z)
    have habs : |s * z| ≤ θ₀ / 2 * |z| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg z)
    have hexpmono : Real.exp |s * z| ≤ Real.exp (θ₀ / 2 * |z|) := Real.exp_le_exp.mpr habs
    have hsq : z ^ 2 ≤ 4 / (θ₀ / 2) ^ 2 * Real.exp (θ₀ / 2 * |z|) := by
      have := sq_le_exp_mul (θ₀ / 2) hθ2 |z| (abs_nonneg z)
      rwa [sq_abs] at this
    have hc : 4 / (θ₀ / 2) ^ 2 = 16 / θ₀ ^ 2 := by field_simp; ring
    rw [hc] at hsq
    have hjoin : Real.exp (θ₀ / 2 * |z|) * Real.exp (θ₀ / 2 * |z|)
        = Real.exp (θ₀ * |z|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hpos : (0 : ℝ) ≤ Real.exp (θ₀ / 2 * |z|) := (Real.exp_pos _).le
    calc Real.exp (s * z) ≤ 1 + s * z + (s * z) ^ 2 * Real.exp |s * z| := hbase
      _ ≤ 1 + s * z + s ^ 2 * (16 / θ₀ ^ 2) * Real.exp (θ₀ * |z|) := by
          rw [← hjoin]
          have h1 : (s * z) ^ 2 = s ^ 2 * z ^ 2 := by ring
          rw [h1]
          have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
          have hprod : z ^ 2 * Real.exp |s * z|
              ≤ (16 / θ₀ ^ 2 * Real.exp (θ₀ / 2 * |z|)) * Real.exp (θ₀ / 2 * |z|) :=
            mul_le_mul hsq hexpmono (Real.exp_pos _).le (by positivity)
          have hfin := mul_le_mul_of_nonneg_left hprod hs2
          nlinarith [hfin]
  have hmeasL : Measurable fun z : ℝ => Real.exp (s * z) := by fun_prop
  have hintL : Integrable (fun z : ℝ => Real.exp (s * z)) ν := by
    refine hexp.mono' hmeasL.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc s * z ≤ |s * z| := le_abs_self _
      _ = |s| * |z| := abs_mul s z
      _ ≤ θ₀ / 2 * |z| := mul_le_mul_of_nonneg_right hs (abs_nonneg z)
      _ ≤ θ₀ * |z| := by nlinarith [abs_nonneg z, hθ₀]
  have hsid : Integrable (fun z : ℝ => s * z) ν := hid.const_mul s
  have hA : Integrable (fun z : ℝ => 1 + s * z) ν := (integrable_const 1).add hsid
  have hB : Integrable
      (fun z : ℝ => s ^ 2 * (16 / θ₀ ^ 2) * Real.exp (θ₀ * |z|)) ν := hexp.const_mul _
  have hintR : Integrable
      (fun z : ℝ => 1 + s * z + s ^ 2 * (16 / θ₀ ^ 2) * Real.exp (θ₀ * |z|)) ν := hA.add hB
  refine le_trans (integral_mono hintL hintR (fun z => hpt z)) ?_
  have hsplit : ∫ z, (1 + s * z + s ^ 2 * (16 / θ₀ ^ 2) * Real.exp (θ₀ * |z|)) ∂ν
      = (∫ z, (1 + s * z) ∂ν)
        + ∫ z, s ^ 2 * (16 / θ₀ ^ 2) * Real.exp (θ₀ * |z|) ∂ν := integral_add hA hB
  have hA' : ∫ z, (1 + s * z) ∂ν = 1 := by
    rw [integral_add (integrable_const 1) hsid, integral_const_mul, hmean, integral_const]
    simp
  have hB' : ∫ z, s ^ 2 * (16 / θ₀ ^ 2) * Real.exp (θ₀ * |z|) ∂ν
      = s ^ 2 * (16 / θ₀ ^ 2) * ∫ z, Real.exp (θ₀ * |z|) ∂ν := integral_const_mul _ _
  rw [hsplit, hA', hB']
  have hc : (0 : ℝ) ≤ s ^ 2 * (16 / θ₀ ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hK hc
  nlinarith [hmul]

/-- A law with an exponential moment has a first moment. -/
theorem integrable_id_of_exp_moment (ν : Measure ℝ) (θ₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) : Integrable id ν := by
  refine (hexp.const_mul (1 / θ₀)).mono' (measurable_id.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  have h1 : θ₀ * |z| ≤ Real.exp (θ₀ * |z|) := by
    have := Real.add_one_le_exp (θ₀ * |z|)
    linarith
  rw [show |id z| = |z| from rfl,
    show (1 : ℝ) / θ₀ * Real.exp (θ₀ * |z|) = Real.exp (θ₀ * |z|) / θ₀ by ring,
    le_div_iff₀ hθ₀]
  nlinarith [h1]

/-- `X` is sub-Gaussian on the range `s₀`: its moment generating function is
Gaussian for every parameter of size at most `s₀`.  Mathlib's
`ProbabilityTheory.HasSubgaussianMGF` is the case `s₀ = ∞`, which a variable with
only an exponential moment does not satisfy. -/
def SubGaussianOn {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (c s₀ : ℝ)
    (μ : Measure Ω) : Prop :=
  ∀ s : ℝ, |s| ≤ s₀ →
    Integrable (fun ω => Real.exp (s * X ω)) μ ∧
      ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (c * s ^ 2)

/-- A centred law with an exponential moment is sub-Gaussian on the range
`θ₀/2`. -/
theorem subGaussianOn_of_exp_moment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hK : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hid : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) :
    SubGaussianOn id (16 / θ₀ ^ 2 * K₀) (θ₀ / 2) ν := by
  intro s hs
  have hint : Integrable (fun z : ℝ => Real.exp (s * z)) ν := by
    refine hexp.mono' (by fun_prop : Measurable fun z : ℝ => Real.exp (s * z)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc s * z ≤ |s * z| := le_abs_self _
      _ = |s| * |z| := abs_mul s z
      _ ≤ θ₀ / 2 * |z| := mul_le_mul_of_nonneg_right hs (abs_nonneg z)
      _ ≤ θ₀ * |z| := by nlinarith [abs_nonneg z, hθ₀]
  refine ⟨hint, ?_⟩
  refine le_trans (integral_exp_mul_le ν θ₀ K₀ hθ₀ hexp hK hid hmean s hs) ?_
  have := Real.add_one_le_exp (16 / θ₀ ^ 2 * K₀ * s ^ 2)
  linarith

/-- Sub-Gaussianity on a range passes to independent weighted sums, with the
range shrunk by the largest weight. -/
theorem integral_exp_weighted_sum_le {N : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c s₀ : ℝ) (hSG : SubGaussianOn id c s₀ ν) (ℓ : Fin N → ℝ) (lam : ℝ)
    (hlam : ∀ i, |lam * ℓ i| ≤ s₀) :
    ∫ ξ, Real.exp (lam * ∑ i : Fin N, ℓ i * ξ i) ∂(Measure.pi fun _ : Fin N => ν)
      ≤ Real.exp (c * lam ^ 2 * ∑ i : Fin N, ℓ i ^ 2) := by
  have hfac : ∀ ξ : Fin N → ℝ, Real.exp (lam * ∑ i : Fin N, ℓ i * ξ i)
      = ∏ i : Fin N, Real.exp (lam * ℓ i * ξ i) := by
    intro ξ
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc ∫ ξ, Real.exp (lam * ∑ i : Fin N, ℓ i * ξ i) ∂(Measure.pi fun _ : Fin N => ν)
      = ∫ ξ : Fin N → ℝ, ∏ i : Fin N, Real.exp (lam * ℓ i * ξ i)
        ∂(Measure.pi fun _ : Fin N => ν) :=
        integral_congr_ae (Filter.Eventually.of_forall hfac)
    _ = ∏ i : Fin N, ∫ z : ℝ, Real.exp (lam * ℓ i * z) ∂ν :=
        integral_fintype_prod_eq_prod (fun i z => Real.exp (lam * ℓ i * z))
    _ ≤ ∏ i : Fin N, Real.exp (c * (lam * ℓ i) ^ 2) := by
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
        · exact integral_nonneg fun z => (Real.exp_pos _).le
        · exact (hSG (lam * ℓ i) (hlam i)).2
    _ = Real.exp (c * lam ^ 2 * ∑ i : Fin N, ℓ i ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Chernoff from sub-Gaussianity on a range: the Bernstein tail, Gaussian at
small deviations and exponential beyond the range. -/
theorem measure_ge_le_of_subGaussianOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c s₀ : ℝ) (hc : 0 < c) (hs₀ : 0 < s₀)
    (hSG : SubGaussianOn X c s₀ μ) (r : ℝ) (hr : 0 ≤ r) :
    μ.real {ω | r ≤ X ω}
      ≤ Real.exp (-min (r ^ 2 / (4 * c)) (s₀ * r / 2)) := by
  set lam : ℝ := min (r / (2 * c)) s₀ with hlamdef
  have hc2 : (0 : ℝ) < 2 * c := by linarith
  have hlam0 : 0 ≤ lam := le_min (by positivity) hs₀.le
  have hlams : |lam| ≤ s₀ := by
    rw [abs_of_nonneg hlam0]
    exact min_le_right _ _
  obtain ⟨hint, hmgf⟩ := hSG lam hlams
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) (t := lam) r hlam0 hint
  have hmgfle : mgf X μ lam ≤ Real.exp (c * lam ^ 2) := hmgf
  have hexp0 : (0 : ℝ) < Real.exp (-lam * r) := Real.exp_pos _
  have hstep : Real.exp (-lam * r) * mgf X μ lam
      ≤ Real.exp (-lam * r + c * lam ^ 2) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left hmgfle hexp0.le
  refine le_trans hch (le_trans hstep (Real.exp_le_exp.mpr ?_))
  rcases le_total (r / (2 * c)) s₀ with hcase | hcase
  · have hl : lam = r / (2 * c) := min_eq_left hcase
    rw [hl]
    have : -(r / (2 * c)) * r + c * (r / (2 * c)) ^ 2 = -(r ^ 2 / (4 * c)) := by
      field_simp
      ring
    rw [this]
    exact neg_le_neg (min_le_left _ _)
  · have hl : lam = s₀ := min_eq_right hcase
    rw [hl]
    have hcs : c * s₀ ≤ r / 2 := by
      rw [le_div_iff₀ hc2] at hcase
      nlinarith [hcase, hs₀]
    have hbound : -s₀ * r + c * s₀ ^ 2 ≤ -(s₀ * r / 2) := by nlinarith [hcs, hs₀.le]
    exact le_trans hbound (neg_le_neg (min_le_right _ _))

end LatticeProb
