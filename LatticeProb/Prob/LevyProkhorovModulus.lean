import Mathlib
import LatticeProb.Prob.LevyProkhorovLipschitz

/-!
# Integrals of bounded functions with a modulus of continuity and the Lévy-Prokhorov distance

The quantitative statement `|∫ f dμ - ∫ f dν| ≤ (L + 2 ‖f‖) ε` for bounded `L`-Lipschitz `f` and
`levyProkhorovEDist μ ν < ε` uses the Lipschitz property of `f` only through its consequence at scale `ε`:
`|f x - f y| ≤ c` whenever `dist x y < ε`, with `c = L ε`. This file states the bound in that form, so that it
applies to every bounded continuous function with a modulus of continuity, for instance a function that is
Lipschitz for another metric inducing the same uniform structure on a compact piece.

## Main results

* `integral_le_add_of_levyProkhorovEDist_lt_of_modulus`: for `f ≥ 0` bounded with
  `|f x - f y| ≤ c` whenever `dist x y < ε`, `∫ f dμ ≤ ∫ f dν + (c + ‖f‖ ε)`.
* `abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_modulus`: for bounded `f` with the same property,
  `|∫ f dμ - ∫ f dν| ≤ c + 2 ‖f‖ ε`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric BoundedContinuousFunction
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- **One-sided bound for nonnegative bounded functions with a modulus of continuity.** If
`levyProkhorovEDist μ ν < ε`, `f ≥ 0` is bounded continuous and `|f x - f y| ≤ c` whenever `dist x y < ε`,
then `∫ f dμ ≤ ∫ f dν + (c + ‖f‖ ε)`. -/
theorem integral_le_add_of_levyProkhorovEDist_lt_of_modulus (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hmod : ∀ x y, dist x y < ε → |f x - f y| ≤ c) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν + (c + ‖f‖ * ε) := by
  have h1 := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt μ ν hε hμν f
    (Filter.Eventually.of_forall hf0)
  -- thickening of `{t ≤ f}` lies in `{t ≤ f + c}`
  have hsub : ∀ t : ℝ, thickening ε {a | t ≤ f a} ⊆ {a | t ≤ f a + c} := by
    intro t a ha
    obtain ⟨b, hb, hab⟩ := mem_thickening_iff.1 ha
    have h2 := hmod a b hab
    have h4 : f b - f a ≤ |f a - f b| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have hb' : t ≤ f b := hb
    show t ≤ f a + c
    linarith
  have hanti1 : Antitone (fun t : ℝ => thickening ε {a | t ≤ f a}) :=
    fun s t hst => thickening_subset_of_subset ε (fun _ h => hst.trans h)
  have hanti2 : Antitone (fun t : ℝ => {a | t ≤ f a + c}) :=
    fun s t hst a ha => le_trans hst ha
  have h5 : ∫ t in Ioc 0 ‖f‖, ν.real (thickening ε {a | t ≤ f a})
      ≤ ∫ t in Ioc 0 ‖f‖, ν.real {a | t ≤ f a + c} :=
    setIntegral_mono (integrableOn_measureReal_of_antitone ν _ hanti1 0 ‖f‖)
      (integrableOn_measureReal_of_antitone ν _ hanti2 0 ‖f‖)
      (fun t => measureReal_mono (hsub t))
  -- layer cake for `f + c`
  have hint : Integrable (fun x => f x + c) ν := (f.integrable ν).add (integrable_const c)
  have hnn : 0 ≤ᵐ[ν] fun x => f x + c := Filter.Eventually.of_forall (fun x => by
    have := hf0 x; simp only [Pi.zero_apply]; linarith)
  have hbdd : (fun x => f x + c) ≤ᵐ[ν] fun _ => ‖f‖ + c := Filter.Eventually.of_forall (fun x => by
    have := f.norm_coe_le_norm x
    have := le_abs_self (f x)
    simp only [Real.norm_eq_abs] at *
    linarith)
  have hlay := Integrable.integral_eq_integral_Ioc_meas_le hint hnn hbdd
  have h6 : ∫ t in Ioc 0 ‖f‖, ν.real {a | t ≤ f a + c}
      ≤ ∫ t in Ioc 0 (‖f‖ + c), ν.real {a | t ≤ f a + c} := by
    apply setIntegral_mono_set (integrableOn_measureReal_of_antitone ν _ hanti2 0 (‖f‖ + c))
    · exact Filter.Eventually.of_forall (fun t => measureReal_nonneg)
    · exact Filter.Eventually.of_forall (Ioc_subset_Ioc_right (by linarith))
  have h7 : ∫ x, (f x + c) ∂ν = ∫ x, f x ∂ν + c := by
    rw [integral_add (f.integrable ν) (integrable_const c)]; simp
  nlinarith [h1, h5, hlay, h6, h7]

/-- **Bounded functions with a modulus of continuity and the Lévy-Prokhorov distance.** If
`levyProkhorovEDist μ ν < ε`, `f` is bounded continuous and `|f x - f y| ≤ c` whenever `dist x y < ε`, then
`|∫ f dμ - ∫ f dν| ≤ c + 2 ‖f‖ ε`. -/
theorem abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_modulus (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ)
    (hmod : ∀ x y, dist x y < ε → |f x - f y| ≤ c) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ c + 2 * ‖f‖ * ε := by
  -- shift to a nonnegative function
  let g : Ω →ᵇ ℝ := f + BoundedContinuousFunction.const Ω ‖f‖
  have hgx : ∀ x, g x = f x + ‖f‖ := fun x => by simp [g]
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    have h1 := f.norm_coe_le_norm x
    have h2 := neg_abs_le (f x)
    rw [hgx]
    simp only [Real.norm_eq_abs] at h1
    linarith
  have hgm : ∀ x y, dist x y < ε → |g x - g y| ≤ c := fun x y hxy => by
    rw [hgx, hgx, add_sub_add_right_eq_sub]
    exact hmod x y hxy
  have hgn : ‖g‖ ≤ 2 * ‖f‖ := by
    refine (norm_le (by positivity)).2 (fun x => ?_)
    have h1 := f.norm_coe_le_norm x
    rw [hgx]
    simp only [Real.norm_eq_abs] at h1 ⊢
    rw [abs_le] at h1
    rw [abs_le]
    constructor <;> linarith [norm_nonneg f]
  have hgint : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → ∫ x, g x ∂ρ = ∫ x, f x ∂ρ + ‖f‖ := by
    intro ρ hρ
    have : (g : Ω → ℝ) = fun x => f x + ‖f‖ := funext hgx
    rw [this, integral_add (f.integrable ρ) (integrable_const _)]; simp
  have hμν' : levyProkhorovEDist ν μ < ENNReal.ofReal ε := by rwa [levyProkhorovEDist_comm]
  have a1 := integral_le_add_of_levyProkhorovEDist_lt_of_modulus μ ν hε hc hμν g hg0 hgm
  have a2 := integral_le_add_of_levyProkhorovEDist_lt_of_modulus ν μ hε hc hμν' g hg0 hgm
  rw [hgint μ inferInstance, hgint ν inferInstance] at a1 a2
  have hb : ‖g‖ * ε ≤ 2 * ‖f‖ * ε := mul_le_mul_of_nonneg_right hgn hε.le
  rw [abs_le]
  constructor <;> linarith

end LatticeProb
