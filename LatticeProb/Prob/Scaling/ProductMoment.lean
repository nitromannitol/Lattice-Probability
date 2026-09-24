/-
A Minkowski-type inequality for a nonnegative function of two independent arguments: the
`ν`-average of the `μ`-side `r`-th-moment norm is bounded by the JOINT `r`-th-moment norm on
the product measure `μ.prod ν`. Stated for abstract measurable spaces and measures only. Proved
by a Fubini swap (identifying the iterated integral of the `r`-th power with the integral over
the product) followed by Jensen's inequality for the concave map `t ↦ t^{1/r}`.

Moved from Parking-Sharpness.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Filter

noncomputable section

namespace LatticeProb.Scaling.ProductMoment

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- **The `ν`-average of the `μ`-side `L^r` norm is bounded by the joint `L^r` norm on the
product measure.**  For a nonnegative `F : Ω → Ω' → ℝ` whose `r`-th power is integrable on the
product `μ.prod ν` (`r ≥ 1`, `μ` `σ`-finite, `ν` a probability measure). -/
theorem integral_rpow_root_le_prod_rpow_root (μ : Measure Ω) (ν : Measure Ω') [SFinite μ]
    [IsProbabilityMeasure ν] (F : Ω → Ω' → ℝ) (hF0 : ∀ p η, 0 ≤ F p η) {r : ℝ} (hr : 1 ≤ r)
    (hFi : Integrable (fun ω : Ω × Ω' => F ω.1 ω.2 ^ r) (μ.prod ν)) :
    Integrable (fun η => (∫ p, F p η ^ r ∂μ) ^ (1 / r)) ν ∧
      ∫ η, (∫ p, F p η ^ r ∂μ) ^ (1 / r) ∂ν ≤
        (∫ ω : Ω × Ω', F ω.1 ω.2 ^ r ∂(μ.prod ν)) ^ (1 / r) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  set f2 : Ω → Ω' → ℝ := fun p η => F p η ^ r with hf2def
  have huncurry : Function.uncurry f2 = fun ω : Ω × Ω' => F ω.1 ω.2 ^ r := by
    funext ω; simp [f2, Function.uncurry]
  have hfi' : Integrable (Function.uncurry f2) (μ.prod ν) := by rw [huncurry]; exact hFi
  have hswap := integral_integral_swap (μ := μ) (ν := ν) hfi'
  have hint := integral_integral (μ := μ) (ν := ν) hfi'
  have hkey : (∫ η, ∫ p, f2 p η ∂μ ∂ν) = ∫ ω : Ω × Ω', F ω.1 ω.2 ^ r ∂(μ.prod ν) := by
    rw [← hswap, hint]
  -- Jensen: `t ↦ t^(1/r)` is concave on `[0, ∞)`.
  have hp2 : (0 : ℝ) ≤ 1 / r := by positivity
  have hp1 : 1 / r ≤ 1 := by
    rw [div_le_one hr0]; exact hr
  have hg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun y : ℝ => y ^ (1 / r)) := Real.concaveOn_rpow hp2 hp1
  have hgc : ContinuousOn (fun y : ℝ => y ^ (1 / r)) (Set.Ici (0 : ℝ)) :=
    continuousOn_id.rpow_const (fun x _ => Or.inr hp2)
  set Y : Ω' → ℝ := fun η => ∫ p, f2 p η ∂μ with hYdef
  have hYnn : ∀ η, 0 ≤ Y η := fun η => integral_nonneg fun p => Real.rpow_nonneg (hF0 p η) r
  have hYmem : ∀ᵐ η ∂ν, Y η ∈ Set.Ici (0 : ℝ) := Filter.Eventually.of_forall fun η => hYnn η
  have hYint : Integrable Y ν := by rw [hYdef]; exact hfi'.integral_prod_right
  have hcont : Continuous (fun t : ℝ => t ^ ((1:ℝ) / r)) := by
    exact Real.continuous_rpow_const hp2
  have hgi2 : Integrable ((fun y : ℝ => y ^ (1 / r)) ∘ Y) ν := by
    have heqYY : (fun y : ℝ => y ^ (1 / r)) ∘ Y = fun η => (Y η) ^ (1 / r) := rfl
    rw [heqYY]
    have hbound : ∀ η, (Y η) ^ (1 / r) ≤ 1 + Y η := by
      intro η
      have hYη := hYnn η
      rcases le_total (Y η) 1 with h | h
      · have h1 : (Y η) ^ (1 / r) ≤ 1 := Real.rpow_le_one (hYnn η) h hp2
        linarith
      · have h2 : (Y η) ^ (1 / r) ≤ (Y η) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h hp1
        rw [Real.rpow_one] at h2
        linarith
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hYint)
      (hcont.comp_aestronglyMeasurable hYint.1) ?_
    filter_upwards with η
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hYnn η) _)]
    exact hbound η
  have hjen := ConcaveOn.le_map_integral hg hgc (isClosed_Ici) hYmem hYint hgi2
  rw [hkey] at hjen
  refine ⟨?_, hjen⟩
  have heqYY : (fun η => (Y η) ^ (1 / r)) = (fun y : ℝ => y ^ (1 / r)) ∘ Y := rfl
  rw [heqYY]
  exact hgi2

end LatticeProb.Scaling.ProductMoment

end
