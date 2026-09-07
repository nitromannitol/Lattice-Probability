/-
Pre-Brownian motion exists.

Mathlib 4.32 defines `ProbabilityTheory.IsPreBrownianReal` and the projective
family of its finite-dimensional laws, and records that the Kolmogorov extension
theorem, which would produce a process with those laws, is not available.  White
noise supplies one directly: the indicators of the intervals `(0, t]` have
`L²`-inner products `min s t`, so the isonormal process evaluated at them is a
centred Gaussian process with the covariance of Brownian motion.
-/
import Mathlib
import LatticeProb.Gauss.WhiteNoise

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

/-- The indicator of the interval `(0, t]`, the test function whose white noise
is Brownian motion at time `t`. -/
def brownianTest (t : ℝ≥0) : ℝ → ℝ := (Set.Ioc (0 : ℝ) (t : ℝ)).indicator fun _ => (1 : ℝ)

theorem memLp_brownianTest (t : ℝ≥0) : MemLp (brownianTest t) 2 (volume : Measure ℝ) := by
  refine memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr ?_)
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

theorem integral_brownianTest_mul (s t : ℝ≥0) :
    ∫ y : ℝ, brownianTest s y * brownianTest t y = (min s t : ℝ≥0) := by
  have hpt : ∀ y : ℝ, brownianTest s y * brownianTest t y
      = (Set.Ioc (0 : ℝ) ((min s t : ℝ≥0) : ℝ)).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases h1 : y ∈ Set.Ioc (0 : ℝ) (s : ℝ) <;> by_cases h2 : y ∈ Set.Ioc (0 : ℝ) (t : ℝ) <;>
      simp only [brownianTest, Set.indicator_apply, h1, h2, if_pos, if_neg, not_false_iff] <;>
      simp_all [Set.mem_Ioc, NNReal.coe_min]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_indicator_const _
    measurableSet_Ioc, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal (NNReal.coe_nonneg (min s t))]

/-! ### Pre-Brownian motion -/

section PreBrownian

variable {w : Set (Lp ℝ 2 (volume : Measure ℝ))} [Countable ↥w]

/-- Brownian motion built from white noise on the line: the value at time `t` is
the noise of the indicator of `(0, t]`. -/
def brownian (b : HilbertBasis w ℝ (Lp ℝ 2 (volume : Measure ℝ))) (t : ℝ≥0) :
    (↥w → ℝ) → ℝ := whiteNoise b (brownianTest t)

theorem memLp_whiteNoise {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {v : Set (Lp ℝ 2 μ)} [Countable ↥v] (b : HilbertBasis v ℝ (Lp ℝ 2 μ)) (f : X → ℝ) :
    MemLp (whiteNoise b f) 2 (gaussLaw ↥v) := memLp_isoProc b _

/-- **Pre-Brownian motion exists.**  The white noise of the indicators of the
intervals `(0, t]` is a centred Gaussian process with covariance `min s t`,
which is the definition of a pre-Brownian motion. -/
theorem isPreBrownianReal_brownian (b : HilbertBasis w ℝ (Lp ℝ 2 (volume : Measure ℝ))) :
    IsPreBrownianReal (brownian b) (gaussLaw ↥w) := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance
    ((isGaussianProcess_whiteNoise b).comp_right brownianTest) (fun t => ?_) (fun s t hst => ?_)
  · exact integral_whiteNoise b _
  · show cov[whiteNoise b (brownianTest s), whiteNoise b (brownianTest t); gaussLaw ↥w] = (s : ℝ)
    rw [covariance_eq_sub (memLp_whiteNoise b _) (memLp_whiteNoise b _),
      integral_whiteNoise b _, integral_whiteNoise b _]
    have hmul : ∫ ω, (whiteNoise b (brownianTest s) * whiteNoise b (brownianTest t)) ω
          ∂(gaussLaw ↥w)
        = ∫ y : ℝ, brownianTest s y * brownianTest t y := by
      simp only [Pi.mul_apply]
      exact integral_whiteNoise_mul b (memLp_brownianTest s) (memLp_brownianTest t)
    rw [hmul, integral_brownianTest_mul, min_eq_left hst]
    ring

/-! ### The canonical pre-Brownian motion -/

/-- **The canonical pre-Brownian motion**, on the Gaussian product space over a
countable orthonormal basis of `L²(ℝ)`. -/
def brownianOf (t : ℝ≥0) : (↥(l2Basis (volume : Measure ℝ)) → ℝ) → ℝ :=
  brownian (l2HilbertBasis (volume : Measure ℝ)) t

theorem isPreBrownianReal_brownianOf :
    IsPreBrownianReal brownianOf (whiteNoiseLaw (volume : Measure ℝ)) :=
  isPreBrownianReal_brownian _

end PreBrownian

/-- **Pre-Brownian motion exists**, on the Gaussian product space over a
countable orthonormal basis of `L²(ℝ)`. -/
theorem exists_isPreBrownianReal :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → ℝ), @IsPreBrownianReal Ω mΩ B P := by
  obtain ⟨v, hv, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2 (volume : Measure ℝ)
  haveI : Countable ↥v := hv.to_subtype
  exact ⟨↥v → ℝ, inferInstance, gaussLaw ↥v, brownian b, isPreBrownianReal_brownian b⟩

end LatticeProb

end
