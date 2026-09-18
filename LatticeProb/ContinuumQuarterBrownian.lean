/-
A continuous Brownian motion with variance `t/4`, constructed by halving
a standard Brownian motion. Finite weighted combinations are centred Gaussian
with covariance `min(s,t)/4`, yielding their characteristic functions.
-/
import LatticeProb.ContinuumNoiseField
import LatticeProb.Prob.BrownianContAll

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace LatticeProb.ContinuumStopping

/-- **A concrete quarter-Brownian motion with every path continuous exists.** Halving a real
Brownian motion `C` (`LatticeProb.exists_isBrownianReal_cont`) gives `B := C / 2`, and
`IsQuarterBrownian B P` unfolds to `IsBrownianReal (fun t ω => 2 * B t ω) P`, which is `C`
itself after the algebraic identity `2 * (C t ω / 2) = C t ω`. -/
theorem exists_isQuarterBrownian_cont :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → ℝ), (∀ t, @Measurable Ω ℝ mΩ _ (B t)) ∧ @IsQuarterBrownian Ω mΩ B P ∧
      ∀ ω, Continuous fun t => B t ω := by
  obtain ⟨Ω, mΩ, P, C, hCm, hC, hCcont⟩ := LatticeProb.exists_isBrownianReal_cont
  refine ⟨Ω, mΩ, P, fun t ω => C t ω / 2, fun t => (hCm t).div_const 2, ?_,
    fun ω => (hCcont ω).div_const 2⟩
  have heq : (fun t ω => 2 * (C t ω / 2)) = C := by funext t ω; ring
  show IsBrownianReal (fun t ω => 2 * (C t ω / 2)) P
  rw [heq]
  exact hC

section LinearCombination

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The quarter-Brownian motion is a Gaussian process.** -/
theorem isGaussianProcess_quarterBrownian (hB : IsQuarterBrownian B P) :
    IsGaussianProcess B P := by
  have hC : IsBrownianReal (fun t ω => 2 * B t ω) P := hB
  have hCgp := hC.toIsPreBrownianReal.isGaussianProcess
  have heq : (fun t ω => (1 / 2 : ℝ) • (fun t ω => 2 * B t ω) t ω) = B := by
    funext t ω
    show (1 / 2 : ℝ) * (2 * B t ω) = B t ω
    ring
  rw [← heq]
  exact hCgp.smul (fun _ => 1 / 2)

/-- **The quarter-Brownian motion is centred.** -/
theorem integral_quarterBrownian_eval (hB : IsQuarterBrownian B P) (t : ℝ≥0) :
    ∫ ω, B t ω ∂P = 0 := by
  have hC : IsBrownianReal (fun t ω => 2 * B t ω) P := hB
  have h := hC.toIsPreBrownianReal.integral_eval t
  have hrw : ∫ ω, (fun t ω => 2 * B t ω) t ω ∂P = 2 * ∫ ω, B t ω ∂P := by
    show ∫ ω, 2 * B t ω ∂P = 2 * ∫ ω, B t ω ∂P
    rw [integral_const_mul]
  rw [hrw] at h
  linarith

/-- **Each value of the quarter-Brownian motion is integrable.** -/
theorem integrable_quarterBrownian_eval (hB : IsQuarterBrownian B P) (t : ℝ≥0) :
    Integrable (B t) P := by
  have hC : IsBrownianReal (fun t ω => 2 * B t ω) P := hB
  have h := hC.toIsPreBrownianReal.integrable_eval t
  have h2 : Integrable (fun ω => (2 * B t ω) / 2) P := h.div_const 2
  have heq2 : (fun ω => (2 * B t ω) / 2) = B t := by funext ω; ring
  rwa [heq2] at h2

/-- **The covariance of the quarter-Brownian motion is `min s t / 4`.** -/
theorem covariance_quarterBrownian_eval (hB : IsQuarterBrownian B P) (s t : ℝ≥0) :
    cov[B s, B t; P] = (min s t : ℝ) / 4 := by
  have hC : IsBrownianReal (fun t ω => 2 * B t ω) P := hB
  have h := hC.toIsPreBrownianReal.covariance_eval s t
  have hrw : cov[(fun t ω => 2 * B t ω) s, (fun t ω => 2 * B t ω) t; P]
      = 4 * cov[B s, B t; P] := by
    show cov[fun ω => 2 * B s ω, fun ω => 2 * B t ω; P] = 4 * cov[B s, B t; P]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring
  rw [hrw, NNReal.coe_min] at h
  linarith

/-- **Any finite weighted combination of the quarter-Brownian motion at finitely many times is
a genuine real Gaussian random variable.** -/
theorem hasGaussianLaw_sum_quarterBrownian (hB : IsQuarterBrownian B P) {m : ℕ}
    (ts : Fin m → ℝ≥0) (t : Fin m → ℝ) :
    HasGaussianLaw (fun ω => ∑ k, t k * B (ts k) ω) P := by
  have hgp := isGaussianProcess_quarterBrownian hB
  have h1 : IsGaussianProcess (B ∘ ts) P := hgp.comp_right ts
  have h2 : IsGaussianProcess (fun k ω => t k • (B ∘ ts) k ω) P := h1.smul t
  have h3 := h2.hasGaussianLaw_fun_sum (I := (Finset.univ : Finset (Fin m)))
  have heq : (fun ω => ∑ k ∈ (Finset.univ : Finset (Fin m)), t k • (B ∘ ts) k ω)
      = fun ω => ∑ k, t k * B (ts k) ω := by
    funext ω
    exact Finset.sum_congr rfl fun k _ => by simp [smul_eq_mul, Function.comp_apply]
  rwa [heq] at h3

/-- **The mean of a finite weighted combination of the quarter-Brownian motion is zero.** -/
theorem integral_sum_quarterBrownian (hB : IsQuarterBrownian B P) {m : ℕ}
    (ts : Fin m → ℝ≥0) (t : Fin m → ℝ) :
    ∫ ω, (∑ k, t k * B (ts k) ω) ∂P = 0 := by
  have hint : ∀ k : Fin m, Integrable (fun ω => t k * B (ts k) ω) P :=
    fun k => (integrable_quarterBrownian_eval hB (ts k)).const_mul (t k)
  rw [integral_finsetSum Finset.univ (fun k _ => hint k)]
  have hz : ∀ k : Fin m, ∫ ω, t k * B (ts k) ω ∂P = 0 := fun k => by
    rw [integral_const_mul, integral_quarterBrownian_eval hB (ts k), mul_zero]
  simp [hz]

/-- **The variance of a finite weighted combination of the quarter-Brownian motion matches,
the quadratic form with entries `min(s,t)/4`.** -/
theorem variance_sum_quarterBrownian (hB : IsQuarterBrownian B P) {m : ℕ}
    (ts : Fin m → ℝ≥0) (t : Fin m → ℝ) :
    Var[fun ω => ∑ k, t k * B (ts k) ω; P]
      = (∑ i, ∑ l, t i * t l * (min (ts i) (ts l) : ℝ)) / 4 := by
  have hgp := isGaussianProcess_quarterBrownian hB
  haveI : IsProbabilityMeasure P := hgp.isProbabilityMeasure
  have hmem : ∀ k : Fin m, MemLp (fun ω => t k * B (ts k) ω) 2 P := fun k =>
    (hgp.hasGaussianLaw_eval (ts k)).memLp_two.const_mul (t k)
  have hmemsum : MemLp (fun ω => ∑ k, t k * B (ts k) ω) 2 P := memLp_finsetSum Finset.univ
    fun k _ => hmem k
  rw [← covariance_self hmemsum.aemeasurable, covariance_fun_sum_fun_sum hmem hmem]
  have hterm : ∀ i l : Fin m,
      cov[fun ω => t i * B (ts i) ω, fun ω => t l * B (ts l) ω; P]
        = t i * t l * (min (ts i) (ts l) : ℝ) / 4 := by
    intro i l
    rw [covariance_const_mul_left, covariance_const_mul_right, covariance_quarterBrownian_eval hB]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun l _ => hterm i l)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]

/-- **The finite-dimensional characteristic function of any weighted combination of the
quarter-Brownian motion**. -/
theorem charFun_quarterBrownian_linearCombination (hB : IsQuarterBrownian B P) {m : ℕ}
    (ts : Fin m → ℝ≥0) (t : Fin m → ℝ) :
    charFun (P.map (fun ω => ∑ k, t k * B (ts k) ω)) (1 : ℝ)
      = Complex.exp (-((∑ i, ∑ l, t i * t l * (min (ts i) (ts l) : ℝ) : ℝ) : ℂ) / 8) := by
  have hgauss := hasGaussianLaw_sum_quarterBrownian hB ts t
  have hmean := integral_sum_quarterBrownian hB ts t
  have hvar := variance_sum_quarterBrownian hB ts t
  have hinner : (fun ω : Ω => (⟪(1 : ℝ), ∑ k, t k * B (ts k) ω⟫ : ℝ))
      = fun ω => ∑ k, t k * B (ts k) ω := by
    funext ω
    rw [RCLike.inner_apply]
    simp
  rw [hgauss.charFun_map_eq]
  have hmean' : (P[fun ω => (⟪(1 : ℝ), ∑ k, t k * B (ts k) ω⟫ : ℝ)] : ℝ) = 0 := by
    rw [hinner]; exact hmean
  have hvar' : Var[fun ω => (⟪(1 : ℝ), ∑ k, t k * B (ts k) ω⟫ : ℝ); P]
      = (∑ i, ∑ l, t i * t l * (min (ts i) (ts l) : ℝ)) / 4 := by
    rw [hinner]; exact hvar
  rw [hmean', hvar']
  congr 1
  push_cast
  ring

end LinearCombination

end LatticeProb.ContinuumStopping

end
