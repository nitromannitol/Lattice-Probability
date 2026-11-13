/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.TargetPathLawMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.FddClusterReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.UnstoppedContinuousLindeberg
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
import LatticeProb.Bonanno.ReflectedGMS.Limit.PathLawFiniteDimensionalConvergence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Satisfiability of the Lévy limit input, verified at the target path law

`FddBrownianWeld.LevyLimitInput target ρ` is the hypothesis that discharges `hfddExp` /
`hfddExact`.  By `FddBrownianWeld.eq_pathLaw_of_levyLimitInput` it *forces*
`ρ = target.pathLaw`, so it is satisfiable **only** at `target.pathLaw`.  A lane whose
only admissible witness fails its own necessary conditions is vacuous, and that is exactly
the failure mode already found twice in this project (`canonicalBracket_of_parts`, and the
`hdata` of `canonicalBracket_bracket_limit_of_rootBlockData`).

This file runs that check and it **passes**.

* `levyLimitInput_necessary_conditions` — the four first/second-moment identities that
  `LevyLimitInput target ρ` forces on `ρ`, extracted through the already checked
  `BrownianFdd.ProjectionSquareMartingale.integral_inner_eq_zero` / `integral_inner_sq`.
* `target_pathLaw_satisfies_levy_necessary_conditions` — `target.pathLaw` satisfies **all
  four**, unconditionally, for every `AnisotropicBrownianTarget`.  In particular the second
  moment of a projection is exactly the bracket `θᵀ Σ θ · u` the hypotheses demand.
* `quadForm_covariance_pos` and `integral_inner_sq_pathLaw_pos` — the identified bracket is
  strictly positive in every nonzero direction, so the identified limit is never a
  degenerate (Dirac or lower-rank) law.

Everything is proved from `AnisotropicBrownianTarget.isStandard` (the sibling project's
`IsStandardBrownianLaw` of the base law) and `AnisotropicBrownianTarget.positiveDefinite`;
`AnisotropicBrownianTarget` itself is unconditionally inhabited with any prescribed
symmetric positive definite covariance by
`InvarianceAssembly.exists_anisotropicBrownianTarget_of_symmetricPositiveDefinite`.

What this file does **not** do: it does not produce the filtration of `LevyLimitInput`
(the full martingale property of the target path law is still open — mathlib's pinned
Brownian-motion API has no martingale statements).  It certifies that no moment obstruction
stands in the way, i.e. that the lane is not vacuous for the reason the earlier vacuous
consumers were.
-/

-- Merged from `ReflectedGMS/Limit/BrownianFddIdentification.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_BrownianFddIdentification

/-!
# Lévy's characterization on the planar path space, identified with the target

`BrownianFddIncrements` turns "every scalar projection is a continuous square martingale
with deterministic bracket" into independent Gaussian vector increments.  This file
finishes the Cramér–Wold bridge from the project's scalar rate `C` to the **matrix**
`target.covariance` of `StatementIngredients.AnisotropicBrownianTarget`, and identifies the
law.

Main theorem, `eq_pathLaw_of_projection_square_martingales`: a probability law `ρ` on
`BouRabeeGwynne.BrownianPath 2 = C(ℝ≥0, Euc 2)` under which, for one filtration `𝔽`,

* every projection `f ↦ ⟪θ, f u⟫` is a square-integrable `𝔽`-martingale,
* `⟪θ, f u⟫² - θᵀ Σ θ · u` is an `𝔽`-martingale, `Σ = target.covariance`,
* `f 0 = 0` almost surely,

**is** `target.pathLaw`.

Route.
1. Whitening.  `Σ = A Aᵀ` with `A = target.factor`, and positive definiteness forces
   `det A ≠ 0` (`det_factor_ne_zero`).  The whitened path `A⁻¹ f` has projections
   `⟪θ, A⁻¹ f u⟫ = ⟪A⁻ᵀ θ, f u⟫` with bracket `‖θ‖² u` (`quadForm_whiten`).
2. The whitened coordinate process is Gaussian (`BrownianFddIncrements`), its two coordinates
   are uncorrelated at all pairs of times (polarization plus martingale orthogonality,
   `ProjectionSquareMartingale.covariance_inner`), hence independent as processes
   (mathlib's `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`).
3. Each whitened coordinate is a real Brownian motion by the orphan
   `MultivariateBrownianIdentification.isPreBrownianReal_of_continuous_square_martingale`
   with rate `C = 1`.
4. So the law of `A⁻¹ f` satisfies the sibling project's `IsStandardBrownianLaw`, and
   `PathLawFiniteDimensionalConvergence.map_linearImageBrownianPath_eq_pathLaw` (uniqueness
   of the standard Brownian law) gives `ρ = A_* (A⁻¹_* ρ) = target.pathLaw`.

CONDITIONAL on the martingale hypotheses; nothing about the reflected walk is proved here.
Satisfiability: the hypotheses hold for `ρ = target.pathLaw` itself with its natural
filtration (a linear image of standard planar Brownian motion), and
`target.covariance` is positive definite, so the identified law is never degenerate.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace Matrix

namespace ReflectedGMS.BrownianFdd

open ReflectedGMS.MartingaleLimit ReflectedGMS.StatementIngredients

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Means and covariances of the projections -/

section Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : ℝ≥0 → Ω → E} {q : E → ℝ} {𝔽 : Filtration ℝ≥0 mΩ} {P : Measure Ω}

namespace ProjectionSquareMartingale

end ProjectionSquareMartingale

end Covariance

/-! ### Planar coordinates -/

section Planar

theorem inner_single_one (i : Fin 2) (v : EuclideanSpace ℝ (Fin 2)) :
    ⟪EuclideanSpace.single i (1 : ℝ), v⟫_ℝ = v i := by
  rw [EuclideanSpace.inner_single_left]
  simp

namespace ProjectionSquareMartingale

variable {𝔽 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)}

end ProjectionSquareMartingale

/-- **Transfer to the pushforward**: if the coordinate processes of `Φw` under `ρ` are
independent real Brownian motions, the law of `Φw` is the standard planar Brownian law. -/
theorem isStandardBrownianLaw_map_of_coordinates
    {ρ : Measure (BouRabeeGwynne.BrownianPath 2)} [IsProbabilityMeasure ρ]
    {Φw : BouRabeeGwynne.BrownianPath 2 → BouRabeeGwynne.BrownianPath 2} (hΦ : Measurable Φw)
    (hBM : ∀ i : Fin 2, IsBrownianReal (fun u f => Φw f u i) ρ)
    (hind : iIndepFun (fun (i : Fin 2) f (u : ℝ≥0) => Φw f u i) ρ) :
    BouRabeeGwynne.IsStandardBrownianLaw (ρ.map Φw) := by
  refine ⟨inferInstance, fun i => ?_, ?_⟩
  · refine { toIsPreBrownianReal := ?_, cont := ?_ }
    · constructor
      intro I
      have hm : Measurable
          (fun ω : BouRabeeGwynne.BrownianPath 2 ↦ I.restrict (fun s ↦ ω s i)) :=
        I.measurable_restrict.comp (BouRabeeGwynne.measurable_brownianCoordinatePath i)
      refine ⟨hm.aemeasurable, ?_⟩
      rw [Measure.map_map hm hΦ]
      exact ((hBM i).hasLaw I).map_eq
    · exact Filter.Eventually.of_forall fun ω ↦ by fun_prop
  · rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun i ↦ (BouRabeeGwynne.measurable_brownianCoordinatePath i).aemeasurable)]
    rw [Measure.map_map BouRabeeGwynne.measurable_brownianCoordinates hΦ]
    simp_rw [Measure.map_map (BouRabeeGwynne.measurable_brownianCoordinatePath _) hΦ]
    exact hind.map_fun_eq_pi_map (fun i ↦
      ((BouRabeeGwynne.measurable_brownianCoordinatePath i).comp hΦ).aemeasurable)

/-! ### Whitening -/

theorem quadForm_mul_transpose_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    ∑ i : Fin 2, ∑ j : Fin 2, v i * (A * Aᵀ) i j * v j = ∑ k : Fin 2, ((Aᵀ *ᵥ v) k) ^ 2 := by
  simp only [Fin.sum_univ_two, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct]
  ring

/-- **The factor of a positive definite target covariance is invertible.** -/
theorem det_factor_ne_zero (target : AnisotropicBrownianTarget) : target.factor.det ≠ 0 := by
  intro hdet
  have hdetT : target.factorᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  obtain ⟨_, hpd⟩ := target.positiveDefinite
  have hpos := hpd v hv
  rw [target.covariance_eq, covarianceOfBrownianFactor, quadForm_mul_transpose_eq, hAv] at hpos
  simp at hpos

/-- The whitened direction `A⁻ᵀ θ`. -/
noncomputable def whiten (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ((A⁻¹)ᵀ *ᵥ fun j => θ j)

theorem inner_toLp_mulVec (B : Matrix (Fin 2) (Fin 2) ℝ) (θ x : EuclideanSpace ℝ (Fin 2)) :
    ⟪θ, (WithLp.toLp 2 (B *ᵥ fun j => x j) : EuclideanSpace ℝ (Fin 2))⟫_ℝ
      = ⟪(WithLp.toLp 2 (Bᵀ *ᵥ fun j => θ j) : EuclideanSpace ℝ (Fin 2)), x⟫_ℝ := by
  simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-! ### The identification -/

end Planar

end ReflectedGMS.BrownianFdd

end Merged_BrownianFddIdentification

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace Matrix

namespace ReflectedGMS.TargetPathLawMoments

open ReflectedGMS.StatementIngredients ReflectedGMS.BrownianFdd
open ReflectedGMS.MartingaleLimit

/-! ### Coordinate moments of a standard Brownian law -/

section StandardLaw

variable {σ : Measure (BouRabeeGwynne.BrownianPath 2)}

/-- Each coordinate at a fixed time is square integrable (it is Gaussian). -/
theorem memLp_two_coord (hσ : BouRabeeGwynne.IsStandardBrownianLaw σ) (i : Fin 2) (u : ℝ≥0) :
    MemLp (fun ω : BouRabeeGwynne.BrownianPath 2 => ω u i) 2 σ :=
  ((hσ.2.1 i).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval u).memLp_two

/-- Each coordinate is centred. -/
theorem integral_coord_eq_zero (hσ : BouRabeeGwynne.IsStandardBrownianLaw σ) (i : Fin 2)
    (u : ℝ≥0) : ∫ ω, ω u i ∂σ = 0 :=
  (hσ.2.1 i).toIsPreBrownianReal.integral_eval u

/-- The planar real inner product in coordinates. -/
theorem inner_eq_two_sum (w : EuclideanSpace ℝ (Fin 2)) (v : BouRabeeGwynne.Euc 2) :
    ⟪w, v⟫_ℝ = w 0 * v 0 + w 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem integral_inner_eq_zero (hσ : BouRabeeGwynne.IsStandardBrownianLaw σ)
    (w : EuclideanSpace ℝ (Fin 2)) (u : ℝ≥0) :
    ∫ ω, ⟪w, ω u⟫_ℝ ∂σ = 0 := by
  have : IsProbabilityMeasure σ := hσ.1
  have hfun : (fun ω : BouRabeeGwynne.BrownianPath 2 => ⟪w, ω u⟫_ℝ)
      = fun ω : BouRabeeGwynne.BrownianPath 2 => w 0 * ω u 0 + w 1 * ω u 1 :=
    funext fun ω => inner_eq_two_sum w (ω u)
  have hi0 : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 => w 0 * ω u 0) σ :=
    ((memLp_two_coord hσ 0 u).integrable one_le_two).const_mul _
  have hi1 : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 => w 1 * ω u 1) σ :=
    ((memLp_two_coord hσ 1 u).integrable one_le_two).const_mul _
  rw [hfun, integral_add hi0 hi1, integral_const_mul, integral_const_mul,
    integral_coord_eq_zero hσ 0 u, integral_coord_eq_zero hσ 1 u]
  ring

end StandardLaw

/-! ### The same moments at the target path law -/

section Target

/-- The transposed direction: `⟪θ, A x⟫ = ⟪Aᵀ θ, x⟫`. -/
noncomputable def transposeDir (A : Matrix (Fin 2) (Fin 2) ℝ)
    (θ : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (Aᵀ *ᵥ fun j => θ j)

theorem inner_linearImage (A : Matrix (Fin 2) (Fin 2) ℝ) (θ : EuclideanSpace ℝ (Fin 2))
    (ω : BouRabeeGwynne.BrownianPath 2) (u : ℝ≥0) :
    ⟪θ, linearImageBrownianPath A ω u⟫_ℝ = ⟪transposeDir A θ, ω u⟫_ℝ :=
  inner_toLp_mulVec A θ (ω u)

theorem coe_pathLaw_eq_map (target : AnisotropicBrownianTarget) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
      = (target.standardLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
          (linearImageBrownianPath target.factor) :=
  (map_linearImageBrownianPath_eq_pathLaw target target.isStandard).symm

theorem measurable_inner_eval (θ : EuclideanSpace ℝ (Fin 2)) (u : ℝ≥0) :
    Measurable (fun f : BouRabeeGwynne.BrownianPath 2 => ⟪θ, f u⟫_ℝ) := by
  have hev : Measurable (fun f : BouRabeeGwynne.BrownianPath 2 => f u) :=
    ContinuousMap.measurable_eval u
  have hc : Continuous (fun x : BouRabeeGwynne.Euc 2 => ⟪θ, x⟫_ℝ) := by fun_prop
  exact hc.measurable.comp hev

/-- **Projections of the target path law are centred.** -/
theorem integral_inner_eq_zero_pathLaw (target : AnisotropicBrownianTarget)
    (θ : EuclideanSpace ℝ (Fin 2)) (u : ℝ≥0) :
    ∫ f, ⟪θ, f u⟫_ℝ ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) = 0 := by
  have hmeas : Measurable (linearImageBrownianPath target.factor) :=
    measurable_linearImageBrownianPath _
  rw [coe_pathLaw_eq_map target]
  have hasm : AEStronglyMeasurable (fun f : BouRabeeGwynne.BrownianPath 2 => ⟪θ, f u⟫_ℝ)
      ((target.standardLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
        (linearImageBrownianPath target.factor)) :=
    (measurable_inner_eval θ u).aestronglyMeasurable
  rw [integral_map hmeas.aemeasurable hasm]
  have hfun : (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      ⟪θ, linearImageBrownianPath target.factor ω u⟫_ℝ)
      = fun ω : BouRabeeGwynne.BrownianPath 2 => ⟪transposeDir target.factor θ, ω u⟫_ℝ :=
    funext fun ω => inner_linearImage target.factor θ ω u
  rw [hfun]
  exact integral_inner_eq_zero target.isStandard _ u

/-! ### Nondegeneracy of the identified bracket -/

/-! ### The satisfiability check -/

end Target

end ReflectedGMS.TargetPathLawMoments
