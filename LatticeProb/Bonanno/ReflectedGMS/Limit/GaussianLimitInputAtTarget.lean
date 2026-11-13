/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GaussianLimitInputAtTarget at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GaussianLimitIdentification

/-!
# The Gaussian limit input is satisfied by the target path law

`GaussianLimitIdentification.eq_pathLaw_of_gaussianLimitInput` shows that
`GaussianLimitInput target ρ` forces `ρ = target.pathLaw`, so the input is satisfiable at
**one law only**.  A hypothesis whose unique admissible witness does not satisfy it is
vacuous — the failure mode already found three times in this project.  This file runs the
check to the end and it **passes**: `gaussianLimitInput_pathLaw` proves

  `GaussianLimitInput target target.pathLaw`

unconditionally, for every `AnisotropicBrownianTarget`, so

  `GaussianLimitInput target ρ ↔ ρ = target.pathLaw`   (`gaussianLimitInput_iff`).

Unlike `TargetPathLawMoments`, which could only check the *necessary conditions* of
`FddBrownianWeld.LevyLimitInput` (its filtration was never built), the Gaussian input is
checked in full: no filtration occurs in it.

## Contents

* `integral_coord_mul_coord_self`, `integral_coord_mul_coord_of_ne` — the two-time coordinate
  moments of a standard planar Brownian law, `E[B_s^i B_t^j] = δ_{ij} (s ∧ t)`.
* `integral_inner_mul_inner` — the two-time projection moment `⟪w, w'⟫ (s ∧ t)`.
* `isGaussianProcess_standard` — the planar canonical process of a standard Brownian law is a
  Gaussian process (independent Gaussian coordinates are jointly Gaussian,
  `iIndepFun.hasGaussianLaw`).
* `isGaussianProcess_pathLaw`, `integral_inner_mul_inner_pathLaw` — the same two facts for the
  linear image `target.pathLaw`.
* `gaussianLimitInput_pathLaw`, `gaussianLimitInput_iff` — the satisfiability check.

Nothing here is conditional: every statement is proved from `target.isStandard` alone, and
`AnisotropicBrownianTarget` is unconditionally inhabited with any prescribed symmetric
positive definite covariance by
`InvarianceAssembly.exists_anisotropicBrownianTarget_of_symmetricPositiveDefinite`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace Matrix

namespace ReflectedGMS.GaussianLimitInputAtTarget

open ReflectedGMS.StatementIngredients ReflectedGMS.BrownianFdd
open ReflectedGMS.MartingaleLimit ReflectedGMS.GaussianLimitIdentification

/-! ### Two-time moments of a standard planar Brownian law -/

section StandardLaw

variable {σ : Measure (BouRabeeGwynne.BrownianPath 2)}

/-- **The two-time second moment of one coordinate is `s ∧ t`.** -/
theorem integral_coord_mul_coord_self (hσ : BouRabeeGwynne.IsStandardBrownianLaw σ)
    (i : Fin 2) (s t : ℝ≥0) :
    ∫ ω, ω s i * ω t i ∂σ = ((min s t : ℝ≥0) : ℝ) := by
  have : IsProbabilityMeasure σ := hσ.1
  have hms := TargetPathLawMoments.memLp_two_coord hσ i s
  have hmt := TargetPathLawMoments.memLp_two_coord hσ i t
  have hcov : cov[fun ω : BouRabeeGwynne.BrownianPath 2 => ω s i,
      fun ω : BouRabeeGwynne.BrownianPath 2 => ω t i; σ] = ((min s t : ℝ≥0) : ℝ) := by
    have h := (hσ.2.1 i).toIsPreBrownianReal.covariance_eval s t
    simpa using h
  rw [covariance_eq_sub hms hmt] at hcov
  simp only [Pi.mul_apply, TargetPathLawMoments.integral_coord_eq_zero hσ i s,
    TargetPathLawMoments.integral_coord_eq_zero hσ i t, mul_zero, sub_zero] at hcov
  exact hcov

/-- **Distinct coordinates are uncorrelated at all pairs of times.** -/
theorem integral_coord_mul_coord_of_ne (hσ : BouRabeeGwynne.IsStandardBrownianLaw σ)
    {i j : Fin 2} (hij : i ≠ j) (s t : ℝ≥0) : ∫ ω, ω s i * ω t j ∂σ = 0 := by
  have : IsProbabilityMeasure σ := hσ.1
  have hms := TargetPathLawMoments.memLp_two_coord hσ i s
  have hmt := TargetPathLawMoments.memLp_two_coord hσ j t
  have hind : IndepFun (fun ω : BouRabeeGwynne.BrownianPath 2 => ω s i)
      (fun ω : BouRabeeGwynne.BrownianPath 2 => ω t j) σ :=
    (hσ.2.2.indepFun hij).comp (measurable_pi_apply s) (measurable_pi_apply t)
  have hcov := hind.covariance_eq_zero hms hmt
  rw [covariance_eq_sub hms hmt] at hcov
  simp only [Pi.mul_apply, TargetPathLawMoments.integral_coord_eq_zero hσ i s,
    TargetPathLawMoments.integral_coord_eq_zero hσ j t, mul_zero, sub_zero] at hcov
  exact hcov

/-- **The two-time projection moment of a standard planar Brownian law.** -/
theorem integral_inner_mul_inner (hσ : BouRabeeGwynne.IsStandardBrownianLaw σ)
    (w w' : EuclideanSpace ℝ (Fin 2)) (s t : ℝ≥0) :
    ∫ ω, ⟪w, ω s⟫_ℝ * ⟪w', ω t⟫_ℝ ∂σ = ⟪w, w'⟫_ℝ * ((min s t : ℝ≥0) : ℝ) := by
  have : IsProbabilityMeasure σ := hσ.1
  have hm : ∀ (i : Fin 2) (u : ℝ≥0),
      MemLp (fun ω : BouRabeeGwynne.BrownianPath 2 => ω u i) 2 σ :=
    fun i u => TargetPathLawMoments.memLp_two_coord hσ i u
  have hi : ∀ (i j : Fin 2) (c : ℝ), Integrable
      (fun ω : BouRabeeGwynne.BrownianPath 2 => c * (ω s i * ω t j)) σ :=
    fun i j c => (((hm i s).integrable_mul (hm j t))).const_mul c
  have hfun : (fun ω : BouRabeeGwynne.BrownianPath 2 => ⟪w, ω s⟫_ℝ * ⟪w', ω t⟫_ℝ)
      = fun ω : BouRabeeGwynne.BrownianPath 2 =>
          w 0 * w' 0 * (ω s 0 * ω t 0)
            + (w 0 * w' 1 * (ω s 0 * ω t 1)
              + (w 1 * w' 0 * (ω s 1 * ω t 0) + w 1 * w' 1 * (ω s 1 * ω t 1))) := by
    funext ω
    rw [TargetPathLawMoments.inner_eq_two_sum w (ω s),
      TargetPathLawMoments.inner_eq_two_sum w' (ω t)]
    ring
  have hA : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      w 0 * w' 0 * (ω s 0 * ω t 0)) σ := hi 0 0 _
  have hB : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      w 0 * w' 1 * (ω s 0 * ω t 1)) σ := hi 0 1 _
  have hC : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      w 1 * w' 0 * (ω s 1 * ω t 0)) σ := hi 1 0 _
  have hD : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      w 1 * w' 1 * (ω s 1 * ω t 1)) σ := hi 1 1 _
  have hCD : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      w 1 * w' 0 * (ω s 1 * ω t 0) + w 1 * w' 1 * (ω s 1 * ω t 1)) σ := hC.add hD
  have hBCD : Integrable (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      w 0 * w' 1 * (ω s 0 * ω t 1)
        + (w 1 * w' 0 * (ω s 1 * ω t 0) + w 1 * w' 1 * (ω s 1 * ω t 1))) σ := hB.add hCD
  rw [hfun, integral_add hA hBCD, integral_add hB hCD, integral_add hC hD,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_coord_mul_coord_self hσ 0 s t, integral_coord_mul_coord_self hσ 1 s t,
    integral_coord_mul_coord_of_ne hσ (show (0 : Fin 2) ≠ 1 by decide) s t,
    integral_coord_mul_coord_of_ne hσ (show (1 : Fin 2) ≠ 0 by decide) s t,
    TargetPathLawMoments.inner_eq_two_sum w w']
  ring

/-- **The planar canonical process of a standard Brownian law is a Gaussian process.**  The
two coordinate processes are independent (`IsStandardBrownianLaw`) pre-Brownian motions, hence
jointly Gaussian by `iIndepFun.hasGaussianLaw`, and the planar value at a time is the
continuous linear image of its two coordinates. -/
theorem isGaussianProcess_standard (hσ : BouRabeeGwynne.IsStandardBrownianLaw σ) :
    IsGaussianProcess
      (fun (u : ℝ≥0) (ω : BouRabeeGwynne.BrownianPath 2) => ω u) σ := by
  constructor
  intro I
  have hindI : iIndepFun (fun (i : Fin 2) (ω : BouRabeeGwynne.BrownianPath 2) =>
      I.restrict (fun u => ω u i)) σ :=
    hσ.2.2.comp (fun _ : Fin 2 => I.restrict) (fun _ => I.measurable_restrict)
  have hgi : ∀ i : Fin 2, HasGaussianLaw
      (fun ω : BouRabeeGwynne.BrownianPath 2 => I.restrict (fun u => ω u i)) σ :=
    fun i => (hσ.2.1 i).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw I
  have hjoint := iIndepFun.hasGaussianLaw hgi hindI
  let L : ((_ : Fin 2) → (I → ℝ)) →L[ℝ] (I → BouRabeeGwynne.Euc 2) :=
    { toFun := fun x u => (WithLp.toLp 2 (fun i => x i u) : BouRabeeGwynne.Euc 2)
      map_add' := fun x y => by
        funext u
        ext i
        simp only [Pi.add_apply, PiLp.add_apply]
      map_smul' := fun c x => by
        funext u
        ext i
        simp only [Pi.smul_apply, PiLp.smul_apply, RingHom.id_apply, smul_eq_mul] }
  have heq : (fun ω : BouRabeeGwynne.BrownianPath 2 => I.restrict (fun u => ω u))
      = L ∘ (fun ω : BouRabeeGwynne.BrownianPath 2 =>
          fun i : Fin 2 => I.restrict (fun u => ω u i)) := by
    funext ω
    funext u
    ext i
    rfl
  show HasGaussianLaw (fun ω : BouRabeeGwynne.BrownianPath 2 => I.restrict (fun u => ω u)) σ
  rw [heq]
  exact hjoint.map L

end StandardLaw

/-! ### The same two facts at the target path law -/

section Target

/-- The whitening-free transpose identity: `⟪Aᵀθ, Aᵀη⟫ = θᵀ (A Aᵀ) η`. -/
theorem inner_transposeDir (A : Matrix (Fin 2) (Fin 2) ℝ)
    (θ η : EuclideanSpace ℝ (Fin 2)) :
    ⟪TargetPathLawMoments.transposeDir A θ, TargetPathLawMoments.transposeDir A η⟫_ℝ
      = bilinForm (A * Aᵀ) θ η := by
  have h : bilinForm (A * Aᵀ) θ η
      = ∑ k : Fin 2, (Aᵀ *ᵥ fun j => θ j) k * (Aᵀ *ᵥ fun j => η j) k :=
    bilinForm_mul_transpose_eq A (fun j => θ j) (fun j => η j)
  rw [TargetPathLawMoments.inner_eq_two_sum, h, Fin.sum_univ_two]
  rfl

theorem bilinForm_covariance_eq (target : AnisotropicBrownianTarget)
    (θ η : EuclideanSpace ℝ (Fin 2)) :
    bilinForm target.covariance θ η
      = ⟪TargetPathLawMoments.transposeDir target.factor θ,
          TargetPathLawMoments.transposeDir target.factor η⟫_ℝ := by
  have hcovM : target.covariance = target.factor * target.factorᵀ := target.covariance_eq
  rw [hcovM, inner_transposeDir]

/-- **The two-time projection moment of the target path law is `(θᵀ Σ η)(s ∧ t)`** — exactly
the `moment` clause of `GaussianLimitInput`. -/
theorem integral_inner_mul_inner_pathLaw (target : AnisotropicBrownianTarget)
    (θ η : EuclideanSpace ℝ (Fin 2)) (s t : ℝ≥0) :
    ∫ f, ⟪θ, f s⟫_ℝ * ⟪η, f t⟫_ℝ
        ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
      = bilinForm target.covariance θ η * ((min s t : ℝ≥0) : ℝ) := by
  have hmeas : Measurable (linearImageBrownianPath target.factor) :=
    measurable_linearImageBrownianPath _
  rw [TargetPathLawMoments.coe_pathLaw_eq_map target]
  have hasm : AEStronglyMeasurable
      (fun f : BouRabeeGwynne.BrownianPath 2 => ⟪θ, f s⟫_ℝ * ⟪η, f t⟫_ℝ)
      ((target.standardLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
        (linearImageBrownianPath target.factor)) :=
    ((TargetPathLawMoments.measurable_inner_eval θ s).mul
      (TargetPathLawMoments.measurable_inner_eval η t)).aestronglyMeasurable
  rw [integral_map hmeas.aemeasurable hasm]
  have hfun : (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      ⟪θ, linearImageBrownianPath target.factor ω s⟫_ℝ
        * ⟪η, linearImageBrownianPath target.factor ω t⟫_ℝ)
      = fun ω : BouRabeeGwynne.BrownianPath 2 =>
          ⟪TargetPathLawMoments.transposeDir target.factor θ, ω s⟫_ℝ
            * ⟪TargetPathLawMoments.transposeDir target.factor η, ω t⟫_ℝ := by
    funext ω
    rw [TargetPathLawMoments.inner_linearImage, TargetPathLawMoments.inner_linearImage]
  rw [hfun, integral_inner_mul_inner target.isStandard, bilinForm_covariance_eq]

/-- **The canonical process of the target path law is a Gaussian process.** -/
theorem isGaussianProcess_pathLaw (target : AnisotropicBrownianTarget) :
    IsGaussianProcess (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) => f u)
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) := by
  have hmeas : Measurable (linearImageBrownianPath target.factor) :=
    measurable_linearImageBrownianPath _
  have hstd := isGaussianProcess_standard target.isStandard
  -- the matrix action as a continuous linear map on the plane
  let Amat : BouRabeeGwynne.Euc 2 →L[ℝ] BouRabeeGwynne.Euc 2 :=
    { toFun := fun x => (WithLp.toLp 2 (target.factor *ᵥ fun j => x j) : BouRabeeGwynne.Euc 2)
      map_add' := fun x y => by
        ext i
        simp only [PiLp.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      map_smul' := fun c x => by
        ext i
        simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul, Matrix.mulVec,
          dotProduct, Fin.sum_univ_two]
        ring }
  have hmapped : IsGaussianProcess
      (fun (u : ℝ≥0) (ω : BouRabeeGwynne.BrownianPath 2) => Amat (ω u))
      (target.standardLaw : Measure (BouRabeeGwynne.BrownianPath 2)) :=
    hstd.comp_left fun _ => Amat
  constructor
  intro I
  have hres : Measurable
      (fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (fun u => f u)) :=
    Measurable.of_eval fun u => ContinuousMap.measurable_eval (u : ℝ≥0)
  have heq : ((fun f : BouRabeeGwynne.BrownianPath 2 => I.restrict (fun u => f u))
      ∘ linearImageBrownianPath target.factor)
      = fun ω : BouRabeeGwynne.BrownianPath 2 => I.restrict (fun u => Amat (ω u)) := by
    funext ω
    funext u
    rfl
  refine { aemeasurable := hres.aemeasurable, isGaussian_map := ?_ }
  rw [TargetPathLawMoments.coe_pathLaw_eq_map target,
    Measure.map_map hres hmeas, heq]
  exact (hmapped.hasGaussianLaw I).isGaussian_map

/-! ### The satisfiability check -/

/-- **ANTI-VACUITY, in full.**  The target path law satisfies the Gaussian limit input.
Together with `eq_pathLaw_of_gaussianLimitInput` — which says nothing else can — the input is
satisfiable, at exactly one law, and the lane it feeds is not vacuous. -/
theorem gaussianLimitInput_pathLaw (target : AnisotropicBrownianTarget) :
    GaussianLimitInput target target.pathLaw where
  gaussian := isGaussianProcess_pathLaw target
  centered := TargetPathLawMoments.integral_inner_eq_zero_pathLaw target
  moment := integral_inner_mul_inner_pathLaw target

end Target

end ReflectedGMS.GaussianLimitInputAtTarget
