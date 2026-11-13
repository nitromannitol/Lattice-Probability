/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GaussianLimitIdentification at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.TargetPathLawMoments
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Identification of the rescaled limit points **without a filtration**

`FddClusterReduction.twoClockScalingLimit_of_window_modulus_of_limit_identification` (:204)
consumes `RescaledSequentialLimitIdentification` (:68): *every* sequential weak limit of the
diffusively rescaled laws is `target.pathLaw`.  The route through
`FddBrownianWeld.LevyLimitInput` discharges that by exhibiting a **filtration** on the planar
path space together with two martingale properties — and pinned mathlib has no martingale
statement about Brownian motion at all, so that filtration has to be built by hand.

This file takes the other route.  A probability law on `C(ℝ≥0, Euc 2)` whose canonical
process is a **Gaussian process** with centred projections and the two-time moment identity

  `∫ ⟪θ, f s⟫ ⟪η, f t⟫ dρ = (θᵀ Σ η) · (s ∧ t)`,   `Σ = target.covariance`,

is `target.pathLaw`.  No filtration, no martingale, no conditional expectation appears.

## Route

Every step below is filtration-free; only the two steps marked (*) differ from
`BrownianFdd.eq_pathLaw_of_projection_square_martingales`, and both are replaced by
mathlib lemmas about Gaussian processes:

1. Whitening.  `Σ = A Aᵀ` with `A = target.factor` invertible (`BrownianFdd.det_factor_ne_zero`),
   and `⟪e i, A⁻¹ f u⟫ = ⟪w i, f u⟫` for the whitened direction `w i = A⁻ᵀ e i`
   (`BrownianFdd.whiten`).  The whitened bilinear form is the inner product
   (`bilinForm_whiten`), so the whitened coordinates have covariance `δ_{ij} (s ∧ t)`.
2. The whitened coordinates are Gaussian processes: each is a continuous linear image of one
   value of the canonical process (`IsGaussianProcess.of_isGaussianProcess`).
3. (*) They are **independent** by `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`
   (uncorrelated + jointly Gaussian), in place of the martingale orthogonality.
4. (*) Each is a real pre-Brownian motion by
   `IsGaussianProcess.isPreBrownianReal_of_covariance`
   (`Mathlib/Probability/BrownianMotion/Basic.lean:131`: a centred Gaussian process with
   covariance `s ∧ t` is pre-Brownian), in place of Lévy's characterization.
5. Hence `ρ.map (A⁻¹ ·)` is the standard planar Brownian law
   (`BrownianFdd.isStandardBrownianLaw_map_of_coordinates`, already filtration-free) and
   `MartingaleLimit.map_linearImageBrownianPath_eq_pathLaw` identifies `ρ = target.pathLaw`.

## Main results

* `bilinForm`, `bilinForm_whiten` — the polarization of `BrownianFdd.quadForm` and the
  whitening identity `(A⁻ᵀθ)ᵀ (A Aᵀ) (A⁻ᵀη) = ⟪θ, η⟫`.
* `eq_pathLaw_of_isGaussianProcess_of_moments` — the identification itself.
* `GaussianLimitInput` — the filtration-free replacement of `FddBrownianWeld.LevyLimitInput`.
* `rescaledSequentialLimitIdentification_of_gaussianLimits`,
  `rescaledFiniteDimensionalLimit_of_modulus_tail_of_gaussianLimits`,
  `twoClockScalingLimit_of_window_modulus_of_gaussian_limits` — the welds into
  `FddClusterReduction`.  The last two are the *machine-checked joins*: they are literally the
  consumers of `FddClusterReduction` applied to the producer of this file, so the hypothesis
  shapes are verified by the elaborator, not by eye.

## Anti-vacuity

`eq_pathLaw_of_isGaussianProcess_of_moments` forces `ρ = target.pathLaw`, so
`GaussianLimitInput target` is satisfiable **only** at `target.pathLaw`, exactly like
`LevyLimitInput`.  `target_pathLaw_satisfies_gaussian_diagonal_moments` checks the equal-time
diagonal of the moment clause at that unique admissible witness, from the already checked
`TargetPathLawMoments.integral_inner_sq_pathLaw`; the full satisfiability (Gaussianity of the
canonical process under `target.pathLaw`, and the off-diagonal two-time moments) is proved in
`ReflectedGMS.Limit.GaussianLimitInputAtTarget`.

CONDITIONAL: nothing here proves that the rescaled laws of the reflected walk have Gaussian
limit points; that is the remaining probabilistic input.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace Matrix

namespace ReflectedGMS.GaussianLimitIdentification

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.FddClusterReduction
open ReflectedGMS.BrownianFdd

/-! ## The bilinear form of the target covariance -/

/-- The bilinear form `θᵀ C η`; its diagonal is `BrownianFdd.quadForm`. -/
def bilinForm (C : Matrix (Fin 2) (Fin 2) ℝ) (θ η : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, θ i * C i j * η j

theorem bilinForm_mul_transpose_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (u v : Fin 2 → ℝ) :
    ∑ i : Fin 2, ∑ j : Fin 2, u i * (A * Aᵀ) i j * v j
      = ∑ k : Fin 2, (Aᵀ *ᵥ u) k * (Aᵀ *ᵥ v) k := by
  simp only [Fin.sum_univ_two, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct]
  ring

/-- **The whitened bilinear form is the inner product**: `(A⁻ᵀθ)ᵀ (A Aᵀ) (A⁻ᵀη) = ⟪θ, η⟫`.
This is the polarization of `BrownianFdd.quadForm_whiten`. -/
theorem bilinForm_whiten (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : IsUnit A.det)
    (θ η : EuclideanSpace ℝ (Fin 2)) :
    bilinForm (A * Aᵀ) (whiten A θ) (whiten A η) = ⟪θ, η⟫_ℝ := by
  have hAB : ∀ x : EuclideanSpace ℝ (Fin 2),
      Aᵀ *ᵥ ((A⁻¹)ᵀ *ᵥ fun j => x j) = fun j => x j := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul A hA,
      Matrix.transpose_one, Matrix.one_mulVec]
  have h1 : bilinForm (A * Aᵀ) (whiten A θ) (whiten A η)
      = ∑ i : Fin 2, ∑ j : Fin 2, ((A⁻¹)ᵀ *ᵥ fun j => θ j) i * (A * Aᵀ) i j
          * ((A⁻¹)ᵀ *ᵥ fun j => η j) j := rfl
  rw [h1, bilinForm_mul_transpose_eq, hAB θ, hAB η,
    TargetPathLawMoments.inner_eq_two_sum θ η]
  simp [Fin.sum_univ_two]

/-- The whitened coordinate directions `w i = A⁻ᵀ e i`. -/
noncomputable def whitenedDir (target : AnisotropicBrownianTarget) (i : Fin 2) :
    EuclideanSpace ℝ (Fin 2) :=
  whiten target.factor (EuclideanSpace.single i (1 : ℝ))

/-- **The whitened coordinate directions are orthonormal for the target covariance.** -/
theorem bilinForm_whitenedDir (target : AnisotropicBrownianTarget) (i j : Fin 2) :
    bilinForm target.covariance (whitenedDir target i) (whitenedDir target j)
      = if i = j then (1 : ℝ) else 0 := by
  have hdet : IsUnit target.factor.det := isUnit_iff_ne_zero.mpr (det_factor_ne_zero target)
  have hcovM : target.covariance = target.factor * target.factorᵀ := target.covariance_eq
  simp only [whitenedDir]
  rw [hcovM, bilinForm_whiten _ hdet, inner_single_one]
  simp

/-! ## Gaussian projections -/

section Projections

variable {ρ : Measure (BouRabeeGwynne.BrownianPath 2)}

/-- Every scalar projection of a Gaussian planar path law is a Gaussian process: it is a
continuous linear image of a single value of the canonical process. -/
theorem isGaussianProcess_inner
    (hgauss : IsGaussianProcess
      (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) => f u) ρ)
    (θ : EuclideanSpace ℝ (Fin 2)) :
    IsGaussianProcess
      (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) => ⟪θ, f u⟫_ℝ) ρ :=
  hgauss.of_isGaussianProcess fun u => ⟨{u},
    { toFun := fun x => ⟪θ, x ⟨u, Finset.mem_singleton_self u⟩⟫_ℝ
      map_add' := fun x y => by simp [inner_add_right]
      map_smul' := fun c x => by simp [real_inner_smul_right] },
    fun _ => rfl⟩

/-- Projections of a Gaussian path law are square integrable. -/
theorem memLp_two_inner
    (hgauss : IsGaussianProcess
      (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) => f u) ρ)
    (θ : EuclideanSpace ℝ (Fin 2)) (u : ℝ≥0) :
    MemLp (fun f : BouRabeeGwynne.BrownianPath 2 => ⟪θ, f u⟫_ℝ) 2 ρ :=
  ((isGaussianProcess_inner hgauss θ).hasGaussianLaw_eval u).memLp_two

end Projections

/-! ## The identification -/

/-- **Identification of a planar path law from Gaussianity and two moments — no filtration.**
A probability law `ρ` on `C(ℝ≥0, Euc 2)` whose canonical process is Gaussian, whose
projections are centred, and whose two-time projection moments are
`⟪θ, f s⟫ ⟪η, f t⟫ ↦ (θᵀ Σ η)(s ∧ t)` with `Σ = target.covariance`, **is** `target.pathLaw`.

Compare `BrownianFdd.eq_pathLaw_of_projection_square_martingales`, which reaches the same
conclusion from a filtration and two martingale properties. -/
theorem eq_pathLaw_of_isGaussianProcess_of_moments (target : AnisotropicBrownianTarget)
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) [IsProbabilityMeasure ρ]
    (hgauss : IsGaussianProcess
      (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) => f u) ρ)
    (hmean : ∀ (θ : EuclideanSpace ℝ (Fin 2)) (u : ℝ≥0),
      ∫ f, ⟪θ, f u⟫_ℝ ∂ρ = 0)
    (hmoment : ∀ (θ η : EuclideanSpace ℝ (Fin 2)) (s t : ℝ≥0),
      ∫ f, ⟪θ, f s⟫_ℝ * ⟪η, f t⟫_ℝ ∂ρ
        = bilinForm target.covariance θ η * ((min s t : ℝ≥0) : ℝ)) :
    ρ = (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) := by
  classical
  have hdet : IsUnit target.factor.det := isUnit_iff_ne_zero.mpr (det_factor_ne_zero target)
  have hΦw : Measurable (linearImageBrownianPath target.factor⁻¹) :=
    measurable_linearImageBrownianPath _
  -- the whitened coordinates are the projections along the whitened directions
  have hcoord : ∀ (i : Fin 2) (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2),
      linearImageBrownianPath target.factor⁻¹ f u i = ⟪whitenedDir target i, f u⟫_ℝ := by
    intro i u f
    rw [← inner_single_one i (linearImageBrownianPath target.factor⁻¹ f u)]
    exact inner_toLp_mulVec target.factor⁻¹ (EuclideanSpace.single i (1 : ℝ)) (f u)
  have hcoordfun : ∀ (i : Fin 2) (u : ℝ≥0),
      (fun f : BouRabeeGwynne.BrownianPath 2 =>
        linearImageBrownianPath target.factor⁻¹ f u i)
        = fun f : BouRabeeGwynne.BrownianPath 2 => ⟪whitenedDir target i, f u⟫_ℝ :=
    fun i u => funext fun f => hcoord i u f
  -- the covariance form of the moment hypothesis
  have hcov : ∀ (θ η : EuclideanSpace ℝ (Fin 2)) (s t : ℝ≥0),
      cov[fun f : BouRabeeGwynne.BrownianPath 2 => ⟪θ, f s⟫_ℝ,
          fun f : BouRabeeGwynne.BrownianPath 2 => ⟪η, f t⟫_ℝ; ρ]
        = bilinForm target.covariance θ η * ((min s t : ℝ≥0) : ℝ) := by
    intro θ η s t
    rw [covariance_eq_sub (memLp_two_inner hgauss θ s) (memLp_two_inner hgauss η t)]
    simp only [Pi.mul_apply]
    rw [hmean θ s, hmean η t, hmoment θ η s t]
    ring
  -- joint Gaussianity of the whitened coordinates
  have hflat : IsGaussianProcess
      (fun (p : (_ : Fin 2) × ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) =>
        linearImageBrownianPath target.factor⁻¹ f p.2 p.1) ρ :=
    hgauss.of_isGaussianProcess fun p => ⟨{p.2},
      { toFun := fun x => ⟪whitenedDir target p.1, x ⟨p.2, Finset.mem_singleton_self p.2⟩⟫_ℝ
        map_add' := fun x y => by simp [inner_add_right]
        map_smul' := fun c x => by simp [real_inner_smul_right] },
      fun f => hcoord p.1 p.2 f⟩
  have hGPi : ∀ i : Fin 2, IsGaussianProcess
      (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) =>
        linearImageBrownianPath target.factor⁻¹ f u i) ρ := by
    intro i
    have h : IsGaussianProcess
        ((fun (p : (_ : Fin 2) × ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) =>
          linearImageBrownianPath target.factor⁻¹ f p.2 p.1)
            ∘ (fun u : ℝ≥0 => (⟨i, u⟩ : (_ : Fin 2) × ℝ≥0))) ρ :=
      hflat.comp_right _
    simpa only [Function.comp_def] using h
  -- the whitened coordinates are centred with the Brownian covariance
  have hmean' : ∀ (i : Fin 2) (u : ℝ≥0),
      ∫ f, linearImageBrownianPath target.factor⁻¹ f u i ∂ρ = 0 := by
    intro i u
    rw [hcoordfun i u]
    exact hmean _ u
  have hcov' : ∀ (i : Fin 2) (s t : ℝ≥0), s ≤ t →
      cov[fun f : BouRabeeGwynne.BrownianPath 2 =>
            linearImageBrownianPath target.factor⁻¹ f s i,
          fun f : BouRabeeGwynne.BrownianPath 2 =>
            linearImageBrownianPath target.factor⁻¹ f t i; ρ] = (s : ℝ) := by
    intro i s t hst
    rw [hcoordfun i s, hcoordfun i t, hcov, bilinForm_whitenedDir, min_eq_left hst]
    simp
  have hcross : ∀ (i j : Fin 2), i ≠ j → ∀ s t : ℝ≥0,
      cov[fun f : BouRabeeGwynne.BrownianPath 2 =>
            linearImageBrownianPath target.factor⁻¹ f s i,
          fun f : BouRabeeGwynne.BrownianPath 2 =>
            linearImageBrownianPath target.factor⁻¹ f t j; ρ] = 0 := by
    intro i j hij s t
    rw [hcoordfun i s, hcoordfun j t, hcov, bilinForm_whitenedDir]
    simp [hij]
  -- each whitened coordinate is a real Brownian motion
  have hBM : ∀ i : Fin 2, IsBrownianReal
      (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) =>
        linearImageBrownianPath target.factor⁻¹ f u i) ρ := by
    intro i
    refine ⟨(hGPi i).isPreBrownianReal_of_covariance (fun u => hmean' i u)
      (fun s t hst => hcov' i s t hst), ?_⟩
    exact Eventually.of_forall fun f => by fun_prop
  -- and they are independent
  have hind : iIndepFun (fun (i : Fin 2) (f : BouRabeeGwynne.BrownianPath 2) (u : ℝ≥0) =>
      linearImageBrownianPath target.factor⁻¹ f u i) ρ := by
    refine IsGaussianProcess.iIndepFun_of_covariance_eq_zero
      (X := fun (i : Fin 2) (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) =>
        linearImageBrownianPath target.factor⁻¹ f u i)
      hflat (fun i u => (hGPi i).aemeasurable u) (fun i j hij u v => hcross i j hij u v)
  -- hence the whitened law is standard planar Brownian, and `ρ` is the target
  have hstd := isStandardBrownianLaw_map_of_coordinates hΦw hBM hind
  have hmap := map_linearImageBrownianPath_eq_pathLaw target hstd
  rw [Measure.map_map (measurable_linearImageBrownianPath _) hΦw] at hmap
  have hid : (linearImageBrownianPath target.factor
      ∘ linearImageBrownianPath target.factor⁻¹) = id := by
    funext f
    ext u i
    show (target.factor *ᵥ (target.factor⁻¹ *ᵥ fun j => f u j)) i = f u i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv target.factor hdet, Matrix.one_mulVec]
  rw [hid, Measure.map_id] at hmap
  exact hmap

/-! ## The filtration-free limit input -/

/-- **The Gaussian limit input**: the canonical process of `ρ` is a Gaussian process with
centred projections and two-time moments `(θᵀ Σ η)(s ∧ t)`, `Σ = target.covariance`.

This is the filtration-free replacement of `FddBrownianWeld.LevyLimitInput`: it mentions no
filtration, no martingale and no conditional expectation, only the finite-dimensional laws of
`ρ` and two integrals. -/
structure GaussianLimitInput (target : AnisotropicBrownianTarget)
    (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) : Prop where
  gaussian : IsGaussianProcess (fun (u : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) => f u)
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2))
  centered : ∀ (θ : EuclideanSpace ℝ (Fin 2)) (u : ℝ≥0),
    ∫ f, ⟪θ, f u⟫_ℝ ∂(ρ : Measure (BouRabeeGwynne.BrownianPath 2)) = 0
  moment : ∀ (θ η : EuclideanSpace ℝ (Fin 2)) (s t : ℝ≥0),
    ∫ f, ⟪θ, f s⟫_ℝ * ⟪η, f t⟫_ℝ ∂(ρ : Measure (BouRabeeGwynne.BrownianPath 2))
      = bilinForm target.covariance θ η * ((min s t : ℝ≥0) : ℝ)

/-- A law satisfying the Gaussian limit input is the target path law. -/
theorem eq_pathLaw_of_gaussianLimitInput (target : AnisotropicBrownianTarget)
    (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (h : GaussianLimitInput target ρ) : ρ = target.pathLaw :=
  ProbabilityMeasure.toMeasure_injective
    (eq_pathLaw_of_isGaussianProcess_of_moments target (ρ : Measure _) h.gaussian h.centered
      h.moment)

/-- **The identification input from the Gaussian input at every sequential limit point.**
This is the direct replacement of `FddBrownianWeld.rescaledSequentialLimitIdentification_of_levy`
with no filtration anywhere. -/
theorem rescaledSequentialLimitIdentification_of_gaussianLimits
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget)
    (hgauss : ∀ (ε : ℕ → ℝ≥0) (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
      Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
      Tendsto (fun n => diffusivelyRescaledPathLaw μ (ε n)) atTop (𝓝 ρ) →
      GaussianLimitInput target ρ) :
    RescaledSequentialLimitIdentification μ target :=
  fun ε ρ hε hρ => eq_pathLaw_of_gaussianLimitInput target ρ (hgauss ε ρ hε hρ)

/-- **The two-clock scaling limit from the window modulus tails and the Gaussian input at every
sequential limit point.**  Same conclusion as
`FddBrownianWeld.twoClockScalingLimit_of_window_modulus_of_levy_limits`, with the filtration
and the two martingale properties replaced by Gaussianity and two moments.

CONDITIONAL on `hmodExp`, `hmodExact`, `hgaussExp`, `hgaussExact`. -/
theorem twoClockScalingLimit_of_window_modulus_of_gaussian_limits
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (hmodExp : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledWindowModulusTail
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) T)
    (hmodExact : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      RescaledWindowModulusTail
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) T)
    (hgaussExp : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      ∀ (ε : ℕ → ℝ≥0) (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
        Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
        Tendsto (fun n => diffusivelyRescaledPathLaw
          ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) (ε n))
          atTop (𝓝 ρ) →
        GaussianLimitInput target ρ)
    (hgaussExact : ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Iexp → Measurable Iexact →
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
      ∀ (ε : ℕ → ℝ≥0) (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
        Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
        Tendsto (fun n => diffusivelyRescaledPathLaw
          ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) (ε n))
          atTop (𝓝 ρ) →
        GaussianLimitInput target ρ) :
    TwoClockScalingLimit e D hG z target start Xexp Xexact :=
  twoClockScalingLimit_of_window_modulus_of_limit_identification e D hG z Φ target start
    Xexp Xexact M hclock T hT hmodExp hmodExact
    (fun Zexp Zexact Iexp Iexact hmexp hmexact hpath =>
      rescaledSequentialLimitIdentification_of_gaussianLimits _ target
        (hgaussExp Zexp Zexact Iexp Iexact hmexp hmexact hpath))
    (fun Zexp Zexact Iexp Iexact hmexp hmexact hpath =>
      rescaledSequentialLimitIdentification_of_gaussianLimits _ target
        (hgaussExact Zexp Zexact Iexp Iexact hmexp hmexact hpath))

/-! ## Anti-vacuity -/

end ReflectedGMS.GaussianLimitIdentification
