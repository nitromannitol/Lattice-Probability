/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GaussianWeakLimitClosure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GaussianLimitInputAtTarget
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Gaussianity of a weak limit from converging finite-dimensional characteristic functions

`GaussianLimitIdentification.GaussianLimitInput target ρ` asks three things of a candidate
limit law `ρ` on `C(ℝ≥0, Euc 2)`:

1. the canonical process is a Gaussian process (`IsGaussianProcess`);
2. its projections are centred;
3. its two-time projection moments are `(θᵀ Σ η)(s ∧ t)`.

All three speak about an **abstract** weak limit point, which no estimate on the walk can
address directly.  This file removes the limit law from the hypothesis entirely: it shows
that the three clauses follow from the convergence of the **finite-dimensional
characteristic functions of the rescaled laws themselves** to the Gaussian ones —
a statement about the walk's own sample space, which is exactly the output shape of a
Lindeberg / characteristic-function argument (`ConditionalGaussianIdentification`,
`GaussianIdentificationUnlocalization`, `UnstoppedContinuousLindeberg`), where the
filtration already exists.  **No filtration on `C(ℝ≥0, Euc 2)` is used or built here.**

## Route

* `fddCharFun ρ u θ = ∫ f, exp (i ∑ⱼ ⟪θ j, f (u j)⟫) dρ` — the finite-dimensional
  characteristic function of a path law at a finite family of times and directions.
* `tendsto_fddCharFun_of_tendsto` — **Lévy continuity, easy half.**  The integrand is a
  bounded continuous function of the path (`fddCharBcf`), so weak convergence of path laws
  gives convergence of `fddCharFun`.  This needs nothing about the space beyond the weak
  topology on `ProbabilityMeasure`.
* `eq_of_tendsto_charFunDual`, `isGaussian_of_tendsto_charFunDual` — **closedness of
  `IsGaussian` under weak limits**, in its honest minimal form: two limits of the same
  net of characteristic functions coincide (`Measure.ext_of_charFunDual`), so a limit law
  whose characteristic function is a Gaussian one *is* that Gaussian law.  This is the
  lemma that pinned mathlib does not have; `Mathlib/MeasureTheory/Measure/LevyConvergence.lean`
  proves Lévy's theorem but says nothing about Gaussianity of the limit.
* `exists_fddCharFun_eq_charFunDual` — every continuous linear functional on
  `(↥I → Euc 2)` is `x ↦ ∑ᵢ ⟪θ i, x i⟫` (`ContinuousLinearMap.sum_comp_single` and
  `InnerProductSpace.toDual`), so `charFunDual` of a finite-dimensional projection of a
  path law *is* an `fddCharFun`.
* `fddCharFun_of_gaussianLimitInput` — conversely, a law satisfying `GaussianLimitInput`
  has `fddCharFun = exp (-Q/2)` with `Q = gaussQuad` the Gaussian quadratic form.  Applied
  at `target.pathLaw` (where `GaussianLimitInputAtTarget.gaussianLimitInput_pathLaw` holds
  unconditionally) this computes the target's finite-dimensional characteristic function.
* `gaussianLimitInput_of_tendsto_fddCharFun` — the producer.  All three clauses come from
  the single measure identity `ρ.map (restrictPath I) = target.pathLaw.map (restrictPath I)`,
  so clauses 2 and 3 need **no uniform integrability**: the moments are integrals of the
  same function against the same finite-dimensional law.

## Anti-vacuity

`FddClusterReduction`'s note at :80 records that the identification input follows from the
convergence it helps to produce, so at each single limit law it is *equivalent* to the
conclusion; the same is true of `GaussianLimitInput` (`gaussianLimitInput_iff`).  The proofs
here therefore never assume anything conclusion-shaped: **no fdd convergence of measures, no
tightness and no scaling limit is a hypothesis anywhere in this file.**  The hypothesis
`RescaledFddCharFunLimits` is a statement about *oscillatory integrals of the rescaled laws*,
and the honest accounting is recorded as an equivalence:

* `rescaledFddCharFunLimits_of_tendsto` proves the new input is *implied by* the path-law
  convergence, exactly as `FddClusterReduction.rescaledSequentialLimitIdentification_of_tendsto`
  does for the input it replaces — so this is a **reduction, not a discharge**.  What
  improves is what the atom is *about*: the abstract limit law `ρ` disappears, and what is
  left is a characteristic-function limit on the walk's own sample space.
* `gaussQuad_nonneg` and `fddCharFun_pathLaw` check that the target law really does satisfy
  the new input, so it is satisfiable.

CONDITIONAL: nothing here proves that the rescaled laws of the reflected walk have
converging Gaussian characteristic functions; that is the (unchanged) martingale-CLT input.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.GaussianWeakLimit

open ReflectedGMS.StatementIngredients ReflectedGMS.BrownianFdd
open ReflectedGMS.MartingaleLimit ReflectedGMS.GaussianLimitIdentification
open ReflectedGMS.GaussianLimitInputAtTarget
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.FddClusterReduction

/-! ## Closedness of `IsGaussian` under weak limits

The general lemma the project needed and pinned mathlib does not package: a limit of a net of
measures whose characteristic functions converge to a Gaussian characteristic function is that
Gaussian measure.  `Measure.ext_of_charFunDual` supplies the uniqueness; the only content is
that limits in `ℂ` are unique. -/

section Closure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

end Closure

/-! ## Finite-dimensional characteristic functions of a path law -/

/-- The finite-dimensional projection of a path onto the times of a finite set. -/
def restrictPath (I : Finset ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) :
    ↥I → BouRabeeGwynne.Euc 2 :=
  I.restrict fun v => f v

theorem measurable_restrictPath (I : Finset ℝ≥0) : Measurable (restrictPath I) :=
  Measurable.of_eval fun v => ContinuousMap.measurable_eval (v : ℝ≥0)

/-- The real linear combination `f ↦ ∑ⱼ ⟪θ j, f (u j)⟫` of the values of a path. -/
noncomputable def pathCombination {ι : Type*} [Fintype ι] (u : ι → ℝ≥0)
    (θ : ι → EuclideanSpace ℝ (Fin 2)) (f : BouRabeeGwynne.BrownianPath 2) : ℝ :=
  ∑ i, ⟪θ i, f (u i)⟫_ℝ

theorem continuous_pathCombination {ι : Type*} [Fintype ι] (u : ι → ℝ≥0)
    (θ : ι → EuclideanSpace ℝ (Fin 2)) : Continuous (pathCombination u θ) :=
  continuous_finset_sum _ fun i _ => continuous_const.inner (continuous_eval_const (u i))

/-- **The finite-dimensional characteristic function of a path law** at a finite family of
times `u` and directions `θ`. -/
noncomputable def fddCharFun {ι : Type*} [Fintype ι]
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) (u : ι → ℝ≥0)
    (θ : ι → EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ∫ f, Complex.exp ((pathCombination u θ f : ℂ) * Complex.I) ∂ρ

/-- Reindexing a finite family does not change the finite-dimensional characteristic
function. -/
theorem fddCharFun_congr {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) (u : ι → ℝ≥0)
    (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    fddCharFun ρ (u ∘ e) (θ ∘ e) = fddCharFun ρ u θ := by
  have hsum : ∀ f : BouRabeeGwynne.BrownianPath 2,
      pathCombination (u ∘ e) (θ ∘ e) f = pathCombination u θ f := by
    intro f
    exact Fintype.sum_equiv e _ _ fun i => rfl
  simp only [fddCharFun, hsum]

/-! ### The bounded continuous test function -/

/-- `f ↦ exp (i ∑ⱼ ⟪θ j, f (u j)⟫)` as a bounded continuous function of the path. -/
noncomputable def fddCharBcf {ι : Type*} [Fintype ι] (u : ι → ℝ≥0)
    (θ : ι → EuclideanSpace ℝ (Fin 2)) : BouRabeeGwynne.BrownianPath 2 →ᵇ ℂ where
  toFun f := Complex.exp ((pathCombination u θ f : ℂ) * Complex.I)
  continuous_toFun :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_pathCombination u θ)).mul continuous_const)
  map_bounded' := by
    refine ⟨2, fun x y => ?_⟩
    have hx : ‖Complex.exp ((pathCombination u θ x : ℂ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    have hy : ‖Complex.exp ((pathCombination u θ y : ℂ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    calc dist (Complex.exp ((pathCombination u θ x : ℂ) * Complex.I))
          (Complex.exp ((pathCombination u θ y : ℂ) * Complex.I))
        ≤ ‖Complex.exp ((pathCombination u θ x : ℂ) * Complex.I)‖
            + ‖Complex.exp ((pathCombination u θ y : ℂ) * Complex.I)‖ :=
          dist_le_norm_add_norm _ _
      _ = 2 := by rw [hx, hy]; norm_num

theorem integral_fddCharBcf {ι : Type*} [Fintype ι]
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) (u : ι → ℝ≥0)
    (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    ∫ f, fddCharBcf u θ f ∂ρ = fddCharFun ρ u θ := rfl

/-- **Lévy continuity, easy half, on the path space.**  Weak convergence of path laws gives
convergence of all finite-dimensional characteristic functions: the integrand is a bounded
continuous function of the path. -/
theorem tendsto_fddCharFun_of_tendsto {α : Type*} {F : Filter α}
    {𝓛 : α → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    {ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    (h : Tendsto 𝓛 F (𝓝 ρ)) {ι : Type*} [Fintype ι] (u : ι → ℝ≥0)
    (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun a => fddCharFun (𝓛 a : Measure (BouRabeeGwynne.BrownianPath 2)) u θ) F
      (𝓝 (fddCharFun (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) u θ)) := by
  have h' := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h
    (fddCharBcf u θ)
  simpa only [integral_fddCharBcf] using h'

/-! ### `charFunDual` of a finite-dimensional projection is an `fddCharFun` -/

/-- **Every continuous linear functional on `(↥I → Euc 2)` is a family of directions.**  Hence
the dual characteristic function of the finite-dimensional projection of *any* path law is
the finite-dimensional characteristic function at one fixed family `θ` depending only on the
functional. -/
theorem exists_fddCharFun_eq_charFunDual (I : Finset ℝ≥0)
    (L : StrongDual ℝ (↥I → BouRabeeGwynne.Euc 2)) :
    ∃ θ : ↥I → EuclideanSpace ℝ (Fin 2),
      ∀ ρ : Measure (BouRabeeGwynne.BrownianPath 2),
        charFunDual (ρ.map (restrictPath I)) L
          = fddCharFun ρ (fun i : ↥I => (i : ℝ≥0)) θ := by
  classical
  refine ⟨fun i => (InnerProductSpace.toDual ℝ (BouRabeeGwynne.Euc 2)).symm
      (L.comp (ContinuousLinearMap.single ℝ (fun _ : ↥I => BouRabeeGwynne.Euc 2) i)), ?_⟩
  intro ρ
  have hL : ∀ f : BouRabeeGwynne.BrownianPath 2,
      L (restrictPath I f)
        = pathCombination (fun i : ↥I => (i : ℝ≥0))
            (fun i => (InnerProductSpace.toDual ℝ (BouRabeeGwynne.Euc 2)).symm
              (L.comp (ContinuousLinearMap.single ℝ
                (fun _ : ↥I => BouRabeeGwynne.Euc 2) i))) f := by
    intro f
    simp only [pathCombination]
    rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ↥I => BouRabeeGwynne.Euc 2) L
      (restrictPath I f)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (InnerProductSpace.toDual_symm_apply).symm
  have hc : Continuous fun v : ↥I → BouRabeeGwynne.Euc 2 =>
      Complex.exp ((L v : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp L.continuous).mul continuous_const)
  rw [charFunDual_apply,
    integral_map (measurable_restrictPath I).aemeasurable hc.measurable.aestronglyMeasurable]
  simp only [fddCharFun, hL]

/-! ## The Gaussian quadratic form and the target's characteristic function -/

/-- The quadratic form `∑ᵢⱼ (θᵢᵀ Σ θⱼ)(uᵢ ∧ uⱼ)` of the anisotropic Brownian target. -/
noncomputable def gaussQuad (target : AnisotropicBrownianTarget) {ι : Type*} [Fintype ι]
    (u : ι → ℝ≥0) (θ : ι → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i, ∑ j, bilinForm target.covariance (θ i) (θ j) * ((min (u i) (u j) : ℝ≥0) : ℝ)

theorem gaussQuad_congr (target : AnisotropicBrownianTarget) {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] (e : ι' ≃ ι) (u : ι → ℝ≥0) (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    gaussQuad target (u ∘ e) (θ ∘ e) = gaussQuad target u θ := by
  refine (Fintype.sum_equiv e _ _ fun i => ?_)
  exact Fintype.sum_equiv e _ _ fun j => rfl

section Moments

variable {target : AnisotropicBrownianTarget}
  {ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}

/-- A finite family of projections of a Gaussian path law is a real Gaussian process. -/
theorem isGaussianProcess_projections
    (hgauss : IsGaussianProcess (fun (v : ℝ≥0) (f : BouRabeeGwynne.BrownianPath 2) => f v)
      (ρ : Measure (BouRabeeGwynne.BrownianPath 2)))
    {ι : Type*} (u : ι → ℝ≥0) (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    IsGaussianProcess (fun (i : ι) (f : BouRabeeGwynne.BrownianPath 2) => ⟪θ i, f (u i)⟫_ℝ)
      (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) :=
  hgauss.of_isGaussianProcess fun i => ⟨{u i},
    { toFun := fun x => ⟪θ i, x ⟨u i, Finset.mem_singleton_self (u i)⟩⟫_ℝ
      map_add' := fun x y => by simp [inner_add_right]
      map_smul' := fun c x => by simp [real_inner_smul_right] },
    fun _ => rfl⟩

/-- **The finite-dimensional characteristic function of a law satisfying the Gaussian limit
input is the Gaussian one.**  This is the converse half of the reduction, and it is what
computes the target's own characteristic function. -/
theorem fddCharFun_of_gaussianLimitInput (h : GaussianLimitInput target ρ)
    {ι : Type*} [Fintype ι] (u : ι → ℝ≥0) (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    fddCharFun (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) u θ
      = Complex.exp (-(gaussQuad target u θ : ℂ) / 2) := by
  classical
  set P : Measure (BouRabeeGwynne.BrownianPath 2) :=
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) with hP
  set X : ι → BouRabeeGwynne.BrownianPath 2 → ℝ :=
    fun i f => ⟪θ i, f (u i)⟫_ℝ with hX
  have hmem : ∀ i, MemLp (X i) 2 P := fun i => memLp_two_inner h.gaussian (θ i) (u i)
  have hint : ∀ i, Integrable (X i) P := fun i => (hmem i).integrable one_le_two
  have hGP : IsGaussianProcess X P := isGaussianProcess_projections h.gaussian u θ
  have hS : HasGaussianLaw (pathCombination u θ) P := by
    have := hGP.hasGaussianLaw_fun_sum (I := (Finset.univ : Finset ι))
    exact this
  -- the mean vanishes
  have hmean : P[pathCombination u θ] = 0 := by
    have : ∫ f, pathCombination u θ f ∂P = ∑ i, ∫ f, X i f ∂P :=
      integral_finset_sum _ fun i _ => hint i
    rw [this]
    exact Finset.sum_eq_zero fun i _ => h.centered (θ i) (u i)
  -- the variance is the Gaussian quadratic form
  have hcov : ∀ i j, cov[X i, X j; P] = bilinForm target.covariance (θ i) (θ j)
      * ((min (u i) (u j) : ℝ≥0) : ℝ) := by
    intro i j
    rw [covariance_eq_sub (hmem i) (hmem j)]
    simp only [Pi.mul_apply]
    rw [h.centered (θ i) (u i), h.centered (θ j) (u j), h.moment (θ i) (θ j) (u i) (u j)]
    ring
  have hvar : Var[pathCombination u θ; P] = gaussQuad target u θ := by
    have hself : cov[pathCombination u θ, pathCombination u θ; P]
        = Var[pathCombination u θ; P] :=
      covariance_self (hS.aemeasurable)
    rw [← hself]
    have hsplit : cov[fun f => ∑ i, X i f, fun f => ∑ j, X j f; P]
        = ∑ i, ∑ j, cov[X i, X j; P] :=
      covariance_fun_sum_fun_sum (fun i => hmem i) (fun j => hmem j)
    rw [show (pathCombination u θ : BouRabeeGwynne.BrownianPath 2 → ℝ)
        = fun f => ∑ i, X i f from rfl, hsplit, gaussQuad]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hcov i j
  -- the law of the linear combination is the real Gaussian law
  have hlaw : P.map (pathCombination u θ)
      = gaussianReal (P[pathCombination u θ]) (Var[pathCombination u θ; P]).toNNReal :=
    hS.map_eq_gaussianReal
  have hq : (0 : ℝ) ≤ gaussQuad target u θ := hvar ▸ variance_nonneg _ _
  have hc : Continuous fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hchar : fddCharFun P u θ = charFun (P.map (pathCombination u θ)) 1 := by
    have h1 : ∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) ∂(P.map (pathCombination u θ))
        = ∫ f, Complex.exp ((pathCombination u θ f : ℂ) * Complex.I) ∂P :=
      integral_map hS.aemeasurable hc.measurable.aestronglyMeasurable
    rw [charFun_apply_real]
    simp only [Complex.ofReal_one, one_mul, h1, fddCharFun]
  rw [hchar, hlaw, charFun_gaussianReal, hmean, hvar]
  rw [Real.coe_toNNReal _ hq]
  congr 1
  push_cast
  ring

end Moments

/-- **The target's finite-dimensional characteristic function.** -/
theorem fddCharFun_pathLaw (target : AnisotropicBrownianTarget) {ι : Type*} [Fintype ι]
    (u : ι → ℝ≥0) (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    fddCharFun (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) u θ
      = Complex.exp (-(gaussQuad target u θ : ℂ) / 2) :=
  fddCharFun_of_gaussianLimitInput (gaussianLimitInput_pathLaw target) u θ

/-! ## The producer: Gaussian limit input from converging characteristic functions -/

section Producer

variable {α : Type*} {F : Filter α} [F.NeBot]

/-- Generalisation of the `Fin n`-indexed hypothesis to an arbitrary finite index type. -/
theorem tendsto_fddCharFun_of_forall_fin (target : AnisotropicBrownianTarget)
    (𝓛 : α → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (hchar : ∀ (n : ℕ) (u : Fin n → ℝ≥0) (θ : Fin n → EuclideanSpace ℝ (Fin 2)),
      Tendsto (fun a => fddCharFun (𝓛 a : Measure (BouRabeeGwynne.BrownianPath 2)) u θ) F
        (𝓝 (Complex.exp (-(gaussQuad target u θ : ℂ) / 2))))
    {ι : Type} [Fintype ι] (u : ι → ℝ≥0) (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun a => fddCharFun (𝓛 a : Measure (BouRabeeGwynne.BrownianPath 2)) u θ) F
      (𝓝 (Complex.exp (-(gaussQuad target u θ : ℂ) / 2))) := by
  have e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := hchar (Fintype.card ι) (u ∘ e) (θ ∘ e)
  rw [gaussQuad_congr target e u θ] at h
  simpa only [fddCharFun_congr e] using h

/-- **Every finite-dimensional characteristic function of the limit law is the target's.** -/
theorem fddCharFun_eq_pathLaw_of_tendsto (target : AnisotropicBrownianTarget)
    {𝓛 : α → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    {ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    (hconv : Tendsto 𝓛 F (𝓝 ρ))
    (hchar : ∀ (n : ℕ) (u : Fin n → ℝ≥0) (θ : Fin n → EuclideanSpace ℝ (Fin 2)),
      Tendsto (fun a => fddCharFun (𝓛 a : Measure (BouRabeeGwynne.BrownianPath 2)) u θ) F
        (𝓝 (Complex.exp (-(gaussQuad target u θ : ℂ) / 2))))
    {ι : Type} [Fintype ι] (u : ι → ℝ≥0) (θ : ι → EuclideanSpace ℝ (Fin 2)) :
    fddCharFun (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) u θ
      = fddCharFun (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) u θ := by
  rw [fddCharFun_pathLaw target u θ]
  exact tendsto_nhds_unique (tendsto_fddCharFun_of_tendsto hconv u θ)
    (tendsto_fddCharFun_of_forall_fin target 𝓛 hchar u θ)

/-- **The finite-dimensional laws of the limit are the target's.**  This single identity
carries all three clauses of `GaussianLimitInput`; in particular the moment clauses need no
uniform integrability, being integrals against the *same* finite-dimensional law. -/
theorem map_restrictPath_eq_of_tendsto (target : AnisotropicBrownianTarget)
    {𝓛 : α → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    {ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    (hconv : Tendsto 𝓛 F (𝓝 ρ))
    (hchar : ∀ (n : ℕ) (u : Fin n → ℝ≥0) (θ : Fin n → EuclideanSpace ℝ (Fin 2)),
      Tendsto (fun a => fddCharFun (𝓛 a : Measure (BouRabeeGwynne.BrownianPath 2)) u θ) F
        (𝓝 (Complex.exp (-(gaussQuad target u θ : ℂ) / 2))))
    (I : Finset ℝ≥0) :
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)).map (restrictPath I)
      = (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map (restrictPath I) := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  obtain ⟨θ, hθ⟩ := exists_fddCharFun_eq_charFunDual I L
  rw [hθ, hθ, fddCharFun_eq_pathLaw_of_tendsto target hconv hchar]

/-- Integrals of a measurable function of the finite-dimensional projection agree once the
projected laws agree. -/
theorem integral_comp_restrictPath (ρ ρ' : Measure (BouRabeeGwynne.BrownianPath 2))
    (I : Finset ℝ≥0) (hmap : ρ.map (restrictPath I) = ρ'.map (restrictPath I))
    {g : (↥I → BouRabeeGwynne.Euc 2) → ℝ} (hg : Measurable g) :
    ∫ f, g (restrictPath I f) ∂ρ = ∫ f, g (restrictPath I f) ∂ρ' := by
  rw [← integral_map (measurable_restrictPath I).aemeasurable hg.aestronglyMeasurable, hmap,
    integral_map (measurable_restrictPath I).aemeasurable hg.aestronglyMeasurable]

/-- **The producer.**  Convergence of the finite-dimensional characteristic functions of a
net of path laws to the Gaussian ones forces every weak limit of the net to satisfy the
filtration-free Gaussian limit input. -/
theorem gaussianLimitInput_of_tendsto_fddCharFun (target : AnisotropicBrownianTarget)
    {𝓛 : α → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    {ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    (hconv : Tendsto 𝓛 F (𝓝 ρ))
    (hchar : ∀ (n : ℕ) (u : Fin n → ℝ≥0) (θ : Fin n → EuclideanSpace ℝ (Fin 2)),
      Tendsto (fun a => fddCharFun (𝓛 a : Measure (BouRabeeGwynne.BrownianPath 2)) u θ) F
        (𝓝 (Complex.exp (-(gaussQuad target u θ : ℂ) / 2)))) :
    GaussianLimitInput target ρ := by
  have hmap := map_restrictPath_eq_of_tendsto target hconv hchar
  refine ⟨⟨fun I => ?_⟩, fun θ v => ?_, fun θ η s t => ?_⟩
  · -- Gaussianity of every finite-dimensional law
    refine { aemeasurable := (measurable_restrictPath I).aemeasurable, isGaussian_map := ?_ }
    show IsGaussian ((ρ : Measure (BouRabeeGwynne.BrownianPath 2)).map (restrictPath I))
    rw [hmap I]
    exact ((isGaussianProcess_pathLaw target).hasGaussianLaw I).isGaussian_map
  · -- centred projections
    have hg : Measurable fun x : ↥({v} : Finset ℝ≥0) → BouRabeeGwynne.Euc 2 =>
        ⟪θ, x ⟨v, Finset.mem_singleton_self v⟩⟫_ℝ :=
      (continuous_const.inner
        (continuous_apply (⟨v, Finset.mem_singleton_self v⟩ : ↥({v} : Finset ℝ≥0)))).measurable
    have h := integral_comp_restrictPath (ρ : Measure (BouRabeeGwynne.BrownianPath 2))
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) {v} (hmap {v}) hg
    exact h.trans (TargetPathLawMoments.integral_inner_eq_zero_pathLaw target θ v)
  · -- two-time moments
    have hs : s ∈ ({s, t} : Finset ℝ≥0) := Finset.mem_insert_self s {t}
    have ht : t ∈ ({s, t} : Finset ℝ≥0) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
    have hg : Measurable fun x : ↥({s, t} : Finset ℝ≥0) → BouRabeeGwynne.Euc 2 =>
        ⟪θ, x ⟨s, hs⟩⟫_ℝ * ⟪η, x ⟨t, ht⟩⟫_ℝ :=
      ((continuous_const.inner
            (continuous_apply (⟨s, hs⟩ : ↥({s, t} : Finset ℝ≥0)))).mul
        (continuous_const.inner
            (continuous_apply (⟨t, ht⟩ : ↥({s, t} : Finset ℝ≥0))))).measurable
    have h := integral_comp_restrictPath (ρ : Measure (BouRabeeGwynne.BrownianPath 2))
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) {s, t} (hmap {s, t}) hg
    exact h.trans (integral_inner_mul_inner_pathLaw target θ η s t)

end Producer

/-! ## The weld into `FddClusterReduction` -/

/-- **The finite-dimensional characteristic-function limits of the rescaled laws.**  This is
the replacement of `FddClusterReduction.RescaledSequentialLimitIdentification`: it never
mentions a limit law, and is the statement a Lindeberg / characteristic-function argument on
the walk's own sample space produces. -/
def RescaledFddCharFunLimits (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) : Prop :=
  ∀ ε : ℕ → ℝ≥0, Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
    ∀ (n : ℕ) (u : Fin n → ℝ≥0) (θ : Fin n → EuclideanSpace ℝ (Fin 2)),
      Tendsto (fun k => fddCharFun
          (diffusivelyRescaledPathLaw μ (ε k) : Measure (BouRabeeGwynne.BrownianPath 2)) u θ)
        atTop (𝓝 (Complex.exp (-(gaussQuad target u θ : ℂ) / 2)))

/-! ## Machine-checked welds

Each `example` is the consumer of another module applied to the producer above, so the
hypothesis shapes are verified by the elaborator rather than by eye. -/

/-- Weld into `GaussianLimitIdentification.rescaledSequentialLimitIdentification_of_gaussianLimits`:
the producer fills the `GaussianLimitInput` slot at every sequential limit point. -/
example (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) (h : RescaledFddCharFunLimits μ target) :
    RescaledSequentialLimitIdentification μ target :=
  rescaledSequentialLimitIdentification_of_gaussianLimits μ target
    fun ε ρ hε hρ => gaussianLimitInput_of_tendsto_fddCharFun target hρ (h ε hε)

end ReflectedGMS.GaussianWeakLimit
