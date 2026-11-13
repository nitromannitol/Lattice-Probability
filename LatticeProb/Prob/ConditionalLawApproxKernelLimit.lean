import LatticeProb.Prob.ConditionalLawKernelLimit

/-!
# Limits of conditional laws with approximate kernels

In `LatticeProb.compProd_eq_of_kernel_locally_uniform` the discrete conditional laws are exactly given by
kernels: `E[f (X n) | Y n] = ∫ f d(κ n (Y n))` almost surely.  In applications to Markov chains in a random
environment the kernel that is available as a function of the conditioning variable `Y n` only approximates
the conditional law: the conditional expectation of `f (X n)` is the average of a quenched kernel over the
unobserved part of the environment, and the observed kernel `κ n` is close to it in probability.

Here the exact identity is replaced by closeness in `L¹`:

`E |E[f (X n) | Y n] - ∫ f d(κ n (Y n))| → 0`  for every bounded continuous `f`.

* `LatticeProb.integral_mul_eq_of_approx_condexp_tendsto`: the limit identity
  `E[f (X) g (Y)] = E[(∫ f d(P Y)) g (Y)]` for a limit pair `(X, Y)` with law `ν`, when the conditional
  expectations are approximated in `L¹` by integrable functions `B i` such that `(B i, Y i)` converges in law
  to `(∫ f d(P Y), Y)`.
* `LatticeProb.compProd_eq_of_approx_condexp_tendsto`: the criterion for convergence of conditional laws
  (`LatticeProb.compProd_eq_of_condexp_tendsto`) with this approximation.
* `LatticeProb.compProd_eq_of_kernel_approx_locally_uniform`: the limit of approximate kernels that converge
  locally uniformly at almost every point of the limit kernel (the analogue of
  `LatticeProb.compProd_eq_of_kernel_locally_uniform`).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology BoundedContinuousFunction ProbabilityTheory MeasurableSpace
open scoped ENNReal NNReal

namespace LatticeProb

/-- The truncation `a ↦ max (-C) (min C a)` is `1`-Lipschitz. -/
theorem abs_clip_sub_clip_le (C a b : ℝ) :
    |max (-C) (min C a) - max (-C) (min C b)| ≤ |a - b| := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, abs_le]
    constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)
  · rw [abs_of_nonneg (sub_nonneg.2 h), abs_le]
    constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)

section Main

variable {E F : Type*}
  [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
  [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [TopologicalSpace.PseudoMetrizableSpace E] in
/-- **Limit identity with approximate conditional expectations.**  Let `(X i, Y i)` converge in law to `ν` and
let `B i` be integrable functions on the probability spaces `Ω i` such that
`E |E[f (X i) | Y i] - B i| → 0` and `(B i, Y i)` converges in law to `(∫ f d(P Y), Y)` with `(X, Y) ∼ ν`.
Then `E[f (X) g (Y)] = E[(∫ f d(P Y)) g (Y)]` for every bounded continuous `g`. -/
theorem integral_mul_eq_of_approx_condexp_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {X : ∀ i, Ω i → E} {Y : ∀ i, Ω i → F}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {ν : Measure (E × F)} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (E × F) →ᵇ ℝ, Tendsto (fun i => ∫ ω, g (X i ω, Y i ω) ∂μ i) l
      (𝓝 (∫ p, g p ∂ν)))
    {P : F → Measure E} [∀ y, IsProbabilityMeasure (P y)]
    (f : E →ᵇ ℝ) {B : ∀ i, Ω i → ℝ} (hBm : ∀ i, Measurable (B i)) (hBi : ∀ i, Integrable (B i) (μ i))
    (hBapprox : Tendsto (fun i => ∫ ω, |condExpGiven (μ i) (X i) (Y i) f ω - B i ω| ∂μ i) l (𝓝 0))
    (hBlaw : ∀ g : (ℝ × F) →ᵇ ℝ, Tendsto (fun i => ∫ ω, g (B i ω, Y i ω) ∂μ i) l
      (𝓝 (∫ p, g (∫ x, f x ∂P p.2, p.2) ∂ν)))
    (φ : F →ᵇ ℝ) :
    ∫ p, f p.1 * φ p.2 ∂ν = ∫ p, (∫ x, f x ∂P p.2) * φ p.2 ∂ν := by
  classical
  set C : ℝ := ‖f‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg f
  have hm : ∀ i, MeasurableSpace.comap (Y i) inferInstance ≤ (inferInstance : MeasurableSpace (Ω i)) :=
    fun i => (hY i).comap_le
  have hfX : ∀ i, Integrable (fun ω => f (X i ω)) (μ i) := fun i =>
    Integrable.of_bound (f.continuous.measurable.comp (hX i)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X i ω))
  have hstep : ∀ i, ∫ ω, f (X i ω) * φ (Y i ω) ∂μ i =
      ∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i := by
    intro i
    have hgY : StronglyMeasurable[MeasurableSpace.comap (Y i) inferInstance]
        (fun ω => φ (Y i ω)) := by
      have : Measurable[MeasurableSpace.comap (Y i) inferInstance] (Y i) := comap_measurable (Y i)
      exact (φ.continuous.measurable.comp this).stronglyMeasurable
    have hce := condExp_stronglyMeasurable_mul_of_bound (hm i) hgY (hfX i) ‖φ‖
      (Filter.Eventually.of_forall fun ω => φ.norm_coe_le_norm (Y i ω))
    calc ∫ ω, f (X i ω) * φ (Y i ω) ∂μ i
        = ∫ ω, ((fun ω => φ (Y i ω)) * (fun ω => f (X i ω))) ω ∂μ i := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp [mul_comm]
      _ = ∫ ω, (μ i)[(fun ω => φ (Y i ω)) * (fun ω => f (X i ω)) |
            MeasurableSpace.comap (Y i) inferInstance] ω ∂μ i := (integral_condExp (hm i)).symm
      _ = ∫ ω, ((fun ω => φ (Y i ω)) * condExpGiven (μ i) (X i) (Y i) f) ω ∂μ i :=
          integral_congr_ae hce
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp [mul_comm]
  have hbd : ∀ i, ∀ᵐ ω ∂μ i, |condExpGiven (μ i) (X i) (Y i) f ω| ≤ C := by
    intro i
    exact ae_bdd_abs_condExp_of_ae_bdd_abs (μ := μ i)
      (m := MeasurableSpace.comap (Y i) inferInstance) (R := C)
      (f := fun ω => f (X i ω)) (Filter.Eventually.of_forall fun ω => by
        have := f.norm_coe_le_norm (X i ω)
        rwa [Real.norm_eq_abs] at this)
  have hbdP : ∀ y, |∫ x, f x ∂P y| ≤ C := by
    intro y
    have := norm_integral_le_of_norm_le_const (μ := P y) (f := fun x => f x) (C := C)
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
    simpa [Real.norm_eq_abs] using this
  have hL := hlaw (prodBCF f φ)
  have hR := hBlaw (clipMulBCF C hC0 φ)
  have e2 : ∫ p, clipMulBCF C hC0 φ (∫ x, f x ∂P p.2, p.2) ∂ν =
      ∫ p, (∫ x, f x ∂P p.2) * φ p.2 ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [clipMulBCF_apply, clipBCF_of_abs_le hC0 (hbdP p.2)]
  rw [e2] at hR
  -- integrability of the two comparison sequences
  have hcI : ∀ i, Integrable (fun ω => condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω)) (μ i) := by
    intro i
    refine Integrable.of_bound (C := C * ‖φ‖) ?_ ?_
    · exact (((stronglyMeasurable_condExp (m := MeasurableSpace.comap (Y i) inferInstance)
        (μ := μ i) (f := fun ω => f (X i ω))).mono (hm i)).aestronglyMeasurable).mul
        (φ.continuous.measurable.comp (hY i)).aestronglyMeasurable
    · filter_upwards [hbd i] with ω hω
      rw [norm_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hω) (φ.norm_coe_le_norm (Y i ω))
        (norm_nonneg _) hC0
  have hbI : ∀ i, Integrable (fun ω => clipMulBCF C hC0 φ (B i ω, Y i ω)) (μ i) := fun i =>
    Integrable.of_bound ((clipMulBCF C hC0 φ).continuous.measurable.comp
      ((hBm i).prodMk (hY i))).aestronglyMeasurable ‖clipMulBCF C hC0 φ‖
      (Filter.Eventually.of_forall fun ω => (clipMulBCF C hC0 φ).norm_coe_le_norm _)
  have hdI : ∀ i, Integrable (fun ω => |condExpGiven (μ i) (X i) (Y i) f ω - B i ω|) (μ i) := fun i =>
    ((integrable_condExp).sub (hBi i)).abs
  -- the distance between the two sequences
  have hdist : ∀ i, dist (∫ ω, clipMulBCF C hC0 φ (B i ω, Y i ω) ∂μ i)
      (∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i) ≤
      ‖φ‖ * ∫ ω, |condExpGiven (μ i) (X i) (Y i) f ω - B i ω| ∂μ i := by
    intro i
    rw [Real.dist_eq, ← integral_sub (hbI i) (hcI i), ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae ((hbI i).sub (hcI i)).abs
      ((hdI i).const_mul _) ?_)
    filter_upwards [hbd i] with ω hω
    rw [clipMulBCF_apply, ← sub_mul, abs_mul]
    have h1 : |clipBCF C hC0 (B i ω) - condExpGiven (μ i) (X i) (Y i) f ω| ≤
        |condExpGiven (μ i) (X i) (Y i) f ω - B i ω| := by
      calc |clipBCF C hC0 (B i ω) - condExpGiven (μ i) (X i) (Y i) f ω|
          = |clipBCF C hC0 (B i ω) - clipBCF C hC0 (condExpGiven (μ i) (X i) (Y i) f ω)| := by
            rw [clipBCF_of_abs_le hC0 hω]
        _ = |clipBCF C hC0 (condExpGiven (μ i) (X i) (Y i) f ω) - clipBCF C hC0 (B i ω)| :=
            abs_sub_comm _ _
        _ ≤ |condExpGiven (μ i) (X i) (Y i) f ω - B i ω| := abs_clip_sub_clip_le C _ _
    calc |clipBCF C hC0 (B i ω) - condExpGiven (μ i) (X i) (Y i) f ω| * |φ (Y i ω)|
        ≤ |condExpGiven (μ i) (X i) (Y i) f ω - B i ω| * ‖φ‖ :=
          mul_le_mul h1 (by simpa [Real.norm_eq_abs] using φ.norm_coe_le_norm (Y i ω))
            (abs_nonneg _) (abs_nonneg _)
      _ = ‖φ‖ * |condExpGiven (μ i) (X i) (Y i) f ω - B i ω| := mul_comm _ _
  have hdist0 : Tendsto (fun i => dist (∫ ω, clipMulBCF C hC0 φ (B i ω, Y i ω) ∂μ i)
      (∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i)) l (𝓝 0) := by
    refine squeeze_zero (fun i => dist_nonneg) hdist ?_
    simpa using hBapprox.const_mul ‖φ‖
  have hR' := hR.congr_dist hdist0
  have hL' : Tendsto (fun i => ∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i) l
      (𝓝 (∫ p, f p.1 * φ p.2 ∂ν)) := hL.congr hstep
  exact tendsto_nhds_unique hL' hR'

/-- **Criterion for convergence of conditional laws with approximate conditional expectations**
(after `LatticeProb.compProd_eq_of_condexp_tendsto`).  Let `(X i, Y i)` be random pairs, on probability spaces
indexed by the filter `l`, converging in law to a probability measure `ν` on `E × F`, and let `P : F → Measure E`
be a family of probability measures with measurable integrals of bounded continuous functions.  Suppose that
for every bounded continuous `f` the conditional expectations `E[f (X i) | Y i]` are approximated in `L¹` by
integrable functions `B i` such that `(B i, Y i)` converges in law to `(∫ f d(P Y), Y)`.  Then `P` is a regular
conditional law of the first coordinate given the second under `ν`: `ν.map swap = ν.snd ⊗ₘ P`. -/
theorem compProd_eq_of_approx_condexp_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {X : ∀ i, Ω i → E} {Y : ∀ i, Ω i → F}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {ν : Measure (E × F)} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (E × F) →ᵇ ℝ, Tendsto (fun i => ∫ ω, g (X i ω, Y i ω) ∂μ i) l
      (𝓝 (∫ p, g p ∂ν)))
    {P : F → Measure E} [∀ y, IsProbabilityMeasure (P y)]
    (hP : ∀ f : E →ᵇ ℝ, Measurable fun y => ∫ x, f x ∂P y)
    (hB : ∀ f : E →ᵇ ℝ, ∃ B : ∀ i, Ω i → ℝ, (∀ i, Measurable (B i)) ∧ (∀ i, Integrable (B i) (μ i)) ∧
      Tendsto (fun i => ∫ ω, |condExpGiven (μ i) (X i) (Y i) f ω - B i ω| ∂μ i) l (𝓝 0) ∧
      ∀ g : (ℝ × F) →ᵇ ℝ, Tendsto (fun i => ∫ ω, g (B i ω, Y i ω) ∂μ i) l
        (𝓝 (∫ p, g (∫ x, f x ∂P p.2, p.2) ∂ν))) :
    ∃ κ : Kernel F E, IsMarkovKernel κ ∧ (∀ y, κ y = P y) ∧ ν.map Prod.swap = ν.snd ⊗ₘ κ := by
  have hPm : Measurable P := measurable_measure_of_measurable_integral_boundedContinuous hP
  let κ : Kernel F E := ⟨P, hPm⟩
  have : IsMarkovKernel κ := ⟨fun y => inferInstanceAs (IsProbabilityMeasure (P y))⟩
  refine ⟨κ, inferInstance, fun y => rfl, ?_⟩
  have hν : ν = (ν.snd ⊗ₘ κ).map Prod.swap := by
    refine ext_of_integral_mul_boundedContinuous (fun f φ => ?_)
    have hmap : ∫ p : E × F, f p.1 * φ p.2 ∂((ν.snd ⊗ₘ κ).map Prod.swap) =
        ∫ q : F × E, f q.2 * φ q.1 ∂(ν.snd ⊗ₘ κ) :=
      integral_map measurable_swap.aemeasurable (prodBCF f φ).continuous.aestronglyMeasurable
    obtain ⟨B, hBm, hBi, hBa, hBl⟩ := hB f
    rw [integral_mul_eq_of_approx_condexp_tendsto hX hY hlaw f hBm hBi hBa hBl φ, hmap]
    have hint : Integrable (fun q : F × E => f q.2 * φ q.1) (ν.snd ⊗ₘ κ) :=
      Integrable.of_bound
        ((f.continuous.comp continuous_snd).mul (φ.continuous.comp continuous_fst)).aestronglyMeasurable
        (‖f‖ * ‖φ‖) (Filter.Eventually.of_forall fun q => by
          rw [norm_mul]
          exact mul_le_mul (f.norm_coe_le_norm q.2) (φ.norm_coe_le_norm q.1) (norm_nonneg _)
            (norm_nonneg _))
    have h1 : ∫ q : F × E, f q.2 * φ q.1 ∂(ν.snd ⊗ₘ κ) =
        ∫ y, (∫ x, f x ∂P y) * φ y ∂ν.snd := by
      rw [Measure.integral_compProd hint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show ∫ x, f x * φ y ∂P y = _
      exact integral_mul_const _ _
    rw [h1]
    have hm : Measurable fun y => (∫ x, f x ∂P y) * φ y := (hP f).mul φ.continuous.measurable
    exact (integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable).symm
  have h2 := congrArg (Measure.map (Prod.swap : E × F → F × E)) hν
  rw [Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id] at h2
  exact h2

/-- **Regular conditional law of a limit of approximate kernels.**  Let `(X n, Y n)` converge in law to `ν`
on `E × F` and let `κ n : F → Measure E` be probability measures with measurable integrals of bounded
continuous functions such that `E |E[f (X n) | Y n] - ∫ f d(κ n (Y n))| → 0` for every bounded continuous `f`.
If `P` is a family of probability measures with measurable integrals and, for every bounded continuous `f` and
`ν.snd`-almost every `y`, the functions `y' ↦ ∫ f d(κ n y')` converge to `∫ f d(P y)` uniformly on a small ball
around `y`, then `P` is a regular conditional law of `X` given `Y` under `ν`: `ν.map swap = ν.snd ⊗ₘ P`. -/
theorem compProd_eq_of_kernel_approx_locally_uniform
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)] {X : ∀ n, Ω n → E} {Y : ∀ n, Ω n → F}
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    {ν : Measure (E × F)} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (E × F) →ᵇ ℝ, Tendsto (fun n => ∫ ω, g (X n ω, Y n ω) ∂μ n) atTop
      (𝓝 (∫ p, g p ∂ν)))
    {κ : ℕ → F → Measure E} [∀ n y, IsProbabilityMeasure (κ n y)]
    (hκm : ∀ n (f : E →ᵇ ℝ), Measurable fun y => ∫ x, f x ∂κ n y)
    (hκ : ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ ω,
      |condExpGiven (μ n) (X n) (Y n) f ω - ∫ x, f x ∂κ n (Y n ω)| ∂μ n) atTop (𝓝 0))
    {P : F → Measure E} [∀ y, IsProbabilityMeasure (P y)]
    (hP : ∀ f : E →ᵇ ℝ, Measurable fun y => ∫ x, f x ∂P y)
    (hlu : ∀ f : E →ᵇ ℝ, ∀ᵐ y ∂ν.snd, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n → ∀ y' : F, dist y' y < δ → |∫ x, f x ∂κ n y' - ∫ x, f x ∂P y| ≤ ε) :
    ∃ κ' : Kernel F E, IsMarkovKernel κ' ∧ (∀ y, κ' y = P y) ∧
      ν.map Prod.swap = ν.snd ⊗ₘ κ' := by
  classical
  refine compProd_eq_of_approx_condexp_tendsto (l := atTop) hX hY hlaw hP ?_
  intro f
  refine ⟨fun n ω => ∫ x, f x ∂κ n (Y n ω), fun n => (hκm n f).comp (hY n), fun n => ?_, hκ f, ?_⟩
  · refine Integrable.of_bound ((hκm n f).comp (hY n)).aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun ω => ?_)
    have := norm_integral_le_of_norm_le_const (μ := κ n (Y n ω)) (f := fun x => f x) (C := ‖f‖)
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
    simpa using this
  · intro g
    have hlimY : ∀ G : F →ᵇ ℝ, Tendsto (fun n => ∫ y, G y ∂((μ n).map (Y n))) atTop
        (𝓝 (∫ y, G y ∂ν.snd)) := by
      intro G
      have h := hlaw (G.compContinuous ⟨Prod.snd, continuous_snd⟩)
      have e1 : ∀ n, ∫ y, G y ∂((μ n).map (Y n)) = ∫ ω, G (Y n ω) ∂μ n := fun n =>
        integral_map (hY n).aemeasurable G.continuous.aestronglyMeasurable
      have e2 : ∫ y, G y ∂ν.snd = ∫ p, G p.2 ∂ν :=
        integral_map measurable_snd.aemeasurable G.continuous.aestronglyMeasurable
      simpa [e1, e2] using h
    have hlu' : ∀ᵐ y ∂ν.snd, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ y' : F, dist y' y < δ →
          dist (∫ x, f x ∂κ n y') (∫ x, f x ∂P y) ≤ ε := by
      filter_upwards [hlu f] with y hy ε hε
      obtain ⟨δ, hδ, N, hN⟩ := hy ε hε
      exact ⟨δ, hδ, N, fun n hn y' hy' => by simpa [Real.dist_eq] using hN n hn y' hy'⟩
    have hmain := tendsto_integral_comp_prod_of_ae_locally_uniform ν.snd
      (fun n => (μ n).map (Y n)) hlimY (fun y => ∫ x, f x ∂P y) (fun n y => ∫ x, f x ∂κ n y)
      (fun n => hκm n f) (hP f) hlu' g
    have e1 : ∀ n, ∫ ω, g (∫ x, f x ∂κ n (Y n ω), Y n ω) ∂μ n =
        ∫ y, g (∫ x, f x ∂κ n y, y) ∂((μ n).map (Y n)) := by
      intro n
      have hm : Measurable fun y => g (∫ x, f x ∂κ n y, y) :=
        g.continuous.measurable.comp ((hκm n f).prodMk measurable_id)
      rw [integral_map (hY n).aemeasurable hm.aestronglyMeasurable]
    have e2 : ∫ p, g (∫ x, f x ∂P p.2, p.2) ∂ν = ∫ y, g (∫ x, f x ∂P y, y) ∂ν.snd := by
      have hm : Measurable fun y => g (∫ x, f x ∂P y, y) :=
        g.continuous.measurable.comp ((hP f).prodMk measurable_id)
      exact (integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable).symm
    show Tendsto (fun n => ∫ ω, g (∫ x, f x ∂κ n (Y n ω), Y n ω) ∂μ n) atTop _
    rw [funext e1, e2]
    exact hmain

end Main

end LatticeProb
