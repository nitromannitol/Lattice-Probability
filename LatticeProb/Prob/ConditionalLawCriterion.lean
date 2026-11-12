import Mathlib

/-!
# A criterion for convergence of conditional laws

Let `(X n, Y n)` be random pairs in a product `E × F` of separable pseudo-metrizable spaces converging
in law to a pair with law `ν`, and let `P : F → Measure E` be a family of probability measures such
that `y ↦ ∫ f dP y` is measurable for every bounded continuous `f`. If for every bounded continuous
`f` the pairs `(E[f (X n) | Y n], Y n)` converge in law to `(∫ f d(P Y), Y)`, then `P` is a regular
conditional law of the first coordinate given the second under `ν`.

* `measurable_measure_of_measurable_integral_boundedContinuous`: such a family is a kernel.
* `ext_of_integral_mul_boundedContinuous`: a finite measure on `E × F` is determined by the integrals
  of the products `f x * g y` of bounded continuous functions.
* `integral_mul_eq_of_condexp_tendsto`: the identity `E[f X * g Y] = E[(∫ f dP Y) * g Y]` in the limit.
* `compProd_eq_of_condexp_tendsto`: the conclusion `ν.map swap = ν.snd ⊗ₘ κ` with `κ y = P y`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology BoundedContinuousFunction ProbabilityTheory MeasurableSpace
open scoped ENNReal NNReal

namespace LatticeProb

section Aux

variable {E F : Type*}
  [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace F] [TopologicalSpace.PseudoMetrizableSpace F] [MeasurableSpace F] [BorelSpace F]

/-- The real-valued bounded continuous function underlying an `ℝ≥0`-valued one bounded by `1`. -/
noncomputable def toRealUnit (g : E →ᵇ ℝ≥0) (hg : ∀ x, g x ≤ 1) : E →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (g x : ℝ), NNReal.continuous_coe.comp g.continuous⟩ 1 (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have hx : (g x : ℝ) ≤ 1 := by exact_mod_cast hg x
      have hy : (g y : ℝ) ≤ 1 := by exact_mod_cast hg y
      have hx0 := NNReal.coe_nonneg (g x)
      have hy0 := NNReal.coe_nonneg (g y)
      rw [abs_le]; constructor <;> linarith)

omit [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem toRealUnit_apply (g : E →ᵇ ℝ≥0) (hg : ∀ x, g x ≤ 1) (x : E) :
    toRealUnit g hg x = (g x : ℝ) := rfl

/-- The product `x, y ↦ f x * g y` as a bounded continuous function on `E × F`. -/
noncomputable def prodBCF (f : E →ᵇ ℝ) (g : F →ᵇ ℝ) : (E × F) →ᵇ ℝ :=
  f.compContinuous ⟨Prod.fst, continuous_fst⟩ * g.compContinuous ⟨Prod.snd, continuous_snd⟩

omit [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.PseudoMetrizableSpace F] [MeasurableSpace F] [BorelSpace F] in
theorem prodBCF_apply (f : E →ᵇ ℝ) (g : F →ᵇ ℝ) (p : E × F) : prodBCF f g p = f p.1 * g p.2 := rfl

omit [TopologicalSpace F] [TopologicalSpace.PseudoMetrizableSpace F] [BorelSpace F] in
/-- A family of probability measures on `E` indexed by `F`, whose integrals of bounded continuous
functions are measurable in the index, is measurable (i.e. a Markov kernel). -/
theorem measurable_measure_of_measurable_integral_boundedContinuous
    {P : F → Measure E} [∀ y, IsProbabilityMeasure (P y)]
    (hP : ∀ f : E →ᵇ ℝ, Measurable fun y => ∫ x, f x ∂P y) : Measurable P := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {s : Set E | IsClosed s}) ?_ isPiSystem_isClosed ?_
  · rw [BorelSpace.measurable_eq (α := E)]
    exact borel_eq_generateFrom_isClosed
  · intro s hs
    have hlim : Tendsto (fun n y => ∫⁻ x, (hs.apprSeq n x : ℝ≥0∞) ∂P y) atTop
        (𝓝 fun y => P y s) := by
      rw [tendsto_pi_nhds]
      intro y
      exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hs (P y)
    refine measurable_of_tendsto_metrizable (fun n => ?_) hlim
    have heq : (fun y => ∫⁻ x, (hs.apprSeq n x : ℝ≥0∞) ∂P y) = fun y => ENNReal.ofReal
        (∫ x, toRealUnit (hs.apprSeq n) (HasOuterApproxClosed.apprSeq_apply_le_one hs n) x ∂P y) := by
      funext y
      rw [ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr fun x => ?_
        simp [toRealUnit_apply]
      · exact (toRealUnit (hs.apprSeq n) (HasOuterApproxClosed.apprSeq_apply_le_one hs n)).integrable
          (P y)
      · exact Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _
    rw [heq]
    exact ENNReal.measurable_ofReal.comp (hP _)

section ProdExt

variable [SecondCountableTopology F]

/-- Integrals of products of approximating functions of two closed sets converge to the measure of
the product of the sets. -/
theorem tendsto_ofReal_integral_apprSeq_prod {A : Set E} (hA : IsClosed A) {B : Set F} (hB : IsClosed B)
    (ν : Measure (E × F)) [IsFiniteMeasure ν] :
    Tendsto (fun k => ENNReal.ofReal (∫ p,
      toRealUnit (hA.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hA k) p.1 *
        toRealUnit (hB.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hB k) p.2 ∂ν))
      atTop (𝓝 (ν (A ×ˢ B))) := by
  classical
  have h1 : ∀ k, ENNReal.ofReal (∫ p,
      toRealUnit (hA.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hA k) p.1 *
        toRealUnit (hB.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hB k) p.2 ∂ν) =
      ∫⁻ p, ((hA.apprSeq k p.1 * hB.apprSeq k p.2 : ℝ≥0) : ℝ≥0∞) ∂ν := by
    intro k
    have hint : Integrable (fun p : E × F =>
        toRealUnit (hA.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hA k) p.1 *
          toRealUnit (hB.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hB k) p.2) ν := (prodBCF
      (toRealUnit (hA.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hA k))
      (toRealUnit (hB.apprSeq k) (HasOuterApproxClosed.apprSeq_apply_le_one hB k))).integrable ν
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun p => mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))]
    refine lintegral_congr fun p => ?_
    simp only [toRealUnit_apply]
    rw [← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]
  refine (tendsto_congr h1).2 ?_
  have hmeas : ∀ k, Measurable (fun p : E × F =>
      ((hA.apprSeq k p.1 * hB.apprSeq k p.2 : ℝ≥0) : ℝ≥0∞)) := fun k =>
    (ENNReal.continuous_coe.comp
      (((hA.apprSeq k).continuous.comp continuous_fst).mul
        ((hB.apprSeq k).continuous.comp continuous_snd))).measurable
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := ν) (fun _ => (1 : ℝ≥0∞))
    (F := fun k (p : E × F) => ((hA.apprSeq k p.1 * hB.apprSeq k p.2 : ℝ≥0) : ℝ≥0∞))
    (f := (A ×ˢ B).indicator 1) hmeas ?_ (by simp [measure_ne_top]) ?_
  · rwa [lintegral_indicator_one (hA.measurableSet.prod hB.measurableSet)] at hlim
  · intro k
    refine Filter.Eventually.of_forall fun p => ?_
    have ha := HasOuterApproxClosed.apprSeq_apply_le_one hA k p.1
    have hb := HasOuterApproxClosed.apprSeq_apply_le_one hB k p.2
    have : hA.apprSeq k p.1 * hB.apprSeq k p.2 ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul' ha hb
        _ = 1 := one_mul 1
    show ((hA.apprSeq k p.1 * hB.apprSeq k p.2 : ℝ≥0) : ℝ≥0∞) ≤ 1
    exact_mod_cast this
  · refine Filter.Eventually.of_forall fun p => ?_
    have hx := tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hA) p.1
    have hy := tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hB) p.2
    have := ENNReal.tendsto_coe.2 (hx.mul hy)
    have heq : (A ×ˢ B).indicator (1 : E × F → ℝ≥0∞) p =
        ((A.indicator (fun _ => (1 : ℝ≥0)) p.1 * B.indicator (fun _ => (1 : ℝ≥0)) p.2 : ℝ≥0) :
          ℝ≥0∞) := by
      by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
        simp [Set.indicator, h1, h2, Set.mem_prod]
    rw [heq]
    exact this

/-- A finite measure on a product of separable pseudo-metrizable spaces is determined by the integrals
of the products `f x * g y` of bounded continuous functions. -/
theorem ext_of_integral_mul_boundedContinuous {ν₁ ν₂ : Measure (E × F)} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂]
    (h : ∀ (f : E →ᵇ ℝ) (g : F →ᵇ ℝ), ∫ p, f p.1 * g p.2 ∂ν₁ = ∫ p, f p.1 * g p.2 ∂ν₂) :
    ν₁ = ν₂ := by
  have hrect : ∀ A : Set E, IsClosed A → ∀ B : Set F, IsClosed B → ν₁ (A ×ˢ B) = ν₂ (A ×ˢ B) := by
    intro A hA B hB
    refine tendsto_nhds_unique (tendsto_ofReal_integral_apprSeq_prod hA hB ν₁) ?_
    have := tendsto_ofReal_integral_apprSeq_prod hA hB ν₂
    refine this.congr fun k => ?_
    congr 1
    exact (h _ _).symm
  refine ext_of_generate_finite
    (Set.image2 (· ×ˢ ·) {s : Set E | IsClosed s} {s : Set F | IsClosed s}) ?_
    (isPiSystem_isClosed.prod isPiSystem_isClosed) ?_ ?_
  · have hE : (‹MeasurableSpace E›) = generateFrom {s : Set E | IsClosed s} := by
      rw [BorelSpace.measurable_eq (α := E)]
      exact borel_eq_generateFrom_isClosed
    have hF' : (‹MeasurableSpace F›) = generateFrom {s : Set F | IsClosed s} := by
      rw [BorelSpace.measurable_eq (α := F)]
      exact borel_eq_generateFrom_isClosed
    have hcsE : IsCountablySpanning {s : Set E | IsClosed s} :=
      ⟨fun _ => Set.univ, fun _ => isClosed_univ, Set.iUnion_const _⟩
    have hcsF : IsCountablySpanning {s : Set F | IsClosed s} :=
      ⟨fun _ => Set.univ, fun _ => isClosed_univ, Set.iUnion_const _⟩
    rw [← generateFrom_prod_eq hcsE hcsF, ← hE, ← hF']
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hrect A hA B hB
  · simpa using hrect Set.univ isClosed_univ Set.univ isClosed_univ

end ProdExt

section Main

variable [SecondCountableTopology F]

/-- The bounded continuous truncation `a ↦ max (-C) (min C a)` of the real line. -/
noncomputable def clipBCF (C : ℝ) (hC : 0 ≤ C) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun a => max (-C) (min C a), by fun_prop⟩ (2 * C)
    (fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : -C ≤ max (-C) (min C a) := le_max_left _ _
      have h2 : max (-C) (min C a) ≤ C := max_le (by linarith) (min_le_left _ _)
      have h3 : -C ≤ max (-C) (min C b) := le_max_left _ _
      have h4 : max (-C) (min C b) ≤ C := max_le (by linarith) (min_le_left _ _)
      rw [abs_le]; constructor <;> linarith)

theorem clipBCF_apply (C : ℝ) (hC : 0 ≤ C) (a : ℝ) : clipBCF C hC a = max (-C) (min C a) := rfl

theorem clipBCF_of_abs_le {C : ℝ} (hC : 0 ≤ C) {a : ℝ} (ha : |a| ≤ C) : clipBCF C hC a = a := by
  rw [abs_le] at ha
  rw [clipBCF_apply, min_eq_right ha.2, max_eq_right ha.1]

/-- The product `(a, y) ↦ clip a * φ y` as a bounded continuous function on `ℝ × F`. -/
noncomputable def clipMulBCF (C : ℝ) (hC : 0 ≤ C) (φ : F →ᵇ ℝ) : (ℝ × F) →ᵇ ℝ :=
  (clipBCF C hC).compContinuous ⟨Prod.fst, continuous_fst⟩ *
    φ.compContinuous ⟨Prod.snd, continuous_snd⟩

omit [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E] [MeasurableSpace E]
  [TopologicalSpace.PseudoMetrizableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace F] in
theorem clipMulBCF_apply (C : ℝ) (hC : 0 ≤ C) (φ : F →ᵇ ℝ) (a : ℝ) (y : F) :
    clipMulBCF C hC φ (a, y) = clipBCF C hC a * φ y := rfl

omit [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E]
  [TopologicalSpace F] [TopologicalSpace.PseudoMetrizableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- The conditional expectation `E[f (X) | Y]` given the `σ`-algebra generated by `Y`. -/
noncomputable abbrev condExpGiven {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → E)
    (Y : Ω → F) (f : E → ℝ) : Ω → ℝ :=
  μ[fun ω => f (X ω) | MeasurableSpace.comap Y inferInstance]

omit [TopologicalSpace.PseudoMetrizableSpace E] [TopologicalSpace.PseudoMetrizableSpace F]
  [SecondCountableTopology F] in
/-- **Limit identity of the conditional law criterion.** Under the hypotheses of the criterion,
`E[f X * g Y] = E[(∫ f d(P Y)) * g Y]` for the limit pair `(X, Y)` with law `ν`. -/
theorem integral_mul_eq_of_condexp_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {X : ∀ i, Ω i → E} {Y : ∀ i, Ω i → F}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {ν : Measure (E × F)} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (E × F) →ᵇ ℝ, Tendsto (fun i => ∫ ω, g (X i ω, Y i ω) ∂μ i) l
      (𝓝 (∫ p, g p ∂ν)))
    {P : F → Measure E} [∀ y, IsProbabilityMeasure (P y)]
    (hcond : ∀ (f : E →ᵇ ℝ) (g : (ℝ × F) →ᵇ ℝ),
      Tendsto (fun i => ∫ ω, g (condExpGiven (μ i) (X i) (Y i) f ω, Y i ω) ∂μ i) l (𝓝 (∫ p, g (∫ x, f x ∂P p.2, p.2) ∂ν)))
    (f : E →ᵇ ℝ) (φ : F →ᵇ ℝ) :
    ∫ p, f p.1 * φ p.2 ∂ν = ∫ p, (∫ x, f x ∂P p.2) * φ p.2 ∂ν := by
  classical
  set C : ℝ := ‖f‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg f
  have hstep : ∀ i, ∫ ω, f (X i ω) * φ (Y i ω) ∂μ i =
      ∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i := by
    intro i
    have hm : MeasurableSpace.comap (Y i) inferInstance ≤ (inferInstance : MeasurableSpace (Ω i)) :=
      (hY i).comap_le
    have hfX : Integrable (fun ω => f (X i ω)) (μ i) :=
      Integrable.of_bound (f.continuous.measurable.comp (hX i)).aestronglyMeasurable C
        (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X i ω))
    have hgY : StronglyMeasurable[MeasurableSpace.comap (Y i) inferInstance]
        (fun ω => φ (Y i ω)) := by
      have : Measurable[MeasurableSpace.comap (Y i) inferInstance] (Y i) := comap_measurable (Y i)
      exact (φ.continuous.measurable.comp this).stronglyMeasurable
    have hce := condExp_stronglyMeasurable_mul_of_bound hm hgY hfX ‖φ‖
      (Filter.Eventually.of_forall fun ω => φ.norm_coe_le_norm (Y i ω))
    calc ∫ ω, f (X i ω) * φ (Y i ω) ∂μ i
        = ∫ ω, ((fun ω => φ (Y i ω)) * (fun ω => f (X i ω))) ω ∂μ i := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp [mul_comm]
      _ = ∫ ω, (μ i)[(fun ω => φ (Y i ω)) * (fun ω => f (X i ω)) |
            MeasurableSpace.comap (Y i) inferInstance] ω ∂μ i := (integral_condExp hm).symm
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
  have hR := hcond f (clipMulBCF C hC0 φ)
  have hR' : Tendsto (fun i => ∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i) l
      (𝓝 (∫ p, (∫ x, f x ∂P p.2) * φ p.2 ∂ν)) := by
    have e1 : ∀ i, ∫ ω, clipMulBCF C hC0 φ (condExpGiven (μ i) (X i) (Y i) f ω, Y i ω) ∂μ i =
        ∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i := by
      intro i
      refine integral_congr_ae ?_
      filter_upwards [hbd i] with ω hω
      rw [clipMulBCF_apply, clipBCF_of_abs_le hC0 hω]
    have e2 : ∫ p, clipMulBCF C hC0 φ (∫ x, f x ∂P p.2, p.2) ∂ν =
        ∫ p, (∫ x, f x ∂P p.2) * φ p.2 ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      beta_reduce
      rw [clipMulBCF_apply, clipBCF_of_abs_le hC0 (hbdP p.2)]
    rw [← e2]
    exact hR.congr e1
  have hL' : Tendsto (fun i => ∫ ω, condExpGiven (μ i) (X i) (Y i) f ω * φ (Y i ω) ∂μ i) l
      (𝓝 (∫ p, f p.1 * φ p.2 ∂ν)) := hL.congr hstep
  exact tendsto_nhds_unique hL' hR'

/-- **Criterion for convergence of conditional laws** (Bou-Rabee–Gwynne, random walks on mated-CRT maps,
Lemma 7.5, after Gwynne–Pfeffer). Let `(X i, Y i)` be random pairs, on probability spaces indexed by
the filter `l`, with values in `E × F` for pseudo-metrizable `E`, `F` and `F` second countable, whose
laws converge weakly to a probability measure `ν` on `E × F`. Let `P : F → Measure E` be a family of
probability measures such that `y ↦ ∫ f d(P y)` is measurable for each bounded continuous `f`, and
suppose that for all bounded continuous `f` the pairs `(E[f (X i) | Y i], Y i)` converge in law to
`(∫ f d(P Y), Y)`, where `(X, Y)` has law `ν`. Then `P` is a regular conditional law of the first
coordinate given the second under `ν`: `P` is a Markov kernel and `ν.map swap = ν.snd ⊗ₘ P`. -/
theorem compProd_eq_of_condexp_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {X : ∀ i, Ω i → E} {Y : ∀ i, Ω i → F}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {ν : Measure (E × F)} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (E × F) →ᵇ ℝ, Tendsto (fun i => ∫ ω, g (X i ω, Y i ω) ∂μ i) l
      (𝓝 (∫ p, g p ∂ν)))
    {P : F → Measure E} [∀ y, IsProbabilityMeasure (P y)]
    (hP : ∀ f : E →ᵇ ℝ, Measurable fun y => ∫ x, f x ∂P y)
    (hcond : ∀ (f : E →ᵇ ℝ) (g : (ℝ × F) →ᵇ ℝ),
      Tendsto (fun i => ∫ ω, g (condExpGiven (μ i) (X i) (Y i) f ω, Y i ω) ∂μ i) l
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
    rw [integral_mul_eq_of_condexp_tendsto hX hY hlaw hcond f φ, hmap]
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

end Main

end Aux

end LatticeProb
