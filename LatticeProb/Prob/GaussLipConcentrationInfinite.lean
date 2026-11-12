import LatticeProb.Gauss.Coords
import LatticeProb.Prob.GaussLipConcentration
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.ProductMeasure

/-!
# Gaussian concentration on an arbitrary product of standard Gaussians

Let `ι` be any index type and `gaussLaw ι` the product of standard Gaussians on `ι → ℝ`.
A measurable integrable `F : (ι → ℝ) → ℝ` that moves by at most `L` times the `ℓ²` distance
between any two configurations at finite `ℓ²` distance satisfies
`P(F ≥ E F + t) ≤ exp (-t² / (2 L²))` for `t ≥ 0` (`gaussLaw_tail_le_of_hasSum_lipschitz`).

## Proof

* A measurable `F` is measurable with respect to the coordinates in a countable set `J`
  (`exists_countable_measurable`).
* For a finite set `S`, `(ω, η) ↦ S.piecewise ω η` maps two independent copies of `gaussLaw ι`
  to `gaussLaw ι` (`measurePreserving_piecewise`). Hence the conditional expectation of `F`
  given the coordinates in `S` is `avgOff F S ω = ∫ F (S.piecewise ω η) dη`
  (`avgOff_ae_eq_condExp`). It is a Euclidean `L`-Lipschitz function of the coordinates in `S`,
  so the finite-dimensional bound `GaussConc.lintegral_exp_le_of_lipschitz` controls its
  exponential moments (`lintegral_exp_avgOff_le`).
* Along finite sets exhausting `J`, Lévy's upward theorem gives almost sure convergence of
  `avgOff F S` to `F`. Fatou's lemma passes the exponential moment bound to `F`, and Markov's
  inequality gives the tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.GaussConc

variable {ι : Type*}

section Countable

/-- Every measurable set of `ι → ℝ` is measurable with respect to the coordinates in some
countable set. -/
theorem exists_countable_measurableSet {A : Set (ι → ℝ)} (hA : MeasurableSet A) :
    ∃ J : Set ι, J.Countable ∧
      MeasurableSet[⨆ j ∈ J, MeasurableSpace.comap (fun ω : ι → ℝ => ω j) inferInstance] A := by
  have hA' : MeasurableSet[⨆ i, MeasurableSpace.comap (fun ω : ι → ℝ => ω i) inferInstance] A :=
    hA
  rw [MeasurableSpace.measurableSet_iSup] at hA'
  clear hA
  induction hA' with
  | basic s hs =>
    obtain ⟨i, hi⟩ := hs
    exact ⟨{i}, countable_singleton i,
      le_iSup₂ (f := fun j (_ : j ∈ ({i} : Set ι)) =>
        MeasurableSpace.comap (fun ω : ι → ℝ => ω j) inferInstance) i rfl s hi⟩
  | empty => exact ⟨∅, countable_empty, MeasurableSpace.measurableSet_empty _⟩
  | compl s _ ih =>
    obtain ⟨J, hJ, h⟩ := ih
    exact ⟨J, hJ, MeasurableSpace.measurableSet_compl _ _ h⟩
  | iUnion f _ ih =>
    choose J hJ h using ih
    refine ⟨⋃ n, J n, countable_iUnion hJ, MeasurableSpace.measurableSet_iUnion _ _ fun n => ?_⟩
    exact (iSup₂_mono' fun j hj => ⟨j, mem_iUnion.2 ⟨n, hj⟩, le_rfl⟩ :
      (⨆ j ∈ J n, MeasurableSpace.comap (fun ω : ι → ℝ => ω j) inferInstance) ≤ _) _ (h n)

/-- Every measurable `F : (ι → ℝ) → ℝ` is measurable with respect to the coordinates in some
countable set. -/
theorem exists_countable_measurable {F : (ι → ℝ) → ℝ} (hF : Measurable F) :
    ∃ J : Set ι, J.Countable ∧
      Measurable[⨆ j ∈ J, MeasurableSpace.comap (fun ω : ι → ℝ => ω j) inferInstance] F := by
  choose J hJ h using fun q : ℚ =>
    exists_countable_measurableSet (hF measurableSet_Iio : MeasurableSet (F ⁻¹' Iio (q : ℝ)))
  refine ⟨⋃ q, J q, countable_iUnion hJ, ?_⟩
  have key := @measurable_generateFrom _ _
    (⨆ j ∈ ⋃ q, J q, MeasurableSpace.comap (fun ω : ι → ℝ => ω j) inferInstance)
    (⋃ a : ℚ, {Iio (a : ℝ)}) F (by
      rintro t ⟨_, ⟨q, rfl⟩, ht⟩
      rw [mem_singleton_iff.1 ht]
      exact (iSup₂_mono' fun j hj => ⟨j, mem_iUnion.2 ⟨q, hj⟩, le_rfl⟩ :
        (⨆ j ∈ J q, MeasurableSpace.comap (fun ω : ι → ℝ => ω j) inferInstance) ≤ _) _ (h q))
  rwa [← Real.borel_eq_generateFrom_Iio_rat] at key

/-- A countable set is covered by an increasing sequence of finite sets. -/
theorem exists_monotone_finset_cover {J : Set ι} (hJ : J.Countable) :
    ∃ S : ℕ → Finset ι, Monotone S ∧ ∀ j ∈ J, ∃ n, j ∈ S n := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => ∅, monotone_const, by simp⟩
  · obtain ⟨f, rfl⟩ := hJ.exists_eq_range hne
    refine ⟨fun n => (Finset.range n).image f,
      fun m n hmn => Finset.image_subset_image (Finset.range_subset_range.2 hmn), ?_⟩
    rintro _ ⟨k, rfl⟩
    exact ⟨k + 1, Finset.mem_image.2 ⟨k, Finset.mem_range.2 k.lt_succ_self, rfl⟩⟩

end Countable

section Splice

variable [DecidableEq ι]

theorem measurable_piecewise (S : Finset ι) :
    Measurable fun p : (ι → ℝ) × (ι → ℝ) => S.piecewise p.1 p.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i ∈ S
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hi]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi]
    exact (measurable_pi_apply i).comp measurable_snd

/-- `(ω, η) ↦ S.piecewise ω η` maps two independent copies of `gaussLaw ι` to `gaussLaw ι`. -/
theorem measurePreserving_piecewise (S : Finset ι) :
    MeasurePreserving (fun p : (ι → ℝ) × (ι → ℝ) => S.piecewise p.1 p.2)
      ((gaussLaw ι).prod (gaussLaw ι)) (gaussLaw ι) := by
  refine ⟨measurable_piecewise S, ?_⟩
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (measurable_piecewise S)
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun p : (ι → ℝ) × (ι → ℝ) => S.piecewise p.1 p.2) ⁻¹' Set.pi (↑s) t =
      Set.pi (↑(s ∩ S)) t ×ˢ Set.pi (↑(s \ S)) t := by
    ext p
    simp only [mem_preimage, Set.mem_pi, mem_prod, Finset.coe_inter, Finset.coe_sdiff,
      mem_inter_iff, Set.mem_sdiff, Finset.mem_coe]
    constructor
    · intro h
      exact ⟨fun i ⟨hs, hS⟩ => by simpa [Finset.piecewise_eq_of_mem _ _ _ hS] using h i hs,
        fun i ⟨hs, hS⟩ => by simpa [Finset.piecewise_eq_of_notMem _ _ _ hS] using h i hs⟩
    · rintro ⟨h1, h2⟩ i hs
      by_cases hS : i ∈ S
      · simpa [Finset.piecewise_eq_of_mem _ _ _ hS] using h1 i ⟨hs, hS⟩
      · simpa [Finset.piecewise_eq_of_notMem _ _ _ hS] using h2 i ⟨hs, hS⟩
  rw [hpre, Measure.prod_prod]
  simp only [gaussLaw]
  rw [Measure.infinitePi_pi _ (fun i _ => ht i), Measure.infinitePi_pi _ (fun i _ => ht i),
    Finset.prod_inter_mul_prod_sdiff]

/-- The average of `F` over the coordinates outside `S`, the coordinates in `S` being those
of `ω`. -/
def avgOff (F : (ι → ℝ) → ℝ) (S : Finset ι) (ω : ι → ℝ) : ℝ :=
  ∫ η, F (S.piecewise ω η) ∂gaussLaw ι

variable {F : (ι → ℝ) → ℝ}

theorem avgOff_congr {S : Finset ι} {ω ω' : ι → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    avgOff F S ω = avgOff F S ω' := by
  unfold avgOff
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  change F (S.piecewise ω η) = F (S.piecewise ω' η)
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [Finset.piecewise_eq_of_mem _ _ _ hi, h i hi]
  · simp [Finset.piecewise_eq_of_notMem _ _ _ hi]

theorem stronglyMeasurable_avgOff (hFm : Measurable F) (S : Finset ι) :
    StronglyMeasurable (avgOff F S) :=
  (hFm.comp (measurable_piecewise S)).stronglyMeasurable.integral_prod_right'

theorem integrable_comp_piecewise (hFi : Integrable F (gaussLaw ι)) (S : Finset ι) :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) => F (S.piecewise p.1 p.2))
      ((gaussLaw ι).prod (gaussLaw ι)) :=
  ((measurePreserving_piecewise S).integrable_comp hFi.aestronglyMeasurable).2 hFi

theorem integrable_avgOff (hFi : Integrable F (gaussLaw ι)) (S : Finset ι) :
    Integrable (avgOff F S) (gaussLaw ι) :=
  (integrable_comp_piecewise hFi S).integral_prod_left

/-- Extension by zero of a configuration on `S`. -/
def extendZero (S : Finset ι) (x : S → ℝ) : ι → ℝ := fun i => if h : i ∈ S then x ⟨i, h⟩ else 0

theorem measurable_extendZero (S : Finset ι) : Measurable (extendZero S) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i ∈ S
  · simpa [extendZero, hi] using measurable_pi_apply (⟨i, hi⟩ : S)
  · simp [extendZero, hi]

theorem avgOff_eq_comp_restrict (S : Finset ι) (ω : ι → ℝ) :
    avgOff F S ω = avgOff F S (extendZero S (S.restrict ω)) :=
  avgOff_congr fun i hi => by simp [extendZero, hi]

/-- `avgOff F S` is measurable with respect to the coordinates in `S`. -/
theorem stronglyMeasurable_avgOff_piFinset (hFm : Measurable F) (S : Finset ι) :
    StronglyMeasurable[Filtration.piFinset (X := fun _ : ι => ℝ) S] (avgOff F S) := by
  have h := ((stronglyMeasurable_avgOff hFm S).comp_measurable
    (measurable_extendZero S)).comp_measurable
      (comap_measurable (@Finset.restrict ι (fun _ => ℝ) S))
  have hfun : avgOff F S = (avgOff F S ∘ extendZero S) ∘ S.restrict :=
    funext fun ω => avgOff_eq_comp_restrict S ω
  rw [hfun]
  exact h

/-- **Conditional expectation given finitely many coordinates.** -/
theorem setIntegral_avgOff (hFi : Integrable F (gaussLaw ι)) {S : Finset ι}
    {A : Set (ι → ℝ)} (hA : MeasurableSet[Filtration.piFinset (X := fun _ : ι => ℝ) S] A) :
    ∫ ω in A, avgOff F S ω ∂gaussLaw ι = ∫ ω in A, F ω ∂gaussLaw ι := by
  have hmp := measurePreserving_piecewise (ι := ι) S
  have hA' : MeasurableSet A := Filtration.le _ S A hA
  obtain ⟨B, -, hB⟩ := hA
  have hmem : ∀ ω η, S.piecewise ω η ∈ A ↔ ω ∈ A := by
    intro ω η
    rw [← hB]
    simp only [mem_preimage]
    rw [show S.restrict (S.piecewise ω η) = S.restrict ω from
      funext fun i => Finset.piecewise_eq_of_mem _ _ _ i.2]
  rw [← integral_indicator hA', ← integral_indicator hA']
  have hRHS : ∫ ω, A.indicator F ω ∂gaussLaw ι =
      ∫ p, A.indicator F (S.piecewise p.1 p.2) ∂((gaussLaw ι).prod (gaussLaw ι)) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact (hFi.indicator hA').aestronglyMeasurable)
  have hfun : (fun p : (ι → ℝ) × (ι → ℝ) => A.indicator F (S.piecewise p.1 p.2)) =
      (Prod.fst ⁻¹' A).indicator fun p => F (S.piecewise p.1 p.2) := by
    funext p
    by_cases h : p.1 ∈ A
    · rw [indicator_of_mem ((hmem _ _).2 h), indicator_of_mem (show p ∈ Prod.fst ⁻¹' A from h)]
    · rw [indicator_of_notMem (fun h' => h ((hmem _ _).1 h')),
        indicator_of_notMem (show p ∉ Prod.fst ⁻¹' A from h)]
  rw [hRHS, hfun,
    integral_prod _ ((integrable_comp_piecewise hFi S).indicator (measurable_fst hA'))]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  by_cases h : ω ∈ A
  · simp only [indicator_of_mem h, indicator_of_mem (show (ω, _) ∈ Prod.fst ⁻¹' A from h)]
    rfl
  · simp only [indicator_of_notMem h,
      indicator_of_notMem (show (ω, _) ∉ Prod.fst ⁻¹' A from h), integral_zero]

theorem avgOff_ae_eq_condExp (hFm : Measurable F) (hFi : Integrable F (gaussLaw ι))
    (S : Finset ι) :
    avgOff F S =ᵐ[gaussLaw ι] (gaussLaw ι)[F | Filtration.piFinset (X := fun _ : ι => ℝ) S] :=
  ae_eq_condExp_of_forall_setIntegral_eq (Filtration.le _ S) hFi
    (fun _ _ _ => (integrable_avgOff hFi S).integrableOn)
    (fun _ hA _ => setIntegral_avgOff hFi hA)
    (stronglyMeasurable_avgOff_piFinset hFm S).aestronglyMeasurable

theorem integral_avgOff (hFi : Integrable F (gaussLaw ι)) (S : Finset ι) :
    ∫ ω, avgOff F S ω ∂gaussLaw ι = ∫ ω, F ω ∂gaussLaw ι := by
  simpa only [Measure.restrict_univ] using setIntegral_avgOff hFi (S := S) MeasurableSet.univ

variable {L : ℝ}

theorem hasSum_sq_sub_piecewise (S : Finset ι) (ω ω' η : ι → ℝ) :
    HasSum (fun i => (S.piecewise ω η i - S.piecewise ω' η i) ^ 2) (∑ i ∈ S, (ω i - ω' i) ^ 2) := by
  have h : HasSum (fun i => (S.piecewise ω η i - S.piecewise ω' η i) ^ 2)
      (∑ i ∈ S, (S.piecewise ω η i - S.piecewise ω' η i) ^ 2) :=
    hasSum_sum_of_ne_finset_zero fun i hi => by simp [Finset.piecewise_eq_of_notMem _ _ _ hi]
  convert h using 1
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.piecewise_eq_of_mem _ _ _ hi]

theorem integrable_piecewise (hFm : Measurable F) (hFi : Integrable F (gaussLaw ι))
    (hFL : ∀ ω η : ι → ℝ, ∀ M : ℝ, HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * √M) (S : Finset ι) (ω : ι → ℝ) :
    Integrable (fun η => F (S.piecewise ω η)) (gaussLaw ι) := by
  obtain ⟨ω₀, hω₀⟩ := (integrable_comp_piecewise hFi S).prod_right_ae.exists
  refine (hω₀.abs.add (integrable_const (L * √(∑ i ∈ S, (ω i - ω₀ i) ^ 2)))).mono'
    (hFm.comp ((measurable_piecewise S).comp measurable_prodMk_left)).aestronglyMeasurable
    (ae_of_all _ fun η => ?_)
  have h := hFL _ _ _ (hasSum_sq_sub_piecewise S ω ω₀ η)
  rw [Real.norm_eq_abs]
  calc |F (S.piecewise ω η)|
      ≤ |F (S.piecewise ω₀ η)| + |F (S.piecewise ω η) - F (S.piecewise ω₀ η)| := by
        have := abs_add_le (F (S.piecewise ω₀ η)) (F (S.piecewise ω η) - F (S.piecewise ω₀ η))
        rwa [add_sub_cancel] at this
    _ ≤ _ := add_le_add le_rfl h

theorem abs_avgOff_sub_le (hFm : Measurable F) (hFi : Integrable F (gaussLaw ι))
    (hFL : ∀ ω η : ι → ℝ, ∀ M : ℝ, HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * √M) (S : Finset ι) (ω ω' : ι → ℝ) :
    |avgOff F S ω - avgOff F S ω'| ≤ L * √(∑ i ∈ S, (ω i - ω' i) ^ 2) := by
  rw [avgOff, avgOff, ← integral_sub (integrable_piecewise hFm hFi hFL S ω)
    (integrable_piecewise hFm hFi hFL S ω')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ η, |F (S.piecewise ω η) - F (S.piecewise ω' η)| ∂gaussLaw ι
      ≤ ∫ _η, L * √(∑ i ∈ S, (ω i - ω' i) ^ 2) ∂gaussLaw ι :=
        integral_mono ((integrable_piecewise hFm hFi hFL S ω).sub
          (integrable_piecewise hFm hFi hFL S ω')).abs (integrable_const _)
          fun η => hFL _ _ _ (hasSum_sq_sub_piecewise S ω ω' η)
    _ = L * √(∑ i ∈ S, (ω i - ω' i) ^ 2) := by simp

/-- **Exponential moments of `avgOff F S`**, from the finite-dimensional Gaussian
concentration of Lipschitz functions. -/
theorem lintegral_exp_avgOff_le (hL : 0 < L) (hFm : Measurable F)
    (hFi : Integrable F (gaussLaw ι))
    (hFL : ∀ ω η : ι → ℝ, ∀ M : ℝ, HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * √M) (S : Finset ι) (s : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (exp (s * (avgOff F S ω - ∫ η, F η ∂gaussLaw ι))) ∂gaussLaw ι ≤
      ENNReal.ofReal (exp (s ^ 2 * L ^ 2 / 2)) := by
  set H : (S → ℝ) → ℝ := fun x => avgOff F S (extendZero S x)
  have hHm : Measurable H :=
    (stronglyMeasurable_avgOff hFm S).measurable.comp (measurable_extendZero S)
  set G : EuclideanSpace ℝ S → ℝ := fun e => H (WithLp.ofLp e)
  have hGm : Measurable G := hHm.comp (PiLp.continuous_ofLp 2 _).measurable
  have hmt : Measurable (WithLp.toLp 2 : (S → ℝ) → EuclideanSpace ℝ S) :=
    (PiLp.continuous_toLp 2 _).measurable
  have hG : LipschitzWith ⟨L, hL.le⟩ G := by
    refine LipschitzWith.of_dist_le_mul fun e e' => ?_
    rw [Real.dist_eq, EuclideanSpace.dist_eq]
    refine (abs_avgOff_sub_le hFm hFi hFL S _ _).trans (le_of_eq ?_)
    show L * _ = L * _
    rw [← Finset.sum_coe_sort S]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [extendZero, Real.dist_eq, sq_abs]
  have hmap : (gaussLaw ι).map S.restrict = Measure.pi fun _ : S => gaussianReal 0 1 :=
    Measure.infinitePi_map_restrict _
  have hstd : (Measure.pi fun _ : S => gaussianReal 0 1).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℝ S) := map_pi_eq_stdGaussian
  have hcomp : ∀ ω, avgOff F S ω = G (WithLp.toLp 2 (S.restrict ω)) :=
    fun ω => avgOff_eq_comp_restrict S ω
  set c := ∫ e, G e ∂stdGaussian (EuclideanSpace ℝ S) with hc
  have hint : ∫ η, F η ∂gaussLaw ι = c := by
    rw [← integral_avgOff hFi S, hc, ← hstd,
      integral_map hmt.aemeasurable hGm.aestronglyMeasurable, ← hmap]
    refine Eq.trans ?_ (integral_map (Finset.measurable_restrict S).aemeasurable
      (hGm.comp hmt).aestronglyMeasurable).symm
    exact integral_congr_ae (ae_of_all _ hcomp)
  have hΨ : Measurable fun e : EuclideanSpace ℝ S => ENNReal.ofReal (exp (s * (G e - c))) :=
    ENNReal.measurable_ofReal.comp (measurable_exp.comp (measurable_const.mul
      (hGm.sub measurable_const)))
  have e1 : ∫⁻ e, ENNReal.ofReal (exp (s * (G e - c))) ∂stdGaussian (EuclideanSpace ℝ S) =
      ∫⁻ x, ENNReal.ofReal (exp (s * (G (WithLp.toLp 2 x) - c)))
        ∂(Measure.pi fun _ : S => gaussianReal 0 1) := by
    rw [← hstd]
    exact lintegral_map hΨ hmt
  have e2 : ∫⁻ x, ENNReal.ofReal (exp (s * (G (WithLp.toLp 2 x) - c)))
        ∂(Measure.pi fun _ : S => gaussianReal 0 1) =
      ∫⁻ ω, ENNReal.ofReal (exp (s * (G (WithLp.toLp 2 (S.restrict ω)) - c))) ∂gaussLaw ι := by
    rw [← hmap]
    exact lintegral_map (hΨ.comp hmt) (Finset.measurable_restrict S)
  rw [hint]
  calc ∫⁻ ω, ENNReal.ofReal (exp (s * (avgOff F S ω - c))) ∂gaussLaw ι
      = ∫⁻ e, ENNReal.ofReal (exp (s * (G e - c))) ∂stdGaussian (EuclideanSpace ℝ S) := by
        rw [e1, e2]
        refine lintegral_congr fun ω => ?_
        rw [hcomp]
    _ ≤ ENNReal.ofReal (exp (s ^ 2 * ((⟨L, hL.le⟩ : ℝ≥0) : ℝ) ^ 2 / 2)) :=
        lintegral_exp_le_of_lipschitz hG s
    _ = ENNReal.ofReal (exp (s ^ 2 * L ^ 2 / 2)) := rfl

end Splice

/-- The filtration of the coordinates in an increasing sequence of finite sets. -/
def finsetFiltration (S : ℕ → Finset ι) (hS : Monotone S) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) where
  seq n := Filtration.piFinset (X := fun _ : ι => ℝ) (S n)
  mono' _ _ h := Filtration.mono _ (hS h)
  le' n := Filtration.le _ (S n)

/-- **Gaussian concentration for a Cameron-Martin Lipschitz functional** of an arbitrary family
of independent standard Gaussians: if `F` moves by at most `L` times the `ℓ²` distance between
any two configurations at finite `ℓ²` distance, then `P(F ≥ E F + t) ≤ exp (-t² / (2 L²))`. -/
theorem gaussLaw_tail_le_of_hasSum_lipschitz {F : (ι → ℝ) → ℝ} {L : ℝ} (hL : 0 < L)
    (hFm : Measurable F) (hFi : Integrable F (gaussLaw ι))
    (hFL : ∀ ω η : ι → ℝ, ∀ M : ℝ, HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * √M) {t : ℝ} (ht : 0 ≤ t) :
    gaussLaw ι {ω | ∫ η, F η ∂gaussLaw ι + t ≤ F ω} ≤
      ENNReal.ofReal (exp (-(t ^ 2) / (2 * L ^ 2))) := by
  classical
  set m := ∫ η, F η ∂gaussLaw ι
  obtain ⟨J, hJ, hFJ⟩ := exists_countable_measurable hFm
  obtain ⟨S, hS, hSJ⟩ := exists_monotone_finset_cover hJ
  set ℱ := finsetFiltration S hS
  have hFℱ : StronglyMeasurable[⨆ n, ℱ n] F := by
    refine (Measurable.mono hFJ ?_ le_rfl).stronglyMeasurable
    refine iSup₂_le fun j hj => ?_
    obtain ⟨n, hn⟩ := hSJ j hj
    refine le_trans ?_ (le_iSup ℱ n)
    have : (fun ω : ι → ℝ => ω j) = (fun x : S n → ℝ => x ⟨j, hn⟩) ∘ (S n).restrict := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  have hlim : ∀ᵐ ω ∂gaussLaw ι, Tendsto (fun n => avgOff F (S n) ω) atTop (𝓝 (F ω)) := by
    have h1 := tendsto_ae_condExp (μ := gaussLaw ι) (ℱ := ℱ) F
    rw [condExp_of_stronglyMeasurable (iSup_le ℱ.le) hFℱ hFi] at h1
    have h2 : ∀ᵐ ω ∂gaussLaw ι, ∀ n, avgOff F (S n) ω = (gaussLaw ι)[F | ℱ n] ω :=
      ae_all_iff.2 fun n => avgOff_ae_eq_condExp hFm hFi (S n)
    filter_upwards [h1, h2] with ω h1 h2
    exact h1.congr fun n => (h2 n).symm
  set s := t / L ^ 2 with hs
  have hs0 : 0 ≤ s := div_nonneg ht (sq_nonneg L)
  have hΦc : Continuous fun y : ℝ => ENNReal.ofReal (exp (s * (y - m))) :=
    ENNReal.continuous_ofReal.comp (continuous_exp.comp (continuous_const.mul
      (continuous_id.sub continuous_const)))
  have hmgf : ∫⁻ ω, ENNReal.ofReal (exp (s * (F ω - m))) ∂gaussLaw ι ≤
      ENNReal.ofReal (exp (s ^ 2 * L ^ 2 / 2)) := by
    calc ∫⁻ ω, ENNReal.ofReal (exp (s * (F ω - m))) ∂gaussLaw ι
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (exp (s * (avgOff F (S n) ω - m)))) atTop
            ∂gaussLaw ι := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with ω hω
          exact ((hΦc.tendsto (F ω)).comp hω).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (exp (s * (avgOff F (S n) ω - m)))
            ∂gaussLaw ι) atTop :=
          lintegral_liminf_le' fun n =>
            (hΦc.measurable.comp (stronglyMeasurable_avgOff hFm (S n)).measurable).aemeasurable
      _ ≤ ENNReal.ofReal (exp (s ^ 2 * L ^ 2 / 2)) :=
          liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
            lintegral_exp_avgOff_le hL hFm hFi hFL (S n) s)
  calc gaussLaw ι {ω | m + t ≤ F ω}
      ≤ ∫⁻ ω, ENNReal.ofReal (exp (s * (F ω - m))) * ENNReal.ofReal (exp (-(s * t)))
          ∂gaussLaw ι := by
        rw [← lintegral_indicator_one (measurableSet_le measurable_const hFm)]
        refine lintegral_mono fun ω => ?_
        by_cases hω : m + t ≤ F ω
        · rw [indicator_of_mem (show ω ∈ {ω | m + t ≤ F ω} from hω), Pi.one_apply,
            ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
          refine ENNReal.one_le_ofReal.2 (one_le_exp ?_)
          have : s * (F ω - m) + -(s * t) = s * (F ω - m - t) := by ring
          rw [this]
          exact mul_nonneg hs0 (by linarith)
        · rw [indicator_of_notMem (show ω ∉ {ω | m + t ≤ F ω} from hω)]
          exact zero_le
    _ = (∫⁻ ω, ENNReal.ofReal (exp (s * (F ω - m))) ∂gaussLaw ι) *
          ENNReal.ofReal (exp (-(s * t))) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (exp (s ^ 2 * L ^ 2 / 2)) * ENNReal.ofReal (exp (-(s * t))) :=
        by gcongr
    _ = ENNReal.ofReal (exp (-(t ^ 2) / (2 * L ^ 2))) := by
        rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
        congr 2
        rw [hs]
        field_simp
        ring

end LatticeProb.GaussConc
