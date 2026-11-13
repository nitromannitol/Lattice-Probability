/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.Measurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# M4-R5 (measurability): the LQG measures are measurable functions of good samples

For a good sample `x` (`IsLQGGood γ x`), `qBoundaryMeasure γ x` and `qAreaMeasure γ x` are the
limits of the approximations `bdryApprox γ x k`, `areaApprox γ x k` (radius `2^{-k}`). Hence:

* for a continuous compactly supported `f`, `∫ f d(qBoundaryMeasure γ x)` agrees on good samples
  with the measurable function `liminf_k ∫ f d(bdryApprox γ x k)` (`bdryFun`), and similarly on
  `ℍ` (`areaFun`, for `tsupport f ⊆ H`);
* the measure of a bounded open set is a countable supremum of such integrals (`openBump`);
* a Dynkin (`π`–`λ`) argument on the finite-measure pieces `s ∩ V N` upgrades this to
  measurability into `Measure` with the Giry `σ`-algebra, on the subtype of good samples
  (`measurable_qBoundaryMeasure_good`, `measurable_qAreaMeasure_good`);
* `scaleParam` is an `sInf` of an up-closed set of radii tested at rationals
  (`measurable_scaleParam_good`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace LQGMeas

/-! ## Integrals against the approximating measures are measurable -/

theorem meas_integral_bdryApprox (γ : ℝ) (k : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun x : FieldSample => ∫ t, f t ∂bdryApprox γ x k := by
  let D : FieldSample × ℝ → ℝ := fun p =>
    radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg p.1 k (p.2 : ℂ))
  have hDm : Measurable D :=
    (Real.measurable_exp.comp (((measurable_avgReg k).comp
      (measurable_fst.prodMk (Complex.continuous_ofReal.measurable.comp measurable_snd))).const_mul
        (γ / 2))).const_mul _
  have hD0 : ∀ p, 0 ≤ D p := fun p =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have heq : ∀ x : FieldSample, ∫ t, f t ∂bdryApprox γ x k = ∫ t, D (x, t) * f t := fun x =>
    GoodSample.integral_withDensity_ofReal (hDm.comp (measurable_const.prodMk measurable_id))
      (fun t => hD0 _) f
  simp_rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (f := fun p : FieldSample × ℝ => D p * f p.2)
    (hDm.mul (hf.comp measurable_snd)).stronglyMeasurable).measurable

theorem meas_integral_areaApprox (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun x : FieldSample => ∫ z, f z ∂areaApprox γ x k := by
  let D : FieldSample × ℂ → ℝ := fun p =>
    radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg p.1 k p.2)
  have hDm : Measurable D :=
    (Real.measurable_exp.comp ((measurable_avgReg k).const_mul γ)).const_mul _
  have hD0 : ∀ p, 0 ≤ D p := fun p =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have heq : ∀ x : FieldSample,
      ∫ z, f z ∂areaApprox γ x k = ∫ z, D (x, z) * f z ∂(volume.restrict H) := fun x =>
    GoodSample.integral_withDensity_ofReal (μ := volume.restrict H)
      (hDm.comp (measurable_const.prodMk measurable_id)) (fun z => hD0 _) f
  simp_rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (ν := volume.restrict H)
    (f := fun p : FieldSample × ℂ => D p * f p.2)
    (hDm.mul (hf.comp measurable_snd)).stronglyMeasurable).measurable

/-! ## Convergence of the approximations on good samples -/

theorem tendsto_bdryApprox_of_good {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun k => ∫ t, f t ∂bdryApprox γ x k) atTop
      (𝓝 (∫ t, f t ∂qBoundaryMeasure γ x)) := by
  obtain ⟨F, hF⟩ := hx.1
  have := (hx.qBoundaryMeasure_spec.2 f hf hfc).comp GoodSample.tendsto_one_goodFilter
  refine this.congr fun k => ?_
  simp only [Function.comp, goodRad, GoodSample.bdryR_radius γ hF]

theorem tendsto_areaApprox_of_good {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    Tendsto (fun k => ∫ z, f z ∂areaApprox γ x k) atTop
      (𝓝 (∫ z, f z ∂qAreaMeasure γ x)) := by
  obtain ⟨F, hF⟩ := hx.1
  have := (hx.qAreaMeasure_spec.2.2 f hf hfc hfH).comp GoodSample.tendsto_one_goodFilter
  refine this.congr fun k => ?_
  simp only [Function.comp, goodRad, GoodSample.areaR_radius γ hF]

/-- The measurable candidate for `∫ f d(qBoundaryMeasure γ x)`. -/
def bdryFun (γ : ℝ) (f : ℝ → ℝ) (x : FieldSample) : ℝ :=
  liminf (fun k => ∫ t, f t ∂bdryApprox γ x k) atTop

/-- The measurable candidate for `∫ f d(qAreaMeasure γ x)`. -/
def areaFun (γ : ℝ) (f : ℂ → ℝ) (x : FieldSample) : ℝ :=
  liminf (fun k => ∫ z, f z ∂areaApprox γ x k) atTop

theorem measurable_bdryFun (γ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (bdryFun γ f) :=
  Measurable.liminf (f := fun k x => ∫ t, f t ∂bdryApprox γ x k)
    fun k => meas_integral_bdryApprox γ k hf

theorem measurable_areaFun (γ : ℝ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable (areaFun γ f) :=
  Measurable.liminf (f := fun k x => ∫ z, f z ∂areaApprox γ x k)
    fun k => meas_integral_areaApprox γ k hf

theorem bdryFun_eq {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    bdryFun γ f x = ∫ t, f t ∂qBoundaryMeasure γ x :=
  (tendsto_bdryApprox_of_good hx hf hfc).liminf_eq

theorem areaFun_eq {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    areaFun γ f x = ∫ z, f z ∂qAreaMeasure γ x :=
  (tendsto_areaApprox_of_good hx hf hfc hfH).liminf_eq

/-! ## Open sets as countable suprema of test functions -/

section OpenApprox

variable {α : Type*} [MetricSpace α]

/-- Continuous cut-offs increasing to the indicator of `U`, supported in `U`. -/
def openBump (U : Set α) (n : ℕ) (z : α) : ℝ :=
  min 1 (max 0 ((n : ℝ) * Metric.infDist z Uᶜ - 1))

theorem continuous_openBump (U : Set α) (n : ℕ) : Continuous (openBump U n) :=
  continuous_const.min (continuous_const.max
    ((continuous_const.mul (Metric.continuous_infDist_pt _)).sub continuous_const))

theorem openBump_nonneg (U : Set α) (n : ℕ) (z : α) : 0 ≤ openBump U n z :=
  le_min zero_le_one (le_max_left _ _)

theorem openBump_le_one (U : Set α) (n : ℕ) (z : α) : openBump U n z ≤ 1 := min_le_left _ _

theorem openBump_mono (U : Set α) (z : α) : Monotone fun n => openBump U n z := by
  intro m n hmn
  have hd := Metric.infDist_nonneg (x := z) (s := Uᶜ)
  have : (m : ℝ) * Metric.infDist z Uᶜ ≤ n * Metric.infDist z Uᶜ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hd
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

theorem support_openBump_subset (U : Set α) (n : ℕ) :
    Function.support (openBump U n) ⊆ {z | 1 ≤ (n : ℝ) * Metric.infDist z Uᶜ} := by
  intro z hz
  simp only [mem_ofPred_eq]
  by_contra h
  rw [not_le] at h
  apply hz
  simp only [openBump]
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem setOf_one_le_infDist_subset (U : Set α) (n : ℕ) :
    {z | 1 ≤ (n : ℝ) * Metric.infDist z Uᶜ} ⊆ U := by
  intro z hz
  by_contra h
  simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem (show z ∈ Uᶜ from h), mul_zero] at hz
  linarith

theorem tsupport_openBump_subset (U : Set α) (n : ℕ) : tsupport (openBump U n) ⊆ U :=
  (closure_minimal (support_openBump_subset U n) (isClosed_le continuous_const
    (continuous_const.mul (Metric.continuous_infDist_pt _)))).trans
    (setOf_one_le_infDist_subset U n)

theorem hasCompactSupport_openBump [ProperSpace α] {U : Set α} (hU : Bornology.IsBounded U) (n : ℕ) :
    HasCompactSupport (openBump U n) :=
  hU.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_openBump_subset U n).trans subset_closure)

theorem iSup_openBump {U : Set α} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) (z : α) :
    ⨆ n : ℕ, ENNReal.ofReal (openBump U n z) = U.indicator 1 z := by
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz, Pi.one_apply]
    refine le_antisymm (iSup_le fun n => ?_) ?_
    · exact ENNReal.ofReal_le_one.2 (openBump_le_one U n z)
    · have hd : 0 < Metric.infDist z Uᶜ :=
        (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h hz)
      obtain ⟨n, hn⟩ := exists_nat_gt (2 / Metric.infDist z Uᶜ)
      refine le_iSup_of_le n (le_of_eq ?_)
      have h2 : 2 ≤ (n : ℝ) * Metric.infDist z Uᶜ := by
        rw [div_lt_iff₀ hd] at hn; linarith
      rw [openBump, max_eq_right (by linarith), min_eq_left (by linarith), ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]
    refine le_antisymm (iSup_le fun n => ?_) zero_le
    have : openBump U n z = 0 := by
      by_contra h
      exact hz (tsupport_openBump_subset U n (subset_tsupport _ h))
    rw [this, ENNReal.ofReal_zero]

theorem measure_open_eq_iSup [MeasurableSpace α] [BorelSpace α] (μ : Measure α) {U : Set α} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    μ U = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (openBump U n z) ∂μ := by
  rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (openBump U n z))
    (fun n => ENNReal.measurable_ofReal.comp (continuous_openBump U n).measurable)
    (fun m n hmn z => ENNReal.ofReal_le_ofReal (openBump_mono U z hmn)),
    ← lintegral_indicator_one hU.measurableSet]
  congr 1
  funext z
  exact (iSup_openBump hU hUc z).symm

end OpenApprox

/-! ## Measures of open sets on good samples -/

theorem measurable_qBoundaryMeasure_open (γ : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Uᶜ.Nonempty) :
    Measurable fun x : {x // IsLQGGood γ x} => qBoundaryMeasure γ x.1 U := by
  have key : ∀ x : {x // IsLQGGood γ x}, qBoundaryMeasure γ x.1 U =
      ⨆ n : ℕ, ENNReal.ofReal (bdryFun γ (openBump U n) x.1) := by
    intro x
    rw [measure_open_eq_iSup _ hU hUc]
    congr 1
    funext n
    have := x.2.qBoundaryMeasure_spec.1
    rw [bdryFun_eq x.2 (continuous_openBump U n) (hasCompactSupport_openBump hUb n),
      ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun z => openBump_nonneg U n z)]
    exact (continuous_openBump U n).integrable_of_hasCompactSupport
      (hasCompactSupport_openBump hUb n)
  simp_rw [key]
  exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    ((measurable_bdryFun γ (continuous_openBump U n).measurable).comp measurable_subtype_coe)

theorem measurable_qAreaMeasure_open (γ : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUH : U ⊆ H) :
    Measurable fun x : {x // IsLQGGood γ x} => qAreaMeasure γ x.1 U := by
  have hUc : Uᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hUH h⟩
  have key : ∀ x : {x // IsLQGGood γ x}, qAreaMeasure γ x.1 U =
      ⨆ n : ℕ, ENNReal.ofReal (areaFun γ (openBump U n) x.1) := by
    intro x
    rw [measure_open_eq_iSup _ hU hUc]
    congr 1
    funext n
    have hsupp := (tsupport_openBump_subset U n).trans hUH
    rw [areaFun_eq x.2 (continuous_openBump U n) (hasCompactSupport_openBump hUb n) hsupp,
      ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun z => openBump_nonneg U n z)]
    exact GoodSample.integrable_of_tsupport x.2.qAreaMeasure_spec.2.1 (continuous_openBump U n)
      (hasCompactSupport_openBump hUb n) hsupp
  simp_rw [key]
  exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    ((measurable_areaFun γ (continuous_openBump U n).measurable).comp measurable_subtype_coe)

/-! ## A Dynkin argument: measurability into `Measure` from open sets -/

theorem measurable_measure_of_open {X α : Type*} [MeasurableSpace X] [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] (M : X → Measure α) (V : ℕ → Set α)
    (hVm : ∀ N, MeasurableSet (V N)) (hVmono : Monotone V)
    (hnull : ∀ x, M x (⋃ N, V N)ᶜ = 0) (hfin : ∀ x N, M x (V N) ≠ ⊤)
    (hopen : ∀ (U : Set α) (N : ℕ), IsOpen U → Measurable fun x => M x (U ∩ V N)) :
    Measurable M := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hN : ∀ N, ∀ t, MeasurableSet t → Measurable fun x => M x (t ∩ V N) := by
    intro N t ht
    induction t, ht using MeasurableSpace.induction_on_inter
      (h_eq := BorelSpace.measurable_eq) (h_inter := @isPiSystem_isOpen α _) with
    | empty => simp only [empty_inter, measure_empty]; exact measurable_const
    | basic t ht => exact hopen t N ht
    | compl t htm iht =>
      have hV : Measurable fun x => M x (V N) := by
        simpa only [univ_inter] using hopen univ N isOpen_univ
      have heq : ∀ x, M x (tᶜ ∩ V N) = M x (V N) - M x (t ∩ V N) := by
        intro x
        have : tᶜ ∩ V N = V N \ (t ∩ V N) := by ext; simp; tauto
        rw [this, measure_sdiff inter_subset_right (htm.inter (hVm N)).nullMeasurableSet
          (ne_top_of_le_ne_top (hfin x N) (measure_mono inter_subset_right))]
      simp_rw [heq]
      exact hV.sub iht
    | iUnion f hd hfm ih =>
      have heq : ∀ x, M x ((⋃ i, f i) ∩ V N) = ∑' i, M x (f i ∩ V N) := by
        intro x
        rw [iUnion_inter, measure_iUnion
          (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
          (fun i => (hfm i).inter (hVm N))]
      simp_rw [heq]
      exact Measurable.ennreal_tsum ih
  have heq : ∀ x, M x s = ⨆ N, M x (s ∩ V N) := by
    intro x
    rw [← measure_inter_conull (s := s) (hnull x), inter_iUnion]
    exact Monotone.measure_iUnion fun m n hmn => inter_subset_inter_right _ (hVmono hmn)
  simp_rw [heq]
  exact Measurable.iSup fun N => hN N s hs

/-! ## Giry measurability of the LQG measures on good samples -/

/-- **M4-R5 (2), boundary.** On good samples, `x ↦ qBoundaryMeasure γ x` is measurable into
`Measure ℝ` (Giry `σ`-algebra). -/
theorem measurable_qBoundaryMeasure_good (γ : ℝ) :
    Measurable fun x : {x // IsLQGGood γ x} => qBoundaryMeasure γ x.1 := by
  refine measurable_measure_of_open _ (fun N => Ioo (-(N : ℝ)) N) (fun N => measurableSet_Ioo)
    (fun m n hmn => Ioo_subset_Ioo (by simpa using hmn) (by exact_mod_cast hmn))
    (fun x => ?_) (fun x N => ?_) (fun U N hU => ?_)
  · have : (⋃ N : ℕ, Ioo (-(N : ℝ)) N) = univ := by
      refine eq_univ_of_forall fun t => mem_iUnion.2 ?_
      obtain ⟨N, hN⟩ := exists_nat_gt |t|
      exact ⟨N, abs_lt.1 hN⟩
    rw [this, compl_univ, measure_empty]
  · have := x.2.qBoundaryMeasure_spec.1
    exact measure_Ioo_lt_top.ne
  · refine measurable_qBoundaryMeasure_open γ (hU.inter isOpen_Ioo)
      (Metric.isBounded_Ioo _ _ |>.subset inter_subset_right) ⟨N, fun h => ?_⟩
    exact lt_irrefl _ h.2.2

/-- The exhaustion of `ℍ` by open sets with compact closure in `ℍ`. -/
def hExh (N : ℕ) : Set ℂ := {z | ‖z‖ < N ∧ 1 / ((N : ℝ) + 1) < z.im}

theorem isOpen_hExh (N : ℕ) : IsOpen (hExh N) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem hExh_mono : Monotone hExh := by
  intro m n hmn z hz
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  refine ⟨hz.1.trans_le hmn', lt_of_le_of_lt ?_ hz.2⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem H_subset_iUnion_hExh : H ⊆ ⋃ N, hExh N := by
  intro z hz
  have him : 0 < z.im := hz
  obtain ⟨N, hN⟩ := exists_nat_gt (max ‖z‖ (1 / z.im))
  refine mem_iUnion.2 ⟨N, (le_max_left _ _).trans_lt hN, ?_⟩
  have h1 : 1 / z.im < N := (le_max_right _ _).trans_lt hN
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) h1
  rw [div_lt_iff₀ him] at h1
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem hExh_subset_compact (N : ℕ) :
    hExh N ⊆ Metric.closedBall 0 N ∩ {z : ℂ | 1 / ((N : ℝ) + 1) ≤ z.im} :=
  fun z hz => ⟨by simpa using hz.1.le, hz.2.le⟩

theorem isCompact_hExhK (N : ℕ) :
    IsCompact (Metric.closedBall (0 : ℂ) N ∩ {z : ℂ | 1 / ((N : ℝ) + 1) ≤ z.im}) :=
  (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)

theorem hExhK_subset_H (N : ℕ) :
    Metric.closedBall (0 : ℂ) N ∩ {z : ℂ | 1 / ((N : ℝ) + 1) ≤ z.im} ⊆ H :=
  fun z hz => (show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity).trans_le hz.2

/-- **M4-R5 (2), area.** On good samples, `x ↦ qAreaMeasure γ x` is measurable into
`Measure ℂ` (Giry `σ`-algebra). -/
theorem measurable_qAreaMeasure_good (γ : ℝ) :
    Measurable fun x : {x // IsLQGGood γ x} => qAreaMeasure γ x.1 := by
  refine measurable_measure_of_open _ hExh (fun N => (isOpen_hExh N).measurableSet) hExh_mono
    (fun x => ?_) (fun x N => ?_) (fun U N hU => ?_)
  · exact measure_mono_null (compl_subset_compl.2 H_subset_iUnion_hExh)
      x.2.qAreaMeasure_spec.1
  · exact (lt_of_le_of_lt (measure_mono (hExh_subset_compact N))
      (x.2.qAreaMeasure_spec.2.1 _ (isCompact_hExhK N) (hExhK_subset_H N))).ne
  · refine measurable_qAreaMeasure_open γ (hU.inter (isOpen_hExh N)) ?_
      (inter_subset_right.trans ((hExh_subset_compact N).trans (hExhK_subset_H N)))
    exact (isCompact_hExhK N).isBounded.subset (inter_subset_right.trans (hExh_subset_compact N))

theorem measurable_qAreaMeasure_apply_good (γ : ℝ) {s : Set ℂ} (hs : MeasurableSet s) :
    Measurable fun x : {x // IsLQGGood γ x} => qAreaMeasure γ x.1 s :=
  (Measure.measurable_coe hs).comp (measurable_qAreaMeasure_good γ)

/-! ## `scaleParam` -/

/-- The infimum of an up-closed set of positive reals is measurable if membership of each
rational is. -/
theorem measurable_sInf_upClosed {X : Type*} [MeasurableSpace X] (S : X → Set ℝ)
    (hS : ∀ q : ℚ, MeasurableSet {x | (q : ℝ) ∈ S x})
    (hup : ∀ x a b, a ∈ S x → a ≤ b → b ∈ S x) (hpos : ∀ x a, a ∈ S x → 0 < a) :
    Measurable fun x => sInf (S x) := by
  refine measurable_of_Iio fun c => ?_
  have key : (fun x => sInf (S x)) ⁻¹' Iio c =
      {x | 0 < c} ∩ ((⋂ q : ℚ, {x | (q : ℝ) ∈ S x}ᶜ) ∪
        ⋃ q : ℚ, {x | (q : ℝ) < c} ∩ {x | (q : ℝ) ∈ S x}) := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_inter_iff, mem_ofPred_eq, mem_union, mem_iInter,
      mem_iUnion, mem_compl_iff]
    by_cases hne : (S x).Nonempty
    · have hbdd : BddBelow (S x) := ⟨0, fun a ha => (hpos x a ha).le⟩
      rw [csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨a, ha, hac⟩
        obtain ⟨q, haq, hqc⟩ := exists_rat_btwn hac
        exact ⟨(hpos x a ha).trans (haq.trans hqc), Or.inr ⟨q, hqc, hup x a q ha haq.le⟩⟩
      · rintro ⟨-, h | ⟨q, hqc, hq⟩⟩
        · obtain ⟨a, ha⟩ := hne
          obtain ⟨q, hq⟩ := exists_rat_gt a
          exact absurd (hup x a q ha hq.le) (h q)
        · exact ⟨q, hq, hqc⟩
    · rw [not_nonempty_iff_eq_empty.1 hne, Real.sInf_empty]
      simp
  rw [key]
  exact (MeasurableSet.const _).inter ((MeasurableSet.iInter fun q => (hS q).compl).union
    (MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hS q)))

/-- **M4-R5 (2), scale parameter.** On good samples, `x ↦ scaleParam γ x` is measurable. -/
theorem measurable_scaleParam_good (γ : ℝ) :
    Measurable fun x : {x // IsLQGGood γ x} => scaleParam γ x.1 := by
  let m : {x // IsLQGGood γ x} → ℝ → ℝ≥0∞ := fun x a =>
    qAreaMeasure γ x.1 (Metric.ball (0 : ℂ) a ∩ H)
  have hm : ∀ a, Measurable fun x => m x a := fun a =>
    measurable_qAreaMeasure_apply_good γ
      (Metric.isOpen_ball.measurableSet.inter isOpen_H.measurableSet)
  have hS : ∀ q : ℚ, MeasurableSet {x | (q : ℝ) ∈ {a : ℝ | 0 < a ∧ 1 ≤ m x a}} := fun q =>
    (MeasurableSet.const (0 < (q : ℝ))).inter (measurableSet_le measurable_const (hm q))
  have hup : ∀ x a b, a ∈ {a : ℝ | 0 < a ∧ 1 ≤ m x a} → a ≤ b →
      b ∈ {a : ℝ | 0 < a ∧ 1 ≤ m x a} :=
    fun x a b ha hab => ⟨ha.1.trans_le hab, ha.2.trans (measure_mono
      (inter_subset_inter_left _ (Metric.ball_subset_ball hab)))⟩
  exact measurable_sInf_upClosed (fun x => {a : ℝ | 0 < a ∧ 1 ≤ m x a}) hS hup
    (fun x a ha => ha.1)

/-! ## Global versions, conditional on the measurability of the good set -/

open Classical in
theorem measurable_qBoundaryMeasure_of_measurableSet (γ : ℝ)
    (hG : MeasurableSet {x : FieldSample | IsLQGGood γ x}) :
    Measurable fun x => if IsLQGGood γ x then qBoundaryMeasure γ x else 0 := by
  convert Measurable.dite (s := {x : FieldSample | IsLQGGood γ x})
    (f := fun x => qBoundaryMeasure γ x.1) (measurable_qBoundaryMeasure_good γ)
    (g := fun _ => (0 : Measure ℝ)) measurable_const hG using 1
  funext x
  by_cases h : IsLQGGood γ x <;> simp [h]

open Classical in
theorem measurable_qAreaMeasure_of_measurableSet (γ : ℝ)
    (hG : MeasurableSet {x : FieldSample | IsLQGGood γ x}) :
    Measurable fun x => if IsLQGGood γ x then qAreaMeasure γ x else 0 := by
  convert Measurable.dite (s := {x : FieldSample | IsLQGGood γ x})
    (f := fun x => qAreaMeasure γ x.1) (measurable_qAreaMeasure_good γ)
    (g := fun _ => (0 : Measure ℂ)) measurable_const hG using 1
  funext x
  by_cases h : IsLQGGood γ x <;> simp [h]

open Classical in
theorem measurable_scaleParam_of_measurableSet (γ : ℝ)
    (hG : MeasurableSet {x : FieldSample | IsLQGGood γ x}) :
    Measurable fun x => if IsLQGGood γ x then scaleParam γ x else 0 := by
  convert Measurable.dite (s := {x : FieldSample | IsLQGGood γ x})
    (f := fun x => scaleParam γ x.1) (measurable_scaleParam_good γ)
    (g := fun _ => (0 : ℝ)) measurable_const hG using 1
  funext x
  by_cases h : IsLQGGood γ x <;> simp [h]

/-! ## First reduction towards M4-R5 (1): the canonical regularity witness -/

end LQGMeas

end QuantumZipper
