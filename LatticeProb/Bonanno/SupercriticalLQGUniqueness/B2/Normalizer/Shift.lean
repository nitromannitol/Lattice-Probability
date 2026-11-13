/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Normalizer.Shift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Normalizer.Window
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylBounds
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M7

 










set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Normalizer

open LQGMetric

 

 

def crossingChain (ξ ε : ℝ) (g : DistC) : ℝ≥0∞ :=
  ⨅ (a : LFPP.sideRat 0) (b : LFPP.sideRat 1),
    ⨅ (N : ℕ) (q : Fin N → ↥(LFPP.gaussRat ∩ Blueprint.closedUnitSquare)),
      LFPP.chainCost ξ (heatMollify ε g) a b N q

theorem measurable_crossingChain (ξ ε : ℝ) : Measurable (crossingChain ξ ε) := by
  have := (LFPP.sideRat_countable 0).to_subtype
  have := (LFPP.sideRat_countable 1).to_subtype
  exact Measurable.iInf fun a => Measurable.iInf fun b =>
    LFPP.measurable_iInf_chainCost ξ ε (LFPP.gaussRat_countable.mono inter_subset_left) a b

 
theorem crossingChain_eq_of_heatMollify_eq (ξ ε : ℝ) {g : DistC} {φ : C(ℂ, ℝ)}
    (h : heatMollify ε g = ⇑φ) : crossingChain ξ ε g = lfppCrossingLength ξ φ := by
  unfold crossingChain
  rw [h]
  exact (lfppCrossingLength_eq_chain ξ φ).symm

 

theorem ae_crossingChain_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (ξ ε : ℝ) (hε : 0 < ε) (X : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z))) :
    ∀ᵐ ω ∂P, crossingChain ξ ε (h ω) = lfppCrossingLength ξ (X ω) := by
  obtain ⟨H, hHeq, hHlim⟩ := exists_heatVersion hh ε hε
  filter_upwards [Exponent.HeatVersion.ae_eq_continuous_heat_versions ε hε X H hX hHlim, hHeq]
    with ω hXH hHω
  rw [hXH]
  exact crossingChain_eq_of_heatMollify_eq ξ ε (funext fun z => (hHω z).symm)

 

 
def shiftBump : ContDiffBump (0 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

 
def shiftTest : TestC where
  toFun := shiftBump
  contDiff' := shiftBump.contDiff
  hasCompactSupport' := shiftBump.hasCompactSupport
  tsupport_subset' := subset_univ _

theorem shiftTest_apply (x : ℂ) : shiftTest x = shiftBump x := rfl

 
theorem shiftTest_eq_zero_of_mem_sphere (x : ℂ) (hx : x ∈ Metric.sphere (0 : ℂ) |1|) :
    shiftTest x = 0 := by
  rw [shiftTest_apply]
  refine shiftBump.zero_of_le_dist ?_
  rw [Metric.mem_sphere] at hx
  rw [hx]
  norm_num [shiftBump]

theorem abs_testCont_shiftTest_le (w : ℂ) : |testCont shiftTest w| ≤ 1 := by
  change |shiftBump w| ≤ 1
  rw [abs_of_nonneg shiftBump.nonneg]
  exact shiftBump.le_one

 
def shiftField (ε : ℝ) (hε : ε ≠ 0) : C(ℂ, ℝ) :=
  LFPP.mollCont ε hε (testCont shiftTest) 1 abs_testCont_shiftTest_le

theorem shiftField_apply (ε : ℝ) (hε : ε ≠ 0) (z : ℂ) :
    shiftField ε hε z = heatMollify ε (ofCont (testCont shiftTest)) z := rfl

 
theorem shiftField_pos (ε : ℝ) (hε : ε ≠ 0) (z : ℂ) : 0 < shiftField ε hε z := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  rw [shiftField_apply, heatMollify_ofCont _ 1 abs_testCont_shiftTest_le ε hε z]
  have hp : ∀ w, 0 < heatKernel (ε ^ 2 / 2) z w := fun w => by
    unfold heatKernel; positivity
  have hnn : 0 ≤ fun w => testCont shiftTest w * heatKernel (ε ^ 2 / 2) z w := fun w =>
    mul_nonneg shiftBump.nonneg (hp w).le
  have hint : Integrable fun w => testCont shiftTest w * heatKernel (ε ^ 2 / 2) z w := by
    simpa only [mul_comm] using
      integrable_heatKernel_mul_of_bdd (testCont shiftTest) 1 abs_testCont_shiftTest_le _ hs z
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4))
    (measure_mono fun w hw => ?_)
  rw [Function.mem_support]
  have h1 : testCont shiftTest w = 1 :=
    shiftBump.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
  rw [h1, one_mul]
  exact (hp w).ne'

theorem isCompact_unitSquare : IsCompact unitSquare := by
  have : unitSquare = Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
    ext z
    simp [unitSquare, Complex.mem_reProdIm, and_assoc]
  rw [this]
  exact isCompact_Icc.reProdIm isCompact_Icc

 
theorem exists_shiftField_bounds (ε : ℝ) (hε : ε ≠ 0) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ z ∈ unitSquare, m₀ ≤ shiftField ε hε z ∧ shiftField ε hε z ≤ 1 := by
  obtain ⟨z₀, -, hmin⟩ := isCompact_unitSquare.exists_isMinOn
    ⟨0, by simp [unitSquare]⟩ (shiftField ε hε).continuous.continuousOn
  refine ⟨shiftField ε hε z₀, shiftField_pos ε hε z₀, fun z hz => ⟨hmin hz, ?_⟩⟩
  exact (le_abs_self _).trans
    (LFPP.abs_heatMollify_ofCont_le (testCont shiftTest) abs_testCont_shiftTest_le hε z)

 
theorem heatMollify_addFun_shift {ε : ℝ} (hε : 0 < ε) {g : DistC}
    (hg : TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => g (heatTrunc (ε ^ 2 / 2) z n))
      (heatMollify ε g) atTop ∧ Continuous (heatMollify ε g)) (t : ℝ) :
    heatMollify ε (addFun g (t • testCont shiftTest)) =
      ⇑((⟨heatMollify ε g, hg.2⟩ : C(ℂ, ℝ)) + t • shiftField ε hε.ne') := by
  have hb : ∀ w, |(t • testCont shiftTest) w| ≤ |t| := fun w => by
    rw [ContinuousMap.smul_apply, smul_eq_mul, abs_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_testCont_shiftTest_le w) (abs_nonneg t)
  rw [LFPP.heatMollify_addFun hε.ne'
    (fun z => hg.1.tendsto_comp hg.2.continuousAt tendsto_const_nhds) _ |t| hb]
  funext z
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
    smul_eq_mul, shiftField_apply]
  congr 1
  rw [heatMollify_ofCont _ |t| hb ε hε.ne' z,
    heatMollify_ofCont _ 1 abs_testCont_shiftTest_le ε hε.ne' z, ← integral_const_mul]
  congr 1
  funext w
  rw [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]

 

theorem addFun_shift_neg_shift (t : ℝ) (x : DistC) :
    addFun (addFun x ((-t) • testCont shiftTest)) (t • testCont shiftTest) = x := by
  have h0 : ofCont 0 = 0 := by
    have := CONF.ofCont_add_m1 0 0
    rw [add_zero] at this
    simpa using this
  simp only [addFun, add_assoc, ← CONF.ofCont_add_m1, neg_smul, neg_add_cancel, h0, add_zero]

 

theorem map_shift_ac {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) (t : ℝ) :
    (P.map h).map (fun x => addFun x (t • testCont shiftTest)) ≪ P.map h := by
  have h0 := CONF.ac_shift_normalized hh.1 one_pos 0
    (isNormalizedWholePlaneGFF_iff_old.mp hh).2 shiftTest shiftTest_eq_zero_of_mem_sphere (-t)
  have h1 := h0.map (measurable_addFun_left (t • testCont shiftTest))
  rw [Measure.map_map (measurable_addFun_left _) (measurable_addFun_left _)] at h1
  have hid : ((fun x => addFun x (t • testCont shiftTest)) ∘
      fun x => addFun x ((-t) • testCont shiftTest)) = id :=
    funext fun x => addFun_shift_neg_shift t x
  rwa [hid, Measure.map_id] at h1

 
theorem ae_exists_rat_shift_mem_Ioo {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    {ξ ε : ℝ} (hξ : 0 < ξ) (hε : 0 < ε) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᵐ ω ∂P, ∃ q : ℚ, crossingChain ξ ε (addFun (h ω) ((q : ℝ) • testCont shiftTest)) ∈
      Ioo (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  obtain ⟨m₀, hm₀, hψ⟩ := exists_shiftField_bounds ε hε.ne'
  filter_upwards [hh.1.ae_tendstoLocallyUniformly_heatMollify ε hε.ne'] with ω hω
  obtain ⟨q, hq⟩ := exists_rat_lfppCrossingLength_mem_Ioo hξ
    ⟨heatMollify ε (h ω), hω.2⟩ (shiftField ε hε.ne') hm₀ hψ ha hab
  refine ⟨q, ?_⟩
  rw [crossingChain_eq_of_heatMollify_eq ξ ε (heatMollify_addFun_shift hε hω q)]
  exact hq

 
theorem map_pos_of_ae_exists_rat_shift {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    {A : Set DistC} (hA : MeasurableSet A)
    (hcover : ∀ᵐ ω ∂P, ∃ q : ℚ, addFun (h ω) ((q : ℝ) • testCont shiftTest) ∈ A) :
    P.map h A ≠ 0 := by
  have hex : ∃ q : ℚ,
      P ((fun ω => addFun (h ω) ((q : ℝ) • testCont shiftTest)) ⁻¹' A) ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    have hnull : ∀ᵐ ω ∂P, ∀ q : ℚ, addFun (h ω) ((q : ℝ) • testCont shiftTest) ∉ A :=
      ae_all_iff.2 fun q => measure_eq_zero_iff_ae_notMem.1 (hne q)
    have : (ae P).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero P)
    obtain ⟨ω, ⟨q, hq⟩, hn⟩ := (hcover.and hnull).exists
    exact hn q hq
  obtain ⟨q, hq⟩ := hex
  have hm : Measurable fun x : DistC => addFun x ((q : ℝ) • testCont shiftTest) :=
    measurable_addFun_left _
  have hmapS : P ((fun ω => addFun (h ω) ((q : ℝ) • testCont shiftTest)) ⁻¹' A) =
      ((P.map h).map fun x => addFun x ((q : ℝ) • testCont shiftTest)) A := by
    rw [Measure.map_apply hm hA, Measure.map_apply hh.1.measurable (hm hA)]
    rfl
  intro h0
  exact hq (hmapS.trans (map_shift_ac hh q h0))

 

theorem measure_lfppCrossingLength_mem_Ioo_pos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    {ξ ε : ℝ} (hξ : 0 < ξ) (hε : 0 < ε) (X : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < P {ω | ENNReal.ofReal a < lfppCrossingLength ξ (X ω) ∧
      lfppCrossingLength ξ (X ω) < ENNReal.ofReal b} := by
  have hA : MeasurableSet (crossingChain ξ ε ⁻¹' Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) :=
    measurable_crossingChain ξ ε measurableSet_Ioo
  have hμA := map_pos_of_ae_exists_rat_shift hh hA
    (ae_exists_rat_shift_mem_Ioo hh hξ hε ha hab)
  rw [Measure.map_apply hh.1.measurable hA] at hμA
  
  have hset : (h ⁻¹' (crossingChain ξ ε ⁻¹' Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) :
      Set Ω) =ᵐ[P] {ω | ENNReal.ofReal a < lfppCrossingLength ξ (X ω) ∧
        lfppCrossingLength ξ (X ω) < ENNReal.ofReal b} := by
    filter_upwards [ae_crossingChain_eq hh ξ ε hε X hX] with ω hω
    simp only [mem_preimage, mem_Ioo, hω]
  rw [← measure_congr hset]
  exact pos_iff_ne_zero.2 hμA

end SupercriticalLQGUniqueness.B2.Normalizer
