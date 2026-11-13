/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.AreaTestL1 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: UniformIntegrable no longer contains the measurability of the family.
   Changed for Lean v4.35: eLpNorm_eq_lintegral_rpow_enorm_toReal and eLpNorm_eq_eLpNorm' take the measurability argument, eLpNorm_le_eLpNorm_of_exponent_le no longer does.
   Changed for Lean v4.35: the measurability argument of tendsto_integral_of_L1' (dropped from its signature) removed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.UniformIntegrability
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.WeightedMoment
import Mathlib.MeasureTheory.Function.UnifTight

/-!
# L¹ convergence of LQG approximation tests from uniform disk moments

For compactly supported continuous tests in the open unit disk, the checked uniform moment bound
on the approximating disk masses gives uniform integrability. The almost sure vague convergence
in `IsLQGAreaOf` then upgrades to convergence in L¹.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMSLemma27
open MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {H : ℝ → ℂ → Ω → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}

/-- A test integral against the `k`th LQG approximation. -/
def approxTestIntegral (f : ℂ → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∫ z, f z ∂(MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω)

/-- The same test integral against the limiting LQG area. -/
def areaTestIntegral (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z, f z ∂(μ ω)

/-- The approximation test integral is measurable in the sample. -/
lemma measurable_approxTestIntegral
    (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (f : ℂ → ℝ) (hf : Continuous f) (k : ℕ) :
    Measurable (approxTestIntegral (γ := γ) (H := H) f k) := by
  have hr : 0 < MatedCRTHarmonic.GMSLemma27.dyadicRadius k := by
    rw [MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius]
    exact QuantumZipper.radius_pos k
  have hj := measurable_uncurry_coord hH hHm hr
  let d : ℂ × Ω → ℝ := fun p =>
    MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) p.1 p.2)
  have hd : Measurable d := by
    dsimp [d]
    exact measurable_const.mul ((hj.const_mul γ).exp)
  have hm : StronglyMeasurable (fun p : ℂ × Ω => d p * f p.1) :=
    (hd.mul (hf.measurable.comp measurable_fst)).stronglyMeasurable
  have hEq : approxTestIntegral (γ := γ) (H := H) f k = fun ω =>
      ∫ z, d (z, ω) * f z := by
    funext ω
    rw [approxTestIntegral, MatedCRTHarmonic.GMSLemma27.lqgApprox,
      integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with z
      simp only [smul_eq_mul, d]
      rw [ENNReal.toReal_ofReal (by positivity)]
    · exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul
          (Real.continuous_exp.comp ((hH.continuous _ hr ω).const_mul γ)).measurable)
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [hEq]
  exact (hm.integral_prod_left' (μ := (volume : Measure ℂ))).measurable

/-- On a probability space, a uniform finite `L^q` bound for some `q > 1` gives uniform
integrability in `L¹`. -/
lemma uniformIntegrable_one_of_uniform_eLpNorm_gt_one
    [IsProbabilityMeasure P] {F : ℕ → Ω → ℝ} {q C : ℝ≥0∞}
    (hq : 1 < q) (hqtop : q < ⊤) (hCtop : C < ⊤)
    (hF : ∀ k, AEStronglyMeasurable (F k) P)
    (hbound : ∀ k, eLpNorm (F k) q P ≤ C) :
    UniformIntegrable F 1 P := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hqt : q ≠ ⊤ := ne_of_lt hqtop
  have hqR1 : 1 < q.toReal := by
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqt).2 hq
  have ha : 0 < 1 - 1 / q.toReal := by
    have hqp : 0 < q.toReal := (ENNReal.toReal_pos hq0 hqt)
    have : 1 / q.toReal < 1 := (div_lt_one hqp).2 hqR1
    linarith
  have hui : UnifIntegrable F 1 P := by
    apply unifIntegrable_iff.2
    intro ε hε
    by_cases hεtop : ε = ⊤
    · refine ⟨1, by norm_num, fun k s hμs => ?_⟩
      rw [hεtop]
      exact le_top
    let a : ℝ := 1 - 1 / q.toReal
    let δ : ℝ≥0∞ := (ε / (C + 1)) ^ (1 / a)
    have ha' : a = 1 - 1 / q.toReal := rfl
    have hbase_top : ε / (C + 1) ≠ ⊤ := by finiteness
    have hden_top : C + 1 ≠ ⊤ := by finiteness
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact ENNReal.rpow_pos (ENNReal.div_pos hε.ne' hden_top) hbase_top
    refine ⟨δ, hδpos, fun k s hμs => ?_⟩
    let ν : Measure Ω := P.restrict s
    have hνle : ν ≤ P := by
      dsimp [ν]
      exact Measure.restrict_le_self
    have hFν : AEStronglyMeasurable (F k) ν := (hF k).mono_measure hνle
    have hqcomp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := ν) (p := (1 : ℝ≥0∞)) (q := q) (le_of_lt hq) hFν
    have hmass : ν Set.univ ≤ δ := by
      dsimp [ν]
      rw [Measure.restrict_apply_univ]
      exact hμs
    have hcomp : eLpNorm (F k) 1 ν ≤ C * δ ^ a := by
      calc
        eLpNorm (F k) 1 ν ≤
            eLpNorm (F k) q ν * ν Set.univ ^ a := by
              convert hqcomp using 1 <;> simp [a]
        _ ≤ C * δ ^ a := by
              exact mul_le_mul
                ((eLpNorm_mono_measure (F k) hνle).trans (hbound k))
                (ENNReal.rpow_le_rpow hmass (le_of_lt ha))
                (by positivity) (by positivity)
    calc
      eLpNorm (F k) 1 ν ≤ C * δ ^ a := hcomp
      _ = C * (ε / (C + 1)) := by
        dsimp [δ]
        rw [← ENNReal.rpow_mul]
        have hexp : 1 / a * a = 1 := div_mul_cancel₀ 1 ha.ne'
        rw [hexp, ENNReal.rpow_one]
      _ ≤ ε := by
        calc
          C * (ε / (C + 1)) ≤ (C + 1) * (ε / (C + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (by positivity)) (by positivity)
          _ = ε := ENNReal.mul_div_cancel (by positivity) hden_top
  refine ⟨hui, ?_⟩
  refine ⟨C.toNNReal, fun k => ?_⟩
  have hcomp := eLpNorm_le_eLpNorm_of_exponent_le (f := F k) (μ := P) (le_of_lt hq)
  exact hcomp.trans (by simpa [ENNReal.coe_toNNReal hCtop.ne] using hbound k)

/-- Compact support follows from containment of the topological support in the unit disk. -/
lemma hasCompactSupport_of_tsupport_subset_unitDisk {f : ℂ → ℝ}
    (hfs : tsupport f ⊆ ball (0 : ℂ) 1) : HasCompactSupport f := by
  change IsCompact (tsupport f)
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport f)
    (Metric.isBounded_ball.subset hfs)

/-- A test supported in the unit disk is bounded by its supremum times the approximating
unit-disk mass. -/
lemma approxTestIntegral_abs_le_diskMass
    (hH : LQGDimension.IsGFFCircleAverage H P) (f : ℂ → ℝ)
    (hfs : tsupport f ⊆ ball (0 : ℂ) 1) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z, ‖f z‖ ≤ B) (k : ℕ) (ω : Ω) :
    |approxTestIntegral (γ := γ) (H := H) f k ω| ≤
      B * (MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
        (ball (0 : ℂ) 1)).toReal := by
  let ν := MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
  letI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_lqgApprox hH γ k ω
  have hmass_top : ν (ball (0 : ℂ) 1) ≠ ⊤ := measure_ball_ne_top
  haveI : IsFiniteMeasure (ν.restrict (ball (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr hmass_top
  have hzero : ∀ z, z ∉ ball (0 : ℂ) 1 → f z = 0 := by
    intro z hz
    have hnot : z ∉ tsupport f := fun h => hz (hfs h)
    exact image_eq_zero_of_notMem_tsupport hnot
  have hset : ∫ z in ball (0 : ℂ) 1, f z ∂ν = ∫ z, f z ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hnorm := norm_integral_le_of_norm_le_const (μ := ν.restrict (ball (0 : ℂ) 1))
    (C := B) (ae_of_all _ fun z => hB z)
  unfold approxTestIntegral
  rw [← hset]
  simpa [Real.norm_eq_abs, measureReal_restrict_apply_univ, Measure.real, ν] using hnorm

/-- A uniform higher moment of the unit-disk approximating masses makes every compactly
supported test integral whose support lies in the open unit disk uniformly integrable. -/
theorem uniformIntegrable_approxTestIntegral
    (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ ball (0 : ℂ) 1) :
    UniformIntegrable
      (fun k ω => approxTestIntegral (γ := γ) (H := H) f k ω) 1 P := by
  letI : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_unitDisk hfs
  obtain ⟨B₀, hB₀⟩ := hfc.exists_bound_of_continuousOn hf.norm.continuousOn
  let B : ℝ := max B₀ 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ z, ‖f z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ tsupport f
    · have hzB : ‖f z‖ ≤ B₀ := by simpa using hB₀ z hz
      exact hzB.trans (le_max_left _ _)
    · simpa [B, image_eq_zero_of_notMem_tsupport hz]
  obtain ⟨hp, C, hCtop, hmoment⟩ :=
    exists_unitDisk_approx_moment hH hHm hγ hγ2
  let p : ℝ := unitApproxMomentP γ
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hp1 : 1 < p := by simpa [p] using hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact (ENNReal.ofReal_pos.mpr hp0).ne'
  have hqtop : q < ⊤ := by dsimp [q]; exact ENNReal.ofReal_lt_top
  have hqreal : q.toReal = p := by simp [q, hp0.le]
  have hq1 : 1 < q := by
    change 1 < ENNReal.ofReal p
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff hp0).2 hp1
  let X : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω (ball (0 : ℂ) 1)
  have hXm : ∀ k, Measurable (X k) := by
    intro k
    exact measurable_lqgApprox_set hH hHm γ k measurableSet_ball
  have hXae : ∀ k, AEStronglyMeasurable (X k) P := fun k => (hXm k).aestronglyMeasurable
  have hF : ∀ k, AEStronglyMeasurable
      (approxTestIntegral (γ := γ) (H := H) f k) P := by
    intro k
    exact (measurable_approxTestIntegral hH hHm f hf k).aestronglyMeasurable
  have hmassLp : ∀ k, eLpNorm (X k) q P ≤ C ^ (1 / p) := by
    intro k
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 (ne_of_lt hqtop) (hXae k)]
    have he : (fun ω => ‖X k ω‖ₑ ^ q.toReal) = fun ω => X k ω ^ p := by
      funext ω
      simp [hqreal]
    rw [he, hqreal]
    exact ENNReal.rpow_le_rpow (hmoment k) (by positivity)
  have htestPointwise : ∀ k ω,
      ‖approxTestIntegral (γ := γ) (H := H) f k ω‖ₑ ≤
        ENNReal.ofReal B * ‖X k ω‖ₑ := by
    intro k ω
    have hmassTop : X k ω ≠ ⊤ := by
      haveI : IsLocallyFiniteMeasure
          (MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω) :=
        isLocallyFiniteMeasure_lqgApprox hH γ k ω
      dsimp [X]
      exact measure_ball_ne_top
    rw [Real.enorm_eq_ofReal_abs]
    calc
      ENNReal.ofReal |approxTestIntegral (γ := γ) (H := H) f k ω| ≤
          ENNReal.ofReal (B * (X k ω).toReal) :=
        ENNReal.ofReal_le_ofReal (approxTestIntegral_abs_le_diskMass
          hH f hfs hB0 hB k ω)
      _ = ENNReal.ofReal B * ‖X k ω‖ₑ := by
        rw [ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal hmassTop]
        simp
  let b : ℝ≥0 := ⟨B, hB0⟩
  have hb : (b : ℝ≥0∞) = ENNReal.ofReal B := by
    rw [ENNReal.ofReal_eq_coe_nnreal hB0]
    rfl
  have hbound : ∀ k,
      eLpNorm (approxTestIntegral (γ := γ) (H := H) f k) q P ≤
        ENNReal.ofReal B * C ^ (1 / p) := by
    intro k
    have hpoint : ∀ᵐ ω ∂P,
        ‖approxTestIntegral (γ := γ) (H := H) f k ω‖ₑ ≤
          (b : ℝ≥0∞) * ‖X k ω‖ₑ := by
      filter_upwards [ae_of_all P (htestPointwise k)] with ω hω
      simpa only [hb] using hω
    have hcompare := eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
      (f := approxTestIntegral (γ := γ) (H := H) f k) (g := X k)
      (c := b) (p := p) hpoint hp0
    have hmass' : eLpNorm' (X k) p P ≤ C ^ (1 / p) := by
      simpa only [← hqreal, ← eLpNorm_eq_eLpNorm' hq0 (ne_of_lt hqtop) (hXae k)] using hmassLp k
    have hcompare' : eLpNorm'
        (approxTestIntegral (γ := γ) (H := H) f k) p P ≤
          (b : ℝ≥0∞) * eLpNorm' (X k) p P := by
      simpa [ENNReal.smul_def, smul_eq_mul] using hcompare
    calc
      eLpNorm (approxTestIntegral (γ := γ) (H := H) f k) q P =
          eLpNorm' (approxTestIntegral (γ := γ) (H := H) f k) p P := by
            rw [eLpNorm_eq_eLpNorm' hq0 (ne_of_lt hqtop) (hF k), hqreal]
      _ ≤ (b : ℝ≥0∞) * eLpNorm' (X k) p P := hcompare'
      _ ≤ ENNReal.ofReal B * C ^ (1 / p) := by
            rw [hb]
            exact mul_le_mul_of_nonneg_left hmass' (by positivity)
  have hboundTop : ENNReal.ofReal B * C ^ (1 / p) < ⊤ := by
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hCtop.ne)
  have hUI : UniformIntegrable
      (fun k ω => approxTestIntegral (γ := γ) (H := H) f k ω) 1 P :=
    uniformIntegrable_one_of_uniform_eLpNorm_gt_one hq1 hqtop hboundTop hF hbound

  exact hUI

/-- Almost-sure convergence of the approximation tests, together with their uniform disk moment,
upgrades to convergence in L¹. -/
theorem tendsto_approxTestIntegral_L1
    (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : IsLQGAreaOf γ H μ P)
    {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ ball (0 : ℂ) 1) :
    Tendsto
      (fun k => eLpNorm
        (fun ω => approxTestIntegral (γ := γ) (H := H) f k ω -
          areaTestIntegral (μ := μ) f ω) 1 P)
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_unitDisk hfs
  have hconv : ∀ᵐ ω ∂P, Tendsto
      (fun k => approxTestIntegral (γ := γ) (H := H) f k ω) atTop
      (𝓝 (areaTestIntegral (μ := μ) f ω)) := by
    filter_upwards [hμ] with ω hω
    exact hω.2 f hf hfc
  have hUI : UniformIntegrable
      (fun k ω => approxTestIntegral (γ := γ) (H := H) f k ω) 1 P :=
    uniformIntegrable_approxTestIntegral hH hHm hγ hγ2 hf hfs
  have hF : ∀ k, AEStronglyMeasurable
      (approxTestIntegral (γ := γ) (H := H) f k) P := by
    intro k
    exact (measurable_approxTestIntegral hH hHm f hf k).aestronglyMeasurable
  have hlimit : MemLp (areaTestIntegral (μ := μ) f) 1 P :=
    hUI.memLp_of_ae_tendsto hconv
  exact tendsto_Lp_finite_of_tendsto_ae (p := (1 : ℝ≥0∞)) (by norm_num)
    ENNReal.coe_ne_top hF hlimit hUI.1 hconv

/-- The normalization correction vanishes when the averaging circle stays inside the unit disk.
This local computation is needed to identify the exact first moment of interior approximations. -/
private lemma areaTest_betaAvg_eq_zero_of_inside_circle {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) : LQGDimension.Osc37.betaAvg r z = 0 := by
  unfold LQGDimension.Osc37.betaAvg
  apply Real.circleAverage_const_on_circle
  intro y hy
  rw [mem_sphere_iff_norm, abs_of_pos hr] at hy
  have hy1 : ‖y‖ ≤ 1 := by
    calc
      ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 := by rw [hy]; linarith
  rw [max_eq_right hy1, Real.log_one]

private lemma areaTest_gffCircleCov_self_eq_neg_log {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) : LQGDimension.gffCircleCov r z r z = -Real.log r := by
  rw [LQGDimension.Osc37.gffCircleCov_formula hr,
    LQGDimension.Osc37.aAvg_self hr]
  rw [areaTest_betaAvg_eq_zero_of_inside_circle hr hz]
  ring

/-- The expected approximation density is one when its averaging circle is contained in the
normalization disk. -/
private lemma areaTest_lintegral_dens_eq_one
    (hH : LQGDimension.IsGFFCircleAverage H P) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : ‖z‖ + r ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) ∂P = 1 := by
  have hm : ∀ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) =
      ENNReal.ofReal (r ^ (γ ^ 2 / 2)) * ENNReal.ofReal (Real.exp (γ * H r z ω)) := fun ω =>
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)
  simp_rw [hm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    LQGMetric.DG.lintegral_exp_circleAvg hH hr z γ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  rw [ENNReal.ofReal_eq_one]
  rw [areaTest_gffCircleCov_self_eq_neg_log hr hz, Real.rpow_def_of_pos hr, ← Real.exp_add]
  rw [Real.exp_eq_one_iff]
  ring

/-- At a scale whose averaging circles stay inside the normalization circle on the support of a
nonnegative test, the approximation has the exact Lebesgue first moment. -/
lemma integral_approxTestIntegral_eq_volume_of_fit
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {f : ℂ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hf : Continuous f) (hfs : tsupport f ⊆ ball (0 : ℂ) 1)
    (hf_nonneg : ∀ z, 0 ≤ f z) (k : ℕ)
    (hfit : ∀ z ∈ tsupport f,
      ‖z‖ + MatedCRTHarmonic.GMSLemma27.dyadicRadius k ≤ 1) :
    ∫ ω, approxTestIntegral (γ := γ) (H := H) f k ω ∂P = ∫ z, f z := by
  letI : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_unitDisk hfs
  have hr : 0 < MatedCRTHarmonic.GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]
    exact QuantumZipper.radius_pos k
  have hdensity : Measurable fun p : ℂ × Ω => ENNReal.ofReal
      (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) p.1 p.2)) := by
    have hj := measurable_uncurry_coord hH hHm hr
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul ((hj.const_mul γ).exp))
  have hprod : Measurable fun p : Ω × ℂ => ENNReal.ofReal (f p.2) *
      ENNReal.ofReal (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) p.2 p.1)) := by
    exact (ENNReal.measurable_ofReal.comp (hf.measurable.comp measurable_snd)).mul
      (hdensity.comp (measurable_snd.prodMk measurable_fst))
  have hpoint : ∀ ω,
      ENNReal.ofReal (approxTestIntegral (γ := γ) (H := H) f k ω) =
        ∫⁻ z, ENNReal.ofReal (f z) *
          ENNReal.ofReal (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
            Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω)) ∂volume := by
    intro ω
    let ν := MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
    haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_lqgApprox hH γ k ω
    have hfi : Integrable f ν := hf.integrable_of_hasCompactSupport hfc
    have hnonneg : 0 ≤ᵐ[ν] f := ae_of_all ν hf_nonneg
    have hdν : AEMeasurable (fun z => ENNReal.ofReal
        (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
          Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω))) volume :=
      (ENNReal.measurable_ofReal.comp
        (measurable_const.mul
          (Real.continuous_exp.comp ((hH.continuous _ hr ω).const_mul γ)).measurable)).aemeasurable
    have hmeasure : ∫⁻ z, ENNReal.ofReal (f z) ∂ν =
        ∫⁻ z, ENNReal.ofReal (f z) * ENNReal.ofReal
          (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
            Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω)) ∂volume := by
      simp only [ν, MatedCRTHarmonic.GMSLemma27.lqgApprox]
      rw [lintegral_withDensity_eq_lintegral_mul₀ hdν
        (g := fun z => ENNReal.ofReal (f z))
        (ENNReal.measurable_ofReal.comp hf.measurable).aemeasurable]
      apply lintegral_congr
      intro z
      simp only [Pi.mul_apply, mul_comm]
    change ENNReal.ofReal (∫ z, f z ∂ν) = _
    rw [ofReal_integral_eq_lintegral_ofReal hfi hnonneg, hmeasure]
  have hswap := lintegral_lintegral_swap
    (μ := P) (ν := (volume : Measure ℂ))
    (f := fun ω z => ENNReal.ofReal (f z) *
      ENNReal.ofReal (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω)))
    hprod.aemeasurable
  have hrad1 : ∀ᵐ ω ∂P, 0 ≤ approxTestIntegral (γ := γ) (H := H) f k ω := by
    filter_upwards [] with ω
    unfold approxTestIntegral
    apply integral_nonneg_of_ae
    exact ae_of_all _ hf_nonneg
  have hrealLin : ∫⁻ ω,
      ENNReal.ofReal (approxTestIntegral (γ := γ) (H := H) f k ω) ∂P =
      ∫⁻ z, ENNReal.ofReal (f z) ∂volume := by
    calc
      ∫⁻ ω, ENNReal.ofReal (approxTestIntegral (γ := γ) (H := H) f k ω) ∂P =
          ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (f z) *
            ENNReal.ofReal (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
              Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω)) ∂volume ∂P := by
                apply lintegral_congr_ae
                exact ae_of_all _ hpoint
      _ = ∫⁻ z, ∫⁻ ω, ENNReal.ofReal (f z) *
            ENNReal.ofReal (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
              Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) z ω)) ∂P ∂volume := hswap
      _ = ∫⁻ z, ENNReal.ofReal (f z) ∂volume := by
            apply lintegral_congr
            intro z
            by_cases hzero : f z = 0
            · simp [hzero]
            · have hzmem : z ∈ Function.support f := by
                simpa only [Function.mem_support] using hzero
              have hzsup : z ∈ tsupport f := subset_tsupport _ hzmem
              have hzfit := hfit z hzsup
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                areaTest_lintegral_dens_eq_one hH hr hzfit]
              simp
  have hFint : Integrable (approxTestIntegral (γ := γ) (H := H) f k) P := by
    have hUI := uniformIntegrable_approxTestIntegral hH hHm hγ hγ2 hf hfs
    exact memLp_one_iff_integrable.mp (hUI.memLp k)
  have hVolint : Integrable f (volume : Measure ℂ) :=
    hf.integrable_of_hasCompactSupport hfc
  have hVolnn : 0 ≤ᵐ[volume] f := ae_of_all _ hf_nonneg
  have hFnn : 0 ≤ᵐ[P] (approxTestIntegral (γ := γ) (H := H) f k) := hrad1
  have hOfReal : ENNReal.ofReal (∫ ω, approxTestIntegral (γ := γ) (H := H) f k ω ∂P) =
      ENNReal.ofReal (∫ z, f z ∂volume) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFint hFnn,
      hrealLin, ← ofReal_integral_eq_lintegral_ofReal hVolint hVolnn]
  have hFintnn : 0 ≤ ∫ ω, approxTestIntegral (γ := γ) (H := H) f k ω ∂P :=
    integral_nonneg_of_ae hFnn
  have hVolnn' : 0 ≤ ∫ z, f z ∂volume := integral_nonneg_of_ae hVolnn
  have hToReal := congrArg ENNReal.toReal hOfReal
  simpa [ENNReal.toReal_ofReal hFintnn, ENNReal.toReal_ofReal hVolnn'] using hToReal

/-- Compact support strictly inside the normalization disk gives a common positive margin, so
all sufficiently fine approximations have the exact first moment. -/
lemma eventually_fit_of_tsupport_subset_unitDisk {f : ℂ → ℝ}
    (hf : Continuous f) (hfs : tsupport f ⊆ ball (0 : ℂ) 1) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ tsupport f,
      ‖z‖ + MatedCRTHarmonic.GMSLemma27.dyadicRadius k ≤ 1 := by
  have hcompact : IsCompact (tsupport f) :=
    hasCompactSupport_of_tsupport_subset_unitDisk hfs
  by_cases hne : (tsupport f).Nonempty
  · obtain ⟨a, ha, hbound⟩ := hcompact.exists_forall_le'
      (continuous_norm.neg.continuousOn) (a := -1) (fun z hz => by
        have hznorm : ‖z‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using hfs hz
        change -1 < -‖z‖
        exact neg_lt_neg hznorm)
    have hgap : 0 < a + 1 := by linarith
    have hradius : Tendsto
        (fun k : ℕ => MatedCRTHarmonic.GMSLemma27.dyadicRadius k) atTop (𝓝 0) := by
      simpa only [MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius,
        QuantumZipper.radius] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one
            (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
    have hevent : ∀ᶠ k : ℕ in atTop,
        MatedCRTHarmonic.GMSLemma27.dyadicRadius k < a + 1 :=
      hradius.eventually (Iio_mem_nhds hgap)
    filter_upwards [hevent] with k hk z hz
    have hzbound : ‖z‖ ≤ -a := by
      have hx := hbound z hz
      change a ≤ -‖z‖ at hx
      linarith
    linarith
  · have hempty : tsupport f = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    filter_upwards [] with k z hz
    simp [hempty] at hz

/-- For a nonnegative continuous test supported inside the unit disk, the limiting LQG area has
the exact Lebesgue first moment. -/
theorem integral_areaTestIntegral_eq_volume
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z))
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGAreaOf γ H μ P)
    {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ ball (0 : ℂ) 1)
    (hf_nonneg : ∀ z, 0 ≤ f z) :
    Integrable (areaTestIntegral (μ := μ) f) P ∧
      (∫ ω, areaTestIntegral (μ := μ) f ω ∂P = ∫ z, f z) := by
  letI : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_unitDisk hfs
  have hconv : ∀ᵐ ω ∂P, Tendsto
      (fun k => approxTestIntegral (γ := γ) (H := H) f k ω) atTop
      (𝓝 (areaTestIntegral (μ := μ) f ω)) := by
    filter_upwards [hμ] with ω hω
    exact hω.2 f hf hfc
  have hUI : UniformIntegrable
      (fun k ω => approxTestIntegral (γ := γ) (H := H) f k ω) 1 P :=
    uniformIntegrable_approxTestIntegral hH hHm hγ hγ2 hf hfs
  have hlimit : MemLp (areaTestIntegral (μ := μ) f) 1 P :=
    hUI.memLp_of_ae_tendsto hconv
  have hL1 := tendsto_approxTestIntegral_L1 hH hHm hγ hγ2 hμ hf hfs
  have hmeas : AEStronglyMeasurable (areaTestIntegral (μ := μ) f) P :=
    hlimit.aestronglyMeasurable
  have hFi : ∀ᶠ k : ℕ in atTop,
      Integrable (approxTestIntegral (γ := γ) (H := H) f k) P := by
    filter_upwards [] with k
    exact memLp_one_iff_integrable.mp (hUI.memLp k)
  have hint : Tendsto
      (fun k => ∫ ω, approxTestIntegral (γ := γ) (H := H) f k ω ∂P)
      atTop (𝓝 (∫ ω, areaTestIntegral (μ := μ) f ω ∂P)) :=
    tendsto_integral_of_L1' (areaTestIntegral (μ := μ) f) hFi hL1
  have hfit := eventually_fit_of_tsupport_subset_unitDisk hf hfs
  have hexact : ∀ᶠ k : ℕ in atTop,
      ∫ ω, approxTestIntegral (γ := γ) (H := H) f k ω ∂P = ∫ z, f z := by
    filter_upwards [hfit] with k hk
    exact integral_approxTestIntegral_eq_volume_of_fit hH hHm hγ hγ2 hf hfs
      hf_nonneg k hk
  have hconst : Tendsto
      (fun _ : ℕ => ∫ z, f z) atTop (𝓝 (∫ z, f z)) := tendsto_const_nhds
  have hexact' : (fun _ : ℕ => ∫ z, f z) =ᶠ[atTop]
      (fun k => ∫ ω, approxTestIntegral (γ := γ) (H := H) f k ω ∂P) := by
    filter_upwards [hexact] with k hk
    exact hk.symm
  have hlimEq := tendsto_nhds_unique hint (Tendsto.congr' hexact' hconst)
  exact ⟨hlimit.integrable (by norm_num), hlimEq⟩

end MatedCRTHarmonic.ConeLemmaA10
