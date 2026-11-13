/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCone.OpenSupport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea8C

/-!
# Full support of the quantum-cone area

The fixed positive bump mass from `MoTPort.ConeArea8B` is transported to every Gaussian-rational
dyadic ball by the exact dyadic affine scaling of the area approximations. Countability then gives
full support for the whole-plane GFF area. On the punctured plane the cone area is a strictly
positive continuous density times that whole-plane area, so the same conclusion holds for the
cone field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCone

open LQGMetric QuantumZipper
open MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic.MoTPort.ConeArea4
open MatedCRTHarmonic.MoTPort.ConeArea8

/-- The dyadic ball obtained by contracting the positive bump window about a rational centre. -/
def ratBumpBall (q : ℚ × ℚ) (m : ℕ) : Set ℂ :=
  ball (ratPt q) ((2 : ℝ)⁻¹ ^ m / 40)

lemma support_ofReal_bumpW_subset_ball :
    Function.support (fun z => ENNReal.ofReal (bumpW z)) ⊆ ball c₀ (1 / 40) := by
  intro z hz
  have hp : 0 < bumpW z := by
    rw [Function.mem_support] at hz
    by_contra h
    rw [not_lt] at h
    exact hz (ENNReal.ofReal_eq_zero.2 h)
  rw [mem_ball]
  change 0 < max 0 (1 / 40 - dist z c₀) at hp
  simp only [lt_max_iff, lt_self_iff_false, false_or] at hp
  linarith

/-- A positive bump integral forces positive mass on its open support ball. -/
lemma measure_ball_pos_of_lintegral_bumpW_pos {μ : Measure ℂ}
    (h : 0 < ∫⁻ z, ENNReal.ofReal (bumpW z) ∂μ) :
    0 < μ (ball c₀ (1 / 40)) := by
  rw [lintegral_pos_iff_support measurable_bumpW'] at h
  exact h.trans_le (measure_mono support_ofReal_bumpW_subset_ball)

/-- Vague convergence is preserved by a homeomorphism. -/
lemma isVagueLimitOn_map_homeomorph {U : Set ℂ} (hU : IsOpen U)
    {μs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : IsVagueLimitOn U μs μ)
    (T : ℂ ≃ₜ ℂ) :
    IsVagueLimitOn (T '' U) (fun k => (μs k).map T) (μ.map T) := by
  have hpre : T ⁻¹' (T '' U) = U := T.preimage_image U
  have hKpre : ∀ K, IsCompact K → K ⊆ T '' U → IsCompact (T ⁻¹' K) ∧ T ⁻¹' K ⊆ U :=
    fun K hK hKU => ⟨T.isCompact_preimage.2 hK, (preimage_mono hKU).trans hpre.subset⟩
  refine ⟨?_, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.map_apply T.measurable (T.isOpenMap U hU).measurableSet.compl,
      preimage_compl, hpre, h.1]
  · rw [Measure.map_apply T.measurable hK.isClosed.measurableSet]
    exact h.2.1 _ (hKpre K hK hKU).1 (hKpre K hK hKU).2
  · have e : ∀ ν : Measure ℂ, ∫ z, f z ∂(ν.map T) = ∫ z, (f ∘ T) z ∂ν := fun ν =>
      integral_map T.measurable.aemeasurable hf.aestronglyMeasurable
    simp only [e]
    refine h.2.2 _ (hf.comp T.continuous) (hfc.comp_homeomorph T) ?_
    rw [tsupport_comp_eq_preimage]
    exact (preimage_mono hfU).trans hpre.subset

/-- Deterministic transport of a global vague limit through a dyadic affine scaling. -/
lemma qAreaC_map_eq_smul_of_dyadic
    {γ : ℝ} {x y : Field} (m : ℕ) (T : ℂ ≃ₜ ℂ)
    (hx : ConeArea4.AreaGood univ (areaApproxC γ x))
    (hy : ConeArea4.AreaGood univ (areaApproxC γ y))
    (hmap : ∀ k, (areaApproxC γ x (k + m)).map T =
      ConeArea4.scaleConst γ m • areaApproxC γ y k) :
    (qAreaC γ x).map T = ConeArea4.scaleConst γ m • qAreaC γ y := by
  have hxq : IsVagueLimitOn univ (areaApproxC γ x) (qAreaC γ x) :=
    MoTPort.ConeArea.isVagueLimitOn_qAreaC hx.1
  have hyq : IsVagueLimitOn univ (areaApproxC γ y) (qAreaC γ y) :=
    MoTPort.ConeArea.isVagueLimitOn_qAreaC hy.1
  have hleft : IsVagueLimitOn univ
      (fun k => (areaApproxC γ x (k + m)).map T) ((qAreaC γ x).map T) := by
    have hshift : IsVagueLimitOn univ (fun k => areaApproxC γ x (k + m))
        (qAreaC γ x) :=
      ⟨hxq.1, hxq.2.1, fun f hf hfc hfU =>
        (hxq.2.2 f hf hfc hfU).comp (tendsto_add_atTop_nat m)⟩
    simpa using isVagueLimitOn_map_homeomorph isOpen_univ hshift T
  have hright : IsVagueLimitOn univ
      (fun k => ConeArea4.scaleConst γ m • areaApproxC γ y k)
      (ConeArea4.scaleConst γ m • qAreaC γ y) :=
    MoTPort.ConeArea.isVagueLimitOn_smul hyq (ConeArea4.scaleConst_ne_top γ m)
  rw [show (fun k => (areaApproxC γ x (k + m)).map T) =
      (fun k => ConeArea4.scaleConst γ m • areaApproxC γ y k) from funext hmap] at hleft
  exact isVagueLimitOn_unique isOpen_univ hleft hright

/-- Positivity of `qAreaC` on one rational dyadic ball. -/
theorem ae_qAreaC_ratBumpBall_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} (hX : IsWholePlaneGFF X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (q : ℚ × ℚ) (m : ℕ) :
    ∀ᵐ ω ∂P, 0 < qAreaC γ (X ω) (ratBumpBall q m) := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ m
  have hr : 0 < r := by dsimp [r]; positivity
  let a : ℂ := ratPt q - (r : ℂ) * c₀
  let Y : Ω → Field := fun ω => affineComp r a (X ω)
  have hY : IsWholePlaneGFF Y P := hX.affineComp hr a
  let s : ℝ := (2 : ℝ) ^ m
  have hs : 0 < s := by dsimp [s]; positivity
  let b : ℂ := -((s : ℂ) * a)
  let T : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ (s : ℂ) (by exact_mod_cast hs.ne')).trans (Homeomorph.addRight b)
  filter_upwards [ConeArea4.ae_areaGood_univ hX hγ hγ2,
    ConeArea4.ae_areaGood_univ hY hγ hγ2,
    ae_massW_pos hY hγ hγ2,
    ae_all_iff.2 fun k => ConeArea4.ae_ae_circleAvg_scale hY m k b] with ω hx hy hm hca
  have hxy : affineComp s b (Y ω) = X ω := by
    dsimp [Y]
    rw [GM.affineComp_comp hs.ne' (by positivity : (2 : ℝ)⁻¹ ^ m ≠ 0)]
    have hsr : (2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ m = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    have hrs : r * s = 1 := by dsimp [r, s]; rw [mul_comm, hsr]
    have hz : (r : ℂ) * b + a = 0 := by
      dsimp [b]
      rw [mul_neg, ← mul_assoc, ← Complex.ofReal_mul, hrs]
      simp
    rw [hrs, hz]
    exact GM.affineComp_one_zero (X ω)
  have hmap : ∀ k, (areaApproxC γ (X ω) (k + m)).map T =
      ConeArea4.scaleConst γ m • areaApproxC γ (Y ω) k := by
    intro k
    rw [← hxy]
    exact ConeArea4.map_areaApproxC_scale (hca k)
  have hμmap := qAreaC_map_eq_smul_of_dyadic m T hx hy hmap
  have hyq : IsVagueLimitOn univ (areaApproxC γ (Y ω)) (qAreaC γ (Y ω)) :=
    MoTPort.ConeArea.isVagueLimitOn_qAreaC hy.1
  have hint : 0 < ∫⁻ z, ENNReal.ofReal (bumpW z) ∂qAreaC γ (Y ω) := by
    rw [← massW_eq_of_isVagueLimitOn hyq (subset_univ _)
      (hy.2 _ (isCompact_closedBall _ _) (subset_univ _))]
    exact hm
  have hball : 0 < qAreaC γ (Y ω) (ball c₀ (1 / 40)) :=
    measure_ball_pos_of_lintegral_bumpW_pos hint
  have hscale : 0 < ConeArea4.scaleConst γ m :=
    pos_iff_ne_zero.2 (ConeArea4.scaleConst_ne_zero γ m)
  have hpre : T ⁻¹' (ball c₀ (1 / 40)) = ratBumpBall q m := by
    ext z
    simp only [T, Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀,
      Homeomorph.coe_addRight, ratBumpBall, mem_preimage, mem_ball, b, a, r, s,
      dist_eq_norm]
    have hsr : (2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ m = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    rw [show (s : ℂ) * z + b - c₀ = (s : ℂ) * (z - ratPt q) by
      have hc : (s : ℂ) * (r : ℂ) = 1 := by
        dsimp [s, r]
        exact_mod_cast hsr
      dsimp [b, a]
      calc
        (s : ℂ) * z + -((s : ℂ) * (ratPt q - (r : ℂ) * c₀)) - c₀ =
            (s : ℂ) * z - (s : ℂ) * ratPt q + ((s : ℂ) * (r : ℂ)) * c₀ - c₀ := by ring
        _ = (s : ℂ) * (z - ratPt q) := by rw [hc]; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hrs : s * r = 1 := by dsimp [s, r]; exact hsr
    constructor <;> intro h
    · nlinarith [norm_nonneg (z - ratPt q)]
    · nlinarith [norm_nonneg (z - ratPt q)]
  have hEval := congrArg (fun μ : Measure ℂ => μ (ball c₀ (1 / 40))) hμmap
  rw [Measure.map_apply T.measurable isOpen_ball.measurableSet, hpre,
    Measure.smul_apply, smul_eq_mul] at hEval
  rw [hEval]
  exact ENNReal.mul_pos hscale.ne' hball.ne'

/-- The whole-plane GFF area charges every nonempty open set. -/
theorem ae_qAreaC_open_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} (hX : IsWholePlaneGFF X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < qAreaC γ (X ω) U := by
  filter_upwards [ae_all_iff.2 fun q : ℚ × ℚ =>
    ae_all_iff.2 fun m : ℕ => ae_qAreaC_ratBumpBall_pos hX hγ hγ2 q m] with ω hω
  intro U hU hUne
  obtain ⟨z, hz⟩ := hUne
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε * 20 by positivity)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hr : (2 : ℝ)⁻¹ ^ m / 40 < ε / 2 := by linarith
  obtain ⟨q, hq⟩ := LQGMetric.exists_ratPt_dist_lt z (half_pos hε)
  have hsub : ratBumpBall q m ⊆ U := by
    intro w hw
    apply hεU
    rw [ratBumpBall, mem_ball] at hw
    rw [mem_ball]
    calc
      dist w z ≤ dist w (ratPt q) + dist (ratPt q) z := dist_triangle _ _ _
      _ < ε := by linarith
  exact (hω q m).trans_le (measure_mono hsub)

lemma open_sdiff_singleton_nonempty {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    (U \ {(0 : ℂ)}).Nonempty := by
  obtain ⟨z, hz⟩ := hUne
  by_cases hz0 : z = 0
  · subst z
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU 0 hz
    refine ⟨((ε / 2 : ℝ) : ℂ), hεU ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    · simp only [mem_singleton_iff]
      exact_mod_cast (half_pos hε).ne'
  · exact ⟨z, hz, by simpa using hz0⟩

/-- The LQG area of the quantum-cone field charges every nonempty open set. -/
theorem ae_lqgArea_coneField_open_pos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} {X : Ω → LQGMetric.DistC}
    {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < QuantumZipper.Qc γ)
    (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXA : IndepFun X (fun ω t =>
      motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty →
      0 < MatedCRTHarmonic.CellScaling.lqgArea γ
        (MatedCRTHarmonic.CellScaling.coneField (X ω)
          (MatedCRTHarmonic.CellScaling.coneRadial γ α
            (fun s => B s ω) (fun s => B' s ω))) U := by
  let W : ℝ := 2 * γ * (QuantumZipper.Qc γ - α)
  have hW : 0 < W := by dsimp [W]; positivity
  have hconeAlpha : MoTPort.coneAlpha γ W = α := by
    dsimp [MoTPort.coneAlpha, W]
    field_simp
    ring
  let A : ℝ → Ω → ℝ := fun t ω =>
    motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t
  have hA : MoTPort.IsConeProcess α (QuantumZipper.Qc γ) A P :=
    isConeProcess_motConeRadial hB hB' hBB'
  have hAlpha : MoTPort.IsConeProcess (MoTPort.coneAlpha γ W)
      (QuantumZipper.Qc γ) A P := by rw [hconeAlpha]; exact hA
  have hcone := ConeArea8.ae_qAreaC_coneField_eq hγ hγ2 hW hX hAlpha hXA
  filter_upwards [hcone, ae_qAreaC_open_pos hX hγ hγ2,
    ConeArea4.ae_areaGood_univ hX hγ hγ2, ConeArea4.ae_radial_R2 hX,
    ConeArea4.ae_locallyIntegrable_coneProfile hA, MoTPort.ConeArea3.ae_hasCircleAvgs hX,
    (MoTPort.ConeMeas2.aemeasurable_conePath hA).2]
    with ω ⟨μ, hq, hμ, _, _⟩ hpos hgood ⟨R, hRc, hRm, hxR, hRl⟩ hAl hc hAc
  intro U hU hUne
  let V : Set ℂ := U \ {(0 : ℂ)}
  have hVo : IsOpen V := hU.sdiff isClosed_singleton
  have hVne : V.Nonempty := open_sdiff_singleton_nonempty hU hUne
  have hVp : V ⊆ univ \ {(0 : ℂ)} := fun z hz => ⟨mem_univ z, hz.2⟩
  have hXq : IsVagueLimitOn univ (areaApproxC γ (X ω)) (qAreaC γ (X ω)) :=
    MoTPort.ConeArea.isVagueLimitOn_qAreaC hgood.1
  have hX' := AtomlessUncond.isVagueLimitOn_restrict
    (U' := univ \ {(0 : ℂ)}) (isOpen_univ.sdiff isClosed_singleton) (subset_univ _) hXq
  let μX : Measure ℂ := (qAreaC γ (X ω)).restrict (univ \ {(0 : ℂ)})
  have hLA := MoTPort.ConeArea3.isVagueLimitOn_coneField_punctured
    (γ := γ) (Q := QuantumZipper.Qc γ) (a := fun t => A t ω)
    hAc hRc hRm hxR hRl hAl hc hX'
  have hconeEq : μ = μX.withDensity (fun z => ENNReal.ofReal
      (Real.exp (γ * MoTPort.ConeArea3.coneShift (fun t => A t ω)
        (QuantumZipper.Qc γ) R z))) :=
    isVagueLimitOn_unique (isOpen_univ.sdiff isClosed_singleton) hμ hLA
  have hg := ConeArea8.measurable_expDens
    (a := fun t => A t ω) hAc.measurable γ (QuantumZipper.Qc γ) hRm
  have hμXV : 0 < μX V := by
    dsimp [μX]
    rw [Measure.restrict_apply hVo.measurableSet, inter_eq_left.2 hVp]
    exact hpos V hVo hVne
  have hdV : 0 < (μX.withDensity (fun z => ENNReal.ofReal
      (Real.exp (γ * MoTPort.ConeArea3.coneShift (fun t => A t ω)
        (QuantumZipper.Qc γ) R z)))) V := by
    apply pos_iff_ne_zero.2
    rw [Ne, withDensity_apply_eq_zero' hg.aemeasurable]
    have he : {z | ENNReal.ofReal (Real.exp (γ * MoTPort.ConeArea3.coneShift
        (fun t => A t ω) (QuantumZipper.Qc γ) R z)) ≠ 0} = univ := by
      ext z
      simp [Real.exp_pos]
    rw [he, univ_inter]
    exact hμXV.ne'
  rw [lqgArea_eq_qAreaC, coneField_eq_motConeField γ α (X ω)
    (fun s => B s ω) (fun s => B' s ω)]
  change 0 < qAreaC γ (coneField (lateralPartC (X ω))
    (fun t => A t ω) (QuantumZipper.Qc γ)) U
  rw [hq, hconeEq]
  exact hdV.trans_le (measure_mono inter_subset_left)

end MatedCRTHarmonic.LQGCone
