/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea8B at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W2

/-!
# Cone area, part 22: positivity of the whole-plane LQG measure near `c₀`

For the bump `bumpW` (a tent of radius `1/40` at `c₀ = (1+i)/2`, inside the window `U₀` of
ConeArea4B) and the measurable functional

  `massW γ x = liminf_k ∫ bumpW d(areaApproxC γ x k)`,

* `massW_eq_of_isVagueLimitOn`: `massW` is `∫ bumpW dμ` for every vague limit `μ` on an open set
  containing the support (deterministic);
* `ae_massW_pos_wn`: for the white-noise whole-plane GFF `h₀`, a.s. `massW γ h₀ > 0`: on `U₀` the
  limit is `e^{−γY} μ_{h^𝕍}` (DG Lemma 3.1 coupling, LM `DG.ae_isVagueLimitOn_muOfMod_loc`, as in
  ConeArea4B), and `μ_{h^𝕍}` charges every rational ball in the unit square (LM
  `DZZ.ae_qArea_wn_ball_pos`, DZZ Lemma 2.10, negative moments);
* **`ae_massW_pos`**: the same for **every** whole-plane GFF `X`, by the law transfer of
  ConeArea4C (`map_normField_eq`; `massW` is multiplied by `e^{γc}` under `x ↦ x + c`).

Own elementary glue around the cited facts (the transfer copies `ConeArea4.ae_areaGood_U₀`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea8

open QuantumZipper LQGMetric LQGMetric.DG LQGMetric.WhiteNoise LQGMetric.GFFExist LQGMetric.SupTail
  ConeArea4

/-! ## The bump -/

/-- the tent of radius `1/40` at `c₀` -/
def bumpW (z : ℂ) : ℝ := max 0 (1 / 40 - dist z c₀)

lemma continuous_bumpW : Continuous bumpW :=
  continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))

lemma measurable_bumpW' : Measurable fun z => ENNReal.ofReal (bumpW z) :=
  ENNReal.measurable_ofReal.comp continuous_bumpW.measurable

lemma bumpW_nonneg (z : ℂ) : 0 ≤ bumpW z := le_max_left _ _

lemma bumpW_eq_zero {z : ℂ} (h : 1 / 40 ≤ dist z c₀) : bumpW z = 0 :=
  max_eq_left (by linarith)

lemma bumpW_pos {z : ℂ} (h : z ∈ ball c₀ (1 / 40)) : 0 < bumpW z := by
  rw [mem_ball] at h
  exact lt_max_of_lt_right (by linarith)

lemma mem_of_bumpW_ne_zero {z : ℂ} (h : bumpW z ≠ 0) : z ∈ closedBall c₀ (1 / 40) := by
  by_contra h'
  rw [mem_closedBall, not_le] at h'
  exact h (bumpW_eq_zero h'.le)

lemma tsupport_bumpW : tsupport bumpW ⊆ closedBall c₀ (1 / 40) :=
  closure_minimal (fun _ hz => mem_of_bumpW_ne_zero hz) isClosed_closedBall

lemma hasCompactSupport_bumpW : HasCompactSupport bumpW :=
  (isCompact_closedBall c₀ (1 / 40)).of_isClosed_subset (isClosed_tsupport _) tsupport_bumpW

lemma closedBall_subset_U₀ : closedBall c₀ (1 / 40) ⊆ U₀ :=
  closedBall_subset_ball (by norm_num)

/-! ## The bump mass functional -/

/-- `liminf_k ∫ bumpW d(areaApproxC γ x k)` -/
def massW (γ : ℝ) (x : Field) : ℝ≥0∞ :=
  liminf (fun k => ∫⁻ z, ENNReal.ofReal (bumpW z) ∂(areaApproxC γ x k)) atTop

lemma measurable_massW (γ : ℝ) : Measurable (massW γ) :=
  Measurable.liminf fun k =>
    (Measure.measurable_lintegral measurable_bumpW').comp (ConeArea.measurable_areaApproxC γ k)

/-- **`massW` is the bump integral of any vague limit** on an open set containing the support,
given eventual finiteness there -/
theorem liminf_eq_of_isVagueLimitOn {U : Set ℂ} {νs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitOn U νs μ) (hsub : closedBall c₀ (1 / 40) ⊆ U)
    (hfin : ∀ᶠ k in atTop, νs k (closedBall c₀ (1 / 40)) < ⊤) :
    liminf (fun k => ∫⁻ z, ENNReal.ofReal (bumpW z) ∂(νs k)) atTop =
      ∫⁻ z, ENNReal.ofReal (bumpW z) ∂μ := by
  have hts := tsupport_bumpW
  have hint : ∀ ν : Measure ℂ, ν (closedBall c₀ (1 / 40)) < ⊤ → Integrable bumpW ν :=
    fun ν hν => AtomlessUncond.integrable_of_finite_tsupport continuous_bumpW
      hasCompactSupport_bumpW ((measure_mono hts).trans_lt hν)
  have hμ := hint μ (h.2.1 _ (isCompact_closedBall _ _) hsub)
  have ht := ENNReal.tendsto_ofReal (h.2.2 bumpW continuous_bumpW hasCompactSupport_bumpW
    (hts.trans hsub))
  rw [ofReal_integral_eq_lintegral_ofReal hμ (ae_of_all _ bumpW_nonneg)] at ht
  refine (ht.congr' ?_).liminf_eq
  filter_upwards [hfin] with k hk
  exact ofReal_integral_eq_lintegral_ofReal (hint _ hk) (ae_of_all _ bumpW_nonneg)

theorem massW_eq_of_isVagueLimitOn {γ : ℝ} {x : Field} {U : Set ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitOn U (areaApproxC γ x) μ) (hsub : closedBall c₀ (1 / 40) ⊆ U)
    (hfin : ∀ᶠ k in atTop, areaApproxC γ x k (closedBall c₀ (1 / 40)) < ⊤) :
    massW γ x = ∫⁻ z, ENNReal.ofReal (bumpW z) ∂μ :=
  liminf_eq_of_isVagueLimitOn h hsub hfin

/-- a measure charging the small ball has positive bump integral -/
theorem lintegral_bumpW_pos {μ : Measure ℂ} (h : μ (ball c₀ (1 / 40)) ≠ 0) :
    0 < ∫⁻ z, ENNReal.ofReal (bumpW z) ∂μ := by
  refine pos_iff_ne_zero.2 fun h0 => h ?_
  rw [lintegral_eq_zero_iff measurable_bumpW'] at h0
  refine measure_mono_null (fun z hz => ?_) (ae_iff.1 h0)
  simp only [mem_ofPred_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
  exact bumpW_pos hz

/-- additive constants multiply `massW` by `e^{γc}` -/
theorem massW_addConst {γ : ℝ} {x : Field} (hx : ConeArea.HasCircleAvgs x) (c : ℝ) :
    massW γ (addConst x c) = ENNReal.ofReal (Real.exp (γ * c)) * massW γ x := by
  unfold massW
  simp_rw [ConeArea.areaApproxC_addConst hx c, lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top

theorem massW_addConst_pos_iff {γ : ℝ} {x : Field} (hx : ConeArea.HasCircleAvgs x) (c : ℝ) :
    0 < massW γ (addConst x c) ↔ 0 < massW γ x := by
  rw [massW_addConst hx c, ENNReal.mul_pos_iff]
  simp [Real.exp_pos]

/-! ## Positivity for the white-noise field -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {h₀ : Ω → Field}

lemma ball_bump_subset_openSquare : ball c₀ (1 / 40) ⊆ openSquare :=
  (ball_subset_ball (by norm_num)).trans
    (U₀_subset_box₀.trans box₀_subset_openSquare)

/-- **a.s. positivity for the white-noise whole-plane GFF** -/
theorem ae_massW_pos_wn (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) : ∀ᵐ ω ∂P, 0 < massW γ (h₀ ω) := by
  obtain ⟨Y, hY⟩ := exists_isDGMod_h0 hW hh hae
  have hV : ∀ k z, z ∈ dSet U₀ k → (fun ω => circleAvg (h₀ ω) (radius k) z) =ᵐ[P]
      (fun z r ω => circleAvg (h₀ ω) r z) z ((2 : ℝ)⁻¹ ^ k) :=
    fun _ _ _ => ae_of_all _ fun _ => rfl
  have hvag := ae_isVagueLimitOn_muOfMod_loc hW hγ hγ2 isCompact_box₀ box₀_subset_openSquare
    isOpen_U₀ U₀_subset_box₀ hY (V := fun k z ω => circleAvg (h₀ ω) (radius k) z)
    (measurable_circleAvg_h0 hh) hV
  filter_upwards [hvag, ae_areaGood_wn hW hh hae hγ hγ2, DZZ.ae_qArea_wn_ball_pos hW hγ hγ2]
    with ω hv hgood hpos
  have hlim : IsVagueLimitOn U₀ (areaApproxC γ (h₀ ω)) ((muOfMod W γ box₀ Y ω).restrict U₀) := by
    refine isVagueLimitOn_of_restrict isOpen_U₀ ?_
    convert hv using 2 with k
    unfold areaApproxC
    rw [restrict_withDensity isOpen_U₀.measurableSet]
    rfl
  rw [massW_eq_of_isVagueLimitOn hlim closedBall_subset_U₀
    (hgood.2 _ (isCompact_closedBall _ _) closedBall_subset_U₀)]
  apply lintegral_bumpW_pos
  have hbU : ball c₀ (1 / 40) ⊆ U₀ := ball_subset_ball (by norm_num)
  have hbB : ball c₀ (1 / 40) ⊆ box₀ := hbU.trans U₀_subset_box₀
  have hdm : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (γ * -Y z ω)))
      ((muHU W γ ω).restrict box₀) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (hY.1 ω).neg))).measurable.aemeasurable
  rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hbU, muOfMod, Ne,
    withDensity_apply_eq_zero' hdm]
  have hne : {z | ENNReal.ofReal (Real.exp (γ * -Y z ω)) ≠ 0} = univ :=
    eq_univ_of_forall fun z => by simp [Real.exp_pos]
  rw [hne, univ_inter, Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hbB]
  have hq := hpos ((1 / 2 : ℚ), (1 / 2 : ℚ)) (1 / 40 : ℚ) (by norm_num) (by
    have e : ratPt ((1 / 2 : ℚ), (1 / 2 : ℚ)) = c₀ := by
      apply Complex.ext <;> simp [ratPt, c₀]
    rw [e]; push_cast; exact ball_bump_subset_openSquare)
  have e : ratPt ((1 / 2 : ℚ), (1 / 2 : ℚ)) = c₀ := by
    apply Complex.ext <;> simp [ratPt, c₀]
  rw [e] at hq
  push_cast at hq
  exact hq.ne'

/-- **a.s. positivity of `massW` for every whole-plane GFF** (law transfer, as
`ConeArea4.ae_areaGood_U₀`) -/
theorem ae_massW_pos {X : Ω → Field} [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : ∀ᵐ ω ∂P, 0 < massW γ (X ω) := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := DG.exists_wn_wholePlaneGFF
  have hS : MeasurableSet {x : Field | 0 < massW γ x} :=
    measurableSet_lt measurable_const (measurable_massW γ)
  have hXn := isWholePlaneGFF_normField hX
  have hhn := isWholePlaneGFF_normField hh
  have h0 : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, 0 < massW γ (normField (h₀ ω)) := by
    filter_upwards [ae_massW_pos_wn hW hh hae hγ hγ2, ConeArea3.ae_hasCircleAvgs hh] with ω h1 h2
    rwa [normField, massW_addConst_pos_iff h2]
  have h0' : ∀ᵐ x ∂(LQGDimension.ExistAsm.stdP.map fun ω => normField (h₀ ω)),
      0 < massW γ x :=
    (ae_map_iff hhn.measurable.aemeasurable hS).2 h0
  rw [← map_normField_eq hX hh] at h0'
  have h1 := (ae_map_iff hXn.measurable.aemeasurable hS).1 h0'
  filter_upwards [h1, ConeArea3.ae_hasCircleAvgs hX] with ω hc hca
  rwa [normField, massW_addConst_pos_iff hca] at hc

end ConeArea8
end MatedCRTHarmonic.MoTPort
