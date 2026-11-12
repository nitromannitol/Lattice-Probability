/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent3Vague at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Law

/-!
# Law transfer, part 2: a.s. vague limits for circle-determined fields (P2-GMCID3, D85)

* `VagueGood γ x`: the deterministic hypotheses of DS's existence argument (convergence of the
  test integrals of a fixed countable dense family times cut-offs, local finiteness at fine
  scales); `exists_isVagueLimitOn_of_good` (the deterministic tail of
  `ae_exists_isVagueLimitOn_openSquare`, QZ `VagueOpen.exists_isVagueLimitOn_of_cutoff`);
  `measurableSet_vagueGood`: the event is measurable in the field sample.
* `ae_isVagueLimitOn_circExt`: under the law `ν` of the circle family of a zero-boundary GFF,
  `qAreaMeasureOn γ (circExt v) 𝕍` is a.s. the vague limit; `ae_isVagueLimitOn_wn`: the same for
  the white-noise field `circExt (wnCircVec W)`.
* `ae_iff_wn`: an a.s. property of `M_γ` transfers between an arbitrary zero-boundary GFF `X`
  and the white-noise field, as soon as the event is null-measurable for `ν` (D85).
* `measurable_integral_areaApprox`: test integrals of the approximations are measurable in the
  field sample (input for the `L¹` transfer).

Source: Duplantier–Sheffield arXiv:0808.1560 Prop. 1.1 (existence; same argument as
`GMCSqExist.lean`); the transfer is orchestrator decision D85.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent3

open GMCIdent WhiteNoise

/-- a fixed countable dense test family -/
def denseF : Set (ℂ → ℝ) := VagueH.exists_denseTestFamily.choose

lemma denseF_countable : denseF.Countable := VagueH.exists_denseTestFamily.choose_spec.1

lemma denseF_dense : VagueH.IsDenseTestFamily denseF := VagueH.exists_denseTestFamily.choose_spec.2

/-- the deterministic hypotheses of the existence argument -/
def VagueGood (γ : ℝ) (x : FieldSample) : Prop :=
  (∀ n : ℕ, ∀ g ∈ denseF, ∃ l,
    Tendsto (fun k => ∫ z, sqCut n z * g z ∂(areaApprox γ x k)) atTop (𝓝 l)) ∧
  ∀ n k : ℕ, radius k < 1 / ((n : ℝ) + 2) / 2 →
    areaApprox γ x k (sqIn (1 / ((n : ℝ) + 2))) < ∞

theorem exists_isVagueLimitOn_of_good {γ : ℝ} {x : FieldSample} (h : VagueGood γ x) :
    ∃ μ, IsVagueLimitOn openSquare (areaApprox γ x) μ := by
  obtain ⟨h1, h2⟩ := h
  have hr : Tendsto radius atTop (𝓝 0) := by
    unfold radius; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsq : ∀ K, IsCompact K → K ⊆ openSquare → ∃ n : ℕ, K ⊆ sqIn (2 / ((n : ℝ) + 2)) := by
    intro K hK hKU
    obtain ⟨s, hs, hKs⟩ := exists_sqIn_of_isCompact hK hKU
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / s)
    refine ⟨n, hKs.trans fun z ⟨a, b, c, d⟩ => ?_⟩
    have : 2 / ((n : ℝ) + 2) ≤ s := by
      rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hs] at hn; nlinarith
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine VagueOpen.exists_isVagueLimitOn_of_cutoff isOpen_openSquare openSquare_subset_H
    continuous_sqCut sqCut_nonneg sqCut_le_one tsupport_sqCut_subset_openSquare ?_ denseF_dense ?_
    h1
  · intro K hK hKU
    obtain ⟨n, hn⟩ := hsq K hK hKU
    exact ⟨n, fun z hz => sqCut_eq_one (hn hz)⟩
  · intro K hK hKU
    obtain ⟨n, hn⟩ := hsq K hK hKU
    have hsub : K ⊆ sqIn (1 / ((n : ℝ) + 2)) := hn.trans fun z ⟨a, b, c, d⟩ => by
      have : 1 / ((n : ℝ) + 2) ≤ 2 / ((n : ℝ) + 2) :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    filter_upwards [hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((n : ℝ) + 2) / 2 by
      positivity))] with k hk
    exact (measure_mono hsub).trans_lt (h2 n k hk)

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

theorem ae_vagueGood [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : ∀ᵐ ω ∂P, VagueGood γ (X ω) := by
  have hconv : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ g ∈ denseF, ∃ l,
      Tendsto (fun k => ∫ z, sqCut n z * g z ∂(areaApprox γ (X ω) k)) atTop (𝓝 l) := by
    rw [ae_all_iff]; intro n
    rw [ae_ball_iff denseF_countable]; intro g hg
    obtain ⟨hgc, hgs, -⟩ := denseF_dense.1 g hg
    exact ae_tendsto_areaApprox_sq hX hγ hγ2 ((continuous_sqCut n).mul hgc) hgs.mul_left
      (tsupport_mul_subset_left.trans (tsupport_sqCut_subset_openSquare n))
  have hfin0 : ∀ᵐ ω ∂P, ∀ n k : ℕ, radius k < 1 / ((n : ℝ) + 2) / 2 →
      areaApprox γ (X ω) k (sqIn (1 / ((n : ℝ) + 2))) < ∞ := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    by_cases hk : radius k < 1 / ((n : ℝ) + 2) / 2
    · filter_upwards [ae_areaApprox_sqIn_lt_top hX γ n k hk] with ω h _ using h
    · exact ae_of_all _ fun ω h => absurd h hk
  filter_upwards [hconv, hfin0] with ω h1 h2
  exact ⟨h1, h2⟩

/-- test integrals of the approximations are measurable in the field sample -/
lemma measurable_integral_areaApprox (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Measurable f) {s : ℝ}
    (hs : 0 < s) (hfS : ∀ z ∉ sqIn s, f z = 0) :
    Measurable fun x : FieldSample => ∫ z, f z ∂(areaApprox γ x k) := by
  have e : (fun x : FieldSample => ∫ z, f z ∂(areaApprox γ x k)) =
      fun x => ∫ z in sqIn s, f z * sDens γ (fun x : FieldSample => x) k z x :=
    funext fun x => integral_areaApprox_sq (X := fun x : FieldSample => x) γ k (sqIn_subset_H hs)
      hfS x
  rw [e]
  have hj : Measurable fun p : ℂ × FieldSample => avgReg p.2 k p.1 :=
    (measurable_avgReg k).comp (measurable_snd.prodMk measurable_fst)
  have hi : Measurable fun p : ℂ × FieldSample =>
      f p.1 * sDens γ (fun x : FieldSample => x) k p.1 p.2 :=
    (hf.comp measurable_fst).mul (measurable_const.mul (Real.measurable_exp.comp (hj.const_mul γ)))
  exact hi.stronglyMeasurable.integral_prod_left.measurable

lemma measurable_integral_areaApprox_cpt (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare) :
    Measurable fun x : FieldSample => ∫ z, f z ∂(areaApprox γ x k) := by
  obtain ⟨s, hs, hTs⟩ := exists_sqIn_of_isCompact hfc.isCompact hfU
  exact measurable_integral_areaApprox γ k hf.measurable hs fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hTs h)

theorem measurableSet_vagueGood (γ : ℝ) : MeasurableSet {x : FieldSample | VagueGood γ x} := by
  unfold VagueGood
  simp only [setOf_and, setOf_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.biInter denseF_countable
    fun g hg => ?_) (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_)
  · obtain ⟨hgc, hgs, -⟩ := denseF_dense.1 g hg
    exact StronglyMeasurable.measurableSet_exists_tendsto fun k =>
      (measurable_integral_areaApprox_cpt γ k ((continuous_sqCut n).mul hgc) hgs.mul_left
        (tsupport_mul_subset_left.trans (tsupport_sqCut_subset_openSquare n))).stronglyMeasurable
  · exact MeasurableSet.iInter fun _ => measurableSet_lt ((Measure.measurable_coe
      (isClosed_sqIn _).measurableSet).comp (measurable_areaApprox γ k)) measurable_const

lemma vagueGood_circExt {γ : ℝ} {x : FieldSample} (h : VagueGood γ x) :
    VagueGood γ (circExt (circVec x)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun n g hg => ?_, fun n k hk => ?_⟩
  · obtain ⟨l, hl⟩ := h1 n g hg
    obtain ⟨-, hgs, -⟩ := denseF_dense.1 g hg
    exact ⟨l, hl.congr' ((eventually_integral_areaApprox_circExt γ x hgs.mul_left
      (tsupport_mul_subset_left.trans (tsupport_sqCut_subset_openSquare n))).mono
        fun k hk => hk.symm)⟩
  · have hT : MeasurableSet (sqIn (1 / ((n : ℝ) + 2))) := (isClosed_sqIn _).measurableSet
    have hk' : radius k < 1 / ((n : ℝ) + 2) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    rw [← Measure.restrict_apply_self, areaApprox_restrict_circExt γ hk' x,
      Measure.restrict_apply_self]
    exact h2 n k hk

lemma isVagueLimitOn_qAreaMeasureOn_of_good {γ : ℝ} {x : FieldSample} (h : VagueGood γ x) :
    IsVagueLimitOn openSquare (areaApprox γ x) (qAreaMeasureOn γ x openSquare) := by
  have he := exists_isVagueLimitOn_of_good h
  unfold qAreaMeasureOn
  rw [dif_pos he]
  exact he.choose_spec

/-- the law of the circle family of a zero-boundary GFF -/
abbrev circLaw (P : Measure Ω) (X : Ω → Measure ℂ → ℝ) : Measure (CircIdx → ℝ) :=
  P.map fun ω => circVec (X ω)

theorem ae_vagueGood_circExt [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : ∀ᵐ v ∂(circLaw P X), VagueGood γ (circExt v) := by
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  refine (ae_map_iff (p := fun v => VagueGood γ (circExt v)) hm.aemeasurable
    (measurable_circExt (measurableSet_vagueGood γ))).2 ?_
  filter_upwards [ae_vagueGood hX hγ hγ2] with ω h
  exact vagueGood_circExt h

/-- **a.s. vague limit for the canonical circle-determined field** -/
theorem ae_isVagueLimitOn_circExt [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ v ∂(circLaw P X), IsVagueLimitOn openSquare (areaApprox γ (circExt v))
      (qAreaMeasureOn γ (circExt v) openSquare) := by
  filter_upwards [ae_vagueGood_circExt hX hγ hγ2] with v h
  exact isVagueLimitOn_qAreaMeasureOn_of_good h

/-- **a.s. vague limit for the white-noise field** `circExt (wnCircVec W)` -/
theorem ae_isVagueLimitOn_wn [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', IsVagueLimitOn openSquare (areaApprox γ (circExt (wnCircVec W ω)))
      (qAreaMeasureOn γ (circExt (wnCircVec W ω)) openSquare) := by
  refine ae_of_ae_map (p := fun v => IsVagueLimitOn openSquare (areaApprox γ (circExt v))
    (qAreaMeasureOn γ (circExt v) openSquare)) (measurable_wnCircVec hW).aemeasurable ?_
  rw [← map_circVec_eq hX hW]
  exact ae_isVagueLimitOn_circExt hX hγ hγ2

end GMCIdent3
end LQGMetric
