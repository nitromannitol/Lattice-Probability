/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Loc1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Measure
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of `μ_{ĥ^tr}` (P2-DGLOC, part 1): DG:984 for a general field, on an open set

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:984 ("we can then define
`μ_{h+f}` as the a.s. weak limit `lim ε^{γ²/2} e^{γ(h+f)_ε(z)} dz`"), applied to `h = h^𝕍` and
`f = −Y`, `Y` a continuous modification of `h^𝕍 − G` (DG:986, `G = ĥ^tr` for `μ_{ĥ^tr}`).

`ae_isVagueLimitOn_muOfMod` (S3D105Mu2) proves this for `G = ĥ` on `interior K`. The proof uses
nothing about `ĥ` except the modification hypothesis, so here it is stated for an arbitrary
field `G` (circle averages `G z r`) and an arbitrary open `U ⊆ K`, the version `V k z` being
required only on the dyadic level sets `dSet U k`. Same proof as S3D105Mu/S3D105Mu2 (own glue,
DV-D105-2); it is the input for the locality of `μ_{ĥ^tr}` (DG:1268, 1302–1305): the
approximations on `U` only involve the circle averages of `G` around points of `U`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the circle averages of `G`, `h^𝕍` and `Y` are linked (Fubini), on `dSet U k` -/
theorem ae_ae_locCirc_eq (hW : IsWhiteNoise P W) {K U : Set ℂ} (hUK : U ⊆ K)
    (hKU : K ⊆ openSquare) {G : ℂ → ℝ → Ω → ℝ} {Y : ℂ → Ω → ℝ}
    (hY : IsDGMod P K (fun z r ω => dgHU W z r ω - G z r ω) Y)
    {V : ℕ → ℂ → Ω → ℝ} (hVm : ∀ k, Measurable fun p : ℂ × Ω => V k p.1 p.2)
    (hV : ∀ k z, z ∈ dSet U k → V k z =ᵐ[P] G z ((2 : ℝ)⁻¹ ^ k))
    (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), z ∉ dSet U k ∨
      V k z ω = avgReg (wnField W ω) k z - ∫ x, Y x ω ∂(circleUnif z (radius k)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  have hmeas : MeasurableSet {q : ℂ × Ω | q.1 ∉ dSet U k ∨ V k q.1 q.2 =
      avgReg (wnField W q.2) k q.1 - ∫ x, Y x q.2 ∂(circleUnif q.1 (radius k))} := by
    refine ((measurableSet_dSet U k).compl.preimage measurable_fst).union
      (measurableSet_eq_fun (hVm k) ?_)
    refine Measurable.sub ?_ (measurable_circAvg hY.1 hY.2.1 _)
    exact (measurable_avgReg k).comp ((measurable_circExt.comp
      ((measurable_wnCircVec hW).comp measurable_snd)).prodMk measurable_fst)
  refine (Measure.ae_ae_comm hmeas).1 (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ dSet U k
  swap
  · exact Eventually.of_forall fun _ => Or.inl hz
  have hB := closedBall_subset_of_mem_dSet hz
  have hB2 : closedBall z (2 * radius k) ⊆ openSquare := hB.trans (hUK.trans hKU)
  have hBK : closedBall z (radius k) ⊆ K :=
    (closedBall_subset_closedBall (by linarith [radius_pos k])).trans (hB.trans hUK)
  filter_upwards [avgReg_ae_eq_wn hX hW hB2, hY.2.2.2 z (radius k) (radius_pos k) hBK,
    hV k z hz] with ω h1 h2 h3
  right
  rw [h1, h2, h3]
  simp only [dgHU, radius]
  ring

/-- **DG:984 for a general field `G`, on an open `U ⊆ K`**: for `Y` a continuous modification of
`h^𝕍 − G` on the compact `K ⊆ 𝕍` and any jointly measurable `V` with `V k z = G_{2^{-k}}(z)` a.s.
for `z ∈ dSet U k`, a.s. `(2^{-k})^{γ²/2} e^{γ V k z} dz → e^{−γY} μ_{h^𝕍}` vaguely on `U` -/
theorem ae_isVagueLimitOn_muOfMod_loc (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare) {U : Set ℂ}
    (hUo : IsOpen U) (hUK : U ⊆ K) {G : ℂ → ℝ → Ω → ℝ} {Y : ℂ → Ω → ℝ}
    (hY : IsDGMod P K (fun z r ω => dgHU W z r ω - G z r ω) Y)
    {V : ℕ → ℂ → Ω → ℝ} (hVm : ∀ k, Measurable fun p : ℂ × Ω => V k p.1 p.2)
    (hV : ∀ k z, z ∈ dSet U k → V k z =ᵐ[P] G z ((2 : ℝ)⁻¹ ^ k)) :
    ∀ᵐ ω ∂P, IsVagueLimitOn U
      (fun k => (volume.restrict U).withDensity fun z =>
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ (γ ^ 2 / 2) * Real.exp (γ * V k z ω)))
      ((muOfMod W γ K Y ω).restrict U) := by
  have := hW.isProbabilityMeasure
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  have hUS : U ⊆ openSquare := hUK.trans hKU
  have hne : (Uᶜ).Nonempty := ⟨0, fun h => by have := hUS h; simp [openSquare] at this⟩
  have hr : Tendsto radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [ae_isVagueLimitOn_wn hX hW hγ hγ2, ae_areaApprox_wnField_lt_top hW γ,
    ae_all_iff.2 (ae_ae_locCirc_eq hW hUK hKU hY hVm hV)] with ω hvag hfin hdens
  have hvag' : IsVagueLimitOn openSquare (areaApprox γ (wnField W ω)) (muHU W γ ω) := hvag
  have hYc := hY.1 ω
  have hec : Continuous fun z => Real.exp (γ * -Y z ω) :=
    Real.continuous_exp.comp (continuous_const.mul hYc.neg)
  refine ⟨?_, fun C hC hCU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hUo.measurableSet.compl, compl_inter_self, measure_empty]
  · calc _ ≤ muOfMod W γ K Y ω univ :=
          (Measure.le_iff'.1 Measure.restrict_le_self C).trans (measure_mono (subset_univ C))
      _ < ⊤ := muOfMod_univ_lt_top W γ hK hKU hY.1 ω
  have hf0 : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hlim : ∫ z, f z ∂((muOfMod W γ K Y ω).restrict U) =
      ∫ z, f z * Real.exp (γ * -Y z ω) ∂(muHU W γ ω) := by
    unfold muOfMod
    rw [restrict_withDensity hUo.measurableSet, GMCIdent4.integral_withDensity_ofReal hec.measurable
      (fun _ => (Real.exp_pos _).le), Measure.restrict_restrict hUo.measurableSet,
      inter_eq_left.2 hUK, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hf0 z (fun h => hz (hfU h))])]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    ring
  rw [hlim]
  refine tendsto_integral_of_density hUS hvag' ?_ hec
    (ek := fun k z => Real.exp (γ * -∫ x, Y x ω ∂(circleUnif z (radius k)))) ?_ ?_ ?_ hf hfc hfU
  · intro C hC hCU
    obtain ⟨s, hs, hCs⟩ := exists_sqIn_of_isCompact hC (hCU.trans hUS)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / s)
    have hns : 1 / ((n : ℝ) + 2) ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hs] at hn
      nlinarith
    have hsub : sqIn s ⊆ sqIn (1 / ((n : ℝ) + 2)) := fun z ⟨a, b, c, d⟩ =>
      ⟨by linarith, by linarith, by linarith, by linarith⟩
    filter_upwards [hr.eventually (gt_mem_nhds
      (show (0 : ℝ) < 1 / ((n : ℝ) + 2) / 2 by positivity))] with k hk
    exact (measure_mono (hCs.trans hsub)).trans_lt (hfin n k hk)
  · intro k
    exact Real.measurable_exp.comp ((((measurable_circAvg hY.1 hY.2.1 (radius k)).comp
      (measurable_id.prodMk measurable_const)).neg).const_mul γ)
  · intro C hC _
    exact tendstoUniformlyOn_exp_neg γ hC hYc (tendstoUniformlyOn_circleAvg hYc hC)
  · intro g hg hgc hgU
    have hg0 : ∀ z, z ∉ tsupport g → g z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
    obtain ⟨δ, hδ, hδC⟩ : ∃ δ > 0, ∀ z ∈ tsupport g, δ ≤ infDist z Uᶜ := by
      rcases (tsupport g).eq_empty_or_nonempty with he | hCne
      · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (notMem_empty z)⟩
      obtain ⟨z₀, hz₀, hmin⟩ := (hgc : IsCompact (tsupport g)).exists_isMinOn hCne
        (continuous_infDist_pt _).continuousOn
      exact ⟨_, (hUo.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h (hgU hz₀)),
        fun z hz => hmin hz⟩
    filter_upwards [hr.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))] with k hk
    have hdm : Measurable fun z => ((2 : ℝ)⁻¹ ^ k) ^ (γ ^ 2 / 2) * Real.exp (γ * V k z ω) :=
      (Real.measurable_exp.comp (((hVm k).comp
        (measurable_id.prodMk measurable_const)).const_mul γ)).const_mul _
    have ham : Measurable fun z =>
        radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (wnField W ω) k z) :=
      have hav : Measurable fun z => avgReg (wnField W ω) k z :=
        (measurable_avgReg k).comp (f := fun z : ℂ => (wnField W ω, z))
          (measurable_const.prodMk measurable_id)
      (Real.measurable_exp.comp (hav.const_mul γ)).const_mul _
    rw [GMCIdent4.integral_withDensity_ofReal hdm (fun _ => by positivity)]
    unfold areaApprox
    rw [GMCIdent4.integral_withDensity_ofReal ham
      (fun _ => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by simp [hg0 z (fun h => hz (hgU h))]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by simp [hg0 z (fun h => hz (openSquare_subset_H (hUS (hgU h))))])]
    refine integral_congr_ae ?_
    filter_upwards [hdens k] with z hz
    by_cases hzC : z ∈ tsupport g
    · have hzD : z ∈ dSet U k := by
        show 2 * radius k < infDist z Uᶜ
        linarith [hδC z hzC]
      rcases hz with hz | hz
      · exact absurd hzD hz
      rw [hz, show γ * (avgReg (wnField W ω) k z - ∫ x, Y x ω ∂(circleUnif z (radius k))) =
        γ * avgReg (wnField W ω) k z + γ * -∫ x, Y x ω ∂(circleUnif z (radius k)) by ring,
        Real.exp_add]
      simp only [radius]
      ring
    · simp [hg0 z hzC]

end DG
end LQGMetric
