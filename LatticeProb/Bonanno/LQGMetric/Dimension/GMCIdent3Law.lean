/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent3Law at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent2Circ
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Law transfer for the circle-average LQG measure, part 1: the circle family (P2-GMCID3, D85)

* `CircIdx`: the circles `∂B(z,r)` with `r > 0`, `B̄(z,r) ⊆ 𝕍 = (0,1)²`.
* `circVec x = (x(σ_{z,r}))_{(z,r)}` (`σ_{z,r}` = `foldedCircle z r`, the uniform measure on the
  circle) and `wnCircVec W = (√π W(K_{σ_{z,r}}))_{(z,r)}`.
* **(T1)** `map_circVec_eq`: for every zero-boundary GFF `X` on `𝕍` and every white noise `W`, the
  laws of `circVec ∘ X` and `wnCircVec W` on `CircIdx → ℝ` agree. Both are centred Gaussian
  processes; their covariances agree by `pi_inner_measKerL2_circle` and `circleCov_eq_kernel`
  (both equal `∫∫ G_𝕍 dσ dσ'`). Finite-dimensional laws: QZ `WedgeRes.map_eq_of_gaussian_vec`;
  the law on the product: mathlib `IsProjectiveLimit.unique` (same proof as
  `IsZBGFFProcess.map_eq`, Field/ZeroBoundaryLaw.lean).
* **(T2)** `qAreaMeasureOn_circExt`: `qAreaMeasureOn γ x 𝕍` depends on the field sample `x` only
  through `circVec x`: `qAreaMeasureOn γ (circExt (circVec x)) 𝕍 = qAreaMeasureOn γ x 𝕍`, where the
  measurable map `circExt` extends a circle family by `0` off the circles. The vague-limit
  predicate tests only `f ∈ C_c(𝕍)`, and on `supp f` at fine scales the regularized circle
  averages `avgReg` use only dyadic circles inside `𝕍` (`avgReg_circExt`).

DZZ (arXiv:1807.00422, l. 648–658) identify the LQG measure with the white-noise GMC "in law";
the law-transfer route itself is orchestrator decision D85 (own argument, no source needed beyond
the uniqueness of Gaussian laws).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent3

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2

/-- the circles `∂B(z,r)`, `r > 0`, with `B̄(z,r) ⊆ 𝕍` -/
def CircIdx : Type := {p : ℂ × ℝ // 0 < p.2 ∧ closedBall p.1 p.2 ⊆ openSquare}

/-- the circle-average family of a field sample -/
def circVec (x : FieldSample) : CircIdx → ℝ := fun j => x (foldedCircle j.1.1 j.1.2)

/-- the white-noise circle family `√π W(K_{σ_{z,r}})` -/
def wnCircVec {Ω : Type*} (W : WNSpace → Ω → ℝ) (ω : Ω) : CircIdx → ℝ := fun j =>
  Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif j.1.1 j.1.2)) ω

lemma measurable_circVec : Measurable circVec :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

lemma measurable_wnCircVec {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) : Measurable (wnCircVec W) :=
  measurable_pi_iff.2 fun _ => (hW.measurable _).const_mul _

/-! ## (T1) the two circle families have the same law -/

/-- **(T1)** the circle family of any zero-boundary GFF on `𝕍` and the white-noise circle family
have the same law on `CircIdx → ℝ` -/
theorem map_circVec_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}
    (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W) :
    P.map (fun ω => circVec (X ω)) = P'.map (wnCircVec W) := by
  have := hX.gaussian.isProbabilityMeasure
  have := hW.isProbabilityMeasure
  set U : CircIdx → Ω → ℝ := fun j ω => X ω (foldedCircle j.1.1 j.1.2)
  set V : CircIdx → Ω' → ℝ := fun j ω => wnCircVec W ω j
  have hadm : ∀ j : CircIdx, IsAdmissibleDual openSquare (zeroSpace openSquare)
      (foldedCircle j.1.1 j.1.2) := fun j =>
    isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall j.2.1 j.2.2) j.2.1
  have hU : IsGaussianProcess U P :=
    hX.gaussian.comp_right (fun j : CircIdx =>
      (⟨_, hadm j⟩ : {μ // IsAdmissibleDual openSquare (zeroSpace openSquare) μ}))
  have hV : IsGaussianProcess V P' := by
    have := (hW.isGaussianProcess_comp (fun j : CircIdx =>
      measKerL2 openSquare (Ioi 0) (circleUnif j.1.1 j.1.2))).smul (fun _ => Real.sqrt Real.pi)
    simpa [V, wnCircVec, smul_eq_mul] using this
  have hUm : ∀ j, Measurable (U j) := fun j => hX.measurable_coord _
  have hVm : ∀ j, Measurable (V j) := fun j => (hW.measurable _).const_mul _
  have hm : Measurable fun ω => circVec (X ω) := measurable_pi_iff.2 hUm
  have hm' : Measurable (wnCircVec W) := measurable_wnCircVec hW
  have hfin : ∀ I : Finset CircIdx, (P.map (fun ω => circVec (X ω))).map I.restrict =
      (P'.map (wnCircVec W)).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm,
      Measure.map_map (Finset.measurable_restrict I) hm']
    refine QuantumZipper.WedgeRes.map_eq_of_gaussian_vec
      (U := fun (i : I) ω => U i.1 ω) (V := fun (i : I) ω => V i.1 ω)
      (hU.hasGaussianLaw I) (hV.hasGaussianLaw I)
      (fun i => hUm _) (fun i => hVm _)
      (fun i => (hU.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => (hV.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => hX.centered _ (hadm i.1)) (fun i => ?_) (fun i j => ?_)
    · simp only [V, wnCircVec]
      rw [integral_const_mul, (hW.hasLaw_single _).integral_eq, integral_id_gaussianReal,
        mul_zero]
    · obtain ⟨⟨⟨z, r⟩, hr, hB₁⟩, -⟩ := i
      obtain ⟨⟨⟨w, s⟩, hs, hB₂⟩, -⟩ := j
      simp only [U, V, wnCircVec]
      rw [circleCov_eq_kernel hX hr hs hB₁ hB₂, covariance_const_mul_left,
        covariance_const_mul_right, hW.cov_eq, ← mul_assoc, Real.mul_self_sqrt Real.pi_pos.le,
        pi_inner_measKerL2_circle hr hs hB₁ hB₂]
  exact IsProjectiveLimit.unique (P := fun I => (P'.map (wnCircVec W)).map I.restrict)
    hfin (fun _ => rfl)

/-! ## (T2) the LQG measure factors through the circle family -/

open Classical in
/-- extension of a circle family to a field sample (junk `0` off the circles inside `𝕍`) -/
def circExt (v : CircIdx → ℝ) : FieldSample := fun μ =>
  if h : ∃ j : CircIdx, foldedCircle j.1.1 j.1.2 = μ then v h.choose else 0

lemma measurable_circExt : Measurable circExt := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : ∃ j : CircIdx, foldedCircle j.1.1 j.1.2 = μ
  · simp only [circExt, dif_pos h]; exact measurable_pi_apply _
  · simp only [circExt, dif_neg h]; exact measurable_const

lemma circExt_apply (v : CircIdx → ℝ) (j : CircIdx) :
    circExt v (foldedCircle j.1.1 j.1.2) =
      v (⟨j, rfl⟩ : ∃ i : CircIdx, foldedCircle i.1.1 i.1.2 = foldedCircle j.1.1 j.1.2).choose := by
  unfold circExt
  rw [dif_pos ⟨j, rfl⟩]

lemma circExt_circVec (x : FieldSample) (j : CircIdx) :
    circExt (circVec x) (foldedCircle j.1.1 j.1.2) = x (foldedCircle j.1.1 j.1.2) := by
  have h : ∃ i : CircIdx, foldedCircle i.1.1 i.1.2 = foldedCircle j.1.1 j.1.2 := ⟨j, rfl⟩
  rw [circExt_apply]
  exact congrArg x h.choose_spec

lemma dyadicRound_bounds (n : ℕ) (x : ℝ) :
    x - ((2 : ℝ) ^ n)⁻¹ < dyadicRound n x ∧ dyadicRound n x ≤ x := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  unfold dyadicRound
  constructor
  · rw [lt_div_iff₀ h2, sub_mul, inv_mul_cancel₀ h2.ne', mul_comm]
    linarith [Int.lt_floor_add_one ((2 : ℝ) ^ n * x)]
  · rw [div_le_iff₀ h2, mul_comm]
    exact Int.floor_le _

/-- at fine dyadic scales, circles of radius `r < s` about the rounded points of `sqIn s` lie
inside `𝕍` -/
lemma eventually_inSq_dyadic {s r : ℝ} (hrs : r < s) {z : ℂ} (hz : z ∈ sqIn s) :
    ∀ᶠ n : ℕ in atTop, InSq r (dyadicRoundC n z) := by
  have ht : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.2 hrs))] with n hn
  obtain ⟨a, b, c, d⟩ := hz
  obtain ⟨h1, h2⟩ := dyadicRound_bounds n z.re
  obtain ⟨h3, h4⟩ := dyadicRound_bounds n z.im
  change r < dyadicRound n z.re ∧ dyadicRound n z.re + r < 1 ∧ r < dyadicRound n z.im ∧
    dyadicRound n z.im + r < 1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- the regularized circle averages on `sqIn s` at scales `radius k < s` see only the circle
family -/
lemma avgReg_circExt {s : ℝ} {k : ℕ} (hk : radius k < s) {z : ℂ} (hz : z ∈ sqIn s)
    (x : FieldSample) : avgReg (circExt (circVec x)) k z = avgReg x k z := by
  have he : (fun n => circExt (circVec x) (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      fun n => x (foldedCircle (dyadicRoundC n z) (radius k)) := by
    filter_upwards [eventually_inSq_dyadic hk hz] with n hn
    exact circExt_circVec x ⟨(dyadicRoundC n z, radius k), radius_pos k,
      closedBall_subset_openSquare hn⟩
  unfold avgReg limUnder
  rw [Filter.map_congr he]

lemma areaApprox_restrict_circExt (γ : ℝ) {s : ℝ} {k : ℕ} (hk : radius k < s) (x : FieldSample) :
    (areaApprox γ (circExt (circVec x)) k).restrict (sqIn s) =
      (areaApprox γ x k).restrict (sqIn s) := by
  have hm : MeasurableSet (sqIn s) := (isClosed_sqIn s).measurableSet
  unfold areaApprox
  rw [restrict_withDensity hm, restrict_withDensity hm]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hm] with z hz
  rw [avgReg_circExt hk hz]

lemma integral_areaApprox_circExt (γ : ℝ) {s : ℝ} {k : ℕ} (hk : radius k < s) (x : FieldSample)
    {f : ℂ → ℝ} (hfS : ∀ z ∉ sqIn s, f z = 0) :
    ∫ z, f z ∂(areaApprox γ (circExt (circVec x)) k) = ∫ z, f z ∂(areaApprox γ x k) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := areaApprox γ (circExt (circVec x)) k) hfS,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := areaApprox γ x k) hfS,
    areaApprox_restrict_circExt γ hk x]

/-- test integrals of `f ∈ C_c(𝕍)` against the approximations coincide at fine scales -/
lemma eventually_integral_areaApprox_circExt (γ : ℝ) (x : FieldSample) {f : ℂ → ℝ}
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare) :
    ∀ᶠ k in atTop, ∫ z, f z ∂(areaApprox γ (circExt (circVec x)) k) =
      ∫ z, f z ∂(areaApprox γ x k) := by
  obtain ⟨s, hs, hTs⟩ := exists_sqIn_of_isCompact hfc.isCompact hfU
  have hfS : ∀ z ∉ sqIn s, f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hTs h)
  obtain ⟨k₀, hk₀⟩ := exists_radius_le hs
  filter_upwards [eventually_ge_atTop k₀] with k hk
  exact integral_areaApprox_circExt γ (by linarith [hk₀ k hk, radius_pos k]) x hfS

end GMCIdent3
end LQGMetric
