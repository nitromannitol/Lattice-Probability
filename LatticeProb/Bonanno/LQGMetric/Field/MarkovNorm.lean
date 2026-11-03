/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovNorm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovExt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Normalized pairings and independence of the two parts (task P2-MARKOV, part 8)

For a whole-plane GFF normalized by `h_1(0) = 0`, every pairing `⟨h, φ⟩`, `φ ∈ 𝓓(ℂ)` (not only
mean-zero ones), lies in the Gaussian space of the mean-zero pairings: it is the `L²` limit of
`⟨h, φ − (∫φ)σₙ⟩` (`exists_tendsto_apxVec`; the increments are `(∫φ)⟨h, σₙ₊₁ − σₙ⟩` with
variance `≤ (∫φ)² 4·2⁻ⁿ`, `logCov_circDiff_succ_le`). For a bounded open `U` disjoint from `∂𝔻`
its covariance with the Dirichlet pairings is `∫ f φ` (`inner_pairVec_cmLin`; the correction
`∫ f σₙ` vanishes once `σₙ` is supported off `supp f`), so `[⟨h, φ⟩]` pairs with `H₀¹(U)` like the
Riesz vector of `φ 1_U` (`inner_pairVec_cmIso`). Consequently the harmonic part
`𝔥(φ) := ⟨h, φ⟩ − ⟨h̊, φ 1_U⟩` is orthogonal to, hence independent of, the zero-boundary part
(`indepFun_harm_zbExt`): the clause "`h̊` is independent of `𝔥`" of LM Lemma 2.1 at the level of
pairings (IG4 Prop. 2.8: `h = h₁ + h₂` with independent projections; BP Thm 1.52).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovNorm

open MarkovGauss MarkovZB MarkovGerm MarkovExt CircleAvg Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- `[⟨h, φ − (∫φ)σₙ⟩] ∈ L²(P)` -/
def apxVec (hh : IsWholePlaneGFF h P) (φ : TestC) (n : ℕ) : Lp ℝ 2 P :=
  (memLp_pair hh (meanZeroApprox φ n)).toLp _

lemma pair_meanZeroApprox_succ_sub (g : DistC) (φ : TestC) (n : ℕ) :
    g (meanZeroApprox φ (n + 1)).1 - g (meanZeroApprox φ n).1 =
      -(∫ x, φ x) * g (circDiff (n + 1) 0 1 n 0 1).1 := by
  rw [meanZeroApprox_apply, meanZeroApprox_apply, ← mollAvg_sub_eq]; ring

lemma norm_apxVec_sub (hh : IsWholePlaneGFF h P) (φ : TestC) (n : ℕ) :
    ‖apxVec hh φ (n + 1) - apxVec hh φ n‖ ≤ (2 * |∫ x, φ x|) * Real.sqrt 2⁻¹ ^ n := by
  have hD := memLp_pair hh (circDiff (n + 1) 0 1 n 0 1)
  have heq : apxVec hh φ (n + 1) - apxVec hh φ n = (-(∫ x, φ x)) • hD.toLp _ := by
    rw [apxVec, apxVec, ← MemLp.toLp_sub, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pairProc]
      exact pair_meanZeroApprox_succ_sub (h ω) φ n)
  rw [heq, norm_smul, Real.norm_eq_abs, abs_neg]
  have hn : ‖hD.toLp (pairProc h (circDiff (n + 1) 0 1 n 0 1))‖ ≤ 2 * Real.sqrt 2⁻¹ ^ n := by
    have h2 : ‖hD.toLp (pairProc h (circDiff (n + 1) 0 1 n 0 1))‖ ^ 2 ≤
        (2 * Real.sqrt 2⁻¹ ^ n) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_cov _ _ (centered_pairProc hh _)]
      refine ((hh.covariance_eq _ _).trans_le (logCov_circDiff_succ_le one_pos 0 n)).trans_eq ?_
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num)]
      norm_num
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  calc |∫ x, φ x| * ‖hD.toLp _‖ ≤ |∫ x, φ x| * (2 * Real.sqrt 2⁻¹ ^ n) :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg _)
    _ = _ := by ring

/-- the approximations converge in `L²` to a version of `⟨h, φ⟩` -/
theorem exists_tendsto_apxVec (hh : IsNormalizedWPGFF h P) (φ : TestC) :
    ∃ Y : Lp ℝ 2 P, Tendsto (apxVec hh.1 φ) atTop (𝓝 Y) ∧
      (Y : Ω → ℝ) =ᵐ[P] fun ω => h ω φ := by
  have hr : Real.sqrt 2⁻¹ < 1 := (Real.sqrt_lt' one_pos).2 (by norm_num)
  have hc : CauchySeq (apxVec hh.1 φ) := cauchySeq_of_le_geometric _ _ hr fun n => by
    rw [dist_comm, dist_eq_norm]; exact norm_apxVec_sub hh.1 φ n
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨Y, hY, ?_⟩
  have h1 : TendstoInMeasure P (fun n ω => pairProc h (meanZeroApprox φ n) ω) atTop Y :=
    (tendstoInMeasure_of_tendsto_Lp hY).congr_left fun n => (memLp_pair hh.1 _).coeFn_toLp
  have h2 : TendstoInMeasure P (fun n ω => pairProc h (meanZeroApprox φ n) ω) atTop
      fun ω => h ω φ := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (measurable_eval hh.1 _).aestronglyMeasurable)
      ?_
    filter_upwards [ae_tendsto_meanZeroApprox hh] with ω hω using hω φ
  exact tendstoInMeasure_ae_unique h1 h2

/-- `[⟨h, φ⟩] ∈ L²(P)` for a normalized field -/
def pairVec (hh : IsNormalizedWPGFF h P) (φ : TestC) : Lp ℝ 2 P :=
  (exists_tendsto_apxVec hh φ).choose

lemma tendsto_pairVec (hh : IsNormalizedWPGFF h P) (φ : TestC) :
    Tendsto (apxVec hh.1 φ) atTop (𝓝 (pairVec hh φ)) :=
  (exists_tendsto_apxVec hh φ).choose_spec.1

lemma pairVec_ae (hh : IsNormalizedWPGFF h P) (φ : TestC) :
    (pairVec hh φ : Ω → ℝ) =ᵐ[P] fun ω => h ω φ :=
  (exists_tendsto_apxVec hh φ).choose_spec.2

theorem pairVec_mem_gaussSpace (hh : IsNormalizedWPGFF h P) (φ : TestC) :
    pairVec hh φ ∈ gaussSpace (pairProc h) (memLp_pair hh.1) :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (tendsto_pairVec hh φ)
    (Eventually.of_forall fun n => toLp_mem_gaussSpace (memLp_pair hh.1) _)

/-- `E[⟨h, φ⟩ (h, f)_∇] = ∫ f φ` for `f ∈ C_c^∞(U)`, `U ∩ ∂𝔻 = ∅` -/
theorem inner_pairVec_cmLin (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) (φ : TestC) (f : zsSub U) :
    ⟪pairVec hh φ, cmLin hh.1 U f⟫ = ∫ x, φ x * f.1 x := by
  set O : Opens ℂ := ⟨(tsupport (f.1))ᶜ, (isClosed_tsupport _).isOpen_compl⟩
  have hO : sphere (0 : ℂ) 1 ⊆ O := fun x hx hxf =>
    Set.disjoint_left.1 hU (f.2.2.2 hxf) hx
  obtain ⟨N, hN⟩ := exists_pow_cthickening_subset hO
  have hev : ∀ n, N ≤ n → ⟪apxVec hh.1 φ n, cmLin hh.1 U f⟫ = ∫ x, φ x * f.1 x := by
    intro n hn
    simp only [apxVec, cmLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [inner_toLp_eq_cov _ _ (centered_pairProc hh.1 _)]
    refine (hh.1.covariance_eq _ _).trans ((logCov_cmTest_right _ _).trans ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change (φ x - (∫ y, φ y) * circBump n 0 1 x) * f.1 x = φ x * f.1 x
    by_cases hx : x ∈ tsupport f.1
    · rw [circBump_eq_zero fun hc => hN n hn hc hx]; ring
    · rw [image_eq_zero_of_notMem_tsupport hx]; ring
  have hlim := (tendsto_pairVec hh φ).inner (𝕜 := ℝ) (tendsto_const_nhds (x := cmLin hh.1 U f))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn =>
    (hev n hn).symm⟩))

omit [IsProbabilityMeasure P] in
lemma cov_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- `∫ f d(ρ⁺) − ∫ f d(ρ⁻) = ∫ ρ f` for bounded measurable `ρ` and `f ∈ C_c^∞` -/
lemma integral_testMeas_sub {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    ∫ x, f x ∂(testMeasPos ρ) - ∫ x, f x ∂(testMeasNeg ρ) = ∫ x, ρ x * f x := by
  have hfi : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  have i1 : Integrable fun x => max (ρ x) 0 * f x :=
    hfi.bdd_mul (hρ.max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le ((le_abs_self _).trans (hC z)) ((abs_nonneg _).trans (hC z)))
  have i2 : Integrable fun x => max (-ρ x) 0 * f x :=
    hfi.bdd_mul (hρ.neg.max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le ((neg_le_abs _).trans (hC z)) ((abs_nonneg _).trans (hC z)))
  rw [integral_testMeasPos_K3 hρ, integral_testMeasNeg_K3 hρ, ← integral_sub i1 i2]
  congr 1; funext x; rw [← sub_mul, max_sub_max_neg_K3]

/-- `[⟨h, φ⟩]` pairs with `H₀¹(U)` like the Riesz vector of `φ 1_U` (bounded `U`, `U ∩ ∂𝔻 = ∅`) -/
theorem inner_pairVec_cmIso (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) (hUb : Bornology.IsBounded (U : Set ℂ))
    (φ : TestC) (v : gradClosure (U : Set ℂ) (zeroSpace U)) :
    ⟪pairVec hh φ, cmIso hh.1 U v⟫ = ⟪rieszFun U ((U : Set ℂ).indicator φ), (v : GradSpace U)⟫ := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact isClosed_eq ((continuous_const.inner continuous_id).comp (cmIso hh.1 U).continuous)
      (continuous_const.inner continuous_subtype_val)
  by_cases hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g
  · rw [cmIso_gradLin, inner_pairVec_cmLin hh hU φ f]
    change _ = ⟪rieszFun U ((U : Set ℂ).indicator φ), gradFeat U f.1⟫
    have hadm := admissible_bddOn hUb (extZeroTest U φ)
    obtain ⟨hm, ⟨C, hC⟩, -⟩ := (extZeroTest U φ).2
    rw [rieszFun, inner_sub_left]
    change ∫ x, φ x * f.1 x =
      ⟪rieszVec U (zeroSpace U) (testMeasPos (extZeroTest U φ).1), gradFeat U f.1⟫ -
      ⟪rieszVec U (zeroSpace U) (testMeasNeg (extZeroTest U φ).1), gradFeat U f.1⟫
    rw [pair_rieszVec hV hadm.1 hpos f.1 f.2,
      pair_rieszVec hV hadm.2 hpos f.1 f.2]
    change _ = ∫ x, f.1 x ∂testMeasPos (extZeroTest U φ).1 -
      ∫ x, f.1 x ∂testMeasNeg (extZeroTest U φ).1
    rw [integral_testMeas_sub hm hC f.2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change φ x * f.1 x = (U : Set ℂ).indicator φ x * f.1 x
    by_cases hx : x ∈ (U : Set ℂ)
    · rw [indicator_of_mem hx]
    · rw [image_eq_zero_of_notMem_tsupport fun h' => hx (f.2.2.2 h'), mul_zero, mul_zero]
  · have h0 : gradLin U f = 0 := Subtype.ext (gradFeat_eq_zero_of_energy hV f.2
      (le_antisymm (not_lt.1 fun hlt => hpos ⟨f.1, f.2, hlt⟩) (energy_nonneg _ _)))
    rw [h0, map_zero, inner_zero_right, ZeroMemClass.coe_zero, inner_zero_right]

end MarkovNorm
end LQGMetric
