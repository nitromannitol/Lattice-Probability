/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovVer2Fub at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer2Rect
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer2SFub
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVerCont

/-!
# Leaf (V) of the Markov property: the extension by zero of `h̊` is a random distribution
(task P2-MKV)

With `Y` the continuous version of the rectangle field `F(x) = ⟨h̊, 1_V 1_{[0,x]}⟩`
(`exists_continuous_rectVec`), `⟨h̊, 1_V φ⟩ = ∫ Y ∂_re∂_im φ` a.s. for every `φ ∈ 𝓓(ℂ)`
(`ae_integral_d12_mul_Y`). Proof: in the Cameron–Martin space the Bochner integral
`∫ ∂_re∂_im φ(x) R(1_V 1_{[0,x]}) dx` is the Riesz vector `R(1_V φ)` (pair with `∇f`,
`f ∈ C_c^∞(V)`: Fubini and `GFFExist.integral_d12_mul_rectInd`); push it through the isometry
`cmIso`; the stochastic Fubini step `integral_A_mul_gen` identifies `E[(∫ Y ∂∂φ) Z]` with
`E[⟨h̊, 1_V φ⟩ Z]` for all `Z ∈ L²(P)`.

Hence a.s. the countable family `c ↦ ⟨h̊, 1_V comb c⟩` is the pairing family of the
distribution `gffOf Y` (`ae_zbExt_mem_rangeSet`), and leaf (V) follows from
`MarkovVer.exists_dist_version_zbExt_of_adm` (`exists_dist_version_zbExt`).

Route: as for the whole-plane field in `ExistGFF` (own elementary proof; the published proofs
that the zero-boundary GFF is a random distribution, Sheffield math/0312099 §2 and
Berestycki–Powell arXiv:2404.16642 §1, use Sobolev-space series instead; the version step is
BP `definitionGFF.tex` l. 842–862 via `RandomDistVersion.exists_version`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovVer2

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm MarkovVer GFFExist Blueprint
  QuantumZipper QuantumZipper.K3

/-- Fubini against rectangles: `∫ ∂∂φ(x) ∫ 1_{[0,x]} K = ∫ φ K` (after `GFFExist` `ExistKerId`) -/
lemma integral_d12_mul_integral_rect (φ : TestC) {K : ℂ → ℝ} (hKm : Measurable K) {Kb : ℝ}
    (hKb : ∀ u, |K u| ≤ Kb) :
    ∫ x, d12 φ x * ∫ u, rectInd x u * K u = ∫ u, φ u * K u := by
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 φ)
  set H : ℂ × ℂ → ℝ := fun p => d12 φ p.1 * (rectInd p.1 p.2 * K p.2) with hH
  have hHm : Measurable H :=
    ((d12 φ).continuous.measurable.comp measurable_fst).mul
      (measurable_rectInd₂.mul (hKm.comp measurable_snd))
  have hdom : Integrable (fun p : ℂ × ℂ => |d12 φ p.1| *
      (closedBall (0 : ℂ) (2 * L)).indicator (fun _ => Kb) p.2) (volume.prod volume) :=
    (GFFInv.integrable_test (d12 φ)).abs.mul_prod
      ((integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne))
  have hHi : Integrable H (volume.prod volume) := by
    refine hdom.mono' hHm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [hH, Real.norm_eq_abs, abs_mul]
    by_cases hx : L < ‖p.1‖
    · rw [hL _ hx]; simp
    · push_neg at hx
      by_cases hu : p.2 ∈ closedBall (0 : ℂ) (2 * L)
      · rw [indicator_of_mem hu]
        have h1 := (rectInd_bddSupp p.1).bdd p.2
        gcongr
        calc |rectInd p.1 p.2| * |K p.2| ≤ 1 * Kb :=
              mul_le_mul h1 (hKb _) (abs_nonneg _) zero_le_one
          _ = Kb := one_mul _
      · have hu' : 2 * ‖p.1‖ < ‖p.2‖ := by
          rw [mem_closedBall, dist_zero_right, not_le] at hu; linarith
        rw [rectInd_eq_zero_of hu', indicator_of_notMem hu]; simp
  have e1 : ∀ x, d12 φ x * ∫ u, rectInd x u * K u = ∫ u, H (x, u) := fun x => by
    simp only [hH]; rw [integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun x u => H (x, u)) hHi]
  congr 1; funext u
  simp only [hH]
  have e2 : ∀ x, d12 φ x * (rectInd x u * K u) = (d12 φ x * rectInd x u) * K u := fun x => by ring
  simp_rw [e2]
  rw [integral_mul_const, integral_d12_mul_rectInd]

lemma isBddDensOn_indicator_test (V : Opens ℂ) (φ : TestC) :
    ∃ A, 1 ≤ A ∧ IsBddDensOn V A ((V : Set ℂ).indicator φ) := by
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish φ
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  refine ⟨L + 1, by linarith, (φ.continuous.measurable.indicator V.isOpen.measurableSet),
    ⟨C, fun z => ?_⟩, fun z hz => ?_, fun z hz => indicator_of_notMem hz _⟩
  · by_cases h : z ∈ (V : Set ℂ)
    · rw [indicator_of_mem h, ← Real.norm_eq_abs]; exact hC z
    · rw [indicator_of_notMem h, abs_zero]; exact (norm_nonneg _).trans (hC z)
  · rw [mem_ball, dist_zero_right, not_lt] at hz
    by_cases h : z ∈ (V : Set ℂ)
    · rw [indicator_of_mem h]; exact hL z (by linarith)
    · exact indicator_of_notMem h _

/-- deterministic identity, paired with `∇f` -/
lemma integral_d12_inner_rieszFun {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1))
    (φ : TestC) {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) (hp : 0 < dirichletEnergyOn V f) :
    ∫ x, d12 φ x * ⟪rieszFun V (rectDens V x), gradFeat V f⟫ =
      ⟪rieszFun V ((V : Set ℂ).indicator φ), gradFeat V f⟫ := by
  have hfc : Continuous f := hf.1.continuous
  obtain ⟨Cf, hCf⟩ := hfc.bounded_above_of_compact_support hf.2.1
  have hKm : Measurable ((V : Set ℂ).indicator f) :=
    hfc.measurable.indicator V.isOpen.measurableSet
  have hKb : ∀ u, |(V : Set ℂ).indicator f u| ≤ Cf := fun u => by
    by_cases h : u ∈ (V : Set ℂ)
    · rw [indicator_of_mem h, ← Real.norm_eq_abs]; exact hCf u
    · rw [indicator_of_notMem h, abs_zero]; exact (norm_nonneg _).trans (hCf u)
  have e : ∀ x, ⟪rieszFun V (rectDens V x), gradFeat V f⟫ =
      ∫ u, rectInd x u * (V : Set ℂ).indicator f u := fun x => by
    rw [inner_rieszFun_gradFeat hV (isBddDensOn_rectDens V (A := |x.re| + |x.im| + 1)
      (by linarith)) hf hp]
    congr 1; funext u
    by_cases h : u ∈ (V : Set ℂ)
    · simp [rectDens, indicator_of_mem h]
    · simp [rectDens, indicator_of_notMem h]
  simp_rw [e]
  obtain ⟨A, -, hφA⟩ := isBddDensOn_indicator_test V φ
  rw [integral_d12_mul_integral_rect φ hKm hKb, inner_rieszFun_gradFeat hV hφA hf hp]
  congr 1; funext u
  by_cases h : u ∈ (V : Set ℂ)
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the Riesz vector of `1_V 1_{[0,x]}` in the Cameron–Martin space -/
def rVec (V : Opens ℂ) (x : ℂ) : gradClosure (V : Set ℂ) (zeroSpace V) :=
  ⟨rieszFun V (rectDens V x), rieszFun_mem V _⟩

lemma rectVec_zero (hh : IsWholePlaneGFF h P) (V : Opens ℂ) : rectVec hh V 0 = 0 := by
  have h0 : rectDens V 0 = 0 := funext fun u => by simp [rectDens, rectInd_zero]
  have : (⟨rieszFun V 0, rieszFun_mem V 0⟩ : gradClosure (V : Set ℂ) (zeroSpace V)) = 0 :=
    Subtype.ext (rieszFun_zero V)
  rw [rectVec, extVec, h0, this, map_zero]

lemma continuous_rectVec (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) : Continuous (rectVec hh V) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set A := ‖x0‖ + 1
  set c := 2 * Real.pi * (2 * A + 1) ^ 3
  have hb : ∀ᶠ x in 𝓝 x0, ‖rectVec hh V x - rectVec hh V x0‖ ≤ √(c * (2 * (4 * A * ‖x - x0‖))) := by
    filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
    rw [mem_ball, dist_eq_norm] at hx
    have hxA : ‖x‖ ≤ A := by
      have := norm_le_norm_add_norm_sub' x x0
      have : ‖x - x0‖ = ‖x0 - x‖ := norm_sub_rev _ _
      linarith [norm_sub_norm_le x x0]
    have hx0A : ‖x0‖ ≤ A := by linarith
    have := sq_norm_rectVec_sub_le hh hV (A := A) ((Complex.abs_re_le_norm x).trans hxA)
      ((Complex.abs_im_le_norm x).trans hxA) ((Complex.abs_re_le_norm x0).trans hx0A)
      ((Complex.abs_im_le_norm x0).trans hx0A)
    rw [← abs_of_nonneg (norm_nonneg (rectVec hh V x - rectVec hh V x0))]
    exact Real.abs_le_sqrt this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb ?_
  have hc : Continuous fun x : ℂ => √(c * (2 * (4 * A * ‖x - x0‖))) := by fun_prop
  simpa using hc.tendsto x0

lemma continuous_rVec (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) : Continuous (rVec V) :=
  (cmIso hh V).isometry.comp_continuous_iff.1 (continuous_rectVec hh hV)

/-- **Bochner identity**: `∫ ∂∂φ(x) [⟨h̊, 1_V 1_{[0,x]}⟩] dx = [⟨h̊, 1_V φ⟩]` in `L²(P)`. -/
theorem integral_d12_smul_rectVec (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (φ : TestC) :
    ∫ x, d12 φ x • rectVec hh V x = extVec hh V ((V : Set ℂ).indicator φ) := by
  set K := gradClosure (V : Set ℂ) (zeroSpace V)
  have hDN := isDNSpace_zeroSpace (V : Set ℂ)
  have hi : Integrable fun x => d12 φ x • rVec V x :=
    ((d12 φ).continuous.smul (continuous_rVec hh hV)).integrable_of_hasCompactSupport
      (d12 φ).hasCompactSupport.smul_right
  have hi' : Integrable fun x => d12 φ x • (rVec V x : GradSpace V) :=
    ((d12 φ).continuous.smul (continuous_subtype_val.comp (continuous_rVec hh hV))).integrable_of_hasCompactSupport
      (d12 φ).hasCompactSupport.smul_right
  have hcoe : ((∫ x, d12 φ x • rVec V x : K) : GradSpace V) =
      ∫ x, d12 φ x • (rVec V x : GradSpace V) := by
    have := (K.subtypeL).integral_comp_comm hi
    simpa using this.symm
  have key : (∫ x, d12 φ x • rVec V x : K) =
      ⟨rieszFun V ((V : Set ℂ).indicator φ), rieszFun_mem V _⟩ := by
    apply Subtype.ext
    refine LQGMetric.eq_of_mem_gradClosure (Subtype.mem _) (rieszFun_mem V _) fun f hf => ?_
    rw [hcoe, real_inner_comm, ← integral_inner hi']
    have e : ∫ x, ⟪gradFeat (V : Set ℂ) f, d12 φ x • (rVec V x : GradSpace V)⟫ =
        ∫ x, d12 φ x * ⟪rieszFun V (rectDens V x), gradFeat V f⟫ :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [real_inner_smul_right, rVec]; rw [real_inner_comm])
    rw [e]
    rcases (energy_nonneg (V : Set ℂ) f).lt_or_eq with hp | hz
    · exact integral_d12_inner_rieszFun hV φ hf hp
    · rw [gradFeat_eq_zero_of_energy hDN hf hz.symm]; simp
  have hL := ((cmIso hh V).toContinuousLinearMap).integral_comp_comm hi
  simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul] at hL
  rw [extVec, ← key, ← hL]
  rfl

/-- `E[X Z] = ⟪u, Z⟫` for `X` a representative of `u ∈ L²(P)` -/
lemma integral_mul_eq_inner (u : Lp ℝ 2 P) {X Z : Ω → ℝ} (hX : X =ᵐ[P] u) (hZ : MemLp Z 2 P) :
    ∫ ω, X ω * Z ω ∂P = ⟪u, hZ.toLp Z⟫ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX, hZ.coeFn_toLp] with ω h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.re_to_real]
  simp [mul_comm]

/-- **Stochastic Fubini**: `∫ ∂∂φ(x) Y(x) dx = ⟨h̊, 1_V φ⟩` a.s. -/
theorem ae_integral_d12_mul_Y (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] rectVec hh V x) (φ : TestC) :
    (fun ω => ∫ x, d12 φ x * Y x ω) =ᵐ[P] extVec hh V ((V : Set ℂ).indicator φ) := by
  have hYL2 : ∀ x, MemLp (Y x) 2 P := fun x => (Lp.memLp _).ae_eq (hY x).symm
  have hsq : ∀ x, ∫ ω, Y x ω ^ 2 ∂P = ‖rectVec hh V x‖ ^ 2 := fun x => by
    have := integral_mul_eq_inner (rectVec hh V x) (hY x) (hYL2 x)
    rw [MemLp.toLp_congr (hYL2 x) (Lp.memLp _) (hY x), Lp.toLp_coeFn,
      real_inner_self_eq_norm_sq] at this
    rw [← this]; congr 1; funext ω; ring
  have hYb : ∀ L : ℝ, ∃ Ck, ∀ x : ℂ, ‖x‖ ≤ L → ∫ ω, Y x ω ^ 2 ∂P ≤ Ck := fun L =>
    ⟨2 * Real.pi * (2 * L + 1) ^ 3 * (2 * (4 * L * L)), fun x hx => by
      have hL : 0 ≤ L := (norm_nonneg _).trans hx
      have := sq_norm_rectVec_sub_le hh hV (x' := 0) (A := L)
        ((Complex.abs_re_le_norm x).trans hx) ((Complex.abs_im_le_norm x).trans hx)
        (by simpa using hL) (by simpa using hL)
      rw [rectVec_zero, sub_zero, sub_zero] at this
      rw [hsq]
      refine this.trans ?_
      have : 0 ≤ 2 * Real.pi * (2 * L + 1) ^ 3 := by positivity
      gcongr⟩
  set u := extVec hh V ((V : Set ℂ).indicator φ)
  set A : Ω → ℝ := fun ω => ∫ x, d12 φ x * Y x ω
  have hAL : MemLp A 2 P := memLp_A_gen hYc hYm hYL2 hYb φ
  have hAZ : ∀ {Z : Ω → ℝ} (hZ : MemLp Z 2 P), ∫ ω, A ω * Z ω ∂P = ∫ ω, u ω * Z ω ∂P := by
    intro Z hZ
    rw [integral_A_mul_gen hYc hYm hYL2 hYb φ hZ,
      integral_mul_eq_inner u EventuallyEq.rfl hZ]
    have e : ∀ x, ∫ ω, Y x ω * Z ω ∂P = ⟪rectVec hh V x, hZ.toLp Z⟫ := fun x =>
      integral_mul_eq_inner _ (hY x) hZ
    simp_rw [e]
    have hi : Integrable fun x => d12 φ x • rectVec hh V x :=
      ((d12 φ).continuous.smul (continuous_rectVec hh hV)).integrable_of_hasCompactSupport
        (d12 φ).hasCompactSupport.smul_right
    rw [show u = ∫ x, d12 φ x • rectVec hh V x from (integral_d12_smul_rectVec hh hV φ).symm,
      real_inner_comm, ← integral_inner hi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [real_inner_smul_right]
    rw [real_inner_comm]
  have hD : MemLp (fun ω => A ω - u ω) 2 P := hAL.sub (Lp.memLp u)
  have h0 : ∫ ω, (A ω - u ω) ^ 2 ∂P = 0 := by
    have e : ∀ ω, (A ω - u ω) ^ 2 = A ω * (A ω - u ω) - u ω * (A ω - u ω) := fun ω => by ring
    simp_rw [e]
    have i1 : Integrable (fun ω => A ω * (A ω - u ω)) P := hAL.integrable_mul hD
    have i2 : Integrable (fun ω => u ω * (A ω - u ω)) P := (Lp.memLp u).integrable_mul hD
    rw [integral_sub i1 i2, hAZ hD, sub_self]
  have h1 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (A ω - u ω))
    hD.integrable_sq).mp h0
  filter_upwards [h1] with ω hω
  have : (A ω - u ω) ^ 2 = 0 := hω
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- **A.s. admissibility** of the extension by zero on the countable coordinate family. -/
theorem ae_zbExt_mem_rangeSet (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) :
    ∀ᵐ ω ∂P, (fun c => zbExt hh.1 V (comb ⊤ c) ω) ∈ rangeSet ⊤ := by
  obtain ⟨Y, hYc, hYm, hY⟩ := exists_continuous_rectVec hh.1 hV
  have hall : ∀ᵐ ω ∂P, ∀ c : CoordJ, zbExt hh.1 V (comb ⊤ c) ω = gffOf Y hYc ω (comb ⊤ c) := by
    rw [ae_all_iff]
    intro c
    filter_upwards [zbExt_ae hh.1 V (comb ⊤ c),
      ae_integral_d12_mul_Y hh.1 hV hYc hYm hY (comb ⊤ c)] with ω h1 h2
    rw [h1, gffOf_apply, h2]
  filter_upwards [hall] with ω hω
  have : (fun c => zbExt hh.1 V (comb ⊤ c) ω) = pairJ ⊤ (gffOf Y hYc ω) := funext fun c => hω c
  rw [this]
  exact range_pairJ_subset ⊤ ⟨_, rfl⟩

/-- **Leaf (V)**: a measurable `𝒟'(ℂ)`-valued version of `φ ↦ ⟨h̊, 1_V φ⟩` vanishing off
`cl V` for every `ω`. -/
theorem exists_dist_version_zbExt (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) :
    ∃ hz : Ω → DistC, Measurable hz ∧ (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh.1 V φ) ∧
      ∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0 :=
  exists_dist_version_zbExt_of_adm hh hV (ae_zbExt_mem_rangeSet hh hV)

end MarkovVer2
end LQGMetric
