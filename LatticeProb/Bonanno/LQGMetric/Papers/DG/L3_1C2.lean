/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L3_1C2 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: the measurability arguments of tendstoInMeasure_of_tendsto_eLpNorm (dropped from its signature) removed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1C1
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont

/-!
# DG Lemma 3.1, the pair `(h, ĥ)`: circle averages of the white-noise GFF (task P2-DG105e, D109)

For a white noise `W` and a whole-plane GFF `h₀` with `h₀(φ) = W(kerFun φ)` a.s. (the
construction of `Field/ExistGFF`), and a circle `σ = circleUnif z r`, `r > 0`:

  `ae_circleAvg_eq_wn`: `h₀_r(z) = √π W(K̂_σ) + √π W(∫ largeKerL2 u σ(du))` a.s.,

`K̂_σ = hatMeasKerL2 σ` the kernel of `(ĥ, σ)` (DG (3.1)). Proof: the mollified circle averages
`h₀(σ * ψ_n) = W(kerFun (σ * ψ_n))` (`CircleAvg.mollAvg_eq`); the kernels `kerFun (σ * ψ_n)` are
Cauchy in `L²` (their increments have variance `logCov ≤ (4/r) 2^{-n}`,
`CircleAvg.logCov_circDiff_succ_le`), with pointwise limit
`√π 1_{t>0} (∫ p_{t/2}(u,y) σ(du) − 1_{t>1} p_{t/2}(0,y))` (`CircleAvg.tendsto_mollAvg_ofCont`),
which splits as `√π (hatMeasKer σ + ∫ largeKer u σ(du))`; the `L²(P)` limit of
`W(kerFun (σ * ψ_n))` agrees with the a.s. limit `h₀_r(z)` (`CircleAvg.ae_tendsto_mollAvg`).
Own elementary argument (DEVIATIONS, D109).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DG

open WhiteNoise GFFExist DZZ QuantumZipper SupTail CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the pointwise limit of `kerFun (σ_{z,r} * ψ_n)` -/
def circKerLim (z : ℂ) (r : ℝ) (q : ℝ × ℂ) : ℝ :=
  Real.sqrt Real.pi * (Ioi (0 : ℝ)).indicator (fun t => ∫ u, heatKernel (t / 2) u q.2 ∂circleUnif z r -
    (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (t / 2) 0 q.2) t) q.1

lemma continuous_heatKernel_left {s : ℝ} (y : ℂ) : Continuous fun u => heatKernel s u y := by
  unfold heatKernel; fun_prop

lemma tendsto_kerFun_circBump (z : ℂ) {r : ℝ} (hr : 0 < r) (q : ℝ × ℂ) :
    Tendsto (fun n => kerFun (circBump n z r) q) atTop (𝓝 (circKerLim z r q)) := by
  unfold kerFun circKerLim
  by_cases hq : q.1 ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hq]
    refine Tendsto.const_mul _ ?_
    set c := (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (q.1 / 2) 0 q.2) q.1
    set F : C(ℂ, ℝ) := ⟨fun u => heatKernel (q.1 / 2) u q.2 - c,
      (continuous_heatKernel_left q.2).sub continuous_const⟩
    have e : ∀ n, kerInner (circBump n z r) q.1 q.2 = mollAvg (ofCont F) n z r := fun n => by
      rw [mollAvg_eq, ofCont_apply_heat]; rfl
    simp_rw [e]
    have hl := tendsto_mollAvg_ofCont F r z
    rw [← QuantumZipper.CoordReg.integral_circleUnif_eq_circleAverage F.continuous.measurable] at hl
    convert hl using 2
    show _ = ∫ u, (heatKernel (q.1 / 2) u q.2 - c) ∂circleUnif z r
    rw [integral_sub (integrable_circleUnif_of_continuous (continuous_heatKernel_left q.2) hr)
      (integrable_const c), integral_const, probReal_univ, one_smul]
  · simp only [indicator_of_notMem hq]
    exact tendsto_const_nhds

/-- `E (W f − W g)² = ‖f − g‖²` -/
lemma integral_sq_wn_sub (hW : IsWhiteNoise P W) (f g : WNSpace) :
    ∫ ω, (W f ω - W g ω) ^ 2 ∂P = ‖f - g‖ ^ 2 := by
  have h := integral_sq_sqrtPi_sub hW f g
  have e : ∀ ω, (Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω) ^ 2 =
      Real.pi * (W f ω - W g ω) ^ 2 := fun ω => by
    rw [← mul_sub, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  simp_rw [e] at h
  rw [integral_const_mul] at h
  exact mul_left_cancel₀ Real.pi_pos.ne' h

lemma eLpNorm_wn_sub (hW : IsWhiteNoise P W) (f g : WNSpace) :
    eLpNorm (W f - W g) 2 P = ENNReal.ofReal ‖f - g‖ := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    ((wn_memLp hW f).sub (wn_memLp hW g))]
  congr 1
  have e : ∀ ω, ‖(W f - W g) ω‖ ^ (ENNReal.toReal 2) = (W f ω - W g ω) ^ 2 := fun ω => by
    rw [Pi.sub_apply, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  rw [integral_sq_wn_sub hW, ENNReal.toReal_ofNat]
  exact_mod_cast Real.pow_rpow_inv_natCast (norm_nonneg (f - g)) two_ne_zero

variable {h₀ : Ω → DistC}

section Circle

variable (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
  (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) (z : ℂ) {r : ℝ} (hr : 0 < r)

include hW hh hae hr in
lemma norm_testL2_circBump_succ_sub_le (n : ℕ) :
    ‖testL2 (circBump (n + 1) z r) - testL2 (circBump n z r)‖ ^ 2 ≤ 4 / r * (2 : ℝ)⁻¹ ^ n := by
  rw [← integral_sq_wn_sub hW]
  have e : (fun ω => (W (testL2 (circBump (n + 1) z r)) ω - W (testL2 (circBump n z r)) ω) ^ 2)
      =ᵐ[P] fun ω => (mollAvg (h₀ ω) (n + 1) z r - mollAvg (h₀ ω) n z r) ^ 2 := by
    filter_upwards [hae (circBump (n + 1) z r), hae (circBump n z r)] with ω h1 h2
    rw [mollAvg_eq, mollAvg_eq, ← h1, ← h2]
  rw [integral_congr_ae e, integral_sq_mollAvg_sub hh]
  exact logCov_circDiff_succ_le hr z n

include hW hh hae hr in
lemma cauchySeq_testL2_circBump : CauchySeq fun n => testL2 (circBump n z r) := by
  refine cauchySeq_of_le_geometric (Real.sqrt 2⁻¹) (Real.sqrt (4 / r)) ?_ fun n => ?_
  · rw [Real.sqrt_lt' one_pos]; norm_num
  · rw [dist_comm, dist_eq_norm]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine (norm_testL2_circBump_succ_sub_le hW hh hae z hr n).trans (le_of_eq ?_)
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]

include hr in
lemma ae_eq_circKerLim {K : WNSpace}
    (hK : Tendsto (fun n => testL2 (circBump n z r)) atTop (𝓝 K)) :
    (K : ℝ × ℂ → ℝ) =ᵐ[volume] circKerLim z r := by
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp hK).exists_seq_tendsto_ae
  have hc : ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), ∀ n,
      (testL2 (circBump n z r) : ℝ × ℂ → ℝ) q = kerFun (circBump n z r) q :=
    ae_all_iff.2 fun n => (memLp_kerFun_test _).coeFn_toLp
  filter_upwards [hae', hc] with q h1 h2
  simp_rw [h2] at h1
  exact tendsto_nhds_unique h1 ((tendsto_kerFun_circBump z hr q).comp hns.tendsto_atTop)

include hW hh hae hr in
lemma ae_circleAvg_eq_wn_lim {K : WNSpace}
    (hK : Tendsto (fun n => testL2 (circBump n z r)) atTop (𝓝 K)) :
    (fun ω => circleAvg (h₀ ω) r z) =ᵐ[P] W K := by
  have := hW.isProbabilityMeasure
  have hmo : ∀ n, W (testL2 (circBump n z r)) =ᵐ[P] fun ω => mollAvg (h₀ ω) n z r := fun n => by
    filter_upwards [hae (circBump n z r)] with ω hω
    rw [mollAvg_eq, hω]
  have h1 : TendstoInMeasure P (fun n ω => W (testL2 (circBump n z r)) ω) atTop (W K) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
      ?_
    have e : ∀ n, eLpNorm (W (testL2 (circBump n z r)) - W K) 2 P =
        ENNReal.ofReal ‖testL2 (circBump n z r) - K‖ := fun n => eLpNorm_wn_sub hW _ _
    simp_rw [e]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 hK)
  have h2 : TendstoInMeasure P (fun n ω => mollAvg (h₀ ω) n z r) atTop (W K) :=
    h1.congr' (Eventually.of_forall hmo) EventuallyEq.rfl
  have h3 : TendstoInMeasure P (fun n ω => mollAvg (h₀ ω) n z r) atTop
      (fun ω => circleAvg (h₀ ω) r z) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · exact (hW.measurable _).aestronglyMeasurable.congr (hmo n)
    · filter_upwards [ae_tendsto_mollAvg hh z hr] with ω ⟨a, ha⟩
      rwa [circleAvg_eq_of_tendsto ha]
  exact tendstoInMeasure_ae_unique h3 h2

end Circle

/-- the limit kernel splits into the kernel of `ĥ` and the large-time kernel -/
lemma circKerLim_eq (z : ℂ) {r : ℝ} (hr : 0 < r) (q : ℝ × ℂ) : circKerLim z r q =
    Real.sqrt Real.pi * hatMeasKer (circleUnif z r) q +
      Real.sqrt Real.pi * ∫ u, largeKer u q ∂circleUnif z r := by
  rcases q with ⟨t, y⟩
  simp only [circKerLim, hatMeasKer, hatKer, largeKer]
  rcases le_or_gt t 0 with ht | ht
  · have h0 : t ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi, not_lt]; exact ht
    have h01 : t ∉ Ioc (0 : ℝ) 1 := by simp only [mem_Ioc, not_and, not_le]; intro h; linarith
    have h1 : t ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi, not_lt]; linarith
    simp only [indicator_of_notMem h0, indicator_of_notMem h01, indicator_of_notMem h1,
      integral_zero, mul_zero, add_zero]
  rcases le_or_gt t 1 with ht1 | ht1
  · have h0 : t ∈ Ioi (0 : ℝ) := ht
    have h01 : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
    have h1 : t ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi, not_lt]; exact ht1
    simp only [indicator_of_mem h0, indicator_of_mem h01, indicator_of_notMem h1,
      integral_zero, mul_zero, add_zero, sub_zero]
  · have h0 : t ∈ Ioi (0 : ℝ) := ht
    have h01 : t ∉ Ioc (0 : ℝ) 1 := by simp only [mem_Ioc, not_and, not_le]; intro _; exact ht1
    have h1 : t ∈ Ioi (1 : ℝ) := ht1
    simp only [indicator_of_mem h0, indicator_of_notMem h01, indicator_of_mem h1,
      integral_zero, mul_zero, zero_add]
    rw [integral_sub (integrable_circleUnif_of_continuous (continuous_heatKernel_left y) hr)
      (integrable_const _), integral_const, probReal_univ, one_smul]

/-- **Circle averages of the white-noise GFF.** `h₀_r(z) = √π W(K̂_σ) + √π W(∫ largeKerL2 dσ)`
almost surely (`σ = circleUnif z r`, `r > 0`). -/
theorem ae_circleAvg_eq_wn (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun ω => circleAvg (h₀ ω) r z) =ᵐ[P] fun ω =>
      Real.sqrt Real.pi * W (hatMeasKerL2 (circleUnif z r)) ω +
        Real.sqrt Real.pi * W (∫ u, largeKerL2 u ∂circleUnif z r) ω := by
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete (cauchySeq_testL2_circBump hW hh hae z hr)
  set σ := circleUnif z r with hσ
  have hKG := ae_eq_circKerLim z hr hK
  have hFi : Integrable largeKerL2 σ := integrable_circleUnif_of_continuous' continuous_largeKerL2 hr
  have hL := integral_largeKerL2_ae_eq σ hFi
  have hGm : MemLp (circKerLim z r) 2 volume := (Lp.memLp K).ae_eq hKG
  have hLm : MemLp (fun q => ∫ u, largeKer u q ∂σ) 2 volume := (Lp.memLp _).ae_eq hL
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hHm : MemLp (hatMeasKer σ) 2 volume := by
    have := (hGm.sub (hLm.const_mul (Real.sqrt Real.pi))).const_mul (Real.sqrt Real.pi)⁻¹
    refine this.ae_eq (Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply, circKerLim_eq z hr q]
    field_simp
    ring
  have e2 : (hatMeasKerL2 σ : ℝ × ℂ → ℝ) =ᵐ[volume] hatMeasKer σ := by
    rw [hatMeasKerL2, dite_eq_left_of_eq_true (eq_true hHm)]; exact hHm.coeFn_toLp
  have hKeq : K = Real.sqrt Real.pi • hatMeasKerL2 σ +
      Real.sqrt Real.pi • ∫ u, largeKerL2 u ∂σ := by
    refine Lp.ext ?_
    filter_upwards [hKG, e2, hL, Lp.coeFn_add (Real.sqrt Real.pi • hatMeasKerL2 σ)
      (Real.sqrt Real.pi • ∫ u, largeKerL2 u ∂σ), Lp.coeFn_smul (Real.sqrt Real.pi) (hatMeasKerL2 σ),
      Lp.coeFn_smul (Real.sqrt Real.pi) (∫ u, largeKerL2 u ∂σ)] with q h1 h2 h3 h4 h5 h6
    rw [h4, Pi.add_apply, h5, h6, Pi.smul_apply, Pi.smul_apply, h2, h3, h1, circKerLim_eq z hr q,
      smul_eq_mul, smul_eq_mul]
  filter_upwards [ae_circleAvg_eq_wn_lim hW hh hae z hr hK,
    hW.add_ae (Real.sqrt Real.pi • hatMeasKerL2 σ) (Real.sqrt Real.pi • ∫ u, largeKerL2 u ∂σ),
    hW.smul_ae (Real.sqrt Real.pi) (hatMeasKerL2 σ),
    hW.smul_ae (Real.sqrt Real.pi) (∫ u, largeKerL2 u ∂σ)] with ω h1 h2 h3 h4
  rw [h1, hKeq, h2, h3, h4]

end DG
end LQGMetric
