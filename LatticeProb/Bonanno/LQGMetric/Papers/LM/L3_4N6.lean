/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4N6 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N5

/-!
# `𝔥^r(0) = h_r(0)` (`LMHarmCenterLeaf`), proved

For the Markov decomposition `lmScaled h r = 𝔥 + h̊` on `B_1(0)` (`IsLMRep`), with `Y = lmScaled h r`
a whole-plane GFF normalized by `Y_1(0) = 0`, and `g` the harmonic representative of `𝔥`:

* for `ρ < 1`, `Y_ρ(0) = g(0) + Δ_ρ` a.s., where `Δ_ρ = lim_n ⟨h̊, circBump n 0 ρ⟩` (the mollified
  circle averages of `𝔥` converge to `g(0)`, `tendsto_mollAvg_of_harmonic`); `Δ_ρ` is an a.s.
  limit of functions of `h̊`, hence independent of `σ(Y|_{ℂ∖B_1})` (`MarkovIndep`), while
  `g(0) = ⟨𝔥, ψ_0⟩/∫ψ_0` is measurable for it;
* hence `Var g(0) ≤ Var Y_ρ(0) = log(1/ρ)` (the circle average process is a Brownian motion in
  `log(1/ρ)`, `CircleAvg.isPreBrownianReal_circleAvg`); letting `ρ → 1`, `Var g(0) = 0`, and
  `E g(0) = 0`, so `g(0) = 0 = Y_1(0)` a.s.

This is the statement that the harmonic extension of the boundary values takes at the centre the
boundary circle average (LM arXiv:1905.00379 l. 586–590 use `𝔥^r` centred at `h_r(0)`); the
variance argument is our own.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace Topology
open scoped ENNReal NNReal

namespace LQGMetric.LM

open Blueprint GM CircleAvg MarkovGauss MarkovZB MarkovNorm

lemma tsupport_radBump_subset {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    tsupport (radBump δ hδ.le x : ℂ → ℝ) ⊆ closedBall x δ := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra hy'
  rw [mem_closedBall, dist_eq_norm, not_le] at hy'
  exact hy (radProf_eq_zero hδ.le hy'.le)

/-- **`𝔥^r(0) = h_r(0)`** (`LMHarmCenterLeaf`). -/
theorem lmHarmCenterLeaf : LMHarmCenterLeaf := by
  intro Ω mΩ P _ h hh r hr hh0 hz G H
  set Y := lmScaled h r with hYdef
  have hY : IsWholePlaneGFF Y P := isWholePlaneGFF_lmScaled hh.1 hr
  have hY1 : ∀ᵐ ω ∂P, circleAvg (Y ω) 1 0 = 0 := ae_circleAvg_lmScaled hh.1 hr
  have hYn : IsNormalizedWPGFF Y P := ⟨hY, hY1⟩
  obtain ⟨hdec, hhG, hGm, hharm, hzb, hind⟩ := H
  have hm : lmOut h r ≤ mΩ := MarkovZBIndep.fieldSigmaClosed_le hY _
  have hcomap : ∀ φ : TestOn (ballO 0 1),
      MeasurableSpace.comap (fun ω => restrictTo (ballO 0 1) (hz ω) φ) inferInstance ≤
        MeasurableSpace.comap hz inferInstance := fun φ =>
    (MeasurableSpace.comap_comp (f := fun T : DistC => restrictTo (ballO 0 1) T φ)
      (g := hz)).symm.le.trans (MeasurableSpace.comap_mono
        ((measurable_distOn_apply φ).comp (measurable_restrictTo _)).comap_le)
  -- the value at the centre, `g0 = ⟨G, ψ_0⟩ / ∫ ψ_0`
  set δ : ℝ := 1 / 4 with hδdef
  have hδ : 0 < δ := by norm_num
  have hBδ : closedBall (0 : ℂ) δ ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball (by norm_num)
  set ψ0 : TestC := radBump δ hδ.le 0
  have hts0 : tsupport (ψ0 : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 := (tsupport_radBump_subset hδ 0).trans hBδ
  set I := ∫ y, radProf δ y
  have hI : 0 < I := integral_radProf_pos hδ
  set g0 : Ω → ℝ := fun ω => G ω ψ0 / I with hg0def
  have hg0m' : Measurable[lmOut h r] g0 :=
    ((measurable_distOn_apply ψ0).comp hGm).div_const I
  have hg0m : Measurable g0 := hg0m'.mono hm le_rfl
  -- `g0 = (⟨Y, ψ_0⟩ − ⟨h̊, ψ_0⟩)/I`: square integrable and centred
  set Z0 : Ω → ℝ := fun ω => restrictTo (ballO 0 1) (hz ω) (testOn1 ψ0 hts0)
  have hZ0L : MemLp Z0 2 P :=
    (hzb.process.gaussian.hasGaussianLaw_eval (testOn1 ψ0 hts0)).memLp_two
  have hZ00 : ∫ ω, Z0 ω ∂P = 0 := hzb.process.centered _
  have hYψL : MemLp (fun ω => Y ω ψ0) 2 P := (Lp.memLp _).ae_eq (pairVec_ae hYn ψ0)
  have hYψ0 : ∫ ω, Y ω ψ0 ∂P = 0 := by
    rw [← integral_congr_ae (pairVec_ae hYn ψ0)]
    exact (isCGauss_of_mem_gaussSpace (gaussian_pairProc hY) (centered_pairProc hY)
      (memLp_pair hY) (pairVec_mem_gaussSpace hYn ψ0)).2
  have hg0ae : g0 =ᵐ[P] fun ω => I⁻¹ * (Y ω ψ0 - Z0 ω) := by
    filter_upwards [hhG] with ω h1
    have k := congrArg (fun T : DistC => T ψ0) (hdec ω)
    simp only [ContinuousLinearMap.add_apply] at k
    simp only [hg0def, Z0, restrictTo_testOn1, ← h1]
    rw [k, div_eq_inv_mul]; ring
  have hg0L : MemLp g0 2 P := ((hYψL.sub hZ0L).const_mul I⁻¹).ae_eq hg0ae.symm
  have hg00 : ∫ ω, g0 ω ∂P = 0 := by
    rw [integral_congr_ae hg0ae, integral_const_mul, integral_sub (hYψL.integrable one_le_two)
      (hZ0L.integrable one_le_two), hYψ0, hZ00, sub_zero, mul_zero]
  -- `Var g0 ≤ log(1/ρ)` for every `ρ = e^{-t} < 1`
  obtain ⟨B, hB, -, hBae⟩ := isPreBrownianReal_circleAvg hY 0
  have hvar : ∀ t : ℝ≥0, 0 < t → Var[g0; P] ≤ t := by
    intro t ht
    set ρ := Real.exp (-(t : ℝ)) with hρdef
    have hρ0 : 0 < ρ := Real.exp_pos _
    have hρ1 : ρ < 1 := by
      rw [hρdef, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (by exact_mod_cast ht))
    set Yρ : Ω → ℝ := fun ω => circleAvg (Y ω) ρ 0
    have hYρB : Yρ =ᵐ[P] B t := by
      filter_upwards [hBae t, hY1] with ω h1 h2
      rw [h1, h2, sub_zero]
    have hYρL : MemLp Yρ 2 P :=
      ((hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two).ae_eq hYρB.symm
    have hVρ : Var[Yρ; P] = t := by
      rw [variance_congr hYρB, ← covariance_self (hB.aemeasurable t), hB.covariance_eval t t,
        min_self]
    set Δ : Ω → ℝ := fun ω => Yρ ω - g0 ω
    have hΔm : Measurable Δ := ((measurable_circleAvg_left ρ 0).comp hY.measurable).sub hg0m
    have hΔL : MemLp Δ 2 P := hYρL.sub hg0L
    -- `Δ` is the limit of `⟨h̊, circBump n 0 ρ⟩`
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hρ1) (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hts : ∀ n, tsupport (circBump (n + N) 0 ρ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 := fun n =>
      tsupport_circBump_subset_ball hρ0.le (by
        have : (2 : ℝ)⁻¹ ^ (n + N) ≤ (2 : ℝ)⁻¹ ^ N :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith)
    set Zn : ℕ → Ω → ℝ := fun n ω =>
      restrictTo (ballO 0 1) (hz ω) (testOn1 (circBump (n + N) 0 ρ) (hts n))
    have hZnm : ∀ n, Measurable (Zn n) := fun n => hzb.process.measurable _
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Δ ω)) := by
      filter_upwards [ae_tendsto_mollAvg hY 0 hρ0, hhG, hharm] with ω ⟨a, ha⟩ hGω ⟨g, hg, hgrep⟩
      have hG1 := tendsto_mollAvg_of_harmonic hg hgrep hρ0.le hρ1
      have hg0 : g0 ω = g 0 := by
        have e := pair_radBump_of_harmonic (V := ballO 0 1) hg hgrep hδ hBδ
        simp only [hg0def, ← hGω]
        rw [e, mul_div_cancel_right₀ _ hI.ne']
      have hYρa : Yρ ω = a := circleAvg_eq_of_tendsto ha
      have key : ∀ n, Zn n ω = mollAvg (Y ω) (n + N) 0 ρ - mollAvg (hh0 ω) (n + N) 0 ρ := by
        intro n
        simp only [Zn, restrictTo_testOn1]
        rw [mollAvg_eq, mollAvg_eq, show Y ω = hh0 ω + hz ω from hdec ω,
          ContinuousLinearMap.add_apply]
        ring
      have hT := (ha.comp (tendsto_add_atTop_nat N)).sub (hG1.comp (tendsto_add_atTop_nat N))
      have he : a - g 0 = Δ ω := by simp only [Δ, hYρa, hg0]
      rw [he] at hT
      refine hT.congr fun n => ?_
      rw [key n]; rfl
    have hΔind : Indep (MeasurableSpace.comap Δ inferInstance) (lmOut h r) P :=
      MarkovIndep.indep_comap_of_tendsto_ae hΔm hZnm hm hlim fun n =>
        indep_of_indep_of_le_left hind (hcomap _)
    have hIF : IndepFun g0 Δ P :=
      (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_left hΔind.symm hg0m'.comap_le)
    have hsum : Yρ = g0 + Δ := by funext ω; simp only [Pi.add_apply, Δ]; ring
    have hadd := hIF.variance_add hg0L hΔL
    rw [← hsum, hVρ] at hadd
    have := variance_nonneg Δ P
    linarith
  have hv0 : Var[g0; P] = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (variance_nonneg _ _)
    refine (hvar ⟨ε, hε.le⟩ hε).trans ?_
    show ε ≤ 0 + ε
    linarith
  have hsq : ∫ ω, (g0 ^ 2) ω ∂P = 0 := by
    have := variance_eq_sub hg0L
    rw [hv0, hg00] at this
    simpa using this.symm
  have hsq' : (fun ω => g0 ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hg0L.integrable_sq).1 hsq
  filter_upwards [hsq', hY1] with ω h0 h1 g hg hgrep
  have e := pair_radBump_of_harmonic (V := ballO 0 1) hg hgrep hδ hBδ
  have hz0 : g0 ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  have e' : G ω ψ0 = g 0 * I := e
  have h2 : g 0 * I / I = 0 := by rw [← e']; exact hz0
  rw [mul_div_cancel_right₀ _ hI.ne'] at h2
  rw [h2]
  exact h1.symm

/-- **LM Lemma 3.1 (1)** (`N = 0`) from the canonical nesting alone. -/
theorem lmLem3_1a_of_canon' (hC : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestCanonLeaf s₁) :
    LMLem3_1a :=
  lmLem3_1a_of_canon hC lmHarmCenterLeaf

end LQGMetric.LM
