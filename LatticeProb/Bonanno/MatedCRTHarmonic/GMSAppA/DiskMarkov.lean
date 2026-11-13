/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.DiskMarkov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA4
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N6
import LatticeProb.Bonanno.LQGMetric.Field.MarkovIndep
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIndep

/-!
# The Markov decomposition of a whole-plane GFF on `𝔻` and the value of its harmonic part at `0`

[18] (GMS, arXiv 1807.07511v3) Lemma 2.2 : for a whole-plane GFF normalized
on a circle disjoint from `U = 𝔻`, `h|_𝔻 = 𝔥 + h̊` with `𝔥` harmonic on `𝔻` and determined by `h|_{ℂ∖𝔻}`, and `h̊` a
zero-boundary GFF on `𝔻` independent of `h|_{ℂ∖𝔻}`. This is LQGMetric's `DFGPS.markov_normAt` (with
`MarkovFinal.lmLem2_1`); `DiskMarkov` packages its output, with the harmonic part replaced by its
`σ(h|_{ℂ∖𝔻})`-measurable version.

The proof of [18] Lemma A.5 uses "`𝔥(0) = h_1(0)`" (the harmonic extension takes at the centre the
boundary circle average). We prove it (`DiskMarkov.center`) by the variance argument of LQGMetric's
`LM.lmHarmCenterLeaf`: for `ρ < 1`, `h_ρ(0) − h_1(0) = (𝔥(0) − h_1(0)) + Δ_ρ` with `Δ_ρ = lim ⟨h̊, circBump⟩`
independent of the first summand, so `E(𝔥(0) − h_1(0))² ≤ Var(h_ρ(0) − h_1(0)) = |log ρ| → 0`.

* `GMSAppA.DiskMarkov` — the decomposition.
* `GMSAppA.exists_diskMarkov` — existence for every normalization circle disjoint from `𝔻`.
* `GMSAppA.DiskMarkov.center` — `𝔥(0) = h_1(0)` a.s.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM LQGMetric.Blueprint LQGMetric.CircleAvg
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSAppA

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The exterior σ-algebra `σ(h|_{ℂ∖𝔻})`. -/
abbrev extSigma (h : Ω → DistC) : MeasurableSpace Ω := fieldSigmaClosed h (ball (0 : ℂ) 1)ᶜ

/-- **The Markov decomposition of `h` on `𝔻`** ([18] Lemma 2.2 with `U = 𝔻`): `h = G + h̊` a.s., `G` measurable
w.r.t. `σ(h|_{ℂ∖𝔻})` and a.s. harmonic on `𝔻`, `h̊|_𝔻` a zero-boundary GFF on `𝔻` independent of `σ(h|_{ℂ∖𝔻})`. -/
structure DiskMarkov (P : Measure Ω) (h : Ω → DistC) where
  /-- the (exterior-measurable version of the) harmonic part -/
  G : Ω → DistC
  /-- the zero-boundary part -/
  hz : Ω → DistC
  G_meas : Measurable[extSigma h] G
  dec : ∀ᵐ ω ∂P, h ω = G ω + hz ω
  harm : ∀ᵐ ω ∂P, ∃ g, HarmRep (G ω) g
  zb : IsZeroBoundaryGFF (ballO 0 1) (fun ω => restrictTo (ballO 0 1) (hz ω)) P
  indep : Indep (MeasurableSpace.comap hz inferInstance) (extSigma h) P

/-- **Existence** of the Markov decomposition on `𝔻` for a whole-plane GFF normalized on a circle `∂B_r(w)` disjoint
from `𝔻` (LQGMetric `DFGPS.markov_normAt`). -/
theorem exists_diskMarkov [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {r : ℝ} {w : ℂ} (hr : 0 < r) (hn : ∀ᵐ ω ∂P, circleAvg (h ω) r w = 0)
    (hV : Disjoint (ball (0 : ℂ) 1) (sphere w r)) : Nonempty (DiskMarkov P h) := by
  obtain ⟨hh', hz, hsum, hharm, ⟨G', hG'm, hG'⟩, -, hzb, -, hindep⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P h hh hr w hn (ballO 0 1) hV
  refine ⟨⟨G', hz, hG'm, ?_, ?_, hzb, hindep⟩⟩
  · filter_upwards [hG'] with ω hω
    rw [hsum ω, hω]
  · filter_upwards [hharm, hG'] with ω ⟨g, hg, hgrep⟩ hω
    exact ⟨g, hg, by rw [← hω]; exact hgrep⟩

lemma extSigma_le {h : Ω → DistC} (hh : Measurable h) : extSigma h ≤ ‹MeasurableSpace Ω› :=
  GM.Bilip.fieldSigmaClosed_le hh _

namespace DiskMarkov

variable {h : Ω → DistC}
lemma measurable_G (M : DiskMarkov P h) (hh : Measurable h) : Measurable M.G :=
  M.G_meas.mono (extSigma_le hh) le_rfl

/-- the circle average `h_1(0)` is `σ(h|_{ℂ∖𝔻})`-measurable -/
lemma measurable_circleAvg_one (h : Ω → DistC) :
    Measurable[extSigma h] fun ω => circleAvg (h ω) 1 0 := by
  refine measurable_circleAvg_fieldSigmaClosed h 1 0 fun x hx => ?_
  rw [abs_one] at hx
  simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
  rw [mem_sphere_iff_norm, sub_zero] at hx
  rw [hx]

/-- **`𝔥(0) = h_1(0)`**: almost surely every harmonic representative `g` of the harmonic part on `𝔻` satisfies
`g(0) = h_1(0)`. -/
theorem center [IsProbabilityMeasure P] (M : DiskMarkov P h) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ g, HarmRep (M.G ω) g → g 0 = circleAvg (h ω) 1 0 := by
  have hm : extSigma h ≤ ‹MeasurableSpace Ω› := extSigma_le hh.measurable
  have hcomap : ∀ φ : TestOn (ballO 0 1),
      MeasurableSpace.comap (fun ω => restrictTo (ballO 0 1) (M.hz ω) φ) inferInstance ≤
        MeasurableSpace.comap M.hz inferInstance := fun φ =>
    (MeasurableSpace.comap_comp (f := fun T : DistC => restrictTo (ballO 0 1) T φ)
      (g := M.hz)).symm.le.trans (MeasurableSpace.comap_mono
        ((measurable_distOn_apply φ).comp (measurable_restrictTo _)).comap_le)
  -- the value at the centre, `g0 = ⟨G, ψ_0⟩ / ∫ ψ_0`, minus `h_1(0)`
  set δ : ℝ := 1 / 4 with hδdef
  have hδ : 0 < δ := by norm_num
  have hBδ : closedBall (0 : ℂ) δ ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball (by norm_num)
  set ψ0 : TestC := radBump δ hδ.le 0
  have hts0 : tsupport (ψ0 : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 :=
    (LM.tsupport_radBump_subset hδ 0).trans hBδ
  set I := ∫ y, radProf δ y
  have hI : 0 < I := integral_radProf_pos hδ
  set C1 : Ω → ℝ := fun ω => circleAvg (h ω) 1 0
  have hC1m' : Measurable[extSigma h] C1 := measurable_circleAvg_one h
  set U : Ω → ℝ := fun ω => M.G ω ψ0 / I - C1 ω with hUdef
  have hUm' : Measurable[extSigma h] U :=
    (((measurable_distOn_apply ψ0).comp M.G_meas).div_const I).sub hC1m'
  have hUm : Measurable U := hUm'.mono hm le_rfl
  -- for every `ρ = e^{-t} < 1`: `U ∈ L²` and `E U² ≤ t`
  have hvar : ∀ t : ℝ≥0, 0 < t → MemLp U 2 P ∧ ∫ ω, U ω ^ 2 ∂P ≤ t := by
    intro t ht
    set ρ := Real.exp (-(t : ℝ)) with hρdef
    have hρ0 : 0 < ρ := Real.exp_pos _
    have hρ1 : ρ < 1 := by
      rw [hρdef, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (by exact_mod_cast ht))
    set W : Ω → ℝ := cInc h ρ 0 1 0
    have hWlaw := map_cInc hh hρ0 one_pos (0 : ℂ) (0 : ℂ)
    have hWm : Measurable W := measurable_cInc hh ρ 0 1 0
    have hWG : HasGaussianLaw W P := ⟨hWm.aemeasurable, by rw [hWlaw.1]; infer_instance⟩
    have hWL : MemLp W 2 P := hWG.memLp_two
    have hW0 : ∫ ω, W ω ∂P = 0 := by
      have := integral_map (μ := P) (f := fun x : ℝ => x) hWm.aemeasurable aestronglyMeasurable_id
      rw [hWlaw.1, integral_id_gaussianReal] at this
      exact this.symm
    have hVW : Var[W; P] = |Real.log ρ| := variance_cInc_one hh hρ0 0
    set Δ : Ω → ℝ := fun ω => W ω - U ω
    have hΔm : Measurable Δ := hWm.sub hUm
    -- `Δ` is the a.s. limit of `⟨h̊, circBump n 0 ρ⟩`
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hρ1) (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hts : ∀ n, tsupport (circBump (n + N) 0 ρ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 := fun n =>
      LM.tsupport_circBump_subset_ball hρ0.le (by
        have : (2 : ℝ)⁻¹ ^ (n + N) ≤ (2 : ℝ)⁻¹ ^ N :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith)
    set Zn : ℕ → Ω → ℝ := fun n ω =>
      restrictTo (ballO 0 1) (M.hz ω) (LM.testOn1 (circBump (n + N) 0 ρ) (hts n))
    have hZnm : ∀ n, Measurable (Zn n) := fun n => M.zb.process.measurable _
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Δ ω)) := by
      filter_upwards [ae_tendsto_mollAvg hh 0 hρ0, ae_tendsto_mollAvg hh 0 one_pos, M.dec,
        M.harm] with ω ⟨a, ha⟩ ⟨b, hb⟩ hdec ⟨g, hg, hgrep⟩
      have hG1 := LM.tendsto_mollAvg_of_harmonic hg hgrep hρ0.le hρ1
      have hg0 : M.G ω ψ0 / I = g 0 := by
        have e := pair_radBump_of_harmonic (V := ballO 0 1) hg hgrep hδ hBδ
        rw [e, mul_div_cancel_right₀ _ hI.ne']
      have hWω : W ω = a - b := by
        simp only [W, cInc, circleAvg_eq_of_tendsto ha, circleAvg_eq_of_tendsto hb]
      have key : ∀ n, Zn n ω = mollAvg (h ω) (n + N) 0 ρ - mollAvg (M.G ω) (n + N) 0 ρ := by
        intro n
        simp only [Zn, LM.restrictTo_testOn1]
        rw [mollAvg_eq, mollAvg_eq, hdec, ContinuousLinearMap.add_apply]
        ring
      have hT := (ha.comp (tendsto_add_atTop_nat N)).sub (hG1.comp (tendsto_add_atTop_nat N))
      have he : a - g 0 = Δ ω := by
        simp only [Δ, hWω, hUdef, hg0, C1, circleAvg_eq_of_tendsto hb]
        ring
      rw [he] at hT
      refine hT.congr fun n => ?_
      rw [key n]; rfl
    have hΔind : Indep (MeasurableSpace.comap Δ inferInstance) (extSigma h) P :=
      MarkovIndep.indep_comap_of_tendsto_ae hΔm hZnm hm hlim fun n =>
        indep_of_indep_of_le_left M.indep (hcomap _)
    have hIF : IndepFun U Δ P :=
      (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_left hΔind.symm hUm'.comap_le)
    -- `Δ` is a centred Gaussian (a.s. limit of centred Gaussians)
    have hZnG : ∀ n, HasGaussianLaw (Zn n) P := fun n =>
      M.zb.process.gaussian.hasGaussianLaw_eval _
    have hZn0 : ∀ n, P[Zn n] = 0 := fun n => M.zb.process.centered _
    obtain ⟨hΔG, hΔ0, -⟩ := CircleAvgIndep.gaussian_of_ae_tendsto hZnG hZn0 hΔm.aemeasurable hlim
    have hΔL : MemLp Δ 2 P := hΔG.memLp_two
    have hUL : MemLp U 2 P := by
      have : U = fun ω => W ω - Δ ω := by funext ω; simp only [Δ]; ring
      rw [this]; exact hWL.sub hΔL
    have hU0 : ∫ ω, U ω ∂P = 0 := by
      have : U = fun ω => W ω - Δ ω := by funext ω; simp only [Δ]; ring
      rw [this, integral_sub (hWL.integrable one_le_two) (hΔL.integrable one_le_two), hW0, hΔ0,
        sub_zero]
    have hsum : W = U + Δ := by funext ω; simp only [Pi.add_apply, Δ]; ring
    have hadd := hIF.variance_add hUL hΔL
    rw [← hsum, hVW] at hadd
    have hΔv := variance_nonneg Δ P
    have hUv : Var[U; P] = ∫ ω, U ω ^ 2 ∂P := by
      rw [variance_eq_sub hUL, hU0]; simp
    have hlog : |Real.log ρ| = t := by
      rw [hρdef, Real.log_exp, abs_neg, abs_of_nonneg (NNReal.coe_nonneg t)]
    refine ⟨hUL, ?_⟩
    rw [← hUv]
    linarith
  have hU2 : ∫ ω, U ω ^ 2 ∂P = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
      (integral_nonneg fun ω => sq_nonneg _)
    refine (hvar ⟨ε, hε.le⟩ hε).2.trans ?_
    show ε ≤ 0 + ε
    linarith
  have hUi : Integrable (fun ω => U ω ^ 2) P := (hvar 1 one_pos).1.integrable_sq
  have hU0ae : (fun ω => U ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hUi).1 hU2
  filter_upwards [hU0ae] with ω hω g hg
  have e := pair_radBump_of_harmonic (V := ballO 0 1) hg.1 hg.2 hδ hBδ
  have hz : U ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hω
  have e' : M.G ω ψ0 / I = g 0 := by rw [e, mul_div_cancel_right₀ _ hI.ne']
  simp only [hUdef, e'] at hz
  linarith

end DiskMarkov

end MatedCRTHarmonic.GMSAppA
