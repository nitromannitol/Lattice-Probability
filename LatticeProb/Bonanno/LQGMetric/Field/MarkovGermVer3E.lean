/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer3E at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer3D

/-!
# Germ step for unbounded `V`: the uniform truncation bound (task P2-MKD3)

* `sq_dev_le_schur`: Poincaré inequality from the Schur bound: for a bump `ζ` (values in
  `[0,1]`, vanishing off `B̄(0,2)`) and the `ζ²`-weighted mean `c` of `g ∈ C_c^∞`,
  `∫ (ζ (g − c))² ≤ L ‖(h, g)_∇‖²` (the covariance-Poincaré step of `exists_zsSub_approx`, with
  `w = 0`: `X = ∫ ζ²(g−c)² = ⟪(h,g)_∇, ⟨h, ζ²(g−c)⟩⟫ ≤ ‖(h,g)_∇‖ √(L X)`).
* `trunc_energy_le`: the uniform bound
  `gradEnergy (logInf r r² · (g − c)) ≤ M gradEnergy g` for `r ≥ 4`, from
  `|∇(λu)|² ≤ 2|∇u|² + 2u²|∇λ|²`, `|∇λ| ≤ C/(log(r/2)|x|)` on `2r < |x| < r²`, the Hardy
  inequality `hardy_far` and `sq_dev_le_schur`.
Own elementary proofs (standard 2D log-cutoff/Hardy argument, cf. Berestycki–Powell
arXiv:2404.16642 §1.8).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the Schur constant on `B̄(0,2)` -/
def schurL2 : ℝ := 2 * (2 * 2 * (Real.pi * (2 * 2) ^ 2) + logBallConst)

lemma schurL2_nonneg : 0 ≤ schurL2 := by
  have := logBallConst_nonneg; unfold schurL2; positivity

/-- the `ζ²`-weighted mean -/
def zmean (ζ g : ℂ → ℝ) : ℝ := (∫ y, ζ y * ζ y * g y) / ∫ y, ζ y * ζ y

lemma hasCompactSupport_of_ball2 {ζ : ℂ → ℝ} (hζR : ∀ x, 2 < ‖x‖ → ζ x = 0) :
    HasCompactSupport ζ :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun x hx => by
    simp only [mem_closedBall, dist_zero_right, not_le] at hx
    exact hζR x hx

set_option maxHeartbeats 1000000 in
/-- **Poincaré inequality from the Schur bound** -/
theorem sq_dev_le_schur (hh : IsWholePlaneGFF h P) {ζ : ℂ → ℝ}
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, 2 < ‖x‖ → ζ x = 0) (g : zsSub ((⊤ : Opens ℂ) : Set ℂ)) :
    ∫ x, (ζ x * (g.1 x - zmean ζ g.1)) ^ 2 ≤ schurL2 * ‖cmLin hh ⊤ g‖ ^ 2 := by
  have hζc := hasCompactSupport_of_ball2 hζR
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.1 := g.2.1
  set e := ‖cmLin hh ⊤ g‖
  have hζ2i : Integrable fun x => ζ x * ζ x :=
    integrable_of_cs (hζs.continuous.mul hζs.continuous) hζc.mul_right
  have hζfi : Integrable fun x => ζ x * ζ x * g.1 x :=
    integrable_of_cs ((hζs.continuous.mul hζs.continuous).mul hfs.continuous)
      hζc.mul_right.mul_right
  set A := ∫ x, ζ x * ζ x
  set B := ∫ x, ζ x * ζ x * g.1 x
  set c := zmean ζ g.1
  have hcBA : c = B / A := rfl
  have hBA : B - c * A = 0 := by
    by_cases hA : A = 0
    · have hz := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (ζ x)) hζ2i).1 hA
      have hB : B = 0 := integral_eq_zero_of_ae (by
        filter_upwards [hz] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx, zero_mul])
      rw [hB, hA]; ring
    · rw [hcBA]; field_simp; ring
  set F : ℂ → ℝ := fun x => g.1 x - c with hF
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hfs.sub contDiff_const
  set pf : ℂ → ℝ := fun x => ζ x * (ζ x * F x) with hpf
  have hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pf := hζs.mul (hζs.mul hFs)
  have hpc : HasCompactSupport pf := hζc.mul_right
  have hpi : Integrable pf := integrable_of_cs hps.continuous hpc
  have hp0 : ∫ x, pf x = 0 := by
    have e1 : pf = fun x => ζ x * ζ x * g.1 x - c * (ζ x * ζ x) := funext fun x => by
      simp only [pf, F]; ring
    rw [e1, integral_sub hζfi (hζ2i.const_mul c), integral_const_mul]
    linarith [hBA]
  set p : TestC0 := ⟨tC hps hpc, hp0⟩
  have hpfun : (p.1 : ℂ → ℝ) = pf := rfl
  set X := ∫ x, (ζ x * F x) ^ 2
  have hXi : Integrable fun x => (ζ x * F x) ^ 2 :=
    integrable_of_cs ((hζs.continuous.mul hFs.continuous).pow 2)
      (hcs_of_vanish hζc fun x hx => by simp [hx])
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have hXp : ⟪cmLin hh ⊤ g, (memLp_pair hh p).toLp (pairProc h p)⟫ = X := by
    rw [inner_cmLin_pair, hpfun]
    have e1 : (fun x => pf x * g.1 x) = fun x => (ζ x * F x) ^ 2 + c * pf x := funext fun x => by
      simp only [pf, F]; ring
    rw [e1, integral_add hXi (hpi.const_mul c), integral_const_mul, hp0, mul_zero, add_zero]
  have hMp : ‖(memLp_pair hh p).toLp (pairProc h p)‖ ^ 2 ≤ schurL2 * X := by
    rw [norm_pair_sq hh, hpfun]
    have hL := logCov_self_le_schur (R := 2) (by norm_num) hps.continuous
      fun x hx => by simp [pf, hζR x hx]
    refine hL.trans (mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
      (ae_of_all _ fun x => sq_nonneg _) hXi (ae_of_all _ fun x => ?_)) schurL2_nonneg)
    have h1 := hζ01 x
    change (ζ x * (ζ x * F x)) ^ 2 ≤ (ζ x * F x) ^ 2
    rw [mul_pow]
    nlinarith [sq_nonneg (ζ x * F x), (pow_le_one₀ h1.1 h1.2 : ζ x ^ 2 ≤ 1)]
  have he0 : 0 ≤ e := norm_nonneg _
  set M := ‖(memLp_pair hh p).toLp (pairProc h p)‖
  have h1 : X ≤ e * M := hXp ▸ real_inner_le_norm _ _
  have hM0 : 0 ≤ M := norm_nonneg _
  have h2 : X * X ≤ X * (schurL2 * e ^ 2) := by
    have h3 : X * X ≤ (e * M) ^ 2 := by nlinarith
    have h4 : (e * M) ^ 2 ≤ e ^ 2 * (schurL2 * X) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hMp (sq_nonneg e)
    nlinarith
  change X ≤ schurL2 * e ^ 2
  rcases hX0.lt_or_eq with hpos | h0
  · exact le_of_mul_le_mul_left h2 hpos
  · rw [← h0]; have := schurL2_nonneg; positivity

lemma norm_fderiv_lam_mul_sq_le {lam u : ℂ → ℝ} {z : ℂ} (hl : DifferentiableAt ℝ lam z)
    (hu : DifferentiableAt ℝ u z) (hl1 : |lam z| ≤ 1) :
    ‖fderiv ℝ (fun x => lam x * u x) z‖ ^ 2 ≤
      2 * ‖fderiv ℝ u z‖ ^ 2 + 2 * (u z ^ 2 * ‖fderiv ℝ lam z‖ ^ 2) := by
  have e : fderiv ℝ (fun x => lam x * u x) z = lam z • fderiv ℝ u z + u z • fderiv ℝ lam z :=
    fderiv_mul hl hu
  have hn : ‖fderiv ℝ (fun x => lam x * u x) z‖ ≤ ‖fderiv ℝ u z‖ + |u z| * ‖fderiv ℝ lam z‖ := by
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hl1
    · rw [norm_smul, Real.norm_eq_abs]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h3 : (|u z| * ‖fderiv ℝ lam z‖) ^ 2 = u z ^ 2 * ‖fderiv ℝ lam z‖ ^ 2 := by
    rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg (‖fderiv ℝ u z‖ - |u z| * ‖fderiv ℝ lam z‖)]

/-- the constant of the uniform truncation bound -/
def truncM (δ : ℝ) : ℝ :=
  2 + 16 * logCutoffConst ^ 2 + 4 * logCutoffConst ^ 2 * schurL2 /
    (2 * Real.pi * (((1 + δ) ^ 2 - 1) / 2) * Real.log 2)

set_option maxHeartbeats 2000000 in
/-- **The uniform truncation bound** -/
theorem trunc_energy_le (hh : IsWholePlaneGFF h P) {ζ : ℂ → ℝ}
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, 2 < ‖x‖ → ζ x = 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hζ1 : ∀ x : ℂ, 1 < ‖x‖ → ‖x‖ < 1 + δ → ζ x = 1) {r : ℝ} (hr : 4 ≤ r)
    (g : zsSub ((⊤ : Opens ℂ) : Set ℂ)) :
    gradEnergy (fun x => logInf r (r ^ 2) x * (g.1 x - zmean ζ g.1)) ≤
      truncM δ * gradEnergy g.1 := by
  set C := logCutoffConst
  have hC : (0 : ℝ) ≤ C := by simp [C, logCutoffConst]
  set lam := logInf r (r ^ 2)
  set c := zmean ζ g.1
  set u : ℂ → ℝ := fun x => g.1 x - c with hu
  have hr0 : 0 < r := by linarith
  have h2R : 2 * r < r ^ 2 := by nlinarith
  set L := Real.log (r ^ 2 / (2 * r)) with hL
  have hLr : L = Real.log (r / 2) := by rw [hL]; congr 1; field_simp
  have hl2 : Real.log 2 ≤ L := by
    rw [hLr]; exact Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := hlog2.trans_le hl2
  have hlogr : Real.log (r ^ 2 / 1) ≤ 4 * L := by
    rw [div_one, Real.log_pow, hLr, Real.log_div hr0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have : Real.log 2 ≤ Real.log r - Real.log 2 := by
      rw [← Real.log_div hr0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.log_le_log (by norm_num) (by linarith)
    push_cast; linarith
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.1 := g.2.1
  have hgc : HasCompactSupport g.1 := g.2.2.1
  have hls : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) lam := contDiff_logInf hr0 h2R
  have hlc : HasCompactSupport lam := hasCompactSupport_logInf hr0 h2R
  have hus : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := hgs.sub contDiff_const
  have c1 : ∀ {φ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → Continuous (fderiv ℝ φ) :=
    fun hφ => (smooth_le hφ 1).continuous_fderiv one_ne_zero
  have d1 : ∀ {φ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ z,
      DifferentiableAt ℝ φ z := fun hφ z => (smooth_le hφ 1).differentiable one_ne_zero z
  set D := ∫ x, ‖fderiv ℝ g.1 x‖ ^ 2 with hD
  have hDi : Integrable fun x => ‖fderiv ℝ g.1 x‖ ^ 2 := integrable_norm_fderiv_sq hgs hgc
  have hD0 : 0 ≤ D := integral_nonneg fun x => sq_nonneg _
  have hud : ∀ z, fderiv ℝ u z = fderiv ℝ g.1 z := fun z => fderiv_sub_const c
  -- the error term `Q`
  set Q := ∫ x, u x ^ 2 * ‖fderiv ℝ lam x‖ ^ 2 with hQ
  have hQi : Integrable fun x => u x ^ 2 * ‖fderiv ℝ lam x‖ ^ 2 :=
    integrable_of_cs ((hus.continuous.pow 2).mul ((c1 hls).norm.pow 2))
      (hcs_of_vanish (hlc.fderiv (𝕜 := ℝ)) fun x hx => by simp [hx])
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => by positivity
  have hI1 : ∫ x, ‖fderiv ℝ (fun x => lam x * u x) x‖ ^ 2 ≤ 2 * D + 2 * Q := by
    have hpt := fun z => norm_fderiv_lam_mul_sq_le (d1 hls z) (d1 hus z)
      (by have := logInf_mem_Icc r (r ^ 2) z; rw [abs_le]; constructor <;> linarith [this.1])
    have hmono : ∫ x, ‖fderiv ℝ (fun x => lam x * u x) x‖ ^ 2 ≤
        ∫ x, (2 * ‖fderiv ℝ g.1 x‖ ^ 2 + 2 * (u x ^ 2 * ‖fderiv ℝ lam x‖ ^ 2)) :=
      integral_mono (integrable_norm_fderiv_sq (hls.mul hus) hlc.mul_right)
        ((hDi.const_mul 2).add (hQi.const_mul 2)) fun z => by
          have := hpt z; rw [hud] at this; exact this
    rwa [integral_add (hDi.const_mul 2) (hQi.const_mul 2), integral_const_mul,
      integral_const_mul] at hmono
  -- `Q ≤ C²/L² H`
  set A : Set ℂ := {x : ℂ | 2 * r < ‖x - 0‖ ∧ ‖x - 0‖ < r ^ 2}
  have hcont : Continuous fun x : ℂ => ‖x - 0‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hA : MeasurableSet A := (isOpen_lt continuous_const hcont).measurableSet.inter
      (isOpen_lt hcont continuous_const).measurableSet
  set H := ∫ x in A, (g.1 x - c) ^ 2 / ‖x - 0‖ ^ 2 with hH
  obtain ⟨Cg, hCg⟩ := hgc.exists_bound_of_continuous hgs.continuous
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hHi : IntegrableOn (fun x => (g.1 x - c) ^ 2 / ‖x - 0‖ ^ 2) A := by
    refine Measure.integrableOn_of_bounded (M := (Cg + |c|) ^ 2 / (2 * r) ^ 2) ?_
      (((hgs.continuous.sub continuous_const).pow 2).measurable.div
        (by fun_prop)).aestronglyMeasurable ?_
    · have hsub : A ⊆ closedBall (0 : ℂ) (r ^ 2) := fun x hx => by
        have h2 : ‖x - 0‖ < r ^ 2 := hx.2
        rw [mem_closedBall, dist_eq_norm]; exact h2.le
      exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne
    · refine (ae_restrict_iff' hA).2 (ae_of_all _ fun x hx => ?_)
      have hx0 : 2 * r < ‖x - 0‖ := hx.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hgb : |g.1 x - c| ≤ Cg + |c| := by
        have := hCg x; rw [Real.norm_eq_abs] at this
        exact (abs_sub _ _).trans (by linarith)
      have hg2 : (g.1 x - c) ^ 2 ≤ (Cg + |c|) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hgb 2
      exact div_le_div₀ (by positivity) hg2 (pow_pos h2r 2) (pow_le_pow_left₀ h2r.le hx0.le 2)
  have hQH : Q ≤ C ^ 2 / L ^ 2 * H := by
    have hQA : Q = ∫ x in A, u x ^ 2 * ‖fderiv ℝ lam x‖ ^ 2 := by
      rw [hQ, ← integral_indicator hA]
      congr 1; funext x
      by_cases hx : x ∈ A
      · simp [hx]
      · simp [hx, lam, fderiv_logInf_eq_zero hr0 h2R hx]
    rw [hQA, hH, ← integral_const_mul]
    refine setIntegral_mono_on hQi.integrableOn (hHi.const_mul _) hA fun x hx => ?_
    have hx0 : 0 < ‖x - 0‖ := h2r.trans hx.1
    have hb := norm_fderiv_logInf_le hr0 h2R x
    have hb2 : ‖fderiv ℝ lam x‖ ^ 2 ≤ (C / (L * ‖x - 0‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    calc u x ^ 2 * ‖fderiv ℝ lam x‖ ^ 2 ≤ u x ^ 2 * (C / (L * ‖x - 0‖)) ^ 2 :=
          mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
      _ = C ^ 2 / L ^ 2 * ((g.1 x - c) ^ 2 / ‖x - 0‖ ^ 2) := by
          simp only [hu]; field_simp
  -- the Hardy inequality and the Poincaré bound
  set k := ((1 + δ) ^ 2 - 1 ^ 2) / 2 with hk
  have hkpos : 0 < k := by rw [hk]; nlinarith
  set Pn := ∫ x in {x : ℂ | 1 < ‖x - 0‖ ∧ ‖x - 0‖ < 1 + δ}, (g.1 x - c) ^ 2 with hPn
  have hHardy := hardy_far (smooth_le hgs 1) hgc c (s1 := 1) (s2 := 1 + δ) (a := 2 * r)
    (b := r ^ 2) one_pos (by linarith) (by linarith) h2R
  have hPn0 : 0 ≤ Pn := setIntegral_nonneg
    ((isOpen_lt continuous_const hcont).measurableSet.inter
      (isOpen_lt hcont continuous_const).measurableSet) fun x _ => sq_nonneg _
  have hPS : Pn ≤ schurL2 * gradEnergy g.1 := by
    have hS := sq_dev_le_schur hh hζs hζ01 hζR g
    rw [norm_cmLin_sq] at hS
    have hζc := hasCompactSupport_of_ball2 hζR
    have hXi : Integrable fun x => (ζ x * (g.1 x - c)) ^ 2 :=
      integrable_of_cs ((hζs.continuous.mul (hgs.continuous.sub continuous_const)).pow 2)
        (hcs_of_vanish hζc fun x hx => by simp [hx])
    set S1 : Set ℂ := {x : ℂ | 1 < ‖x - 0‖ ∧ ‖x - 0‖ < 1 + δ}
    refine le_trans (le_of_eq ?_) ((setIntegral_le_integral (s := S1) hXi
      (Eventually.of_forall fun x => sq_nonneg _)).trans hS)
    · exact setIntegral_congr_fun ((isOpen_lt continuous_const hcont).measurableSet.inter
        (isOpen_lt hcont continuous_const).measurableSet) fun x hx => by
          have h1 : 1 < ‖x‖ := by simpa using hx.1
          have h2 : ‖x‖ < 1 + δ := by simpa using hx.2
          simp only [hζ1 x h1 h2, one_mul]
  -- assemble
  have hkH : k * H ≤ 2 * L * (k * (4 * L) * D + Pn) := by
    have h1 : k * H ≤ 2 * L * (k * Real.log (r ^ 2 / 1) * D + Pn) := hHardy
    have h2 : k * Real.log (r ^ 2 / 1) * D ≤ k * (4 * L) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogr hkpos.le) hD0
    nlinarith
  have hHle : H ≤ 2 * L * (k * (4 * L) * D + Pn) / k := by
    rw [le_div_iff₀ hkpos]; linarith
  have hQb : Q ≤ 8 * C ^ 2 * D + 2 * C ^ 2 * Pn / (k * L) := by
    calc Q ≤ C ^ 2 / L ^ 2 * H := hQH
      _ ≤ C ^ 2 / L ^ 2 * (2 * L * (k * (4 * L) * D + Pn) / k) :=
          mul_le_mul_of_nonneg_left hHle (by positivity)
      _ = 8 * C ^ 2 * D + 2 * C ^ 2 * Pn / (k * L) := by field_simp; ring
  have hQb' : 2 * C ^ 2 * Pn / (k * L) ≤ 2 * C ^ 2 * Pn / (k * Real.log 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hl2 hkpos.le)
  have hE : gradEnergy g.1 = (2 * Real.pi)⁻¹ * D := rfl
  have hpi : 0 < Real.pi := Real.pi_pos
  have hk' : ((1 + δ) ^ 2 - 1) / 2 = k := by rw [hk]; ring
  unfold gradEnergy
  rw [truncM, hk']
  set E := gradEnergy g.1 with hEdef
  have hDE : D = 2 * Real.pi * E := by rw [hE]; field_simp
  have hfin : (2 * Real.pi)⁻¹ * (2 * D + 2 * Q) ≤
      (2 + 16 * C ^ 2 + 4 * C ^ 2 * schurL2 / (2 * Real.pi * k * Real.log 2)) * E := by
    have hP' : 4 * C ^ 2 * Pn / (k * Real.log 2) ≤ 4 * C ^ 2 * (schurL2 * E) / (k * Real.log 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPS (by positivity)) (by positivity)
    have hstep : 2 * D + 2 * Q ≤ 2 * D + 16 * C ^ 2 * D + 4 * C ^ 2 * (schurL2 * E) /
        (k * Real.log 2) := by
      have : 2 * (2 * C ^ 2 * Pn / (k * Real.log 2)) = 4 * C ^ 2 * Pn / (k * Real.log 2) := by
        ring
      linarith
    calc (2 * Real.pi)⁻¹ * (2 * D + 2 * Q)
        ≤ (2 * Real.pi)⁻¹ * (2 * D + 16 * C ^ 2 * D + 4 * C ^ 2 * (schurL2 * E) /
          (k * Real.log 2)) := mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = _ := by rw [hDE]; field_simp
  calc (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ (fun x => lam x * (g.1 x - c)) z‖ ^ 2
      ≤ (2 * Real.pi)⁻¹ * (2 * D + 2 * Q) := mul_le_mul_of_nonneg_left hI1 (by positivity)
    _ ≤ _ := hfin

end MarkovGermVer
end LQGMetric
