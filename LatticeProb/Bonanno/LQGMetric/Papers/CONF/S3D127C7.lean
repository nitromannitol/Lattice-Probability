/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127C7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C4
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4(c) replaced, part 3: continuity on `U` of `P^U_h f` and of the Green potential
(packet P-127C)

* `continuousOn_killedConv`: for open `U`, `h > 0` and bounded measurable `f`,
  `x ↦ ∫ p_U(h; x, w) f(w) dw` is continuous on `U`;
* `continuousOn_greenPot'`: for bounded open `U` and bounded measurable `ρ`,
  `x ↦ ∫ G_U(x, y) ρ(y) dy` is continuous on `U` (the hypothesis `hcont` of
  `S3D127D1.contDiffOn_greenPot`).

Proof of the first (classical strong-Feller argument; own elementary implementation,
DV-P127C-2):
`P^U_h f = P^U_ε (P^U_{h−ε} f)` (`integral_killedHeat_add_mul`), and on `{x : B(x, d) ⊆ U}`,
`|P^U_ε g − P_ε g| ≤ ‖g‖_∞ err(d, ε) ≤ ‖g‖_∞ · 104 ε / d²` (`abs_killedConv_sub_heatConv_le`,
`exitErr_le`), with `P_ε g` continuous (`continuous_heatConv`). Second: dominated convergence in
`s` (`|P^U_s ρ| ≤ M min(1, R⁴ s⁻²) ≤ 4M(1 + R⁴)(1 + s)⁻²`) after Fubini.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat Blueprint

/-- **Interior continuity of the killed semigroup.** -/
theorem continuousOn_killedConv {U : Set ℂ} (hU : IsOpen U) {h : ℝ≥0} (hh : h ≠ 0)
    {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ w, |f w| ≤ M) :
    ContinuousOn (fun x ↦ ∫ w, killedHeat U h x w * f w) U := by
  intro x0 hx0
  refine (Metric.continuousAt_iff.mpr ?_).continuousWithinAt
  intro η hη
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hh' : (0 : ℝ) < h := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
  obtain ⟨d0, hd0, hball0⟩ := Metric.isOpen_iff.mp hU x0 hx0
  set d := d0 / 2 with hd_def
  have hd : 0 < d := by positivity
  -- the small time `ε`
  set e : ℝ := min ((h : ℝ) / 2) (η * d ^ 2 / (4 * 104 * (M + 1))) with he_def
  have he0 : 0 < e := lt_min (by positivity) (by positivity)
  set ε : ℝ≥0 := e.toNNReal with hε_def
  have hεe : (ε : ℝ) = e := Real.coe_toNNReal _ he0.le
  have hε0 : ε ≠ 0 := by
    intro h0; have : (ε : ℝ) = 0 := by rw [h0]; rfl
    linarith
  have hεh : ε < h := by
    rw [← NNReal.coe_lt_coe, hεe]
    exact (min_le_left _ _).trans_lt (by linarith)
  set τ : ℝ≥0 := h - ε with hτ_def
  have hτ0 : τ ≠ 0 := (tsub_pos_of_lt hεh).ne'
  have hsplit : h = ε + τ := (add_tsub_cancel_of_le hεh.le).symm
  have herr : M * exitErr d ε < η / 4 := by
    have h1 := exitErr_le hd (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hε0))
    rw [hεe] at h1 ⊢
    have h2 : 104 * e / d ^ 2 ≤ η / (4 * (M + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := min_le_right ((h : ℝ) / 2) (η * d ^ 2 / (4 * 104 * (M + 1)))
      rw [← he_def, le_div_iff₀ (by positivity)] at this
      nlinarith
    calc M * exitErr d e ≤ M * (η / (4 * (M + 1))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hM0
      _ < η / 4 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- the function `g = P^U_τ f`
  set g : ℂ → ℝ := fun v ↦ ∫ w, killedHeat U τ v w * f w with hg_def
  have hgm : AEStronglyMeasurable g := by
    have hm : StronglyMeasurable fun q : ℂ × ℂ ↦ killedHeat U τ q.1 q.2 * f q.2 :=
      ((measurable_killedHeat_uncurry hU τ).mul (hf.comp measurable_snd)).stronglyMeasurable
    exact (hm.integral_prod_right' (ν := volume)).aestronglyMeasurable
  have hgM : ∀ v, |g v| ≤ M := fun v ↦
    (abs_integral_killedHeat_mul_le hU hτ0 v hM).trans
      (mul_le_of_le_one_right hM0 (ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact killedSurv_le_one U hτ0 v)))
  have hF : ∀ x, ∫ w, killedHeat U h x w * f w = ∫ v, killedHeat U ε x v * g v := fun x ↦ by
    rw [hsplit]; exact integral_killedHeat_add_mul hU hε0 hτ0 x hf hM
  -- the continuous approximation
  have hA := continuous_heatConv (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hε0)) hgm hgM
  obtain ⟨δ', hδ', hAδ⟩ := Metric.continuousAt_iff.mp hA.continuousAt (η / 4) (by positivity)
  have happrox : ∀ x, dist x x0 < d →
      |(∫ v, killedHeat U ε x v * g v) - ∫ v, heatKernel ε x v * g v| < η / 4 := by
    intro x hx
    have hb : ball x d ⊆ U := fun y hy ↦ hball0 (by
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle y x x0])
    exact (abs_killedConv_sub_heatConv_le hU hε0 hgm hgM hd hb).trans_lt herr
  refine ⟨min d δ', lt_min hd hδ', fun x hx ↦ ?_⟩
  have hx1 : dist x x0 < d := hx.trans_le (min_le_left _ _)
  have hx2 : dist x x0 < δ' := hx.trans_le (min_le_right _ _)
  rw [hF, hF, Real.dist_eq]
  have a1 := happrox x hx1
  have a2 := happrox x0 (by rw [dist_self]; exact hd)
  have a3 := hAδ hx2
  rw [Real.dist_eq] at a3
  set K1 := ∫ v, killedHeat U ε x v * g v
  set K0 := ∫ v, killedHeat U ε x0 v * g v
  set H1 := ∫ v, heatKernel ε x v * g v
  set H0 := ∫ v, heatKernel ε x0 v * g v
  have t1 := abs_sub_le K1 H1 K0
  have t2 := abs_sub_le H1 H0 K0
  have t3 : |H0 - K0| = |K0 - H0| := abs_sub_comm _ _
  linarith

/-- `P^x(τ_U > s) ≤ 4(1 + R⁴)(1 + |s|)⁻²` for `U ⊆ B(c, R)`, `s > 0`. -/
lemma toReal_killedSurv_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {s : ℝ} (hs : 0 < s) (x : ℂ) :
    (killedSurv U s.toNNReal x).toReal ≤ 4 * (1 + R ^ 4) * (1 + ‖s‖) ^ (-(2 : ℝ)) := by
  have hs' : s.toNNReal ≠ 0 := by simpa using hs
  rw [Real.norm_eq_abs, abs_of_pos hs, Real.rpow_neg (by positivity), Real.rpow_two]
  have hR4 : 0 ≤ R ^ 4 := by positivity
  rcases le_or_gt s 1 with h1 | h1
  · refine (ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact killedSurv_le_one U hs' x)).trans ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith
  · refine (ENNReal.toReal_le_of_le_ofReal (by positivity)
      (killedSurv_le_rpow hU hR hUR hs x)).trans ?_
    rw [Real.rpow_neg hs.le, Real.rpow_two, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (1 + s) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hR4, sq_nonneg s]

/-- **Continuity of the Green potential on `U`** (bounded open `U`, bounded measurable `ρ`):
the hypothesis `hcont` of `contDiffOn_greenPot` (S3D127D1). -/
theorem continuousOn_greenPot' {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {ρ : ℂ → ℝ} (hρ : Measurable ρ) {M : ℝ} (hM : ∀ y, |ρ y| ≤ M) :
    ContinuousOn (fun x ↦ ∫ y, killedGreen U x y * ρ y) U := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set F : ℂ → ℝ → ℝ := fun x s ↦ ∫ y, killedHeat U s.toNNReal x y * ρ y with hF_def
  have hjm : ∀ x, Measurable fun q : ℂ × ℝ ↦ killedHeat U q.2.toNNReal x q.1 := fun x ↦ by
    have := (measurable_killedHeat hU).comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
      ((measurable_const : Measurable fun _ : ℂ × ℝ ↦ x).prodMk measurable_fst))
    exact this
  -- Fubini: `∫ G_U(x, ·) ρ = π ∫ F x`
  have hrep : ∀ x, ∫ y, killedGreen U x y * ρ y = Real.pi * ∫ s, F x s ∂μ := by
    intro x
    have hint0 : Integrable (fun q : ℂ × ℝ ↦ killedHeat U q.2.toNNReal x q.1) (volume.prod μ) := by
      refine ⟨(hjm x).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun q ↦ killedHeat_nonneg _ _ _ _),
        lintegral_prod _ (hjm x).ennreal_ofReal.aemeasurable]
      have hsw := lintegral_lintegral_swap (μ := (volume : Measure ℂ)) (ν := μ)
        (f := fun (y : ℂ) (s : ℝ) ↦ ENNReal.ofReal (killedHeat U s.toNNReal x y))
        (hjm x).ennreal_ofReal.aemeasurable
      rw [hsw]
      have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
      refine (lintegral_killedSurv_le hU hR hUR h1 x).trans_lt ?_
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ?_
        ENNReal.ofReal_lt_top⟩
      exact (killedSurv_le_one U h1 x).trans_lt ENNReal.one_lt_top
    have hint : Integrable (fun q : ℂ × ℝ ↦ killedHeat U q.2.toNNReal x q.1 * ρ q.1)
        (volume.prod μ) := by
      refine (hint0.const_mul M).mono' ((hjm x).mul (hρ.comp measurable_fst)).aestronglyMeasurable
        (Eventually.of_forall fun q ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _) (killedHeat_nonneg _ _ _ _)
    have hpt : ∀ y, killedGreen U x y * ρ y =
        Real.pi * ∫ s, killedHeat U s.toNNReal x y * ρ y ∂μ := fun y ↦ by
      rw [killedGreen, mul_assoc, integral_mul_const]
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
    congr 1
    exact integral_integral_swap (f := fun (y : ℂ) (s : ℝ) ↦ killedHeat U s.toNNReal x y * ρ y) hint
  have hcont : ContinuousOn (fun x ↦ ∫ s, F x s ∂μ) U := by
    refine continuousOn_of_dominated (bound := fun s ↦ M * (4 * (1 + R ^ 4) *
      (1 + ‖s‖) ^ (-(2 : ℝ)))) ?_ ?_ ?_ ?_
    · intro x _
      have hm : StronglyMeasurable fun q : ℝ × ℂ ↦ killedHeat U q.1.toNNReal x q.2 * ρ q.2 := by
        have := ((hjm x).comp measurable_swap).mul (hρ.comp measurable_snd)
        exact this.stronglyMeasurable
      exact (hm.integral_prod_right' (ν := volume)).aestronglyMeasurable
    · intro x _
      refine (ae_restrict_mem measurableSet_Ioi).mono fun s hs ↦ ?_
      have hs : (0 : ℝ) < s := hs
      have hs' : s.toNNReal ≠ 0 := by simpa using hs
      rw [Real.norm_eq_abs]
      exact (abs_integral_killedHeat_mul_le hU hs' x hM).trans
        (mul_le_mul_of_nonneg_left (toReal_killedSurv_le hU hR hUR hs x) hM0)
    · exact (((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
        (by simp)).const_mul _).const_mul _).integrableOn
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun s hs ↦ ?_
      have hs : (0 : ℝ) < s := hs
      exact continuousOn_killedConv hU (by simpa using hs) hρ hM
  exact (hcont.const_smul Real.pi).congr fun x _ ↦ by
    rw [hrep x, Pi.smul_apply, smul_eq_mul]

/-- `|∫ G_U(x, y) ρ(y) dy| ≤ M ∫ G_U(x, y) dy` for bounded open `U`, `|ρ| ≤ M`. -/
theorem abs_integral_killedGreen_mul_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {ρ : ℂ → ℝ} {M : ℝ} (hM : ∀ y, |ρ y| ≤ M) (x : ℂ) :
    |∫ y, killedGreen U x y * ρ y| ≤ M * ∫ y, killedGreen U x y := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrable_killedGreen hU hR hUR x).const_mul M)
    (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedGreen_nonneg U x y), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM y) (killedGreen_nonneg U x y)

/-- **D127 N4(a)–(c) at `confU`, for the Green potential** `u = ∫ G_U(·, y) ρ(y) dy` of a bounded
measurable `ρ`: `u` is continuous on `U`, `u → 0` uniformly at `∂U`, and its superlevel sets
`{x ∈ U | ε ≤ u x}` have compact closure inside `U`. -/
theorem greenPot_confU_props {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) (T : Finset (ℤ × ℤ))
    {ρ : ℂ → ℝ} (hρ : Measurable ρ) {M : ℝ} (hM : ∀ y, |ρ y| ≤ M) :
    ContinuousOn (fun x ↦ ∫ y, killedGreen (confU r δ z T) x y * ρ y) (confU r δ z T) ∧
    (∀ ε > 0, ∃ η > 0, ∀ x : ℂ, infDist x (confU r δ z T)ᶜ < η →
      |∫ y, killedGreen (confU r δ z T) x y * ρ y| ≤ ε) ∧
    ∀ ε > 0, IsCompact (closure {x | x ∈ confU r δ z T ∧
        ε ≤ ∫ y, killedGreen (confU r δ z T) x y * ρ y}) ∧
      closure {x | x ∈ confU r δ z T ∧ ε ≤ ∫ y, killedGreen (confU r δ z T) x y * ρ y} ⊆
        confU r δ z T := by
  have hU := isOpen_confU r δ z T
  have hR : (0 : ℝ) < 4 * r := by positivity
  have hUR := confU_subset_ball r δ z T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨continuousOn_greenPot' hU hR.le hUR hρ hM, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · obtain ⟨η, hη, hG⟩ := integral_killedGreen_confU_le hr hδ z T (ε / (M + 1)) (by positivity)
    refine ⟨η, hη, fun x hx ↦ ?_⟩
    refine (abs_integral_killedGreen_mul_le hU hR.le hUR hM x).trans ?_
    calc M * ∫ y, killedGreen (confU r δ z T) x y ≤ (M + 1) * (ε / (M + 1)) :=
          mul_le_mul (by linarith) (hG x hx)
            (integral_nonneg fun y ↦ killedGreen_nonneg _ x y) (by linarith)
      _ = ε := by field_simp
  · exact closure_superlevel_subset hU hR hUR (lt_min (by positivity) hr)
      (extCorkscrew_confU hr hδ z T) (fun x _ ↦ (le_abs_self _).trans
        (abs_integral_killedGreen_mul_le hU hR.le hUR hM x)) hε

end ZBM
end CONF
end LQGMetric
