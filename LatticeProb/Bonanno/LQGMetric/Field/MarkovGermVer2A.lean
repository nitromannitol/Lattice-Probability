/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer2A at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVerPot
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar

/-!
# Mean-zero pairings are whole-plane Dirichlet pairings (task P2-MKD2, nodes (a1), (a2))

Node (a) of `handoff/P2-MKD.md`: for `ψ ∈ 𝓓₀(ℂ)`, `[⟨h, ψ⟩]` lies in the range of the
whole-plane Cameron–Martin isometry `cmIso hh ⊤`.

* `abs_logPot_le` (a1): the logarithmic potential of a mean-zero test function decays like
  `C/|x|` (write `u_ψ(x) = −∫ (log|x−y| − log|x|) ψ(y) dy` and use `|log|x−y| − log|x|| ≤ 2|y|/|x|`
  for `|y| ≤ |x|/2`);
* `pair_mem_range_cmIso_top` (a2): with the cutoffs `χ_R(x) = χ₁(x/R)` (`χ₁` a bump, `= 1` on
  `B̄₁`, supported in `B̄₂`), `norm_cmLin_cut_sub_sq` gives
  `‖(h, χ_R u_ψ)_∇ − ⟨h, ψ⟩‖² = (2π)⁻¹ ∫ u_ψ² |∇χ_R|² = O(R⁻²)`, and the range of the isometry
  `cmIso hh ⊤` is closed.

Source: Sheffield, *Gaussian free fields for mathematicians* (math/0312099), §2.6
(`(h, a)_∇ = (h, ρ)` for `−Δa = 2πρ`); Berestycki–Powell (arXiv:2404.16642) §1.8 (whole-plane
GFF as the Dirichlet-space Gaussian field modulo constants). The decay estimate and the cutoff
limit are the standard elementary steps (own elementary proof of these two estimates).
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

/-- `|log a − log b| ≤ 2 s / b` when `|a − b| ≤ s` and `2 s ≤ b` -/
lemma abs_log_sub_log_le {a b s : ℝ} (hab : |a - b| ≤ s) (hb : 2 * s ≤ b) (hs : 0 < s) :
    |Real.log a - Real.log b| ≤ 2 * s / b := by
  have hb0 : 0 < b := by linarith
  have h1 := (abs_le.1 hab)
  have ha0 : 0 < a := by linarith
  have ha2 : b / 2 ≤ a := by linarith
  rw [abs_le]
  constructor
  · -- log b − log a = log (b/a) ≤ b/a − 1 = (b − a)/a ≤ s/a ≤ 2s/b
    have e : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb0.ne' ha0.ne').symm
    have h2 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : b / a - 1 ≤ 2 * s / b := by
      rw [div_sub_one ha0.ne', div_le_div_iff₀ ha0 hb0]
      nlinarith
    linarith
  · have e : Real.log a - Real.log b = Real.log (a / b) := (Real.log_div ha0.ne' hb0.ne').symm
    have h2 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : a / b - 1 ≤ 2 * s / b := by
      rw [div_sub_one hb0.ne', div_le_div_iff_of_pos_right hb0]
      linarith
    linarith

/-- **(a1) Decay of the logarithmic potential of a mean-zero test function.** -/
theorem abs_logPot_le (ψ : TestC0) : ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ x : ℂ, R₀ ≤ ‖x‖ →
    |logPot ψ.1 x| ≤ C / ‖x‖ := by
  obtain ⟨r, hr⟩ := ψ.1.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set r' := max r 1 with hr'
  have hr'0 : 0 < r' := lt_max_of_lt_right one_pos
  have hψi : Integrable (ψ.1 : ℂ → ℝ) :=
    ψ.1.contDiff.continuous.integrable_of_hasCompactSupport ψ.1.hasCompactSupport
  refine ⟨2 * r' * ∫ y, |ψ.1 y|, 2 * r', by positivity, fun x hx => ?_⟩
  have hx0 : 0 < ‖x‖ := by linarith
  have hpt : ∀ y, ‖(Real.log ‖x - y‖ - Real.log ‖x‖) * ψ.1 y‖ ≤ 2 * r' / ‖x‖ * |ψ.1 y| := by
    intro y
    by_cases hy : y ∈ tsupport (ψ.1 : ℂ → ℝ)
    · have hyr : ‖y‖ ≤ r' := (mem_closedBall_zero_iff.1 (hr hy)).trans (le_max_left _ _)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right (abs_log_sub_log_le ?_ hx hr'0) (abs_nonneg _)
      refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [sub_sub_cancel_left, norm_neg]; exact hyr
    · rw [image_eq_zero_of_notMem_tsupport hy]; simp
  have hm : AEStronglyMeasurable (fun y => (Real.log ‖x - y‖ - Real.log ‖x‖) * ψ.1 y) volume :=
    ((((measurable_const.sub measurable_id).norm.log).sub measurable_const).mul
      ψ.1.contDiff.continuous.measurable).aestronglyMeasurable
  have hi1 : Integrable (fun y => (Real.log ‖x - y‖ - Real.log ‖x‖) * ψ.1 y) :=
    Integrable.mono' (hψi.abs.const_mul _) hm (ae_of_all _ hpt)
  have hi2 : Integrable (fun y => Real.log ‖x‖ * ψ.1 y) := hψi.const_mul _
  have e : logPot ψ.1 x = -∫ y, (Real.log ‖x - y‖ - Real.log ‖x‖) * ψ.1 y := by
    have e1 : (fun y => -Real.log ‖x - y‖ * ψ.1 y) = fun y =>
        -((Real.log ‖x - y‖ - Real.log ‖x‖) * ψ.1 y + Real.log ‖x‖ * ψ.1 y) := by
      funext y; ring
    rw [logPot, e1, integral_neg, integral_add hi1 hi2, integral_const_mul, ψ.2, mul_zero,
      add_zero]
  rw [e, abs_neg]
  refine (norm_integral_le_of_norm_le (hψi.abs.const_mul _) (ae_of_all _ hpt)).trans
    (le_of_eq ?_)
  rw [integral_const_mul]; ring

/-! ## The cutoffs `χ_R` -/

/-- the bump `χ₁`: `= 1` on `B̄₁(0)`, support `B₂(0)` -/
def bump1 : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ_R(x) = χ₁(x/R)` -/
def cutR (R : ℝ) (x : ℂ) : ℝ := bump1 (R⁻¹ • x)

lemma contDiff_cutR (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutR R) :=
  bump1.contDiff.comp (contDiff_id.const_smul R⁻¹)

lemma cutR_eq_zero {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : 2 * R < ‖x‖) : cutR R x = 0 := by
  refine bump1.zero_of_le_dist ?_
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  change (2 : ℝ) ≤ R⁻¹ * ‖x‖
  rw [le_inv_mul_iff₀ hR]; linarith

lemma hasCompactSupport_cutR {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutR R) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (2 * R)) fun x hx =>
    cutR_eq_zero hR (by simpa using hx)

lemma cutR_eq_one {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : ‖x‖ ≤ R) : cutR R x = 1 := by
  refine bump1.one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  change R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]; linarith

lemma hasFDerivAt_cutR (R : ℝ) (x : ℂ) :
    HasFDerivAt (cutR R) ((fderiv ℝ bump1 (R⁻¹ • x)).comp
      (R⁻¹ • ContinuousLinearMap.id ℝ ℂ)) x := by
  have h1 : HasFDerivAt (fun y : ℂ => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ ℂ) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  exact ((bump1.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x h1

/-- `|∇χ₁| ≤ K₁` -/
lemma exists_bound_fderiv_bump1 : ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖fderiv ℝ bump1 y‖ ≤ K := by
  obtain ⟨K, hK⟩ := (bump1.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((bump1.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  exact ⟨max K 0, le_max_right _ _, fun y => (hK y).trans (le_max_left _ _)⟩

/-- `|∇χ_R(x)| ≤ K₁/R`, and `∇χ_R(x) = 0` unless `R ≤ |x| ≤ 2R` -/
lemma norm_fderiv_cutR_le {R K : ℝ} (hR : 0 < R) (hK : ∀ y, ‖fderiv ℝ bump1 y‖ ≤ K) (x : ℂ) :
    ‖fderiv ℝ (cutR R) x‖ ≤ K / R ∧
      (fderiv ℝ (cutR R) x ≠ 0 → R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R) := by
  rw [(hasFDerivAt_cutR R x).fderiv]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨?_, fun hne => ?_⟩
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_mul_inv]
    refine mul_le_mul (hK _) ?_ (by positivity) hK0
    exact (mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le)
  · have hne' : fderiv ℝ bump1 (R⁻¹ • x) ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    have hn : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    constructor
    · by_contra hlt
      push Not at hlt
      apply hne'
      have hb : R⁻¹ • x ∈ ball (0 : ℂ) bump1.rIn := by
        rw [mem_ball_zero_iff, hn]
        change R⁻¹ * ‖x‖ < 1
        rw [inv_mul_lt_iff₀ hR]; linarith
      rw [(bump1.eventuallyEq_one_of_mem_ball hb).fderiv_eq]
      exact fderiv_const_apply _
    · by_contra hlt
      push Not at hlt
      apply hne'
      refine fderiv_of_notMem_tsupport ℝ ?_
      rw [bump1.tsupport_eq, mem_closedBall_zero_iff, hn, not_le]
      change (2 : ℝ) < R⁻¹ * ‖x‖
      rw [lt_inv_mul_iff₀ hR]; linarith

omit [IsProbabilityMeasure P] in
lemma integral_logPot_cutR_le {ψ : TestC0} {C K R : ℝ} (hR : 0 < R)
    (hC : ∀ x : ℂ, R ≤ ‖x‖ → |logPot ψ.1 x| ≤ C / ‖x‖)
    (hK : ∀ y, ‖fderiv ℝ bump1 y‖ ≤ K) :
    ∫ x, logPot ψ.1 x ^ 2 * ‖fderiv ℝ (cutR R) x‖ ^ 2 ≤
      (C / R) ^ 2 * (K / R) ^ 2 * (Real.pi * (2 * R) ^ 2) := by
  set c := (C / R) ^ 2 * (K / R) ^ 2
  have hc : 0 ≤ c := by positivity
  have hpt : ∀ x, logPot ψ.1 x ^ 2 * ‖fderiv ℝ (cutR R) x‖ ^ 2 ≤
      (closedBall (0 : ℂ) (2 * R)).indicator (fun _ => c) x := by
    intro x
    obtain ⟨hb, hs⟩ := norm_fderiv_cutR_le hR hK x
    by_cases hne : fderiv ℝ (cutR R) x = 0
    · rw [hne, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact indicator_nonneg (fun _ _ => hc) _
    obtain ⟨h1, h2⟩ := hs hne
    rw [indicator_of_mem (mem_closedBall_zero_iff.2 h2)]
    have hx0 : 0 < ‖x‖ := hR.trans_le h1
    have hu := hC x h1
    have hC0 : 0 ≤ C := by
      have := (abs_nonneg _).trans hu
      exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hx0)
    have hu' : |logPot ψ.1 x| ≤ C / R :=
      hu.trans (div_le_div_of_nonneg_left hC0 hR h1)
    have e1 : logPot ψ.1 x ^ 2 ≤ (C / R) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu' 2
    have e2 : ‖fderiv ℝ (cutR R) x‖ ^ 2 ≤ (K / R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  refine (integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
    ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)) (ae_of_all _ hpt)).trans (le_of_eq ?_)
  rw [integral_indicator measurableSet_closedBall, setIntegral_const]
  simp only [smul_eq_mul, measureReal_def, volume_closedBall_toReal _ (by positivity : (0:ℝ) ≤ 2 * R)]
  ring

/-- **(a2) Every mean-zero pairing is a whole-plane Dirichlet pairing**: `[⟨h, ψ⟩]` lies in the
range of `cmIso hh ⊤` (it is the limit of `(h, χ_R u_ψ)_∇`). -/
theorem pair_mem_range_cmIso_top (hh : IsWholePlaneGFF h P) (ψ : TestC0) :
    (memLp_pair hh ψ).toLp (pairProc h ψ) ∈ Set.range (cmIso hh ⊤) := by
  have hcl : IsClosed (Set.range (cmIso hh ⊤)) :=
    (cmIso hh ⊤).isometry.isClosedEmbedding.isClosed_range
  rw [← hcl.closure_eq, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨C, R₀, hR₀, hC⟩ := abs_logPot_le ψ
  obtain ⟨K, hK0, hK⟩ := exists_bound_fderiv_bump1
  obtain ⟨r, hr⟩ := ψ.1.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set M := 2 * C ^ 2 * K ^ 2 with hM
  set R := max (max R₀ r) (max 1 (M / δ ^ 2 + 1)) with hRdef
  have hR1 : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRpos : 0 < R := one_pos.trans_le hR1
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRr : r ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hRM : M / δ ^ 2 < R :=
    (lt_add_one _).trans_le ((le_max_right _ _).trans (le_max_right _ _))
  have hχ1 : ∀ x ∈ tsupport (ψ.1 : ℂ → ℝ), cutR R x = 1 := fun x hx =>
    cutR_eq_one hRpos ((mem_closedBall_zero_iff.1 (hr hx)).trans hRr)
  have key := norm_cmLin_cut_sub_sq hh ψ (contDiff_cutR R) (hasCompactSupport_cutR hRpos) hχ1
  refine ⟨_, ⟨gradLin ⊤ (ofSmooth ((contDiff_cutR R).mul (contDiff_logPot ψ.1))
    ((hasCompactSupport_cutR hRpos).mul_right (f' := logPot ψ.1))), rfl⟩, ?_⟩
  rw [cmIso_gradLin, dist_comm, dist_eq_norm]
  have hb := integral_logPot_cutR_le (ψ := ψ) hRpos (fun x hx => hC x (hRR₀.trans hx)) hK
  have hsq : ‖cmLin hh ⊤ (ofSmooth ((contDiff_cutR R).mul (contDiff_logPot ψ.1))
      ((hasCompactSupport_cutR hRpos).mul_right (f' := logPot ψ.1))) -
        (memLp_pair hh ψ).toLp (pairProc h ψ)‖ ^ 2 < δ ^ 2 := by
    rw [key]
    refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_lt ?_
    have e : (2 * Real.pi)⁻¹ * ((C / R) ^ 2 * (K / R) ^ 2 * (Real.pi * (2 * R) ^ 2)) =
        M / R ^ 2 := by
      rw [hM]; field_simp
    rw [e]
    have hδ2 : 0 < δ ^ 2 := by positivity
    have h1 : M / R ^ 2 ≤ M / R := by
      have hM0 : 0 ≤ M := by positivity
      exact div_le_div_of_nonneg_left hM0 hRpos (by nlinarith)
    refine h1.trans_lt ?_
    rw [div_lt_iff₀ hRpos]
    rw [div_lt_iff₀ hδ2] at hRM
    linarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 hsq

end MarkovGermVer
end LQGMetric
