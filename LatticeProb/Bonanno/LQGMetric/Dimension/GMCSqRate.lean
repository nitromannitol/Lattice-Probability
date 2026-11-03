/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqRate at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqTRL

/-!
# `L¹` rate for the approximating area measures of the square GFF (P2-GMC, WP-24)

For `hX : IsZeroBoundaryGFFOn openSquare X P`, `0 < γ < 2` and `f` bounded measurable, vanishing
off a measurable `S ⊆ sqIn s`:

* `integral_abs_areaApprox_step_le_sq` : the two-radius bound for consecutive levels;
* `integral_abs_areaApprox_step_le_rate_sq` : `≤ C e^{−β k log 2}`, `β = areaRate γ > 0`;
* `integral_abs_areaApprox_sub_le_rate_sq` : telescoped, for `k ≤ k'`.

Verbatim port of QZ `AreaExist.integral_abs_areaApprox_step_le`, `…_step_le_rate`,
`…_sub_le_rate` (`Proofs/LQG/AreaExistence.lean`) from the normalized free field on `ℍ` to the
zero-boundary field on `𝕍` (hypotheses `trlHypC_sq`; `K = log 3`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper Real
open scoped ENNReal NNReal

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Measure ℂ → ℝ}

/-- density of `areaApprox γ (X ω) j` -/
def sDens (γ : ℝ) (X : Ω → Measure ℂ → ℝ) (j : ℕ) (z : ℂ) (ω : Ω) : ℝ :=
  radius j ^ (γ ^ 2 / 2) * exp (γ * sU X j z ω)

/-- Joint integrability of `f z · dens_j(z, ω)` on `P × (vol|S)`. -/
theorem integrable_fDens_sq (hX : IsZeroBoundaryGFFOn openSquare X P) {s : ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hSs : S ⊆ sqIn s) (γ : ℝ) {f : ℂ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) {j : ℕ} (hj : 4 * radius j ≤ s) :
    Integrable (fun p : Ω × ℂ => f p.2 * sDens γ X j p.2 p.1) (P.prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  have h := trlHypC_sq (P := P) hX hSs hj
  have h1 : Measurable (fun p : Ω × ℂ => sU X j p.2 p.1) :=
    (measurable_sU hX j).comp (measurable_snd.prodMk measurable_fst)
  have hmeas : Measurable (fun p : Ω × ℂ => f p.2 * sDens γ X j p.2 p.1) :=
    (hf.comp measurable_snd).mul (measurable_const.mul ((h1.const_mul _).exp))
  have hr := (rpow_pos_of_pos (radius_pos j) (γ ^ 2 / 2))
  set Vb := 2 * (1 / 2 * log (1 / radius j)) + Real.log 3 with hVb
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' hS]
    refine ae_of_all _ fun z hz => ?_
    have hL := h.lawU z hz
    have hi : Integrable (fun ω => exp (0 + γ * sU X j z ω)) P :=
      hL.integrable_fun_comp (TwoRadius.integrable_exp_mul_add_gaussianReal _ γ 0)
    simp only [zero_add] at hi
    exact (hi.const_mul _).const_mul (f z)
  · refine Integrable.mono' (integrable_const
      (M * (radius j ^ (γ ^ 2 / 2) * exp (Vb * γ ^ 2 / 2)))) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    · rw [ae_restrict_iff' hS]
      refine ae_of_all _ fun z hz => ?_
      have e : ∀ ω, ‖f z * sDens γ X j z ω‖ =
          |f z| * (radius j ^ (γ ^ 2 / 2) * exp (γ * sU X j z ω)) := by
        intro ω
        rw [Real.norm_eq_abs, abs_mul, sDens, abs_of_pos (mul_pos hr (exp_pos _))]
      simp_rw [e]
      have hexp : ∫ ω, exp (γ * sU X j z ω) ∂P = exp (sV j z * γ ^ 2 / 2) := by
        have hL := h.lawU z hz
        have h2 := TwoRadius.integral_exp_mul_add_gaussianReal (sV j z) γ 0
        simp only [zero_add] at h2
        rw [← h2]
        exact hL.integral_comp (f := fun x => exp (γ * x)) (by fun_prop)
      rw [integral_const_mul, integral_const_mul, hexp, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      have hv : (sV j z : ℝ) * γ ^ 2 / 2 ≤ Vb * γ ^ 2 / 2 := by
        have := h.varU z hz
        have hg2 : 0 ≤ γ ^ 2 := sq_nonneg γ
        nlinarith
      exact mul_le_mul (hM z) (mul_le_mul_of_nonneg_left (exp_le_exp.2 hv) hr.le)
        (by positivity) ((abs_nonneg _).trans (hM z))

omit [IsProbabilityMeasure P] in
theorem integral_areaApprox_sq (γ : ℝ) (j : ℕ) {S : Set ℂ} (hSH : S ⊆ H)
    {f : ℂ → ℝ} (hfS : ∀ z ∉ S, f z = 0) (ω : Ω) :
    ∫ z, f z ∂(areaApprox γ (X ω) j) = ∫ z in S, f z * sDens γ X j z ω :=
  AreaExist.integral_areaApprox_eq γ _ j hSH hfS

lemma sqIn_subset_H {s : ℝ} (hs : 0 < s) : sqIn s ⊆ H := fun z hz =>
  (sqIn_subset_openSquare hs hz).2.2.1

theorem integrable_integral_areaApprox_sq (hX : IsZeroBoundaryGFFOn openSquare X P) {s : ℝ}
    (hs : 0 < s) {S : Set ℂ} (hS : MeasurableSet S) (hSf : volume S < ∞) (hSs : S ⊆ sqIn s)
    (γ : ℝ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (hfS : ∀ z ∉ S, f z = 0) {j : ℕ} (hj : 4 * radius j ≤ s) :
    Integrable (fun ω => ∫ z, f z ∂(areaApprox γ (X ω) j)) P := by
  simp_rw [integral_areaApprox_sq (X := X) γ j (hSs.trans (sqIn_subset_H hs)) hfS]
  exact (integrable_fDens_sq hX hS hSf hSs γ hf hM hj).integral_prod_left

open TwoRadius TwoRadiusC in
/-- **planar two-radius lemma for the square field** (port of QZ
`AreaExist.integral_abs_areaApprox_step_le`) -/
theorem integral_abs_areaApprox_step_le_sq (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {s M : ℝ} (hs : 0 < s) {S : Set ℂ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSs : S ⊆ sqIn s) {f : ℂ → ℝ} (hf : Measurable f)
    (hM : ∀ z, |f z| ≤ M) (hfS : ∀ z ∉ S, f z = 0) {k : ℕ} (hk : 4 * radius k ≤ s) :
    ∫ ω, |∫ z, f z ∂(areaApprox γ (X ω) k) - ∫ z, f z ∂(areaApprox γ (X ω) (k + 1))| ∂P
      ≤ √(M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
            (exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 * Real.log 3 / 2) *
            exp ((2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) *
              (1 / 2 * log (1 / radius k))))) *
            (π * (2 * radius k) ^ 2 * volume.real S))
        + M * (2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * Real.log 3 / 2) *
            exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * log (1 / radius k))))) * volume.real S := by
  have hSH : S ⊆ H := hSs.trans (sqIn_subset_H hs)
  have h := trlHypC_sq (P := P) hX hSs hk
  have hk1 : 4 * radius (k + 1) ≤ s := by
    rw [radius_succ']; linarith [radius_pos k]
  have hr := radius_pos k
  have hb := trlC_bound_area hγ hγ2 (δ := 2 * radius k) (by positivity) hS hSf hf hM h
  refine le_trans (le_of_eq (integral_congr_ae ?_)) hb
  filter_upwards [(integrable_fDens_sq hX hS hSf hSs γ hf hM hk).prod_right_ae,
    (integrable_fDens_sq hX hS hSf hSs γ hf hM hk1).prod_right_ae] with ω h1 h2
  rw [integral_areaApprox_sq γ k hSH hfS, integral_areaApprox_sq γ (k + 1) hSH hfS,
    ← integral_sub h1 h2]
  congr 1
  refine setIntegral_congr_fun hS fun z _ => ?_
  set A := sU X k z ω with hA
  set B := sU X (k + 1) z ω with hB
  have e1 : radius k ^ (γ ^ 2 / 2) * exp (γ * A)
      = exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (1 / radius k)) + 2 * γ / 2 * A) := by
    rw [rpow_def_of_pos hr, ← exp_add,
      show log (1 / radius k) = -log (radius k) by rw [one_div, log_inv]]
    congr 1; ring
  have e2 : radius (k + 1) ^ (γ ^ 2 / 2) * exp (γ * B)
      = exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (1 / radius k)) + 2 * γ / 2 * A) *
        exp (-((2 * γ) ^ 2 / 8 * log 2) + 2 * γ / 2 * (B - A)) := by
    rw [radius_succ', rpow_def_of_pos (by positivity), ← exp_add, ← exp_add,
      log_div hr.ne' two_ne_zero,
      show log (1 / radius k) = -log (radius k) by rw [one_div, log_inv]]
    congr 1; ring
  have hlog2 : (0 : ℝ) ≤ log 2 := log_nonneg one_le_two
  simp only [sDens, dC, tiltY, sΔ, ← hA, ← hB]
  rw [Real.coe_toNNReal _ hlog2, e1, e2]
  ring

/-- **rate form** (port of QZ `AreaExist.integral_abs_areaApprox_step_le_rate`) -/
theorem integral_abs_areaApprox_step_le_rate_sq (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {s M : ℝ} (hs : 0 < s) {S : Set ℂ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hSs : S ⊆ sqIn s) {f : ℂ → ℝ}
    (hf : Measurable f) (hM : ∀ z, |f z| ≤ M) (hfS : ∀ z ∉ S, f z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, 4 * radius k ≤ s →
      ∫ ω, |∫ z, f z ∂(areaApprox γ (X ω) k) - ∫ z, f z ∂(areaApprox γ (X ω) (k + 1))| ∂P
        ≤ C * exp (-AreaExist.areaRate γ * (k * log 2)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set θ := max 0 ((3 * γ - 2) / 2) with hθ
  set e₁ := 2 - γ ^ 2 + θ ^ 2 / 2 with he₁
  set β := AreaExist.areaRate γ with hβ
  set K := Real.log 3 with hK
  have hβ1 : β ≤ e₁ / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 8 := min_le_right _ _
  set c₁ := M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
      exp ((2 * γ - θ) ^ 2 * K / 2)) * (4 * π * volume.real S) with hc₁
  set c₂ := M * (2 * exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S
    with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨√c₁ + c₂, by positivity, fun k hk => ?_⟩
  refine (integral_abs_areaApprox_step_le_sq hX hγ hγ2 hs hS hSf hSs hf hM hfS hk).trans ?_
  set L := log (1 / radius k) with hL
  have hLk : L = k * log 2 := AreaExist.alog_one_div_radius k
  have hL0 : 0 ≤ L := by rw [hLk]; exact mul_nonneg (Nat.cast_nonneg k) (log_nonneg one_le_two)
  have hrad : radius k = exp (-L) := by
    rw [hL, one_div, log_inv, neg_neg, exp_log (radius_pos k)]
  have hin : M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
        (exp ((2 * γ - θ) ^ 2 * K / 2) * exp ((2 * γ ^ 2 - θ ^ 2) * (1 / 2 * L)))) *
        (π * (2 * radius k) ^ 2 * volume.real S) = c₁ * exp (-e₁ * L) := by
    rw [hrad, hc₁, he₁]
    have : exp ((2 * γ ^ 2 - θ ^ 2) * (1 / 2 * L)) * exp (-L) ^ 2
        = exp (-(2 - γ ^ 2 + θ ^ 2 / 2) * L) := by
      rw [← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
    calc _ = M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
          exp ((2 * γ - θ) ^ 2 * K / 2)) * (4 * π * volume.real S) *
          (exp ((2 * γ ^ 2 - θ ^ 2) * (1 / 2 * L)) * exp (-L) ^ 2) := by ring
      _ = _ := by rw [this]
  have hexp1 : exp (-e₁ * L) ≤ exp (-β * L) ^ 2 := by
    rw [← exp_nat_mul]; apply exp_le_exp.2; push_cast; nlinarith
  have hexp2 : exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * L)) ≤ exp (-β * L) := by
    apply exp_le_exp.2; nlinarith
  rw [hin, ← hLk]
  have ht1 : √(c₁ * exp (-e₁ * L)) ≤ √c₁ * exp (-β * L) := by
    rw [← Real.sqrt_sq (exp_pos (-β * L)).le, ← Real.sqrt_mul hc₁0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hexp1 hc₁0)
  have ht2 : M * (2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
      exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * L)))) * volume.real S ≤ c₂ * exp (-β * L) := by
    rw [hc₂]
    calc _ = M * (2 * exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S *
          exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp2 (by positivity)
  calc _ ≤ √c₁ * exp (-β * L) + c₂ * exp (-β * L) := add_le_add ht1 ht2
    _ = (√c₁ + c₂) * exp (-β * L) := by ring

end LQGMetric
