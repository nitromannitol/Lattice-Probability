/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea6 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing

/-!
A process-level version of QuantumZipper's interior sup-moment chain
(`QuantumZipper/Proofs/LQG/AreaP3bMoment.lean`, `AreaP3bSup.lean`), with the free-boundary field
`innerS X z δ D R` replaced by an arbitrary jointly measurable process `U : ℕ → ℂ → Ω → ℝ` (the
"inner circle averages" `U k t ≈ Y_{2^{-k}}(t)`) satisfying, at every level `k ≥ k₀`, the Gaussian
hypotheses `TwoRadiusC.TRLHypC` of QZ's planar two-radius lemma for the pair
`(U k, U (k+1) − U k)`. With the rescaled masses

  `W_k = massU γ S δ k U = ∫_S (2^{-k}/δ)^{γ²/2} e^{γ U_k(t)} dt`

we get (copying the QZ proofs, with `innerS` replaced by `U`):

* `lintegral_massU_le`: `E W_k ≤ e^{γ²K/2} |S|` (QZ `lintegral_massFunC_inner_le`);
* `integral_abs_massU_step_le_rate`: `E|W_k − W_{k+1}| ≤ cRate γ K V · δ² e^{−β L_k}`
  (QZ `integral_abs_massFunC_step_le` and `integral_abs_massFunC_step_le_rate'`, via
  `TwoRadiusC.trlC_bound_area`);
* **`lintegral_iSup_massU_rpow_le`**: `E (sup_m W_{k₀+m})^p ≤ (e^{γ²K/2}|S|)^p +
  (cRate γ K V δ²)^p (1 − q)⁻¹` for `0 < p ≤ 1` (QZ `lintegral_iSup_massFunC_inner_rpow_le`).

Source: Duplantier–Sheffield, Invent. Math. 185 (2011), §3.2, (14)–(15) and Prop. 3.3; the proofs
are copied from the QZ files named above (from QuantumZipper), only the field
argument is abstracted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea6

open QuantumZipper TwoRadiusC AreaP3b

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- rescaled area density `(2^{-k}/δ)^{γ²/2} e^{γ U_k(t)}` (QZ `FinArea.wDensC`) -/
def wDensU (γ δ : ℝ) (k : ℕ) (U : ℕ → ℂ → Ω → ℝ) (t : ℂ) (ω : Ω) : ℝ :=
  (radius k / δ) ^ (γ ^ 2 / 2) * exp (γ * U k t ω)

/-- rescaled area mass `W_k(S)` (QZ `FinArea.massFunC`) -/
def massU (γ : ℝ) (S : Set ℂ) (δ : ℝ) (k : ℕ) (U : ℕ → ℂ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t in S, ENNReal.ofReal (wDensU γ δ k U t ω)

/-- the two-radius hypotheses at level `k` -/
def LevelHyp (P : Measure Ω) (S : Set ℂ) (δ K : ℝ) (U : ℕ → ℂ → Ω → ℝ) (k : ℕ) : Prop :=
  radius k ≤ δ ∧ ∃ v : ℂ → ℝ≥0, TRLHypC P S (2 * radius k) K (log 2)
    (fun _ => 1 / 2 * log (δ / radius k)) v (fun _ => (log 2).toNNReal) (U k)
    (fun t ω => U (k + 1) t ω - U k t ω)

omit [MeasurableSpace Ω] in
theorem wDensU_nonneg (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (U : ℕ → ℂ → Ω → ℝ) (t : ℂ)
    (ω : Ω) : 0 ≤ wDensU γ δ k U t ω :=
  mul_nonneg (rpow_nonneg (div_nonneg (radius_pos k).le hδ.le) _) (exp_pos _).le

theorem measurable_massU (γ : ℝ) (S : Set ℂ) (δ : ℝ) (k : ℕ) {U : ℕ → ℂ → Ω → ℝ}
    (hU : Measurable (fun p : ℂ × Ω => U k p.1 p.2)) :
    Measurable (massU γ S δ k U) := by
  have hm : Measurable (fun q : Ω × ℂ => ENNReal.ofReal (wDensU γ δ k U q.2 q.1)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((hU.comp measurable_swap).const_mul γ).exp)
  exact hm.lintegral_prod_right'

variable [IsProbabilityMeasure P] {S : Set ℂ} {δ K : ℝ} {U : ℕ → ℂ → Ω → ℝ}

/-- One-point first moment of the rescaled density (QZ `integral_wDensC_inner_le`). -/
theorem integral_wDensU_le (γ : ℝ) (hδ : 0 < δ) {k : ℕ} (h : LevelHyp P S δ K U k) {w : ℂ}
    (hw : w ∈ S) :
    Integrable (fun ω => wDensU γ δ k U w ω) P ∧
      ∫ ω, wDensU γ δ k U w ω ∂P ≤ exp (γ ^ 2 / 2 * K) := by
  have hr := radius_pos k
  obtain ⟨hrδ, v, hT⟩ := h
  have hL := hT.lawU w hw
  have hi : Integrable (fun ω => exp (0 + γ * U k w ω)) P :=
    hL.integrable_fun_comp (TwoRadius.integrable_exp_mul_add_gaussianReal _ γ 0)
  simp only [zero_add] at hi
  refine ⟨hi.const_mul _, ?_⟩
  have h2 := TwoRadius.integral_exp_mul_add_gaussianReal (v w) γ 0
  simp only [zero_add] at h2
  have h3 : ∫ ω, exp (γ * U k w ω) ∂P = exp (v w * γ ^ 2 / 2) := by
    rw [← h2]; exact hL.integral_comp (f := fun x => exp (γ * x)) (by fun_prop)
  simp only [wDensU]
  rw [integral_const_mul, h3, rpow_def_of_pos (div_pos hr hδ), ← exp_add]
  apply exp_le_exp.2
  have hv := hT.varU w hw
  have hL0 : 0 ≤ log (δ / radius k) := log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  rw [log_div hr.ne' hδ.ne']
  rw [log_div hδ.ne' hr.ne'] at hv hL0
  have hg : 0 ≤ γ ^ 2 / 2 := by positivity
  nlinarith

/-- `E W_k(S) ≤ e^{γ²K/2} |S|` (QZ `lintegral_massFunC_inner_le`). -/
theorem lintegral_massU_le (γ : ℝ) (hδ : 0 < δ) {k : ℕ} (h : LevelHyp P S δ K U k) :
    ∫⁻ ω, massU γ S δ k U ω ∂P ≤ ENNReal.ofReal (exp (γ ^ 2 / 2 * K)) * volume S := by
  have hU := h.2.choose_spec.measU
  have hmeas : Measurable (fun q : Ω × ℂ => ENNReal.ofReal (wDensU γ δ k U q.2 q.1)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((hU.comp measurable_swap).const_mul γ).exp)
  simp only [massU]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ w in S, ∫⁻ ω, ENNReal.ofReal (wDensU γ δ k U w ω) ∂P
      ≤ ∫⁻ w in S, ENNReal.ofReal (exp (γ ^ 2 / 2 * K)) :=
        setLIntegral_mono measurable_const fun w hw => by
          obtain ⟨hi, hle⟩ := integral_wDensU_le γ hδ h hw
          rw [← ofReal_integral_eq_lintegral_ofReal hi
            (ae_of_all _ fun ω => wDensU_nonneg γ hδ k U w ω)]
          exact ENNReal.ofReal_le_ofReal hle
    _ = _ := setLIntegral_const _ _

theorem ae_massU_lt_top (γ : ℝ) (hδ : 0 < δ) (hSf : volume S < ∞) {k : ℕ}
    (h : LevelHyp P S δ K U k) : ∀ᵐ ω ∂P, massU γ S δ k U ω < ⊤ :=
  ae_lt_top (measurable_massU γ S δ k h.2.choose_spec.measU)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf.ne)
      (lintegral_massU_le γ hδ h))

theorem integrable_massU_toReal (γ : ℝ) (hδ : 0 < δ) (hSf : volume S < ∞) {k : ℕ}
    (h : LevelHyp P S δ K U k) : Integrable (fun ω => (massU γ S δ k U ω).toReal) P :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_massU γ S δ k h.2.choose_spec.measU).aemeasurable
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf.ne)
      (lintegral_massU_le γ hδ h))

omit [IsProbabilityMeasure P] in
/-- For a sample with finite mass, `W_k` is the Bochner integral of the density
(QZ `integrableOn_wDensC_of_lt_top`). -/
theorem integrableOn_wDensU_of_lt_top (γ : ℝ) (hδ : 0 < δ) (k : ℕ) {ω : Ω}
    (hm : Measurable fun t => U k t ω) (hx : massU γ S δ k U ω < ⊤) :
    IntegrableOn (fun t => wDensU γ δ k U t ω) S ∧
      ∫ t in S, wDensU γ δ k U t ω = (massU γ S δ k U ω).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict S] fun t => wDensU γ δ k U t ω :=
    ae_of_all _ fun t => wDensU_nonneg γ hδ k U t ω
  have hm' : Measurable (fun t : ℂ => wDensU γ δ k U t ω) :=
    measurable_const.mul ((hm.const_mul γ).exp)
  have hfi : HasFiniteIntegral (fun t : ℂ => wDensU γ δ k U t ω) (volume.restrict S) :=
    (hasFiniteIntegral_iff_ofReal hnn).2 (by simpa only [massU] using hx)
  refine ⟨⟨hm'.aestronglyMeasurable, hfi⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm'.aestronglyMeasurable]
  rfl

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The TRL density is the difference of consecutive rescaled densities (QZ `dC_inner_eq`). -/
theorem dC_eq_wDensU (γ : ℝ) (hδ : 0 < δ) (k : ℕ) (t : ℂ) (ω : Ω) :
    dC (2 * γ) (fun _ => (1 : ℝ)) (fun _ => 1 / 2 * log (δ / radius k))
        (fun _ => (log 2).toNNReal) (U k) (fun t ω => U (k + 1) t ω - U k t ω) t ω =
      wDensU γ δ k U t ω - wDensU γ δ (k + 1) U t ω := by
  have hr := radius_pos k
  have hlog2 : (0 : ℝ) ≤ log 2 := log_nonneg one_le_two
  simp only [dC, TwoRadius.tiltY, one_mul, wDensU]
  rw [Real.coe_toNNReal _ hlog2]
  set A := U k t ω
  set B := U (k + 1) t ω
  have e1 : (radius k / δ) ^ (γ ^ 2 / 2) * exp (γ * A) =
      exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (δ / radius k)) + 2 * γ / 2 * A) := by
    rw [rpow_def_of_pos (div_pos hr hδ), ← exp_add, log_div hr.ne' hδ.ne',
      log_div hδ.ne' hr.ne']
    congr 1; ring
  have e2 : (radius (k + 1) / δ) ^ (γ ^ 2 / 2) * exp (γ * B) =
      exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (δ / radius k)) + 2 * γ / 2 * A) *
        exp (-((2 * γ) ^ 2 / 8 * log 2) + 2 * γ / 2 * (B - A)) := by
    rw [AreaExist.aradius_succ, rpow_def_of_pos (div_pos (div_pos hr two_pos) hδ), ← exp_add,
      ← exp_add, log_div (div_pos hr two_pos).ne' hδ.ne', log_div hr.ne' two_ne_zero,
      log_div hδ.ne' hr.ne']
    congr 1; ring
  rw [e1, e2]
  ring

/-- **Two-radius step bound** for the rescaled masses (QZ `integral_abs_massFunC_step_le`). -/
theorem integral_abs_massU_step_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hδ : 0 < δ)
    (hS : MeasurableSet S) (hSf : volume S < ∞) {k : ℕ} (h : LevelHyp P S δ K U k)
    (h1 : LevelHyp P S δ K U (k + 1)) :
    ∫ ω, |(massU γ S δ k U ω).toReal - (massU γ S δ (k + 1) U ω).toReal| ∂P
      ≤ √(((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
            (exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 * K / 2) *
            exp ((2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) *
              (1 / 2 * log (δ / radius k))))) *
            (π * (2 * radius k) ^ 2 * volume.real S))
        + 2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
            exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * log (δ / radius k)))) * volume.real S := by
  have hr := radius_pos k
  have hT := h.2.choose_spec
  have hb := trlC_bound_area (P := P) hγ hγ2 (δ := 2 * radius k) (M := 1)
    (Lc := 1 / 2 * log (δ / radius k)) (f := fun _ => (1 : ℝ)) (by positivity) hS hSf
    measurable_const (fun _ => by simp) hT
  have hEq : ∫ ω, |(massU γ S δ k U ω).toReal - (massU γ S δ (k + 1) U ω).toReal| ∂P =
      ∫ ω, |∫ t in S, dC (2 * γ) (fun _ => (1 : ℝ)) (fun _ => 1 / 2 * log (δ / radius k))
        (fun _ => (log 2).toNNReal) (U k) (fun t ω => U (k + 1) t ω - U k t ω) t ω| ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_massU_lt_top γ hδ hSf h, ae_massU_lt_top γ hδ hSf h1] with ω h1' h2'
    have hm0 : Measurable fun t => U k t ω :=
      hT.measU.comp (measurable_id.prodMk measurable_const)
    have hm1 : Measurable fun t => U (k + 1) t ω :=
      h1.2.choose_spec.measU.comp (measurable_id.prodMk measurable_const)
    have i1 := integrableOn_wDensU_of_lt_top γ hδ k hm0 h1'
    have i2 := integrableOn_wDensU_of_lt_top γ hδ (k + 1) hm1 h2'
    have hkey : (massU γ S δ k U ω).toReal - (massU γ S δ (k + 1) U ω).toReal =
        ∫ t in S, dC (2 * γ) (fun _ => (1 : ℝ)) (fun _ => 1 / 2 * log (δ / radius k))
          (fun _ => (log 2).toNNReal) (U k) (fun t ω => U (k + 1) t ω - U k t ω) t ω := by
      rw [← i1.2, ← i2.2, ← integral_sub i1.1 i2.1]
      exact setIntegral_congr_fun hS fun t _ => (dC_eq_wDensU γ hδ k t ω).symm
    exact congrArg abs hkey
  refine hEq.trans_le ?_
  refine hb.trans ?_
  simp only [one_pow, one_mul]
  exact le_rfl

end ConeArea6
end MatedCRTHarmonic.MoTPort
