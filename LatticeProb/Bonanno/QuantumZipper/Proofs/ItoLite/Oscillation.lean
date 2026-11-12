/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.ItoLite.Oscillation at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# BM-OSC: moments of the Brownian oscillation

* `BMOsc.expGrid_submartingale` : along a monotone grid of times, `k ↦ exp (θ (B (u k) - B t))`
  is a submartingale for the natural filtration.
* `BMOsc.tail_upper` : the exponential maximal inequality on a finite grid (Doob's weak maximal
  inequality, `maximal_ineq`).
* `bmOsc_tail` : `P (a < bmOsc B t s) ≤ 2 exp (-a² / (2 s))` (dyadic grids and continuity).
* `bm_osc_moment`, `integrable_bmOsc_pow` : `E[bmOsc B t s ^ p] ≤ C_p s^{p/2}` (layer cake and the
  Gamma integral).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal NNReal

namespace QuantumZipper

namespace BMOsc

set_option linter.unusedSectionVars false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- Generalised IL-1: a past-measurable weight against a measurable function of an increment. -/
theorem integral_mul_comp_incr (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    {t s : ℝ≥0} {ξ : Ω → ℝ} (hξ : Measurable[bmFiltration B t] ξ) {g : ℝ → ℝ}
    (hg : Measurable g) :
    ∫ ω, ξ ω * g (B (t + s) ω - B t ω) ∂P = (∫ ω, ξ ω ∂P) * ∫ x, g x ∂gaussianReal 0 s := by
  set F : Ω → ℝ≥0 → ℝ := fun ω u => B (t + u) ω - B t ω
  set Y : Ω → ℝ := fun ω => g (B (t + s) ω - B t ω)
  have hind : IndepFun F (fun ω (r : Set.Iic t) => B r ω) P := hB.indepFun_shift t
  have hY : Measurable[MeasurableSpace.comap F MeasurableSpace.pi] Y := by
    have h0 : Measurable (fun f : ℝ≥0 → ℝ => g (f s)) := hg.comp (measurable_pi_apply s)
    exact h0.comp (comap_measurable F)
  have hξY : IndepFun ξ Y P := by
    rw [IndepFun_iff_Indep] at hind ⊢
    exact (indep_of_indep_of_le hind hY.comap_le
      (hξ.comap_le.trans (bmFiltration_le_comap_restrict t))).symm
  have hξm : Measurable ξ := hξ.mono (bmFiltration_le hBm t) le_rfl
  have hYm : Measurable Y := hg.comp ((hBm _).sub (hBm _))
  have h1 := hξY.integral_mul_eq_mul_integral hξm.aestronglyMeasurable hYm.aestronglyMeasurable
  simp only [Pi.mul_apply] at h1
  rw [h1]
  congr 1
  exact ((hB.shift t).hasLaw_eval s).integral_comp (f := g) hg.aestronglyMeasurable

theorem measurable_bmFiltration {r u : ℝ≥0} (h : r ≤ u) : Measurable[bmFiltration B u] (B r) :=
  Measurable.of_comap_le
    (le_iSup₂ (f := fun s (_ : s ≤ u) => (inferInstance : MeasurableSpace ℝ).comap (B s)) r h)

theorem bmFiltration_mono {r u : ℝ≥0} (h : r ≤ u) : bmFiltration B r ≤ bmFiltration B u :=
  iSup₂_le fun s hs =>
    le_iSup₂ (f := fun s (_ : s ≤ u) => (inferInstance : MeasurableSpace ℝ).comap (B s)) s
      (hs.trans h)

/-- The natural filtration sampled along a monotone sequence of times. -/
def gridFiltration (hBm : ∀ r, Measurable (B r)) (u : ℕ → ℝ≥0) (hu : Monotone u) :
    Filtration ℕ mΩ :=
  ⟨fun k => bmFiltration B (u k), fun _ _ hij => bmFiltration_mono (hu hij),
    fun _ => bmFiltration_le hBm _⟩

theorem integral_exp_gaussianReal (v : ℝ≥0) (θ : ℝ) :
    ∫ x, rexp (θ * x) ∂gaussianReal 0 v = rexp (v * θ ^ 2 / 2) := by
  have := mgf_gaussianReal (HasLaw.id : HasLaw id (gaussianReal 0 v) (gaussianReal 0 v)) θ
  simpa [mgf] using this

theorem integrable_exp_incr (hB : IsPreBrownianReal B P) {t r : ℝ≥0} (h : t ≤ r) (θ : ℝ) :
    Integrable (fun ω => rexp (θ * (B r ω - B t ω))) P := by
  have hlaw := (hB.shift t).hasLaw_eval (r - t)
  rw [add_tsub_cancel_of_le h] at hlaw
  exact hlaw.integrable_comp (f := fun x => rexp (θ * x)) (integrable_exp_mul_gaussianReal θ)

theorem integral_exp_incr (hB : IsPreBrownianReal B P) {t r : ℝ≥0} (h : t ≤ r) (θ : ℝ) :
    ∫ ω, rexp (θ * (B r ω - B t ω)) ∂P = rexp (((r - t : ℝ≥0) : ℝ) * θ ^ 2 / 2) := by
  have hlaw := (hB.shift t).hasLaw_eval (r - t)
  have h2 := hlaw.integral_comp (f := fun x => rexp (θ * x)) (by fun_prop)
  rw [integral_exp_gaussianReal] at h2
  rw [← h2]
  simp only [Function.comp_def, add_tsub_cancel_of_le h]

/-- Along a monotone grid of times after `t`, `k ↦ exp (θ (B (u k) - B t))` is a submartingale. -/
theorem expGrid_submartingale (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    {t : ℝ≥0} {u : ℕ → ℝ≥0} (hu : Monotone u) (ht : t ≤ u 0) (θ : ℝ) :
    Submartingale (fun k ω => rexp (θ * (B (u k) ω - B t ω))) (gridFiltration hBm u hu) P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have htk : ∀ k, t ≤ u k := fun k => ht.trans (hu (Nat.zero_le k))
  have hmeas : ∀ k, Measurable[bmFiltration B (u k)] (fun ω => rexp (θ * (B (u k) ω - B t ω))) :=
    fun k => ((measurable_bmFiltration le_rfl).sub (measurable_bmFiltration (htk k))).const_mul
      θ |>.exp
  refine submartingale_of_setIntegral_le (fun k => (hmeas k).stronglyMeasurable)
    (fun k => integrable_exp_incr hB (htk k) θ) ?_
  intro i j hij A hA
  have hAm : MeasurableSet A := (gridFiltration hBm u hu).le i A hA
  have hξ : Measurable[bmFiltration B (u i)]
      (A.indicator fun ω => rexp (θ * (B (u i) ω - B t ω))) := (hmeas i).indicator hA
  have key := integral_mul_comp_incr hB hBm (s := u j - u i) hξ (g := fun x => rexp (θ * x))
    (by fun_prop)
  rw [add_tsub_cancel_of_le (hu hij), integral_exp_gaussianReal] at key
  rw [← integral_indicator hAm, ← integral_indicator hAm]
  have hpt : (fun ω => A.indicator (fun ω => rexp (θ * (B (u j) ω - B t ω))) ω) =
      fun ω => A.indicator (fun ω => rexp (θ * (B (u i) ω - B t ω))) ω *
        rexp (θ * (B (u j) ω - B (u i) ω)) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, ← Real.exp_add]
      ring_nf
    · simp [indicator_of_notMem hω]
  rw [hpt, key]
  exact le_mul_of_one_le_right
    (integral_nonneg fun ω => indicator_nonneg (fun _ _ => (exp_pos _).le) _)
    (one_le_exp (by positivity))

/-- The exponential maximal inequality on a finite monotone grid. -/
theorem tail_upper (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    {t : ℝ≥0} {u : ℕ → ℝ≥0} (hu : Monotone u) (ht : t ≤ u 0) (n : ℕ) (a : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    P {ω | ∃ k ≤ n, a ≤ B (u k) ω - B t ω} ≤
      ENNReal.ofReal (rexp (((u n - t : ℝ≥0) : ℝ) * θ ^ 2 / 2 - θ * a)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have htn : t ≤ u n := ht.trans (hu (Nat.zero_le n))
  have hsub := expGrid_submartingale hB hBm hu ht θ
  have hmax := maximal_ineq hsub (fun k ω => (exp_pos _).le) (ε := (rexp (θ * a)).toNNReal) n
  rw [Real.coe_toNNReal _ (exp_pos _).le] at hmax
  set S := {ω | rexp (θ * a) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => rexp (θ * (B (u k) ω - B t ω))}
  have hsubset : {ω | ∃ k ≤ n, a ≤ B (u k) ω - B t ω} ⊆ S := by
    rintro ω ⟨k, hk, hak⟩
    exact le_trans (exp_le_exp.2 (mul_le_mul_of_nonneg_left hak hθ.le))
      (Finset.le_sup' (fun k => rexp (θ * (B (u k) ω - B t ω)))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  have hle : ∫ ω in S, rexp (θ * (B (u n) ω - B t ω)) ∂P ≤
      rexp (((u n - t : ℝ≥0) : ℝ) * θ ^ 2 / 2) := by
    rw [← integral_exp_incr hB htn θ]
    exact setIntegral_le_integral (integrable_exp_incr hB htn θ)
      (Eventually.of_forall fun ω => (exp_pos _).le)
  have h2 : ENNReal.ofReal (rexp (θ * a)) * P S ≤
      ENNReal.ofReal (rexp (((u n - t : ℝ≥0) : ℝ) * θ ^ 2 / 2)) :=
    hmax.trans (ENNReal.ofReal_le_ofReal hle)
  have hS : P S ≤ ENNReal.ofReal (rexp (((u n - t : ℝ≥0) : ℝ) * θ ^ 2 / 2)) /
      ENNReal.ofReal (rexp (θ * a)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [exp_pos])) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact h2
  rw [← ENNReal.ofReal_div_of_pos (exp_pos _), ← Real.exp_sub] at hS
  exact (measure_mono hsubset).trans hS

/-- Two-sided exponential maximal inequality on a finite monotone grid. -/
theorem tail_abs (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    {t : ℝ≥0} {u : ℕ → ℝ≥0} (hu : Monotone u) (ht : t ≤ u 0) (n : ℕ) {a s : ℝ} (ha : 0 < a)
    (hs : 0 < s) (hV : ((u n - t : ℝ≥0) : ℝ) ≤ s) :
    P {ω | ∃ k ≤ n, a < |B (u k) ω - B t ω|} ≤ ENNReal.ofReal (2 * rexp (-(a ^ 2) / (2 * s))) := by
  have hθ : 0 < a / s := div_pos ha hs
  have hexp : rexp (((u n - t : ℝ≥0) : ℝ) * (a / s) ^ 2 / 2 - a / s * a) ≤
      rexp (-(a ^ 2) / (2 * s)) := by
    refine exp_le_exp.2 ?_
    have h1 : ((u n - t : ℝ≥0) : ℝ) * (a / s) ^ 2 / 2 ≤ s * (a / s) ^ 2 / 2 := by gcongr
    have h2 : s * (a / s) ^ 2 / 2 - a / s * a = -(a ^ 2) / (2 * s) := by field_simp; ring
    linarith
  have hup := (tail_upper hB hBm hu ht n a hθ).trans (ENNReal.ofReal_le_ofReal hexp)
  have hlo := (tail_upper (B := -B) hB.neg (fun r => (hBm r).neg) hu ht n a hθ).trans
    (ENNReal.ofReal_le_ofReal hexp)
  have hsub : {ω | ∃ k ≤ n, a < |B (u k) ω - B t ω|} ⊆
      {ω | ∃ k ≤ n, a ≤ B (u k) ω - B t ω} ∪ {ω | ∃ k ≤ n, a ≤ (-B) (u k) ω - (-B) t ω} := by
    rintro ω ⟨k, hk, h⟩
    rcases lt_abs.1 h with h | h
    · exact Or.inl ⟨k, hk, h.le⟩
    · refine Or.inr ⟨k, hk, ?_⟩
      simp only [Pi.neg_apply]
      linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hup hlo).trans ?_))
  rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le, ← two_mul]

end BMOsc

end QuantumZipper
