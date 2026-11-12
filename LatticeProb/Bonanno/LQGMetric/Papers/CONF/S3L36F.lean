/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36F at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# CONF Lemma 3.6, Step 3: the iteration and the rate

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 3 (C:1425–1432):
"we can iterate (3.24) `⌊η log ε⁻¹⌋` times to get that the conditional probability given
`(𝓑^•_τ, h|_{𝓑^•_τ})` that `G̃^n` does not occur for every `n ∈ [1, η log ε⁻¹]` is at most
`(1 − 𝔭)^{⌊η log ε⁻¹⌋}`. That is, a.s. `P[G^ε_x | 𝓑^•_τ, h|_{𝓑^•_τ}] ≥ 1 − C₀ε^α` for `α`
slightly smaller than `η log(1/(1−𝔭))`."

* `conf36_iter` : the iteration, in integrated form: if for each `n < N` and `A ∈ ℱ`,
  `𝔭 · P(A ∩ ⋂_{m ≤ n} (G̃^m)ᶜ) ≤ P(A ∩ ⋂_{m ≤ n} (G̃^m)ᶜ ∩ G̃^{n+1})`, then
  `P(A ∩ ⋂_{m ≤ N} (G̃^m)ᶜ) ≤ (1 − 𝔭)^N P(A)`;
* `conf36_condExp_ge` : an integrated bound `P(A ∩ Gᶜ) ≤ q P(A)` (`A ∈ ℱ`) gives
  `P[G | ℱ] ≥ 1 − q` a.s.;
* `conf36_rate` : `(1 − 𝔭)^{⌊η log ε⁻¹⌋} ≤ C₀ ε^α` with `α = η log(1/(1 − 𝔭))` (CONF's exponent
  itself, not "slightly smaller") and `C₀ = 2/(1 − 𝔭)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.CONF

variable {Ω : Type} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω}

/-- `ω` avoids `F 1, …, F n` -/
def conf36Avoid (F : ℕ → Set Ω) (A : Set Ω) (n : ℕ) : Set Ω :=
  A ∩ {ω | ∀ m, 1 ≤ m → m ≤ n → ω ∉ F m}

theorem conf36Avoid_succ (F : ℕ → Set Ω) (A : Set Ω) (n : ℕ) :
    conf36Avoid F A (n + 1) = conf36Avoid F A n \ (conf36Avoid F A n ∩ F (n + 1)) := by
  ext ω
  simp only [conf36Avoid, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, not_and]
  constructor
  · rintro ⟨hA, h⟩
    exact ⟨⟨hA, fun m h1 h2 => h m h1 (h2.trans (Nat.le_succ n))⟩,
      fun _ => h (n + 1) (Nat.succ_pos n) le_rfl⟩
  · rintro ⟨⟨hA, h⟩, h'⟩
    refine ⟨hA, fun m h1 h2 => ?_⟩
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · exact h m h1 (Nat.lt_succ_iff.1 hm)
    · rw [le_antisymm h2 hm]; exact h' ⟨hA, h⟩

/-- **The iteration of CONF C:1425–1430** (integrated form) -/
theorem conf36Avoid_meas {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet (F n)) {A : Set Ω}
    (hA : MeasurableSet A) (n : ℕ) : MeasurableSet (conf36Avoid F A n) := by
  have : {ω | ∀ m, 1 ≤ m → m ≤ n → ω ∉ F m} = ⋂ m, ⋂ (_ : 1 ≤ m), ⋂ (_ : m ≤ n), (F m)ᶜ := by
    ext ω; simp
  unfold conf36Avoid
  rw [this]
  exact hA.inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => (hF m).compl)

theorem conf36_iter [IsFiniteMeasure P] {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet (F n))
    {A : Set Ω} (hA : MeasurableSet A) {𝔭 : ℝ≥0∞} {N : ℕ}
    (hstep : ∀ n < N, 𝔭 * P (conf36Avoid F A n) ≤ P (conf36Avoid F A n ∩ F (n + 1))) :
    ∀ n ≤ N, P (conf36Avoid F A n) ≤ (1 - 𝔭) ^ n * P A := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [pow_zero, one_mul]
    exact measure_mono inter_subset_left
  | succ n ih =>
    intro hn
    rw [conf36Avoid_succ]
    have hsub : conf36Avoid F A n ∩ F (n + 1) ⊆ conf36Avoid F A n := inter_subset_left
    calc P (conf36Avoid F A n \ (conf36Avoid F A n ∩ F (n + 1)))
        = P (conf36Avoid F A n) - P (conf36Avoid F A n ∩ F (n + 1)) :=
          measure_sdiff hsub ((conf36Avoid_meas hF hA n).inter (hF _)).nullMeasurableSet
            (measure_ne_top _ _)
      _ ≤ P (conf36Avoid F A n) - 𝔭 * P (conf36Avoid F A n) := tsub_le_tsub_left (hstep n hn) _
      _ = (1 - 𝔭) * P (conf36Avoid F A n) := by
          rw [ENNReal.sub_mul (fun _ _ => measure_ne_top _ _), one_mul]
      _ ≤ (1 - 𝔭) * ((1 - 𝔭) ^ n * P A) := by gcongr; exact ih (Nat.le_of_succ_le hn)
      _ = (1 - 𝔭) ^ (n + 1) * P A := by rw [pow_succ]; ring

/-- from an integrated bound on `P(A ∩ Gᶜ)` to the conditional probability bound -/
theorem conf36_condExp_ge [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {G : Set Ω} (hG : MeasurableSet[m0] G) {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ A, MeasurableSet[m] A → P (A ∩ Gᶜ) ≤ ENNReal.ofReal q * P A) :
    ∀ᵐ ω ∂P, 1 - q ≤ (P[G.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  have hint : Integrable (G.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hG
  have hfm : StronglyMeasurable[m] (fun _ : Ω => 1 - q) := stronglyMeasurable_const
  refine ae_of_ae_trim hm (ae_le_of_forall_setIntegral_le ((integrable_const _).trim hm hfm)
    (integrable_condExp.trim hm stronglyMeasurable_condExp) fun s hs _ => ?_)
  rw [← setIntegral_trim hm hfm hs, ← setIntegral_trim hm stronglyMeasurable_condExp hs,
    setIntegral_condExp hm hint hs, setIntegral_const, setIntegral_indicator hG,
    setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one]
  have hs0 : MeasurableSet[m0] s := hm s hs
  have h1 := h s hs
  have hsplit : P.real (s ∩ G) + P.real (s ∩ Gᶜ) = P.real s := by
    rw [← sdiff_eq]; exact measureReal_inter_add_sdiff (s := s) hG
  have h2 : P.real (s ∩ Gᶜ) ≤ q * P.real s := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq] at this
  nlinarith

/-- **the rate of CONF C:1432**: `(1 − 𝔭)^{⌊η log ε⁻¹⌋} ≤ C₀ε^α` -/
theorem conf36_rate {𝔭 η : ℝ} (h𝔭 : 0 < 𝔭) (h𝔭1 : 𝔭 < 1) (hη : 0 < η) :
    ∃ α C₀ : ℝ, 0 < α ∧ 1 < C₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      (1 - 𝔭) ^ ⌊η * Real.log ε⁻¹⌋₊ ≤ C₀ * ε ^ α := by
  have hq : 0 < 1 - 𝔭 := by linarith
  have hlog : Real.log (1 - 𝔭) < 0 := Real.log_neg hq (by linarith)
  refine ⟨-η * Real.log (1 - 𝔭), 2 / (1 - 𝔭), by nlinarith, ?_, fun ε hε => ?_⟩
  · rw [lt_div_iff₀ hq]; linarith
  have hx : 0 ≤ η * Real.log ε⁻¹ :=
    mul_nonneg hη.le (Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε.1, hε.2.le⟩))
  set N := ⌊η * Real.log ε⁻¹⌋₊
  have hN : η * Real.log ε⁻¹ - 1 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one (η * Real.log ε⁻¹); linarith
  have e1 : (1 - 𝔭) ^ N = Real.exp (Real.log (1 - 𝔭) * N) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq]
  have e2 : ε ^ (-η * Real.log (1 - 𝔭)) = Real.exp (Real.log ε * (-η * Real.log (1 - 𝔭))) :=
    Real.rpow_def_of_pos hε.1 _
  have e3 : Real.log ε⁻¹ = - Real.log ε := Real.log_inv ε
  have hle : Real.log (1 - 𝔭) * N ≤
      Real.log ε * (-η * Real.log (1 - 𝔭)) + (- Real.log (1 - 𝔭)) := by
    rw [e3] at hN; nlinarith
  rw [e1, e2]
  calc Real.exp (Real.log (1 - 𝔭) * N)
      ≤ Real.exp (Real.log ε * (-η * Real.log (1 - 𝔭)) + (- Real.log (1 - 𝔭))) :=
        Real.exp_le_exp.2 hle
    _ = (1 - 𝔭)⁻¹ * Real.exp (Real.log ε * (-η * Real.log (1 - 𝔭))) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hq, mul_comm]
    _ ≤ 2 / (1 - 𝔭) * Real.exp (Real.log ε * (-η * Real.log (1 - 𝔭))) := by
        gcongr
        rw [div_eq_mul_inv]; linarith [inv_pos.2 hq]

end LQGMetric.CONF
