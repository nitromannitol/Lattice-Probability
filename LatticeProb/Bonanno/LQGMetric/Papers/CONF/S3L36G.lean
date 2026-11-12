/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36G at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36F
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# CONF Lemma 3.6, Step 3: property B from the one-step bounds

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 3 (C:1425–1432).

`conf36_propB_of_steps`: let `F n` (`= G̃^n`) be events, `N` (`= ⌊η log ε⁻¹⌋`) an `ℱ`-measurable
`ℕ`-valued random variable and `G := {∃ n ∈ [1, N], F n}`. If on each `ℱ`-event `{N = j}` the
one-step bounds (3.24) hold in integrated form, `𝔭 P(A ∩ ⋂_{m ≤ n} F_mᶜ) ≤ P(A ∩ ⋂_{m ≤ n} F_mᶜ ∩
F_{n+1})` for `A ∈ ℱ`, `A ⊆ {N = j}`, `n < j`, then a.s. `P[G | ℱ] ≥ 1 − (1 − 𝔭)^N` (CONF
C:1428–1430: "iterate (3.24) `⌊η log ε⁻¹⌋` times").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.CONF

variable {Ω : Type} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω}

/-- the conditional bound localized to an `ℱ`-event `C` -/
theorem conf36_condExp_ge_on [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {G C : Set Ω} (hG : MeasurableSet[m0] G) (hC : MeasurableSet[m] C) {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ A, MeasurableSet[m] A → A ⊆ C → P (A ∩ Gᶜ) ≤ ENNReal.ofReal q * P A) :
    ∀ᵐ ω ∂P, ω ∈ C → 1 - q ≤ (P[G.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  have hC0 : MeasurableSet[m0] C := hm C hC
  have hG' : MeasurableSet[m0] (G ∪ Cᶜ) := hG.union hC0.compl
  have h1 := conf36_condExp_ge hm hG' hq fun A hA => by
    have e : A ∩ (G ∪ Cᶜ)ᶜ = (A ∩ C) ∩ Gᶜ := by ext ω; simp; tauto
    rw [e]
    exact (h _ (hA.inter hC) inter_subset_right).trans
      (mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have hi : ∀ {S : Set Ω}, MeasurableSet[m0] S → Integrable (S.indicator (fun _ => (1 : ℝ))) P :=
    fun hS => (integrable_const (1 : ℝ)).indicator hS
  have e1 := condExp_indicator (hi hG') hC
  have e2 := condExp_indicator (hi hG) hC
  have e3 : C.indicator ((G ∪ Cᶜ).indicator (fun _ => (1 : ℝ))) =
      C.indicator (G.indicator (fun _ => (1 : ℝ))) := by
    ext ω
    by_cases hω : ω ∈ C
    · simp only [indicator_of_mem hω]
      by_cases hg : ω ∈ G
      · simp [hg]
      · simp [hg, hω]
    · simp [hω]
  rw [e3] at e1
  filter_upwards [h1, e1, e2] with ω hω1 hω2 hω3 hωC
  have := hω2.symm.trans hω3
  simp only [indicator_of_mem hωC] at this
  rw [← this]; exact hω1

/-- **CONF Lemma 3.6, property B from the one-step bounds** (C:1425–1432) -/
theorem conf36_propB_of_steps [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet[m0] (F n)) {N : Ω → ℕ} (hN : Measurable[m] N)
    {𝔭 : ℝ} (h𝔭 : 0 < 𝔭) (h𝔭1 : 𝔭 < 1)
    (hstep : ∀ j : ℕ, ∀ n < j, ∀ A, MeasurableSet[m] A → A ⊆ {ω | N ω = j} →
      ENNReal.ofReal 𝔭 * P (conf36Avoid F A n) ≤ P (conf36Avoid F A n ∩ F (n + 1))) :
    ∀ᵐ ω ∂P, 1 - (1 - 𝔭) ^ N ω ≤
      (P[{ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F n}.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  set G := {ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F n} with hGdef
  have hNm0 : Measurable[m0] N := hN.mono hm le_rfl
  have hG : MeasurableSet[m0] G := by
    have : G = ⋃ n, ({ω | 1 ≤ n ∧ n ≤ N ω} ∩ F n) := by ext ω; simp [hGdef]; tauto
    rw [this]
    refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ (hF n)
    by_cases h1 : 1 ≤ n
    · have : {ω | 1 ≤ n ∧ n ≤ N ω} = N ⁻¹' Ici n := by ext ω; simp [h1]
      rw [this]; exact hNm0 measurableSet_Ici
    · have : {ω | 1 ≤ n ∧ n ≤ N ω} = ∅ := by ext ω; simp [h1]
      rw [this]; exact @MeasurableSet.empty Ω m0
  have hj : ∀ j : ℕ, ∀ᵐ ω ∂P, ω ∈ {ω | N ω = j} → 1 - (1 - 𝔭) ^ j ≤
      (P[G.indicator (fun _ => (1 : ℝ)) | m]) ω := by
    intro j
    have hCj : MeasurableSet[m] {ω | N ω = j} := by
      show MeasurableSet[m] (N ⁻¹' {j}); exact hN (measurableSet_singleton j)
    refine conf36_condExp_ge_on hm hG hCj (pow_nonneg (by linarith) j) fun A hA hAC => ?_
    have e : A ∩ Gᶜ = conf36Avoid F A j := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, hGdef, mem_ofPred_eq, conf36Avoid, not_exists,
        not_and]
      constructor
      · rintro ⟨hA', h'⟩
        exact ⟨hA', fun n h1 h2 hn => h' n h1 (by rw [hAC hA']; exact h2) hn⟩
      · rintro ⟨hA', h'⟩
        exact ⟨hA', fun n h1 h2 hn => h' n h1 (by rw [← hAC hA']; exact h2) hn⟩
    rw [e]
    have hA0 : MeasurableSet[m0] A := hm A hA
    refine (conf36_iter hF hA0 (fun n hn => hstep j n hn A hA hAC) j le_rfl).trans_eq ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h𝔭.le, ← ENNReal.ofReal_pow (by linarith)]
  rw [← ae_all_iff] at hj
  filter_upwards [hj] with ω hω
  exact hω (N ω) rfl

end LQGMetric.CONF
