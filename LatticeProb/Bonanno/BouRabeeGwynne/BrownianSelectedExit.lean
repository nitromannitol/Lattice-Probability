/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSelectedExit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNextExit

/-! The next genuine exit for a domain selected from the observed history.
Returning `none` retains the previous time. The application supplies the
permanent termination flag as part of this observed choice. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def brownianSelectedNextExitTime (U : J → Set (Euc d)) (z : Euc d)
    (τ : BrownianPath d → ℝ≥0∞) (choice : BrownianPath d → Option J)
    (ω : BrownianPath d) : ℝ≥0∞ :=
  match choice ω with
  | none => τ ω
  | some j => brownianNextExitTime (U j) z τ ω

lemma le_brownianSelectedNextExitTime (U : J → Set (Euc d)) (z : Euc d)
    (τ : BrownianPath d → ℝ≥0∞) (choice : BrownianPath d → Option J) (ω : BrownianPath d) :
    τ ω ≤ brownianSelectedNextExitTime U z τ choice ω := by
  cases h : choice ω with
  | none => simp only [brownianSelectedNextExitTime, h, le_refl]
  | some j =>
    simpa only [brownianSelectedNextExitTime, h] using le_brownianNextExitTime (U j) z τ ω

lemma measurable_brownianSelectedNextExitTime (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d)
    {τ : BrownianPath d → ℝ≥0∞} (hτ : Measurable τ)
    {choice : BrownianPath d → Option J} (hchoice : Measurable choice) :
    Measurable (brownianSelectedNextExitTime U z τ choice) := by
  have hm : Measurable (fun p : Option J × BrownianPath d ↦
      match p.1 with
      | none => τ p.2
      | some j => brownianNextExitTime (U j) z τ p.2) := by
    apply measurable_from_prod_countable_right
    intro j
    cases j with
    | none => exact hτ
    | some j => exact measurable_brownianNextExitTime (hU j) z hτ
  exact hm.comp (hchoice.prodMk measurable_id)

theorem brownianSelectedNextExitTime_frozen (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : ∀ t ω, τ (frozenBrownianPath t ω) =
      if τ ω ≤ (t : ℝ≥0∞) then τ ω else ∞)
    {choice : BrownianPath d → Option J}
    (hchoice : ∀ (t : ℝ≥0) ω, τ ω ≤ (t : ℝ≥0∞) →
      choice (frozenBrownianPath t ω) = choice ω) (t : ℝ≥0) (ω : BrownianPath d) :
    brownianSelectedNextExitTime U z τ choice (frozenBrownianPath t ω) =
      if brownianSelectedNextExitTime U z τ choice ω ≤ (t : ℝ≥0∞)
        then brownianSelectedNextExitTime U z τ choice ω else ∞ := by
  classical
  by_cases ht : τ ω ≤ (t : ℝ≥0∞)
  · cases hc : choice ω with
    | none =>
      simp only [brownianSelectedNextExitTime, hchoice t ω ht, hc, hτ t ω, if_pos ht]
    | some j =>
      simpa only [brownianSelectedNextExitTime, hchoice t ω ht, hc] using
        brownianNextExitTime_frozen (hU j) z hτ t ω
  · have hnot : ¬ brownianSelectedNextExitTime U z τ choice ω ≤ (t : ℝ≥0∞) :=
      fun hle ↦ ht ((le_brownianSelectedNextExitTime U z τ choice ω).trans hle)
    rw [if_neg hnot]
    cases hc : choice (frozenBrownianPath t ω) with
    | none => simp only [brownianSelectedNextExitTime, hc, hτ t ω, if_neg ht]
    | some j =>
      simp only [brownianSelectedNextExitTime, hc, brownianNextExitTime,
        hτ t ω, if_neg ht, top_add]

theorem isStoppingTime_brownianSelectedNextExitTime (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d)
    {τ : BrownianPath d → ℝ≥0∞} (hmτ : Measurable τ)
    (hτ : ∀ t ω, τ (frozenBrownianPath t ω) =
      if τ ω ≤ (t : ℝ≥0∞) then τ ω else ∞)
    {choice : BrownianPath d → Option J} (hmchoice : Measurable choice)
    (hchoice : ∀ (t : ℝ≥0) ω, τ ω ≤ (t : ℝ≥0∞) →
      choice (frozenBrownianPath t ω) = choice ω) :
    IsStoppingTime (brownianNaturalFiltration d)
      (brownianSelectedNextExitTime U z τ choice) := by
  apply isStoppingTime_of_frozen_events
    (measurable_brownianSelectedNextExitTime U hU z hmτ hmchoice)
  intro t ω
  rw [brownianSelectedNextExitTime_frozen U hU z hτ hchoice]
  split_ifs <;> simp_all

theorem standardBrownianLaw_ae_finiteSelectedNextExit (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (z : Euc d)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞) (choice : BrownianPath d → Option J) :
    ∀ᵐ ω ∂μ, brownianSelectedNextExitTime U z τ choice ω ≠ ∞ := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, brownianNextExitTime (U j) z τ ω ≠ ∞ :=
    ae_all_iff.mpr (fun j ↦ standardBrownianLaw_ae_finiteNextExit hd hμ (hU j) (hUb j)
      z hτ hfinite)
  filter_upwards [hfinite, hall] with ω hω hnext
  cases hc : choice ω with
  | none => simpa only [brownianSelectedNextExitTime, hc] using hω
  | some j => simpa only [brownianSelectedNextExitTime, hc] using hnext j

end BouRabeeGwynne
