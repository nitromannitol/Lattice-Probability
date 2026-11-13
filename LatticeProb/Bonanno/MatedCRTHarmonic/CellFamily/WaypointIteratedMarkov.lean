/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.WaypointIteratedMarkov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.StrongMarkov

/-!
# Iterating the strong Markov lower bound over successive target hits

`iteratedStrongMarkovLower` is the reusable finite-step product bound. A step is restarted at the
previous stopping time, its success event is measurable at its own stopping time, and success records
both a finite next hit and the next entrance state. The stopping times can be successive hitting times
or finite composites built with `Markov.thenTime`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic.Markov

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The time of the `n`th restart, where `δ n` is the next step's stopping time on the restarted path. -/
noncomputable def iteratedRestartTime (δ : ℕ → (ℕ → S) → ℕ∞) :
    ℕ → (ℕ → S) → ℕ∞
  | 0 => 0
  | n + 1 => thenTime (iteratedRestartTime δ n) (δ n)

/-- The event that the chain starts at `x` and succeeds on its first `n` restarted steps. -/
def iteratedSuccessPrefix (x : S) (δ : ℕ → (ℕ → S) → ℕ∞)
    (B : ℕ → Set (ℕ → S)) : ℕ → Set (ℕ → S)
  | 0 => {ω | ω 0 = x}
  | n + 1 => iteratedSuccessPrefix x δ B n ∩
      {ω | iteratedRestartTime δ n ω < ⊤} ∩
      stopShift (iteratedRestartTime δ n) ⁻¹' B n

private theorem isStoppingTime_zeroPath {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) (fun _ => (0 : ℕ∞)) := by
  intro n
  have hset : {ω : ℕ → S | (fun _ => (0 : ℕ∞)) ω ≤ (n : ℕ∞)} = Set.univ := by
    ext ω
    simp
  change MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n]
    {ω : ℕ → S | (fun _ => (0 : ℕ∞)) ω ≤ (n : ℕ∞)}
  rw [hset]
  exact MeasurableSet.univ

private theorem measurableSet_startAt {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] (x : S) :
    MeasurableSet {ω : ℕ → S | ω 0 = x} := by
  exact (measurableSet_singleton x).preimage
    (measurable_pi_apply 0)

private theorem startAt_measurableAt_zero {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] (x : S) :
    MeasurableSet[(isStoppingTime_zeroPath (S := S)).measurableSpace]
      {ω : ℕ → S | ω 0 = x} := by
  apply measurableSet_stopping_of_forall_eq (isStoppingTime_zeroPath (S := S))
    (measurableSet_startAt x)
  intro ω ω' hfinite hagree hω
  have h0 : (0 : ℕ∞) ≤ (fun _ : ℕ → S => (0 : ℕ∞)) ω := le_rfl
  exact (hagree 0 h0).symm.trans hω

private theorem iteratedRestartTime_isStoppingTime
    (δ : ℕ → (ℕ → S) → ℕ∞)
    (hδ : ∀ n, IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) (δ n)) :
    ∀ n, IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S))
      (iteratedRestartTime δ n) := by
  intro n
  induction n with
  | zero => exact isStoppingTime_zeroPath
  | succ n ih =>
      exact isStoppingTime_thenTime ih (hδ n)

/-- **Iterated strong Markov lower bound.** Suppose each local success event `B n` occurs with
probability at least `p n` from every entrance state in `A n`; each success is visible at its step's
stopping time, ends at an entrance state in `A (n+1)`, and entails that step's stopping time is finite.
Then the probability that the chain starts at `x` and succeeds on its first `n` restarted steps is at
least the product of the step bounds. -/
theorem iteratedStrongMarkovLower
    (κ : Kernel S S) [IsMarkovKernel κ] (x : S)
    (δ : ℕ → (ℕ → S) → ℕ∞) (B : ℕ → Set (ℕ → S))
    (A : ℕ → Set S) (p : ℕ → ℝ≥0∞)
    (hA0 : x ∈ A 0)
    (hδ : ∀ n, IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) (δ n))
    (hB : ∀ n, MeasurableSet[(hδ n).measurableSpace] (B n))
    (hBfinite : ∀ n ω, ω ∈ B n → δ n ω < ⊤)
    (hBentry : ∀ n ω, ω ∈ B n →
      stopState (δ n) ω ∈ A (n + 1))
    (hprob : ∀ n y, y ∈ A n → p n ≤ chainLaw κ y (B n)) :
    ∀ n, (∏ i ∈ Finset.range n, p i) ≤
      chainLaw κ x (iteratedSuccessPrefix x δ B n) := by
  let τ := iteratedRestartTime δ
  let F := iteratedSuccessPrefix x δ B
  have hτ : ∀ n, IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) (τ n) :=
    iteratedRestartTime_isStoppingTime δ hδ
  have hFmeas : ∀ n, MeasurableSet[(hτ n).measurableSpace] (F n) := by
    intro n
    induction n with
    | zero =>
        exact startAt_measurableAt_zero x
    | succ n ih =>
        let hnext := isStoppingTime_thenTime (hτ n) (hδ n)
        have hprev : MeasurableSet[hnext.measurableSpace] (F n) :=
          measurableSpace_le_thenTime (hτ n) (hδ n) (F n) ih
        have hstep : MeasurableSet[hnext.measurableSpace]
            ({ω | τ n ω < ⊤} ∩ stopShift (τ n) ⁻¹' B n) :=
          measurableSet_thenTime_of_stopShift (hτ n) (hδ n) (hB n)
        have hstep' : MeasurableSet[hnext.measurableSpace]
            ({ω | iteratedRestartTime δ n ω < ⊤} ∩
              stopShift (iteratedRestartTime δ n) ⁻¹' B n) := by
          simpa only [τ] using hstep
        simp only [F, iteratedSuccessPrefix]
        change MeasurableSet[hnext.measurableSpace]
          (iteratedSuccessPrefix x δ B n ∩
            {ω | iteratedRestartTime δ n ω < ⊤} ∩
              stopShift (iteratedRestartTime δ n) ⁻¹' B n)
        rw [Set.inter_assoc]
        exact hprev.inter hstep'
  have hFfinite : ∀ n ω, ω ∈ F n → τ n ω < ⊤ := by
    intro n
    induction n with
    | zero =>
        intro ω hω
        simp [τ, iteratedRestartTime]
    | succ n ih =>
        intro ω hω
        simp only [F, iteratedSuccessPrefix, Set.mem_inter_iff] at hω
        rcases hω with ⟨⟨_, hprevFinite⟩, hgood⟩
        have hδfinite := hBfinite n (stopShift (τ n) ω) hgood
        exact (thenTime_lt_top_iff (σ := τ n) (τ := δ n) (ω := ω)).2
          ⟨hprevFinite, hδfinite⟩
  have hFentry : ∀ n ω, ω ∈ F n → stopState (τ n) ω ∈ A n := by
    intro n
    induction n with
    | zero =>
        intro ω hω
        have hstart : ω 0 = x := hω
        simpa [τ, iteratedRestartTime, stopState] using hstart ▸ hA0
    | succ n ih =>
        intro ω hω
        simp only [F, iteratedSuccessPrefix, Set.mem_inter_iff] at hω
        have hgood : stopShift (τ n) ω ∈ B n := hω.2
        have hfinite : τ (n + 1) ω < ⊤ := by
          exact hFfinite (n + 1) ω hω
        change stopState (thenTime (τ n) (δ n)) ω ∈ A (n + 1)
        rw [stopState_thenTime (σ := τ n) (τ := δ n)
          (lt_top_iff_ne_top.mp (by simpa [τ, iteratedRestartTime] using hfinite))]
        exact hBentry n (stopShift (τ n) ω) hgood
  have hbase : (1 : ℝ≥0∞) ≤ chainLaw κ x (F 0) := by
    have hstart := chainLaw_ae_start κ x
    have hnull : chainLaw κ x (F 0)ᶜ = 0 := by
      have heq : (F 0)ᶜ = {ω | ω 0 ≠ x} := by
        ext ω
        simp [F, iteratedSuccessPrefix]
      rw [ae_iff] at hstart
      rw [heq]
      exact hstart
    have hsum := measure_add_measure_compl (μ := chainLaw κ x) (measurableSet_startAt x)
    have hsum' : chainLaw κ x (F 0) + chainLaw κ x (F 0)ᶜ = 1 := by
      simpa [F, iteratedSuccessPrefix, add_comm] using hsum
    rw [hnull, add_zero] at hsum'
    exact hsum'.ge
  have hstepBound (n : ℕ) :
      p n * chainLaw κ x (F n) ≤ chainLaw κ x (F (n + 1)) := by
    have hlocal : ∀ ω ∈ F n ∩ {ω | τ n ω < ⊤},
        p n ≤ chainLaw κ (stopState (τ n) ω) (B n) := by
      intro ω hω
      exact hprob n _ (hFentry n ω hω.1)
    have hSM := le_chainLaw_inter_stopShift_preimage κ x (τ := τ n) (hτ n)
      (F := F n) (hFmeas n) (B := B n)
      (measurableSet_of_measurableSet_stopping (hδ n) (hB n)) hlocal
    have hset : F n ∩ {ω | τ n ω < ⊤} = F n := by
      ext ω
      constructor
      · exact fun h => h.1
      · intro hω
        exact ⟨hω, hFfinite n ω hω⟩
    rw [hset] at hSM
    have hnext : F (n + 1) = F n ∩ stopShift (τ n) ⁻¹' B n := by
      ext ω
      simp only [F, iteratedSuccessPrefix, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hprev, _⟩, hgood⟩
        exact ⟨hprev, hgood⟩
      · rintro ⟨hprev, hgood⟩
        exact ⟨⟨hprev, hFfinite n ω hprev⟩, hgood⟩
    rw [hnext]
    exact hSM
  intro n
  induction n with
  | zero => simpa [F] using hbase
  | succ n ih =>
      rw [Finset.prod_range_succ]
      calc
        (∏ i ∈ Finset.range n, p i) * p n ≤
            chainLaw κ x (F n) * p n :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = p n * chainLaw κ x (F n) := mul_comm _ _
        _ ≤ chainLaw κ x (F (n + 1)) := hstepBound n

end MatedCRTHarmonic.CellFamily

