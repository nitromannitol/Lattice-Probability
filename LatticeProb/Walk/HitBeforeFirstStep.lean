import LatticeProb.Prob.InfinitePiSplit

/-! First-step decomposition for a walk driven by independent instructions.
The ordered hitting event observes time zero and excludes a simultaneous visit
of the forbidden set and the target set. -/

namespace LatticeProb.DrivenWalk

open MeasureTheory

variable {α δ : Type*}

/-- Position after a finite number of instructions, starting at `x`. -/
def position (step : α → δ → α) (x : α) (ω : ℕ → δ) : ℕ → α
  | 0 => x
  | n + 1 => step (position step x ω n) (ω n)

/-- A walk starts at its prescribed initial point. -/
@[simp] theorem position_zero (step : α → δ → α) (x : α) (ω : ℕ → δ) :
    position step x ω 0 = x := rfl

/-- The next position applies the next instruction to the current position. -/
@[simp] theorem position_succ (step : α → δ → α) (x : α) (ω : ℕ → δ) (n : ℕ) :
    position step x ω (n + 1) = step (position step x ω n) (ω n) := rfl

/-- Removing the first instruction starts the remaining walk one step later. -/
theorem position_consNat_succ (step : α → δ → α) (x : α) (u : δ)
    (ω : ℕ → δ) (n : ℕ) :
    position step x (consNat u ω) (n + 1) = position step (step x u) ω n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [position_succ, consNat_succ, ih, position_succ]

/-- A target visit before any forbidden visit, with both times allowed to be zero. -/
def hitBefore (step : α → δ → α) (A C : Set α) (x : α) : Set (ℕ → δ) :=
  {ω | ∃ n, position step x ω n ∈ C ∧ ∀ m ≤ n, position step x ω m ∉ A}

/-- A walk starting in the forbidden set cannot hit the target first. -/
theorem hitBefore_eq_empty (step : α → δ → α) (A C : Set α) (x : α) (hx : x ∈ A) :
    hitBefore step A C x = ∅ := by
  ext ω
  constructor
  · rintro ⟨n, _, hn⟩
    exact hn 0 (Nat.zero_le n) hx
  · exact False.elim

/-- A start in the target but outside the forbidden set is already a valid hit. -/
theorem hitBefore_eq_univ (step : α → δ → α) (A C : Set α) (x : α)
    (hxA : x ∉ A) (hxC : x ∈ C) : hitBefore step A C x = Set.univ := by
  ext ω
  constructor
  · intro _; trivial
  · intro _
    refine ⟨0, hxC, ?_⟩
    intro m hm
    obtain rfl := Nat.eq_zero_of_le_zero hm
    exact hxA

/-- Away from both boundary sets, an ordered hit depends on the walk after its first step. -/
theorem consNat_mem_hitBefore_iff (step : α → δ → α) (A C : Set α) (x : α)
    (hxA : x ∉ A) (hxC : x ∉ C) (u : δ) (ω : ℕ → δ) :
    consNat u ω ∈ hitBefore step A C x ↔ ω ∈ hitBefore step A C (step x u) := by
  constructor
  · rintro ⟨n, hnC, hnA⟩
    cases n with
    | zero => exact (hxC hnC).elim
    | succ n =>
      refine ⟨n, ?_, ?_⟩
      · exact (position_consNat_succ step x u ω n) ▸ hnC
      · intro m hm
        have h := hnA (m + 1) (Nat.succ_le_succ hm)
        exact (position_consNat_succ step x u ω m) ▸ h
  · rintro ⟨n, hnC, hnA⟩
    refine ⟨n + 1, ?_, ?_⟩
    · rw [position_consNat_succ]; exact hnC
    · intro m hm
      cases m with
      | zero => exact hxA
      | succ m =>
        rw [position_consNat_succ]
        exact hnA m (Nat.le_of_succ_le_succ hm)

section Measurable

variable [MeasurableSpace α] [MeasurableSpace δ]

/-- Every fixed-time position is a measurable function of the instructions. -/
theorem measurable_position (step : α → δ → α)
    (hstep : Measurable (Function.uncurry step)) (x : α) (n : ℕ) :
    Measurable (fun ω => position step x ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hstep.comp (ih.prodMk (measurable_pi_apply n))

/-- Ordered hitting is measurable for measurable step maps and boundary sets. -/
theorem measurableSet_hitBefore (step : α → δ → α)
    (hstep : Measurable (Function.uncurry step)) (A C : Set α)
    (hA : MeasurableSet A) (hC : MeasurableSet C) (x : α) :
    MeasurableSet (hitBefore step A C x) := by
  have hmA (n : ℕ) : MeasurableSet {ω | position step x ω n ∉ A} :=
    ((measurable_position step hstep x n) hA).compl
  have hmC (n : ℕ) : MeasurableSet {ω | position step x ω n ∈ C} :=
    (measurable_position step hstep x n) hC
  simp only [hitBefore, Set.setOf_exists, Set.setOf_and, Set.setOf_forall]
  exact MeasurableSet.iUnion fun n => (hmC n).inter
    (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => hmA m)

/-- **First-step decomposition.** The probability of an ordered hit is the average of the probabilities after
one instruction, when the initial point belongs to neither boundary set. -/
theorem measure_hitBefore_eq_lintegral (μ : Measure δ) [IsProbabilityMeasure μ]
    (step : α → δ → α) (hstep : Measurable (Function.uncurry step))
    (A C : Set α) (hA : MeasurableSet A) (hC : MeasurableSet C) (x : α)
    (hxA : x ∉ A) (hxC : x ∉ C) :
    (Measure.infinitePi fun _ : ℕ => μ) (hitBefore step A C x) =
      ∫⁻ u, (Measure.infinitePi fun _ : ℕ => μ) (hitBefore step A C (step x u)) ∂μ := by
  have hE := measurableSet_hitBefore step hstep A C hA hC x
  have hI : Measurable ((hitBefore step A C x).indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hE
  have h := lintegral_infinitePi_nat_head_tail μ _ hI
  have he (u : δ) :
      (fun ω => (hitBefore step A C x).indicator (fun _ => (1 : ENNReal)) (consNat u ω)) =
        (hitBefore step A C (step x u)).indicator (fun _ => (1 : ENNReal)) := by
    funext ω
    by_cases hm : consNat u ω ∈ hitBefore step A C x
    · have ht := (consNat_mem_hitBefore_iff step A C x hxA hxC u ω).mp hm
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem ht]
    · have ht : ω ∉ hitBefore step A C (step x u) := fun ht =>
        hm ((consNat_mem_hitBefore_iff step A C x hxA hxC u ω).mpr ht)
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem ht]
  simp only [he] at h
  rw [lintegral_indicator_fun_one hE] at h
  simp_rw [lintegral_indicator_fun_one (measurableSet_hitBefore step hstep A C hA hC _)] at h
  exact h

/-- The first-step equation for finitely many instructions with arbitrary weights. -/
theorem measure_hitBefore_eq_sum [Fintype δ] [MeasurableSingletonClass δ]
    (μ : Measure δ) [IsProbabilityMeasure μ]
    (step : α → δ → α) (hstep : Measurable (Function.uncurry step))
    (A C : Set α) (hA : MeasurableSet A) (hC : MeasurableSet C) (x : α)
    (hxA : x ∉ A) (hxC : x ∉ C) :
    (Measure.infinitePi fun _ : ℕ => μ) (hitBefore step A C x) =
      ∑ u, (Measure.infinitePi fun _ : ℕ => μ) (hitBefore step A C (step x u)) * μ {u} := by
  rw [measure_hitBefore_eq_lintegral μ step hstep A C hA hC x hxA hxC,
    lintegral_fintype]

end Measurable
end LatticeProb.DrivenWalk
