import LatticeProb.Prob.JumpChain.PositionFdd
import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Markov property of jump-chain positions

The killed finite-dimensional position laws give the Markov identity on finite cylinders.
Measure uniqueness extends it to the raw natural sigma algebra, and countable singleton
sums give the integral and conditional lower expectation identities. Survival events are
naturally measurable by rational observations and local constancy on the right.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal ENNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S]

/-- The raw natural sigma algebra of the position process up to time `t`. -/
@[reducible] def naturalSigma (t : ℝ≥0) : MeasurableSpace (RegularHistory S) :=
  ⨆ s ≤ t, MeasurableSpace.comap (fun h ↦ h.position s) inferInstance

/-- The natural sigma algebra is contained in the ambient history sigma algebra. -/
theorem naturalSigma_le (t : ℝ≥0) :
    naturalSigma (S := S) t ≤ (inferInstance : MeasurableSpace (RegularHistory S)) := by
  refine iSup_le fun s ↦ iSup_le fun _ ↦ ?_
  exact (RegularHistory.measurable_position s).comap_le

/-- Position observations before `t` are measurable in the raw natural sigma algebra. -/
theorem measurable_position_naturalSigma {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[naturalSigma (S := S) t] (fun h ↦ h.position s) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le s (le_iSup_of_le hst le_rfl)

/-- The raw natural sigma algebras increase with time. -/
theorem naturalSigma_mono : Monotone (naturalSigma (S := S)) := by
  intro s t hst
  refine iSup_le fun r ↦ iSup_le fun hrs ↦ ?_
  exact le_iSup_of_le r (le_iSup_of_le (hrs.trans hst) le_rfl)

omit [MeasurableSpace S] in
/-- Survival is equivalent to survival at the endpoint and at rational observation times. -/
theorem position_mem_iff_rational (h : RegularHistory S) (U : Set S) (t : ℝ≥0) :
    (∀ s ≤ t, h.position s ∈ U) ↔
      h.position t ∈ U ∧ ∀ q : ℚ, (q : ℝ).toNNReal ≤ t →
        h.position (q : ℝ).toNNReal ∈ U := by
  constructor
  · intro hh
    exact ⟨hh t le_rfl, fun q hq ↦ hh _ hq⟩
  · rintro ⟨ht, hq⟩ s hst
    rcases hst.eq_or_lt with rfl | hst
    · exact ht
    · have hlt : (s : ℝ) < min (t : ℝ)
          (jumpTime h.val (h.ringCount s + 1)) :=
        lt_min hst (h.lt_jumpTime_ringCount_succ s)
      obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hlt
      have hq0 : 0 ≤ (q : ℝ) := s.coe_nonneg.trans hsq.le
      have hcoe : ((q : ℝ).toNNReal : ℝ) = q := Real.coe_toNNReal _ hq0
      have hqt' : (q : ℝ).toNNReal ≤ t := by
        exact_mod_cast (hcoe ▸ (lt_min_iff.mp hqt).1.le)
      have heq : h.position (q : ℝ).toNNReal = h.position s := by
        apply h.position_eq_of_interval
        · rw [hcoe]
          exact (h.jumpTime_ringCount_le s).trans hsq.le
        · rw [hcoe]
          exact (lt_min_iff.mp hqt).2
      rw [← heq]
      exact hq q hqt'

variable [Countable S] [MeasurableSingletonClass S]

/-- Survival up to `t` is measurable in the raw natural sigma algebra at `t`. -/
theorem measurableSet_survival_naturalSigma (U : Set S) (t : ℝ≥0) :
    MeasurableSet[naturalSigma (S := S) t]
      {h : RegularHistory S | ∀ s ≤ t, h.position s ∈ U} := by
  have hU : MeasurableSet U := (Set.to_countable U).measurableSet
  simp_rw [position_mem_iff_rational]
  refine (measurable_position_naturalSigma le_rfl hU).inter ?_
  have hq : MeasurableSet[naturalSigma (S := S) t]
      (⋂ q : ℚ, ⋂ _ : (q : ℝ).toNNReal ≤ t,
        {h : RegularHistory S | h.position (q : ℝ).toNNReal ∈ U}) :=
    MeasurableSet.iInter fun q : ℚ ↦ MeasurableSet.iInter
      fun hqt : (q : ℝ).toNNReal ≤ t ↦ measurable_position_naturalSigma hqt hU
  convert hq using 1
  ext h
  simp only [mem_iInter, mem_setOf_eq]
  rfl

/-- Any state function evaluated at the current position is naturally measurable. -/
theorem measurable_current_state_function (t : ℝ≥0) (f : S → ℝ≥0∞) :
    Measurable[naturalSigma (S := S) t] (fun h ↦ f (h.position t)) :=
  (measurable_of_countable f).comp (measurable_position_naturalSigma le_rfl)

/-- Finite cylinders specified by a history, together with the full history space. -/
private def positionCylinders (t : ℝ≥0) : Set (Set (RegularHistory S)) :=
  {A | A = univ ∨ ∃ a : Finset ℝ≥0, (∀ s ∈ a, s ≤ t) ∧
    ∃ h₀ : RegularHistory S, A = {h | ∀ s ∈ a, h.position s = h₀.position s}}

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
/-- Finite position cylinders form a pi system. -/
private theorem isPiSystem_positionCylinders (t : ℝ≥0) :
    IsPiSystem (positionCylinders (S := S) t) := by
  classical
  rintro A (rfl | ⟨a, ha, h₀, rfl⟩) B (rfl | ⟨b, hb, h₁, rfl⟩) hne
  · exact Or.inl (univ_inter univ)
  · exact Or.inr ⟨b, hb, h₁, univ_inter _⟩
  · exact Or.inr ⟨a, ha, h₀, inter_univ _⟩
  · obtain ⟨h₂, h₂a, h₂b⟩ := hne
    refine Or.inr ⟨a ∪ b, ?_, h₂, ?_⟩
    · intro s hs
      exact (Finset.mem_union.mp hs).elim (ha s) (hb s)
    · ext h
      simp only [mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨hA, hB⟩ s hs
        rcases Finset.mem_union.mp hs with hs | hs
        · exact (hA s hs).trans (h₂a s hs).symm
        · exact (hB s hs).trans (h₂b s hs).symm
      · intro hh
        exact ⟨fun s hs ↦ (hh s (Finset.mem_union_left b hs)).trans (h₂a s hs),
          fun s hs ↦ (hh s (Finset.mem_union_right a hs)).trans (h₂b s hs)⟩

/-- Finite singleton cylinders generate the raw natural sigma algebra. -/
private theorem naturalSigma_eq_generateFrom (t : ℝ≥0) :
    naturalSigma (S := S) t = MeasurableSpace.generateFrom (positionCylinders t) := by
  classical
  apply le_antisymm
  · refine iSup_le fun s ↦ iSup_le fun hst ↦ ?_
    rintro A ⟨U, _, rfl⟩
    have heq : (fun h : RegularHistory S ↦ h.position s) ⁻¹' U =
        ⋃ y : U, {h | h.position s = y.val} := by
      ext h
      simp only [mem_preimage, mem_iUnion, mem_setOf_eq, Subtype.exists]
      exact ⟨fun hh ↦ ⟨h.position s, hh, rfl⟩, fun ⟨y, hy, heq⟩ ↦ heq ▸ hy⟩
    rw [heq]
    apply MeasurableSet.iUnion
    intro y
    by_cases hne : ({h : RegularHistory S | h.position s = y.val}).Nonempty
    · obtain ⟨h₀, hh₀⟩ := hne
      change h₀.position s = y.val at hh₀
      apply MeasurableSpace.measurableSet_generateFrom
      refine Or.inr ⟨{s}, ?_, h₀, ?_⟩
      · simpa only [Finset.mem_singleton, forall_eq] using hst
      · ext h
        simp only [mem_setOf_eq, Finset.mem_singleton, forall_eq, hh₀]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact @MeasurableSet.empty _ (MeasurableSpace.generateFrom (positionCylinders t))
  · apply MeasurableSpace.generateFrom_le
    rintro A (rfl | ⟨a, ha, h₀, rfl⟩)
    · exact MeasurableSet.univ
    · simp only [setOf_forall]
      exact MeasurableSet.biInter (Finset.countable_toSet a) fun s hs ↦
        (measurable_position_naturalSigma (ha s hs)) (measurableSet_singleton _)

/-- Appending a value above the last observation preserves monotonicity. -/
private theorem monotone_snoc {α : Type*} [Preorder α] {n : ℕ}
    (f : Fin (n + 1) → α) (hf : Monotone f) (a : α) (ha : f (Fin.last n) ≤ a) :
    Monotone (Fin.snoc f a) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.succ_last, Fin.snoc_last,
      Fin.snoc_castSucc] using ha
  · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using
      hf (Fin.castSucc_le_succ j)

/-- Appending one observation factors a killed sorted cylinder by its last killed kernel. -/
theorem regularLaw_killed_position_fdd_append (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (k : ℕ) (t : Fin (k + 2) → ℝ≥0)
    (ht : Monotone t) (ht0 : t 0 = 0) (x : Fin (k + 2) → S) (u : ℝ≥0) (y : S) :
    rates.regularLaw μ {h |
      ((∀ i : Fin (k + 2), 0 < i → h.position (t i) = x i) ∧
        h.position (t (Fin.last (k + 1)) + u) = y) ∧
      ∀ s ≤ t (Fin.last (k + 1)) + u, h.position s ∈ U} =
    rates.regularLaw μ {h |
      (∀ i : Fin (k + 2), 0 < i → h.position (t i) = x i) ∧
      ∀ s ≤ t (Fin.last (k + 1)), h.position s ∈ U} *
      ENNReal.ofReal (rates.killedKernel U u (x (Fin.last (k + 1))) y) := by
  classical
  let T : Fin (k + 3) → ℝ≥0 := Fin.snoc t (t (Fin.last (k + 1)) + u)
  let Z : Fin (k + 3) → S := Fin.snoc x y
  have hT : Monotone T := monotone_snoc t ht _ (le_add_of_nonneg_right (show 0 ≤ u from zero_le))
  have hT0 : T 0 = 0 := by simpa only [T, Fin.snoc_apply_zero] using ht0
  have hevent : {h : RegularHistory S |
      ((∀ i : Fin (k + 2), 0 < i → h.position (t i) = x i) ∧
        h.position (t (Fin.last (k + 1)) + u) = y) ∧
      ∀ s ≤ t (Fin.last (k + 1)) + u, h.position s ∈ U} =
      {h | (∀ i : Fin (k + 3), 0 < i → h.position (T i) = Z i) ∧
        ∀ s ≤ T (Fin.last (k + 2)), h.position s ∈ U} := by
    ext h
    simp only [mem_setOf_eq, T, Z, Fin.snoc_last]
    constructor
    · rintro ⟨⟨hx, hy⟩, hu⟩
      refine ⟨?_, hu⟩
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · intro _
        simpa only [Fin.snoc_last] using hy
      · intro hj
        simpa only [Fin.snoc_castSucc] using hx j (by exact_mod_cast hj)
    · rintro ⟨hx, hu⟩
      refine ⟨⟨?_, ?_⟩, hu⟩
      · intro i hi
        simpa only [Fin.snoc_castSucc] using hx i.castSucc (by exact_mod_cast hi)
      · simpa only [Fin.snoc_last] using hx (Fin.last (k + 2)) Fin.last_pos'
  rw [hevent, rates.regularLaw_killed_position_fdd μ U (k + 2) T hT hT0 Z,
    rates.regularLaw_killed_position_fdd μ U (k + 1) t ht ht0 x,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x₀
  rw [Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  have hupdate : Function.update Z 0 x₀ = Fin.snoc (Function.update x 0 x₀) y := by
    simpa only [Z, Fin.castSucc_zero] using
      (Fin.snoc_update (α := fun _ : Fin (k + 3) ↦ S) y x 0 x₀).symm
  rw [hupdate]
  have hlast : Function.update x 0 x₀ (Fin.last (k + 1)) = x (Fin.last (k + 1)) :=
    Function.update_of_ne (Fin.ne_of_gt Fin.last_pos') _ _
  simp only [T, ← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.succ_last,
    Fin.snoc_last, hlast, add_tsub_cancel_left]

/-- Adding a zero observation before a sorted nonnegative tuple preserves monotonicity. -/
private theorem monotone_cons_zero {n : ℕ} (f : Fin n → ℝ≥0) (hf : Monotone f) :
    Monotone (Fin.cons 0 f) := by
  intro i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · intro j _
    simp only [Fin.cons_zero]
    exact zero_le
  · intro j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · intro hij
      exact (not_le_of_gt i.succ_pos hij).elim
    · intro hij
      simpa only [Fin.cons_succ] using hf (Fin.succ_le_succ_iff.mp hij)

/-- A finite set of past observations, with a leading zero and the current endpoint. -/
private def cylinderTimes (a : Finset ℝ≥0) (t : ℝ≥0) : Fin (a.card + 2) → ℝ≥0 :=
  Fin.snoc (Fin.cons 0 (a.orderEmbOfFin rfl)) t

/-- The finite observation tuple is sorted when its times are at most the endpoint. -/
private theorem monotone_cylinderTimes (a : Finset ℝ≥0) (t : ℝ≥0)
    (ha : ∀ s ∈ a, s ≤ t) : Monotone (cylinderTimes a t) := by
  apply monotone_snoc _ (monotone_cons_zero _ (a.orderEmbOfFin rfl).monotone)
  refine Fin.cases ?_ (fun i ↦ ?_) (Fin.last a.card)
  · simp only [Fin.cons_zero]
    exact zero_le
  · simp only [Fin.cons_succ]
    exact ha _ (a.orderEmbOfFin_mem rfl i)

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
/-- Positive-index observations in the tuple are exactly the finite cylinder and endpoint. -/
private theorem cylinderTimes_observations (a : Finset ℝ≥0) (t : ℝ≥0)
    (h h₀ : RegularHistory S) :
    (∀ i : Fin (a.card + 2), 0 < i →
      h.position (cylinderTimes a t i) = h₀.position (cylinderTimes a t i)) ↔
      (∀ s ∈ a, h.position s = h₀.position s) ∧ h.position t = h₀.position t := by
  unfold cylinderTimes
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_pos_iff,
    Fin.last_pos', true_implies]
  rw [Fin.forall_fin_succ]
  simp only [lt_self_iff_false, false_implies, Fin.cons_succ, Fin.succ_pos,
    true_implies, true_and]
  constructor
  · rintro ⟨hh, ht⟩
    refine ⟨?_, ht⟩
    intro s hs
    obtain ⟨i, hi⟩ := (a.orderIsoOfFin rfl).surjective ⟨s, hs⟩
    have heq : a.orderEmbOfFin rfl i = s := congrArg Subtype.val hi
    simpa only [heq] using hh i
  · rintro ⟨hh, ht⟩
    exact ⟨fun i ↦ hh _ (a.orderEmbOfFin_mem rfl i), ht⟩

/-- A finite cylinder with its endpoint fixed has the killed one-step factorization. -/
private theorem killed_cylinder_factor (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (t u : ℝ≥0)
    (a : Finset ℝ≥0) (ha : ∀ s ∈ a, s ≤ t) (h₀ : RegularHistory S) (y : S) :
    rates.regularLaw μ {h |
      (((∀ s ∈ a, h.position s = h₀.position s) ∧ h.position t = h₀.position t) ∧
        h.position (t + u) = y) ∧ ∀ s ≤ t + u, h.position s ∈ U} =
    rates.regularLaw μ {h |
      ((∀ s ∈ a, h.position s = h₀.position s) ∧ h.position t = h₀.position t) ∧
        ∀ s ≤ t, h.position s ∈ U} *
      ENNReal.ofReal (rates.killedKernel U u (h₀.position t) y) := by
  have h := rates.regularLaw_killed_position_fdd_append μ U a.card
    (cylinderTimes a t) (monotone_cylinderTimes a t ha)
    (by simp only [cylinderTimes, Fin.snoc_apply_zero, Fin.cons_zero])
    (fun i ↦ h₀.position (cylinderTimes a t i)) u y
  simp_rw [cylinderTimes_observations] at h
  simpa only [cylinderTimes, Fin.snoc_last] using h

/-- Agreement on finite cylinders extends to the raw natural sigma algebra. -/
private theorem measure_eq_on_naturalSigma (t : ℝ≥0)
    (ν₁ ν₂ : Measure (RegularHistory S)) [IsFiniteMeasure ν₁]
    (hν : ∀ A ∈ positionCylinders t, ν₁ A = ν₂ A) :
    ∀ A, MeasurableSet[naturalSigma t] A → ν₁ A = ν₂ A := by
  let hm := naturalSigma_le (S := S) t
  have hmeas {A : Set (RegularHistory S)} (hA : A ∈ positionCylinders t) :
      MeasurableSet[naturalSigma t] A := by
    rw [naturalSigma_eq_generateFrom]
    exact MeasurableSpace.measurableSet_generateFrom hA
  have heq : ν₁.trim hm = ν₂.trim hm := by
    apply Measure.ext_of_generateFrom_of_iUnion (positionCylinders t) (fun _ : ℕ ↦ univ)
      (naturalSigma_eq_generateFrom t) (isPiSystem_positionCylinders t)
    · simp only [iUnion_const]
    · intro _
      exact Or.inl rfl
    · intro _
      exact measure_ne_top _ _
    · intro A hA
      simpa only [trim_measurableSet_eq hm (hmeas hA)] using hν A hA
  intro A hA
  have h := congrArg (fun ν : Measure[naturalSigma t] (RegularHistory S) ↦ ν A) heq
  simpa only [trim_measurableSet_eq hm hA] using h

/-- Fixed endpoint events satisfy the killed Markov identity on the raw natural sigma algebra. -/
private theorem killed_event_factor (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (t u : ℝ≥0) (x y : S)
    (A : Set (RegularHistory S)) (hA : MeasurableSet[naturalSigma t] A) :
    rates.regularLaw μ (A ∩ {h | h.position t = x ∧ h.position (t + u) = y ∧
      ∀ s ≤ t + u, h.position s ∈ U}) =
    rates.regularLaw μ (A ∩ {h | h.position t = x ∧
      ∀ s ≤ t, h.position s ∈ U}) *
      ENNReal.ofReal (rates.killedKernel U u x y) := by
  let ν := rates.regularLaw μ
  let E : Set (RegularHistory S) := {h | h.position t = x ∧
    h.position (t + u) = y ∧ ∀ s ≤ t + u, h.position s ∈ U}
  let F : Set (RegularHistory S) := {h | h.position t = x ∧
    ∀ s ≤ t, h.position s ∈ U}
  let c := ENNReal.ofReal (rates.killedKernel U u x y)
  have hbasic : ∀ B ∈ positionCylinders t,
      (ν.restrict E) B = (c • ν.restrict F) B := by
    intro B hB
    have hBm : MeasurableSet B := by
      apply naturalSigma_le t
      rw [naturalSigma_eq_generateFrom]
      exact MeasurableSpace.measurableSet_generateFrom hB
    rw [Measure.restrict_apply hBm, Measure.smul_apply, Measure.restrict_apply hBm,
      smul_eq_mul, mul_comm c]
    by_cases hne : (B ∩ {h : RegularHistory S | h.position t = x}).Nonempty
    · obtain ⟨h₁, h₁B, h₁t⟩ := hne
      change h₁.position t = x at h₁t
      obtain ⟨a, ha, hBa⟩ : ∃ a : Finset ℝ≥0, (∀ s ∈ a, s ≤ t) ∧
          B = {h | ∀ s ∈ a, h.position s = h₁.position s} := by
        rcases hB with rfl | ⟨a, ha, h₀, rfl⟩
        · exact ⟨∅, by simp, by ext; simp⟩
        · refine ⟨a, ha, ?_⟩
          ext h
          exact ⟨fun hh s hs ↦ (hh s hs).trans (h₁B s hs).symm,
            fun hh s hs ↦ (hh s hs).trans (h₁B s hs)⟩
      have hf := rates.killed_cylinder_factor μ U t u a ha h₁ y
      simpa only [ν, E, F, c, hBa, ← setOf_and, h₁t, and_assoc] using hf
    · have hBE : B ∩ E = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro h ⟨hB, hE⟩
        exact hne ⟨h, hB, hE.1⟩
      have hBF : B ∩ F = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro h ⟨hB, hF⟩
        exact hne ⟨h, hB, hF.1⟩
      simp only [hBE, hBF, measure_empty, zero_mul]
  have h := measure_eq_on_naturalSigma t (ν.restrict E) (c • ν.restrict F) hbasic A hA
  simpa only [Measure.restrict_apply (naturalSigma_le t A hA), Measure.smul_apply,
    smul_eq_mul, ν, E, F, c, mul_comm] using h

/-- Integrating a function of a countable observable sums its singleton fibers. -/
private theorem lintegral_comp_countable {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (X : Ω → S) (hX : Measurable X) (f : S → ℝ≥0∞) :
    ∫⁻ h, f (X h) ∂ν = ∑' x, f x * ν {h | X h = x} := by
  rw [← lintegral_map (measurable_of_countable f) hX, lintegral_countable']
  apply tsum_congr
  intro x
  rw [Measure.map_apply hX (measurableSet_singleton x)]
  rfl

/-- The killed Markov identity also allows dependence on the current position. -/
private theorem setLIntegral_markov_killed_pair (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (t u : ℝ≥0)
    (A : Set (RegularHistory S)) (hA : MeasurableSet[naturalSigma t] A)
    (g : S → S → ℝ≥0∞) :
    ∫⁻ h in A ∩ {h | ∀ s ≤ t + u, h.position s ∈ U},
      g (h.position t) (h.position (t + u)) ∂rates.regularLaw μ =
    ∫⁻ h in A ∩ {h | ∀ s ≤ t, h.position s ∈ U},
      (∑' y, ENNReal.ofReal (rates.killedKernel U u (h.position t) y) *
        g (h.position t) y) ∂rates.regularLaw μ := by
  let ν := rates.regularLaw μ
  let B : Set (RegularHistory S) := A ∩ {h | ∀ s ≤ t + u, h.position s ∈ U}
  let C : Set (RegularHistory S) := A ∩ {h | ∀ s ≤ t, h.position s ∈ U}
  have hmass (x y : S) :
      (ν.restrict B) {h | (h.position t, h.position (t + u)) = (x, y)} =
      (ν.restrict C) {h | h.position t = x} *
        ENNReal.ofReal (rates.killedKernel U u x y) := by
    rw [Measure.restrict_apply
      (measurableSet_eq_fun ((RegularHistory.measurable_position t).prodMk
        (RegularHistory.measurable_position (t + u))) measurable_const),
      Measure.restrict_apply
        (measurableSet_eq_fun (RegularHistory.measurable_position t) measurable_const)]
    have hB : {h : RegularHistory S | (h.position t, h.position (t + u)) = (x, y)} ∩ B =
        A ∩ {h | h.position t = x ∧ h.position (t + u) = y ∧
          ∀ s ≤ t + u, h.position s ∈ U} := by
      ext h
      simp only [B, mem_inter_iff, mem_setOf_eq, Prod.mk.injEq]
      tauto
    have hC : {h : RegularHistory S | h.position t = x} ∩ C =
        A ∩ {h | h.position t = x ∧ ∀ s ≤ t, h.position s ∈ U} := by
      ext h
      simp only [C, mem_inter_iff, mem_setOf_eq]
      tauto
    rw [hB, hC]
    exact rates.killed_event_factor μ U t u x y A hA
  change (∫⁻ h, g (h.position t) (h.position (t + u)) ∂ν.restrict B) =
    ∫⁻ h, (∑' y, ENNReal.ofReal (rates.killedKernel U u (h.position t) y) *
      g (h.position t) y) ∂ν.restrict C
  rw [lintegral_comp_countable (ν.restrict B)
    (fun h ↦ (h.position t, h.position (t + u)))
    ((RegularHistory.measurable_position t).prodMk
      (RegularHistory.measurable_position (t + u))) (fun p ↦ g p.1 p.2),
    ENNReal.tsum_prod', lintegral_comp_countable (ν.restrict C)
      (fun h ↦ h.position t) (RegularHistory.measurable_position t)
      (fun x : S ↦ ∑' y, ENNReal.ofReal (rates.killedKernel U u x y) * g x y)]
  simp_rw [hmass, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x
  apply tsum_congr
  intro y
  ac_rfl

/-- The position process has the Markov property for its raw natural sigma algebra. -/
theorem setLIntegral_markov (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t u : ℝ≥0)
    (A : Set (RegularHistory S)) (hA : MeasurableSet[naturalSigma t] A)
    (g : S → S → ℝ≥0∞) (_hg : Measurable (Function.uncurry g)) :
    ∫⁻ h in A, g (h.position t) (h.position (t + u)) ∂rates.regularLaw μ =
    ∫⁻ h in A, (∑' y, rates.transitionKernel u (h.position t) {y} *
      g (h.position t) y) ∂rates.regularLaw μ := by
  have hmass (x y : S) : ENNReal.ofReal ((rates.transitionKernel u x).real {y}) =
      rates.transitionKernel u x {y} := ofReal_measureReal (measure_ne_top _ _)
  simpa only [mem_univ, implies_true, forall_const, setOf_true, inter_univ,
    killedKernel_univ, hmass] using
      rates.setLIntegral_markov_killed_pair μ univ t u A hA g

/-- Conditional lower expectation of a future observation is its transition-kernel average. -/
theorem condLExp_markov (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t u : ℝ≥0) (g : S → S → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    (rates.regularLaw μ)⁻[fun h ↦ g (h.position t) (h.position (t + u)) |
      naturalSigma t] =ᵐ[rates.regularLaw μ]
      fun h ↦ ∑' y, rates.transitionKernel u (h.position t) {y} * g (h.position t) y := by
  apply Filter.EventuallyEq.symm
  refine ae_eq_condLExp (naturalSigma_le (S := S) t) (rates.regularLaw μ)
    (fun h ↦ g (h.position t) (h.position (t + u)))
    (measurable_current_state_function t
      (fun x : S ↦ ∑' y, rates.transitionKernel u x {y} * g x y)) ?_
  intro A hA
  exact (rates.setLIntegral_markov μ t u A hA g hg).symm

/-- Survival-weighted future observations have the killed transition-kernel average. -/
theorem setLIntegral_markov_killed (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (t u : ℝ≥0)
    (A : Set (RegularHistory S)) (hA : MeasurableSet[naturalSigma t] A)
    (g : S → ℝ≥0∞) (_hg : Measurable g) :
    ∫⁻ h in A ∩ {h | ∀ s ≤ t + u, h.position s ∈ U},
      g (h.position (t + u)) ∂rates.regularLaw μ =
    ∫⁻ h in A ∩ {h | ∀ s ≤ t, h.position s ∈ U},
      (∑' y, ENNReal.ofReal (rates.killedKernel U u (h.position t) y) * g y)
        ∂rates.regularLaw μ :=
  rates.setLIntegral_markov_killed_pair μ U t u A hA (fun _ y ↦ g y)

end

end LatticeProb.JumpChain.BoundedRates
