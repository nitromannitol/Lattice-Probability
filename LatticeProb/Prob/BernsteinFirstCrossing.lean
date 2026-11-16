import LatticeProb.Prob.BernsteinCrossTerm

/-!
# First crossings for bounded increments

Finite first-crossing and overshoot estimates for real-valued partial sums.
-/

namespace LatticeProb

/-- A bounded-increment path that exceeds twice a positive level has a first crossing of
that level, followed by an increment of at least the level minus the increment bound. -/
theorem exists_first_crossing_and_increment {S : ℕ → ℝ} {k : ℕ} {a L : ℝ}
    (hS0 : S 0 = 0) (ha : 0 ≤ a) (hL : a < L)
    (hstep : ∀ i, 1 ≤ i → i ≤ k → |S i - S (i - 1)| ≤ a)
    (hlarge : ∃ n ≤ k, 2 * L < |S n|) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ L < |S j| ∧
      (∀ i, i < j → |S i| ≤ L) ∧
      ∃ n, j ≤ n ∧ n ≤ k ∧ L - a ≤ |S n - S j| := by
  have hLpos : 0 < L := lt_of_le_of_lt ha hL
  obtain ⟨n, hnk, hn⟩ := hlarge
  have hex : ∃ j, j ≤ k ∧ L < |S j| := ⟨n, hnk, by linarith⟩
  let j := Nat.find hex
  have hj : j ≤ k ∧ L < |S j| := Nat.find_spec hex
  have hbefore : ∀ i, i < j → |S i| ≤ L := by
    intro i hij
    have hnot : ¬(i ≤ k ∧ L < |S i|) := Nat.find_min hex hij
    exact le_of_not_gt (fun hi => hnot ⟨le_trans (Nat.le_of_lt hij) hj.1, hi⟩)
  have hjpos : 1 ≤ j := by
    by_contra hj0
    have : j = 0 := by omega
    simp [this, hS0] at hj
    linarith
  have hprev : |S (j - 1)| ≤ L := hbefore _ (by omega)
  have hovershoot : |S j| ≤ L + a := by
    have htri := abs_add_le (S j - S (j - 1)) (S (j - 1))
    have hst := hstep j hjpos hj.1
    have heq : S j - S (j - 1) + S (j - 1) = S j := by ring
    rw [heq] at htri
    linarith
  have hjn : j ≤ n := Nat.find_min' hex ⟨hnk, by linarith⟩
  refine ⟨j, hjpos, hj.1, hj.2, hbefore, n, hjn, hnk, ?_⟩
  have htri := abs_add_le (S n - S j) (S j)
  have heq : S n - S j + S j = S n := by ring
  rw [heq] at htri
  linarith

open MeasureTheory

/-- The event that a path first exceeds a level at time `j`. -/
def firstCrossingEvent {Ω : Type*} (S : ℕ → Ω → ℝ) (L : ℝ) (j : ℕ) : Set Ω :=
  {ω | L < |S j ω| ∧ ∀ i, i < j → |S i ω| ≤ L}

/-- First-crossing events at different times are disjoint. -/
theorem firstCrossingEvent_disjoint {Ω : Type*} (S : ℕ → Ω → ℝ) (L : ℝ)
    {i j : ℕ} (hij : i ≠ j) : Disjoint (firstCrossingEvent S L i)
      (firstCrossingEvent S L j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hj.2 i h)) hi.1
  · exact (not_lt_of_ge (hi.2 j h)) hj.1

/-- A first-crossing event is measurable at the crossing time. -/
theorem measurableSet_firstCrossingEvent {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (S : ℕ → Ω → ℝ) (hS : ∀ i, Measurable[F i] (S i))
    (L : ℝ) (j : ℕ) : MeasurableSet[F j] (firstCrossingEvent S L j) := by
  let : MeasurableSpace Ω := F j
  have hprev : MeasurableSet[F j] {ω | ∀ i, i < j → |S i ω| ≤ L} := by
    simp only [show {ω | ∀ i, i < j → |S i ω| ≤ L} =
      ⋂ i < j, {ω | |S i ω| ≤ L} from by ext ω; simp]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun hij => ?_
    have hSi : Measurable[F j] (S i) := (hS i).mono (F.mono (Nat.le_of_lt hij)) le_rfl
    exact measurableSet_le hSi.abs measurable_const
  exact (measurableSet_lt measurable_const (hS j).abs).inter hprev

/-- The first-crossing events partition the event that a finite path exceeds a level. -/
theorem firstCrossingEvent_biUnion {Ω : Type*} (S : ℕ → Ω → ℝ) (L : ℝ) (k : ℕ) :
    (⋃ j ∈ Finset.range (k + 1), firstCrossingEvent S L j) =
      {ω | ∃ j ≤ k, L < |S j ω|} := by
  ext ω
  constructor
  · intro hω
    simp only [Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff] at hω
    obtain ⟨j, hj, hω⟩ := hω
    exact ⟨j, hj, hω.1⟩
  · intro hω
    let j := Nat.find hω
    have hj := Nat.find_spec hω
    have hprev : ∀ i, i < j → |S i ω| ≤ L := by
      intro i hi
      have hn := Nat.find_min hω hi
      exact le_of_not_gt (fun h => hn ⟨le_trans (Nat.le_of_lt hi) hj.1, h⟩)
    simp only [Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨j, hj.1, hj.2, hprev⟩

/-- A first-crossing estimate obtained from an eventwise maximal inequality. -/
theorem firstCrossing_goodLambda_internal {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (F : Filtration ℕ m)
    (S V : ℕ → Ω → ℝ) (k : ℕ) (a L d : ℝ)
    (ha : 0 ≤ a) (hL : a < L) (hd : 0 < d)
    (hS : ∀ i, Measurable[F i] (S i)) (hS0 : ∀ ω, S 0 ω = 0)
    (hstep : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |S i ω - S (i - 1) ω| ≤ a)
    (hV : ∀ j, j ≤ k → ∀ ω, 0 ≤ V j ω)
    (hevent : ∀ j, j ≤ k → ∀ (B : Set Ω), MeasurableSet[F j] B →
      ∀ t v : ℝ, 0 < t → 0 < v →
        μ.real ((B ∩ {ω | ∃ n, j ≤ n ∧ n ≤ k ∧ t ≤ |S n ω - S j ω|}) ∩
          {ω | V k ω - V j ω ≤ v}) ≤
        (2 * Real.exp (-(t ^ 2) / (2 * (v + a * t / 3)))) * μ.real B) :
    μ.real ({ω | ∃ n ≤ k, 2 * L < |S n ω|} ∩ {ω | Real.sqrt (V k ω) ≤ d * L}) ≤
      (2 * Real.exp (-((L - a) ^ 2) / (2 * (d ^ 2 * L ^ 2 + a * (L - a) / 3)))) *
        μ.real {ω | ∃ n ≤ k, L < |S n ω|} := by
  classical
  let A := firstCrossingEvent S L
  let E : ℕ → Set Ω := fun j =>
    (A j ∩ {ω | ∃ n, j ≤ n ∧ n ≤ k ∧ L - a ≤ |S n ω - S j ω|}) ∩
      {ω | V k ω - V j ω ≤ d ^ 2 * L ^ 2}
  let c := 2 * Real.exp (-((L - a) ^ 2) / (2 * (d ^ 2 * L ^ 2 + a * (L - a) / 3)))
  have hL0 : 0 < L := lt_of_le_of_lt ha hL
  have hdL : 0 ≤ d * L := le_of_lt (mul_pos hd hL0)
  have hsubset : ({ω | ∃ n ≤ k, 2 * L < |S n ω|} ∩
      {ω | Real.sqrt (V k ω) ≤ d * L}) ⊆ ⋃ j ∈ Finset.range (k + 1), E j := by
    intro ω hω
    obtain ⟨j, hjpos, hjk, hj, hprev, n, hjn, hnk, hn⟩ :=
      exists_first_crossing_and_increment (hS0 ω) ha hL (fun i hi hik => hstep i hi hik ω) hω.1
    have hsqrt : V k ω ≤ d ^ 2 * L ^ 2 := by
      have hs := sq_le_sq₀ (Real.sqrt_nonneg _) hdL |>.mpr hω.2
      rw [Real.sq_sqrt (hV k le_rfl ω)] at hs
      nlinarith
    have hv : V k ω - V j ω ≤ d ^ 2 * L ^ 2 := by
      have hvj := hV j hjk ω
      linarith
    simp only [Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨j, hjk, ⟨⟨hj, hprev⟩, n, hjn, hnk, hn⟩, hv⟩
  have hAm : ∀ j, MeasurableSet (A j) := by
    intro j
    exact F.le j _ (measurableSet_firstCrossingEvent F S hS L j)
  have hdisj : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint A := by
    intro i hi j hj hij
    exact firstCrossingEvent_disjoint S L hij
  have hsum : ∑ j ∈ Finset.range (k + 1), μ.real (A j) =
      μ.real {ω | ∃ n ≤ k, L < |S n ω|} := by
    rw [← measureReal_biUnion_finset hdisj (fun j _ => hAm j)]
    exact congrArg μ.real (firstCrossingEvent_biUnion S L k)
  calc μ.real ({ω | ∃ n ≤ k, 2 * L < |S n ω|} ∩
        {ω | Real.sqrt (V k ω) ≤ d * L})
      ≤ μ.real (⋃ j ∈ Finset.range (k + 1), E j) := measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ ∑ j ∈ Finset.range (k + 1), μ.real (E j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1), c * μ.real (A j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      apply hevent j hjk (A j) (measurableSet_firstCrossingEvent F S hS L j)
      · linarith
      · positivity
    _ = c * μ.real {ω | ∃ n ≤ k, L < |S n ω|} := by rw [← Finset.mul_sum, hsum]

/-- The bounded representative of the predictable quadratic variation. -/
noncomputable def bernsteinClippedVariance {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) (F : Filtration ℕ m) (ξ : ℕ → Ω → ℝ) (a : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, min (a ^ 2) (max 0 (μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)] ω))

/-- The first-crossing good-λ estimate for bounded partial sums, conditional on the
corresponding eventwise maximal inequality. -/
theorem bernstein_firstCrossing_goodLambda_internal {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (F : Filtration ℕ m)
    (ξ : ℕ → Ω → ℝ) (k : ℕ) (a L d : ℝ)
    (ha : 0 < a) (hL : a < L) (hd : 0 < d)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (_hξint : ∀ i, Integrable (ξ i) μ)
    (_hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a)
    (hevent : ∀ j, j ≤ k → ∀ (B : Set Ω), MeasurableSet[F j] B →
      ∀ t v : ℝ, 0 < t → 0 < v →
        μ.real ((B ∩ {ω | ∃ n, j ≤ n ∧ n ≤ k ∧
          t ≤ |crossTermPartialSum ξ n ω - crossTermPartialSum ξ j ω|}) ∩
          {ω | bernsteinClippedVariance μ F ξ a k ω -
            bernsteinClippedVariance μ F ξ a j ω ≤ v}) ≤
        (2 * Real.exp (-(t ^ 2) / (2 * (v + a * t / 3)))) * μ.real B) :
    μ.real ({ω | 2 * L < crossTermMax ξ k ω} ∩
      {ω | Real.sqrt (bernsteinClippedVariance μ F ξ a k ω) ≤ d * L}) ≤
      (2 * Real.exp (-((L - a) ^ 2) / (2 * (d ^ 2 * L ^ 2 + a * (L - a) / 3)))) *
        μ.real {ω | L < crossTermMax ξ k ω} := by
  have hS : ∀ i, Measurable[F i] (crossTermPartialSum ξ i) := by
    intro i
    let : MeasurableSpace Ω := F i
    unfold crossTermPartialSum
    refine Finset.measurable_sum _ fun j hj => ?_
    exact (hξ j).mono (F.mono (Finset.mem_Icc.mp hj).2) le_rfl
  have hS0 : ∀ ω, crossTermPartialSum ξ 0 ω = 0 := by
    intro ω
    simp [crossTermPartialSum]
  have hstep : ∀ i, 1 ≤ i → i ≤ k → ∀ ω,
      |crossTermPartialSum ξ i ω - crossTermPartialSum ξ (i - 1) ω| ≤ a := by
    intro i hi hik ω
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hsum : crossTermPartialSum ξ (j + 1) ω = crossTermPartialSum ξ j ω + ξ (j + 1) ω := by
      simp only [crossTermPartialSum]
      rw [Finset.sum_Icc_succ_top (by omega) (fun j => ξ j ω)]
    simpa [hsum] using hbound (j + 1) (by omega) hik ω
  have hV : ∀ j, j ≤ k → ∀ ω, 0 ≤ bernsteinClippedVariance μ F ξ a j ω := by
    intro j hj ω
    unfold bernsteinClippedVariance
    exact Finset.sum_nonneg (fun i hi => le_min (sq_nonneg a) (le_max_left _ _))
  have h := firstCrossing_goodLambda_internal μ F (crossTermPartialSum ξ)
    (bernsteinClippedVariance μ F ξ a) k a L d (le_of_lt ha) hL hd hS hS0 hstep hV hevent
  simpa only [crossTermMax, Finset.lt_sup'_iff, Finset.mem_range, Nat.lt_succ_iff] using h

end LatticeProb
