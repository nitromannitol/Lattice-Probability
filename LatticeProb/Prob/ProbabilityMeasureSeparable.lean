import Mathlib

/-!
# The space of probability measures on a separable metrizable space is separable

For a separable pseudo-metrizable space `X` with its Borel `σ`-algebra, the space
`ProbabilityMeasure X` with the topology of convergence in distribution is separable.
(Together with Mathlib's metrizability instance it is therefore second countable.)

The countable dense set consists of the finite rational mixtures of Dirac masses at the points of
a fixed dense sequence of `X`. Given `P`, the `n`-th approximation partitions `X` into the cells
`{x | the first dense point within distance 1/(n+1) of x is x_k}`, replaces `P` on each cell by a
Dirac mass at `x_k`, truncates the cell sequence and rounds the weights down to rationals; the
remaining mass is placed at `x_0`. Integrals of bounded continuous functions converge by dominated
convergence.
-/

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LatticeProb

/-! ### Rational weights approximating a probability vector -/

/-- A probability vector on `ℕ` can be replaced by a finitely supported vector with rational
weights, with total mass at most one, such that for every bounded sequence `c` the corresponding
mixture of values (the missing mass being assigned to the index `0`) is within `δ * C` of the
infinite weighted sum, where `C` bounds `|c|`. -/
theorem exists_rational_weights {p : ℕ → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp : HasSum p 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (N : ℕ) (q : ℕ → ℚ), (∀ k, 0 ≤ q k) ∧ (∑ k ∈ Finset.range N, (q k : ℝ)) ≤ 1 ∧
      ∀ (C : ℝ) (c : ℕ → ℝ), (∀ k, |c k| ≤ C) →
        |(∑ k ∈ Finset.range N, (q k : ℝ) * c k)
            + (1 - ∑ k ∈ Finset.range N, (q k : ℝ)) * c 0 - ∑' k, p k * c k| ≤ δ * C := by
  have hT : Tendsto (fun N => ∑ k ∈ Finset.range N, p k) atTop (𝓝 1) := hp.tendsto_sum_nat
  obtain ⟨N, hN⟩ := (hT.eventually (lt_mem_nhds (show 1 - δ / 4 < 1 by linarith))).exists
  set η : ℝ := δ / (4 * ((N : ℝ) + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hNη : (N : ℝ) * η ≤ δ / 4 := by
    have h1 : ((N : ℝ) + 1) * η = δ / 4 := by rw [hη]; field_simp
    nlinarith
  have hq : ∀ k, ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ p k ∧ p k - η < q := by
    intro k
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show p k - η < p k by linarith)
    refine ⟨max q 0, le_max_right _ _, ?_, ?_⟩
    · rw [Rat.cast_max]; exact max_le hq2.le (by simpa using hp0 k)
    · rw [Rat.cast_max]; exact lt_max_of_lt_left hq1
  choose q hq0 hqle hqgt using hq
  have hsumq : ∑ k ∈ Finset.range N, (q k : ℝ) ≤ ∑ k ∈ Finset.range N, p k :=
    Finset.sum_le_sum (fun k _ => hqle k)
  have hsump : ∑ k ∈ Finset.range N, p k ≤ 1 := sum_le_hasSum _ (fun k _ => hp0 k) hp
  refine ⟨N, q, fun k => hq0 k, hsumq.trans hsump, ?_⟩
  intro C c hc
  have hC : 0 ≤ C := (abs_nonneg _).trans (hc 0)
  set T : ℝ := 1 - ∑ k ∈ Finset.range N, p k with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; linarith
  have hT1 : T < δ / 4 := by rw [hTdef]; linarith
  have hshift : HasSum (fun n => p (n + N)) T := (hasSum_nat_add_iff' N).mpr hp
  have hpc : Summable (fun k => p k * c k) := by
    refine Summable.of_norm_bounded (hp.summable.mul_right C) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 k)]
    exact mul_le_mul_of_nonneg_left (hc k) (hp0 k)
  have hsplit := hpc.sum_add_tsum_nat_add N
  -- the tail
  have htail : |∑' i, p (i + N) * c (i + N)| ≤ T * C := by
    have := tsum_of_norm_bounded (f := fun i => p (i + N) * c (i + N))
      (hshift.mul_right C) (fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 _)]
        exact mul_le_mul_of_nonneg_left (hc _) (hp0 _))
    simpa [Real.norm_eq_abs] using this
  -- the head
  have hA : |∑ k ∈ Finset.range N, ((q k : ℝ) - p k) * c k| ≤ N * η * C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ k ∈ Finset.range N, |((q k : ℝ) - p k) * c k| ≤ η * C := by
      intro k _
      rw [abs_mul]
      have h1 : |(q k : ℝ) - p k| ≤ η := by
        rw [abs_le]; constructor <;> linarith [hqle k, hqgt k]
      exact mul_le_mul h1 (hc k) (abs_nonneg _) hηpos.le
    refine (Finset.sum_le_sum this).trans ?_
    simp [mul_assoc]
  -- the missing mass
  have hr0 : 0 ≤ 1 - ∑ k ∈ Finset.range N, (q k : ℝ) := by linarith
  have hr1 : 1 - ∑ k ∈ Finset.range N, (q k : ℝ) ≤ T + N * η := by
    have : ∑ k ∈ Finset.range N, (p k - (q k : ℝ)) ≤ N * η := by
      have := Finset.sum_le_card_nsmul (Finset.range N) (fun k => p k - (q k : ℝ)) η
        (fun k _ => by linarith [hqgt k])
      simpa using this
    rw [Finset.sum_sub_distrib] at this
    rw [hTdef]; linarith
  have hr : |(1 - ∑ k ∈ Finset.range N, (q k : ℝ)) * c 0| ≤ (T + N * η) * C := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul hr1 (hc 0) (abs_nonneg _) (by linarith)
  have hsplit' : ∑ k ∈ Finset.range N, p k * c k + ∑' i, p (i + N) * c (i + N)
      = ∑' k, p k * c k := hsplit
  have heq : (∑ k ∈ Finset.range N, (q k : ℝ) * c k)
      + (1 - ∑ k ∈ Finset.range N, (q k : ℝ)) * c 0 - ∑' k, p k * c k
      = ∑ k ∈ Finset.range N, ((q k : ℝ) - p k) * c k
        + (1 - ∑ k ∈ Finset.range N, (q k : ℝ)) * c 0 - ∑' i, p (i + N) * c (i + N) := by
    have : ∑ k ∈ Finset.range N, ((q k : ℝ) - p k) * c k
        = ∑ k ∈ Finset.range N, (q k : ℝ) * c k - ∑ k ∈ Finset.range N, p k * c k := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, ← hsplit']; ring
  rw [heq]
  have h3 := abs_add_le (∑ k ∈ Finset.range N, ((q k : ℝ) - p k) * c k
      + (1 - ∑ k ∈ Finset.range N, (q k : ℝ)) * c 0) (-∑' i, p (i + N) * c (i + N))
  have h4 := abs_add_le (∑ k ∈ Finset.range N, ((q k : ℝ) - p k) * c k)
      ((1 - ∑ k ∈ Finset.range N, (q k : ℝ)) * c 0)
  rw [abs_neg] at h3
  rw [← sub_eq_add_neg] at h3
  have hfin : (N * η * C) + (T + N * η) * C + T * C ≤ δ * C := by
    have : N * η + (T + N * η) + T ≤ δ := by linarith
    nlinarith
  linarith


/-! ### Rational mixtures of Dirac masses -/

section Mixtures

variable {X : Type*} [MeasurableSpace X]

/-- The finite mixture `∑ q k • δ_{xs k}` over `k < N`, the missing mass `1 - ∑ q k` placed at
`xs 0`. -/
noncomputable def mixMeasure (xs : ℕ → X) (N : ℕ) (q : Fin N → ℚ) : Measure X :=
  (∑ k : Fin N, ENNReal.ofReal (q k) • Measure.dirac (xs k))
    + ENNReal.ofReal (1 - ∑ k : Fin N, (q k : ℝ)) • Measure.dirac (xs 0)

theorem mixMeasure_univ (xs : ℕ → X) (N : ℕ) (q : Fin N → ℚ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k : Fin N, (q k : ℝ) ≤ 1) : mixMeasure xs N q Set.univ = 1 := by
  simp only [mixMeasure, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by exact_mod_cast hq0 k),
    ← ENNReal.ofReal_add (Finset.sum_nonneg (fun k _ => by exact_mod_cast hq0 k))
      (by linarith)]
  simp

theorem integral_mixMeasure (xs : ℕ → X) (N : ℕ) (q : Fin N → ℚ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k : Fin N, (q k : ℝ) ≤ 1) [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(mixMeasure xs N q)
      = ∑ k : Fin N, (q k : ℝ) * f (xs k) + (1 - ∑ k : Fin N, (q k : ℝ)) * f (xs 0) := by
  have hint : ∀ (c : ℝ≥0∞), c ≠ ⊤ → ∀ a : X, Integrable f (c • Measure.dirac a) :=
    fun c hc a => (f.integrable (Measure.dirac a)).smul_measure hc
  have hdir : ∀ a : X, ∫ x, f x ∂Measure.dirac a = f a := fun a =>
    integral_dirac' f a f.continuous.stronglyMeasurable
  unfold mixMeasure
  rw [integral_add_measure
    (integrable_finsetSum_measure.2 (fun k _ => hint _ ENNReal.ofReal_ne_top _))
    (hint _ ENNReal.ofReal_ne_top _),
    integral_finsetSum_measure (fun k _ => hint _ ENNReal.ofReal_ne_top _)]
  simp only [integral_smul_measure, hdir, smul_eq_mul]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ENNReal.toReal_ofReal (by exact_mod_cast hq0 k)]
  · rw [ENNReal.toReal_ofReal (by linarith)]

end Mixtures


/-! ### Cells of a partition into small balls around a dense sequence -/

section Cells

variable {X : Type*} [PseudoMetricSpace X]

open Classical in
/-- The index of the first point of the dense sequence `xs` within distance `1 / (n + 1)` of `x`. -/
noncomputable def cellIdx {xs : ℕ → X} (hxs : DenseRange xs) (n : ℕ) (x : X) : ℕ :=
  Nat.find (hxs.exists_dist_lt x (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity))

theorem dist_cellIdx_lt {xs : ℕ → X} (hxs : DenseRange xs) (n : ℕ) (x : X) :
    dist x (xs (cellIdx hxs n x)) < 1 / ((n : ℝ) + 1) := by
  classical
  exact Nat.find_spec (hxs.exists_dist_lt x (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity))

theorem tendsto_cellIdx {xs : ℕ → X} (hxs : DenseRange xs) (x : X) :
    Tendsto (fun n => xs (cellIdx hxs n x)) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [dist_comm]
  exact (dist_cellIdx_lt hxs n x).le

variable [MeasurableSpace X] [BorelSpace X]

theorem measurable_cellIdx {xs : ℕ → X} (hxs : DenseRange xs) (n : ℕ) :
    Measurable (cellIdx hxs n) := by
  classical
  refine measurable_to_countable' (fun k => ?_)
  have hopen : ∀ j, MeasurableSet {x : X | dist x (xs j) < 1 / ((n : ℝ) + 1)} := fun j =>
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).measurableSet
  have hset : cellIdx hxs n ⁻¹' {k}
      = {x : X | dist x (xs k) < 1 / ((n : ℝ) + 1)}
        ∩ ⋂ j, ⋂ (_ : j < k), {x : X | dist x (xs j) < 1 / ((n : ℝ) + 1)}ᶜ := by
    ext x
    simp [cellIdx, Nat.find_eq_iff]
  rw [hset]
  exact (hopen k).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hopen j).compl)

end Cells

/-! ### Separability -/

section Separable

variable {X : Type*} [PseudoMetricSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X]

theorem separableSpace_probabilityMeasure_of_metric :
    SeparableSpace (ProbabilityMeasure X) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty (ProbabilityMeasure X) := ⟨fun P => by
      have h : (P : Measure X) Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.2 hX, measure_empty] at h
      exact zero_ne_one h⟩
    infer_instance
  obtain ⟨xs, hxs⟩ := TopologicalSpace.exists_dense_seq X
  let g : {d : (Σ N : ℕ, (Fin N → ℚ)) // IsProbabilityMeasure (mixMeasure xs d.1 d.2)}
      → ProbabilityMeasure X := fun d => ⟨mixMeasure xs d.1.1 d.1.2, d.2⟩
  refine ⟨⟨Set.range g, Set.countable_range g, ?_⟩⟩
  intro P
  -- the cell weights of `P`
  set p : ℕ → ℕ → ℝ := fun n k => ((P : Measure X).map (cellIdx hxs n)).real {k} with hpdef
  have hmap : ∀ n, IsProbabilityMeasure ((P : Measure X).map (cellIdx hxs n)) := fun n =>
    inferInstance
  have hp0 : ∀ n k, 0 ≤ p n k := fun n k => measureReal_nonneg
  have hpsum : ∀ n, HasSum (p n) 1 := by
    intro n
    have := hmap n
    have hs : Summable (p n) :=
      summable_measure_toReal (μ := (P : Measure X).map (cellIdx hxs n))
        (f := fun k => ({k} : Set ℕ)) (fun k => measurableSet_singleton k)
        (fun i j hij => Set.disjoint_singleton.2 hij)
    have h1 := integral_countable (μ := (P : Measure X).map (cellIdx hxs n))
      (f := fun _ => (1 : ℝ)) (integrable_const 1)
    have hu : ((P : Measure X).map (cellIdx hxs n)).real Set.univ = 1 := by
      rw [measureReal_def, measure_univ]; simp
    simp only [integral_const, hu, smul_eq_mul, mul_one] at h1
    have : ∑' k, p n k = 1 := h1.symm
    rw [← this]
    exact hs.hasSum
  choose N q hq0 hq1 hqc using
    fun n : ℕ => exists_rational_weights (hp0 n) (hpsum n) (δ := 1 / ((n : ℝ) + 1)) (by positivity)
  have hq1' : ∀ n, ∑ i : Fin (N n), ((q n i : ℚ) : ℝ) ≤ 1 := fun n =>
    (Fin.sum_univ_eq_sum_range (fun k => ((q n k : ℚ) : ℝ)) (N n)).le.trans (hq1 n)
  have hprob : ∀ n, IsProbabilityMeasure (mixMeasure xs (N n) (fun i : Fin (N n) => q n i)) :=
    fun n => ⟨mixMeasure_univ xs (N n) _ (fun k => hq0 n k) (hq1' n)⟩
  let Q : ℕ → ProbabilityMeasure X :=
    fun n => ⟨mixMeasure xs (N n) (fun i : Fin (N n) => q n i), hprob n⟩
  have hmem : ∀ n, Q n ∈ Set.range g := fun n => ⟨⟨⟨N n, fun i => q n i⟩, hprob n⟩, rfl⟩
  have hQ : Tendsto Q atTop (𝓝 P) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hbt : Tendsto (fun n => ∫ x, f (xs (cellIdx hxs n x)) ∂(P : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(P : Measure X))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun n => ?_)
        (integrable_const _) (fun n => ae_of_all _ (fun x => ?_)) (ae_of_all _ (fun x => ?_))
      · exact (f.continuous.measurable.comp ((measurable_from_nat (f := xs)).comp
          (measurable_cellIdx hxs n))).aestronglyMeasurable
      · exact f.norm_coe_le_norm _
      · exact (f.continuous.tendsto x).comp (tendsto_cellIdx hxs x)
    have hbsum : ∀ n, ∫ x, f (xs (cellIdx hxs n x)) ∂(P : Measure X)
        = ∑' k, p n k * f (xs k) := by
      intro n
      have hmeas : Measurable (cellIdx hxs n) := measurable_cellIdx hxs n
      have hfm : AEStronglyMeasurable (fun k : ℕ => f (xs k))
          ((P : Measure X).map (cellIdx hxs n)) :=
        (f.continuous.measurable.comp (measurable_from_nat (f := xs))).aestronglyMeasurable
      have hi : Integrable (fun k : ℕ => f (xs k)) ((P : Measure X).map (cellIdx hxs n)) := by
        have := hmap n
        exact (integrable_const ‖f‖).mono' hfm (ae_of_all _ (fun k => f.norm_coe_le_norm _))
      rw [← integral_map hmeas.aemeasurable hfm, integral_countable hi]
      simp only [smul_eq_mul]
      rfl
    have hab : ∀ n, |(∫ x, f x ∂(Q n : Measure X))
        - ∫ x, f (xs (cellIdx hxs n x)) ∂(P : Measure X)| ≤ 1 / ((n : ℝ) + 1) * ‖f‖ := by
      intro n
      have h1 := hqc n ‖f‖ (fun k => f (xs k))
        (fun k => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
      have hint : ∫ x, f x ∂(Q n : Measure X)
          = ∑ k ∈ Finset.range (N n), (q n k : ℝ) * f (xs k)
            + (1 - ∑ k ∈ Finset.range (N n), (q n k : ℝ)) * f (xs 0) := by
        show ∫ x, f x ∂(mixMeasure xs (N n) (fun i : Fin (N n) => q n i)) = _
        rw [integral_mixMeasure xs (N n) _ (fun k => hq0 n k) (hq1' n) f,
          Fin.sum_univ_eq_sum_range (fun k => ((q n k : ℚ) : ℝ) * f (xs k)) (N n),
          Fin.sum_univ_eq_sum_range (fun k => ((q n k : ℚ) : ℝ)) (N n)]
      rw [hint, hbsum n]
      exact h1
    have h0 : Tendsto (fun n => (∫ x, f x ∂(Q n : Measure X))
        - ∫ x, f (xs (cellIdx hxs n x)) ∂(P : Measure X)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using hab n) ?_
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖f‖
    have := hbt.add h0
    simpa using this
  exact mem_closure_of_tendsto hQ (Eventually.of_forall hmem)

end Separable

/-- The space of Borel probability measures on a separable pseudo-metrizable space, with the
topology of convergence in distribution, is separable. -/
instance instSeparableSpaceProbabilityMeasure (X : Type*) [TopologicalSpace X]
    [PseudoMetrizableSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] :
    SeparableSpace (ProbabilityMeasure X) := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  exact separableSpace_probabilityMeasure_of_metric

/-- The space of Borel probability measures on a separable pseudo-metrizable space, with the
topology of convergence in distribution, is second countable. -/
instance instSecondCountableTopologyProbabilityMeasure (X : Type*) [TopologicalSpace X]
    [PseudoMetrizableSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] :
    SecondCountableTopology (ProbabilityMeasure X) := by
  let := TopologicalSpace.pseudoMetrizableSpaceUniformity (ProbabilityMeasure X)
  have := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated
    (ProbabilityMeasure X)
  exact UniformSpace.secondCountable_of_separable (ProbabilityMeasure X)

end LatticeProb
