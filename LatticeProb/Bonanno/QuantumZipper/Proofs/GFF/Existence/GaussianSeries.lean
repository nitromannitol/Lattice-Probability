/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.Existence.GaussianSeries at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Existence.AssemblyAux1
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

/-!
# Gaussian processes from a Gram representation in a separable Hilbert space

Given a separable real Hilbert space `E` and an arbitrary family of vectors `v : T → E`, we
build, on the i.i.d. standard Gaussian sequence space `(ℕ → ℝ, stdP)`, real random variables
`X t` such that every finite linear combination `Σ cᵢ X (τ i)` is a centered Gaussian with
variance `‖Σ cᵢ v (τ i)‖²` (`gs_process_hilbert`).

Construction: expand `v t` in a countable Hilbert basis, `X t = Σ_k ⟪v t, e_k⟫ ω_k`. The series
is summed along a sparse subsequence of partial sums (depending on `t`) that converges almost
surely by Chebyshev and Borel–Cantelli (`gs_exists_subseq`); the laws of the finite
combinations are identified by `LQGDimension.ExistAsm.hasLaw_gaussianReal_of_tendsto`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace QuantumZipper.GFFExist

open LQGDimension.ExistAsm

/-! ### Finite-sum bookkeeping -/

/-- Partial sums of the Gaussian series `Σ_k a_k ω_k`. -/
def gsPartial (a : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range n, a k * ω k

lemma measurable_gsPartial (a : ℕ → ℝ) (n : ℕ) : Measurable (gsPartial a n) := by
  unfold gsPartial
  exact Finset.measurable_sum _ fun k _ => by fun_prop

lemma gs_sum_range_ite {f : ℕ → ℝ} {m M : ℕ} (h : m ≤ M) :
    ∑ k ∈ Finset.range M, (if k < m then f k else 0) = ∑ k ∈ Finset.range m, f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h' => h'.2, fun h' => ⟨lt_of_lt_of_le h' h, h'⟩⟩

lemma gs_ite_mul_ite (f g : ℕ → ℝ) (m n k : ℕ) :
    (if k < m then f k else 0) * (if k < n then g k else 0) =
      if k < min m n then f k * g k else 0 := by
  by_cases h1 : k < m <;> by_cases h2 : k < n <;> simp [h1, h2, lt_min_iff]

lemma gs_summable_mul {a b : ℕ → ℝ} (ha : Summable fun k => a k ^ 2)
    (hb : Summable fun k => b k ^ 2) : Summable fun k => a k * b k := by
  refine Summable.of_norm_bounded (ha.add hb) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|a k| - |b k|), sq_abs (a k), sq_abs (b k)]

/-! ### Chebyshev for centered Gaussians -/

lemma gs_meas_ge_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : Ω → ℝ} {v : NNReal} (hD : HasLaw D (gaussianReal 0 v) P) {c : ℝ} (hc : 0 < c) :
    P {ω | c ≤ |D ω|} ≤ ENNReal.ofReal (v / c ^ 2) := by
  have hmem : MemLp D 2 P := hD.hasGaussianLaw.memLp_two
  have h := meas_ge_le_variance_div_sq hmem hc
  have hmean : P[D] = 0 := by rw [hD.integral_eq, integral_id_gaussianReal]
  rw [hmean, hD.variance_eq, variance_id_gaussianReal] at h
  simpa using h

lemma gs_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℝ} {v : NNReal} (hD : HasLaw D (gaussianReal 0 v) P) : ∫ ω, D ω ∂P = 0 := by
  rw [hD.integral_eq, integral_id_gaussianReal]

/-! ### Almost sure convergence along a subsequence -/

lemma gs_diff_eq (a : ℕ → ℝ) {n m : ℕ} (hnm : n ≤ m) (ω : ℕ → ℝ) :
    gsPartial a m ω - gsPartial a n ω =
      ∑ k ∈ Finset.range m, (if n ≤ k then a k else 0) * ω k := by
  unfold gsPartial
  have hsplit : ∀ k, a k * ω k = (if k < n then a k * ω k else 0) +
      (if n ≤ k then a k else 0) * ω k := by
    intro k
    by_cases h : k < n
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, gs_sum_range_ite hnm]
  ring

lemma gs_diff_var_le (a : ℕ → ℝ) (ha : Summable fun k => a k ^ 2) {n m : ℕ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.range m, (if n ≤ k then a k else 0) ^ 2 ≤ ∑' k, a (k + n) ^ 2 := by
  have h1 : ∑ k ∈ Finset.range m, (if n ≤ k then a k else 0) ^ 2 =
      ∑ k ∈ Finset.Ico n m, a k ^ 2 := by
    rw [Finset.sum_congr rfl (fun k _ => show (if n ≤ k then a k else 0) ^ 2 =
      (if n ≤ k then a k ^ 2 else 0) by split_ifs <;> simp), ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have hs : Summable fun k => a (k + n) ^ 2 := (summable_nat_add_iff n).2 ha
  calc ∑ k ∈ Finset.range (m - n), a (n + k) ^ 2 = ∑ k ∈ Finset.range (m - n), a (k + n) ^ 2 := by
        simp_rw [add_comm n]
    _ ≤ ∑' k, a (k + n) ^ 2 := hs.sum_le_tsum _ (fun k _ => sq_nonneg _)

/-- Partial sums of a Gaussian series with square-summable coefficients converge almost surely
along a (strictly increasing) subsequence. -/
theorem gs_exists_subseq (a : ℕ → ℝ) (ha : Summable fun k => a k ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂stdP, ∃ L, Tendsto (fun j => gsPartial a (φ j) ω) atTop (𝓝 L) := by
  set tail : ℕ → ℝ := fun n => ∑' k, a (k + n) ^ 2 with htail_def
  have htail : Tendsto tail atTop (𝓝 0) := tendsto_sum_nat_add (fun k => a k ^ 2)
  have hN : ∀ j : ℕ, ∃ N, ∀ n ≥ N, tail n ∈ Set.Iic (((1 : ℝ) / 8) ^ j) := fun j =>
    eventually_atTop.1 (htail.eventually (Iic_mem_nhds (by positivity)))
  choose N hN using hN
  set φ : ℕ → ℕ := fun j => (∑ i ∈ Finset.range (j + 1), N i) + j with hφ_def
  have hφ : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    simp only [hφ_def, Finset.sum_range_succ _ (j + 1)]
    omega
  have hNφ : ∀ j, N j ≤ φ j := fun j => by
    have := Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
      (Finset.self_mem_range_succ j)
    simp only [hφ_def]
    omega
  refine ⟨φ, hφ, ?_⟩
  set D : ℕ → (ℕ → ℝ) → ℝ := fun j ω => gsPartial a (φ (j + 1)) ω - gsPartial a (φ j) ω
    with hD_def
  set w : ℕ → ℕ → ℝ := fun j k => if φ j ≤ k then a k else 0 with hw_def
  have hlaw : ∀ j, HasLaw (D j) (gaussianReal 0
      (∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2).toNNReal) stdP := by
    intro j
    have e : D j = fun ω => ∑ k ∈ Finset.range (φ (j + 1)), w j k * ω k := by
      funext ω
      exact gs_diff_eq a (hφ.monotone (Nat.le_succ j)) ω
    rw [e]
    exact hasLaw_sum_mul (w j) (φ (j + 1))
  have hvar : ∀ j, ∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2 ≤ ((1 : ℝ) / 8) ^ j := fun j =>
    (gs_diff_var_le a ha (hφ.monotone (Nat.le_succ j))).trans (hN j (φ j) (hNφ j))
  set s : ℕ → Set (ℕ → ℝ) := fun j => {ω | ((1 : ℝ) / 2) ^ j ≤ |D j ω|} with hs_def
  have hsb : ∀ j, stdP (s j) ≤ ENNReal.ofReal (1 / 2) ^ j := by
    intro j
    refine (gs_meas_ge_le (hlaw j) (by positivity : (0 : ℝ) < (1 / 2) ^ j)).trans ?_
    rw [← ENNReal.ofReal_pow (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hv0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.coe_toNNReal _ hv0, div_le_iff₀ (by positivity)]
    calc ∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2 ≤ ((1 : ℝ) / 8) ^ j := hvar j
      _ = (1 / 2) ^ j * ((1 / 2) ^ j) ^ 2 := by
          rw [← pow_mul, ← pow_add, show j + j * 2 = 3 * j by ring, pow_mul]; norm_num
  have hsum : ∑' j, stdP (s j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsb)
    exact (tsum_geometric_lt_top.2 (by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2
        (by norm_num))).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  have hbd : ∀ᶠ j in cofinite, ‖D j ω‖ ≤ ((1 : ℝ) / 2) ^ j := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hω] with j hj
    simp only [hs_def, Set.mem_ofPred_eq, not_le] at hj
    rw [Real.norm_eq_abs]
    exact hj.le
  have hS : Summable fun j => D j ω :=
    Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one (by norm_num)
      (by norm_num)) hbd
  refine ⟨gsPartial a (φ 0) ω + ∑' j, D j ω, ?_⟩
  have htel : ∀ n, gsPartial a (φ n) ω =
      gsPartial a (φ 0) ω + ∑ j ∈ Finset.range n, D j ω := by
    intro n
    simp only [hD_def]
    rw [Finset.sum_range_sub (fun j => gsPartial a (φ j) ω)]
    ring
  rw [show (fun j => gsPartial a (φ j) ω) =
      fun n => gsPartial a (φ 0) ω + ∑ j ∈ Finset.range n, D j ω from funext htel]
  exact tendsto_const_nhds.add hS.hasSum.tendsto_sum_nat

/-! ### The Gaussian series process -/

/-- The Gaussian series process for coefficient sequences in `ℓ²`: every finite linear
combination is a centered Gaussian with the Gram variance. -/
theorem gs_process (T : Type*) (a : T → ℕ → ℝ) (ha : ∀ t, Summable fun k => a t k ^ 2) :
    ∃ X : T → (ℕ → ℝ) → ℝ, (∀ t, Measurable (X t)) ∧
      ∀ {ι : Type} [Fintype ι] (τ : ι → T) (c : ι → ℝ),
        HasLaw (fun ω => ∑ i, c i * X (τ i) ω)
          (gaussianReal 0
            (∑ i, ∑ i', c i * c i' * ∑' k, a (τ i) k * a (τ i') k).toNNReal) stdP := by
  choose φ hφ hconv using fun t => gs_exists_subseq (a t) (ha t)
  set X : T → (ℕ → ℝ) → ℝ := fun t ω => limUnder atTop (fun j => gsPartial (a t) (φ t j) ω)
    with hX_def
  have hXm : ∀ t, Measurable (X t) := fun t =>
    (StronglyMeasurable.limUnder (fun j => (measurable_gsPartial (a t) (φ t j)).stronglyMeasurable)
      ).measurable
  have hXlim : ∀ t, ∀ᵐ ω ∂stdP,
      Tendsto (fun j => gsPartial (a t) (φ t j) ω) atTop (𝓝 (X t ω)) := by
    intro t
    filter_upwards [hconv t] with ω hω
    exact tendsto_nhds_limUnder hω
  refine ⟨X, hXm, ?_⟩
  intro ι _ τ c
  classical
  set M : ℕ → ℕ := fun j => ∑ i, φ (τ i) j with hM_def
  have hMle : ∀ i j, φ (τ i) j ≤ M j := fun i j =>
    Finset.single_le_sum (f := fun i => φ (τ i) j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set A : ι → ℕ → ℕ → ℝ := fun i j k => if k < φ (τ i) j then a (τ i) k else 0 with hA_def
  set w : ℕ → ℕ → ℝ := fun j k => ∑ i, c i * A i j k with hw_def
  set Y : ℕ → (ℕ → ℝ) → ℝ := fun j ω => ∑ k ∈ Finset.range (M j), w j k * ω k with hY_def
  have hYeq : ∀ j ω, Y j ω = ∑ i, c i * gsPartial (a (τ i)) (φ (τ i) j) ω := by
    intro j ω
    simp only [hY_def, hw_def, Finset.sum_mul, gsPartial]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← gs_sum_range_ite (hMle i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hA_def]
    split_ifs <;> ring
  have hVeq : ∀ j, ∑ k ∈ Finset.range (M j), w j k ^ 2 =
      ∑ i, ∑ i', c i * c i' *
        ∑ k ∈ Finset.range (min (φ (τ i) j) (φ (τ i') j)), a (τ i) k * a (τ i') k := by
    intro j
    simp only [hw_def, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum, ← gs_sum_range_ite (le_trans (min_le_left _ _) (hMle i j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hA_def]
    rw [mul_mul_mul_comm, gs_ite_mul_ite]
    split_ifs <;> ring
  have hlaw : ∀ j, HasLaw (Y j) (gaussianReal 0
      (∑ k ∈ Finset.range (M j), w j k ^ 2).toNNReal) stdP := fun j =>
    hasLaw_sum_mul (w j) (M j)
  refine hasLaw_gaussianReal_of_tendsto hlaw ?_ ?_
  · have hall : ∀ᵐ ω ∂stdP, ∀ i, Tendsto (fun j => gsPartial (a (τ i)) (φ (τ i) j) ω) atTop
        (𝓝 (X (τ i) ω)) := ae_all_iff.2 fun i => hXlim (τ i)
    filter_upwards [hall] with ω hω
    simp_rw [hYeq]
    exact tendsto_finsetSum _ fun i _ => (hω i).const_mul (c i)
  · simp_rw [hVeq]
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun i' _ => ?_
    refine Tendsto.const_mul _ ?_
    have hs := (gs_summable_mul (ha (τ i)) (ha (τ i'))).hasSum.tendsto_sum_nat
    refine hs.comp (tendsto_atTop_mono (fun j => le_min ((hφ (τ i)).id_le j)
      ((hφ (τ i')).id_le j)) tendsto_id)

/-! ### Countable Hilbert bases and the Hilbert-space version -/

lemma gs_countable_of_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] {ι : Type*} {e : ι → E} (he : Orthonormal ℝ e) :
    Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (e i) (1 / 2))
    (fun i j hij => ?_) (fun _ => Metric.isOpen_ball)
    (fun i => ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
  refine Metric.ball_disjoint_ball ?_
  have h2 : dist (e i) (e j) ^ 2 = 2 := by
    rw [dist_eq_norm, @norm_sub_sq_real, he.1 i, he.1 j, he.2 hij]
    ring
  nlinarith [dist_nonneg (x := e i) (y := e j)]

lemma gs_extend_mul {α : Type*} {e : α → ℕ} (he : Function.Injective e) (f g : α → ℝ) (k : ℕ) :
    Function.extend e f 0 k * Function.extend e g 0 k = Function.extend e (f * g) 0 k := by
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    simp [he.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

/-- **Gaussian process from a Gram representation.** For any family of vectors `v : T → E` in a
separable real Hilbert space, there are random variables `X t` on `(ℕ → ℝ, stdP)` all of whose
finite linear combinations `Σ cᵢ X (τ i)` are centered Gaussians of variance
`‖Σ cᵢ v (τ i)‖²`. -/
theorem gs_process_hilbert {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] (T : Type*) (v : T → E) :
    ∃ X : T → (ℕ → ℝ) → ℝ, (∀ t, Measurable (X t)) ∧
      ∀ {ι : Type} [Fintype ι] (τ : ι → T) (c : ι → ℝ),
        HasLaw (fun ω => ∑ i, c i * X (τ i) ω)
          (gaussianReal 0 (‖∑ i, c i • v (τ i)‖ ^ 2).toNNReal) stdP := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ E
  have : Countable w := gs_countable_of_orthonormal b.orthonormal
  obtain ⟨e, he⟩ := Countable.exists_injective_nat w
  set a : T → ℕ → ℝ := fun t => Function.extend e (fun i => ⟪v t, b i⟫) 0 with ha_def
  have hprod : ∀ s t, HasSum (fun k => a s k * a t k) ⟪v s, v t⟫ := by
    intro s t
    have h1 : (fun k => a s k * a t k) =
        Function.extend e ((fun i => ⟪v s, b i⟫) * fun i => ⟪v t, b i⟫) 0 := by
      funext k
      exact gs_extend_mul he _ _ k
    rw [h1, hasSum_extend_zero he]
    have h2 := b.hasSum_inner_mul_inner (v s) (v t)
    have e : ((fun i => ⟪v s, b i⟫) * fun i => ⟪v t, b i⟫) =
        fun i => ⟪v s, b i⟫ * ⟪b i, v t⟫ := by
      funext i
      simp only [Pi.mul_apply]
      rw [real_inner_comm (b i) (v t)]
    rw [e]
    exact h2
  have hsq : ∀ t, Summable fun k => a t k ^ 2 := fun t => by
    simp_rw [sq]; exact (hprod t t).summable
  obtain ⟨X, hXm, hX⟩ := gs_process T a hsq
  refine ⟨X, hXm, fun τ c => ?_⟩
  have key : ‖∑ i, c i • v (τ i)‖ ^ 2 =
      ∑ i, ∑ i', c i * c i' * ∑' k, a (τ i) k * a (τ i') k := by
    simp_rw [fun s t => (hprod s t).tsum_eq]
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  rw [key]
  exact hX τ c

/-! ### Consequences: centering, covariance, Gaussian processes -/

/-- Covariance from Gaussian laws of `A`, `B`, `A + B`, by polarization. -/
lemma gs_cov_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A B : Ω → ℝ} {u w : E}
    (hA : HasLaw A (gaussianReal 0 (‖u‖ ^ 2).toNNReal) P)
    (hB : HasLaw B (gaussianReal 0 (‖w‖ ^ 2).toNNReal) P)
    (hAB : HasLaw (fun ω => A ω + B ω) (gaussianReal 0 (‖u + w‖ ^ 2).toNNReal) P) :
    cov[A, B; P] = ⟪u, w⟫ := by
  have hvA : Var[A; P] = ‖u‖ ^ 2 := by
    rw [hA.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]
  have hvB : Var[B; P] = ‖w‖ ^ 2 := by
    rw [hB.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]
  have hvAB : Var[A + B; P] = ‖u + w‖ ^ 2 := by
    rw [show A + B = fun ω => A ω + B ω from rfl, hAB.variance_eq, variance_id_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg _)]
  have h := variance_add hA.hasGaussianLaw.memLp_two hB.hasGaussianLaw.memLp_two
  rw [hvA, hvB, hvAB, norm_add_sq_real] at h
  linarith

/-- A family all of whose finite linear combinations are centered Gaussians is a Gaussian
process. -/
lemma gs_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Type*}
    {Y : T → Ω → ℝ} (hmeas : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ (I : Finset T) (c : I → ℝ), ∃ v : NNReal,
      HasLaw (fun ω => ∑ i, c i * Y i ω) (gaussianReal 0 v) P) :
    IsGaussianProcess Y P :=
  ⟨fun I => hasGaussianLaw_pi_of_forall_hasLaw (fun i => hmeas i) (h I)⟩

end QuantumZipper.GFFExist
