import LatticeProb.LQG.InternalMetricSquareTailUniform

/-!
# Uniformly small internal diameters of the closed dyadic subsquares

Let `S = [a, a + s] × [b, b + s]` with `s > 0`. The multiscale argument of Dubédat-Falconet-Gwynne-Pfeffer-Sun
(arXiv:1905.00380, proof of Proposition 3.10) bounds the internal diameter of `S` by the half-crossing lengths of its
closed dyadic subsquares. Applied to a subsquare of level `n` instead of `S`, the same argument only involves the
subsquares of level `m ≥ n`, so the bound is a tail sum. For the γ-LQG metric of a whole-plane GFF, with a uniform
unit-square crossing tail, the half-crossing lengths at level `m` decay exponentially in `m` outside events of summable
probability, so the internal diameters of all the subsquares of level `n` (each in its own internal metric) are
simultaneously small with probability tending to `1`.

## Main statements

* `LatticeProb.LQG.IsEuclideanLengthMetric.internalMetric_closedDyadicSubsquare_le_of_hasShortHalfCrossings`:
  the deterministic tail-sum bound for one subsquare.
* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_closedDyadicSubsquare_le`:
  the probability that some subsquare of level `n` has internal diameter larger than `ε` tends to `0`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

/-- **Internal diameter of one closed dyadic subsquare from the half crossings of the finer levels.** If every closed
dyadic subsquare of level `m ≥ n` of `S = [a, a + s] × [b, b + s]` has hard crossings of its four halves of `D`-length at
most `l m`, then any two points of the subsquare `S_{n,i,j}` are at internal distance in `S_{n,i,j}` at most
`3 (l n + 2 ∑_{k ≥ 0} l (n + k + 1))`. -/
theorem IsEuclideanLengthMetric.internalMetric_closedDyadicSubsquare_le_of_hasShortHalfCrossings
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {a b s : ℝ} (hs : 0 < s) (l : ℕ → ℝ≥0∞) {n i j : ℕ}
    (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hcross : ∀ m, n ≤ m → ∀ i' j' : ℕ, i' < 2 ^ m → j' < 2 ^ m →
      HasShortHalfCrossings D (a + i' * (s / 2 ^ m)) (a + (i' + 1) * (s / 2 ^ m)) (b + j' * (s / 2 ^ m))
        (b + (j' + 1) * (s / 2 ^ m)) (l m))
    {z w : ℂ} (hz : z ∈ closedDyadicSubsquare a b s n i j) (hw : w ∈ closedDyadicSubsquare a b s n i j) :
    internalMetric D (closedDyadicSubsquare a b s n i j) z w ≤ 3 * (l n + 2 * ∑' k, l (n + k + 1)) := by
  have hr : 0 < s / 2 ^ n := by positivity
  have e0 : ∀ (c : ℝ) (p : ℕ), c + ((p : ℝ) + 1) * (s / 2 ^ n) = c + p * (s / 2 ^ n) + s / 2 ^ n :=
    fun c p => by ring
  have hsq : closedDyadicSubsquare a b s n i j =
      Icc (a + i * (s / 2 ^ n)) (a + i * (s / 2 ^ n) + s / 2 ^ n) ×ℂ
        Icc (b + j * (s / 2 ^ n)) (b + j * (s / 2 ^ n) + s / 2 ^ n) := by
    simp only [closedDyadicSubsquare, e0]
  rw [hsq] at hz hw ⊢
  refine hD.internalMetric_le_of_hasShortHalfCrossings hr (fun k => l (n + k))
    (fun k i' j' hi' hj' => ?_) hz hw
  -- the level-`k` subsquare `(i', j')` of `S_{n,i,j}` is the level-`(n + k)` subsquare `(2ᵏ i + i', 2ᵏ j + j')` of `S`
  have e1 : ∀ (c : ℝ) (p q : ℕ), c + p * (s / 2 ^ n) + q * (s / 2 ^ n / 2 ^ k) =
      c + ((2 ^ k * p + q : ℕ) : ℝ) * (s / 2 ^ (n + k)) := by
    intro c p q
    push_cast
    rw [pow_add]
    field_simp
    ring
  have e2 : ∀ (c : ℝ) (p q : ℕ), c + p * (s / 2 ^ n) + ((q : ℝ) + 1) * (s / 2 ^ n / 2 ^ k) =
      c + (((2 ^ k * p + q : ℕ) : ℝ) + 1) * (s / 2 ^ (n + k)) := by
    intro c p q
    push_cast
    rw [pow_add]
    field_simp
    ring
  have hlt : ∀ p q : ℕ, p < 2 ^ n → q < 2 ^ k → 2 ^ k * p + q < 2 ^ (n + k) := by
    intro p q hp hq
    calc 2 ^ k * p + q < 2 ^ k * p + 2 ^ k := by omega
      _ = 2 ^ k * (p + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ n := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (n + k) := by rw [pow_add, mul_comm]
  rw [e1, e2, e1, e2]
  exact hcross (n + k) (Nat.le_add_right n k) _ _ (hlt i i' hi hi') (hlt j j' hj hj')

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Uniformly small internal diameters of the closed dyadic subsquares** (Dubédat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380, the multiscale argument of the proof of Proposition 3.10, with their Proposition 3.1 as the hypothesis
`huniv`). Let `𝔇` be a γ-LQG metric with `ξ > 0`, `h` a whole-plane GFF and `S = [a, a + s] × [b, b + s]` with `s > 0`.
Let `δ < θ < ξ (Q - 2) log 2`. Suppose that for every whole-plane GFF `h'` on the same probability space and every `n`,
the probability that the unit square has no half crossings of `D_{h'}`-length at most `e^{δ n}` is at most `p n`, where
`∑ₙ 4ⁿ p n < ∞`. Then for every `ε > 0`, the (outer) probability that some closed dyadic subsquare `S_{n,i,j}` of level `n`
contains two points at `D_h`-internal distance in `S_{n,i,j}` larger than `ε` tends to `0` as `n → ∞`. -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_closedDyadicSubsquare_le
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ)
    {θ δ : ℝ} (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ z ∈ closedDyadicSubsquare a b s n i j, ∀ w ∈ closedDyadicSubsquare a b s n i j,
        internalMetric (𝔇 (hC ω)) (closedDyadicSubsquare a b s n i j) z w ≤ ENNReal.ofReal ε})
      atTop (𝓝 0) := by
  set l : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (Real.exp (-((θ - δ) * m))) with hl_def
  set A : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (Real.exp (δ * m)) with hA_def
  have hlsum : ∑' m, l m ≠ ⊤ := tsum_ofReal_exp_neg_mul_ne_top (by linarith)
  -- the per-level bound of the bad events and its summability
  set F : ℕ → ℝ≥0∞ := fun m => ∑ i ∈ Finset.range (2 ^ m), ∑ j ∈ Finset.range (2 ^ m),
    (P {ω | ¬ HasShortHalfCrossings
        (𝔇 (recentredPairing hC hcirc (s / 2 ^ m) ⟨a + i * (s / 2 ^ m), b + j * (s / 2 ^ m)⟩ ω)) 0 1 0 1 (A m)} +
      P {ω | l m < ENNReal.ofReal (Real.exp (ξ * (hcirc ω (s / 2 ^ m) ⟨a + i * (s / 2 ^ m), b + j * (s / 2 ^ m)⟩ +
        lqgQ γ * Real.log (s / 2 ^ m)))) * A m}) with hF_def
  have hunit := tsum_unitTail_recentredPairing_ne_top (𝔇 := 𝔇) (a := a) (b := b) hG hs A p huniv hp
  have hscale : ∑' m : ℕ, ∑ i ∈ Finset.range (2 ^ m), ∑ j ∈ Finset.range (2 ^ m),
      P {ω | l m < ENNReal.ofReal (Real.exp (ξ * (hcirc ω (s / 2 ^ m) ⟨a + i * (s / 2 ^ m), b + j * (s / 2 ^ m)⟩ +
        lqgQ γ * Real.log (s / 2 ^ m)))) * A m} ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (hG.tsum_dyadic_measure_scaleFactor_ne_top (a := a) (b := b) (Q := lqgQ γ) hs hξ hθ)
      (ENNReal.tsum_le_tsum fun n => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_ofPred_eq, hl_def, hA_def] at hω ⊢
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp] at hω
    rw [Real.exp_lt_exp]
    linarith
  have hFsum : ∑' m, F m ≠ ⊤ := by
    simp only [hF_def, Finset.sum_add_distrib]
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.2 ⟨hunit, hscale⟩
  set B : ℕ → Set Ω := fun m => ⋃ i ∈ Finset.range (2 ^ m), ⋃ j ∈ Finset.range (2 ^ m),
    {ω | ¬ HasShortHalfCrossings (𝔇 (hC ω)) (a + i * (s / 2 ^ m)) (a + (i + 1) * (s / 2 ^ m))
      (b + j * (s / 2 ^ m)) (b + (j + 1) * (s / 2 ^ m)) (l m)} with hB_def
  have hB : ∀ m, P (B m) ≤ F m := by
    intro m
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact h𝔇.measure_not_hasShortHalfCrossings_dyadic_le hG hs m i j (A m) (l m)
  have hZ : P {ω | ¬ IsEuclideanLengthMetric (𝔇 (hC ω))} = 0 := by
    have h := h𝔇.ae_isEuclideanLengthMetric_self hG
    rwa [ae_iff] at h
  -- the deterministic bound `τ n` tends to `0`
  have hτ : Tendsto (fun n : ℕ => 3 * (l n + 2 * ∑' k, l (n + k + 1))) atTop (𝓝 0) := by
    have hl0 : Tendsto l atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hlsum
    have hs0 : Tendsto (fun n => ∑' k, l (n + k + 1)) atTop (𝓝 0) := by
      refine ((ENNReal.tendsto_sum_nat_add l hlsum).comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp only [Function.comp_apply]
      exact tsum_congr fun k => congrArg l (by omega)
    simpa using ENNReal.Tendsto.const_mul (hl0.add (ENNReal.Tendsto.const_mul hs0
      (Or.inr ENNReal.ofNat_ne_top))) (Or.inr ENNReal.ofNat_ne_top)
  have hτε : ∀ᶠ n in atTop, 3 * (l n + 2 * ∑' k, l (n + k + 1)) ≤ ENNReal.ofReal ε :=
    (hτ.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).mono fun _ hn => hn.le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ENNReal.tendsto_sum_nat_add F hFsum)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hτε] with n hn
  have hsub : {ω | ¬ ∀ i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ z ∈ closedDyadicSubsquare a b s n i j, ∀ w ∈ closedDyadicSubsquare a b s n i j,
        internalMetric (𝔇 (hC ω)) (closedDyadicSubsquare a b s n i j) z w ≤ ENNReal.ofReal ε} ⊆
      {ω | ¬ IsEuclideanLengthMetric (𝔇 (hC ω))} ∪ ⋃ m, B (m + n) := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq, not_not] at hcon
    obtain ⟨hDω, hBω⟩ := hcon
    refine hω fun i j hi hj z hz w hw => ?_
    refine (hDω.internalMetric_closedDyadicSubsquare_le_of_hasShortHalfCrossings hs l hi hj
      (fun m hm i' j' hi' hj' => ?_) hz hw).trans hn
    have h := hBω (m - n)
    rw [Nat.sub_add_cancel hm] at h
    simp only [hB_def, mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, not_exists, not_not] at h
    exact h i' hi' j' hj'
  calc P _ ≤ P ({ω | ¬ IsEuclideanLengthMetric (𝔇 (hC ω))} ∪ ⋃ m, B (m + n)) := measure_mono hsub
    _ ≤ P {ω | ¬ IsEuclideanLengthMetric (𝔇 (hC ω))} + P (⋃ m, B (m + n)) := measure_union_le _ _
    _ ≤ 0 + ∑' m, F (m + n) :=
        add_le_add hZ.le ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => hB (m + n)))
    _ = ∑' m, F (m + n) := zero_add _

end LatticeProb.LQG
