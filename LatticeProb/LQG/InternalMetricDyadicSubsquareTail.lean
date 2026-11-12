import LatticeProb.LQG.InternalMetricUnitSquareTail
import LatticeProb.LQG.InternalMetricDyadicSmall

/-!
# A summable tail for the internal diameters of all the closed dyadic subsquares of the unit square

The multiscale argument of Dubédat-Falconet-Gwynne-Pfeffer-Sun (arXiv:1905.00380, proof of Proposition 3.10) bounds the
internal diameter of a closed dyadic subsquare of `[0, 1]²` of level `n` by a tail sum of the half-crossing lengths of the
subsquares of the levels `m ≥ n`. With crossing lengths decreasing in the level, this tail sum is at most the full sum
that bounds the internal diameter of `[0, 1]²` itself. Hence the union bound with thresholds depending on `k`, which
gives a summable tail for the internal diameter of the unit square, gives the same summable tail for the supremum over
all the levels `n` and all the subsquares of level `n` of their internal diameters (each in its own internal metric).

## Main statement

* `LatticeProb.LQG.IsLQGMetric.exists_closedDyadicSubsquare_internalMetric_tail`: there is `ψ` with `∑ₖ ψ k < ∞` such
  that for every whole-plane GFF `h'` and every `k`, the probability that some closed dyadic subsquare of `[0, 1]²` (of
  any level) contains two points at `D_{h'}`-internal distance in that subsquare more than `e^{ε k}` is at most `ψ k`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **A summable tail for the internal diameters of all the closed dyadic subsquares of the unit square, uniform over
the whole-plane GFFs** (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, the union bound of the proof of
Proposition 3.10 with thresholds depending on `k`, their Proposition 3.1 entering as `huniv`). Let `𝔇` be a γ-LQG
metric with `ξ > 0`, `h` a whole-plane GFF on `(Ω, P)`, and `0 < δ < θ < ξ (Q - 2) log 2`. Suppose that for every
whole-plane GFF `h'` on `(Ω, P)` and every `n` the probability that `[0, 1]²` has no half crossings of `D_{h'}`-length
at most `e^{δ n}` is at most `p n`, where `∑ₙ 4ⁿ p n < ∞`. Then for every `ε > 0` there is `ψ` with `∑ₖ ψ k < ∞` such
that for every whole-plane GFF `h'` on `(Ω, P)` and every `k`, the probability that for some level `n` some closed
dyadic subsquare `S_{n,i,j}` of `[0, 1]²` contains two points at `D_{h'}`-internal distance in `S_{n,i,j}` more than
`e^{ε k}` is at most `ψ k`. -/
theorem IsLQGMetric.exists_closedDyadicSubsquare_internalMetric_tail (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {θ δ ε : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) (hδ0 : 0 < δ) (hε : 0 < ε) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∃ ψ : ℕ → ℝ≥0∞, ∑' k, ψ k ≠ ⊤ ∧ ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
        P {ω | ¬ ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
          ∀ u ∈ closedDyadicSubsquare 0 0 1 n i j, ∀ v ∈ closedDyadicSubsquare 0 0 1 n i j,
            internalMetric (𝔇 (hC' ω)) (closedDyadicSubsquare 0 0 1 n i j) u v ≤
              ENNReal.ofReal (Real.exp (ε * k))} ≤ ψ k := by
  -- parameters: crossing lengths `l k n`, unit thresholds `e^{δ (n + m k)}`, Gaussian levels `c n + d k - K`
  have hθδ : 0 < θ - δ := by linarith
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (1 - Real.exp (-(θ - δ))) / 6 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by
    have : Real.exp (-(θ - δ)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    rw [hβ]; linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℕ, m = fun k : ℕ => ⌊ε / (2 * δ) * k⌋₊ := ⟨_, rfl⟩
  have hmδ : ∀ k : ℕ, δ * (m k : ℝ) ≤ ε / 2 * k := by
    intro k
    have h1 : (m k : ℝ) ≤ ε / (2 * δ) * k := by rw [hm]; exact Nat.floor_le (by positivity)
    calc δ * (m k : ℝ) ≤ δ * (ε / (2 * δ) * k) := mul_le_mul_of_nonneg_left h1 hδ0.le
      _ = ε / 2 * k := by field_simp
  obtain ⟨l, hl⟩ : ∃ l : ℕ → ℕ → ℝ≥0∞,
      l = fun (k n : ℕ) => ENNReal.ofReal (Real.exp (ε * k - (θ - δ) * n + Real.log β)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = lqgQ γ * Real.log 2 - θ / ξ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ε / (2 * ξ) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = -Real.log β / ξ := ⟨_, rfl⟩
  have hc2 : 2 * Real.log 2 < c := by
    have : θ / ξ < (lqgQ γ - 2) * Real.log 2 := by rw [div_lt_iff₀ hξ]; linarith
    rw [hc]; linarith
  have hd0 : 0 < d := by rw [hd]; positivity
  refine ⟨fun k => ∑' n : ℕ, 4 ^ n * p (n + m k) + ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n),
    ∑ j ∈ Finset.range (2 ^ n), P {ω | c * n + d * k - K ≤
      hcirc ω (1 / 2 ^ n) ⟨0 + i * (1 / 2 ^ n), 0 + j * (1 / 2 ^ n)⟩}, ?_, ?_⟩
  · rw [ENNReal.tsum_add]
    refine ENNReal.add_ne_top.2 ⟨?_,
      hG.tsum_tsum_dyadic_measure_circle_ge_linear_ne_top (a := 0) (b := 0) (K := K) one_pos hc2 hd0⟩
    rw [hm]
    exact tsum_tsum_four_pow_mul_floor_shift_ne_top hp (by positivity)
  intro hC' hcirc' hG' k
  -- the crossing lengths decrease in the level
  have hanti : ∀ n n' : ℕ, n ≤ n' → l k n' ≤ l k n := by
    intro n n' hnn'
    have hcast : (n : ℝ) ≤ n' := Nat.cast_le.2 hnn'
    rw [hl]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith
  -- the deterministic step: short half crossings at every level bound the internal diameter of every subsquare
  have hsub : {ω | ¬ ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ u ∈ closedDyadicSubsquare 0 0 1 n i j, ∀ v ∈ closedDyadicSubsquare 0 0 1 n i j,
        internalMetric (𝔇 (hC' ω)) (closedDyadicSubsquare 0 0 1 n i j) u v ≤
          ENNReal.ofReal (Real.exp (ε * k))} ⊆ {ω | ¬ IsEuclideanLengthMetric (𝔇 (hC' ω))} ∪
      ⋃ n : ℕ, ⋃ i ∈ Finset.range (2 ^ n), ⋃ j ∈ Finset.range (2 ^ n),
        {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) (0 + i * (1 / 2 ^ n)) (0 + (i + 1) * (1 / 2 ^ n))
          (0 + j * (1 / 2 ^ n)) (0 + (j + 1) * (1 / 2 ^ n)) (l k n)} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_iUnion, mem_ofPred_eq, Finset.mem_range, not_or, not_exists, not_not] at hcon
    obtain ⟨hD, hcr⟩ := hcon
    apply hω
    intro n i j hi hj u hu v hv
    refine (hD.internalMetric_closedDyadicSubsquare_le_of_hasShortHalfCrossings one_pos (l k) hi hj
      (fun n' _ i' j' hi' hj' => hcr n' i' hi' j' hj') hu hv).trans ?_
    have h6 : 6 * ∑' n : ℕ, l k n = ENNReal.ofReal (Real.exp (ε * k)) := by
      rw [hl]; exact six_mul_tsum_ofReal_exp_geometric hθδ hβ (ε * k)
    have hsplit : ∑' n : ℕ, l k n = l k 0 + ∑' n : ℕ, l k (n + 1) :=
      tsum_eq_zero_add' ENNReal.summable
    rw [← h6, hsplit]
    calc 3 * (l k n + 2 * ∑' n', l k (n + n' + 1)) ≤ 3 * (l k 0 + 2 * ∑' n', l k (n' + 1)) := by
          have h1 : l k n ≤ l k 0 := hanti 0 n (Nat.zero_le n)
          have h2 : ∑' n', l k (n + n' + 1) ≤ ∑' n', l k (n' + 1) :=
            ENNReal.tsum_le_tsum fun n' => hanti _ _ (by omega)
          gcongr
      _ = 3 * l k 0 + 6 * ∑' n', l k (n' + 1) := by
          rw [mul_add, ← mul_assoc]; norm_num
      _ ≤ 6 * l k 0 + 6 * ∑' n', l k (n' + 1) := by gcongr; norm_num
      _ = 6 * (l k 0 + ∑' n', l k (n' + 1)) := by rw [mul_add]
  -- the probabilistic step for one dyadic subsquare: coordinate change, uniform unit tail, Gaussian tail
  have hsq : ∀ n i j : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) (0 + i * (1 / 2 ^ n))
      (0 + (i + 1) * (1 / 2 ^ n)) (0 + j * (1 / 2 ^ n)) (0 + (j + 1) * (1 / 2 ^ n)) (l k n)} ≤
      p (n + m k) + P {ω | c * n + d * k - K ≤ hcirc ω (1 / 2 ^ n) ⟨0 + i * (1 / 2 ^ n), 0 + j * (1 / 2 ^ n)⟩} := by
    intro n i j
    refine (h𝔇.measure_not_hasShortHalfCrossings_dyadic_le hG' (a := 0) (b := 0) one_pos n i j
      (ENNReal.ofReal (Real.exp (δ * ((n + m k : ℕ) : ℝ)))) (l k n)).trans (add_le_add ?_ ?_)
    · exact huniv _ _ (isWholePlaneGFF_recentredPairing hG' (by positivity) _) (n + m k)
    · rw [hG.measure_le_circle_eq hG' (by positivity)]
      refine measure_mono fun ω hω => ?_
      simp only [mem_ofPred_eq, hl] at hω ⊢
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp] at hω
      have hlog : Real.log (1 / 2 ^ n) = -(n * Real.log 2) := by
        rw [one_div, Real.log_inv, Real.log_pow]
      rw [hlog] at hω
      push_cast at hω
      have hmk := hmδ k
      refine le_of_mul_le_mul_left ?_ hξ
      have e : ξ * (c * n + d * k - K) = ξ * lqgQ γ * Real.log 2 * n - θ * n + ε / 2 * k + Real.log β := by
        rw [hc, hd, hK]; field_simp; ring
      rw [e]
      nlinarith [hω, hmk]
  -- the union bound over the dyadic subsquares of all levels
  have hN : P {ω | ¬ IsEuclideanLengthMetric (𝔇 (hC' ω))} = 0 :=
    ae_iff.1 (h𝔇.ae_isEuclideanLengthMetric_self hG')
  refine (measure_mono hsub).trans ?_
  calc _ ≤ P {ω | ¬ IsEuclideanLengthMetric (𝔇 (hC' ω))} + ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n),
        ∑ j ∈ Finset.range (2 ^ n), P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) (0 + i * (1 / 2 ^ n))
          (0 + (i + 1) * (1 / 2 ^ n)) (0 + j * (1 / 2 ^ n)) (0 + (j + 1) * (1 / 2 ^ n)) (l k n)} :=
        (measure_union_le _ _).trans (add_le_add le_rfl ((measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun n => (measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _))))
    _ ≤ ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
          (p (n + m k) + P {ω | c * n + d * k - K ≤
            hcirc ω (1 / 2 ^ n) ⟨0 + i * (1 / 2 ^ n), 0 + j * (1 / 2 ^ n)⟩}) := by
        rw [hN, zero_add]
        exact ENNReal.tsum_le_tsum fun n => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq n i j
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [ENNReal.tsum_add]
        congr 1
        refine tsum_congr fun n => ?_
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, ← pow_mul, mul_comm n 2, pow_mul]
        norm_num

end LatticeProb.LQG
