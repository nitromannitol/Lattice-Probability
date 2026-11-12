import LatticeProb.LQG.HalfCrossingScaling
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost sure finiteness of the internal diameter of a closed square from crossing tails

The probabilistic assembly in the proof of Dubédat-Falconet-Gwynne-Pfeffer-Sun (arXiv:1905.00380, Proposition 3.10).
Let `S = [a, a + s] × [b, b + s]` and let `S_{n,i,j}` (`i, j < 2ⁿ`) be its closed dyadic subsquares of level `n`. For a
random length metric `D`, suppose that

* almost surely each `S_{n,i,j}` has hard crossings of its four halves of finite `D`-length, and
* the probability that `S_{n,i,j}` has no hard crossings of its halves of `D`-length at most `l n` is at most `q n i j`,
  where `∑ₙ l n < ∞` and `∑ₙ ∑_{i,j < 2ⁿ} q n i j < ∞`.

Then almost surely the internal diameter of `S` is finite: the first Borel-Cantelli lemma, summed over the `4ⁿ` subsquares
of each level, gives the short half crossings of every subsquare of every level `n ≥ N` for a random `N`, and the
deterministic multiscale bound `IsEuclideanLengthMetric.exists_internalMetric_le_ofReal_of_hasShortHalfCrossings`
concludes.

For a γ-LQG metric the tail of each subsquare is bounded through the coordinate change (axiom IV) by the tail of the unit
square for the recentred field plus the tail of the scaling factor `e^{ξ (h_r(z) + Q log r)}`
(`IsLQGMetric.measure_not_hasShortHalfCrossings_dyadic_le`).

## Main statements

* `LatticeProb.ae_eventually_forall_dyadic_of_tsum_sum`: Borel-Cantelli for events indexed by dyadic squares, with a bound
  for each square.
* `LatticeProb.LQG.ae_exists_internalMetric_closedSquare_le_of_tsum`: the assembly for a random length metric.
* `LatticeProb.LQG.IsLQGMetric.ae_exists_internalMetric_closedSquare_le`: the assembly for a γ-LQG metric, from summable
  tails of the unit-square half crossings of the recentred fields and of the scaling factors.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb

/-- **Borel-Cantelli for events indexed by dyadic squares, with a bound for each square.** If the exceptional sets
`(E n i j)ᶜ` (`i, j < 2ⁿ`) have measure at most `q n i j` and `∑ₙ ∑_{i,j < 2ⁿ} q n i j < ∞`, then almost surely all the
events `E n i j` hold for all large enough `n`. -/
theorem ae_eventually_forall_dyadic_of_tsum_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ℕ → ℕ → ℕ → Set Ω) (q : ℕ → ℕ → ℕ → ℝ≥0∞)
    (hq : ∀ n i j, i < 2 ^ n → j < 2 ^ n → μ (E n i j)ᶜ ≤ q n i j)
    (hsum : ∑' n, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), q n i j ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∃ N, ∀ n ≥ N, ∀ i j, i < 2 ^ n → j < 2 ^ n → ω ∈ E n i j := by
  set B : ℕ → Set Ω := fun n =>
    ⋃ i ∈ Finset.range (2 ^ n), ⋃ j ∈ Finset.range (2 ^ n), (E n i j)ᶜ with hB
  have hBn : ∀ n, μ (B n) ≤ ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), q n i j := by
    intro n
    calc μ (B n)
        ≤ ∑ i ∈ Finset.range (2 ^ n), μ (⋃ j ∈ Finset.range (2 ^ n), (E n i j)ᶜ) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), μ ((E n i j)ᶜ) :=
          Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), q n i j :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
            hq n i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)
  have hfin : ∑' n, μ (B n) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hBn)
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, fun n hn i j hi hj => ?_⟩
  by_contra hcon
  refine hN n hn ?_
  simp only [hB, Set.mem_iUnion]
  exact ⟨i, Finset.mem_range.2 hi, j, Finset.mem_range.2 hj, hcon⟩

namespace LQG

/-- **Almost sure finiteness of the internal diameter of a closed square** (Dubédat-Falconet-Gwynne-Pfeffer-Sun,
Proposition 3.10, assembly). Let `D` be a random metric which is almost surely a length metric inducing the Euclidean
topology, and `S = [a, a + s] × [b, b + s]`. Suppose that almost surely every closed dyadic subsquare `S_{n,i,j}` of `S`
has hard crossings of its halves of finite `D`-length, and that the probability that `S_{n,i,j}` has no hard crossings
of its halves of `D`-length at most `l n` is at most `q n i j`, with `∑ₙ l n < ∞` and `∑ₙ ∑_{i,j < 2ⁿ} q n i j < ∞`.
Then almost surely there is a real `A` with `D(z, w; S) ≤ A` for all `z, w ∈ S`. -/
theorem ae_exists_internalMetric_closedSquare_le_of_tsum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ᵐ ω ∂μ, IsEuclideanLengthMetric (D ω)) {a b s : ℝ} (hs : 0 < s)
    (hfin : ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n → ∀ᵐ ω ∂μ, ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      HasShortHalfCrossings (D ω) (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) (b + j * (s / 2 ^ n))
        (b + (j + 1) * (s / 2 ^ n)) L)
    (l : ℕ → ℝ≥0∞) (hl : ∑' n, l n ≠ ⊤) (q : ℕ → ℕ → ℕ → ℝ≥0∞)
    (hq : ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      μ {ω | ¬ HasShortHalfCrossings (D ω) (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) (b + j * (s / 2 ^ n))
        (b + (j + 1) * (s / 2 ^ n)) (l n)} ≤ q n i j)
    (hsum : ∑' n, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), q n i j ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∃ A : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ w ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric (D ω) (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ ENNReal.ofReal A := by
  have hfin' : ∀ᵐ ω ∂μ, ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n → ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      HasShortHalfCrossings (D ω) (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) (b + j * (s / 2 ^ n))
        (b + (j + 1) * (s / 2 ^ n)) L := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases hi : i < 2 ^ n
    · by_cases hj : j < 2 ^ n
      · filter_upwards [hfin n i j hi hj] with ω h _ _ using h
      · exact Eventually.of_forall fun _ _ hj' => absurd hj' hj
    · exact Eventually.of_forall fun _ hi' => absurd hi' hi
  have hBC := ae_eventually_forall_dyadic_of_tsum_sum μ
    (fun n i j => {ω | HasShortHalfCrossings (D ω) (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n))
      (b + j * (s / 2 ^ n)) (b + (j + 1) * (s / 2 ^ n)) (l n)}) q
    (fun n i j hi hj => by simpa only [Set.compl_ofPred] using hq n i j hi hj) hsum
  filter_upwards [hD, hfin', hBC] with ω hDω hf hN
  obtain ⟨N, hN⟩ := hN
  exact hDω.exists_internalMetric_le_ofReal_of_hasShortHalfCrossings hs
    (fun n _ i j hi hj => hf n i j hi hj) l hl (fun n hn i j hi hj => hN n hn i j hi hj)

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Axiom I for the metric of the whole-plane GFF itself: almost surely `D_h` is a length metric inducing the Euclidean
topology. -/
theorem IsLQGMetric.ae_isEuclideanLengthMetric_self (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
  have hA := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) hG (fun _ => continuous_const)
    (fun _ => measurable_const)
  filter_upwards [hA.ae_isEuclideanLengthMetric] with ω hω
  have h0 : addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := by
    funext φ
    simp [addFunPairing]
  rwa [h0] at hω

/-- **Almost sure finiteness of the internal diameter of a closed square for the γ-LQG metric**
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, Proposition 3.10, assembly). Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF and
`S = [a, a + s] × [b, b + s]`; write `r_n = s / 2ⁿ` and `z_{n,i,j} = (a + i r_n, b + j r_n)`. Suppose that almost surely
every closed dyadic subsquare of `S` has hard crossings of its halves of finite `D_h`-length, and that for sequences
`A n`, `l n` with `∑ₙ l n < ∞`,
* `∑ₙ ∑_{i,j < 2ⁿ} P[the unit square has no hard crossings of its halves of length at most A n for the metric of the
  recentred field h(r_n · + z_{n,i,j}) - h_{r_n}(z_{n,i,j})] < ∞`, and
* `∑ₙ ∑_{i,j < 2ⁿ} P[e^{ξ (h_{r_n}(z_{n,i,j}) + Q log r_n)} A n > l n] < ∞`.
Then almost surely there is a real `A` with `D_h(z, w; S) ≤ A` for all `z, w ∈ S`. -/
theorem IsLQGMetric.ae_exists_internalMetric_closedSquare_le (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s)
    (hfin : ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n → ∀ᵐ ω ∂P, ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      HasShortHalfCrossings (𝔇 (hC ω)) (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) (b + j * (s / 2 ^ n))
        (b + (j + 1) * (s / 2 ^ n)) L)
    (A l : ℕ → ℝ≥0∞) (hl : ∑' n, l n ≠ ⊤)
    (hunit : ∑' n, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | ¬ HasShortHalfCrossings
        (𝔇 (recentredPairing hC hcirc (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ ω)) 0 1 0 1 (A n)} ≠ ⊤)
    (hscale : ∑' n, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | l n < ENNReal.ofReal (Real.exp (ξ * (hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ +
        lqgQ γ * Real.log (s / 2 ^ n)))) * A n} ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ w ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric (𝔇 (hC ω)) (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ ENNReal.ofReal A := by
  refine ae_exists_internalMetric_closedSquare_le_of_tsum (h𝔇.ae_isEuclideanLengthMetric_self hG) hs hfin l hl
    (fun n i j =>
      P {ω | ¬ HasShortHalfCrossings
        (𝔇 (recentredPairing hC hcirc (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ ω)) 0 1 0 1 (A n)} +
      P {ω | l n < ENNReal.ofReal (Real.exp (ξ * (hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ +
        lqgQ γ * Real.log (s / 2 ^ n)))) * A n})
    (fun n i j _ _ => h𝔇.measure_not_hasShortHalfCrossings_dyadic_le hG hs n i j (A n) (l n)) ?_
  simp only [Finset.sum_add_distrib]
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.2 ⟨hunit, hscale⟩

end LQG

end LatticeProb
