import LatticeProb.LQG.InternalMetricChaining

/-!
# Chaining to a point over a sequence of shells

Let `D` be a Euclidean length metric, `C` a closed bounded set and `z ∈ C`. Let `R₀, R₁, …` be subsets of `C` such that
consecutive sets meet and `Rₖ` converges to `z` (eventually inside every ball around `z`), and suppose that the internal
diameter of `Rₖ` is at most `Lₖ`. Then every point of `Rₘ` is at internal distance in `C` at most
`Lₘ + ∑_{k ≥ 0} L_{m + k + 1}` from `z`, so the internal diameter in `C` of `{z} ∪ ⋃ₖ Rₖ` is at most `4 ∑ₖ Lₖ`.

This is the deterministic part of the proof that the metric of a whole-plane GFF plus a logarithmic singularity at `0`
has finite diameter near `0` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.17, last
paragraph of the proof): `Rₖ` is the dyadic shell of scale `2⁻ᵏ` around `z = 0`, and the `Lₖ` are summable almost surely
by the Borel-Cantelli lemma. The limit point `z` may lie on the frontier of `C`.

## Main statements

* `LatticeProb.LQG.IsEuclideanLengthMetric.internalMetric_le_of_shells`: `D(u, z; C) ≤ Lₘ + ∑ₖ L_{m+k+1}` for `u ∈ Rₘ`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.internalMetric_le_two_mul_tsum_of_shells`: `D(u, z; C) ≤ 2 ∑ₖ Lₖ`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.internalMetric_le_four_mul_tsum_of_shells`: internal diameter in `C` of
  `{z} ∪ ⋃ₖ Rₖ` at most `4 ∑ₖ Lₖ`.
-/

open Filter Set Topology
open scoped ENNReal

namespace LatticeProb.LQG

/-- **Chaining to a limit point over shells.** Let `D` be a Euclidean length metric, `C` a closed bounded set, `z ∈ C`,
and `Rₖ ⊆ C` sets with `Rₖ ∩ Rₖ₊₁ ≠ ∅` which are eventually inside every ball around `z`. If `D(u, v; Rₖ) ≤ Lₖ` for
all `u, v ∈ Rₖ`, then `D(u, z; C) ≤ Lₘ + ∑_{k ≥ 0} L_{m+k+1}` for every `u ∈ Rₘ`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_shells {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {C : Set ℂ} (hC : IsClosed C) (hCb : Bornology.IsBounded C) {z : ℂ} (hz : z ∈ C) {R : ℕ → Set ℂ}
    (hRC : ∀ k, R k ⊆ C) (hmeet : ∀ k, (R k ∩ R (k + 1)).Nonempty)
    (hlim : ∀ ε > 0, ∀ᶠ k in atTop, R k ⊆ Metric.ball z ε) {L : ℕ → ℝ≥0∞}
    (hL : ∀ k, ∀ u ∈ R k, ∀ v ∈ R k, internalMetric D (R k) u v ≤ L k) {m : ℕ} {u : ℂ} (hu : u ∈ R m) :
    internalMetric D C u z ≤ L m + ∑' k, L (m + k + 1) := by
  choose x hx using hmeet
  have hxlim : Tendsto x atTop (𝓝 z) :=
    Metric.tendsto_nhds.2 fun ε hε => (hlim ε hε).mono fun k hk => hk (hx k).1
  have hy : Tendsto (fun n => x (m + n)) atTop (𝓝 z) :=
    hxlim.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => hn.trans (Nat.le_add_left n m)⟩)
  have hstep : ∀ n, internalMetric D C (x (m + n)) (x (m + (n + 1))) ≤ L (m + n + 1) := fun n =>
    (internalMetric_anti D (hRC (m + n + 1)) _ _).trans
      (hL (m + n + 1) _ (hx (m + n)).2 _ (hx (m + n + 1)).1)
  have h2 : internalMetric D C (x m) z ≤ ∑' k, L (m + k + 1) :=
    hD.internalMetric_le_tsum_of_tendsto_of_isClosed_of_le hC hCb (x := fun n => x (m + n))
      (hRC m (hx m).1) hz hy hstep
  have h1 : internalMetric D C u (x m) ≤ L m :=
    (internalMetric_anti D (hRC m) _ _).trans (hL m u hu (x m) (hx m).1)
  exact (hD.internalMetric_triangle C u (x m) z).trans (add_le_add h1 h2)

/-- **Chaining to a limit point over shells**, summed form: `D(u, z; C) ≤ 2 ∑ₖ Lₖ` for every `u ∈ Rₘ`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_two_mul_tsum_of_shells {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {C : Set ℂ} (hC : IsClosed C) (hCb : Bornology.IsBounded C) {z : ℂ}
    (hz : z ∈ C) {R : ℕ → Set ℂ} (hRC : ∀ k, R k ⊆ C) (hmeet : ∀ k, (R k ∩ R (k + 1)).Nonempty)
    (hlim : ∀ ε > 0, ∀ᶠ k in atTop, R k ⊆ Metric.ball z ε) {L : ℕ → ℝ≥0∞}
    (hL : ∀ k, ∀ u ∈ R k, ∀ v ∈ R k, internalMetric D (R k) u v ≤ L k) {m : ℕ} {u : ℂ} (hu : u ∈ R m) :
    internalMetric D C u z ≤ 2 * ∑' k, L k := by
  refine (hD.internalMetric_le_of_shells hC hCb hz hRC hmeet hlim hL hu).trans ?_
  rw [two_mul]
  refine add_le_add (ENNReal.le_tsum m) ?_
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun k => m + k + 1)
    (fun a b hab => by simpa using hab) L

/-- **Internal diameter of a set chained to a limit point over shells.** Under the hypotheses of
`IsEuclideanLengthMetric.internalMetric_le_of_shells`, `D(u, v; C) ≤ 4 ∑ₖ Lₖ` for all `u, v ∈ {z} ∪ ⋃ₖ Rₖ`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_four_mul_tsum_of_shells {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {C : Set ℂ} (hC : IsClosed C) (hCb : Bornology.IsBounded C) {z : ℂ}
    (hz : z ∈ C) {R : ℕ → Set ℂ} (hRC : ∀ k, R k ⊆ C) (hmeet : ∀ k, (R k ∩ R (k + 1)).Nonempty)
    (hlim : ∀ ε > 0, ∀ᶠ k in atTop, R k ⊆ Metric.ball z ε) {L : ℕ → ℝ≥0∞}
    (hL : ∀ k, ∀ u ∈ R k, ∀ v ∈ R k, internalMetric D (R k) u v ≤ L k) :
    ∀ u ∈ insert z (⋃ k, R k), ∀ v ∈ insert z (⋃ k, R k), internalMetric D C u v ≤ 4 * ∑' k, L k := by
  have key : ∀ w ∈ ⋃ k, R k, internalMetric D C w z ≤ 2 * ∑' k, L k := fun w hw => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hw
    exact hD.internalMetric_le_two_mul_tsum_of_shells hC hCb hz hRC hmeet hlim hL hk
  have key' : ∀ w ∈ ⋃ k, R k, internalMetric D C z w ≤ 2 * ∑' k, L k := fun w hw => by
    rw [hD.internalMetric_symm]; exact key w hw
  have h24 : 2 * ∑' k, L k ≤ 4 * ∑' k, L k := by gcongr; norm_num
  have hsum : ∀ a b, internalMetric D C a z ≤ 2 * ∑' k, L k → internalMetric D C z b ≤ 2 * ∑' k, L k →
      internalMetric D C a b ≤ 4 * ∑' k, L k := fun a b ha hb =>
    (hD.internalMetric_triangle C a z b).trans ((add_le_add ha hb).trans_eq (by ring))
  obtain ⟨y, hy, -⟩ := hmeet 0
  have hyU : y ∈ ⋃ k, R k := mem_iUnion.2 ⟨0, hy⟩
  intro u hu v hv
  rcases mem_insert_iff.1 hu with huz | hu <;> rcases mem_insert_iff.1 hv with hvz | hv
  · rw [huz, hvz]
    exact (hD.internalMetric_triangle C z y z).trans
      ((add_le_add (key' y hyU) (key y hyU)).trans_eq (by ring))
  · rw [huz]; exact (key' v hv).trans h24
  · rw [hvz]; exact (key u hu).trans h24
  · exact hsum u v (key u hu) (key' v hv)

end LatticeProb.LQG
