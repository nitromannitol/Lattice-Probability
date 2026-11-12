import LatticeProb.LQG.InternalMetricDyadicSmallWeyl

/-!
# Small internal diameters of the closed dyadic subsquares inside chosen cells of a coarser level

Let `S = [a, a + s] × [b, b + s]` with `s > 0`. For `K ≤ m`, the closed dyadic subsquare of `S` of level `m` with
indices `(i, j)` is the closed dyadic subsquare of level `m - K` with indices `(i mod 2^{m-K}, j mod 2^{m-K})` of the
level-`K` cell of `S` with indices `(⌊i / 2^{m-K}⌋, ⌊j / 2^{m-K}⌋)` (`closedDyadicSubsquare_eq_of_le`).

Let `E = e^{ξ f} · D_h` be a Weyl scaling (Gwynne-Miller, arXiv:1905.00383, (1.8)) of a γ-LQG metric `D_h` by a
deterministic weight `f`, and let `T` be a finite set of level-`K` cells on each of which `f` is continuous (for instance
the cells of `S` not containing `0` when `f = -α log |·|`). Then the probability that some level-`m` subsquare lying in a
cell of `T` has `E`-internal diameter larger than a fixed threshold tends to `0` as `m → ∞`
(`IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn_cells`):
apply the single-square statement to each cell of `T` and sum over the finitely many cells.

## Main statements

* `LatticeProb.LQG.closedDyadicSubsquare_eq_of_le`: nesting of the closed dyadic subsquares.
* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn_cells`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

/-- **Nesting of the closed dyadic subsquares.** For `K ≤ m`, the closed dyadic subsquare of `[a, a + s] × [b, b + s]`
of level `m` with indices `(i, j)` is the closed dyadic subsquare of level `m - K` with indices
`(i mod 2^{m-K}, j mod 2^{m-K})` of the level-`K` cell with indices `(⌊i / 2^{m-K}⌋, ⌊j / 2^{m-K}⌋)`. -/
theorem closedDyadicSubsquare_eq_of_le (a b s : ℝ) {K m : ℕ} (hKm : K ≤ m) (i j : ℕ) :
    closedDyadicSubsquare a b s m i j =
      closedDyadicSubsquare (a + ((i / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K))
        (b + ((j / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K)) (s / 2 ^ K) (m - K)
        (i % 2 ^ (m - K)) (j % 2 ^ (m - K)) := by
  have hpow : (2 : ℝ) ^ m = 2 ^ K * 2 ^ (m - K) := by rw [← pow_add, Nat.add_sub_cancel' hKm]
  have hs : s / 2 ^ K / 2 ^ (m - K) = s / 2 ^ m := by rw [hpow, div_div]
  have key : ∀ n : ℕ, (n : ℝ) * (s / 2 ^ m) =
      ((n / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K) + ((n % 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ m) := by
    intro n
    have h' : (n : ℝ) = (2 : ℝ) ^ (m - K) * ((n / 2 ^ (m - K) : ℕ) : ℝ) + ((n % 2 ^ (m - K) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n (2 ^ (m - K))).symm
    rw [h', hpow]
    field_simp
  have e1 : ∀ (c : ℝ) (n : ℕ), c + (n : ℝ) * (s / 2 ^ m) =
      c + ((n / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K) + ((n % 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ m) := by
    intro c n
    rw [key n]
    ring
  have e2 : ∀ (c : ℝ) (n : ℕ), c + ((n : ℝ) + 1) * (s / 2 ^ m) =
      c + ((n / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K) + (((n % 2 ^ (m - K) : ℕ) : ℝ) + 1) * (s / 2 ^ m) := by
    intro c n
    rw [add_mul, key n]
    ring
  unfold closedDyadicSubsquare
  rw [hs, e1 a i, e2 a i, e1 b j, e2 b j]

/-- The closed dyadic subsquare of level `K` with indices `(I, J)` as a product of two closed intervals of length
`s / 2^K`. -/
theorem closedDyadicSubsquare_eq_reProdIm (a b s : ℝ) (K I J : ℕ) :
    closedDyadicSubsquare a b s K I J =
      Icc (a + I * (s / 2 ^ K)) (a + I * (s / 2 ^ K) + s / 2 ^ K) ×ℂ
        Icc (b + J * (s / 2 ^ K)) (b + J * (s / 2 ^ K) + s / 2 ^ K) := by
  simp only [closedDyadicSubsquare, add_mul, one_mul, add_assoc]

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Uniformly small internal diameters of the closed dyadic subsquares inside chosen coarse cells.** Under the
hypotheses of `IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn`,
let `K : ℕ` and let `T` be a finite set of index pairs such that the weight `f` is continuous on the level-`K` closed
dyadic subsquare of `S = [a, a + s] × [b, b + s]` with indices `q` for every `q ∈ T`. Then for every `ε > 0`, the
(outer) probability that some closed dyadic subsquare `S_{m,i,j}` of level `m` whose level-`K` cell
`(⌊i / 2^{m-K}⌋, ⌊j / 2^{m-K}⌋)` belongs to `T` contains two points at `E`-internal distance in `S_{m,i,j}` larger than
`ε` tends to `0` as `m → ∞`. -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn_cells
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ)
    {θ δ : ℝ} (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {E : Ω → ℂ → ℂ → ℝ} {f : ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ f x y)
    (K : ℕ) (T : Finset (ℕ × ℕ)) (hf : ∀ q ∈ T, ContinuousOn f (closedDyadicSubsquare a b s K q.1 q.2))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m →
      (i / 2 ^ (m - K), j / 2 ^ (m - K)) ∈ T →
      ∀ z ∈ closedDyadicSubsquare a b s m i j, ∀ w ∈ closedDyadicSubsquare a b s m i j,
        internalMetric (E ω) (closedDyadicSubsquare a b s m i j) z w ≤ ENNReal.ofReal ε}) atTop (𝓝 0) := by
  have ht : 0 < s / 2 ^ K := by positivity
  have hcell : ∀ q ∈ T, Tendsto (fun m : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ (m - K) → j < 2 ^ (m - K) →
      ∀ z ∈ closedDyadicSubsquare (a + q.1 * (s / 2 ^ K)) (b + q.2 * (s / 2 ^ K)) (s / 2 ^ K) (m - K) i j,
      ∀ w ∈ closedDyadicSubsquare (a + q.1 * (s / 2 ^ K)) (b + q.2 * (s / 2 ^ K)) (s / 2 ^ K) (m - K) i j,
        internalMetric (E ω)
          (closedDyadicSubsquare (a + q.1 * (s / 2 ^ K)) (b + q.2 * (s / 2 ^ K)) (s / 2 ^ K) (m - K) i j) z w ≤
          ENNReal.ofReal ε}) atTop (𝓝 0) := by
    intro q hq
    have hfq := hf q hq
    rw [closedDyadicSubsquare_eq_reProdIm] at hfq
    exact (h𝔇.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn hG ht
      hξ hθ hδ huniv hp hE hfq hε).comp (tendsto_sub_atTop_nat K)
  have hsum := tendsto_finsetSum T hcell
  rw [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop K] with m hm
  refine (measure_mono ?_).trans (measure_biUnion_finset_le T _)
  intro ω hω
  by_contra hcon
  apply hω
  intro i j hi hj hT
  have hq : ω ∉ {ω | ¬ ∀ i' j' : ℕ, i' < 2 ^ (m - K) → j' < 2 ^ (m - K) →
      ∀ z ∈ closedDyadicSubsquare (a + ((i / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K))
        (b + ((j / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K)) (s / 2 ^ K) (m - K) i' j',
      ∀ w ∈ closedDyadicSubsquare (a + ((i / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K))
        (b + ((j / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K)) (s / 2 ^ K) (m - K) i' j',
        internalMetric (E ω) (closedDyadicSubsquare (a + ((i / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K))
          (b + ((j / 2 ^ (m - K) : ℕ) : ℝ) * (s / 2 ^ K)) (s / 2 ^ K) (m - K) i' j') z w ≤
          ENNReal.ofReal ε} :=
    fun h => hcon (mem_iUnion₂.2 ⟨_, hT, h⟩)
  simp only [mem_ofPred_eq, not_not] at hq
  rw [closedDyadicSubsquare_eq_of_le a b s hm i j]
  exact hq _ _ (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))

end LatticeProb.LQG
