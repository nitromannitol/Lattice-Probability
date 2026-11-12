import Mathlib
import LatticeProb.LQG.InternalMetricStripCrossing
import LatticeProb.LQG.InternalMetricSquareTailUniform

/-!
# Hard half-crossings of the unit square from internal distances between compact sets

Proposition 3.1 of Dubédat-Falconet-Gwynne-Pfeffer-Sun (2020) bounds the internal distance
`D_h(K₁, K₂; U) = inf_{z ∈ K₁, w ∈ K₂} D_h(z, w; U)` between two disjoint compact connected sets `K₁, K₂` of an open
set `U`. The proof of their Proposition 3.10 needs hard crossings of the closed half rectangles of a square instead.
These follow from Proposition 3.1 for a long open strip around the half rectangle, by trimming: a path in the strip
`(-1, 2) × (0, 1/2)` from `{-1/2} × [1/8, 3/8]` to `{3/2} × [1/8, 3/8]` contains a left-right crossing of the closed
rectangle `[0, 1] × [0, 1/2]` that is no longer (`exists_leftRightCrossing_pathLength_le`).

* `internalSetDist`: the internal distance `D(K₁, K₂; U)` between two sets;
* `horizontalCrossingDist`, `verticalCrossingDist`: the internal distances of the strip configurations around the
  bottom (top) and left (right) halves of the unit square;
* `hasShortHalfCrossings_zero_one_of_crossingDist_lt`: if the four strip distances are `< L`, the unit square has
  hard half-crossings of `D`-length at most `L`;
* `measure_not_hasShortHalfCrossings_zero_one_le`: the corresponding union bound for a random `D`;
* `IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_crossingDistTail`: the almost sure finiteness of the
  internal diameter of a closed square from a uniform tail bound for the four strip distances.
-/

open Set MeasureTheory LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- The internal distance `D(K₁, K₂; U) = inf_{z ∈ K₁, w ∈ K₂} D(z, w; U)` between two sets `K₁, K₂`, for the
internal metric of `U`. -/
noncomputable def internalSetDist (D : ℂ → ℂ → ℝ) (U K₁ K₂ : Set ℂ) : ℝ≥0∞ :=
  ⨅ z ∈ K₁, ⨅ w ∈ K₂, internalMetric D U z w

/-- If `D(K₁, K₂; U) < L`, there is a path in `U` from a point of `K₁` to a point of `K₂` of `D`-length `< L`. -/
theorem exists_path_of_internalSetDist_lt {D : ℂ → ℂ → ℝ} {U K₁ K₂ : Set ℂ} {L : ℝ≥0∞}
    (h : internalSetDist D U K₁ K₂ < L) :
    ∃ z ∈ K₁, ∃ w ∈ K₂, ∃ P : Path z w, (∀ t, P t ∈ U) ∧ pathLength D P < L := by
  simp only [internalSetDist, internalMetric, iInf_lt_iff] at h
  obtain ⟨z, hz, w, hw, P, hP, hlt⟩ := h
  exact ⟨z, hz, w, hw, P, hP, hlt⟩

/-- A left-right crossing of the closed rectangle `[x₀, x₁] × [y₀, y₁]` of `D`-length at most `L`, from a bound
`D(K₁, K₂; U) < L` where `U` lies in the strip `y₀ ≤ Im z ≤ y₁`, `K₁` in `{Re z ≤ x₀}` and `K₂` in `{x₁ ≤ Re z}`. -/
theorem exists_leftRightCrossing_of_internalSetDist_lt (D : ℂ → ℂ → ℝ) {U K₁ K₂ : Set ℂ} {x₀ x₁ y₀ y₁ : ℝ}
    (hx : x₀ ≤ x₁) (hU : ∀ z ∈ U, z.im ∈ Icc y₀ y₁) (hK₁ : ∀ z ∈ K₁, z.re ≤ x₀) (hK₂ : ∀ w ∈ K₂, x₁ ≤ w.re)
    {L : ℝ≥0∞} (h : internalSetDist D U K₁ K₂ < L) :
    ∃ (u v : ℂ) (P : Path u v), IsLeftRightCrossing x₀ x₁ y₀ y₁ P ∧ pathLength D P ≤ L := by
  obtain ⟨z, hz, w, hw, P, hP, hlt⟩ := exists_path_of_internalSetDist_lt h
  obtain ⟨u, v, Q, hQ, hle⟩ :=
    exists_leftRightCrossing_pathLength_le D hx P (fun t => hU _ (hP t)) (hK₁ z hz) (hK₂ w hw)
  exact ⟨u, v, Q, hQ, hle.trans hlt.le⟩

/-- A top-bottom crossing of the closed rectangle `[x₀, x₁] × [y₀, y₁]` of `D`-length at most `L`, from a bound
`D(K₁, K₂; U) < L` where `U` lies in the strip `x₀ ≤ Re z ≤ x₁`, `K₁` in `{y₁ ≤ Im z}` and `K₂` in `{Im z ≤ y₀}`. -/
theorem exists_topBottomCrossing_of_internalSetDist_lt (D : ℂ → ℂ → ℝ) {U K₁ K₂ : Set ℂ} {x₀ x₁ y₀ y₁ : ℝ}
    (hy : y₀ ≤ y₁) (hU : ∀ z ∈ U, z.re ∈ Icc x₀ x₁) (hK₁ : ∀ z ∈ K₁, y₁ ≤ z.im) (hK₂ : ∀ w ∈ K₂, w.im ≤ y₀)
    {L : ℝ≥0∞} (h : internalSetDist D U K₁ K₂ < L) :
    ∃ (u v : ℂ) (P : Path u v), IsTopBottomCrossing x₀ x₁ y₀ y₁ P ∧ pathLength D P ≤ L := by
  obtain ⟨z, hz, w, hw, P, hP, hlt⟩ := exists_path_of_internalSetDist_lt h
  obtain ⟨u, v, Q, hQ, hle⟩ :=
    exists_topBottomCrossing_pathLength_le D hy P (fun t => hU _ (hP t)) (hK₁ z hz) (hK₂ w hw)
  exact ⟨u, v, Q, hQ, hle.trans hlt.le⟩

/-- The internal distance `D(K₋, K₊; U)` of the horizontal strip configuration at height `y₀`:
`U = (-1, 2) × (y₀, y₀ + 1/2)`, `K₋ = {-1/2} × [y₀ + 1/8, y₀ + 3/8]`, `K₊ = {3/2} × [y₀ + 1/8, y₀ + 3/8]`. These are
disjoint compact connected non-singleton subsets of the open set `U`. -/
noncomputable def horizontalCrossingDist (D : ℂ → ℂ → ℝ) (y₀ : ℝ) : ℝ≥0∞ :=
  internalSetDist D (Ioo (-1) 2 ×ℂ Ioo y₀ (y₀ + 1 / 2)) (({-1 / 2} : Set ℝ) ×ℂ Icc (y₀ + 1 / 8) (y₀ + 3 / 8))
    (({3 / 2} : Set ℝ) ×ℂ Icc (y₀ + 1 / 8) (y₀ + 3 / 8))

/-- The internal distance `D(K₊, K₋; U)` of the vertical strip configuration at abscissa `x₀`:
`U = (x₀, x₀ + 1/2) × (-1, 2)`, `K₊ = [x₀ + 1/8, x₀ + 3/8] × {3/2}`, `K₋ = [x₀ + 1/8, x₀ + 3/8] × {-1/2}`. -/
noncomputable def verticalCrossingDist (D : ℂ → ℂ → ℝ) (x₀ : ℝ) : ℝ≥0∞ :=
  internalSetDist D (Ioo x₀ (x₀ + 1 / 2) ×ℂ Ioo (-1) 2) (Icc (x₀ + 1 / 8) (x₀ + 3 / 8) ×ℂ ({3 / 2} : Set ℝ))
    (Icc (x₀ + 1 / 8) (x₀ + 3 / 8) ×ℂ ({-1 / 2} : Set ℝ))

/-- A left-right crossing of `[0, 1] × [y₀, y₀ + 1/2]` of `D`-length at most `L` from `horizontalCrossingDist D y₀ < L`. -/
theorem exists_leftRightCrossing_of_horizontalCrossingDist_lt (D : ℂ → ℂ → ℝ) {y₀ : ℝ} {L : ℝ≥0∞}
    (h : horizontalCrossingDist D y₀ < L) :
    ∃ (u v : ℂ) (P : Path u v), IsLeftRightCrossing 0 1 y₀ (y₀ + 1 / 2) P ∧ pathLength D P ≤ L := by
  refine exists_leftRightCrossing_of_internalSetDist_lt D zero_le_one (fun z hz => ?_) (fun z hz => ?_)
    (fun w hw => ?_) h
  · exact Ioo_subset_Icc_self (Complex.mem_reProdIm.1 hz).2
  · rw [(Complex.mem_reProdIm.1 hz).1]; norm_num
  · rw [(Complex.mem_reProdIm.1 hw).1]; norm_num

/-- A top-bottom crossing of `[x₀, x₀ + 1/2] × [0, 1]` of `D`-length at most `L` from `verticalCrossingDist D x₀ < L`. -/
theorem exists_topBottomCrossing_of_verticalCrossingDist_lt (D : ℂ → ℂ → ℝ) {x₀ : ℝ} {L : ℝ≥0∞}
    (h : verticalCrossingDist D x₀ < L) :
    ∃ (u v : ℂ) (P : Path u v), IsTopBottomCrossing x₀ (x₀ + 1 / 2) 0 1 P ∧ pathLength D P ≤ L := by
  refine exists_topBottomCrossing_of_internalSetDist_lt D zero_le_one (fun z hz => ?_) (fun z hz => ?_)
    (fun w hw => ?_) h
  · exact Ioo_subset_Icc_self (Complex.mem_reProdIm.1 hz).1
  · rw [(Complex.mem_reProdIm.1 hz).2]; norm_num
  · rw [(Complex.mem_reProdIm.1 hw).2]; norm_num

/-- **Hard half-crossings of the unit square from the strip distances.** If the internal distances of the four strip
configurations around the halves of `[0, 1]²` are `< L`, then `[0, 1]²` has hard crossings of its four halves of
`D`-length at most `L`. -/
theorem hasShortHalfCrossings_zero_one_of_crossingDist_lt (D : ℂ → ℂ → ℝ) {L : ℝ≥0∞}
    (hbot : horizontalCrossingDist D 0 < L) (htop : horizontalCrossingDist D (1 / 2) < L)
    (hleft : verticalCrossingDist D 0 < L) (hright : verticalCrossingDist D (1 / 2) < L) :
    HasShortHalfCrossings D 0 1 0 1 L := by
  have e₁ : ((0 : ℝ) + 1) / 2 = 0 + 1 / 2 := by norm_num
  have e₂ : (1 : ℝ) = 1 / 2 + 1 / 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e₁]; exact exists_leftRightCrossing_of_horizontalCrossingDist_lt D hbot
  · obtain ⟨u, v, P, hP, hl⟩ := exists_leftRightCrossing_of_horizontalCrossingDist_lt D htop
    refine ⟨u, v, P, ?_, hl⟩
    rw [show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num]
    convert hP using 2
  · rw [e₁]; exact exists_topBottomCrossing_of_verticalCrossingDist_lt D hleft
  · obtain ⟨u, v, P, hP, hl⟩ := exists_topBottomCrossing_of_verticalCrossingDist_lt D hright
    refine ⟨u, v, P, ?_, hl⟩
    rw [show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num]
    convert hP using 2

/-- **Union bound.** For a random function `D`, the probability that `[0, 1]²` has no hard half-crossings of
`D`-length at most `L` is at most the sum of the probabilities that the four strip distances are `≥ L`. -/
theorem measure_not_hasShortHalfCrossings_zero_one_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (L : ℝ≥0∞) :
    μ {ω | ¬ HasShortHalfCrossings (D ω) 0 1 0 1 L} ≤
      μ {ω | L ≤ horizontalCrossingDist (D ω) 0} + μ {ω | L ≤ horizontalCrossingDist (D ω) (1 / 2)} +
        μ {ω | L ≤ verticalCrossingDist (D ω) 0} + μ {ω | L ≤ verticalCrossingDist (D ω) (1 / 2)} := by
  set A := {ω | L ≤ horizontalCrossingDist (D ω) 0}
  set B := {ω | L ≤ horizontalCrossingDist (D ω) (1 / 2)}
  set C := {ω | L ≤ verticalCrossingDist (D ω) 0}
  set E := {ω | L ≤ verticalCrossingDist (D ω) (1 / 2)}
  calc μ {ω | ¬ HasShortHalfCrossings (D ω) 0 1 0 1 L} ≤ μ (A ∪ B ∪ C ∪ E) := measure_mono ?_
    _ ≤ μ (A ∪ B ∪ C) + μ E := measure_union_le _ _
    _ ≤ μ (A ∪ B) + μ C + μ E := by gcongr; exact measure_union_le _ _
    _ ≤ μ A + μ B + μ C + μ E := by gcongr; exact measure_union_le _ _
  intro ω hω
  by_contra hcon
  simp only [A, B, C, E, mem_union, mem_ofPred_eq, not_or, not_le] at hcon
  exact hω (hasShortHalfCrossings_zero_one_of_crossingDist_lt (D ω) hcon.1.1.1 hcon.1.1.2 hcon.1.2 hcon.2)

/-- If each of the four strip distances is `≥ L` with probability at most `q`, then `[0, 1]²` fails to have hard
half-crossings of `D`-length at most `L` with probability at most `4 q`. -/
theorem measure_not_hasShortHalfCrossings_zero_one_le_four_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (L q : ℝ≥0∞)
    (hh : ∀ y₀ ∈ ({0, 1 / 2} : Set ℝ), μ {ω | L ≤ horizontalCrossingDist (D ω) y₀} ≤ q)
    (hv : ∀ x₀ ∈ ({0, 1 / 2} : Set ℝ), μ {ω | L ≤ verticalCrossingDist (D ω) x₀} ≤ q) :
    μ {ω | ¬ HasShortHalfCrossings (D ω) 0 1 0 1 L} ≤ 4 * q := by
  refine (measure_not_hasShortHalfCrossings_zero_one_le μ D L).trans ?_
  have h4 : (4 : ℝ≥0∞) * q = q + q + q + q := by ring
  rw [h4]
  gcongr
  · exact hh 0 (by simp)
  · exact hh (1 / 2) (by simp)
  · exact hv 0 (by simp)
  · exact hv (1 / 2) (by simp)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
  {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Internal diameter of a closed square from the strip tails** (Dubédat-Falconet-Gwynne-Pfeffer-Sun, Proposition 3.10,
with Proposition 3.1 applied to the strip configurations). Let `𝔇` be a γ-LQG metric with `ξ > 0` and `h` a whole-plane
GFF. Suppose that for every whole-plane GFF `h'` on the same probability space and each of the four strip configurations
around the halves of `[0, 1]²`, the strip distance of `D_{h'}` is `≥ e^{δ n}` with probability at most `p n`, where
`∑ 4^n p n < ∞` and `δ < θ < ξ (Q - 2) log 2`. Then a.s. the internal metric of `D_h` on the closed square
`S = [a, a + s] × [b, b + s]` is bounded on `S`. -/
theorem IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_crossingDistTail (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (hstrip : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ n : ℕ,
      (∀ y₀ ∈ ({0, 1 / 2} : Set ℝ),
        P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ horizontalCrossingDist (𝔇 (hC' ω)) y₀} ≤ p n) ∧
      (∀ x₀ ∈ ({0, 1 / 2} : Set ℝ),
        P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ verticalCrossingDist (𝔇 (hC' ω)) x₀} ≤ p n))
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ w ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric (𝔇 (hC ω)) (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ ENNReal.ofReal A := by
  refine h𝔇.ae_exists_internalMetric_closedSquare_le_of_uniformUnitTail hG hs hξ hθ hδ (p := fun n => 4 * p n)
    (fun hC' hcirc' hG' n => measure_not_hasShortHalfCrossings_zero_one_le_four_mul P (fun ω => 𝔇 (hC' ω)) _ _
      (hstrip hC' hcirc' hG' n).1 (hstrip hC' hcirc' hG' n).2) ?_
  have : ∑' n, 4 ^ n * (4 * p n) = 4 * ∑' n, 4 ^ n * p n := by
    rw [← ENNReal.tsum_mul_left]; congr 1; ext n; ring
  rw [this]
  exact ENNReal.mul_ne_top (by norm_num) hp

end LatticeProb.LQG
