import Mathlib
import LatticeProb.Prob.CrossingTimesClock

/-!
# The crossing clock of Brownian motion at all times simultaneously

Let `B` be a Brownian motion in `ℝ ^ d` with continuous paths, `N_n(u) = crossCount (2⁻ⁿ) B u`
the number of `2⁻ⁿ`-crossings in `[0, u]`, and `m` the constant of `exists_ae_tendsto_crossCount`.
We upgrade the statement `m 4⁻ⁿ N_n(u) → u` almost surely, for each fixed `u`, to a statement
that holds almost surely for all `u ≥ 0` simultaneously.

The upgrade is deterministic once it holds on the countable grid of positive rationals: the
functions `u ↦ m 4⁻ⁿ N_n(u)` are nondecreasing.

* `tendsto_of_monotone_of_grid`: if nondecreasing functions `G n` converge to the identity at every
  rational `i / (j + 1)`, they converge to the identity everywhere;
* `exists_ae_tendsto_crossCount_all`: almost surely, `m 4⁻ⁿ N_n(u) → u` for every `u ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- **Interpolation of nondecreasing functions from a dense grid.**  If nondecreasing functions
`G n : ℝ≥0 → ℝ` converge to the identity at every rational point `i / (j + 1)`, then they converge
to the identity at every point of `ℝ≥0`. -/
theorem tendsto_of_monotone_of_grid {G : ℕ → ℝ≥0 → ℝ} (hG : ∀ n, Monotone (G n))
    (hgrid : ∀ i j : ℕ, Tendsto (fun n => G n ((i : ℝ≥0) / ((j : ℝ≥0) + 1))) atTop
      (𝓝 (((i : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ)))
    (x : ℝ≥0) : Tendsto (fun n => G n x) atTop (𝓝 (x : ℝ)) := by
  have hcoe : ∀ i j : ℕ, (((i : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ) = (i : ℝ) / ((j : ℝ) + 1) :=
    fun i j => by simp
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 ha')
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h1 : ((⌊(x : ℝ) * ((j : ℝ) + 1)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) * ((j : ℝ) + 1) :=
      Nat.floor_le (by positivity)
    have h2 : (x : ℝ) * ((j : ℝ) + 1) < ((⌊(x : ℝ) * ((j : ℝ) + 1)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h3 : 1 < ((x : ℝ) - a') * ((j : ℝ) + 1) := by rwa [div_lt_iff₀ hpos] at hj
    have hlt : a' < (((⌊(x : ℝ) * ((j : ℝ) + 1)⌋₊ : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ) := by
      rw [hcoe, lt_div_iff₀ hpos]
      nlinarith
    have hle : ((⌊(x : ℝ) * ((j : ℝ) + 1)⌋₊ : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) ≤ x := by
      rw [← NNReal.coe_le_coe, hcoe, div_le_iff₀ hpos]
      exact h1
    filter_upwards [(hgrid ⌊(x : ℝ) * ((j : ℝ) + 1)⌋₊ j).eventually (lt_mem_nhds hlt)] with n hn
    exact lt_of_lt_of_le hn (hG n hle)
  · intro b' hb'
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hb')
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h1 : (x : ℝ) * ((j : ℝ) + 1) ≤ ((⌈(x : ℝ) * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(x : ℝ) * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) < (x : ℝ) * ((j : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h3 : 1 < (b' - (x : ℝ)) * ((j : ℝ) + 1) := by rwa [div_lt_iff₀ hpos] at hj
    have hlt : (((⌈(x : ℝ) * ((j : ℝ) + 1)⌉₊ : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ) < b' := by
      rw [hcoe, div_lt_iff₀ hpos]
      nlinarith
    have hle : x ≤ ((⌈(x : ℝ) * ((j : ℝ) + 1)⌉₊ : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, hcoe, le_div_iff₀ hpos]
      exact h1
    filter_upwards [(hgrid ⌈(x : ℝ) * ((j : ℝ) + 1)⌉₊ j).eventually (gt_mem_nhds hlt)] with n hn
    exact lt_of_le_of_lt (hG n hle) hn

/-- **The crossing clock of Brownian motion at all times simultaneously.**  There is `m ∈ (0, ∞)`,
depending only on `d`, such that for every Brownian motion `B` in `ℝ ^ d` with continuous paths,
almost surely, for every time `u ≥ 0`, `m 4⁻ⁿ N_n(u) → u`, where `N_n(u)` is the number of
`2⁻ⁿ`-crossings of `B` in `[0, u]`. -/
theorem exists_ae_tendsto_crossCount_all (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ, 0 < m ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
      (∀ ω, Continuous fun t => B t ω) → ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun n : ℕ => m * (4⁻¹ : ℝ) ^ n *
          ((crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) u).toNat : ℝ)) atTop (𝓝 (u : ℝ)) := by
  obtain ⟨m, hm, h⟩ := exists_ae_tendsto_crossCount d hd
  refine ⟨m, hm, ?_⟩
  intro Ω _ P _ x B hB hmeas hcont
  have hall : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ,
      Tendsto (fun n : ℕ => m * (4⁻¹ : ℝ) ^ n *
        ((crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) ((p.1 : ℝ≥0) / ((p.2 : ℝ≥0) + 1))).toNat : ℝ))
        atTop (𝓝 (((p.1 : ℝ≥0) / ((p.2 : ℝ≥0) + 1) : ℝ≥0) : ℝ)) :=
    ae_all_iff.2 fun p => h Ω P x B hB hmeas hcont _
  filter_upwards [hall] with ω hω u
  refine tendsto_of_monotone_of_grid
    (G := fun n v => m * (4⁻¹ : ℝ) ^ n *
      ((crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) v).toNat : ℝ)) ?_ (fun i j => hω (i, j)) u
  intro n v w hvw
  have hn : (0 : ℝ) ≤ m * (4⁻¹ : ℝ) ^ n := by positivity
  exact mul_le_mul_of_nonneg_left
    (Nat.cast_le.2 (monotone_toNat_crossCount (hcont ω) (by positivity) hvw)) hn

end LatticeProb
