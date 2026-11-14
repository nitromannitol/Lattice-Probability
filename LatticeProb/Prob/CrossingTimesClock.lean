import Mathlib
import LatticeProb.Analysis.CrossingTimesCount
import LatticeProb.Prob.CrossingTimesChebyshev

/-!
# The crossing clock of Brownian motion at a fixed time

Let `B` be a Brownian motion in `ℝ ^ d` with continuous paths and let `N_n(u) = crossCount (2⁻ⁿ) B u`
be the number of `2⁻ⁿ`-crossings in `[0, u]`.  With the constant `m ∈ (0, ∞)` (the mean exit time of
the unit ball, depending only on `d`) we show that, almost surely, `m 4⁻ⁿ N_n(u) → u`.

The proof combines the Chebyshev bound for the crossing times with the Borel-Cantelli lemma:
for `0 < δ ≤ u`, the events `{σ_{M} ≤ u}` with `M = ⌈(u + δ) / (4⁻ⁿ m)⌉` and `{σ_{M} > u}` with
`M = ⌊(u - δ) / (4⁻ⁿ m)⌋` have probabilities `O(4⁻ⁿ)`, which is summable in `n`.

* `ae_eventually_notMem_of_geometric_bound`: Borel-Cantelli for two families of events whose
  probabilities are bounded by `K 4⁻ⁿ`;
* `abs_mul_sub_le_of_floor_ceil`: the arithmetic step;
* `exists_ae_eventually_abs_clock_sub_le`: eventually `|m 4⁻ⁿ N_n(u) - u| ≤ δ + m 4⁻ⁿ`, almost surely;
* `exists_ae_tendsto_crossCount`: `m 4⁻ⁿ N_n(u) → u` almost surely, for each fixed `u`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- **Borel-Cantelli for two geometric families.**  If `P (bad n (M₁ n))` and `P (bad n (M₂ n))` are
at most `K 4⁻ⁿ`, then almost surely both events fail for all large `n`. -/
theorem ae_eventually_notMem_of_geometric_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (bad : ℕ → ℕ → Set Ω) (M₁ M₂ : ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (h₁ : ∀ n, P (bad n (M₁ n)) ≤ ENNReal.ofReal (K * (4⁻¹ : ℝ) ^ n))
    (h₂ : ∀ n, P (bad n (M₂ n)) ≤ ENNReal.ofReal (K * (4⁻¹ : ℝ) ^ n)) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∉ bad n (M₁ n) ∧ ω ∉ bad n (M₂ n) := by
  have hsm : Summable fun n : ℕ => K * (4⁻¹ : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left K
  have hsum : ∑' n, P (bad n (M₁ n) ∪ bad n (M₂ n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (K * (4⁻¹ : ℝ) ^ n + K * (4⁻¹ : ℝ) ^ n))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsm.add hsm)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    calc P (bad n (M₁ n) ∪ bad n (M₂ n)) ≤ P (bad n (M₁ n)) + P (bad n (M₂ n)) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (K * (4⁻¹ : ℝ) ^ n) + ENNReal.ofReal (K * (4⁻¹ : ℝ) ^ n) :=
          add_le_add (h₁ n) (h₂ n)
      _ = ENNReal.ofReal (K * (4⁻¹ : ℝ) ^ n + K * (4⁻¹ : ℝ) ^ n) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  filter_upwards [ae_eventually_notMem (s := fun n => bad n (M₁ n) ∪ bad n (M₂ n)) hsum] with ω hω
  filter_upwards [hω] with n hn
  exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩

/-- **The arithmetic step.**  If `⌊(u - δ) / c⌋ ≤ N < ⌈(u + δ) / c⌉` then `|c N - u| ≤ δ + c`. -/
theorem abs_mul_sub_le_of_floor_ceil {c δ u : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hδu : δ ≤ u) {N : ℕ}
    (h₁ : ⌊(u - δ) / c⌋₊ ≤ N) (h₂ : N < ⌈(u + δ) / c⌉₊) : |c * N - u| ≤ δ + c := by
  have hpos : 0 ≤ (u + δ) / c := div_nonneg (by linarith) hc.le
  have l1 := Nat.lt_floor_add_one ((u - δ) / c)
  have l2 := Nat.ceil_lt_add_one hpos
  have hN1 : ((⌊(u - δ) / c⌋₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast h₁
  have hN2 : (N : ℝ) + 1 ≤ ((⌈(u + δ) / c⌉₊ : ℕ) : ℝ) := by exact_mod_cast h₂
  have e1 : u - δ < (((⌊(u - δ) / c⌋₊ : ℕ) : ℝ) + 1) * c := (div_lt_iff₀ hc).1 l1
  have e2 : (((⌈(u + δ) / c⌉₊ : ℕ) : ℝ) - 1) * c < u + δ :=
    (lt_div_iff₀ hc).1 (by linarith)
  have e3 : (((⌊(u - δ) / c⌋₊ : ℕ) : ℝ)) * c ≤ N * c := mul_le_mul_of_nonneg_right hN1 hc.le
  have e4 : (N : ℝ) * c ≤ (((⌈(u + δ) / c⌉₊ : ℕ) : ℝ) - 1) * c :=
    mul_le_mul_of_nonneg_right (by linarith) hc.le
  rw [abs_le]
  constructor <;> nlinarith

/-- **Eventual closeness of the crossing clock.**  There is `m ∈ (0, ∞)`, depending only on `d`, such
that for every Brownian motion `B` in `ℝ ^ d` with continuous paths, every `u` and every
`0 < δ ≤ u`, almost surely `|m 4⁻ⁿ N_n(u) - u| ≤ δ + m 4⁻ⁿ` for all large `n`, where
`N_n(u)` is the number of `2⁻ⁿ`-crossings of `B` in `[0, u]`. -/
theorem exists_ae_eventually_abs_clock_sub_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ, 0 < m ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
      (∀ ω, Continuous fun t => B t ω) → ∀ (u : ℝ≥0) (δ : ℝ), 0 < δ → δ ≤ u →
        ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
          |m * (4⁻¹ : ℝ) ^ n * ((crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) u).toNat : ℝ) - u| ≤
            δ + m * (4⁻¹ : ℝ) ^ n := by
  obtain ⟨m', C, hm0, hmtop, hC0, hdev⟩ := exists_measure_crossTime_deviation_le d hd
  have hmpos : 0 < m'.toReal := ENNReal.toReal_pos hm0.ne' hmtop.ne
  refine ⟨m'.toReal, hmpos, ?_⟩
  intro Ω _ P _ x B hB hmeas hcont u δ hδ hδu
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = m'.toReal := ⟨_, rfl⟩
  rw [← hmdef] at hmpos hdev ⊢
  have hε2 : ∀ n : ℕ, ((2 : ℝ)⁻¹ ^ n) ^ 2 = (4⁻¹ : ℝ) ^ n := fun n => by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C * ((u : ℝ) + δ) / (m * δ ^ 2) + C / δ ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have : (0 : ℝ) ≤ u := u.2
    positivity
  have hpart : ∀ (n M : ℕ), (M : ℝ) ≤ ((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m) + 1 →
      P {ω | crossTime ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) M = ⊤ ∨
          δ ≤ |(crossTime ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) M).toReal -
            M * (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)|} ≤ ENNReal.ofReal (K * (4⁻¹ : ℝ) ^ n) := by
    intro n M hM
    refine (hdev Ω P x B hB hmeas hcont ((2 : ℝ)⁻¹ ^ n) (by positivity) M δ hδ).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have e4 : ((2 : ℝ)⁻¹ ^ n) ^ 4 = ((4⁻¹ : ℝ) ^ n) ^ 2 := by
      rw [← hε2 n]
      ring
    rw [e4]
    rw [hε2 n] at hM
    have ha0 : 0 < (4⁻¹ : ℝ) ^ n := by positivity
    have ha1 : (4⁻¹ : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    generalize (4⁻¹ : ℝ) ^ n = a at hM ha0 ha1 ⊢
    have hu0 : (0 : ℝ) ≤ u := u.2
    calc (M : ℝ) * (C * a ^ 2) / δ ^ 2
        ≤ (((u : ℝ) + δ) / (a * m) + 1) * (C * a ^ 2) / δ ^ 2 := by gcongr
      _ = C * ((u : ℝ) + δ) / (m * δ ^ 2) * a + C / δ ^ 2 * a ^ 2 := by
          field_simp
      _ ≤ K * a := by
          have h2 : a ^ 2 ≤ a := by nlinarith
          have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ C / δ ^ 2 by positivity)
          rw [hK]
          nlinarith
  have hcpos : ∀ n : ℕ, 0 < ((2 : ℝ)⁻¹ ^ n) ^ 2 * m := fun n => by positivity
  have hM₁ : ∀ n : ℕ, ((⌊((u : ℝ) - δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)⌋₊ : ℕ) : ℝ) ≤
      ((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m) + 1 := fun n => by
    have hc := hcpos n
    have hu0 : (0 : ℝ) ≤ u := u.2
    have h := Nat.floor_le (show 0 ≤ ((u : ℝ) - δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m) from
      div_nonneg (by linarith) hc.le)
    have h' : ((u : ℝ) - δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m) ≤
        ((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m) := (div_le_div_iff_of_pos_right hc).2 (by linarith)
    linarith
  have hM₂ : ∀ n : ℕ, ((⌈((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)⌉₊ : ℕ) : ℝ) ≤
      ((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m) + 1 := fun n => by
    have hc := hcpos n
    have hu0 : (0 : ℝ) ≤ u := u.2
    exact (Nat.ceil_lt_add_one (div_nonneg (by linarith) hc.le)).le
  have hae := ae_eventually_notMem_of_geometric_bound P
    (fun n M => {ω | crossTime ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) M = ⊤ ∨
          δ ≤ |(crossTime ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) M).toReal -
            M * (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)|})
    (fun n => ⌊((u : ℝ) - δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)⌋₊)
    (fun n => ⌈((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)⌉₊) hK0
    (fun n => hpart n _ (hM₁ n)) (fun n => hpart n _ (hM₂ n))
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with n hn
  obtain ⟨hn1, hn2⟩ := hn
  have hn1' := not_or.1 hn1
  have hn2' := not_or.1 hn2
  have hc := hcpos n
  have hu0 : (0 : ℝ) ≤ u := u.2
  have hb := crossCount_toNat_bounds (hcont ω) (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ n by positivity) u
    (c := ((2 : ℝ)⁻¹ ^ n) ^ 2 * m) (δ := δ)
    (M₁ := ⌊((u : ℝ) - δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)⌋₊)
    (M₂ := ⌈((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m)⌉₊)
    (by
      have h := Nat.floor_le (show 0 ≤ ((u : ℝ) - δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m) from
        div_nonneg (by linarith) hc.le)
      rw [le_div_iff₀ hc] at h
      linarith)
    (by
      have h := Nat.le_ceil (((u : ℝ) + δ) / (((2 : ℝ)⁻¹ ^ n) ^ 2 * m))
      rw [div_le_iff₀ hc] at h
      linarith)
    ⟨hn1'.1, not_le.1 hn1'.2⟩ ⟨hn2'.1, not_le.1 hn2'.2⟩
  have key := abs_mul_sub_le_of_floor_ceil hc hδ.le hδu hb.1 hb.2
  have hc' : ((2 : ℝ)⁻¹ ^ n) ^ 2 * m = m * (4⁻¹ : ℝ) ^ n := by
    rw [hε2 n, mul_comm]
  rw [hc'] at key
  exact key

/-- A continuous path has no crossing in the time interval `[0, 0]`. -/
theorem toNat_crossCount_zero {E : Type*} [PseudoMetricSpace E] {f : ℝ≥0 → E} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) : (crossCount ε f 0).toNat = 0 := by
  by_contra hne
  have hfin : crossCount ε f 0 ≠ ⊤ := (crossCount_lt_top hf hε 0).ne
  have h1 : ((1 : ℕ) : ℕ∞) ≤ crossCount ε f 0 := by
    rw [← ENat.natCast_toNat hfin]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  have h2 := (le_crossCount_iff ε f 0 1).1 h1
  have h3 := crossTime_one_pos hf.continuousAt hε
  exact absurd h2 (not_le.2 (by simpa using h3))

/-- **The crossing clock of Brownian motion at a fixed time.**  There is `m ∈ (0, ∞)`, depending only
on `d`, such that for every Brownian motion `B` in `ℝ ^ d` with continuous paths and every time `u`,
almost surely `m 4⁻ⁿ N_n(u) → u`, where `N_n(u)` is the number of `2⁻ⁿ`-crossings of `B` in
`[0, u]`. -/
theorem exists_ae_tendsto_crossCount (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ, 0 < m ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
      (∀ ω, Continuous fun t => B t ω) → ∀ u : ℝ≥0, ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => m * (4⁻¹ : ℝ) ^ n *
          ((crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) u).toNat : ℝ)) atTop (𝓝 (u : ℝ)) := by
  obtain ⟨m, hm, h⟩ := exists_ae_eventually_abs_clock_sub_le d hd
  refine ⟨m, hm, ?_⟩
  intro Ω _ P _ x B hB hmeas hcont u
  rcases eq_or_ne u 0 with rfl | hu
  · refine Filter.Eventually.of_forall fun ω => ?_
    have h0 : ∀ n : ℕ, (crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) 0).toNat = 0 := fun n =>
      toNat_crossCount_zero (hcont ω) (by positivity)
    have h1 : (fun n : ℕ => m * (4⁻¹ : ℝ) ^ n *
        ((crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) 0).toNat : ℝ)) = fun _ => 0 := by
      funext n
      rw [h0 n]
      simp
    rw [h1, NNReal.coe_zero]
    exact tendsto_const_nhds
  · have hu' : (0 : ℝ) < u := by exact_mod_cast pos_iff_ne_zero.2 hu
    have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
        |m * (4⁻¹ : ℝ) ^ n * ((crossCount ((2 : ℝ)⁻¹ ^ n) (fun t => B t ω) u).toNat : ℝ) - u| ≤
          (u : ℝ) / (j + 1) + m * (4⁻¹ : ℝ) ^ n := by
      rw [ae_all_iff]
      intro j
      exact h Ω P x B hB hmeas hcont u ((u : ℝ) / (j + 1)) (by positivity)
        (div_le_self hu'.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
    filter_upwards [hall] with ω hω
    refine Metric.tendsto_nhds.2 fun η hη => ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (2 * (u : ℝ) / η)
    have hjη : (u : ℝ) / (j + 1) < η / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hη).1 hj
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have hc : Tendsto (fun n : ℕ => m * (4⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 4⁻¹)
        (by norm_num : (4⁻¹ : ℝ) < 1)).const_mul m
    filter_upwards [hω j, hc.eventually (gt_mem_nhds (half_pos hη))] with n h1 h2
    rw [Real.dist_eq]
    linarith

end LatticeProb
