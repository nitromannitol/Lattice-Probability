import Mathlib
import LatticeProb.LQG.WeylChainApprox

/-!
# The internal metric of a Weyl-scaled length metric as a limit of weighted chain infima

Let `D` be a Euclidean length metric on `ℂ`, `f` a continuous function with `ξ f ≤ K`, and `E = e^{ξ f} · D` its
Weyl scaling (Gwynne-Miller, arXiv:1905.00383, (1.7)-(1.8)), assumed to be a Euclidean length metric with `E ≥ 0`.
For an open set `U`, a set `Q` and `δ > 0`, the weighted chain infimum `C_δ(x, y)` is the infimum, over all chains
`x = z₀, z₁, …, z_m = y` with `m ≥ 1` and `z₁, …, z_{m-1} ∈ Q`, of the weighted sums of local internal metrics
`∑_{i < m} e^{ξ f(z_i)} D(z_i, z_{i+1}; B(z_i, δ) ∩ U)`.

* `internalMetric_weylScaling_le_exp_mul_weightedChainInf`: if `η` bounds the oscillation of `ξ f` at distance less
  than `δ` and `x ∈ U`, then `E(x, y; U) ≤ e^η C_δ(x, y)`.
* `weightedChainInf_le_exp_mul_internalMetric`: if moreover `Q` is dense, then `C_δ(x, y) ≤ e^{2η} E(x, y; U)`.
* `internalMetric_weylScaling_eq_iInf_weightedChainInf`: for scales `δ_n > 0` with oscillation bounds `η_n → 0`,
  `E(x, y; U) = inf_n e^{η_n} C_{δ_n}(x, y)`.

For countable `Q` the chain infimum is a countable infimum of finite sums of local internal metrics of `D`; this
expresses the internal metric of `E` through internal metrics of `D` on small balls, with deterministic weights.
-/

namespace LatticeProb.LQG

open Set Filter Topology
open scoped ENNReal

/-- The points of a chain from `x` to `y` with `m` links and interior points `w`: `z₀ = x`, `z_i = w_i` for
`0 < i < m`, and `z_i = y` for `i ≥ m`, `i ≠ 0` (the value `w₀` is not used). -/
def chainPoint {Q : Set ℂ} (x y : ℂ) (m : ℕ) (w : Fin m → Q) (i : ℕ) : ℂ :=
  if i = 0 then x else if h : i < m then (w ⟨i, h⟩ : ℂ) else y

/-- The weighted chain sum `∑_{i < m} e^{g(z_i)} D(z_i, z_{i+1}; B(z_i, δ) ∩ U)` of local internal metrics. -/
noncomputable def weightedChainSum (D : ℂ → ℂ → ℝ) (g : ℂ → ℝ) (U : Set ℂ) (δ : ℝ) (z : ℕ → ℂ) (m : ℕ) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range m,
    ENNReal.ofReal (Real.exp (g (z i))) * internalMetric D (Metric.ball (z i) δ ∩ U) (z i) (z (i + 1))

/-- The weighted chain infimum `C_δ(x, y)`: the infimum of the weighted chain sums over all chains from `x` to `y`
with at least one link and interior points in `Q`. For countable `Q` the index set is countable. -/
noncomputable def weightedChainInf (D : ℂ → ℂ → ℝ) (g : ℂ → ℝ) (U Q : Set ℂ) (δ : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ (m : ℕ) (w : Fin (m + 1) → Q), weightedChainSum D g U δ (chainPoint x y (m + 1) w) (m + 1)

theorem chainPoint_zero {Q : Set ℂ} (x y : ℂ) (m : ℕ) (w : Fin m → Q) : chainPoint x y m w 0 = x := by
  simp [chainPoint]

theorem chainPoint_last {Q : Set ℂ} (x y : ℂ) (m : ℕ) (w : Fin (m + 1) → Q) :
    chainPoint x y (m + 1) w (m + 1) = y := by
  simp [chainPoint]

/-- Upper bound of the internal metric of `E = e^{ξ f} · D` on an open set by the weighted chain infimum: if
`|ξ f(a) - ξ f(b)| ≤ η` whenever `dist a b < δ`, and `x ∈ U`, then `E(x, y; U) ≤ e^η C_δ(x, y)`. -/
theorem internalMetric_weylScaling_le_exp_mul_weightedChainInf {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (hE : IsEuclideanLengthMetric E) (hE0 : ∀ x y, 0 ≤ E x y) {ξ : ℝ}
    {f : ℂ → ℝ} (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {U : Set ℂ} (hU : IsOpen U)
    (Q : Set ℂ) {δ η : ℝ} (hη : ∀ a b, dist a b < δ → |ξ * f a - ξ * f b| ≤ η) {x : ℂ} (hx : x ∈ U) (y : ℂ) :
    internalMetric E U x y ≤
      ENNReal.ofReal (Real.exp η) * weightedChainInf D (fun z => ξ * f z) U Q δ x y := by
  have hc0 : ENNReal.ofReal (Real.exp η) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos η)).ne'
  have hctop : ENNReal.ofReal (Real.exp η) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold weightedChainInf
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun m => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun w => ?_
  set z := chainPoint x y (m + 1) w with hz
  have h0 : z 0 = x := chainPoint_zero x y (m + 1) w
  have h1 : z (m + 1) = y := chainPoint_last x y m w
  have h := internalMetric_weylScaling_le_chain_sum hD hE hE0 hscale hU z (h0 ▸ hx)
    (fun i => Metric.ball (z i) δ ∩ U) (fun _ => inter_subset_right) (fun i => ξ * f (z i) + η)
    (fun i a ha => by
      have := (abs_le.mp (hη a (z i) (Metric.mem_ball.mp ha.1))).2
      linarith) (m + 1)
  rw [h0, h1] at h
  refine h.trans (le_of_eq ?_)
  unfold weightedChainSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/-- A chain `x = z₀, …, z_m = y` with interior points in `Q` bounds the weighted chain infimum by its weighted chain
sum (for `m = 0`, that is `x = y`, the one-link chain from `x` to itself has sum `0` when `x ∈ U`). -/
theorem weightedChainInf_le_weightedChainSum {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (g : ℂ → ℝ)
    {U : Set ℂ} (hU : IsOpen U) {Q : Set ℂ} (hQ : Q.Nonempty) {δ : ℝ} (hδ : 0 < δ) {x y : ℂ} (hx : x ∈ U)
    (m : ℕ) (z : ℕ → ℂ) (hz0 : z 0 = x) (hzm : z m = y) (hzQ : ∀ i, 0 < i → i < m → z i ∈ Q) :
    weightedChainInf D g U Q δ x y ≤ weightedChainSum D g U δ z m := by
  obtain ⟨q, hq⟩ := hQ
  cases m with
  | zero =>
    have hxy : x = y := hz0.symm.trans hzm
    subst hxy
    have hxx : internalMetric D (Metric.ball x δ ∩ U) x x = 0 :=
      hD.internalMetric_self_of_mem_open (euclid_D_nonneg hD) (Metric.isOpen_ball.inter hU)
        ⟨Metric.mem_ball_self hδ, hx⟩
    refine iInf_le_of_le 0 (iInf_le_of_le (fun _ => ⟨q, hq⟩) ?_)
    simp [weightedChainSum, chainPoint, hxx]
  | succ k =>
    let w : Fin (k + 1) → Q := fun i =>
      if h : (i : ℕ) = 0 then ⟨q, hq⟩ else ⟨z i, hzQ i (Nat.pos_of_ne_zero h) i.2⟩
    have hpt : ∀ i ≤ k + 1, chainPoint x y (k + 1) w i = z i := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [chainPoint_zero, hz0]
      rcases lt_or_eq_of_le hi with hlt | rfl
      · simp [chainPoint, hi0.ne', hlt, w]
      · rw [chainPoint_last, hzm]
    refine iInf_le_of_le k (iInf_le_of_le w (le_of_eq ?_))
    unfold weightedChainSum
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [hpt i hi'.le, hpt (i + 1) hi']

/-- Lower bound of the internal metric of `E = e^{ξ f} · D` on an open set by the weighted chain infimum over a dense
set: if `|ξ f(a) - ξ f(b)| ≤ η` whenever `dist a b < δ`, then `C_δ(x, y) ≤ e^{2η} E(x, y; U)`. -/
theorem weightedChainInf_le_exp_mul_internalMetric {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hE0 : ∀ x y, 0 ≤ E x y) {ξ K : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (hK : ∀ z, ξ * f z ≤ K) (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    {U : Set ℂ} (hU : IsOpen U) {Q : Set ℂ} (hQ : Dense Q) {δ η : ℝ} (hδ : 0 < δ)
    (hη : ∀ a b, dist a b < δ → |ξ * f a - ξ * f b| ≤ η) (x y : ℂ) :
    weightedChainInf D (fun z => ξ * f z) U Q δ x y ≤
      ENNReal.ofReal (Real.exp (2 * η)) * internalMetric E U x y := by
  have hc0 : ENNReal.ofReal (Real.exp (2 * η)) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : ENNReal.ofReal (Real.exp (2 * η)) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold internalMetric
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun P => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun hPU => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨m, z, hz0, hzm, hzQ, hsum⟩ :=
    exists_chain_sum_le_pathLength hD hE hE0 hf hK hscale hU hQ hδ hη P hPU (ε := (ε : ℝ))
      (NNReal.coe_pos.mpr hε)
  have hx : x ∈ U := by simpa using hPU 0
  refine (weightedChainInf_le_weightedChainSum hD _ hU hQ.nonempty hδ hx m z hz0 hzm hzQ).trans ?_
  rw [ENNReal.ofReal_coe_nnreal] at hsum
  exact hsum

/-- Chain formula for the internal metric of a Weyl scaling: for scales `δ_n > 0` and oscillation bounds `η_n → 0`
of `ξ f` at distance less than `δ_n`, a dense set `Q` and `x ∈ U`,
`E(x, y; U) = inf_n e^{η_n} C_{δ_n}(x, y)`. -/
theorem internalMetric_weylScaling_eq_iInf_weightedChainInf {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (hE : IsEuclideanLengthMetric E) (hE0 : ∀ x y, 0 ≤ E x y) {ξ K : ℝ}
    {f : ℂ → ℝ} (hf : Continuous f) (hK : ∀ z, ξ * f z ≤ K)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {U : Set ℂ} (hU : IsOpen U) {Q : Set ℂ}
    (hQ : Dense Q) {δ η : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hη : ∀ n a b, dist a b < δ n → |ξ * f a - ξ * f b| ≤ η n) (hη0 : Tendsto η atTop (𝓝 0))
    {x : ℂ} (hx : x ∈ U) (y : ℂ) :
    internalMetric E U x y =
      ⨅ n, ENNReal.ofReal (Real.exp (η n)) * weightedChainInf D (fun z => ξ * f z) U Q (δ n) x y := by
  refine le_antisymm (le_iInf fun n =>
    internalMetric_weylScaling_le_exp_mul_weightedChainInf hD hE hE0 hscale hU Q (hη n) hx y) ?_
  have hlim : Tendsto (fun n => ENNReal.ofReal (Real.exp (3 * η n)) * internalMetric E U x y) atTop
      (𝓝 (internalMetric E U x y)) := by
    have h1 : Tendsto (fun n => Real.exp (3 * η n)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n => 3 * η n) atTop (𝓝 0) := by simpa using hη0.const_mul 3
      have h1' := (Real.continuous_exp.tendsto 0).comp h0
      rw [Real.exp_zero] at h1'
      exact h1'
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_one] at h2
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inl one_ne_zero)
  refine ge_of_tendsto' hlim fun n => iInf_le_of_le n ?_
  calc ENNReal.ofReal (Real.exp (η n)) * weightedChainInf D (fun z => ξ * f z) U Q (δ n) x y
      ≤ ENNReal.ofReal (Real.exp (η n)) *
          (ENNReal.ofReal (Real.exp (2 * η n)) * internalMetric E U x y) := by
        gcongr
        exact weightedChainInf_le_exp_mul_internalMetric hD hE hE0 hf hK hscale hU hQ (hδ n) (hη n) x y
    _ = ENNReal.ofReal (Real.exp (3 * η n)) * internalMetric E U x y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          show η n + 2 * η n = 3 * η n by ring]

end LatticeProb.LQG
