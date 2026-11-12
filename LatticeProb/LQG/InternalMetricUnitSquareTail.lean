import LatticeProb.LQG.InternalMetricSquareTailUniform
import LatticeProb.Gauss.CircleAverageDyadicScaleFactorShift
import LatticeProb.LQG.LQGNegLognormal

/-!
# A summable tail for the internal diameter of the unit square for the γ-LQG metric

Let `𝔇` be a γ-LQG metric with `ξ > 0` and let `0 < δ < θ < ξ (Q - 2) log 2`. Suppose that for every whole-plane GFF
`h'` on a probability space `(Ω, P)` the probability that the unit square `[0, 1]²` has no half crossings of
`D_{h'}`-length at most `e^{δ n}` is at most `p n`, where `∑ₙ 4ⁿ p n < ∞` (the crossing estimate of
Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.1). Then for every `ε > 0` there is a summable
sequence `ψ` such that, for every whole-plane GFF `h'` on `(Ω, P)` and every `k`, the probability that the internal
diameter of `[0, 1]²` for `D_{h'}` exceeds `e^{ε k}` is at most `ψ k`.

The proof is the union bound behind Proposition 3.10 of Dubédat-Falconet-Gwynne-Pfeffer-Sun, with thresholds depending
on `k`: the dyadic subsquares of level `n` get half crossings of length at most `e^{ε k} (1 - e^{-(θ - δ)}) e^{-(θ - δ) n} / 6`,
whose total over the levels bounds the internal diameter by `e^{ε k}`
(`IsEuclideanLengthMetric.internalMetric_le_of_hasShortHalfCrossings`). Through the coordinate change each such event
costs the unit-square tail at level `n + ⌊ε k / (2 δ)⌋`, whose sum over `n` and `k` is finite, plus a Gaussian tail of the
circle average, which is the same in every model (`IsWholePlaneGFF.measure_le_circle_eq`) and is summable over `n` and
`k` (`IsWholePlaneGFF.tsum_tsum_dyadic_measure_circle_ge_linear_ne_top`).

## Main statements

* `LatticeProb.Gauss.IsWholePlaneGFF.measure_le_circle_eq`: one circle average has the same upper tail in every model.
* `LatticeProb.LQG.tsum_tsum_four_pow_mul_floor_shift_ne_top`: `∑ₖ ∑ₙ 4ⁿ p (n + ⌊c k⌋) < ∞` when `∑ₙ 4ⁿ p n < ∞`.
* `LatticeProb.LQG.IsLQGMetric.exists_unitSquare_internalMetric_tail`: the summable tail of the internal diameter.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.Gauss

/-- **One circle average has the same upper tail in every model.** For two whole-plane GFFs, possibly on different
probability spaces, `P[t ≤ h_r(z)] = P'[t ≤ h'_r(z)]` for every `r > 0`, `z ∈ ℂ` and `t ∈ ℝ`. -/
theorem IsWholePlaneGFF.measure_le_circle_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') {r : ℝ} (hr : 0 < r) (z : ℂ)
    (t : ℝ) : P {ω | t ≤ hcirc ω r z} = P' {ω | t ≤ hcirc' ω r z} := by
  have hmap := hh.map_circleVector_eq hh' (fun _ : Unit => r) (fun _ => z) (fun _ => hr)
  have hS : MeasurableSet {f : Unit → ℝ | t ≤ f ()} :=
    measurableSet_le measurable_const (measurable_pi_apply ())
  have hm : Measurable fun ω (_ : Unit) => hcirc ω r z :=
    measurable_pi_iff.2 fun _ => hh.measurable_circle r z hr
  have hm' : Measurable fun ω (_ : Unit) => hcirc' ω r z :=
    measurable_pi_iff.2 fun _ => hh'.measurable_circle r z hr
  have h := congrArg (fun μ : Measure (Unit → ℝ) => μ {f : Unit → ℝ | t ≤ f ()}) hmap
  rw [Measure.map_apply hm hS, Measure.map_apply hm' hS] at h
  exact h

end LatticeProb.Gauss

namespace LatticeProb.LQG

/-- **Shifted crossing tails are summable over the shifts.** If `∑ₙ 4ⁿ p n < ∞` and `c > 0`, then
`∑ₖ ∑ₙ 4ⁿ p (n + ⌊c k⌋) < ∞`: the inner sum is at most `4^{-⌊c k⌋} ∑ₙ 4ⁿ p n`. -/
theorem tsum_tsum_four_pow_mul_floor_shift_ne_top {p : ℕ → ℝ≥0∞} (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {c : ℝ}
    (hc : 0 < c) : ∑' k : ℕ, ∑' n : ℕ, 4 ^ n * p (n + ⌊c * k⌋₊) ≠ ⊤ := by
  have hshift : ∀ m : ℕ, ∑' n : ℕ, 4 ^ n * p (n + m) ≤ (∑' n, 4 ^ n * p n) * ((4 : ℝ≥0∞) ^ m)⁻¹ := by
    intro m
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ (by norm_num)))
      (Or.inl (ENNReal.pow_ne_top (by norm_num))), ← ENNReal.tsum_mul_right]
    calc ∑' n : ℕ, 4 ^ n * p (n + m) * 4 ^ m = ∑' n : ℕ, 4 ^ (n + m) * p (n + m) := by
          congr 1; ext n; rw [pow_add]; ring
      _ ≤ ∑' n, 4 ^ n * p n :=
          ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective m) (fun n => 4 ^ n * p n)
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hinv : ∀ k : ℕ, ((4 : ℝ≥0∞) ^ ⌊c * k⌋₊)⁻¹ ≤
      ENNReal.ofReal (4 * Real.exp (-(c * Real.log 4 * k))) := by
    intro k
    have h4 : (4 : ℝ≥0∞) ^ ⌊c * k⌋₊ = ENNReal.ofReal (Real.exp (⌊c * k⌋₊ * Real.log 4)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ENNReal.ofReal_pow (by norm_num)]
      norm_num
    rw [h4, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
    refine ENNReal.ofReal_le_ofReal ?_
    have hfl : c * k < ⌊c * k⌋₊ + 1 := Nat.lt_floor_add_one _
    calc Real.exp (-(⌊c * k⌋₊ * Real.log 4)) ≤ Real.exp (Real.log 4 + -(c * Real.log 4 * k)) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = 4 * Real.exp (-(c * Real.log 4 * k)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
  have hgeo : ∑' k : ℕ, ((4 : ℝ≥0∞) ^ ⌊c * k⌋₊)⁻¹ ≠ ⊤ :=
    ne_top_of_le_ne_top (tsum_ofReal_mul_exp_ne_top (by norm_num) (mul_pos hc hlog))
      (ENNReal.tsum_le_tsum hinv)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k => hshift ⌊c * k⌋₊)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top hp hgeo

/-- `6 ∑ₙ e^{x - η n + log β} = e^x` for `η > 0` and `β = (1 - e^{-η}) / 6`. -/
theorem six_mul_tsum_ofReal_exp_geometric {η β : ℝ} (hη : 0 < η) (hβ : β = (1 - Real.exp (-η)) / 6) (x : ℝ) :
    6 * ∑' n : ℕ, ENNReal.ofReal (Real.exp (x - η * n + Real.log β)) = ENNReal.ofReal (Real.exp x) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Real.exp (-η) := ⟨_, rfl⟩
  rw [← hρ] at hβ
  have hρ1 : ρ < 1 := by rw [hρ, Real.exp_lt_one_iff]; linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact (Real.exp_pos _).le
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hterm : ∀ n : ℕ, Real.exp (x - η * n + Real.log β) = Real.exp x * β * ρ ^ n := by
    intro n
    rw [hρ, ← Real.exp_nat_mul, Real.exp_add, Real.exp_log hβ0, sub_eq_add_neg, Real.exp_add,
      show -(η * n) = n * -η by ring]
    ring
  simp_rw [hterm]
  have hsum : Summable fun n : ℕ => Real.exp x * β * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum, tsum_mul_left,
    tsum_geometric_of_lt_one hρ0 hρ1, ← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have : (1 - ρ) ≠ 0 := by linarith
  rw [hβ]
  field_simp

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **A summable tail for the internal diameter of the unit square, uniform over the whole-plane GFFs**
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, the union bound of the proof of Proposition 3.10 with
thresholds depending on `k`, their Proposition 3.1 entering as `huniv`). Let `𝔇` be a γ-LQG metric with `ξ > 0`, `h` a
whole-plane GFF on `(Ω, P)`, and `0 < δ < θ < ξ (Q - 2) log 2`. Suppose that for every whole-plane GFF `h'` on `(Ω, P)`
and every `n` the probability that `[0, 1]²` has no half crossings of `D_{h'}`-length at most `e^{δ n}` is at most `p n`,
where `∑ₙ 4ⁿ p n < ∞`. Then for every `ε > 0` there is `ψ` with `∑ₖ ψ k < ∞` such that for every whole-plane GFF `h'` on
`(Ω, P)` and every `k`, the probability that some two points of `[0, 1]²` are at `D_{h'}`-internal distance in `[0, 1]²`
more than `e^{ε k}` is at most `ψ k`. -/
theorem IsLQGMetric.exists_unitSquare_internalMetric_tail (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {θ δ ε : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) (hδ0 : 0 < δ) (hε : 0 < ε) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∃ ψ : ℕ → ℝ≥0∞, ∑' k, ψ k ≠ ⊤ ∧ ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
        P {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
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
  -- the deterministic step: short half crossings at every level bound the internal diameter by `e^{ε k}`
  have hsub : {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
        ENNReal.ofReal (Real.exp (ε * k))} ⊆ {ω | ¬ IsEuclideanLengthMetric (𝔇 (hC' ω))} ∪
      ⋃ n : ℕ, ⋃ i ∈ Finset.range (2 ^ n), ⋃ j ∈ Finset.range (2 ^ n),
        {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) (0 + i * (1 / 2 ^ n)) (0 + (i + 1) * (1 / 2 ^ n))
          (0 + j * (1 / 2 ^ n)) (0 + (j + 1) * (1 / 2 ^ n)) (l k n)} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_iUnion, mem_ofPred_eq, Finset.mem_range, not_or, not_exists, not_not] at hcon
    obtain ⟨hD, hcr⟩ := hcon
    apply hω
    intro u hu v hv
    have hu' : u ∈ Icc 0 (0 + 1) ×ℂ Icc 0 (0 + 1) := by simpa only [zero_add] using hu
    have hv' : v ∈ Icc 0 (0 + 1) ×ℂ Icc 0 (0 + 1) := by simpa only [zero_add] using hv
    have h1 := hD.internalMetric_le_of_hasShortHalfCrossings one_pos (l k)
      (fun n i j hi hj => hcr n i hi j hj) hu' hv'
    simp only [zero_add] at h1
    refine h1.trans ?_
    have h6 : 6 * ∑' n : ℕ, l k n = ENNReal.ofReal (Real.exp (ε * k)) := by
      rw [hl]; exact six_mul_tsum_ofReal_exp_geometric hθδ hβ (ε * k)
    have hsplit : ∑' n : ℕ, l k n = l k 0 + ∑' n : ℕ, l k (n + 1) :=
      tsum_eq_zero_add' ENNReal.summable
    rw [← h6, hsplit]
    calc 3 * (l k 0 + 2 * ∑' n, l k (n + 1)) = 3 * l k 0 + 6 * ∑' n, l k (n + 1) := by
          rw [mul_add, ← mul_assoc]; norm_num
      _ ≤ 6 * l k 0 + 6 * ∑' n, l k (n + 1) := by gcongr; norm_num
      _ = 6 * (l k 0 + ∑' n, l k (n + 1)) := by rw [mul_add]
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
