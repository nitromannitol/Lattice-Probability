import LatticeProb.LQG.InternalMetricWeylScalingShell
import LatticeProb.LQG.CornerSquareWeylChaining
import LatticeProb.LQG.InternalMetricUnitSquareTail
import LatticeProb.LQG.InternalMetricOfTriangle

/-!
# Weyl-scaled LQG internal diameters of the corner squares at a log singularity

Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF and `E` almost surely the Weyl scaling of `D_h` by `ξ f`,
`f = -α log |·|`, with `α < Q`. Let `S = [a, a + s] × [b, b + s]` with `a, b ∈ {0, -s}`, so that `0` is a corner of
`S`, and let `Sₘ = 2^{-m} S` be its corner square of side `s 2^{-m}`. We show that the (outer) probability that the
`E`-internal diameter of `Sₘ` exceeds `ε` tends to `0` as `m → ∞`.

The argument is the quantitative form of the corner chaining
(`LatticeProb.LQG.IsLQGMetric.ae_internalMetric_weylScaling_cornerSquare_le`): every point of `Sₘ \ {0}` lies in one of
the shells of `Sₘ`, each consisting of three squares of side `tₙ = s 2^{-n-1}` (`n ≥ m`) at distance between `tₙ` and
`3 tₙ` from `0`. On each such square the internal `D_h`-diameter is `e^{ξ (h_{tₙ}(c) + Q log tₙ)}` times the internal
diameter of the unit square for a recentred whole-plane GFF, and the weight `e^{ξ f}` is at most
`3^{ξ |α|} tₙ^{-ξ α₊}`. Outside an event of probability at most `3 ∑_{n ≥ m} (ψ n + q n)`, where `ψ` is the unit-square
tail and `q n` the worst circle-average tail at level `n`, the weighted diameters decay like `e^{-η n / 2}`, and the
chaining over the shells (`IsEuclideanLengthMetric.internalMetric_weylScaling_le_tsum_of_shells`) bounds
`E(u, 0; Sₘ)` by a tail of a geometric series. The bound is a countable union bound, so it holds for outer measure.

This is the corner-cell step of the proof that the metric of a whole-plane GFF plus a logarithmic singularity has
small internal diameters near the singularity (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, proof of
Proposition 3.17), with their Proposition 3.1 as the hypothesis `huniv`.

## Main statements

* `LatticeProb.LQG.tsum_iSup₂_measure_ne_top`: if `∑ₙ P(Gₙ(cₙ)) < ∞` for every admissible sequence `cₙ ∈ Aₙ`, then
  `∑ₙ sup_{c ∈ Aₙ} P(Gₙ(c)) < ∞`.
* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_cornerSquare_le`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- **Worst-case tails.** Let `P` be a finite measure. If `∑ₙ P(Gₙ(cₙ)) < ∞` for every sequence with `cₙ ∈ Aₙ`
(and every `Aₙ` is nonempty), then `∑ₙ sup_{c ∈ Aₙ} P(Gₙ(c)) < ∞`. -/
theorem tsum_iSup₂_measure_ne_top {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {A : ℕ → Set ι} (hA : ∀ n, (A n).Nonempty) {G : ℕ → ι → Set Ω}
    (h : ∀ c : ℕ → ι, (∀ n, c n ∈ A n) → ∑' n, P (G n (c n)) ≠ ⊤) :
    ∑' n, ⨆ c ∈ A n, P (G n c) ≠ ⊤ := by
  have key : ∀ n, ∃ c ∈ A n, ⨆ c ∈ A n, P (G n c) ≤ 2 * P (G n c) := by
    intro n
    by_cases hp : ⨆ c ∈ A n, P (G n c) = 0
    · obtain ⟨c, hc⟩ := hA n
      exact ⟨c, hc, by rw [hp]; exact zero_le⟩
    · have hpt : ⨆ c ∈ A n, P (G n c) ≠ ⊤ :=
        ne_top_of_le_ne_top (measure_ne_top P univ) (iSup₂_le fun c _ => measure_mono (subset_univ _))
      have hlt := ENNReal.half_lt_self hp hpt
      simp only [lt_iSup_iff] at hlt
      obtain ⟨c, hc, hlt⟩ := hlt
      refine ⟨c, hc, ?_⟩
      rw [mul_comm]
      exact (ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top).1 hlt.le
  choose c hc hle using key
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (h c hc)

/-- Tails of a geometric series: `∑_{k} e^{c - η (m + k)} → 0` as `m → ∞`, for `η > 0`. -/
theorem tendsto_tsum_ofReal_exp_sub_mul_add {c η : ℝ} (hη : 0 < η) :
    Tendsto (fun m : ℕ => ∑' k : ℕ, ENNReal.ofReal (Real.exp (c - η * ((m + k : ℕ) : ℝ)))) atTop (𝓝 0) := by
  have hs : Summable fun n : ℕ => Real.exp (c - η * n) := by
    have h := (Real.summable_exp_nat_mul_iff.2 (neg_lt_zero.2 hη)).mul_left (Real.exp c)
    refine h.congr fun n => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have h := ENNReal.tendsto_sum_nat_add (fun n : ℕ => ENNReal.ofReal (Real.exp (c - η * n))) (by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hs]
    exact ENNReal.ofReal_ne_top)
  refine h.congr fun m => tsum_congr fun k => ?_
  rw [Nat.add_comm]

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Small Weyl-scaled internal diameters of the corner squares at a log singularity**
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, the corner argument of the proof of Proposition 3.17, with
their Proposition 3.1 as the hypothesis `huniv`). Let `𝔇` be a γ-LQG metric with `ξ > 0`, `h` a whole-plane GFF,
`α < Q`, and `E` a.s. the Weyl scaling of `D_h` by `ξ f`, `f = -α log |·|`. Let `0 < δ < θ < ξ (Q - 2) log 2` and
suppose that the unit-square crossing tail `p` of every whole-plane GFF on `(Ω, P)` satisfies `∑ₙ 4ⁿ p n < ∞`. Let
`a, b ∈ {0, -s}`, `s > 0`, and let `Sₘ = [a 2^{-m}, (a + s) 2^{-m}] × [b 2^{-m}, (b + s) 2^{-m}]` be the corner square
at `0` of side `s 2^{-m}`. Then for every `ε > 0` the (outer) probability that two points of `Sₘ` have `E`-internal
distance in `Sₘ` larger than `ε` tends to `0` as `m → ∞`. -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_cornerSquare_le
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) (hδ0 : 0 < δ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {α : ℝ} (hα : α < lqgQ γ) {E : Ω → ℂ → ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) x y)
    {a b s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) (hb : b = 0 ∨ b = -s) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => P {ω | ¬ ∀ u ∈ Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
        Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m), ∀ v ∈ Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
        Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m),
          internalMetric (E ω) (Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
            Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m)) u v ≤ ENNReal.ofReal ε}) atTop (𝓝 0) := by
  have hPm := hG.isProbabilityMeasure
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `Q > 2`, hence `α₊ = max α 0 < Q`
  have hQ2 : 0 < lqgQ γ - 2 := by
    by_contra h
    replace h := not_lt.1 h
    have : ξ * (lqgQ γ - 2) * Real.log 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hξ.le h) hlog2.le
    linarith
  set αp : ℝ := max α 0 with hαp
  have hαp0 : 0 ≤ αp := le_max_right _ _
  have hααp : α ≤ αp := le_max_left _ _
  have hQα : 0 < lqgQ γ - αp := sub_pos.2 (max_lt hα (by linarith))
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ξ * (lqgQ γ - αp) * Real.log 2 / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηlt : η < ξ * (lqgQ γ - αp) * Real.log 2 := by
    have : 0 < ξ * (lqgQ γ - αp) * Real.log 2 := by positivity
    rw [hη]; linarith
  -- the unit-square tail at rate `η / 2`
  obtain ⟨ψ, hψ, htail⟩ :=
    h𝔇.exists_unitSquare_internalMetric_tail hG hξ hθ hδ hδ0 (half_pos hη0) huniv hp
  -- the worst circle-average tail at level `n`, radius `t / 2^n`
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = s / 2 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; exact half_pos hs
  set Gev : ℕ → ℂ → Set Ω := fun n c => {ω | -η * n < ξ * (hcirc ω (t / 2 ^ n) c +
    (lqgQ γ - αp) * Real.log (t / 2 ^ n))} with hGev
  set q : ℕ → ℝ≥0∞ := fun n => ⨆ c ∈ {c : ℂ | ‖c‖ ≤ 3 * (t / 2 ^ n)}, P (Gev n c) with hq_def
  have hq : ∑' n, q n ≠ ⊤ :=
    tsum_iSup₂_measure_ne_top (A := fun n => {c : ℂ | ‖c‖ ≤ 3 * (t / 2 ^ n)}) (G := Gev)
      (fun n => ⟨0, show ‖(0 : ℂ)‖ ≤ 3 * (t / 2 ^ n) by
        rw [norm_zero]; exact (mul_pos three_pos (div_pos ht (by positivity))).le⟩)
      fun c hc => hG.tsum_measure_shell_circle_exp_ne_top ht hξ hηlt (M := 3) hc
  set F : ℕ → ℝ≥0∞ := fun n => ψ n + q n with hF_def
  have hF : ∑' n, F n ≠ ⊤ := by
    rw [hF_def, ENNReal.tsum_add]
    exact ENNReal.add_ne_top.2 ⟨hψ, hq⟩
  have h3F : Tendsto (fun m : ℕ => 3 * ∑' k, F (k + m)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := 3) (ENNReal.tendsto_sum_nat_add F hF)
      (Or.inr ENNReal.ofNat_ne_top)
    rwa [mul_zero] at h
  -- the deterministic thresholds
  have hT4 : ∀ᶠ m : ℕ in atTop, 4 * (3 * ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 -
      η / 2 * ((m + k : ℕ) : ℝ)))) ≤ ENNReal.ofReal ε := by
    have h := ENNReal.Tendsto.const_mul (a := 4) (ENNReal.Tendsto.const_mul (a := 3)
      (tendsto_tsum_ofReal_exp_sub_mul_add (c := ξ * |α| * Real.log 3) (half_pos hη0))
      (Or.inr ENNReal.ofNat_ne_top)) (Or.inr ENNReal.ofNat_ne_top)
    rw [mul_zero, mul_zero] at h
    exact h.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))
  have hr1ev : ∀ᶠ m : ℕ in atTop, t / 2 ^ m ≤ 1 := by
    have h : Tendsto (fun m : ℕ => t / 2 ^ m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    exact h.eventually (ge_mem_nhds one_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3F
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hT4, hr1ev] with m hm hm1
  obtain ⟨T, hT_def⟩ : ∃ T : ℝ≥0∞, T = 3 * ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 -
      η / 2 * ((m + k : ℕ) : ℝ))) := ⟨_, rfl⟩
  rw [← hT_def] at hm
  -- the shells of the corner square `Sₘ`
  have hsm : 0 < s / 2 ^ m := by positivity
  have ham : a / 2 ^ m = 0 ∨ a / 2 ^ m = -(s / 2 ^ m) := by
    rcases ha with h | h
    · left; rw [h, zero_div]
    · right; rw [h, neg_div]
  have hbm : b / 2 ^ m = 0 ∨ b / 2 ^ m = -(s / 2 ^ m) := by
    rcases hb with h | h
    · left; rw [h, zero_div]
    · right; rw [h, neg_div]
  obtain ⟨xc, yc, Q, hQ, hQS, hQn, hc, hcover, hpre, hmeet⟩ :=
    LatticeProb.Topology.exists_cornerSquareShells hsm ham hbm
  have hrk : ∀ k : ℕ, s / 2 ^ m / 2 ^ (k + 1) = t / 2 ^ (m + k) := fun k => by
    rw [ht_def, pow_add, pow_succ, div_div, div_div]
    congr 1
    ring
  simp only [hrk] at hQ hQn hc
  have hrpos : ∀ k : ℕ, 0 < t / 2 ^ (m + k) := fun k => div_pos ht (by positivity)
  have hr1 : ∀ k : ℕ, t / 2 ^ (m + k) ≤ 1 := fun k => by
    refine le_trans ?_ hm1
    gcongr
    · norm_num
    · omega
  have hlogr : ∀ k : ℕ, Real.log (t / 2 ^ (m + k)) ≤ 0 := fun k => Real.log_nonpos (hrpos k).le (hr1 k)
  have hz : (0 : ℂ) ∈ Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m) := by
    rw [Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, mem_Icc, mem_Icc]
    rcases ham with h | h <;> rcases hbm with h' | h' <;> rw [h, h'] <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hQimg : ∀ k i, Q k i = (fun w : ℂ => ((t / 2 ^ (m + k) : ℝ) : ℂ) * w + ⟨xc k i, yc k i⟩) ''
      (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) := by
    intro k i
    rw [hQ k i, affine_image_reProdIm (hrpos k)]
    simp only [mul_zero, zero_add, mul_one]
    rw [add_comm (xc k i), add_comm (yc k i)]
  have hρ : Tendsto (fun k : ℕ => 4 * (t / 2 ^ (m + k))) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (4 * (t / 2 ^ m)) * (1 / 2 : ℝ) ^ k) atTop (𝓝 ((4 * (t / 2 ^ m)) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    rw [pow_add, one_div, inv_pow]
    field_simp
  have hRρ : ∀ k, (⋃ i, Q k i) ⊆ Metric.ball 0 (4 * (t / 2 ^ (m + k))) := fun k w hw => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    rw [mem_ball_zero_iff]
    have := (hQn k i w hi).2
    linarith [hrpos k]
  -- the weights on the shells
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, ∀ k, B k = -(ξ * αp * Real.log (t / 2 ^ (m + k))) + ξ * |α| * Real.log 3 :=
    ⟨_, fun _ => rfl⟩
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    rw [hB k]
    have h1 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hξ.le hαp0) (hlogr k)
    have h2 : 0 ≤ ξ * |α| * Real.log 3 :=
      mul_nonneg (mul_nonneg hξ.le (abs_nonneg α)) (Real.log_nonneg (by norm_num))
    linarith
  have hBR : ∀ k, ∀ w ∈ ⋃ i, Q k i, ξ * (fun w : ℂ => -α * Real.log ‖w‖) w ≤ B k := by
    intro k w hw
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    obtain ⟨h1, h2⟩ := hQn k i w hi
    have h := mul_neg_mul_log_norm_le (α := α) hξ.le (hrpos k) h1 h2
    have h3 := mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_left hααp hξ.le) (hlogr k)
    show ξ * (-α * Real.log ‖w‖) ≤ B k
    rw [hB k]
    linarith
  -- the bad events
  set A : ℕ → Fin 3 → Set Ω := fun k i => {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
    ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      internalMetric (𝔇 (recentredPairing hC hcirc (t / 2 ^ (m + k)) ⟨xc k i, yc k i⟩ ω))
        (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤ ENNReal.ofReal (Real.exp (η / 2 * ((m + k : ℕ) : ℝ)))}
    with hA_def
  have hA : ∀ k i, P (A k i) ≤ ψ (m + k) := fun k i =>
    htail _ _ (isWholePlaneGFF_recentredPairing hG (hrpos k) _) (m + k)
  have hGq : ∀ k i, P (Gev (m + k) ⟨xc k i, yc k i⟩) ≤ q (m + k) := fun k i =>
    le_iSup₂ (f := fun c (_ : c ∈ {c : ℂ | ‖c‖ ≤ 3 * (t / 2 ^ (m + k))}) => P (Gev (m + k) c))
      (⟨xc k i, yc k i⟩ : ℂ) (hc k i)
  have hbad : P (⋃ k, ⋃ i, (A k i ∪ Gev (m + k) ⟨xc k i, yc k i⟩)) ≤ 3 * ∑' k, F (k + m) := by
    calc P (⋃ k, ⋃ i, (A k i ∪ Gev (m + k) ⟨xc k i, yc k i⟩))
        ≤ ∑' k, ∑ i, (P (A k i) + P (Gev (m + k) ⟨xc k i, yc k i⟩)) :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k => (measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun i _ => measure_union_le _ _))
      _ ≤ ∑' k, ∑ _i : Fin 3, F (m + k) :=
          ENNReal.tsum_le_tsum fun k => Finset.sum_le_sum fun i _ => add_le_add (hA k i) (hGq k i)
      _ = 3 * ∑' k, F (k + m) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
            ENNReal.tsum_mul_left, Nat.add_comm m]
  have hae := ae_all_iff.2 fun k : ℕ => ae_all_iff.2 fun i : Fin 3 =>
    h𝔇.ae_internalMetric_scaling hG (hrpos k) (⟨xc k i, yc k i⟩ : ℂ)
  refine le_trans (measure_mono_ae ?_) hbad
  filter_upwards [hae, hE, h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hsc hEω hD hω
  by_contra hcon
  simp only [mem_iUnion, mem_union, not_exists, not_or] at hcon
  apply hω
  have hAk : ∀ k i, ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      internalMetric (𝔇 (recentredPairing hC hcirc (t / 2 ^ (m + k)) ⟨xc k i, yc k i⟩ ω))
        (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤ ENNReal.ofReal (Real.exp (η / 2 * ((m + k : ℕ) : ℝ))) := by
    intro k i
    have h := (hcon k i).1
    simp only [hA_def, mem_ofPred_eq, not_not] at h
    exact h
  have hGk : ∀ k i, ξ * (hcirc ω (t / 2 ^ (m + k)) ⟨xc k i, yc k i⟩ +
      (lqgQ γ - αp) * Real.log (t / 2 ^ (m + k))) ≤ -η * ((m + k : ℕ) : ℝ) := by
    intro k i
    have h := (hcon k i).2
    simp only [hGev, mem_ofPred_eq, not_lt] at h
    exact h
  -- the triangle inequality and the symmetry of the internal `E`-metric
  have htriE : ∀ U x y z, internalMetric (E ω) U x z ≤ internalMetric (E ω) U x y + internalMetric (E ω) U y z :=
    fun U => internalMetric_triangle_of_ofReal_triangle
      (fun x y z => by rw [hEω, hEω, hEω]; exact hD.weylScaling_triangle _ _ _ _ _) U
  have hsymmE : ∀ U x y, internalMetric (E ω) U x y = internalMetric (E ω) U y x :=
    fun U => internalMetric_symm_of_ofReal_symm
      (fun x y => by rw [hEω, hEω]; exact hD.weylScaling_symm _ _ _ _) U
  -- the internal `D_h`-diameters of the shell squares
  obtain ⟨d, hd_def⟩ : ∃ d : ℕ → Fin 3 → ℝ≥0∞, ∀ k i, d k i =
      ENNReal.ofReal (Real.exp (ξ * (hcirc ω (t / 2 ^ (m + k)) ⟨xc k i, yc k i⟩ +
        lqgQ γ * Real.log (t / 2 ^ (m + k))))) *
        ENNReal.ofReal (Real.exp (η / 2 * ((m + k : ℕ) : ℝ))) := ⟨_, fun _ _ => rfl⟩
  have hd : ∀ k i, ∀ u ∈ Q k i, ∀ v ∈ Q k i, internalMetric (𝔇 (hC ω)) (Q k i) u v ≤ d k i := by
    intro k i u hu v hv
    rw [hQimg k i] at hu hv ⊢
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    beta_reduce
    rw [hsc k i _ u' v', hd_def k i]
    gcongr
    exact hAk k i u' hu' v' hv'
  have hMR : ∀ k, ∀ u ∈ ⋃ i, Q k i, ∀ v ∈ ⋃ i, Q k i,
      internalMetric (𝔇 (hC ω)) (⋃ i, Q k i) u v ≤ ∑ i, d k i := by
    intro k
    have e : (⋃ i ∈ (Finset.univ : Finset (Fin 3)), Q k i) = ⋃ i, Q k i := by simp
    have h := hD.internalMetric_biUnion_le_sum (F := Finset.univ) (R := Q k) (by rw [e]; exact hpre k)
      (fun i _ => by rw [hQ k i]; exact isClosed_Icc.reProdIm isClosed_Icc) (A := d k)
      (fun i _ => hd k i)
    rw [e] at h
    exact h
  have hterm : ∀ k, ENNReal.ofReal (Real.exp (B k)) * ∑ i, d k i ≤
      3 * ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 - η / 2 * ((m + k : ℕ) : ℝ))) := by
    intro k
    rw [Finset.mul_sum]
    calc ∑ i, ENNReal.ofReal (Real.exp (B k)) * d k i
        ≤ ∑ _i : Fin 3, ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 - η / 2 * ((m + k : ℕ) : ℝ))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hd_def k i, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have hg := hGk k i
          rw [hB k]
          linarith
      _ = 3 * ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 - η / 2 * ((m + k : ℕ) : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  -- chaining to the corner over the shells
  have hchain : ∀ j, ∀ u ∈ ⋃ i, Q j i, internalMetric (E ω) (Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
      Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m)) u 0 ≤ T := by
    intro j u hu
    have hW := hD.internalMetric_weylScaling_le_tsum_of_shells hEω hz (R := fun k => ⋃ i, Q k i)
      (fun k => iUnion_subset fun i => hQS k i) hmeet hρ hRρ hB0 hBR (M := fun k => ∑ i, d k i) hMR hu
    refine hW.trans ?_
    calc ∑' k, ENNReal.ofReal (Real.exp (B (j + k))) * ∑ i, d (j + k) i
        ≤ ∑' k, 3 * ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 - η / 2 * ((m + (j + k) : ℕ) : ℝ))) :=
          ENNReal.tsum_le_tsum fun k => hterm (j + k)
      _ ≤ ∑' k, 3 * ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 - η / 2 * ((m + k : ℕ) : ℝ))) :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun k => j + k) (add_right_injective j)
            (fun k => 3 * ENNReal.ofReal (Real.exp (ξ * |α| * Real.log 3 - η / 2 * ((m + k : ℕ) : ℝ))))
      _ = T := by rw [ENNReal.tsum_mul_left, hT_def]
  have hall : ∀ u ∈ Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m),
      internalMetric (E ω) (Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
        Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m)) u 0 ≤ T + T := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      have hw : (⟨xc 0 0, yc 0 0⟩ : ℂ) ∈ ⋃ i, Q 0 i := by
        refine mem_iUnion.2 ⟨0, ?_⟩
        rw [hQ 0 0]
        simp only [Complex.mem_reProdIm, mem_Icc]
        refine ⟨⟨le_rfl, ?_⟩, ⟨le_rfl, ?_⟩⟩ <;> linarith [hrpos 0]
      refine (htriE _ _ (⟨xc 0 0, yc 0 0⟩ : ℂ) _).trans ?_
      rw [hsymmE _ 0]
      exact add_le_add (hchain 0 _ hw) (hchain 0 _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, u ∈ ⋃ i, Q j i := by
        rcases hcover hu with h | h
        · exact absurd h hu0
        · exact mem_iUnion.1 h
      exact (hchain j u hj).trans le_self_add
  intro u hu v hv
  calc _ ≤ _ := htriE _ u 0 v
    _ = _ := by rw [hsymmE _ 0 v]
    _ ≤ (T + T) + (T + T) := add_le_add (hall u hu) (hall v hv)
    _ = 4 * T := by ring
    _ ≤ ENNReal.ofReal ε := hm

end LatticeProb.LQG
