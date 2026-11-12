import LatticeProb.LQG.InternalMetricDyadicSubsquareTail
import LatticeProb.LQG.InternalMetricWeylScalingAtPoint
import LatticeProb.Gauss.CircleAverageShellSum

/-!
# Uniformly small Weyl-scaled internal diameters on the dyadic shells around a log singularity

Let `E = e^{ξ f} · D_h` with `f = -α log |·|` and `α < Q`, where `D_h` is the γ-LQG metric of a whole-plane GFF `h`.
Fix a closed square `t [0, 1]² + c` at distance between `t` and `3t` from `0`, and its dilations `2^{-k} (t [0, 1]² + c)`
by `2^{-k}` (one cell of the `k`-th dyadic shell around `0`). On the `k`-th dilation the weight `e^{ξ f}` is at most
`(t 2^{-k})^{-ξ α} 3^{ξ |α|}`, and the coordinate change of the LQG metric bounds `E`-internal distances there by
`e^{ξ (h_{t 2^{-k}}(2^{-k} c) + Q log (t 2^{-k}))}` times internal distances of the LQG metric of a recentred whole-plane
GFF. The circle averages along the shell centres have summable tails at the exponential rate `ξ (Q - α) log 2 / 2`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, the estimate (3.70) of the proof of Proposition 3.17), and the
internal diameters of all the dyadic subsquares of the unit square have a summable tail uniformly over whole-plane GFFs.
Hence, with probability tending to `1` as `K → ∞`, simultaneously for all shells `k ≥ K` and all closed dyadic subsquares
of the shell cell (of every level), the `E`-internal diameters are at most `ε`.

## Main statements

* `LatticeProb.LQG.mul_neg_mul_log_norm_le_annulus`: the weight bound on an annulus `r ≤ |w| ≤ 3 r`.
* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_shell_le`: the probability that
  some subsquare of some shell cell of index `k ≥ K` has `E`-internal diameter larger than `ε` tends to `0`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

/-- **The weight of a log singularity on an annulus.** If `r ≤ |w| ≤ 3 r` with `r > 0` and `ξ ≥ 0`, then
`ξ (-α log |w|) ≤ -ξ α log r + ξ |α| log 3`. -/
theorem mul_neg_mul_log_norm_le_annulus {ξ α r : ℝ} (hξ : 0 ≤ ξ) (hr : 0 < r) {w : ℂ} (h1 : r ≤ ‖w‖)
    (h2 : ‖w‖ ≤ 3 * r) : ξ * (-α * Real.log ‖w‖) ≤ -(ξ * α * Real.log r) + ξ * |α| * Real.log 3 := by
  have hL0 : Real.log r ≤ Real.log ‖w‖ := Real.log_le_log hr h1
  have hL3 : Real.log ‖w‖ ≤ Real.log 3 + Real.log r := by
    rw [← Real.log_mul (by norm_num) hr.ne']
    exact Real.log_le_log (hr.trans_le h1) h2
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rcases le_or_gt 0 α with h | h
  · rw [abs_of_nonneg h]
    nlinarith [mul_nonneg (mul_nonneg hξ h) (sub_nonneg.2 hL0), mul_nonneg (mul_nonneg hξ h) hlog3]
  · rw [abs_of_neg h]
    nlinarith [mul_nonneg (mul_nonneg hξ (neg_nonneg.2 h.le)) (sub_nonneg.2 hL3)]

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Uniformly small Weyl-scaled internal diameters on the dyadic shells around a log singularity**
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, the shell argument of the proof of Proposition 3.17, with their
Proposition 3.1 as the hypothesis `huniv`). Let `𝔇` be a γ-LQG metric with `ξ > 0`, `h` a whole-plane GFF, `α < Q`, and
`E` a.s. the Weyl scaling of `D_h` by `ξ f`, `f = -α log |·|`. Let `0 < δ < θ < ξ (Q - 2) log 2` and suppose that the
unit-square crossing tail `p` of every whole-plane GFF on `(Ω, P)` satisfies `∑ₙ 4ⁿ p n < ∞`. Let `t > 0` and `c ∈ ℂ` with
`t ≤ |t y + c| ≤ 3 t` for `y ∈ [0, 1]²`, and let `φ_k (x) = t 2^{-k} x + 2^{-k} c`. Then for every `ε > 0` the (outer)
probability that for some `k ≥ K` some closed dyadic subsquare `S` of `[0, 1]²` (of any level) contains points `u, v`
with `E`-internal distance in `φ_k (S)` between `φ_k (u)` and `φ_k (v)` larger than `ε` tends to `0` as `K → ∞`. -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_shell_le
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) (hδ0 : 0 < δ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {α : ℝ} (hα : α < lqgQ γ) {E : Ω → ℂ → ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) x y)
    {t : ℝ} (ht : 0 < t) {c : ℂ}
    (hc : ∀ y ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, t ≤ ‖(t : ℂ) * y + c‖ ∧ ‖(t : ℂ) * y + c‖ ≤ 3 * t)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun K : ℕ => P {ω | ¬ ∀ k : ℕ, K ≤ k → ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ u ∈ closedDyadicSubsquare 0 0 1 n i j, ∀ v ∈ closedDyadicSubsquare 0 0 1 n i j,
        internalMetric (E ω)
          ((fun x : ℂ => ((t / 2 ^ k : ℝ) : ℂ) * x + (2 ^ k : ℂ)⁻¹ * c) '' closedDyadicSubsquare 0 0 1 n i j)
          (((t / 2 ^ k : ℝ) : ℂ) * u + (2 ^ k : ℂ)⁻¹ * c) (((t / 2 ^ k : ℝ) : ℂ) * v + (2 ^ k : ℂ)⁻¹ * c) ≤
            ENNReal.ofReal ε}) atTop (𝓝 0) := by
  -- the exponential rate `η` of the shell circle averages
  have hQα : 0 < lqgQ γ - α := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ξ * (lqgQ γ - α) * Real.log 2 / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηlt : η < ξ * (lqgQ γ - α) * Real.log 2 := by
    have : 0 < ξ * (lqgQ γ - α) * Real.log 2 := by positivity
    rw [hη]; linarith
  -- the uniform tail of the internal diameters of all the dyadic subsquares at threshold `e^{η k / 2}`
  obtain ⟨ψ, hψ, htail⟩ :=
    h𝔇.exists_closedDyadicSubsquare_internalMetric_tail hG hξ hθ hδ hδ0 (half_pos hη0) huniv hp
  -- the circle averages at the shell centres
  have hc0 : ‖c‖ ≤ 3 * t := by
    have h := (hc 0 (by simp [Complex.mem_reProdIm])).2
    simpa using h
  have hcn : ∀ k : ℕ, ‖(2 ^ k : ℂ)⁻¹ * c‖ ≤ 3 * (t / 2 ^ k) := by
    intro k
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_mul, norm_inv, norm_pow, h2, ← mul_div_assoc, inv_mul_eq_div]
    gcongr
  have hq : ∑' k : ℕ, P {ω | -η * k < ξ * (hcirc ω (t / 2 ^ k) ((2 ^ k : ℂ)⁻¹ * c) +
      (lqgQ γ - α) * Real.log (t / 2 ^ k))} ≠ ⊤ :=
    hG.tsum_measure_shell_circle_exp_ne_top (c := fun k : ℕ => (2 ^ k : ℂ)⁻¹ * c) ht hξ hηlt hcn
  set A : ℕ → Set Ω := fun k => {ω | ¬ ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
    ∀ u ∈ closedDyadicSubsquare 0 0 1 n i j, ∀ v ∈ closedDyadicSubsquare 0 0 1 n i j,
      internalMetric (𝔇 (recentredPairing hC hcirc (t / 2 ^ k) ((2 ^ k : ℂ)⁻¹ * c) ω))
        (closedDyadicSubsquare 0 0 1 n i j) u v ≤ ENNReal.ofReal (Real.exp (η / 2 * k))} with hA_def
  set G : ℕ → Set Ω := fun k => {ω | -η * k < ξ * (hcirc ω (t / 2 ^ k) ((2 ^ k : ℂ)⁻¹ * c) +
      (lqgQ γ - α) * Real.log (t / 2 ^ k))} with hG_def
  have hA : ∀ k, P (A k) ≤ ψ k := fun k =>
    htail _ _ (isWholePlaneGFF_recentredPairing hG (by positivity) _) k
  set F : ℕ → ℝ≥0∞ := fun k => ψ k + P (G k) with hF_def
  have hF : ∑' k, F k ≠ ⊤ := by
    rw [hF_def, ENNReal.tsum_add]
    exact ENNReal.add_ne_top.2 ⟨hψ, hq⟩
  -- the coordinate change on every shell, almost surely
  have hae := ae_all_iff.2 fun k : ℕ =>
    h𝔇.ae_internalMetric_weylScaling_affine_image_le (f := fun w : ℂ => -α * Real.log ‖w‖) hG
      (r := t / 2 ^ k) (by positivity) ((2 ^ k : ℂ)⁻¹ * c) hE
  -- the deterministic threshold
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt ((ξ * |α| * Real.log 3 - Real.log ε) / (η / 2))
  have hK₀' : ∀ k : ℕ, K₀ ≤ k → ξ * |α| * Real.log 3 - η / 2 * k ≤ Real.log ε := by
    intro k hk
    have h := (div_lt_iff₀ (half_pos hη0)).1 (hK₀.trans_le (Nat.cast_le.2 hk))
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ENNReal.tendsto_sum_nat_add F hF)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop K₀] with K hK
  have hsub : P {ω | ¬ ∀ k : ℕ, K ≤ k → ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ u ∈ closedDyadicSubsquare 0 0 1 n i j, ∀ v ∈ closedDyadicSubsquare 0 0 1 n i j,
        internalMetric (E ω)
          ((fun x : ℂ => ((t / 2 ^ k : ℝ) : ℂ) * x + (2 ^ k : ℂ)⁻¹ * c) '' closedDyadicSubsquare 0 0 1 n i j)
          (((t / 2 ^ k : ℝ) : ℂ) * u + (2 ^ k : ℂ)⁻¹ * c) (((t / 2 ^ k : ℝ) : ℂ) * v + (2 ^ k : ℂ)⁻¹ * c) ≤
            ENNReal.ofReal ε} ≤ P (⋃ m : ℕ, (A (m + K) ∪ G (m + K))) := by
    refine measure_mono_ae ?_
    filter_upwards [hae] with ω hpr hω
    by_contra hcon
    simp only [mem_iUnion, mem_union, not_exists, not_or] at hcon
    apply hω
    intro k hk n i j hi hj u hu v hv
    obtain ⟨hAk, hGk⟩ := hcon (k - K)
    rw [Nat.sub_add_cancel hk] at hAk hGk
    simp only [hA_def, hG_def, mem_ofPred_eq, not_not, not_lt] at hAk hGk
    have hB : ∀ x ∈ closedDyadicSubsquare 0 0 1 n i j,
        ξ * (fun w : ℂ => -α * Real.log ‖w‖) (((t / 2 ^ k : ℝ) : ℂ) * x + (2 ^ k : ℂ)⁻¹ * c) ≤
          -(ξ * α * Real.log (t / 2 ^ k)) + ξ * |α| * Real.log 3 := by
      intro x hx
      have hx1 : x ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
        simpa only [zero_add] using closedDyadicSubsquare_subset (a := 0) (b := 0) one_pos hi hj hx
      obtain ⟨hlo, hhi⟩ := hc x hx1
      have hw : ((t / 2 ^ k : ℝ) : ℂ) * x + (2 ^ k : ℂ)⁻¹ * c = (2 ^ k : ℂ)⁻¹ * ((t : ℂ) * x + c) := by
        push_cast; ring
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      have hnorm : ‖((t / 2 ^ k : ℝ) : ℂ) * x + (2 ^ k : ℂ)⁻¹ * c‖ = ‖(t : ℂ) * x + c‖ / 2 ^ k := by
        rw [hw, norm_mul, norm_inv, norm_pow, h2, inv_mul_eq_div]
      have hpos : 0 < t / 2 ^ k := by positivity
      refine mul_neg_mul_log_norm_le_annulus hξ.le hpos ?_ ?_
      · rw [hnorm]; gcongr
      · rw [hnorm, ← mul_div_assoc]; gcongr
    refine (hpr k _ _ hB u v).trans ?_
    have hAuv := hAk n i j hi hj u hu v hv
    calc _ ≤ ENNReal.ofReal (Real.exp (-(ξ * α * Real.log (t / 2 ^ k)) + ξ * |α| * Real.log 3 +
            ξ * (hcirc ω (t / 2 ^ k) ((2 ^ k : ℂ)⁻¹ * c) + lqgQ γ * Real.log (t / 2 ^ k)))) *
            ENNReal.ofReal (Real.exp (η / 2 * k)) := by gcongr
      _ = ENNReal.ofReal (Real.exp (-(ξ * α * Real.log (t / 2 ^ k)) + ξ * |α| * Real.log 3 +
            ξ * (hcirc ω (t / 2 ^ k) ((2 ^ k : ℂ)⁻¹ * c) + lqgQ γ * Real.log (t / 2 ^ k)) + η / 2 * k)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      _ ≤ ENNReal.ofReal ε := by
          refine ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.2 ?_).trans_eq (Real.exp_log hε))
          have h1 := hK₀' k (hK.trans hk)
          nlinarith [hGk, h1]
  refine hsub.trans ?_
  calc P (⋃ m : ℕ, (A (m + K) ∪ G (m + K))) ≤ ∑' m : ℕ, (P (A (m + K)) + P (G (m + K))) :=
        (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => measure_union_le _ _)
    _ ≤ ∑' m : ℕ, F (m + K) := ENNReal.tsum_le_tsum fun m => add_le_add (hA _) le_rfl

end LatticeProb.LQG
