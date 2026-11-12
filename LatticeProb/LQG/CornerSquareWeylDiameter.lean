import LatticeProb.LQG.CornerSquareWeylChaining
import LatticeProb.LQG.InternalMetricOfTriangle
import LatticeProb.LQG.InternalMetricUnitSquareTail
import LatticeProb.LQG.ShellWeightBound
import LatticeProb.Gauss.CircleAverageShellSum

/-!
# Internal diameter of a corner square for a γ-LQG metric with a log singularity at the corner

Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF, `ξ > 0`, and `α < Q`. Consider the Weyl scaling
`E = |·|^{-αξ} · D_h`, i.e. `E = e^{ξ f} · D_h` with `f = -α log |·|`, and a closed square
`S = [a, a + s] × [b, b + s]` with the origin as a corner (`a, b ∈ {0, -s}`). Then almost surely `S` has finite
internal `E`-diameter.

This is the almost sure form of the last paragraph of the proof of Proposition 3.17 in Ding, Dubédat, Dunlap and
Falconet, "Tightness of Liouville first passage percolation for γ ∈ (0, 2)". Here the annuli of that proof are replaced
by the dyadic shells of the corner square. The shell weight `e^{Bₖ}` with `Bₖ = max(0, -αξ log tₖ + |α| ξ log 3)` is
paid against the one-point tail of the circle average `h_{tₖ}(cₖ)` at the threshold
`lₖ = -ηk + ξ max(α, 0) log tₖ`, where `ε < η < ξ (Q - max(α, 0)) log 2`.

## Main statements

* `IsLQGMetric.ae_internalMetric_weylScaling_cornerSquare_le_of_tail`: from a uniform unit-square diameter tail at
  rate `ε < ξ (Q - max(α, 0)) log 2`.
* `IsLQGMetric.ae_internalMetric_weylScaling_cornerSquare_le_of_shortHalfCrossings`: from the uniform short half-crossing
  tail of the unit square.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Finite internal diameter of a corner square for `|·|^{-αξ} · D_h`, from a unit-square tail.** If the internal
diameter of the unit square exceeds `e^{εk}` with probability at most `ψₖ` uniformly over whole-plane GFFs, with
`∑ ψₖ < ∞` and `ε < ξ (Q - max(α, 0)) log 2`, then almost surely the corner square `S = [a, a + s] × [b, b + s]`
(`a, b ∈ {0, -s}`) has finite internal diameter for every Weyl scaling `E = e^{-αξ log |·|} · D_h`. -/
theorem IsLQGMetric.ae_internalMetric_weylScaling_cornerSquare_le_of_tail (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {ε : ℝ} {ψ : ℕ → ℝ≥0∞} (hψ : ∑' k, ψ k ≠ ⊤)
    (htail : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
      P {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
          ENNReal.ofReal (Real.exp (ε * k))} ≤ ψ k)
    {α : ℝ} (hε : ε < ξ * (lqgQ γ - max α 0) * Real.log 2)
    {s a b : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) (hb : b = 0 ∨ b = -s) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ E : ℂ → ℂ → ℝ,
      (∀ x y, ENNReal.ofReal (E x y) = weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) x y) →
      ∀ u ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ v ∈ Icc a (a + s) ×ℂ Icc b (b + s),
        internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) u v ≤ ENNReal.ofReal A := by
  obtain ⟨η, hεη, hηK⟩ := exists_between hε
  have hα'α : α ≤ max α 0 := le_max_left _ _
  have hα'0 : 0 ≤ max α 0 := le_max_right _ _
  have ht : ∀ k : ℕ, 0 < s / 2 ^ (k + 1) := fun k => div_pos hs (pow_pos two_pos _)
  have hL : ∀ k : ℕ, Real.log (s / 2 ^ (k + 1)) ≤ |Real.log s| := fun k =>
    (Real.log_le_log (ht k) (div_le_self hs.le (one_le_pow₀ one_le_two))).trans (le_abs_self _)
  -- the circle-average tails along the shells
  have hl : ∀ c : ℕ → ℂ, (∀ k, ‖c k‖ ≤ 3 * (s / 2 ^ (k + 1))) →
      ∑' k, P {ω | -η * k + ξ * max α 0 * Real.log (s / 2 ^ (k + 1)) <
        ξ * (hcirc ω (s / 2 ^ (k + 1)) (c k) + lqgQ γ * Real.log (s / 2 ^ (k + 1)))} ≠ ⊤ := by
    intro c hc
    have ht2 : ∀ k : ℕ, s / 2 / 2 ^ k = s / 2 ^ (k + 1) := fun k => by
      rw [pow_succ, div_div, mul_comm]
    have h6e := hG.tsum_measure_shell_circle_exp_ne_top (half_pos hs) hξ hηK (M := 3) (c := c)
      (fun k => by rw [ht2 k]; exact hc k)
    refine ne_of_eq_of_ne (tsum_congr fun k => congrArg P ?_) h6e
    ext ω
    simp only [mem_ofPred_eq, ht2 k]
    have e : ξ * (hcirc ω (s / 2 ^ (k + 1)) (c k) + lqgQ γ * Real.log (s / 2 ^ (k + 1))) =
        ξ * (hcirc ω (s / 2 ^ (k + 1)) (c k) + (lqgQ γ - max α 0) * Real.log (s / 2 ^ (k + 1))) +
          ξ * max α 0 * Real.log (s / 2 ^ (k + 1)) := by ring
    rw [e]
    exact add_lt_add_iff_right _
  -- the shell weight plus the threshold decays at rate `η - ε`
  have hev : ∀ k : ℕ, max 0 (-α * ξ * Real.log (s / 2 ^ (k + 1)) + |α| * ξ * Real.log 3) +
      (-η * k + ξ * max α 0 * Real.log (s / 2 ^ (k + 1))) + ε * k ≤
      (ξ * max α 0 * |Real.log s| + ξ * (max α 0 - α) * |Real.log s| + |α| * ξ * Real.log 3) -
        (η - ε) * k := by
    intro k
    have h1 : ξ * max α 0 * Real.log (s / 2 ^ (k + 1)) ≤ ξ * max α 0 * |Real.log s| :=
      mul_le_mul_of_nonneg_left (hL k) (mul_nonneg hξ.le hα'0)
    have h2 : ξ * (max α 0 - α) * Real.log (s / 2 ^ (k + 1)) ≤ ξ * (max α 0 - α) * |Real.log s| :=
      mul_le_mul_of_nonneg_left (hL k) (mul_nonneg hξ.le (sub_nonneg.2 hα'α))
    have h3 : 0 ≤ ξ * max α 0 * |Real.log s| := mul_nonneg (mul_nonneg hξ.le hα'0) (abs_nonneg _)
    have h4 : 0 ≤ ξ * (max α 0 - α) * |Real.log s| :=
      mul_nonneg (mul_nonneg hξ.le (sub_nonneg.2 hα'α)) (abs_nonneg _)
    have h5 : 0 ≤ |α| * ξ * Real.log 3 :=
      mul_nonneg (mul_nonneg (abs_nonneg _) hξ.le) (Real.log_nonneg (by norm_num))
    rcases le_total 0 (-α * ξ * Real.log (s / 2 ^ (k + 1)) + |α| * ξ * Real.log 3) with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      linarith
  have hone := h𝔇.ae_internalMetric_weylScaling_cornerSquare_le hG hψ htail hs ha hb
    (f := fun w => -α * Real.log ‖w‖)
    (B := fun k => max 0 (-α * ξ * Real.log (s / 2 ^ (k + 1)) + |α| * ξ * Real.log 3))
    (fun k => le_max_left _ _)
    (fun k w h1 h2 => (mul_neg_mul_log_norm_le_of_mem_shell hξ.le (ht k) h1 h2).trans (le_max_right _ _))
    (l := fun k : ℕ => -η * k + ξ * max α 0 * Real.log (s / 2 ^ (k + 1))) hl
    (η := η - ε) (sub_pos.2 hεη) (Eventually.of_forall hev)
  -- from distances to the corner to the internal diameter
  filter_upwards [hone, h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hω hD
  obtain ⟨A, hA⟩ := hω
  refine ⟨4 * max A 0, fun E hE u hu v hv => ?_⟩
  have htri : ∀ x y z, ENNReal.ofReal (E x z) ≤ ENNReal.ofReal (E x y) + ENNReal.ofReal (E y z) :=
    fun x y z => by
      rw [hE, hE, hE]
      exact hD.weylScaling_triangle ξ _ x y z
  have hsymm : ∀ x y, ENNReal.ofReal (E x y) = ENNReal.ofReal (E y x) := fun x y => by
    rw [hE, hE]
    exact hD.weylScaling_symm ξ _ x y
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ Icc a (a + s) ×ℂ Icc b (b + s), w ≠ 0 := by
    refine ⟨⟨a + s / 2, b⟩, ?_, fun h => ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, by linarith⟩⟩
    · have h' := congrArg Complex.re h
      simp only [Complex.zero_re] at h'
      rcases ha with rfl | rfl
      · linarith
      · linarith
  have hAw : internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) w 0 ≤ ENNReal.ofReal (max A 0) :=
    (hA E hE w hw hw0).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hA0 : ∀ x ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) x 0 ≤ ENNReal.ofReal (2 * max A 0) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      calc internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) 0 0
          ≤ internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) 0 w +
              internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) w 0 :=
            internalMetric_triangle_of_ofReal_triangle htri _ 0 w 0
        _ = internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) w 0 +
              internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) w 0 := by
            rw [internalMetric_symm_of_ofReal_symm hsymm _ 0 w]
        _ ≤ ENNReal.ofReal (max A 0) + ENNReal.ofReal (max A 0) := add_le_add hAw hAw
        _ = ENNReal.ofReal (2 * max A 0) := by
            rw [two_mul, ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    · exact (hA E hE x hx hx0).trans
        (ENNReal.ofReal_le_ofReal (by linarith [le_max_left A 0, le_max_right A 0]))
  calc internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) u v
      ≤ internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) u 0 +
          internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) 0 v :=
        internalMetric_triangle_of_ofReal_triangle htri _ u 0 v
    _ = internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) u 0 +
          internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) v 0 := by
        rw [internalMetric_symm_of_ofReal_symm hsymm _ 0 v]
    _ ≤ ENNReal.ofReal (2 * max A 0) + ENNReal.ofReal (2 * max A 0) := add_le_add (hA0 u hu) (hA0 v hv)
    _ = ENNReal.ofReal (4 * max A 0) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- **Finite internal diameter of a corner square for `|·|^{-αξ} · D_h`.** Assume the uniform short half-crossing tail
of the unit square at exponents `δ < θ < ξ (Q - 2) log 2` (with `∑ 4ⁿ pₙ < ∞`) and `α < Q`. Then almost surely the
corner square `S = [a, a + s] × [b, b + s]` (`a, b ∈ {0, -s}`) has finite internal diameter for every Weyl scaling
`E = e^{-αξ log |·|} · D_h`. -/
theorem IsLQGMetric.ae_internalMetric_weylScaling_cornerSquare_le_of_shortHalfCrossings
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) (hδ0 : 0 < δ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {α : ℝ} (hα : α < lqgQ γ)
    {s a b : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) (hb : b = 0 ∨ b = -s) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ E : ℂ → ℂ → ℝ,
      (∀ x y, ENNReal.ofReal (E x y) = weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) x y) →
      ∀ u ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ v ∈ Icc a (a + s) ×ℂ Icc b (b + s),
        internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) u v ≤ ENNReal.ofReal A := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQ2 : 0 < lqgQ γ - 2 := by
    have h1 : 0 < ξ * (lqgQ γ - 2) * Real.log 2 := by linarith
    exact (mul_pos_iff_of_pos_left hξ).1 ((mul_pos_iff_of_pos_right hlog2).1 h1)
  have hK : 0 < ξ * (lqgQ γ - max α 0) * Real.log 2 :=
    mul_pos (mul_pos hξ (sub_pos.2 (max_lt hα (by linarith)))) hlog2
  obtain ⟨ψ, hψ, htail⟩ := h𝔇.exists_unitSquare_internalMetric_tail hG hξ hθ hδ hδ0
    (ε := ξ * (lqgQ γ - max α 0) * Real.log 2 / 2) (by positivity) huniv hp
  exact h𝔇.ae_internalMetric_weylScaling_cornerSquare_le_of_tail hG hξ hψ htail (by linarith) hs ha hb

end LatticeProb.LQG
