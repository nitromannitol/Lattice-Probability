import LatticeProb.LQG.WeylScalingShellBound
import LatticeProb.LQG.WeylScalingLogOffZero
import LatticeProb.LQG.WeylCompositionOuter

/-!
# A shell criterion for the Weyl scaling by a logarithmic singularity at the origin

Let `D` be a Euclidean length metric on `ℂ` and let `ξ, α₀ ∈ ℝ` with `ξ α₀ ≥ 0`. The weight `-α₀ log |·|` is then such
that `e^{-ξ α₀ log |·|}` blows up at `0`, and the Weyl scaling `D_α = e^{-ξ α₀ log |·|} · D` is a priori infinite at `0`.
Cut a neighbourhood of `0` into the exponential shells `Aₖ = {e^{-(k+1)} ≤ |x| ≤ e^{-k}}` (`expShell`). On the
`e^{-(k+2)}`-neighbourhood of `Aₖ` the weight is at most `e^{ξ α₀ (k + 2)}`. If

  `∑ₖ e^{ξ α₀ k} · diam_D(Aₖ; B_{e^{-(k+2)}}(Aₖ)) < ∞`,

where `diam_D(A; B_δ(A)) = sup_{x, y ∈ A} D(x, y; B_δ(A))` is the internal diameter (`internalDiam`), then
`D_α(u, 0) < ∞` for every `u`, and `D_α(0, w) → 0` as `w → 0`. The proof chains `u` to `0` through the shells
(`IsEuclideanLengthMetric.weylScaling_le_tsum_of_shells`) and bounds `D_α(w, 0)` for `w ∈ Aₘ` by `e^{2 ξ α₀}` times the
tail `∑_{k ≥ m}` of the series.

This is the deterministic part of the proof that the metric of a whole-plane GFF plus the logarithmic singularity
`-α₀ log |·|` is finite at `0` and continuous there (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition
3.17); the summability is the probabilistic part.

## Main statements

* `LatticeProb.LQG.expShell`: the shell `{e^{-(k+1)} ≤ |x| ≤ e^{-k}}`.
* `LatticeProb.LQG.exists_mem_expShell`: every `w ≠ 0` with `|w| < e^{-N}` lies in a shell `Aₘ` with `m ≥ N`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.weylScaling_log_le_tail`: `D_α(u, 0) ≤ e^{2 ξ α₀} ∑_{k ≥ m} e^{ξ α₀ k} Mₖ`
  for `u ∈ Aₘ`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.weylScaling_log_lt_top_and_tendsto_of_summable`: the shell criterion.
-/

open MeasureTheory Filter Set Topology LatticeProb.Gauss
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- The exponential shell `Aₖ = {e^{-(k+1)} ≤ |x| ≤ e^{-k}}` about the origin. -/
def expShell (k : ℕ) : Set ℂ := {x | Real.exp (-((k : ℝ) + 1)) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (-(k : ℝ))}

/-- Consecutive exponential shells meet (on the circle of radius `e^{-(k+1)}`). -/
theorem expShell_inter_succ_nonempty (k : ℕ) : (expShell k ∩ expShell (k + 1)).Nonempty := by
  have hn : ‖((Real.exp (-((k : ℝ) + 1)) : ℝ) : ℂ)‖ = Real.exp (-((k : ℝ) + 1)) :=
    Complex.norm_of_nonneg (Real.exp_pos _).le
  refine ⟨((Real.exp (-((k : ℝ) + 1)) : ℝ) : ℂ), ?_, ?_⟩
  · show _ ≤ _ ∧ _ ≤ _
    rw [hn]
    exact ⟨le_rfl, Real.exp_le_exp.2 (by linarith)⟩
  · show _ ≤ _ ∧ _ ≤ _
    rw [hn]
    push_cast
    exact ⟨Real.exp_le_exp.2 (by linarith), le_rfl⟩

/-- Every `w ≠ 0` with `|w| < e^{-N}` lies in an exponential shell `Aₘ` with `m ≥ N` (namely `m = ⌊-log |w|⌋`). -/
theorem exists_mem_expShell {w : ℂ} (hw : w ≠ 0) {N : ℕ} (hN : ‖w‖ < Real.exp (-(N : ℝ))) :
    ∃ m, N ≤ m ∧ w ∈ expShell m := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hlog : Real.log ‖w‖ < -(N : ℝ) := by
    rw [← Real.log_exp (-(N : ℝ))]
    exact Real.log_lt_log hpos hN
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = -Real.log ‖w‖ := ⟨_, rfl⟩
  have hNt : (N : ℝ) < t := by linarith
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) hNt.le
  have h1 := Nat.lt_floor_add_one t
  have h2 := Nat.floor_le ht0
  refine ⟨⌊t⌋₊, Nat.le_floor hNt.le, ?_, ?_⟩
  · calc Real.exp (-((⌊t⌋₊ : ℝ) + 1)) ≤ Real.exp (Real.log ‖w‖) := Real.exp_le_exp.2 (by linarith)
      _ = ‖w‖ := Real.exp_log hpos
  · calc ‖w‖ = Real.exp (Real.log ‖w‖) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (-(⌊t⌋₊ : ℝ)) := Real.exp_le_exp.2 (by linarith)

/-- The `e^{-(k+2)}`-neighbourhood of the shell `Aₖ` lies in the open annulus `e^{-(k+2)} < |x| < 2 e^{-k}`. -/
theorem norm_bounds_of_mem_thickening_expShell {k : ℕ} {w : ℂ}
    (hw : w ∈ Metric.thickening (Real.exp (-((k : ℝ) + 2))) (expShell k)) :
    Real.exp (-((k : ℝ) + 2)) < ‖w‖ ∧ ‖w‖ < 2 * Real.exp (-(k : ℝ)) := by
  obtain ⟨a, ha, hwa⟩ := Metric.mem_thickening_iff.1 hw
  rw [Complex.dist_eq] at hwa
  obtain ⟨ha1, ha2⟩ := ha
  have h1 := norm_sub_norm_le a w
  have h2 := norm_sub_norm_le w a
  rw [norm_sub_rev] at h1
  have he1 : Real.exp (-((k : ℝ) + 1)) = Real.exp 1 * Real.exp (-((k : ℝ) + 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (-(k : ℝ)) = Real.exp 2 * Real.exp (-((k : ℝ) + 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := Real.exp_pos (-((k : ℝ) + 2))
  have hE1 : 2 * Real.exp (-((k : ℝ) + 2)) ≤ Real.exp 1 * Real.exp (-((k : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)]) hpos.le
  have hE2 : Real.exp (-((k : ℝ) + 2)) ≤ Real.exp 2 * Real.exp (-((k : ℝ) + 2)) :=
    le_mul_of_one_le_left hpos.le (Real.one_le_exp (by norm_num))
  constructor <;> linarith

/-- **Tail bound at the singular point.** Let `D` be a Euclidean length metric and `ξ α₀ ≥ 0`. For `u` in the shell
`Aₘ`, `e^{-ξ α₀ log |·|} · D (u, 0) ≤ e^{2 ξ α₀} ∑_{j ≥ 0} e^{ξ α₀ (m + j)} M_{m+j}`, where
`Mₖ = diam_D(Aₖ; B_{e^{-(k+2)}}(Aₖ))`. -/
theorem IsEuclideanLengthMetric.weylScaling_log_le_tail {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ α₀ : ℝ} (hα : 0 ≤ ξ * α₀) {m : ℕ} {u : ℂ} (hu : u ∈ expShell m) :
    weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u 0 ≤
      ENNReal.ofReal (Real.exp (2 * (ξ * α₀))) *
        ∑' j, ENNReal.ofReal (Real.exp (ξ * α₀ * ((m + j : ℕ) : ℝ))) *
          internalDiam D (Real.exp (-(((m + j : ℕ) : ℝ) + 2))) (expShell (m + j)) := by
  have hρ : Tendsto (fun k : ℕ => 2 * Real.exp (-(k : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
  have h := hD.weylScaling_le_tsum_of_shells ξ (fun x => -α₀ * Real.log ‖x‖) (z := 0) (A := expShell)
    (S := fun k => Metric.thickening (Real.exp (-((k : ℝ) + 2))) (expShell k))
    (B := fun k => ξ * α₀ * ((k : ℝ) + 2))
    (M := fun k => internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k))
    expShell_inter_succ_nonempty hρ
    (fun k w hw => mem_ball_zero_iff.2 (norm_bounds_of_mem_thickening_expShell hw).2)
    (fun k => mul_nonneg hα (by positivity))
    (fun k w hw => by
      have hlt := (norm_bounds_of_mem_thickening_expShell hw).1
      have h' := mul_neg_mul_log_norm_le_of_lt_norm hα (Real.exp_pos _) hlt
      rw [Real.log_exp] at h'
      show ξ * (-α₀ * Real.log ‖w‖) ≤ ξ * α₀ * ((k : ℝ) + 2)
      linarith)
    (fun k x hx y hy => by
      show _ ≤ internalDiam _ _ _
      unfold internalDiam
      exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl))
    hu
  refine h.trans (le_of_eq ?_)
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 3
  ring

/-- **Shell criterion at a logarithmic singularity.** Let `D` be a Euclidean length metric, `ξ α₀ ≥ 0`, and suppose
that `∑ₖ e^{ξ α₀ k} · diam_D(Aₖ; B_{e^{-(k+2)}}(Aₖ)) < ∞` for the exponential shells
`Aₖ = {e^{-(k+1)} ≤ |x| ≤ e^{-k}}`. Then the Weyl scaling `D_α = e^{-ξ α₀ log |·|} · D` satisfies `D_α(u, 0) < ∞` for
every `u`, and `D_α(0, w) → 0` as `w → 0`. -/
theorem IsEuclideanLengthMetric.weylScaling_log_lt_top_and_tendsto_of_summable {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ α₀ : ℝ} (hα : 0 ≤ ξ * α₀)
    (hsum : ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞) :
    (∀ u, weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u 0 < ∞) ∧
      Tendsto (fun w => weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) 0 w) (𝓝 0) (𝓝 0) := by
  set g : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
    internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k) with hg
  set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * (ξ * α₀))) with hC
  have hbound : ∀ m u, u ∈ expShell m →
      weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u 0 ≤ C * ∑' j, g (j + m) := fun m u hu => by
    refine (hD.weylScaling_log_le_tail hα hu).trans (le_of_eq ?_)
    congr 1
    exact tsum_congr fun j => by rw [add_comm m j]
  have hfin : ∀ m, ∑' j, g (j + m) ≠ ∞ := fun m =>
    ne_top_of_le_ne_top hsum (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective m) g)
  have hmem1 : (1 : ℂ) ∈ expShell 0 := by
    show _ ≤ _ ∧ _ ≤ _
    rw [norm_one]
    push_cast
    exact ⟨by rw [zero_add]; exact (Real.exp_le_one_iff).2 (by norm_num), by simp⟩
  refine ⟨fun u => ?_, ?_⟩
  · rcases eq_or_ne u 0 with rfl | hu
    · rw [hD.weylScaling_self_eq_zero]
      exact ENNReal.zero_lt_top
    · calc weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u 0
          ≤ weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u 1 +
              weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) 1 0 := hD.weylScaling_triangle ξ _ u 1 0
        _ < ∞ := ENNReal.add_lt_top.2 ⟨hD.weylScaling_log_lt_top_of_ne ξ α₀ hu one_ne_zero,
            (hbound 0 1 hmem1).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (lt_top_iff_ne_top.2 (hfin 0)))⟩
  · have htail : Tendsto (fun m => C * ∑' j, g (j + m)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_sum_nat_add g hsum)
        (Or.inr ENNReal.ofReal_ne_top)
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 htail) ε hε)
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-(N : ℝ)))] with w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · rw [hD.weylScaling_self_eq_zero]
      exact zero_le
    · obtain ⟨m, hNm, hm⟩ := exists_mem_expShell hw0 (mem_ball_zero_iff.1 hw)
      rw [hD.weylScaling_symm]
      exact (hbound m w hm).trans (hN m hNm)

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Axiom I for the LQG metric of a field with a log singularity, from the shell series.** Let `𝔇` be a γ-LQG metric,
`h^ℂ` a whole-plane GFF, `ξ α₀ ≥ 0` and `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}`. If almost surely
`∑ₖ e^{ξ α₀ k} · diam_{D_{h^ℂ}}(Aₖ; B_{e^{-(k+2)}}(Aₖ)) < ∞` for the exponential shells `Aₖ`, then almost surely `D_h`
is finite and its real part is a Euclidean length metric. -/
theorem IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_summable (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {α₀ : ℝ} (hα : 0 ≤ ξ * α₀)
    (hsum : ∀ᵐ ω ∂P, ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞) :
    ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
  refine h𝔇.ae_isEuclideanLengthMetric_weylScaling_log_of_zero hG α₀ ?_ ?_
  · filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hsum] with ω hD hs
    exact (hD.weylScaling_log_lt_top_and_tendsto_of_summable hα hs).1
  · filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hsum] with ω hD hs
    exact (hD.weylScaling_log_lt_top_and_tendsto_of_summable hα hs).2

/-- **Axiom III for the LQG metric of a field with a log singularity, from the shell series.** Under the hypotheses
of `IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_summable` and `ξ > 0`, almost surely, for every
continuous `f`, `e^{ξ (f - α₀ log |·|)} · D_{h^ℂ} = e^{ξ f} · D_h`. -/
theorem IsLQGMetric.ae_weylScaling_log_add_of_summable (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    (hξ : 0 < ξ) {α₀ : ℝ} (hα : 0 ≤ ξ * α₀)
    (hsum : ∀ᵐ ω ∂P, ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
      weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
        weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ f u v := by
  refine h𝔇.ae_weylScaling_log_add_of_zero hG hξ α₀ ?_
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hsum] with ω hD hs
  exact (hD.weylScaling_log_lt_top_and_tendsto_of_summable hα hs).1

end LatticeProb.LQG
