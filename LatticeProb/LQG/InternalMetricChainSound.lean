import Mathlib
import LatticeProb.LQG.InternalMetricOfTriangle
import LatticeProb.LQG.InternalMetricRationalChain

/-!
# Soundness of chains for the internal metric of a Euclidean length metric

Let `D` be a Euclidean length metric on `ℂ` and `U ⊆ ℂ`. For `z ∈ ℂ` and `ρ > 0` let
`circleDistInf D z ρ = inf_θ D(z, z + ρ e^{iθ})` be the minimum of `D(z, ·)` on the circle `∂B(z, ρ)`.

* `D(z, P(t)) ≤ len(P; D)` for every path `P` from `z` (`IsEuclideanLengthMetric.ofReal_apply_le_pathLength`);
  hence a path from `z` whose `D`-length is smaller than `circleDistInf D z ρ` cannot reach the circle
  `∂B(z, ρ)` and stays in the ball `B(z, ρ)`
  (`IsEuclideanLengthMetric.range_subset_ball_of_pathLength_lt`).
* If `B(z, ρ) ⊆ U` and `D(z, w) < circleDistInf D z ρ`, then `D(z, w; U) = D(z, w)`: the length property gives a
  path of length close to `D(z, w)`, which stays in `B(z, ρ) ⊆ U`
  (`IsEuclideanLengthMetric.internalMetric_le_ofReal_of_lt_circleDistInf`).
* Chains: if `z₀, …, z_m` with `m > 0` satisfy `B(z_i, ρ_i) ⊆ U` and `D(z_i, z_{i+1}) < circleDistInf D z_i ρ_i`,
  then `D(z₀, z_m; U) ≤ ∑ D(z_i, z_{i+1})`
  (`IsEuclideanLengthMetric.internalMetric_chain_le_sum`).
-/

namespace LatticeProb.LQG

open Set Metric
open scoped ENNReal

/-- The minimum of `D(z, ·)` on the circle `∂B(z, ρ)`, as an infimum over the angle. -/
noncomputable def circleDistInf (D : ℂ → ℂ → ℝ) (z : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  ⨅ θ : ℝ, ENNReal.ofReal (D z (z + (ρ : ℂ) * Complex.exp (θ * Complex.I)))

/-- The distance `D(z, P(t))` from the starting point of a path is at most its `D`-length. -/
theorem IsEuclideanLengthMetric.ofReal_apply_le_pathLength {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {z w : ℂ} (P : Path z w) (t : unitInterval) :
    ENNReal.ofReal (D z (P t)) ≤ pathLength D P := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h := ofReal_le_curveLength (E := D) (f := P.extend) h0 t.2 t.2.1
  rw [Path.extend_zero, Path.extend_extends' P t, hD.symm] at h
  exact h

/-- A path from `z` whose `D`-length is smaller than the minimum of `D(z, ·)` on `∂B(z, ρ)` stays in `B(z, ρ)`:
otherwise, by the intermediate value theorem, it meets the circle at a point `P(s)` with
`D(z, P(s)) ≤ len(P; D)`. -/
theorem IsEuclideanLengthMetric.range_subset_ball_of_pathLength_lt {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {z w : ℂ} (P : Path z w) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : pathLength D P < circleDistInf D z ρ) (t : unitInterval) : P t ∈ ball z ρ := by
  by_contra hnot
  rw [mem_ball, not_lt, Complex.dist_eq] at hnot
  have hcont : ContinuousOn (fun s : ℝ => ‖P.extend s - z‖) (Icc 0 (t : ℝ)) :=
    (P.continuous_extend.sub continuous_const).norm.continuousOn
  have hmem : ρ ∈ Icc ((fun s : ℝ => ‖P.extend s - z‖) 0) ((fun s : ℝ => ‖P.extend s - z‖) t) := by
    refine ⟨?_, ?_⟩
    · simp only [Path.extend_zero, sub_self, norm_zero]
      exact hρ.le
    · show ρ ≤ ‖P.extend t - z‖
      rw [Path.extend_extends' P t]
      exact hnot
  obtain ⟨s, hs, hsρ⟩ := intermediate_value_Icc t.2.1 hcont hmem
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans t.2.2⟩
  have hPs : ‖P ⟨s, hs01⟩ - z‖ = ρ := by
    have hsρ' : ‖P.extend s - z‖ = ρ := hsρ
    rwa [show P.extend s = P ⟨s, hs01⟩ from P.extend_extends' ⟨s, hs01⟩] at hsρ'
  have hpt : z + (ρ : ℂ) * Complex.exp (Complex.arg (P ⟨s, hs01⟩ - z) * Complex.I) = P ⟨s, hs01⟩ := by
    have h := Complex.norm_mul_exp_arg_mul_I (P ⟨s, hs01⟩ - z)
    rw [hPs] at h
    rw [h]
    ring
  have hle : circleDistInf D z ρ ≤ ENNReal.ofReal (D z (P ⟨s, hs01⟩)) := by
    refine (iInf_le _ (Complex.arg (P ⟨s, hs01⟩ - z))).trans ?_
    rw [hpt]
  exact absurd (hlen.trans_le (hle.trans (hD.ofReal_apply_le_pathLength P _))) (lt_irrefl _)

/-- If `B(z, ρ) ⊆ U` and `D(z, w)` is smaller than the minimum of `D(z, ·)` on `∂B(z, ρ)`, then
`D(z, w; U) ≤ D(z, w)`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_ofReal_of_lt_circleDistInf {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} {z w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : ball z ρ ⊆ U) (hw : ENNReal.ofReal (D z w) < circleDistInf D z ρ) :
    internalMetric D U z w ≤ ENNReal.ofReal (D z w) := by
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  have hlt : ENNReal.ofReal (D z w) < min b (circleDistInf D z ρ) := lt_min hb hw
  have heq := hD.ofReal_eq_internalMetric z w
  rw [internalMetric] at heq
  rw [heq] at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
  obtain ⟨-, hP⟩ := iInf_lt_iff.1 hP
  have hPU : ∀ t, P t ∈ U := fun t =>
    hU (hD.range_subset_ball_of_pathLength_lt P hρ (hP.trans_le (min_le_right _ _)) t)
  exact (iInf₂_le P hPU).trans (hP.le.trans (min_le_left _ _))

/-- Soundness of chains: if `m > 0`, the balls `B(z_i, ρ_i)` lie in `U`, and each step `D(z_i, z_{i+1})` is smaller
than the minimum of `D(z_i, ·)` on `∂B(z_i, ρ_i)`, then `D(z₀, z_m; U) ≤ ∑ D(z_i, z_{i+1})`. -/
theorem IsEuclideanLengthMetric.internalMetric_chain_le_sum {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} {m : ℕ} (hm : 0 < m) (z : ℕ → ℂ) (ρ : ℕ → ℝ)
    (hρ : ∀ i < m, 0 < ρ i) (hU : ∀ i < m, ball (z i) (ρ i) ⊆ U)
    (hstep : ∀ i < m, ENNReal.ofReal (D (z i) (z (i + 1))) < circleDistInf D (z i) (ρ i)) :
    internalMetric D U (z 0) (z m) ≤ ∑ i ∈ Finset.range m, ENNReal.ofReal (D (z i) (z (i + 1))) := by
  have htri : ∀ x y w : ℂ,
      ENNReal.ofReal (D x w) ≤ ENNReal.ofReal (D x y) + ENNReal.ofReal (D y w) := fun x y w => by
    rw [← ENNReal.ofReal_add (hD.apply_nonneg x y) (hD.apply_nonneg y w)]
    exact ENNReal.ofReal_le_ofReal (hD.triangle x y w)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  clear hm
  induction k with
  | zero =>
    simpa using hD.internalMetric_le_ofReal_of_lt_circleDistInf (hρ 0 (by omega)) (hU 0 (by omega))
      (hstep 0 (by omega))
  | succ k ih =>
    have h1 := ih (fun i hi => hρ i (by omega)) (fun i hi => hU i (by omega))
      (fun i hi => hstep i (by omega))
    have h2 := hD.internalMetric_le_ofReal_of_lt_circleDistInf (hρ (k + 1) (by omega))
      (hU (k + 1) (by omega)) (hstep (k + 1) (by omega))
    rw [Finset.sum_range_succ _ (k + 1)]
    exact (internalMetric_triangle_of_ofReal_triangle htri U (z 0) (z (k + 1)) (z (k + 1 + 1))).trans
      (add_le_add h1 h2)

end LatticeProb.LQG
