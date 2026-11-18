import LatticeProb.LQG.SingularApproximantBallPower
import LatticeProb.LQG.CompactBallApproximantPower
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-!
# Ball power bounds for the approximants of selected whole-plane coordinates

Let `c ω r z` be circle-average coordinates of a whole-plane GFF `X` normalized by
`X_1(0) = 0`: jointly continuous in `(r, z) ∈ (0, ∞) × ℂ` for every sample, and almost surely
equal to the circle average of `X` at each fixed radius and center.

* `isGFFCircleAverage_congr_pos`: `IsGFFCircleAverage` only depends on positive radii.
* `isGFFCircleAverage_of_normalized_coordinates`: `(r, z, ω) ↦ c ω r z` is a circle-average
  process of the normalized whole-plane GFF.
* `ae_regular_approximant_ball_rpow_bound`: almost surely, for every `R`, the dyadic
  approximants `ε^{γ²/2} e^{γ c_ε(z)} dz` give every ball `B(z, s)` with `‖z‖ ≤ R` and
  `0 < s ≤ 1` mass at most `C s^κ`, `κ > 0`, uniformly in the level.
* `ae_singular_approximant_ball_rpow_bound`: the same bound, with some `β > 0`, for the field
  `c - α log |·|` with a logarithmic singularity, `0 ≤ α < Q`.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- `IsGFFCircleAverage` only involves positive radii: a process that agrees with a
circle-average process at every positive radius is again one. -/
theorem isGFFCircleAverage_congr_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H H' : ℝ → ℂ → Ω → ℝ} (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHH' : ∀ r, 0 < r → ∀ z ω, H r z ω = H' r z ω) :
    LQGDimension.IsGFFCircleAverage H' P := by
  have hfun : (fun p : Ioi (0 : ℝ) × ℂ => H' p.1 p.2) = fun p => H p.1 p.2 := by
    funext p ω
    exact (hHH' p.1 p.1.2 p.2 ω).symm
  have hpt : ∀ r, 0 < r → ∀ z, H' r z = H r z := fun r hr z =>
    funext fun ω => (hHH' r hr z ω).symm
  refine ⟨hH.isProbabilityMeasure, ?_, fun ε hε z => ?_, fun ε hε δ hδ z w => ?_,
    fun ε hε ω => ?_⟩
  · rw [hfun]
    exact hH.isGaussianProcess
  · rw [hpt ε hε z]
    exact hH.integral_eq_zero ε hε z
  · rw [hpt ε hε z, hpt δ hδ w]
    exact hH.covariance_eq ε hε δ hδ z w
  · have : (fun z => H' ε z ω) = fun z => H ε z ω := funext fun z => (hHH' ε hε z ω).symm
    rw [this]
    exact hH.continuous ε hε ω

/-- **Selected coordinates of a normalized whole-plane GFF form a circle-average process.**
If `c ω r z` is jointly continuous in `(r, z)` on `(0, ∞) × ℂ` for every sample and equals
the circle average `X_r(z)` almost surely for each `r > 0` and `z`, where `X` is a whole-plane
GFF normalized by `X_1(0) = 0`, then `(r, z, ω) ↦ c ω r z` satisfies `IsGFFCircleAverage`. -/
theorem isGFFCircleAverage_of_normalized_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {c : Ω → ℝ → ℂ → ℝ}
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z) :
    LQGDimension.IsGFFCircleAverage (fun r z ω => c ω r z) P := by
  obtain ⟨H, hH, -, hae⟩ := LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized hX
  have hHc : ∀ r, 0 < r → ∀ z, H r z =ᵐ[P] fun ω => c ω r z := fun r hr z => by
    filter_upwards [hae r hr z, heq r hr z] with ω h1 h2
    rw [h1, h2]
  refine ⟨hH.isProbabilityMeasure, hH.isGaussianProcess.congr fun p => hHc p.1 p.1.2 p.2,
    fun ε hε z => ?_, fun ε hε δ hδ z w => ?_, fun ε hε ω => ?_⟩
  · rw [← integral_congr_ae (hHc ε hε z)]
    exact hH.integral_eq_zero ε hε z
  · rw [← LQGMetric.CircleAvg.covariance_congr_ae (hHc ε hε z) (hHc δ hδ w)]
    exact hH.covariance_eq ε hε δ hδ z w
  · exact (hc ω).comp_continuous (continuous_const.prodMk continuous_id)
      fun z => ⟨hε, mem_univ z⟩

/-- **Regular approximants of selected coordinates on compact sets, almost surely.** Under
the hypotheses of `isGFFCircleAverage_of_normalized_coordinates`, with measurable
coordinates, almost surely, for every `R`, there are `C ≥ 0` and `κ > 0` such that the
dyadic approximants of the `γ`-LQG measure built from `c ω` give every ball `B(z, s)` with
`‖z‖ ≤ R` and `0 < s ≤ 1` mass at most `C s^κ`, for every level. -/
theorem ae_regular_approximant_ball_rpow_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        lqgApprox γ (c ω) (dyadicScale k) (ball z s) ≤ ENNReal.ofReal (C * s ^ κ) := by
  classical
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℂ → Ω → ℝ, H = fun r z ω => if 0 < r then c ω r z else 0 :=
    ⟨_, rfl⟩
  have hHc : ∀ r, 0 < r → ∀ z ω, c ω r z = H r z ω := fun r hr z ω => by
    rw [hHdef]
    simp [hr]
  have hH : LQGDimension.IsGFFCircleAverage H P :=
    isGFFCircleAverage_congr_pos (isGFFCircleAverage_of_normalized_coordinates hX hc heq) hHc
  have hHm : ∀ r z, Measurable (H r z) := fun r z => by
    by_cases hr : 0 < r
    · have : H r z = fun ω => c ω r z := funext fun ω => (hHc r hr z ω).symm
      rw [this]
      exact hcm r z hr
    · have : H r z = fun _ => 0 := by
        rw [hHdef]
        funext ω
        simp [hr]
      rw [this]
      exact measurable_const
  have ht : 1 < 4 / γ ^ 2 := by
    rw [one_lt_div (by positivity)]
    nlinarith
  have hbound : ∀ N : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ z ∈ closedBall (0 : ℂ) N, ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ n,
        lqgApprox γ (fun s w => H s w ω) (QuantumZipper.radius n) (ball z s) ≤
          C * ENNReal.ofReal (s ^ κ) := fun N =>
    ae_exists_compact_center_ball_approximant_power_bound hH hHm hγ hγ2
      (p := 1 + (4 / γ ^ 2 - 1) / 3) (q := 1 + 2 * (4 / γ ^ 2 - 1) / 3)
      (by linarith) (by linarith) (by linarith) _ (isCompact_closedBall 0 N)
  choose κ hκ hae using hbound
  filter_upwards [ae_all_iff.2 hae] with ω hω R
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨C, hC, hCb⟩ := hω N
  refine ⟨C.toReal, κ N, ENNReal.toReal_nonneg, hκ N, fun k z hz s hs hs1 => ?_⟩
  have hk : 0 < dyadicScale k := by
    unfold dyadicScale
    positivity
  have happrox : lqgApprox γ (c ω) (dyadicScale k) =
      lqgApprox γ (fun s w => H s w ω) (QuantumZipper.radius k) := by
    have hrad : QuantumZipper.radius k = dyadicScale k := rfl
    rw [hrad]
    unfold lqgApprox
    congr 1
    funext w
    rw [hHc _ hk w ω]
  rw [happrox, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]
  exact hCb z (mem_closedBall_zero_iff.2 (hz.trans hN)) s hs hs1 k

/-- **Singular approximants of selected coordinates on compact sets, almost surely.** Let
`c ω` be jointly continuous circle-average coordinates of a whole-plane GFF `X` normalized
by `X_1(0) = 0`, and `0 ≤ α < Q`. Almost surely, for every `R`, there are `K` and `β > 0`
such that the dyadic approximants of the `γ`-LQG measure of the field `c - α log |·|` give
every ball `B(z, s)` with `‖z‖ ≤ R` and `0 < s ≤ 1` mass at most `K s^β`, for every
level. -/
theorem ae_singular_approximant_ball_rpow_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : 0 ≤ α) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ K β : ℝ, 0 < β ∧ ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        lqgApprox γ (fieldCircleAverage α (c ω)) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (K * s ^ β) :=
  ae_singular_approximant_ball_rpow_bound_of_regular hX hG hc heq hγ hγ2 hα hαQ
    (δ := 1) (r := 4⁻¹) (ρ := 2⁻¹) one_pos ⟨by norm_num, by norm_num⟩ (by norm_num)
    (by norm_num)
    (ae_regular_approximant_ball_rpow_bound hX (fun r z hr => hG.measurable_circle r z hr)
      hc heq hγ hγ2)

end LatticeProb.LQG
