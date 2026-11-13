import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeas
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Dy

/-!
# The Liouville graph distance is a measurable function of the measure

For a measure `μ` on `ℂ`, the Liouville graph distance `D_δ(u, v)` of Ding-Zeitouni-Zhang
(arXiv:1807.00422, Section 1) is the least number of Euclidean balls of `μ`-mass at most `δ` whose
union contains a path from `u` to `v`. It is unchanged when the balls are taken with rational
centres and radii, so it is a function of the countably many masses `μ (B(c, q))`, `c ∈ ℚ²`,
`q ∈ ℚ`. Each of these masses is a measurable function of `μ` for the Giry σ-algebra on
`Measure ℂ`, so `D_δ(u, v)` is measurable in `μ`, and so is the event that `D_δ(u, v)` has
exponent `χ` as `δ → 0` (by monotonicity in `δ`, the limit may be taken along `δ = 2^{-n}`).

This is the measurability input that lets an almost sure statement about the exponent be
transported between two random measures with the same law.

* `LatticeProb.LQG.measurable_ballMassQ`: the rational ball masses are measurable in `μ`.
* `LatticeProb.LQG.measurable_lgdDZZ`: `μ ↦ D_δ(u, v)` is measurable.
* `LatticeProb.LQG.measurable_lgdMinSet`: `μ ↦ min_{A × B} D_δ` is measurable.
* `LatticeProb.LQG.measurableSet_lgdExponentEvent`: the set of measures `μ` for which
  `log D_δ(u, v) / log δ⁻¹ → χ` as `δ → 0⁺` is measurable.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

open DZZ

/-- The mass of a ball with rational centre and radius is a measurable function of the measure. -/
theorem _root_.LatticeProb.LQG.measurable_ballMassQ (c : ℚ × ℚ) (q : ℚ) :
    Measurable fun μ : Measure ℂ => ballMassQ μ c q :=
  Measure.measurable_coe measurableSet_ball

/-- **The Liouville graph distance `D_δ(u, v)` is a measurable function of the measure.** -/
theorem _root_.LatticeProb.LQG.measurable_lgdDZZ (δ : ℝ) (u v : ℂ) :
    Measurable fun μ : Measure ℂ => lgdDZZ μ δ u v := by
  simp_rw [lgdDZZ_eq_lgdRat]
  exact measurable_lgdRat (fun c q => LatticeProb.LQG.measurable_ballMassQ c q) δ _ _

/-- The minimal Liouville graph distance between two sets is a measurable function of the
measure. -/
theorem _root_.LatticeProb.LQG.measurable_lgdMinSet (δ : ℝ) (A B : Set ℂ) :
    Measurable fun μ : Measure ℂ => lgdMinSet μ δ A B := by
  simp_rw [lgdMinSet_eq_lgdRat]
  exact measurable_lgdRat (fun c q => LatticeProb.LQG.measurable_ballMassQ c q) δ _ _

/-- **The exponent event of the Liouville graph distance is measurable.** The set of measures `μ`
on `ℂ` with `log D_δ(u, v) / log δ⁻¹ → χ` as `δ → 0⁺` is measurable for the Giry σ-algebra. -/
theorem _root_.LatticeProb.LQG.measurableSet_lgdExponentEvent (u v : ℂ) (χ : ℝ) :
    MeasurableSet {μ : Measure ℂ | Tendsto (fun δ : ℝ =>
      Real.log (lgdDZZ μ δ u v).toNat / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)} := by
  have e : {μ : Measure ℂ | Tendsto (fun δ : ℝ =>
      Real.log (lgdDZZ μ δ u v).toNat / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)} =
      {μ | Tendsto (fun n : ℕ => Real.log (lgdDZZ μ ((2 : ℝ)⁻¹ ^ n) u v).toNat /
        Real.log ((2 : ℝ)⁻¹ ^ n)⁻¹) atTop (𝓝 χ)} :=
    Set.ext fun μ => GMCIdent4.tendsto_lgdRatio_iff_dyadic (g := fun δ => lgdDZZ μ δ u v)
      (fun _ _ hδ hle => lgdDZZ_antitone μ hδ.le hle u v) (fun δ => one_le_lgdDZZ μ δ u v) χ
  rw [e]
  exact measurableSet_tendsto (𝓝 χ) fun n =>
    (measurable_log_toNat.comp (LatticeProb.LQG.measurable_lgdDZZ _ u v)).div_const _

end LQGMetric
