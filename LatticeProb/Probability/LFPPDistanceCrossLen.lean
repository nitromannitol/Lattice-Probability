import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import LatticeProb.Bonanno.LQGDimension.LFPP.UpperAssemblyAux1
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

/-!
# The point-to-point LFPP distance as an LFPP crossing length

Let `U = (-2,2)²`. For a continuous field `φ`, the LFPP distance
`D^ξ(φ) = inf_γ ∫₀¹ e^{ξ φ(γ t)} |γ'(t)| dt` from `0` to `1` (over piecewise `C¹` paths
`γ : [0,1] → U`, real Bochner length) and the crossing length
`inf_{π : {0} → {1}, π ⊆ U} ∫_π e^{ξ φ} ds` (same path class, lower-integral length in `[0,∞]`)
agree: along a piecewise `C¹` path the speed `|γ'|` is integrable on `[0,1]` and `e^{ξ φ ∘ γ}` is
bounded, so the two lengths of every path coincide, and the infimum commutes with
`ENNReal.ofReal` because the set of lengths is nonempty (the straight segment) and bounded below.

## Main results
* `lfppLen_eq_ofReal_lfppLength`: the two LFPP lengths of an admissible path agree;
* `isAdmissiblePath_iff`: the two path classes agree;
* `crossLenIn_eq_ofReal_lfppDistance`: `crossLenIn ξ φ U {0} {1} = ofReal (D^ξ(φ))`;
* `toReal_crossLenIn_eq_lfppDistance`, `crossLenIn_ne_top`: the real form; the crossing length is
  finite.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace LQGMetric.HeatCircle

open LQGMetric.DDDF (crossLenIn)

/-- Along an admissible path and for a continuous field, the lower-integral LFPP length
`∫⁻_{[0,1]} e^{ξ φ(γ t)} |γ'(t)| dt` is the Bochner LFPP length `∫₀¹ e^{ξ φ(γ t)} |γ'(t)| dt`. -/
theorem lfppLen_eq_ofReal_lfppLength {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {γ : ℝ → ℂ}
    (hγ : LQGDimension.IsAdmissiblePath γ) :
    lfppLen ξ φ γ = ENNReal.ofReal (LQGDimension.lfppLength ξ φ γ) := by
  have hi : IntegrableOn (fun t => Real.exp (ξ * φ (γ t)) * ‖deriv γ t‖) (Ioc 0 1) :=
    (LQGDimension.TreeIneqJ42.lenIntegrand_intervalIntegrable hγ hφ ξ).1
  unfold lfppLen LQGDimension.lfppLength
  rw [intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t => by positivity),
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- The admissible paths of the LFPP distance are exactly the piecewise `C¹` paths from `0` to `1`
whose restriction to `[0,1]` stays in `U`. -/
theorem isAdmissiblePath_iff {γ : ℝ → ℂ} :
    LQGDimension.IsAdmissiblePath γ ↔
      IsPiecewiseC1Path γ 0 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ LQGDimension.U :=
  ⟨fun h => ⟨⟨h.source, h.target, h.continuousOn, h.piecewise_contDiff⟩, fun _ ht => h.mapsTo ht⟩,
    fun h => ⟨h.1.source, h.1.target, fun _ ht => h.2 _ ht, h.1.continuousOn, h.1.piecewise⟩⟩

/-- The LFPP lengths of the admissible paths are bounded below by `0`. -/
theorem bddBelow_range_lfppLength (ξ : ℝ) (φ : ℂ → ℝ) :
    BddBelow (range fun γ : {γ : ℝ → ℂ // LQGDimension.IsAdmissiblePath γ} =>
      LQGDimension.lfppLength ξ φ γ.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨γ, rfl⟩
  exact intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity

/-- **The point-to-point LFPP distance is a crossing length**: for a continuous field `φ`,
`inf_{π : {0} → {1}, π ⊆ U} ∫_π e^{ξ φ} ds = D^ξ(φ)`, `U = (-2,2)²`. -/
theorem crossLenIn_eq_ofReal_lfppDistance {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) :
    crossLenIn ξ φ LQGDimension.U {0} {1} = ENNReal.ofReal (LQGDimension.lfppDistance ξ φ) := by
  have hne : Nonempty {γ : ℝ → ℂ // LQGDimension.IsAdmissiblePath γ} :=
    ⟨⟨_, LQGDimension.UpperAssemblyAux.straight_admissible⟩⟩
  unfold crossLenIn LQGDimension.lfppDistance
  rw [Monotone.map_ciInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    ENNReal.ofReal_mono (bddBelow_range_lfppLength ξ φ)]
  simp only [mem_singleton_iff, iInf_iInf_eq_left]
  exact (Equiv.subtypeEquivRight fun γ => isAdmissiblePath_iff.symm).iInf_congr fun γ =>
    (lfppLen_eq_ofReal_lfppLength hφ (isAdmissiblePath_iff.2 γ.2)).symm

/-- The LFPP distance of any field is nonnegative. -/
theorem lfppDistance_nonneg (ξ : ℝ) (φ : ℂ → ℝ) : 0 ≤ LQGDimension.lfppDistance ξ φ :=
  Real.iInf_nonneg fun γ => intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity

/-- The real form: `(crossLenIn ξ φ U {0} {1}).toReal = D^ξ(φ)` for a continuous field `φ`. -/
theorem toReal_crossLenIn_eq_lfppDistance {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) :
    (crossLenIn ξ φ LQGDimension.U {0} {1}).toReal = LQGDimension.lfppDistance ξ φ := by
  rw [crossLenIn_eq_ofReal_lfppDistance hφ, ENNReal.toReal_ofReal (lfppDistance_nonneg ξ φ)]

/-- The crossing length from `0` to `1` in `U` of a continuous field is finite. -/
theorem crossLenIn_ne_top {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) :
    crossLenIn ξ φ LQGDimension.U {0} {1} ≠ ∞ := by
  rw [crossLenIn_eq_ofReal_lfppDistance hφ]
  exact ENNReal.ofReal_ne_top

end LQGMetric.HeatCircle
