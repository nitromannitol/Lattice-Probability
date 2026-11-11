import Mathlib
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin

/-!
# Cameron–Martin shifts of a centred Gaussian family are equivalent to the unshifted law

Let `X : I → Ω → ℝ` be a centred Gaussian process on a probability space `(Ω, P)` (`IsGaussianProcess`, with
measurable coordinates), and let `σ : I →₀ ℝ` be a finitely supported coefficient vector. Its Cameron–Martin
direction is the covariance function `j ↦ cov[∑ σ_i X_i, X_j]` (`covShift`). The law of the shifted family
`X + covShift X P σ` on `I → ℝ` (product σ-algebra) is mutually absolutely continuous with the law of `X`.

Proof. The Cameron–Martin tilt `tiltMeasure X P σ` has the strictly positive density
`exp (∑ σ_i X_i - Var/2)` with respect to `P`, so it is equivalent to `P`. Its image under `X` is the shifted law. Image measures of absolutely continuous measures under a
measurable map are absolutely continuous (`map_absolutelyContinuous_of_absolutelyContinuous`).

Literature locator: the Cameron–Martin theorem for Gaussian measures (Bogachev, *Gaussian Measures*, AMS 1998,
Ch. 2, Cameron–Martin space and shifts); the finite-dimensional tilt formula is standard. No theorem number is claimed.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Absolute continuity is preserved under images by a measurable map. -/
theorem map_absolutelyContinuous_of_absolutelyContinuous {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ ν : Measure Ω} (h : μ ≪ ν) {f : Ω → E} (hf : Measurable f) : μ.map f ≪ ν.map f :=
  Measure.AbsolutelyContinuous.mk fun s hs hνs => by
    rw [Measure.map_apply hf hs] at hνs ⊢
    exact h hνs

/-- Cameron–Martin equivalence: for a centred Gaussian family `X` and a finitely supported `σ`, the law of
`X + covShift X P σ` is mutually absolutely continuous with the law of `X`, as measures on `I → ℝ`. -/
theorem gaussian_map_shift_absolutelyContinuous {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : I → Ω → ℝ} (hX : IsGaussianProcess X P) (hmeas : ∀ i, Measurable (X i))
    (hcent : ∀ i, P[X i] = 0) (σ : I →₀ ℝ) :
    P.map (fun ω j => X j ω + QuantumZipper.CameronMartin.covShift X P σ j) ≪ P.map (fun ω j => X j ω) ∧
      P.map (fun ω j => X j ω) ≪ P.map (fun ω j => X j ω + QuantumZipper.CameronMartin.covShift X P σ j) := by
  have hpath := QuantumZipper.CameronMartin.map_tiltMeasure_path hX hmeas hcent σ
  have hXp : Measurable fun ω j => X j ω := measurable_pi_iff.mpr hmeas
  have hdens : Measurable (QuantumZipper.CameronMartin.tiltDensity X P σ) :=
    QuantumZipper.CameronMartin.measurable_tiltDensity hX hmeas σ
  have hτP : QuantumZipper.CameronMartin.tiltMeasure X P σ ≪ P := by
    unfold QuantumZipper.CameronMartin.tiltMeasure
    exact withDensity_absolutelyContinuous _ _
  have hPτ : P ≪ QuantumZipper.CameronMartin.tiltMeasure X P σ := by
    unfold QuantumZipper.CameronMartin.tiltMeasure
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (hdens.real_toNNReal.coe_nnreal_ennreal).aemeasurable
    · refine ae_of_all _ fun ω => ENNReal.coe_ne_zero.mpr ?_
      unfold QuantumZipper.CameronMartin.tiltDensity
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact Real.exp_pos _
  rw [← hpath]
  exact ⟨map_absolutelyContinuous_of_absolutelyContinuous hτP hXp,
    map_absolutelyContinuous_of_absolutelyContinuous hPτ hXp⟩

end LatticeProb
