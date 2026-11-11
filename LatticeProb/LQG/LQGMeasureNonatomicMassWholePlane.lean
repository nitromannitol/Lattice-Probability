import Mathlib
import LatticeProb.LQG.LQGMeasureNonatomicMassScaled
import LatticeProb.LQG.LQGMeasureNonatomicMassWeight
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly
import LatticeProb.LQG.LQGMeasureInputs

/-!
# Non-atomicity of the LQG measure off the origin from the multiscale mass bound: LP form

LP copy of `HarmonicBalls/Proofs/Sec6/WholePlaneNonatomic.lean`, lines 1-100 (the two statements used by the chain:
`ae_wholePlane_nonatomic_of_scaledBallMass` and `ae_singular_nonatomic_off_origin_of_scaledBallMass`). The upper multiscale
ball-mass bound `WholePlaneScaledBallMassStepLP` (`LQGMeasureNonatomicMassScaled.lean`) implies that the LQG measure of the
whole-plane GFF has no atoms (Berestycki-Powell, *Gaussian free field, Liouville quantum gravity and Gaussian multiplicative
chaos*); the singular LQG measure `μ_h` of `h = h^ℂ - α₀ log|·|` has no atom away from `0` by the Weyl relation
`μ_h = |x|^{-γα₀} μ₀` on `ℂ \ {0}` (`singularWeightStep_lp`). The existence input is `LQGMeasureExistenceLP` at `α₀ = 0`
(hypothesis only). The statements use no Harmonic-balls object.
-/

universe u

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory Metric Filter Set LatticeProb.Gauss LatticeProb.LQG
open scoped Topology ENNReal

/-- The multiscale whole-plane ball-mass bound implies almost sure non-atomicity of the whole-plane LQG measure (LP copy of
`HarmonicBalls.Section6.ae_wholePlane_nonatomic_of_scaledBallMass`). -/
theorem ae_wholePlane_nonatomic_of_scaledBallMass
    (hS : WholePlaneScaledBallMassStepLP.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, μ ω {z} = 0 := by
  let β : ℝ := (2 - γ) ^ 2 / 4
  let βm : ℝ := (2 + γ) ^ 2 / 2 + 1
  let ζ : ℝ := min (β / 2) (1 / 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβlt : β < (2 - γ) ^ 2 / 2 := by
    dsimp [β]; nlinarith [sq_pos_of_pos (show 0 < 2 - γ by linarith)]
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζlt : ζ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hβζ : 0 < β - ζ := by
    have := min_le_left (β / 2) (1 / 2)
    dsimp only [ζ]
    linarith
  have key (n : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ closedBall (0 : ℂ) ((n : ℝ) + 1),
        μ ω (ball z ((2 : ℝ)⁻¹ ^ k)) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ (β - ζ)) := by
    have hpoly := hS γ hγ hγ2 Ω P hC hcirc μ hG hμ ((n : ℝ) + 1) (by positivity)
      β βm ζ hβ hβlt (by dsimp [βm]; linarith) hζ hζlt
    filter_upwards [polyHighProb_ae_eventually_dyadic hpoly] with ω hω
    filter_upwards [hω] with k hk z hz
    have hδ : 0 < ((2 : ℝ)⁻¹ ^ k) := by positivity
    have hδ1 : ((2 : ℝ)⁻¹ ^ k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hrad : ((2 : ℝ)⁻¹ ^ k) ^ (1 - ζ) ≤ 1 :=
      Real.rpow_le_one hδ.le hδ1 (by linarith)
    have hbound := (hk 1 hrad le_rfl z (by simpa using hz)).2
    simp only [Real.one_rpow, one_mul, div_one] at hbound
    rw [← Real.rpow_add hδ] at hbound
    simpa only [sub_eq_add_neg] using hbound
  have hscale : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hreal : Tendsto (fun k : ℕ => (((2 : ℝ)⁻¹) ^ k) ^ (β - ζ)) atTop (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hβζ.le).tendsto 0).comp hscale
    simpa only [Function.comp_def, Real.zero_rpow hβζ.ne'] using h
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal ((((2 : ℝ)⁻¹) ^ k) ^ (β - ζ)))
      atTop (𝓝 0) := by simpa using ENNReal.tendsto_ofReal hreal
  filter_upwards [ae_all_iff.mpr key] with ω hω z
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hz : z ∈ closedBall (0 : ℂ) ((n : ℝ) + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  apply le_zero_iff.mp
  apply ge_of_tendsto hlim
  filter_upwards [hω n] with k hk
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self (by positivity)))).trans (hk z hz)

/-- The singular LQG measure has no atom away from the logarithmic singularity (LP copy of
`HarmonicBalls.Section6.ae_singular_nonatomic_off_origin_of_scaledBallMass`). The whole-plane multiscale estimate and the
punctured-plane Weyl identity (`singularWeightStep_lp`) give it; the existence input `LQGMeasureExistenceLP` is used at `α₀ = 0`
only. -/
theorem ae_singular_nonatomic_off_origin_of_scaledBallMass
    (hS : WholePlaneScaledBallMassStepLP.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : LQGMeasureExistenceLP P γ 0 hC hcirc)
    (μ : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, z ≠ 0 → μ ω {z} = 0 := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE hG hγ hγ2 hQ
  have hweight := singularWeightStep_lp γ α₀ hγ hγ2 hα Ω P hC hcirc μ μ₀ hG hμ hμ₀
  filter_upwards [hweight, ae_wholePlane_nonatomic_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀]
    with ω hweight hno z hz
  have heq := congrArg (fun ν : Measure ℂ => ν {z}) hweight
  rw [Measure.restrict_apply (measurableSet_singleton z), Measure.restrict_apply (measurableSet_singleton z)] at heq
  have hs : ({z} : Set ℂ) ∩ ({0} : Set ℂ)ᶜ = {z} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, by simpa [hx] using hz⟩
  rw [hs] at heq
  rw [heq]
  exact (withDensity_absolutelyContinuous (μ₀ ω) _) (hno z)

end LatticeProb.LQG.LQGMeasureNonatomicMass
