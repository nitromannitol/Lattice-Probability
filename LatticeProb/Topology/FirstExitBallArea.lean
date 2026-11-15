import LatticeProb.Topology.FirstExitBallSelection
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Areas of first-exit traces containing balls -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- A closed ball in each Euclidean first-exit trace gives the corresponding
area lower bound for the complex curve, with the same exit radii. -/
theorem first_exit_trace_area_of_not_mem_firstExitBallFailure
    {β : Type*} (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (ω : β)
    (η : ℝ → ℂ) (hη : ∀ t, f ω t = Complex.orthonormalBasisOneI.repr (η t))
    {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hgood : ω ∉ firstExitBallFailure f ε k) :
    ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / (4 / (Real.pi * ε ^ 2))) ≤
      min (volume (η '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 (Real.exp k)}) 0))
        (volume (η '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 (Real.exp k)}))) := by
  classical
  let i := Complex.orthonormalBasisOneI.repr
  have hout (t : ℝ) : f ω t ∉ ball 0 (Real.exp (k : ℝ)) ↔
      η t ∉ ball 0 (Real.exp (k : ℝ)) := by
    rw [hη t]
    simpa only [mem_ball, map_zero, i.dist_map] using
      (show i (η t) ∉ ball (i 0) (Real.exp (k : ℝ)) ↔
        η t ∉ ball 0 (Real.exp (k : ℝ)) by simp only [mem_ball, i.dist_map])
  have hleft : {t : ℝ | t ≤ 0 ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))} =
      {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 (Real.exp (k : ℝ))} := by
    ext t
    simp only [mem_ofPred_eq, hout]
  have hright : {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))} =
      {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 (Real.exp (k : ℝ))} := by
    ext t
    simp only [mem_ofPred_eq, hout]
  have hgood' := Classical.not_not.mp hgood
  obtain ⟨⟨_, _, wR, hwR⟩, ⟨_, _, wL, hwL⟩⟩ := hgood'
  rw [hright] at hwR
  rw [hleft] at hwL
  have transfer (A : Set ℝ) (w : EuclideanSpace ℝ (Fin 2))
      (hw : closedBall w (ε * Real.exp (k : ℝ) / 2) ⊆ f ω '' A) :
      closedBall (i.symm w) (ε * Real.exp (k : ℝ) / 2) ⊆ η '' A := by
    intro x hx
    have hx' : i x ∈ closedBall w (ε * Real.exp (k : ℝ) / 2) := by
      simpa only [mem_closedBall, ← i.dist_map, i.apply_symm_apply] using hx
    obtain ⟨t, ht, heq⟩ := hw hx'
    refine ⟨t, ht, i.injective ?_⟩
    simpa only [hη] using heq
  have hvol (A : Set ℝ) (w : EuclideanSpace ℝ (Fin 2))
      (hw : closedBall w (ε * Real.exp (k : ℝ) / 2) ⊆ f ω '' A) :
      ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / (4 / (Real.pi * ε ^ 2))) ≤
        volume (η '' A) := by
    have hr : 0 ≤ ε * Real.exp (k : ℝ) / 2 := by positivity
    calc
      ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / (4 / (Real.pi * ε ^ 2))) =
          volume (closedBall (i.symm w) (ε * Real.exp (k : ℝ) / 2)) := by
        rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hr,
          ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        simp only [NNReal.coe_real_pi]
        field_simp [ne_of_gt hε, Real.pi_ne_zero]
        ring
      _ ≤ volume (η '' A) := measure_mono (transfer A w hw)
  exact le_min (hvol _ _ hwL) (hvol _ _ hwR)

/-- A finite family of successful scales supplies all trace bounds in any
scale range covered by that family. -/
theorem first_exit_trace_area_of_selected_scales
    {β : Type*} (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (ω : β)
    (η : ℝ → ℂ) (hη : ∀ t, f ω t = Complex.orthonormalBasisOneI.repr (η t))
    {ε : ℝ} (hε : 0 < ε) (K : Finset ℤ) (L U : ℝ)
    (hcover : ∀ k : ℤ, Real.log L - 1 < (k : ℝ) → (k : ℝ) ≤ Real.log U → k ∈ K)
    (hgood : ∀ k ∈ K, ω ∉ firstExitBallFailure f ε k) :
    ∀ k : ℤ, Real.log L - 1 < (k : ℝ) → (k : ℝ) ≤ Real.log U →
      ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / (4 / (Real.pi * ε ^ 2))) ≤
        min (volume (η '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 (Real.exp k)}) 0))
          (volume (η '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 (Real.exp k)}))) := by
  intro k hkL hkU
  exact first_exit_trace_area_of_not_mem_firstExitBallFailure f ω η hη hε k
    (hgood k (hcover k hkL hkU))

end LatticeProb
