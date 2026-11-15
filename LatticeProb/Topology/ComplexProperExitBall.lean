import LatticeProb.Topology.ComplexJointExitBall
import LatticeProb.Topology.ProperCurveFiniteExit

/-! # Finite planar exits of proper complex curves -/

set_option autoImplicit false

open Filter MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A proper complex curve has finite forward and backward planar ball exits. -/
theorem planar_exit_ball_ne_top_of_complex_proper
    (f : ℝ → EuclideanSpace ℝ (Fin 2)) (η : ℝ → ℂ)
    (hη : ∀ t, f t = Complex.orthonormalBasisOneI.repr (η t))
    (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ)) (r : ℝ) :
    openExitTime (fun s (_ : Unit) => f (0 + (s : ℝ))) (ball 0 r) () ≠ ⊤ ∧
    openExitTime (fun s (_ : Unit) => f (0 - (s : ℝ))) (ball 0 r) () ≠ ⊤ := by
  let i := Complex.orthonormalBasisOneI.repr
  have hout (t : ℝ) : f t ∉ ball 0 r ↔ η t ∉ ball 0 r := by
    rw [hη t]
    simpa only [mem_ball, map_zero, i.dist_map] using
      (show i (η t) ∉ ball (i 0) r ↔ η t ∉ ball 0 r by simp only [mem_ball, i.dist_map])
  have transfer (g : ℝ≥0 → ℝ) :
      openExitTime (fun s (_ : Unit) => f (g s)) (ball 0 r) () ≤
      openExitTime (fun s (_ : Unit) => η (g s)) (ball 0 r) () := by
    unfold openExitTime
    refine le_iInf fun t => ?_
    exact iInf_le_of_le ⟨t.1, (hout _).mpr t.2⟩ le_rfl
  have h := openExitTime_ball_ne_top_of_tendsto_cocompact η hproper 0 0 r
  exact ⟨ne_top_of_le_ne_top h.1 (transfer (fun s => 0 + (s : ℝ))),
    ne_top_of_le_ne_top h.2 (transfer (fun s => 0 - (s : ℝ)))⟩

/-- Properness supplies the finite-clock hypotheses for two-sided exit witnesses. -/
theorem not_mem_firstExitBallFailure_of_complex_proper_witnesses
    {β : Type*} (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (ω : β)
    (η : ℝ → ℂ) (hη : ∀ t, f ω t = Complex.orthonormalBasisOneI.repr (η t))
    (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hwback : ∃ z, ball z (ε * Real.exp (k : ℝ)) ⊆
      η '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 (Real.exp (k : ℝ))}) 0)
    (hwforward : ∃ z, ball z (ε * Real.exp (k : ℝ)) ⊆
      η '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 (Real.exp (k : ℝ))})) :
    ω ∉ firstExitBallFailure f ε k := by
  obtain ⟨hfwd, hbwd⟩ := planar_exit_ball_ne_top_of_complex_proper (f ω) η hη hproper _
  exact not_mem_firstExitBallFailure_of_complex_witnesses f ω η hη hε k hfwd hbwd hwback hwforward

/-- Almost-sure properness gives both finite planar exits at every radius at once. -/
theorem ae_forall_planar_exit_ball_ne_top_of_complex_proper
    {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (f : β → ℝ → EuclideanSpace ℝ (Fin 2)) (η : β → ℝ → ℂ)
    (hpath : ∀ᵐ ω ∂μ, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      ∀ t, f ω t = Complex.orthonormalBasisOneI.repr (η ω t)) :
    ∀ᵐ ω ∂μ, ∀ r : ℝ,
      openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ))) (ball 0 r) () ≠ ⊤ ∧
      openExitTime (fun s (_ : Unit) => f ω (0 - (s : ℝ))) (ball 0 r) () ≠ ⊤ := by
  filter_upwards [hpath] with ω hω
  exact fun r => planar_exit_ball_ne_top_of_complex_proper (f ω) (η ω) hω.2 hω.1 r

end LatticeProb
