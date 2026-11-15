import LatticeProb.Analysis.IntervalDirichletExtension
import LatticeProb.Analysis.WedgeArcIntegral

/-! # Classical angular Dirichlet extension on a circular arc -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- For an arc shorter than a full circle, arbitrary endpoint values have a
continuous extension whose angular pullback has zero second derivative in the
interior. -/
theorem exists_wedgeArc_dirichlet_extension {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (u v : ℝ) :
    ∃ F : ℂ → ℝ,
      ContinuousOn F {z : ℂ | ‖z‖ = 1 ∧ z.arg ∈ Icc (-θ / 2) (θ / 2)} ∧
      F (circleMap 0 1 (-θ / 2)) = u ∧
      F (circleMap 0 1 (θ / 2)) = v ∧
      ∀ x ∈ Ioo (-θ / 2) (θ / 2),
        HasDerivAt (deriv (fun t => F (circleMap 0 1 t))) 0 x := by
  obtain ⟨g, hgc, hga, hgb, hgg⟩ :=
    exists_interval_dirichlet_extension (by linarith : -θ / 2 < θ / 2) u v
  let F : ℂ → ℝ := fun z => g z.arg
  have hpull {x : ℝ} (hx : x ∈ Icc (-θ / 2) (θ / 2)) :
      F (circleMap 0 1 x) = g x := by
    have hx' : x ∈ Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) := by
      constructor <;> linarith [hx.1, hx.2]
    simp only [F, arg_circleMap_mem_wedge le_rfl hx']
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      simp [h] at hz
    have hzarg : z.arg ≠ Real.pi := by
      have := hz.2.2
      linarith
    exact (hgc.continuousAt.comp (Complex.continuousAt_arg
      (Complex.mem_slitPlane_iff_arg.mpr ⟨hzarg, hz0⟩))).continuousWithinAt
  · rw [hpull ⟨le_rfl, by linarith⟩, hga]
  · rw [hpull ⟨by linarith, le_rfl⟩, hgb]
  · intro x hx
    have heq : (fun t => F (circleMap 0 1 t)) =ᶠ[𝓝 x] g := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
      exact hpull ⟨ht.1.le, ht.2.le⟩
    exact (hgg x).congr_of_eventuallyEq heq.deriv

end LatticeProb
