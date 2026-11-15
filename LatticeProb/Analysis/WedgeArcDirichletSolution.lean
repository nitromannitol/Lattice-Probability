import LatticeProb.Analysis.WedgeArcDirichletUniqueness
import LatticeProb.Analysis.WedgeArcIntegral

/-! # Classical angular Dirichlet solutions on a circular arc -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Arbitrary endpoint values have a unique classical angular solution on a
closed circular arc shorter than a full turn, with uniqueness on the arc. -/
theorem exists_uniqueOn_wedgeArc_dirichlet_solution {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (u v : ℝ) :
    ∃ F : ℂ → ℝ,
      ContinuousOn F (circleMap 0 1 '' Icc (-θ / 2) (θ / 2)) ∧
      DifferentiableOn ℝ (fun t => F (circleMap 0 1 t)) (Ioo (-θ / 2) (θ / 2)) ∧
      (∀ x ∈ Ioo (-θ / 2) (θ / 2),
        HasDerivAt (deriv (fun t => F (circleMap 0 1 t))) 0 x) ∧
      F (circleMap 0 1 (-θ / 2)) = u ∧
      F (circleMap 0 1 (θ / 2)) = v ∧
      ∀ G : ℂ → ℝ,
        ContinuousOn G (circleMap 0 1 '' Icc (-θ / 2) (θ / 2)) →
        DifferentiableOn ℝ (fun t => G (circleMap 0 1 t)) (Ioo (-θ / 2) (θ / 2)) →
        (∀ x ∈ Ioo (-θ / 2) (θ / 2),
          HasDerivAt (deriv (fun t => G (circleMap 0 1 t))) 0 x) →
        G (circleMap 0 1 (-θ / 2)) = u → G (circleMap 0 1 (θ / 2)) = v →
        (circleMap 0 1 '' Icc (-θ / 2) (θ / 2)).EqOn F G := by
  let a : ℝ := -θ / 2
  let b : ℝ := θ / 2
  have hab : a < b := by dsimp [a, b]; linarith
  let c : ℝ := (v - u) / (b - a)
  let g : ℝ → ℝ := fun x => u + c * (x - a)
  let F : ℂ → ℝ := fun z => g z.arg
  have hg (x : ℝ) : HasDerivAt g c x := by
    dsimp [g]
    have hx : HasDerivAt (fun y : ℝ => y - a) 1 x :=
      (hasDerivAt_id' x).sub_const a
    simpa only [mul_one] using
      (hasDerivAt_const_add_iff u).2 (HasDerivAt.const_mul c hx)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hpull {x : ℝ} (hx : x ∈ Icc a b) : F (circleMap 0 1 x) = g x := by
    have hx' : x ∈ Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) := by
      dsimp [a, b] at hx
      constructor <;> linarith [hx.1, hx.2]
    simp only [F, arg_circleMap_mem_wedge le_rfl hx']
  have hlocal {x : ℝ} (hx : x ∈ Ioo a b) :
      (fun t => F (circleMap 0 1 t)) =ᶠ[𝓝 x] g := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact hpull ⟨ht.1.le, ht.2.le⟩
  have hF : ContinuousOn F (circleMap 0 1 '' Icc a b) := by
    rintro z ⟨x, hx, rfl⟩
    have hx' : x ∈ Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) := by
      dsimp [a, b] at hx
      constructor <;> linarith [hx.1, hx.2]
    have harg : (circleMap 0 1 x).arg ≠ Real.pi := by
      rw [arg_circleMap_mem_wedge le_rfl hx']
      dsimp [a, b] at hx
      linarith [hx.2]
    have hn : circleMap 0 1 x ≠ 0 := by
      intro hz
      have hh := norm_circleMap_zero (1 : ℝ) x
      rw [hz] at hh
      norm_num at hh
    exact (hgc.continuousAt.comp (Complex.continuousAt_arg
      (Complex.mem_slitPlane_iff_arg.mpr ⟨harg, hn⟩))).continuousWithinAt
  have hdF : DifferentiableOn ℝ (fun t => F (circleMap 0 1 t)) (Ioo a b) := by
    intro x hx
    exact ((hg x).congr_of_eventuallyEq (hlocal hx)).differentiableAt.differentiableWithinAt
  have hddF : ∀ x ∈ Ioo a b,
      HasDerivAt (deriv (fun t => F (circleMap 0 1 t))) 0 x := by
    intro x hx
    have hderiv : deriv g = fun _ => c := by
      funext t
      exact (hg t).deriv
    exact ((by rw [hderiv]; exact hasDerivAt_const x c) : HasDerivAt (deriv g) 0 x).congr_of_eventuallyEq (hlocal hx).deriv
  have hFa : F (circleMap 0 1 a) = u := by
    rw [hpull ⟨le_rfl, hab.le⟩]
    simp [g]
  have hFb : F (circleMap 0 1 b) = v := by
    rw [hpull ⟨hab.le, le_rfl⟩]
    dsimp [g, c]
    have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp
    ring
  refine ⟨F, hF, hdF, hddF, hFa, hFb, ?_⟩
  intro G hG hdG hddG hGa hGb
  exact eqOn_circleMap_image_Icc_of_deriv_deriv_eq_zero hab hF hG hdF hdG hddF hddG
    (hFa.trans hGa.symm) (hFb.trans hGb.symm)

end LatticeProb
