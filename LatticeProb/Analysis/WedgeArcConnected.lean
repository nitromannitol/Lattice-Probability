import LatticeProb.Analysis.WedgeArcIntegral

/-! # Connected proper circular arcs -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A nonempty symmetric arc is connected in the unit circle. -/
theorem isConnected_unitCircle_symmetric_arc {θ : ℝ} (hθ : 0 < θ) :
    IsConnected ((Subtype.val : {z : ℂ // ‖z‖ = 1} → ℂ) ⁻¹'
      (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2))) := by
  let f : ℝ → {z : ℂ // ‖z‖ = 1} := fun x =>
    ⟨circleMap 0 1 x, by simp [norm_circleMap_zero]⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    fun_prop
  have heq : (Subtype.val : {z : ℂ // ‖z‖ = 1} → ℂ) ⁻¹'
      (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2)) =
      f '' Ioo (-θ / 2) (θ / 2) := by
    ext z
    constructor
    · rintro ⟨x, hx, hxz⟩
      exact ⟨x, hx, Subtype.ext hxz⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [heq]
  exact (isConnected_Ioo (by linarith : -θ / 2 < θ / 2)).image f hf.continuousOn

/-- A symmetric arc shorter than a full turn omits its positive endpoint. -/
theorem unitCircle_symmetric_arc_ne_univ {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    ((Subtype.val : {z : ℂ // ‖z‖ = 1} → ℂ) ⁻¹'
      (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2))) ≠ univ := by
  let z : {z : ℂ // ‖z‖ = 1} :=
    ⟨circleMap 0 1 (θ / 2), by simp [norm_circleMap_zero]⟩
  intro heq
  have hz : z ∈ (Subtype.val : {z : ℂ // ‖z‖ = 1} → ℂ) ⁻¹'
      (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2)) := by rw [heq]; trivial
  obtain ⟨x, hx, hxz⟩ := hz
  have hargx := arg_circleMap_mem_wedge (by linarith : θ ≤ 2 * Real.pi)
    ⟨hx.1, hx.2.le⟩
  have hargz := arg_circleMap_mem_wedge (by linarith : θ ≤ 2 * Real.pi)
    (show θ / 2 ∈ Ioc (-θ / 2) (θ / 2) from ⟨by linarith, le_rfl⟩)
  have h := congrArg Complex.arg hxz
  change (circleMap 0 1 x).arg = (circleMap 0 1 (θ / 2)).arg at h
  rw [hargx, hargz] at h
  linarith [hx.2]

end LatticeProb
