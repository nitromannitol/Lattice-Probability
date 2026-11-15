import LatticeProb.Topology.PlanarSubspaceVisitCode
import LatticeProb.Prob.BinaryFibreDescent

/-! # Component visit codes from time-decorated surfaces -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- If an observation determines the time-decorated planar image up to
homeomorphism on a measurable set, the restricted component visit code has a
measurable decoder on that set. -/
theorem exists_measurable_visit_code_of_surface_reconstruction
    {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] (W : Ω → X) (hW : Measurable W)
    (f : Ω → C(ℝ, ℂ)) (K : Set ℝ) (u : ℝ) (hu : u ∈ K)
    (hcode : Measurable (fun ω (q : {q : ℚ // (q : ℝ) ∈ K}) =>
      curveComponentVisitCode K (f ω) (f ω u) q.1))
    {G : Set Ω} (hG : MeasurableSet G)
    (hreconstruct : ∀ x ∈ G, ∀ y ∈ G, W x = W y →
      ∃ e : (f x '' K) ≃ₜ (f y '' K),
        ∀ (t : ℝ) (ht : t ∈ K),
          (e ⟨f x t, mem_image_of_mem (f x) ht⟩).1 = f y t) :
    ∃ d : X → {q : ℚ // (q : ℝ) ∈ K} → Bool, Measurable d ∧
      ∀ ω ∈ G, (fun q : {q : ℚ // (q : ℝ) ∈ K} =>
        curveComponentVisitCode K (f ω) (f ω u) q.1) = d (W ω) := by
  apply exists_measurable_binary_decoder_of_fibre_constancy hW hcode hG
  intro x hx y hy heq
  obtain ⟨e, he⟩ := hreconstruct x hx y hy heq
  exact restricted_curveComponentVisitCode_eq_of_planar_subspace_homeomorph
    (f x) (f y) K e he u hu

end LatticeProb
