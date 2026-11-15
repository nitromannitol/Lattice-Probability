import LatticeProb.Topology.PeanoContinuum
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep

/-! # Uniform local connectedness and compact path images -/

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace LatticeProb.Topology

/-- A compact uniformly locally connected plane set is locally connected. -/
theorem isLocallyConnectedSet_of_compact_ulc {K : Set ℂ} (hK : IsCompact K)
    (hULC : QuantumZipper.CA.Topo.ULC K) : IsLocallyConnectedSet K := by
  intro x hx N hN
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhdsWithin_iff.mp hN
  obtain ⟨δ, hδ, hδK⟩ := hULC (r / 2) (half_pos hr)
  let C : Set (Set ℂ) := {A | A ⊆ K ∧ IsPreconnected A ∧ x ∈ A ∧ diam A ≤ r / 2}
  let V : Set ℂ := ⋃₀ C
  have hsingle : {x} ∈ C := by
    refine ⟨singleton_subset_iff.mpr hx, isPreconnected_singleton, mem_singleton x, ?_⟩
    simp only [diam_singleton]
    exact (half_pos hr).le
  have hxV : x ∈ V := mem_sUnion.mpr ⟨{x}, hsingle, mem_singleton x⟩
  refine ⟨V, Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_,
    ⟨⟨x, hxV⟩, isPreconnected_sUnion x C (fun A hA => hA.2.2.1)
      (fun A hA => hA.2.1)⟩⟩
  · intro y hy
    obtain ⟨A, hAK, hAc, hxA, hyA, hAd⟩ :=
      hδK x hx y hy.2 (by simpa only [mem_ball, dist_comm] using hy.1)
    exact mem_sUnion.mpr ⟨A, ⟨hAK, hAc, hxA, hAd⟩, hyA⟩
  · intro y hy
    obtain ⟨A, hA, hyA⟩ := mem_sUnion.mp hy
    have hyK : y ∈ K := hA.1 hyA
    have hd : dist y x ≤ diam A :=
      Metric.dist_le_diam_of_mem (hK.isBounded.subset hA.1) hyA hA.2.2.1
    have hyball : y ∈ ball x r := by
      rw [mem_ball]
      linarith [hA.2.2.2]
    exact ⟨hrN ⟨hyball, hyK⟩, hyK⟩

/-- The image of a continuous unit-interval path is locally connected. -/
theorem isLocallyConnectedSet_image_unitInterval {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 1)) : IsLocallyConnectedSet (f '' Icc 0 1) :=
  isLocallyConnectedSet_of_compact_ulc (isCompact_Icc.image_of_continuousOn hf)
    (QuantumZipper.CA.Topo.ULC.image_Icc hf)

end LatticeProb.Topology
