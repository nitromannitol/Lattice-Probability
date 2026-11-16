import LatticeProb.Topology.CompactImageLocallyPathConnected

/-! # Paths in open portions of compact path images -/

set_option autoImplicit false

open Set

namespace LatticeProb.Topology

/-- A connected open portion of a compact interval image is path connected. -/
theorem joinedIn_image_Icc_inter_open {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : ℝ → Y} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    {U : Set Y} (hU : IsOpen U) (hconn : IsPreconnected (f '' Icc a b ∩ U))
    {x y : Y} (hx : x ∈ f '' Icc a b ∩ U) (hy : y ∈ f '' Icc a b ∩ U) :
    JoinedIn (f '' Icc a b ∩ U) x y := by
  let K : Set Y := f '' Icc a b
  let : LocallyPathConnectedSpace K := locallyPathConnectedSpace_image_Icc hf
  have hK : IsClosed K := (isCompact_Icc.image_of_continuousOn hf).isClosed
  let V : Set K := Subtype.val ⁻¹' U
  have hVopen : IsOpen V := hU.preimage continuous_subtype_val
  have hsub : K ∩ U ⊆ range (Subtype.val : K → Y) := by
    rintro z ⟨hz, _⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have hpre : IsPreconnected ((Subtype.val : K → Y) ⁻¹' (K ∩ U)) :=
    hconn.preimage_of_isClosedMap Subtype.val_injective hK.isClosedMap_subtype_val hsub
  have hVpre : IsPreconnected V := by
    convert hpre using 1
    ext z
    simp only [V, mem_preimage, mem_inter_iff, z.property, true_and]
  have hVconn : IsConnected V := ⟨⟨⟨x, hx.1⟩, hx.2⟩, hVpre⟩
  have hpath := (hVopen.isConnected_iff_isPathConnected.mp hVconn).joinedIn
    ⟨x, hx.1⟩ hx.2 ⟨y, hy.1⟩ hy.2
  have hmapped := hpath.map continuous_subtype_val.continuousOn
  apply hmapped.mono
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w.property, hw⟩

/-- If removing a closed obstacle leaves a connected portion of a compact
interval image, its points can be joined while avoiding the obstacle. -/
theorem joinedIn_image_Icc_diff_closed {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : ℝ → Y} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    {C : Set Y} (hC : IsClosed C) (hconn : IsPreconnected (f '' Icc a b \ C))
    {x y : Y} (hx : x ∈ f '' Icc a b \ C) (hy : y ∈ f '' Icc a b \ C) :
    JoinedIn (f '' Icc a b \ C) x y := by
  exact joinedIn_image_Icc_inter_open hf hC.isOpen_compl hconn hx hy

end LatticeProb.Topology
