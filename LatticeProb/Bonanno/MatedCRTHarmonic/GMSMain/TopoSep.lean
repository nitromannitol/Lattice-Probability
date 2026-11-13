/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.TopoSep at commit fdb5cad; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.TopoLog

/-! # A compact separator between disjoint closed planar sets

A compact side of a closed separation admits an open neighborhood with compact
closure. Its frontier lies outside both sides and separates points on them.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic

open Set QuantumZipper.CA.Topo

/-- A compact set and a disjoint closed set have a compact frontier separating
one chosen point of each set. -/
theorem topo_exists_compact_frontier {K F : Set ℂ} (hK : IsCompact K)
    (hF : IsClosed F) (hKF : Disjoint K F) {a b : ℂ}
    (ha : a ∈ K) (hb : b ∈ F) :
    ∃ J : Set ℂ, IsCompact J ∧ J ⊆ (K ∪ F)ᶜ ∧
      a ∈ Jᶜ ∧ b ∈ Jᶜ ∧ b ∉ connectedComponentIn Jᶜ a := by
  have hKF' : K ⊆ Fᶜ := disjoint_left.mp hKF
  obtain ⟨U, hUo, hKU, hUF, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK hF.isOpen_compl hKF'
  let J := frontier U
  have hJc : IsCompact J := hUc.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hJU : Disjoint J U := by
    change Disjoint (frontier U) U
    rw [hUo.frontier_eq]
    exact disjoint_sdiff_left
  have hJsub : J ⊆ (K ∪ F)ᶜ := by
    intro z hz hmem
    rcases hmem with hzK | hzF
    · exact (disjoint_left.mp hJU hz) (hKU hzK)
    · exact (hUF (frontier_subset_closure hz)) hzF
  have haU : a ∈ U := hKU ha
  have hbcl : b ∉ closure U := fun h => (hUF h) hb
  have haJ : a ∈ Jᶜ := by
    intro h
    exact (disjoint_left.mp hJU h) haU
  have hbJ : b ∈ Jᶜ := by
    intro h
    exact hbcl (frontier_subset_closure h)
  refine ⟨J, hJc, hJsub, haJ, hbJ, ?_⟩
  intro hbC
  have hC : IsPreconnected (connectedComponentIn Jᶜ a) := isPreconnected_connectedComponentIn
  have hJcompl : Jᶜ = U ∪ (closure U)ᶜ := by
    ext z
    simp only [J, hUo.frontier_eq, mem_compl_iff, mem_sdiff, not_and, not_not, mem_union]
    tauto
  have hCsub : connectedComponentIn Jᶜ a ⊆ U ∪ (closure U)ᶜ := by
    rw [← hJcompl]
    exact connectedComponentIn_subset Jᶜ a
  have hdis : connectedComponentIn Jᶜ a ∩ (U ∩ (closure U)ᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
    intro hz
    exact hz.2.2 (subset_closure hz.2.1)
  have hsplit := (isPreconnected_iff_subset_of_disjoint).mp hC U (closure U)ᶜ
    hUo isClosed_closure.isOpen_compl hCsub hdis
  rcases hsplit with hCU | hCU
  · exact hbcl (subset_closure (hCU hbC))
  · exact (hCU (mem_connectedComponentIn haJ)) (subset_closure haU)

/-- A compact side of a closed separation of the complement contradicts simple
connectivity of an open domain. -/
theorem topo_false_of_closed_separation {D K F : Set ℂ} (hDo : IsOpen D)
    [SimplyConnectedSpace D] (hKc : IsCompact K) (hFc : IsClosed F)
    (hKF : Disjoint K F) (hcover : Dᶜ ⊆ K ∪ F)
    (hKD : K ⊆ Dᶜ) (hFD : F ⊆ Dᶜ)
    (hKne : K.Nonempty) (hFne : F.Nonempty) : False := by
  obtain ⟨a, ha⟩ := hKne
  obtain ⟨b, hb⟩ := hFne
  obtain ⟨J, hJc, hJsub, haJ, hbJ, hbsep⟩ :=
    topo_exists_compact_frontier hKc hFc hKF ha hb
  have hJD : J ⊆ D := by
    intro z hz
    by_contra hzD
    exact hJsub hz (hcover hzD)
  obtain ⟨L, hLc, hL⟩ := topo_hasLogOn_ratio_of_simplyConnected hDo
    (hKD ha) (hFD hb)
  have hJlog : HasLogOn (fun z : ℂ => (z - a) / (z - b)) J :=
    ⟨L, hLc.mono hJD, fun z hz => hL z (hJD hz)⟩
  exact hbsep (not_separates_of_hasLogOn hJc haJ hbJ hJlog)

end MatedCRTHarmonic
