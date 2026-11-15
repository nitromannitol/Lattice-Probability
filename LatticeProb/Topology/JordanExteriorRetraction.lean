import LatticeProb.Topology.InvertedExteriorDisc
import LatticeProb.Topology.InvertedDiskRetraction

/-! Retraction of a closed Jordan exterior onto its boundary. -/

set_option autoImplicit false

noncomputable section

open Set Metric Function
open LQGMetric

namespace LatticeProb

/-- The closed exterior of a compact set with Jordan frontier and connected
complement retracts continuously onto its frontier. -/
theorem exists_jordan_exterior_boundary_retraction {K : Set ℂ} {z : ℂ}
    (hK : IsCompact K) (hz : z ∈ interior K) (hKc : IsPreconnected Kᶜ)
    (hJ : JordanMap.IsJordanCurve (frontier K)) :
    ∃ r : closure Kᶜ → ℂ, Continuous r ∧
      (∀ x, r x ∈ frontier K) ∧
      (∀ x : closure Kᶜ, (x : ℂ) ∈ frontier K → r x = x) := by
  obtain ⟨e, he, heB⟩ := exists_inverted_exterior_disc hK hz hKc hJ
  obtain ⟨r, hr, hrB, hrfix⟩ := exists_inverted_disk_boundary_retraction e he
  have hxz : ∀ x : closure Kᶜ, (x : ℂ) ≠ z := by
    intro x h
    have : z ∉ closure Kᶜ := by
      rw [interior_eq_compl_closure_compl] at hz
      exact hz
    exact this (h ▸ x.2)
  have hxinv : ∀ x : closure Kᶜ, ((x : ℂ) - z)⁻¹ ∈ closure (CONF.DD.toOmega K z) := by
    intro x
    have hc : ContinuousAt (fun t : ℂ => (t - z)⁻¹) x :=
      (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 (hxz x))
    apply closure_mono _ (mem_closure_image hc x.2)
    rw [CONF.DD.to_omega_eq hz]
    exact subset_union_left
  let g : closure Kᶜ → {w : ℂ // w ≠ 0 ∧ w⁻¹ ∈ closure (CONF.DD.toOmega K z)} :=
    fun x => ⟨x - z, sub_ne_zero.2 (hxz x), hxinv x⟩
  have hg : Continuous g := (continuous_subtype_val.sub continuous_const).subtype_mk _
  have hboundary : (fun v => (e v : ℂ)⁻¹) '' {v | (v : ℂ) ∈ sphere 0 1} =
      (fun y : ℂ => y - z) '' frontier K := by
    rw [← image_image, heB, image_image]
    apply image_congr
    intro y hy
    simp only [inv_inv]
  refine ⟨fun x => z + r (g x), continuous_const.add (hr.comp hg), ?_, ?_⟩
  · intro x
    change z + r (g x) ∈ frontier K
    have hx := hrB (g x)
    rw [hboundary] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [← hxy, add_sub_cancel]
    exact hy
  · intro x hx
    change z + r (g x) = (x : ℂ)
    have hmem : (g x : ℂ) ∈ (fun v => (e v : ℂ)⁻¹) ''
        {v | (v : ℂ) ∈ sphere 0 1} := by
      rw [hboundary]
      exact ⟨x, hx, rfl⟩
    rw [hrfix (g x) hmem]
    exact add_sub_cancel _ _

end LatticeProb
