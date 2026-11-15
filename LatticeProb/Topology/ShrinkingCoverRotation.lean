import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sequences

/-! # Rotations of images of shrinking covers -/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace LatticeProb

/-- If each cover has arbitrarily small mesh and a single rotation aligns the
corresponding images at that scale, one rotation aligns the maps on the covered set. -/
theorem exists_rotation_eqOn_of_shrinking_cover
    {X : Type*} [PseudoMetricSpace X] {ι : ℕ → Type*}
    (K : Set X) (C : ∀ n, ι n → Set X) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcover : ∀ n, K ⊆ ⋃ j, C n j)
    (hmesh : ∀ n j x y, x ∈ C n j → y ∈ C n j → dist x y ≤ ε n)
    (f g : X → ℂ) (hg : Continuous g)
    (h : ∀ n, ∃ r : ℂ, ‖r‖ = 1 ∧
      ∀ j, f '' C n j = (fun z : ℂ => r * z) '' (g '' C n j)) :
    ∃ r : ℂ, ‖r‖ = 1 ∧ EqOn f (fun x => r * g x) K := by
  classical
  choose r hr himages using h
  have hrmem : ∀ n, r n ∈ sphere (0 : ℂ) 1 := by
    intro n
    simpa [mem_sphere, dist_zero_right] using hr n
  obtain ⟨r₀, hr₀, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hrmem
  refine ⟨r₀, ?_, ?_⟩
  · simpa [mem_sphere, dist_zero_right] using hr₀
  · intro x hx
    have hex : ∀ n, ∃ y, dist y x ≤ ε (φ n) ∧ f x = r (φ n) * g y := by
      intro n
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover (φ n) hx)
      have hfx : f x ∈ f '' C (φ n) j := ⟨x, hxj, rfl⟩
      rw [himages (φ n) j] at hfx
      obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := hfx
      exact ⟨y, hmesh (φ n) j y x hy hxj, hz.symm⟩
    choose y hy hxy using hex
    have hy_lim : Tendsto y atTop (𝓝 x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun _ => dist_nonneg) hy (hε.comp hφ.tendsto_atTop)
    have hprod : Tendsto (fun n => r (φ n) * g (y n)) atTop (𝓝 (r₀ * g x)) :=
      hlim.mul (hg.continuousAt.tendsto.comp hy_lim)
    exact tendsto_nhds_unique (tendsto_const_nhds.congr (fun n => hxy n)) hprod

end LatticeProb
