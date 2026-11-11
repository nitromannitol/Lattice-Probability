import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Removing a point from a connected open set

Removing one point from a connected open subset of a real normed space of dimension at least two leaves it connected.
This is classical plane topology (cf. Newman, *Elements of the Topology of Plane Sets of Points*); in the plane it is the
case `E = ℂ`, where `Module.rank ℝ ℂ = 2`. The punctured ball is the image of `(0, r) × S¹` under `(ρ, e) ↦ z + ρ • e`.
-/

open Metric Set

namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dist_add_smul_eq_of_norm_eq_one (z e : E) {ρ : ℝ} (hρ : 0 ≤ ρ) (he : ‖e‖ = 1) :
    dist (z + ρ • e) z = ρ := by
  simp [dist_eq_norm, norm_smul, he, Real.norm_of_nonneg hρ]

lemma add_smul_mem_ball_diff_singleton (z : E) {r ρ : ℝ} (e : E) (hρ0 : 0 < ρ) (hρr : ρ < r)
    (he : e ∈ sphere (0 : E) 1) : z + ρ • e ∈ ball z r \ {z} := by
  have he' : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp he
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_add_smul_eq_of_norm_eq_one z e hρ0.le he']
    exact hρr
  · intro hz
    have hne : ρ • e ≠ 0 := smul_ne_zero hρ0.ne' (fun h0 => by rw [h0, norm_zero] at he'; exact zero_ne_one he')
    apply hne
    simpa using hz

lemma ball_diff_singleton_eq_image (z : E) (r : ℝ) :
    ball z r \ {z} = (fun p : ℝ × E => z + p.1 • p.2) '' (Ioo 0 r ×ˢ sphere (0 : E) 1) := by
  ext w
  constructor
  · rintro ⟨hwB, hwz⟩
    have hne : w - z ≠ 0 := sub_ne_zero.mpr hwz
    have hpos : 0 < ‖w - z‖ := norm_pos_iff.mpr hne
    refine ⟨(‖w - z‖, ‖w - z‖⁻¹ • (w - z)), ⟨⟨hpos, ?_⟩, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm] at hwB
      exact hwB
    · rw [mem_sphere_zero_iff_norm]
      exact norm_smul_inv_norm hne
    · show z + ‖w - z‖ • (‖w - z‖⁻¹ • (w - z)) = w
      rw [smul_inv_smul₀ hpos.ne']
      abel
  · rintro ⟨⟨ρ, e⟩, ⟨⟨hρ0, hρr⟩, he⟩, rfl⟩
    exact add_smul_mem_ball_diff_singleton z e hρ0 hρr he

/-- The punctured ball `ball z r \ {z}` is connected when `1 < Module.rank ℝ E`. -/
lemma isPreconnected_ball_diff_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) (z : E) (r : ℝ) :
    IsPreconnected (ball z r \ {z}) := by
  rw [ball_diff_singleton_eq_image]
  exact (isPreconnected_Ioo.prod (isConnected_sphere h 0 zero_le_one).isPreconnected).image _
    (continuous_const.add (continuous_fst.smul continuous_snd)).continuousOn

/-- Removing a point from a connected open subset of a real normed space with `1 < Module.rank ℝ E` leaves it
connected (classical plane topology). -/
theorem isConnected_diff_singleton_of_one_lt_rank (h : 1 < Module.rank ℝ E) {U : Set E} (hU : IsOpen U)
    (hc : IsConnected U) (z : E) : IsConnected (U \ {z}) := by
  by_cases hzU : z ∈ U
  swap
  · rw [sdiff_singleton_eq_self hzU]
    exact hc
  obtain ⟨r, hr, hBU⟩ := Metric.isOpen_iff.mp hU z hzU
  have hsph : (sphere (0 : E) 1).Nonempty := (isConnected_sphere h 0 zero_le_one).nonempty
  obtain ⟨e₀, he₀⟩ := hsph
  have hWconn : IsPreconnected (ball z r \ {z}) := isPreconnected_ball_diff_singleton_of_one_lt_rank h z r
  have hWsub : ball z r \ {z} ⊆ U \ {z} := sdiff_subset_sdiff_left hBU
  have hWne : (ball z r \ {z}).Nonempty :=
    ⟨z + (r / 2) • e₀, add_smul_mem_ball_diff_singleton z e₀ (by linarith) (by linarith) he₀⟩
  refine ⟨hWne.mono hWsub, ?_⟩
  intro p q hp hq hcov hpne hqne
  by_contra hno
  have hdisj : ∀ x ∈ U \ {z}, x ∈ p → x ∉ q := fun x hx hxp hxq => hno ⟨x, hx, hxp, hxq⟩
  -- the separation step: if the punctured ball misses `p'`, then `U` splits, a contradiction
  have key : ∀ p' q' : Set E, IsOpen p' → IsOpen q' → U \ {z} ⊆ p' ∪ q' →
      (∀ x ∈ U \ {z}, x ∈ p' → x ∉ q') → (U \ {z} ∩ p').Nonempty → (U \ {z} ∩ q').Nonempty →
      (ball z r \ {z}) ∩ p' = ∅ → False := by
    intro p' q' hp' hq' hcov' hdisj' hpne' hqne' hWp'
    have hzp' : z ∉ p' := by
      intro hzp'
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hp'.inter isOpen_ball) z ⟨hzp', mem_ball_self hr⟩
      have hδ : 0 < min ε r / 2 := half_pos (lt_min hε hr)
      have hδε : min ε r / 2 < ε := by linarith [min_le_left ε r]
      have hδr : min ε r / 2 < r := by linarith [min_le_right ε r]
      have hmemW := add_smul_mem_ball_diff_singleton z e₀ hδ hδr he₀
      have hmemball : z + (min ε r / 2) • e₀ ∈ ball z ε := by
        rw [mem_ball, dist_add_smul_eq_of_norm_eq_one z e₀ hδ.le (mem_sphere_zero_iff_norm.mp he₀)]
        exact hδε
      have hin := hball hmemball
      have hmem : z + (min ε r / 2) • e₀ ∈ (ball z r \ {z}) ∩ p' := ⟨hmemW, hin.1⟩
      rw [hWp'] at hmem; simp at hmem
    have hcover : U ⊆ p' ∪ (q' ∪ ball z r) := by
      intro x hx
      by_cases hxz : x = z
      · exact Or.inr (Or.inr (by rw [hxz]; exact mem_ball_self hr))
      · rcases hcov' ⟨hx, hxz⟩ with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
    obtain ⟨x₁, hx₁U, hx₁p⟩ := hpne'
    obtain ⟨x₂, hx₂U, hx₂q⟩ := hqne'
    have hconn := hc.isPreconnected p' (q' ∪ ball z r) hp' (hq'.union isOpen_ball) hcover
      ⟨x₁, hx₁U.1, hx₁p⟩ ⟨x₂, hx₂U.1, Or.inl hx₂q⟩
    obtain ⟨x, hxU, hxp', hxqb⟩ := hconn
    by_cases hxz : x = z
    · exact hzp' (hxz ▸ hxp')
    · rcases hxqb with hxq' | hxb
      · exact hdisj' x ⟨hxU, hxz⟩ hxp' hxq'
      · have hmem : x ∈ (ball z r \ {z}) ∩ p' := ⟨⟨hxb, hxz⟩, hxp'⟩
        rw [hWp'] at hmem; simp at hmem
  have hWcov : ball z r \ {z} ⊆ p ∪ q := fun x hx => hcov (hWsub hx)
  by_cases hWp : (ball z r \ {z}) ∩ p = ∅
  · exact key p q hp hq hcov hdisj hpne hqne hWp
  · by_cases hWq : (ball z r \ {z}) ∩ q = ∅
    · exact key q p hq hp (fun x hx => Or.symm (hcov hx)) (fun x hx hxq hxp => hdisj x hx hxp hxq)
        hqne hpne hWq
    · obtain ⟨w, hwW, hwp, hwq⟩ := hWconn p q hp hq hWcov (Set.nonempty_iff_ne_empty.mpr hWp)
        (Set.nonempty_iff_ne_empty.mpr hWq)
      exact hdisj w (hWsub hwW) hwp hwq

/-- **Complement of a point in a connected open planar set.** For an open connected `U ⊆ ℂ` and any `z`, `U \ {z}` is
connected (classical plane topology; Newman, *Elements of the Topology of Plane Sets of Points*). -/
theorem IsOpen.isConnected_diff_singleton {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) (z : ℂ) :
    IsConnected (U \ {z}) :=
  isConnected_diff_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) hU hc z

end LatticeProb
