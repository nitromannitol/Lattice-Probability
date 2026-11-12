/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4L47kG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L47kN

/-!
# GM Lemma 4.7 at index `k`: the finite candidate set and the event `G` (DEC-89, packet B)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7, l. 1914–1936:
on `G = {𝓑^•_{t_k} ⊆ B_{(4λ₄ε)^{-M}𝕣}(𝕫), 𝕨 ∉ 𝓑^•_{t_k}}` (an event of `𝓕_k`), the pairs of
`𝒵_k` lie in the finite set of grid points within distance `(4λ₄ε)^{-M}𝕣 + 2λ₄ε𝕣 + 1` of `𝕫`,
times the radii `ℛ`.

* `gmCandFin`, `gm_gridPts_ball_finite`, `gm_gmL47G_measurableSet`, `gm_mem_gmCandFin`;
* `gm_h47_k`: GM (4.14) at index `k` (`gm_h47_k_core` + `gm_h47_count`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the grid points of `cℤ²` in `B_L(0)` form a finite set -/
theorem gm_gridPts_ball_finite {c L : ℝ} (hc : 0 < c) :
    {z : ℂ | z ∈ gridPts c ∧ ‖z‖ < L}.Finite := by
  set N : ℤ := ⌈L / c⌉
  refine ((((Finset.Icc (-N) N) ×ˢ (Finset.Icc (-N) N)).image
    (fun m : ℤ × ℤ => (⟨m.1 * c, m.2 * c⟩ : ℂ))).finite_toSet).subset ?_
  rintro z ⟨⟨a, b, rfl⟩, hz⟩
  simp only [Finset.coe_image, Finset.coe_product, Finset.coe_Icc, mem_image, mem_prod, mem_Icc]
  refine ⟨(a, b), ?_, rfl⟩
  have hre := Complex.abs_re_le_norm (⟨a * c, b * c⟩ : ℂ)
  have him := Complex.abs_im_le_norm (⟨a * c, b * c⟩ : ℂ)
  simp only at hre him
  rw [abs_mul, abs_of_pos hc] at hre him
  have hN : L / c ≤ (N : ℝ) := Int.le_ceil _
  rw [div_le_iff₀ hc] at hN
  have h1 : |(a : ℝ)| ≤ N := by
    by_contra h; push_neg at h; nlinarith
  have h2 : |(b : ℝ)| ≤ N := by
    by_contra h; push_neg at h; nlinarith
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  exact ⟨⟨by exact_mod_cast a1.1, by exact_mod_cast a1.2⟩,
    ⟨by exact_mod_cast a2.1, by exact_mod_cast a2.2⟩⟩

/-- the candidate pairs: grid points of `B_L(0)` times the radii `ℛ` -/
def gmCandSet (R : RegPar) (𝕣 ε L : ℝ) : Set (ℂ × ℝ) :=
  {z : ℂ | z ∈ gridPts (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ∧ ‖z‖ < L} ×ˢ p4Rads R 𝕣 ε

theorem gm_gmCandSet_finite (R : RegPar) {𝕣 ε : ℝ} (L : ℝ)
    (hc : 0 < R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) : (gmCandSet R 𝕣 ε L).Finite :=
  (gm_gridPts_ball_finite hc).prod ((Set.finite_Iio _).image _)

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

end LQGMetric.GM
