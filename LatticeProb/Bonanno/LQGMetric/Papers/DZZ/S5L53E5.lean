/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53E5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E4

/-!
# DZZ Lemma 5.3, part 1: a desirable cell from open-box chains (P2-DZZ53E)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`. A cell `𝖢_i` is desirable "similar to
(eq-par)" (l. 2512–2514). In the heat-kernel proof, on the percolation event `𝒜` (l. 1927) the
segments `L ∈ 𝕃'` of `Λ_{i−1}` connected to `𝕃` by neighbouring good boxes cover
`𝓛₁(Λ') ≥ 0.2 𝓛₁(Λ_{i−1})`. Removing from each such `L` its bad points (measure `≤ a` each) leaves
`≥ 0.1 𝓛₁(Λ_{i−1})` ((Eq.measure-of-Lambda-prime), l. 1946–1952). Here is the LGD analogue.

* **`l53_desirable_of_chains`**: given finitely many segments `L ι ⊆ Λ_{i−1}`, each with a start
  point `z₀ ι` whose bad set in `L ι` has `𝓛₁ ≤ a`, and a chain of at most `N` pieces of
  `lgdLeExp δ T` from `z₀ ι` to `Λ_end` (the output of `l53_open_chain`), with
  `0.2 𝓛₁(Λ_{i−1}) ≤ 𝓛₁(⋃ L)` and `#F · a ≤ 0.1 𝓛₁(Λ_{i−1})`, the set `Λ_start` of the good points
  has `𝓛₁ ≥ 0.1 𝓛₁(Λ_{i−1})`. Each of its points is at `D_δ`-distance `≤ e^{T + log (N+1)}` from
  `Λ_end`. This is exactly the conclusion required of `𝖢_i` in `l53DesirableEvent`, with
  `T' = T + log (N+1)`. DZZ: `N ≤ K²`, `log (K²+1) ≤ (log δ⁻¹)^{0.98}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal MeasureTheory

namespace LQGMetric
namespace DZZ

/-- **A desirable cell from open-box chains** (LGD analogue of DZZ l. 1946–1952). -/
theorem l53_desirable_of_chains (ν : Measure ℂ) (μ : Measure ℂ) {δ T a : ℝ} {N : ℕ}
    {Λ Λend : Set ℂ} (hΛ : ν Λ ≠ ⊤) {ι : Type*} (F : Finset ι) (L : ι → Set ℂ) (z₀ : ι → ℂ)
    (hL : ∀ j ∈ F, L j ⊆ Λ)
    (hbad : ∀ j ∈ F, ν.real {x ∈ L j | ¬ lgdLeExp μ δ T (z₀ j) x} ≤ a)
    (hchain : ∀ j ∈ F, ∃ n ≤ N, ∃ y : ℕ → ℂ, y 0 = z₀ j ∧ y n ∈ Λend ∧
      ∀ k < n, lgdLeExp μ δ T (y (k + 1)) (y k))
    (hcov : 0.2 * ν.real Λ ≤ ν.real (⋃ j ∈ F, L j)) (hcard : (F.card : ℝ) * a ≤ 0.1 * ν.real Λ) :
    ∃ S ⊆ Λ, 0.1 * ν.real Λ ≤ ν.real S ∧
      ∀ x ∈ S, ∃ x' ∈ Λend, lgdLeExp μ δ (T + Real.log (N + 1)) x x' := by
  set S : Set ℂ := ⋃ j ∈ F, {x ∈ L j | lgdLeExp μ δ T (z₀ j) x} with hS
  set B : Set ℂ := ⋃ j ∈ F, {x ∈ L j | ¬ lgdLeExp μ δ T (z₀ j) x} with hB
  have hSΛ : S ⊆ Λ := by
    intro x hx
    simp only [hS, mem_iUnion] at hx
    obtain ⟨j, hj, hx, -⟩ := hx
    exact hL j hj hx
  have hBΛ : B ⊆ Λ := by
    intro x hx
    simp only [hB, mem_iUnion] at hx
    obtain ⟨j, hj, hx, -⟩ := hx
    exact hL j hj hx
  have hsub : (⋃ j ∈ F, L j) ⊆ S ∪ B := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨j, hj, hx⟩ := hx
    by_cases h : lgdLeExp μ δ T (z₀ j) x
    · exact Or.inl (mem_biUnion hj ⟨hx, h⟩)
    · exact Or.inr (mem_biUnion hj ⟨hx, h⟩)
  have hSBf : ν (S ∪ B) ≠ ⊤ := ne_top_of_le_ne_top hΛ (measure_mono (union_subset hSΛ hBΛ))
  have h1 : ν.real (⋃ j ∈ F, L j) ≤ ν.real S + ν.real B :=
    (measureReal_mono hsub hSBf).trans (measureReal_union_le _ _)
  have h2 : ν.real B ≤ F.card * a := by
    refine (measureReal_biUnion_finset_le F _).trans ?_
    calc ∑ j ∈ F, ν.real {x ∈ L j | ¬ lgdLeExp μ δ T (z₀ j) x} ≤ ∑ _j ∈ F, a :=
          Finset.sum_le_sum hbad
      _ = F.card * a := by rw [Finset.sum_const, nsmul_eq_mul]
  refine ⟨S, hSΛ, by linarith, fun x hx => ?_⟩
  simp only [hS, mem_iUnion] at hx
  obtain ⟨j, hj, -, hxR⟩ := hx
  obtain ⟨n, hnN, y, hy0, hyn, hyR⟩ := hchain j hj
  obtain ⟨hfin, hle⟩ := lgdLeExp_chain μ y (by rw [hy0]; exact hxR) hyR
  refine ⟨y n, hyn, hfin, hle.trans ?_⟩
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  rw [Real.exp_add, Real.exp_log hN1, mul_comm]
  gcongr

end DZZ
end LQGMetric
