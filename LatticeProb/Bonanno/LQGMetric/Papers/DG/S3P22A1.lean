/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22A1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22Grid
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L21R

/-!
# DG Proposition 3.22 assembly, part 1: the `𝕍`-scale cells of Lemma 3.21 (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Proposition 3.22
(DG:1739–1771) at `𝕍`-scale (DV-D105-3): the cells are the squares `S = l321In δ_ε (2^{-M}x) 1`
of side `δ_ε = 2^{-M_ε}` of Lemma 3.21 (grid anchored at `0`, so `S = gridSq δ_ε x`,
`S(1) = l321Out … = gridSqOne δ_ε x`), the domain is a closed convex `U` covered by the cells.
`dgP322Hyp_l321` turns the event of Lemma 3.21 ((eqn-square-dist), DG:1684–1687) and the mass
condition of (eqn-lfpp-lower-event) (DG:1741) into `DGP322Hyp`; `p322a_good_l321` then applies
`dg_prop322_det` (DG:1745–1771) to a pair `z, w` with `D^ε(z,w;U) ≤ N` (from Prop. 3.9).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

lemma l321In_zero (M : ℕ) (x : ℕ × ℕ) :
    l321In ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M x) 1 = gridSq ((2 : ℝ)⁻¹ ^ M) ((x.1 : ℤ), (x.2 : ℤ)) := by
  simp only [l321In, l313Corner, gridSq, Complex.zero_re, Complex.zero_im, zero_add,
    Nat.cast_one, mul_one, Int.cast_natCast]
  congr 1 <;> congr 1 <;> ring

lemma l321Out_zero (M : ℕ) (x : ℕ × ℕ) :
    l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M x) 1 =
      gridSqOne ((2 : ℝ)⁻¹ ^ M) ((x.1 : ℤ), (x.2 : ℤ)) := by
  simp only [l321Out, l313Corner, gridSqOne, Complex.zero_re, Complex.zero_im, zero_add,
    Nat.cast_one, mul_one, Int.cast_natCast]
  congr 1 <;> congr 1 <;> ring

lemma p322a_mono_univ {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ} (z w : ℂ) :
    dgLGD μ ε univ z w ≤ dgLGD μ ε U z w := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, h1, h2⟩ := hN
  exact iInf₂_le N ⟨x, ρ, P, fun i => ⟨(h1 i).1, by simp, (h1 i).2.2⟩, h2⟩

/-- **the `𝕍`-scale cell instance of `DGP322Hyp`** (DG:1739–1756): for the cells of a finite
index set `Λ` of the Lemma 3.21 grid at level `M` covering the closed convex domain `U`. -/
theorem dgP322Hyp_l321 {μ : Measure ℂ} {ε L ξ Mx : ℝ} {φ : ℂ → ℝ} {U : Set ℂ} {M : ℕ}
    {Λ : Finset (ℕ × ℕ)} (hUc : IsClosed U) (hUv : Convex ℝ U) (hφ : Continuous φ)
    (hξ : 0 ≤ ξ) (hL : 0 < L)
    (hcell : ∀ x ∈ U, ∃ i ∈ Λ, x ∈ l321In ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1)
    (hmax : ∀ i ∈ Λ, ∀ v ∈ l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1, φ v ≤ Mx)
    (hcross : ∀ i ∈ Λ, ENNReal.ofReal (L * Real.exp (ξ * sSup (φ ''
        l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1))) ≤
      (l313Set μ ε univ (l321In ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1)
        (frontier (l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1)) : ℝ≥0∞))
    (hmass : ∀ c ∈ U, ENNReal.ofReal ε < μ (ball c ((2 : ℝ)⁻¹ ^ M / 2))) :
    DGP322Hyp μ ε U (fun i : Λ => l321In ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1)
      (fun i : Λ => l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1) ((2 : ℝ)⁻¹ ^ M)
      (3 * Real.sqrt 2 * (2 : ℝ)⁻¹ ^ M) L ξ Mx φ := by
  have ha : 0 < (2 : ℝ)⁻¹ ^ M := by positivity
  exact
  { convex := by rw [hUc.closure_eq]; exact hUv
    cont := hφ
    xi_nonneg := hξ
    L_pos := hL
    A_nonneg := by positivity
    cell := fun x hx => by
      rw [hUc.closure_eq] at hx
      obtain ⟨i, hi, hx'⟩ := hcell x hx
      exact ⟨⟨i, hi⟩, hx'⟩
    sub := fun i => by rw [l321In_zero, l321Out_zero]; exact gridSq_subset_interior ha _
    conv := fun i => by rw [l321Out_zero]; exact convex_gridSqOne _ _
    closed := fun i => by rw [l321Out_zero]; exact isClosed_gridSqOne _ _
    sep := fun i => by rw [l321In_zero, l321Out_zero]; exact gridSq_sep ha _
    diam := fun i => by rw [l321Out_zero]; exact gridSqOne_diam ha _
    max := fun i => hmax i i.2
    cross := fun i x hx y hy v hv => by
      have hcpt : IsCompact (l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1) :=
        isCompact_Icc.reProdIm isCompact_Icc
      have hle : φ v ≤ sSup (φ '' l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1) :=
        le_csSup (hcpt.image hφ).bddAbove ⟨v, hv, rfl⟩
      refine le_trans ?_ ((hcross i i.2).trans ?_)
      · apply ENNReal.ofReal_le_ofReal
        gcongr
      · refine ENat.toENNReal_le.2 ((iInf₂_le x hx).trans ((iInf₂_le y hy).trans ?_))
        exact p322a_mono_univ x y
    mass := fun c hc => by rw [hUc.closure_eq] at hc; exact hmass c hc }

/-- **DG Proposition 3.22 on the good event** (DG:1739–1771): if moreover `D^ε(z,w;U) ≤ N`,
then `D^{LFPP}_φ(z,w;U) ≤ 3√2 δ_ε (2N/L + e^{ξ Mx})`. -/
theorem p322a_good_l321 {μ : Measure ℂ} {ε L ξ Mx : ℝ} {φ : ℂ → ℝ} {U : Set ℂ} {M : ℕ}
    {Λ : Finset (ℕ × ℕ)} (hUc : IsClosed U) (hUv : Convex ℝ U) (hφ : Continuous φ)
    (hξ : 0 ≤ ξ) (hL : 0 < L)
    (hcell : ∀ x ∈ U, ∃ i ∈ Λ, x ∈ l321In ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1)
    (hmax : ∀ i ∈ Λ, ∀ v ∈ l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1, φ v ≤ Mx)
    (hcross : ∀ i ∈ Λ, ENNReal.ofReal (L * Real.exp (ξ * sSup (φ ''
        l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1))) ≤
      (l313Set μ ε univ (l321In ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1)
        (frontier (l321Out ((2 : ℝ)⁻¹ ^ M) (l313Corner 0 M i) 1)) : ℝ≥0∞))
    (hmass : ∀ c ∈ U, ENNReal.ofReal ε < μ (ball c ((2 : ℝ)⁻¹ ^ M / 2)))
    {z w : ℂ} {N : ℕ} (hN : dgLGD μ ε U z w ≤ N) :
    dgLFPP ξ φ U z w ≤ 3 * Real.sqrt 2 * (2 : ℝ)⁻¹ ^ M * (2 * N / L + Real.exp (ξ * Mx)) := by
  have h := dg_prop322_det (dgP322Hyp_l321 hUc hUv hφ hξ hL hcell hmax hcross hmass) hN
  rwa [hUc.closure_eq] at h

end DG
end LQGMetric
