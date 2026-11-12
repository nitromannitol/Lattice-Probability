/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53X3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D125A
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Max

/-!
# P-131S (3): the coarse band `ĥ^1_c` on a box of side `≤ 1`, by a grid of boxes of side `2c`
(P2-DZZ53X)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 2537–2545 bound the band `ĥ^{s_i}_{a^{-1}}` on the
image box by a Gaussian sup estimate. In the coupling of P-131S (DEC-131 §3) the band is
`ĥ^1_c[W₁]` on the whole box `𝕍^ξ` (side `1 − 2ξ`) with `c = 2^{-m}/‖a‖ ∈ (0,1]` arbitrary.

Near miss adapted: `dzz_hat_sup_tail_raw` (S5D125A) is Fernique on one box `[x₀, x₀ + s]²`; its
constant `exp(((2s/c) C_F)²/…)` is useless for `s ≫ c`. Here the box is covered by the
`(⌈2s/c⌉ + 1)²` boxes of side `2c` centred at the grid points of `DG.exists_gridPt_near`
(S3L4Max), each with the constant `2 e^{8 C_F²}`, and a union bound gives
`P(sup |ĥ^1_c| ≥ λ) ≤ 16 c^{-2} · 2e^{8C_F²} · e^{−λ²/(4(log c^{-1} + 1))}` (own elementary
bookkeeping, as DEC-125 §1 "union over boxes").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise SupTail

/-- a point within `r` of `g` lies in the box of side `2r` centred at `g` -/
lemma mem_ferniqueBox_of_norm_le {z g : ℂ} {r : ℝ} (h : ‖z - g‖ ≤ r) :
    z ∈ ferniqueBox ⟨g.re - r, g.im - r⟩ (2 * r) := by
  have h1 : |z.re - g.re| ≤ ‖z - g‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : |z.im - g.im| ≤ ‖z - g‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have a1 := abs_le.1 (h1.trans h)
  have a2 := abs_le.1 (h2.trans h)
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **the coarse band on a box of side `s ≤ 1`, at any resolution `c ∈ (0, 1]`**: union of
`dzz_hat_sup_tail_raw` over a grid of boxes of side `2c`. -/
theorem hat_sup_tail_grid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {x₀ : ℂ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hY : ∀ x, Y x =ᵐ[P] phi W c 1 x) :
    ∀ lam : ℝ, 0 ≤ lam →
      P.real {ω | ∃ v ∈ ferniqueBox x₀ s, lam ≤ |Y v ω|} ≤
        16 * (c⁻¹) ^ 2 * (2 * Real.exp (8 * ferniqueCF ^ 2)) *
          Real.exp (-lam ^ 2 / (4 * (Real.log c⁻¹ + 1))) := by
  intro lam hlam
  have hP := hW.isProbabilityMeasure
  set m := ⌈2 * s / c⌉₊ with hm
  set g : Fin (m + 1) × Fin (m + 1) → ℂ := fun p => DG.gridPt x₀ s m p.1 p.2
  set Bx : Fin (m + 1) × Fin (m + 1) → Set ℂ := fun p =>
    ferniqueBox ⟨(g p).re - c, (g p).im - c⟩ (2 * c)
  set E : Fin (m + 1) × Fin (m + 1) → Set Ω := fun p =>
    {ω | lam ≤ ⨆ v : Bx p, |Y v ω|}
  have hsub : {ω | ∃ v ∈ ferniqueBox x₀ s, lam ≤ |Y v ω|} ⊆ ⋃ p, E p := by
    rintro ω ⟨v, hv, hl⟩
    obtain ⟨i, j, -, hij⟩ := DG.exists_gridPt_near hs hc hv
    have hvB : v ∈ Bx (i, j) := mem_ferniqueBox_of_norm_le hij
    have : CompactSpace (Bx (i, j)) := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox _ _)
    have hbdd : BddAbove (range fun u : Bx (i, j) => |Y u ω|) :=
      (isCompact_range (continuous_abs.comp ((hYc ω).comp continuous_subtype_val))).bddAbove
    exact mem_iUnion.2 ⟨(i, j), hl.trans (le_ciSup (f := fun u : Bx (i, j) => |Y u ω|) hbdd
      ⟨v, hvB⟩)⟩
  have hlog : 0 ≤ Real.log c⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hc, hc1⟩)
  set σ := Real.log (1 / c) + 1 with hσ
  have hσ' : σ = Real.log c⁻¹ + 1 := by rw [hσ, one_div]
  have hσ1 : 1 ≤ σ := by rw [hσ']; linarith
  have hone : ∀ p, P.real (E p) ≤ 2 * Real.exp (8 * ferniqueCF ^ 2) *
      Real.exp (-lam ^ 2 / (4 * (Real.log c⁻¹ + 1))) := fun p => by
    refine (dzz_hat_sup_tail_raw hW hc hc1 (x₀ := ⟨(g p).re - c, (g p).im - c⟩)
      (by positivity : (0 : ℝ) < 2 * c) hYc hY lam hlam).trans ?_
    rw [← hσ]
    have hM : (c / (2 * (2 * c)))⁻¹ * ferniqueCF = 4 * ferniqueCF := by field_simp; ring
    rw [hM, ← hσ', show 2 * (2 * σ) = 4 * σ by ring]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by norm_num)) (Real.exp_pos _).le
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ferniqueCF]
  have hcard : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 16 * (c⁻¹) ^ 2 := by
    have h1 : (m : ℝ) < 2 * s / c + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 2 * s / c ≤ 2 * c⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : (1 : ℝ) ≤ c⁻¹ := one_le_inv_iff₀.2 ⟨hc, hc1⟩
    push_cast
    nlinarith
  calc P.real {ω | ∃ v ∈ ferniqueBox x₀ s, lam ≤ |Y v ω|} ≤ P.real (⋃ p, E p) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ p, P.real (E p) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _p : Fin (m + 1) × Fin (m + 1), 2 * Real.exp (8 * ferniqueCF ^ 2) *
          Real.exp (-lam ^ 2 / (4 * (Real.log c⁻¹ + 1))) := Finset.sum_le_sum fun p _ => hone p
    _ = ((m + 1 : ℕ) : ℝ) ^ 2 * (2 * Real.exp (8 * ferniqueCF ^ 2) *
          Real.exp (-lam ^ 2 / (4 * (Real.log c⁻¹ + 1)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ 16 * (c⁻¹) ^ 2 * (2 * Real.exp (8 * ferniqueCF ^ 2) *
          Real.exp (-lam ^ 2 / (4 * (Real.log c⁻¹ + 1)))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end DZZ
end LQGMetric
