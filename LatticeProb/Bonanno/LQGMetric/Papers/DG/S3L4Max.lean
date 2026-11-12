/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L4Max at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax

/-!
# DG Lemma 3.5: the maximum of `ĥ_δ` (task P2-DG3A, WP-118)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.5 (`lem-one-scale-max`,
DG:1065–1070): "For `ζ ∈ (0,1)` and each bounded domain `U ⊂ ℂ`, it holds with polynomially
high probability as `δ → 0` that `max_{z∈U} |ĥ_δ(z)| ≤ (2+ζ) log δ⁻¹`."

DG's proof (DG:1071–1077), followed: each `ĥ_δ(z)` is a centred Gaussian of variance `log δ⁻¹`,
so a union bound over a grid of mesh `≍ δ` gives
`P[max_grid |ĥ_δ| ≤ (2 + ζ/2) log δ⁻¹] ≥ 1 − δ^{(2+ζ/2)²/2 − 2 + o(1)}`; combine with
Lemma 3.4 (`dg_lemma34`, with `ζ/2`) and the triangle inequality.

Bookkeeping (own): the grid is `x₀ + (s/m)(ℤ² ∩ [0,m]²)` in a square `ferniqueBox x₀ s ⊇ U`
(DG: `(δ/2)ℤ² ∩ U`; a point of `U` need not be `δ`-close to a grid point of `U`, so the square
is used), `m = ⌈2s/δ⌉`; the exponent obtained is `p = ζ` (DG: "polynomially", any `p > 0`;
`(2+ζ/2)²/2 − 2 = ζ + ζ²/8 ≥ ζ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DG

open WhiteNoise DZZ SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- one-point Gaussian tail of `ĥ_δ`: `P(|ĥ_δ(z)| ≥ y) ≤ 2 e^{−y²/(2 log δ⁻¹)}` -/
lemma phiVer_point_tail (hW : IsWhiteNoise P W) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (z : ℂ)
    {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | y ≤ |DDDF.phiVer W P δ 1 z ω|} ≤
      2 * Real.exp (-y ^ 2 / (2 * Real.log δ⁻¹)) := by
  have := hW.isProbabilityMeasure
  have hver := DDDF.isPhiVersion_phiVer hW hδ0 hδ1.le
  have hl := DDDF.hasLaw_phi hW δ 1 z
  have hv : ((Real.pi * ‖phiKernelL2 δ 1 z‖ ^ 2).toNNReal : ℝ) = Real.log δ⁻¹ := by
    rw [← variance_phi_delta hW hδ0 hδ1.le z, hl.variance_eq, variance_id_gaussianReal]
  have hL : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ0).2 hδ1)
  have h := DDDF.tail_abs_of_hasLaw (by rw [hv]; exact hL) (hl.congr (hver.ae_eq z)) hy
  rwa [hv] at h

/-- `i = ⌊r/h⌋` is an index in `[0, m]` with `i h ≤ r < (i+1) h` -/
lemma exists_floor_idx {r h : ℝ} (m : ℕ) (hh : 0 < h) (hr0 : 0 ≤ r) (hr : r ≤ m * h) :
    ∃ i : Fin (m + 1), (i : ℝ) * h ≤ r ∧ r - i * h ≤ h := by
  have hq : 0 ≤ r / h := div_nonneg hr0 hh.le
  have hqm : r / h ≤ m := (div_le_iff₀ hh).2 hr
  refine ⟨⟨⌊r / h⌋₊, Nat.lt_succ_of_le ?_⟩, ?_, ?_⟩
  · exact (Nat.floor_le_floor hqm).trans (Nat.floor_natCast m).le
  · have := Nat.floor_le hq
    simp only
    rwa [le_div_iff₀ hh] at this
  · have := Nat.lt_floor_add_one (r / h)
    simp only
    rw [div_lt_iff₀ hh] at this
    linarith

/-- the grid point `x₀ + (s/m)(i + j i)` -/
def gridPt (x₀ : ℂ) (s : ℝ) (m : ℕ) (i j : Fin (m + 1)) : ℂ :=
  x₀ + ⟨s / m * i, s / m * j⟩

/-- every point of `ferniqueBox x₀ s` is within `δ` of a grid point of mesh `s/⌈2s/δ⌉ ≤ δ/2`
lying in the square -/
lemma exists_gridPt_near {x₀ z : ℂ} {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hz : z ∈ ferniqueBox x₀ s) :
    ∃ i j : Fin (⌈2 * s / δ⌉₊ + 1), gridPt x₀ s ⌈2 * s / δ⌉₊ i j ∈ ferniqueBox x₀ s ∧
      ‖z - gridPt x₀ s ⌈2 * s / δ⌉₊ i j‖ ≤ δ := by
  set m := ⌈2 * s / δ⌉₊
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.ceil_pos.2 (by positivity))
  set h := s / m
  have hh : 0 < h := div_pos hs hm
  have hmh : (m : ℝ) * h = s := by simp only [h]; field_simp
  have hhδ : h ≤ δ / 2 := by
    have := Nat.le_ceil (2 * s / δ)
    simp only [h]
    rw [div_le_iff₀ hm]
    rw [div_le_iff₀ hδ] at this
    linarith
  rw [mem_ferniqueBox_iff] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨i, hi1, hi2⟩ := exists_floor_idx (r := z.re - x₀.re) m hh (by linarith)
    (by rw [hmh]; linarith)
  obtain ⟨j, hj1, hj2⟩ := exists_floor_idx (r := z.im - x₀.im) m hh (by linarith)
    (by rw [hmh]; linarith)
  have hi : (i : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.2
  have hj : (j : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ j.2
  refine ⟨i, j, ?_, ?_⟩
  · rw [mem_ferniqueBox_iff]
    simp only [gridPt, Complex.add_re, Complex.add_im]
    have hi' : h * i ≤ s := by rw [← hmh]; nlinarith
    have hj' : h * j ≤ s := by rw [← hmh]; nlinarith
    refine ⟨by nlinarith, by linarith, by nlinarith, by linarith⟩
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [gridPt, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
    have e1 : z.re - (x₀.re + h * i) = z.re - x₀.re - i * h := by ring
    have e2 : z.im - (x₀.im + h * j) = z.im - x₀.im - j * h := by ring
    rw [e1, e2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- **DG Lemma 3.5** (`lem-one-scale-max`, DG:1065–1070): for `ζ > 0` and bounded `U`, with
polynomially high probability (exponent `ζ`) as `δ → 0`, `max_{z∈U} |ĥ_δ(z)| ≤ (2+ζ) log δ⁻¹`. -/
theorem dg_lemma35 (hW : IsWhiteNoise P W) {U : Set ℂ} (hU : Bornology.IsBounded U) {ζ : ℝ}
    (hζ : 0 < ζ) :
    ∃ K δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ∃ z ∈ U, (2 + ζ) * Real.log δ⁻¹ < |DDDF.phiVer W P δ 1 z ω|} ≤
        ENNReal.ofReal (K * δ ^ ζ) := by
  have := hW.isProbabilityMeasure
  obtain ⟨x₀, s, hs1, hUs⟩ := exists_box_of_isBounded hU
  have hs : 0 < s := by linarith
  obtain ⟨δ₁, hδ₁, h34⟩ := dg_lemma34 hW (isCompact_ferniqueBox x₀ s).isBounded
    (half_pos hζ) hζ
  refine ⟨2 * (2 * s + 2) ^ 2 + 1, min δ₁ (1 / 2), lt_min hδ₁ (by norm_num), fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδδ₁ : δ < δ₁ := hδ.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 := (hδ.trans_le (min_le_right _ _)).trans (by norm_num)
  set L := Real.log δ⁻¹ with hL_def
  have hL : 0 < L := Real.log_pos ((one_lt_inv₀ hδ0).2 hδ1)
  set m := ⌈2 * s / δ⌉₊
  set Y := DDDF.phiVer W P δ 1
  set E : Fin (m + 1) × Fin (m + 1) → Set Ω :=
    fun ij => {ω | (2 + ζ / 2) * L ≤ |Y (gridPt x₀ s m ij.1 ij.2) ω|}
  set F := {ω | ∃ z ∈ ferniqueBox x₀ s, ∃ w ∈ ferniqueBox x₀ s, ‖z - w‖ ≤ δ ∧
        ζ / 2 * L < |Y z ω - Y w ω|}
  have hsub : {ω | ∃ z ∈ U, (2 + ζ) * L < |Y z ω|} ⊆ (⋃ ij, E ij) ∪ F := by
    rintro ω ⟨z, hz, hlt⟩
    obtain ⟨i, j, hg, hzg⟩ := exists_gridPt_near hs hδ0 (hUs hz)
    by_cases hE : (2 + ζ / 2) * L ≤ |Y (gridPt x₀ s m i j) ω|
    · exact Or.inl (mem_iUnion.2 ⟨(i, j), hE⟩)
    · refine Or.inr ⟨z, hUs hz, _, hg, hzg, ?_⟩
      have := abs_sub_abs_le_abs_sub (Y z ω) (Y (gridPt x₀ s m i j) ω)
      push Not at hE
      linarith
  -- the grid term
  have hy : 0 ≤ (2 + ζ / 2) * L := by positivity
  have hEi : ∀ ij, P (E ij) ≤ ENNReal.ofReal (2 * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2)) := by
    intro ij
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ((phiVer_point_tail hW hδ0 hδ1 _ hy).trans (le_of_eq ?_))
    congr 2
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    ring
  have hm1 : ((m : ℝ) + 1) ≤ (2 * s + 2) * δ⁻¹ := by
    have hc : (m : ℝ) < 2 * s / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : 1 ≤ δ⁻¹ := one_le_inv_iff₀.2 ⟨hδ0, hδ1.le⟩
    have e : 2 * s / δ = 2 * s * δ⁻¹ := div_eq_mul_inv _ _
    rw [e] at hc
    nlinarith
  have hexpL : Real.exp L = δ⁻¹ := Real.exp_log (inv_pos.2 hδ0)
  have hpow : δ ^ ζ = Real.exp (-(ζ * L)) := by
    rw [Real.rpow_def_of_pos hδ0, hL_def, Real.log_inv]; ring_nf
  have hgrid : ((m : ℝ) + 1) ^ 2 * (2 * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2)) ≤
      2 * (2 * s + 2) ^ 2 * δ ^ ζ := by
    have h1 : ((m : ℝ) + 1) ^ 2 ≤ (2 * s + 2) ^ 2 * Real.exp (2 * L) := by
      rw [show 2 * L = L + L by ring, Real.exp_add, hexpL]
      nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) hm1 2]
    have h2 : Real.exp (2 * L) * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2) ≤ Real.exp (-(ζ * L)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg ζ]
    rw [hpow]
    calc ((m : ℝ) + 1) ^ 2 * (2 * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2))
        ≤ (2 * s + 2) ^ 2 * Real.exp (2 * L) * (2 * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * (2 * s + 2) ^ 2 *
          (Real.exp (2 * L) * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2)) := by ring
      _ ≤ 2 * (2 * s + 2) ^ 2 * Real.exp (-(ζ * L)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hF : P F ≤ ENNReal.ofReal (δ ^ ζ) := h34 δ ⟨hδ0, hδδ₁⟩
  calc P {ω | ∃ z ∈ U, (2 + ζ) * L < |Y z ω|} ≤ P ((⋃ ij, E ij) ∪ F) := measure_mono hsub
    _ ≤ ∑ ij, P (E ij) + P F := (measure_union_le _ _).trans
        (add_le_add (measure_iUnion_fintype_le _ _) le_rfl)
    _ ≤ ∑ _ij : Fin (m + 1) × Fin (m + 1),
          ENNReal.ofReal (2 * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2)) + ENNReal.ofReal (δ ^ ζ) :=
        add_le_add (Finset.sum_le_sum fun ij _ => hEi ij) hF
    _ = ENNReal.ofReal (((m : ℝ) + 1) ^ 2 * (2 * Real.exp (-((2 + ζ / 2) ^ 2 * L) / 2)) +
          δ ^ ζ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal ((2 * (2 * s + 2) ^ 2 + 1) * δ ^ ζ) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith

end DG
end LQGMetric
