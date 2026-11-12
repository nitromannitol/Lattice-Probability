/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_20SqMain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Sq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.20 (`Blueprint.DFGPSLem3_20`) from Lemma 3.19 (task P2-DFA7)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.20 (T:2317–2325) and
its proof (T:2327–2330). Second display: Lemma 3.19's square estimate (`eqn-ep-diam-square`) with
`s = (χ + ξ(Q−2))/2` for every open dyadic square of side `ε2^{-ℓ}𝕣` with corner in
`ε2^{-ℓ}𝕣ℤ²` near `𝕣K`, a union bound over these squares and `ℓ` (`grid_union_bound`), and the
nested-squares chain `sq_det` for the closed squares of the statement; the slack `s > χ` absorbs
the factor `2/(1 − 2^{-s})` for small `ε` (DFA7-2).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L320

open Blueprint Complex LQGDimension.LFPPRecords

lemma sqCentred_eq_osq {σ : ℝ} (hσ : 0 < σ) (p : ℂ) :
    sqCentred σ (p + ((σ / 2 : ℝ) : ℂ) * (1 + I)) = osq σ p := by
  ext y
  simp only [sqCentred, scaleSet, mem_image, osq, mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [add_sub_cancel_right, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
      zero_mul, sub_zero, add_zero]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(y - p) / σ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [div_ofReal_re, sub_re]; exact div_pos (by linarith) hσ
    · rw [div_ofReal_re, sub_re, div_lt_one hσ]; linarith
    · rw [div_ofReal_im, sub_im]; exact div_pos (by linarith) hσ
    · rw [div_ofReal_im, sub_im, div_lt_one hσ]; linarith
    · have : (σ : ℂ) ≠ 0 := ofReal_ne_zero.2 hσ.ne'
      simp only [add_sub_cancel_right]; field_simp; ring

lemma gridSquare_eq_csq (σ : ℝ) (m : ℤ × ℤ) : gridSquare σ m = csq σ (gridPt σ m) := by
  ext x
  simp only [gridSquare, csq, gridPt, mem_setOf_eq]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨by linarith, by linarith, by linarith,
    by linarith⟩

lemma gridPt_sub (t 𝕣 : ℝ) (k j : ℕ) (m : ℤ × ℤ) (n1 n2 : ℤ) :
    gridPt (1 * (t * (1 / 2) ^ (k + j)) * 𝕣) ((2 : ℤ) ^ j * m.1 + n1, (2 : ℤ) ^ j * m.2 + n2) =
      gridPt (t * (1 / 2) ^ k * 𝕣) m + ((t * (1 / 2) ^ k * 𝕣 * (1 / 2) ^ j : ℝ) : ℂ) *
        (((n1 : ℝ) : ℂ) + ((n2 : ℝ) : ℂ) * I) := by
  have hp : (2 : ℝ) ^ j * 2⁻¹ ^ j = 1 := by rw [← mul_pow]; norm_num
  apply Complex.ext
  · simp only [gridPt, one_div, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      sub_zero, zero_mul, mul_one, add_zero, pow_add]
    push_cast
    linear_combination (t * 2⁻¹ ^ k * 𝕣) * (m.1 : ℝ) * hp
  · simp only [gridPt, one_div, add_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, zero_mul, mul_one, add_zero, zero_add, pow_add]
    push_cast
    linear_combination (t * 2⁻¹ ^ k * 𝕣) * (m.2 : ℝ) * hp

/-- the second display of `Blueprint.DFGPSLem3_20` (`eqn-holder-upper-square`) -/
def Lem3_20Sq : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (K : Set ℂ), IsCompact K → ∀ χ : ℝ, 0 < χ → χ < xiGamma γ * (Q γ - 2) →
      PolyHighProbU (fun ε 𝕣 => {g : DistC |
        ∀ (k : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m ∩ scaleSet 𝕣 0 K).Nonempty →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0)) *
              internalDiam (D g) (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m)
                (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m) ≤
            ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k * ε) ^ χ)})

lemma half_pow_rpow (j : ℕ) (s : ℝ) : (((1 : ℝ) / 2) ^ j) ^ s = (((1 : ℝ) / 2) ^ s) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

lemma corner_norm_le {σ 𝕣 R : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 𝕣) {c w : ℂ} {j : ℕ} {n1 n2 : ℤ}
    (hn10 : 0 ≤ (n1 : ℝ)) (hn11 : (n1 : ℝ) + 1 ≤ 2 ^ j) (hn20 : 0 ≤ (n2 : ℝ))
    (hn21 : (n2 : ℝ) + 1 ≤ 2 ^ j) (hw : w ∈ csq σ c) (hwR : ‖w‖ + 2 * 𝕣 ≤ R * 𝕣) :
    ‖c + ((σ * (1 / 2) ^ j : ℝ) : ℂ) * (((n1 : ℝ) : ℂ) + ((n2 : ℝ) : ℂ) * I)‖ ≤ R * 𝕣 := by
  obtain ⟨w1, w2, w3, w4⟩ := hw
  have hpj : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
  have hq0 : (0 : ℝ) < (1 / 2) ^ j := by positivity
  set p := c + ((σ * (1 / 2) ^ j : ℝ) : ℂ) * (((n1 : ℝ) : ℂ) + ((n2 : ℝ) : ℂ) * I) with hp
  have hpre : p.re = c.re + σ * (1 / 2) ^ j * n1 := re_aux _ _ _ _
  have hpim : p.im = c.im + σ * (1 / 2) ^ j * n2 := im_aux _ _ _ _
  have bnd : ∀ n : ℝ, 0 ≤ n → n + 1 ≤ 2 ^ j → 0 ≤ σ * (1 / 2) ^ j * n ∧ σ * (1 / 2) ^ j * n ≤ σ := by
    intro n hn0 hn1
    have h1 : (1 / 2 : ℝ) ^ j * n ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (show n ≤ 2 ^ j - 1 by linarith) hq0.le
      nlinarith
    refine ⟨by positivity, ?_⟩
    rw [mul_assoc]; exact mul_le_of_le_one_right hσ0.le h1
  obtain ⟨b1, b2⟩ := bnd _ hn10 hn11
  obtain ⟨b3, b4⟩ := bnd _ hn20 hn21
  have hpw : ‖p - w‖ ≤ 2 * 𝕣 := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    rw [sub_re, sub_im, hpre, hpim]
    have a1 : |c.re + σ * (1 / 2) ^ j * n1 - w.re| ≤ σ := by
      rw [abs_le]; constructor <;> linarith
    have a2 : |c.im + σ * (1 / 2) ^ j * n2 - w.im| ≤ σ := by
      rw [abs_le]; constructor <;> linarith
    linarith
  calc ‖p‖ = ‖w + (p - w)‖ := by ring_nf
    _ ≤ ‖w‖ + ‖p - w‖ := norm_add_le _ _
    _ ≤ R * 𝕣 := by linarith

/-- deterministic part of the second display -/
theorem sq_display_det (Dg : ContMetric) {F 𝕣 ε s χ R : ℝ} (hF : 0 < F) (h𝕣 : 0 < 𝕣)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 < s) (hχs : χ < s)
    (hεs : ε ^ (s - χ) ≤ (1 - ((1 : ℝ) / 2) ^ s) / 2) {K : Set ℂ}
    (hK : ∀ w ∈ scaleSet 𝕣 0 K, ‖w‖ + 2 * 𝕣 ≤ R * 𝕣)
    (hgood : ∀ (ℓ : ℕ) (a : ℤ × ℤ), a ∈ gridSel (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) (R * 𝕣) →
      internalDiam Dg (osq (ε * (1 / 2) ^ ℓ * 𝕣) (gridPt (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) a))
        (osq (ε * (1 / 2) ^ ℓ * 𝕣) (gridPt (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) a)) ≤
        ENNReal.ofReal ((ε * (1 / 2) ^ ℓ) ^ s * F))
    (k : ℕ) (m : ℤ × ℤ) (hm : (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m ∩ scaleSet 𝕣 0 K).Nonempty) :
    ENNReal.ofReal F⁻¹ * internalDiam Dg (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m)
        (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k * ε) ^ χ) := by
  have hpk : ((1 : ℝ) / 2) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht0 : 0 < ε * ((1 : ℝ) / 2) ^ k := by positivity
  have htε : ε * ((1 : ℝ) / 2) ^ k ≤ ε := mul_le_of_le_one_right hε0.le hpk
  have hσ : (2 : ℝ)⁻¹ ^ k * ε * 𝕣 = ε * (1 / 2) ^ k * 𝕣 := by rw [inv_eq_one_div]; ring
  have ht' : (2 : ℝ)⁻¹ ^ k * ε = ε * (1 / 2) ^ k := by rw [inv_eq_one_div]; ring
  rw [hσ] at hm ⊢
  rw [ht', gridSquare_eq_csq]
  obtain ⟨w, hwS, hwK⟩ := hm
  rw [gridSquare_eq_csq] at hwS
  obtain ⟨w1, w2, w3, w4⟩ := hwS
  have hr0 : (0 : ℝ) ≤ (1 / 2) ^ s := Real.rpow_nonneg (by norm_num) _
  have hr1 : ((1 : ℝ) / 2) ^ s < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs
  have hdet := sq_det Dg (σ := ε * (1 / 2) ^ k * 𝕣) (s := s) (B := (ε * (1 / 2) ^ k) ^ s * F)
    (by positivity) hs (by positivity) (gridPt (ε * (1 / 2) ^ k * 𝕣) m) ?_
  · calc ENNReal.ofReal F⁻¹ * internalDiam Dg (csq (ε * (1 / 2) ^ k * 𝕣)
            (gridPt (ε * (1 / 2) ^ k * 𝕣) m)) (csq (ε * (1 / 2) ^ k * 𝕣)
            (gridPt (ε * (1 / 2) ^ k * 𝕣) m))
          ≤ ENNReal.ofReal F⁻¹ * ENNReal.ofReal (2 * ((ε * (1 / 2) ^ k) ^ s * F /
            (1 - (1 / 2) ^ s))) := by gcongr
      _ = ENNReal.ofReal (2 * (ε * (1 / 2) ^ k) ^ s / (1 - (1 / 2) ^ s)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hF.le)]; congr 1; field_simp
      _ ≤ ENNReal.ofReal ((ε * (1 / 2) ^ k) ^ χ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (ε * (1 / 2 : ℝ) ^ k) ^ s =
              (ε * (1 / 2) ^ k) ^ χ * (ε * (1 / 2) ^ k) ^ (s - χ) := by
            rw [← Real.rpow_add ht0]; ring_nf
          have h2 : (ε * (1 / 2 : ℝ) ^ k) ^ (s - χ) ≤ (1 - (1 / 2) ^ s) / 2 :=
            (Real.rpow_le_rpow ht0.le htε (by linarith)).trans hεs
          rw [div_le_iff₀ (by linarith), h1]
          have : 0 ≤ (ε * (1 / 2 : ℝ) ^ k) ^ χ := (Real.rpow_pos_of_pos ht0 _).le
          nlinarith
  · intro j n1 n2 hn10 hn11 hn20 hn21
    have hpj : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
    have hq0 : (0 : ℝ) < (1 / 2) ^ j := by positivity
    have hside : ε * (1 / 2 : ℝ) ^ (k + j) * 𝕣 = ε * (1 / 2) ^ k * 𝕣 * (1 / 2) ^ j := by
      rw [pow_add]; ring
    have hidx := hgood (k + j) ((2 : ℤ) ^ j * m.1 + n1, (2 : ℤ) ^ j * m.2 + n2) ?_
    · rw [gridPt_sub ε 𝕣 k j m n1 n2, hside] at hidx
      refine hidx.trans (le_of_eq ?_)
      congr 1
      rw [pow_add, show ε * ((1 / 2 : ℝ) ^ k * (1 / 2) ^ j) = (ε * (1 / 2) ^ k) * (1 / 2) ^ j by
        ring, Real.mul_rpow ht0.le hq0.le, half_pow_rpow]
      ring
    · have := corner_norm_le (j := j) (n1 := n1) (n2 := n2) (by positivity : 0 < ε * (1 / 2 : ℝ) ^ k * 𝕣)
        (by nlinarith : ε * (1 / 2 : ℝ) ^ k * 𝕣 ≤ 𝕣) hn10 hn11 hn20 hn21 ⟨w1, w2, w3, w4⟩ (hK w hwK)
      rw [← gridPt_sub ε 𝕣 k j m n1 n2] at this
      exact this

end L320
end LQGMetric.DFGPS
