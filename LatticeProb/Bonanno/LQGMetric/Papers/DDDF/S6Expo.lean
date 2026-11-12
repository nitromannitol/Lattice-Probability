/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Expo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul

/-!
# DDDF (5.77) and (1.3) (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.

* `s6_eq5_77` — **DDDF (5.77)** (Prop 26, l. 1268–1281): "by using Lemma 25, there exists
  `ρ > 0` such that `λ_n = ρ^{n + O(√n)}` … Combining (5.78) and (5.54) we get `ρ = 2^{-(1−ξQ)}`".
* `s6_eq1_3`, `dddfEq1_3_of_s6` — **DDDF (1.3)** (l. 162–166): (5.77) along `2^{-n}` and (6.98)
  (l. 1606–1613: "results obtained along the sequence `2^{-n}` can be extended to `δ ∈ (0,1)`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Real

namespace LQGMetric
namespace DDDF

open WhiteNoise S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

lemma ofReal_half_eq : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- **DDDF (5.77)** (Prop 26, l. 1268–1281) from (5.76), (5.54) and (5.78). -/
theorem s6_eq5_77 {q : ℝ} (hW : IsWhiteNoise P W) (h76 : S6Eq5_76 ξ W P)
    (h54 : S6Eq5_54 ξ q W P) (h78 : S6Eq5_78 ξ q W P) : S6Eq5_77 ξ q W P := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC⟩ := h76
  obtain ⟨ρ, hρ, C', hC'⟩ := dddf_lemma25 (lam := lambdaN ξ W P)
    (fun n _ => lambdaN_pos hW n) hC
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set u := -((1 - ξ * q) * Real.log 2)
  have hlogpow : ∀ (K : ℕ) (e : ℝ), Real.log ((2 : ℝ) ^ (-((K : ℝ) * e))) =
      -((K : ℝ) * e) * Real.log 2 := fun K e => Real.log_rpow two_pos _
  -- (5.54): `u ≤ log ρ`
  have hlow : u ≤ Real.log ρ := by
    refine le_of_asymp (C := C') fun ζ hζ => ?_
    obtain ⟨K₀, hK₀⟩ := h54 (1 / 2) (by norm_num) le_rfl (ζ / Real.log 2) (by positivity)
    refine ⟨max K₀ 1, fun K hK => ?_⟩
    have hK1 : 1 ≤ K := (le_max_right _ _).trans hK
    have h1 := (hK₀ K ((le_max_left _ _).trans hK)).trans
      (T20B.ellN_le_lambdaN (ξ := ξ) (W := W) (P := P) (by rw [ofReal_half_eq]; exact inv_two_pos')
        (by rw [ofReal_half_eq]) K)
    have l1 := Real.log_le_log (by positivity) h1
    rw [hlogpow] at l1
    have h2 := (abs_le.1 (hC' K hK1)).2
    have e : (K : ℝ) * (u - ζ) = -((K : ℝ) * (1 - ξ * q + ζ / Real.log 2)) * Real.log 2 := by
      simp only [u]; field_simp; ring
    rw [e]; linarith
  -- (5.78): `log ρ ≤ u`
  have hup : Real.log ρ ≤ u := by
    refine le_of_asymp (C := C') fun ζ hζ => ?_
    obtain ⟨K₀, hK₀⟩ := h78 (ζ / Real.log 2) (by positivity)
    refine ⟨max K₀ 1, fun K hK => ?_⟩
    have hK1 : 1 ≤ K := (le_max_right _ _).trans hK
    have h1 := hK₀ K ((le_max_left _ _).trans hK)
    have l1 := Real.log_le_log (lambdaN_pos hW K) h1
    rw [hlogpow] at l1
    have h2 := (abs_le.1 (hC' K hK1)).1
    have e : (K : ℝ) * u = -((K : ℝ) * (1 - ξ * q - ζ / Real.log 2)) * Real.log 2 - K * ζ := by
      simp only [u]; field_simp; ring
    linarith
  have hρu : Real.log ρ = u := le_antisymm hup hlow
  refine ⟨C', fun n hn => ?_⟩
  have := hC' n hn
  rw [hρu] at this
  have e : Real.log (lambdaN ξ W P n) - n * u =
      Real.log (lambdaN ξ W P n) + n * (1 - ξ * q) * Real.log 2 := by simp only [u]; ring
  rwa [e] at this

/-- **DDDF (1.3)** (l. 162–166) from (5.77) and (6.98): `λ_δ = δ^{1−ξQ} e^{O(√|log δ|)}`, in the
reading of `Blueprint.DDDFEq1_3` (`δ ∈ (0, δ₀)`). -/
theorem s6_eq1_3 {q : ℝ} (hW : IsWhiteNoise P W) (h77 : S6Eq5_77 ξ q W P)
    (h98 : S6Eq6_98 ξ W P) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      δ ^ (1 - ξ * q) * Real.exp (-C * Real.sqrt |Real.log δ|) ≤ lambdaDelta ξ W P δ ∧
        lambdaDelta ξ W P δ ≤ δ ^ (1 - ξ * q) * Real.exp (C * Real.sqrt |Real.log δ|) := by
  obtain ⟨C₁, hC₁⟩ := log98 hW h98
  obtain ⟨C, hC⟩ := h77
  set κ := (1 - ξ * q) * Real.log 2
  set a : ℝ → ℝ := fun t => Real.log (lamT ξ W P t)
  have hexp := expo_log (a := a) (κ := κ) (C := C) (fun n r h0 h1 => (hC₁ n r h0 h1).2)
    (fun n hn => by
      have := hC n hn
      simp only [a, κ]; rw [lamT_nat]
      rwa [show (n : ℝ) * ((1 - ξ * q) * Real.log 2) = n * (1 - ξ * q) * Real.log 2 by ring])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs2 : 0 < √(Real.log 2) := Real.sqrt_pos.2 hl2
  set D := abs (C₁ + |κ| + |C|) / √(Real.log 2)
  refine ⟨D, 1 / 2, by norm_num, fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  set t := -Real.log δ / Real.log 2
  have hlδ : Real.log δ ≤ -Real.log 2 := by
    rw [← Real.log_inv]; exact Real.log_le_log hδ0 (by have := hδ.2; norm_num at this ⊢; linarith)
  have ht1 : 1 ≤ t := by rw [le_div_iff₀ hl2]; linarith
  have eδ : (2 : ℝ) ^ (-t) = δ := two_rpow_neg_log δ hδ0
  have hy : lambdaDelta ξ W P δ = lamT ξ W P t := by rw [lamT, eδ]
  have et : Real.log δ = -(t * Real.log 2) := by simp only [t]; field_simp
  have hL : |Real.log δ| = t * Real.log 2 := by
    rw [et, abs_neg, abs_of_nonneg (by positivity)]
  have hsq : √t = √|Real.log δ| / √(Real.log 2) := by
    rw [hL, Real.sqrt_mul (by linarith), mul_div_assoc, div_self hs2.ne', mul_one]
  have hk := hexp t ht1
  have hk' : |a t + t * κ| ≤ D * √|Real.log δ| := by
    refine hk.trans ?_
    rw [hsq]
    calc (C₁ + |κ| + |C|) * (√|Real.log δ| / √(Real.log 2))
        ≤ abs (C₁ + |κ| + |C|) * (√|Real.log δ| / √(Real.log 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = D * √|Real.log δ| := by simp only [D]; ring
  obtain ⟨k1, k2⟩ := abs_le.1 hk'
  have hxp := lamT_pos hW h98 (zero_le_one.trans ht1)
  have hpow : Real.log (δ ^ (1 - ξ * q)) = -(t * κ) := by
    rw [Real.log_rpow hδ0, et]; simp only [κ]; ring
  simp only [a] at k1 k2
  rw [hy]
  constructor
  · rw [← Real.log_le_log_iff (by positivity) hxp, Real.log_mul (by positivity) (by positivity),
      Real.log_exp, hpow]
    have : -D * √|Real.log δ| = -(D * √|Real.log δ|) := by ring
    rw [this]; linarith
  · rw [← Real.log_le_log_iff hxp (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, hpow]
    linarith

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3`, from (5.76), (6.98), (5.54) and (5.78) for
`ξ = γ/d_γ`, `Q = 2/γ + γ/2`. -/
theorem dddfEq1_3_of_s6
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6Eq5_76 (xiGamma γ) W P ∧ S6Eq6_98 (xiGamma γ) W P ∧
          S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧ S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) :
    Blueprint.DDDFEq1_3 := by
  intro γ hγ hγ2 Ω _ P W hW
  obtain ⟨h76, h98, h54, h78⟩ := h γ hγ hγ2 P W hW
  exact s6_eq1_3 hW (s6_eq5_77 hW h76 h54 h78) h98

end DDDF
end LQGMetric
