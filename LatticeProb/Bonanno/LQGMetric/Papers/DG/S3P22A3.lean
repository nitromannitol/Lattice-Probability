/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22A3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22A2

/-!
# DG Proposition 3.22 assembly, part 3: the exponent of (eqn-lfpp-upper-show) (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, end of the proof of Proposition 3.22 (DG:1768–1770): with
`δ_ε ≤ ε^β`, `D^ε(z,w;U) ≤ ε^{-1/(d−ζ₁)}` (Prop. 3.9), `L_ε = ε^{-1/d + β(2+γ²/2)/d + ζ₂}`
(Lemma 3.21) and `max ĥ_{ε^β} ≤ (2+ζ₃) log ε^{-β}` (Lemma 3.5), the bound of `p322a_good` is
`≤ ε^{β(1 − 2/d − γ²/(2d)) − ζ}` once `1/(d−ζ₁) − 1/d ≤ ζ/4`, `ζ₂ = ζ/4`, `γζ₃β/d ≤ ζ/2` and
`14 ε^{ζ/2} ≤ 1` ("choosing `ζ̃` sufficiently small").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DG

/-- **the exponent bookkeeping of DG:1768–1770** -/
lemma p322a_exp {ε β γ d ζ ζ₁ ζ₃ δ Mx : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β)
    (hγ : 0 < γ) (hd : 0 < d) (hdz : 0 < d - ζ₁) (hζ : 0 < ζ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ ε ^ β)
    (hMx : Mx ≤ (2 + ζ₃) * β * Real.log ε⁻¹) (h1 : 1 / (d - ζ₁) - 1 / d ≤ ζ / 4)
    (h3 : γ * ζ₃ * β / d ≤ ζ / 2) (h14 : 14 * ε ^ (ζ / 2) ≤ 1) :
    3 * Real.sqrt 2 * δ * (2 * ε ^ (-(1 / (d - ζ₁))) /
        ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4) + Real.exp (γ / d * Mx)) ≤
      ε ^ (β * (1 - 2 / d - γ ^ 2 / (2 * d)) - ζ) := by
  set lam := β * (1 - 2 / d - γ ^ 2 / (2 * d)) with hlam
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- the two exponents
  have e1 : ε ^ β * (ε ^ (-(1 / (d - ζ₁))) / ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4)) =
      ε ^ (β + (-(1 / (d - ζ₁)) - (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4))) := by
    rw [← Real.rpow_sub hε, ← Real.rpow_add hε]
  have hexp : Real.exp (γ / d * Mx) ≤ ε ^ (-(γ / d * ((2 + ζ₃) * β))) := by
    rw [Real.rpow_def_of_pos hε]
    apply Real.exp_le_exp.2
    have : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
    have hg : 0 ≤ γ / d := by positivity
    calc γ / d * Mx ≤ γ / d * ((2 + ζ₃) * β * Real.log ε⁻¹) := mul_le_mul_of_nonneg_left hMx hg
      _ = _ := by rw [this]; ring
  have e2 : ε ^ β * ε ^ (-(γ / d * ((2 + ζ₃) * β))) = ε ^ (β - γ / d * ((2 + ζ₃) * β)) := by
    rw [← Real.rpow_add hε]; ring_nf
  -- both are `≤ ε^{λ − ζ/2}`
  have k1 : ε ^ (β + (-(1 / (d - ζ₁)) - (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4))) ≤
      ε ^ (lam - ζ / 2) := by
    apply Real.rpow_le_rpow_of_exponent_ge hε hε1
    rw [hlam]
    have : β * (1 - 2 / d - γ ^ 2 / (2 * d)) = β - β * (2 + γ ^ 2 / 2) / d := by
      field_simp; ring
    rw [this]; linarith
  have k2 : ε ^ (β - γ / d * ((2 + ζ₃) * β)) ≤ ε ^ (lam - ζ / 2) := by
    apply Real.rpow_le_rpow_of_exponent_ge hε hε1
    rw [hlam]
    have hq : 0 ≤ β / d * ((2 - γ) ^ 2 / 2) := by positivity
    have : β * (1 - 2 / d - γ ^ 2 / (2 * d)) - ζ / 2 =
        β - γ / d * (2 * β) - β / d * ((2 - γ) ^ 2 / 2) - ζ / 2 := by field_simp; ring
    rw [this]
    have : γ / d * ((2 + ζ₃) * β) = γ / d * (2 * β) + γ * ζ₃ * β / d := by field_simp
    rw [this]; linarith
  have hsplit : ε ^ (lam - ζ / 2) = ε ^ (lam - ζ) * ε ^ (ζ / 2) := by
    rw [← Real.rpow_add hε]; ring_nf
  have hpos : 0 < ε ^ (lam - ζ) := Real.rpow_pos_of_pos hε _
  have hq1 : 0 ≤ ε ^ (-(1 / (d - ζ₁))) / ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4) := by
    positivity
  have hq2 : 0 ≤ Real.exp (γ / d * Mx) := (Real.exp_pos _).le
  calc 3 * Real.sqrt 2 * δ * (2 * ε ^ (-(1 / (d - ζ₁))) /
        ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4) + Real.exp (γ / d * Mx))
      = 3 * Real.sqrt 2 * (2 * (δ * (ε ^ (-(1 / (d - ζ₁))) /
        ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4))) + δ * Real.exp (γ / d * Mx)) := by
        ring
    _ ≤ 3 * Real.sqrt 2 * (2 * (ε ^ β * (ε ^ (-(1 / (d - ζ₁))) /
        ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4))) +
          ε ^ β * ε ^ (-(γ / d * ((2 + ζ₃) * β)))) := by
        gcongr
    _ = 3 * Real.sqrt 2 * (2 * ε ^ (β + (-(1 / (d - ζ₁)) -
          (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ / 4))) +
          ε ^ (β - γ / d * ((2 + ζ₃) * β))) := by rw [e1, e2]
    _ ≤ 3 * Real.sqrt 2 * (2 * ε ^ (lam - ζ / 2) + ε ^ (lam - ζ / 2)) := by gcongr
    _ = 9 * Real.sqrt 2 * (ε ^ (lam - ζ) * ε ^ (ζ / 2)) := by rw [hsplit]; ring
    _ ≤ 14 * (ε ^ (lam - ζ) * ε ^ (ζ / 2)) := by
        have : 0 ≤ ε ^ (lam - ζ) * ε ^ (ζ / 2) := by positivity
        nlinarith
    _ = ε ^ (lam - ζ) * (14 * ε ^ (ζ / 2)) := by ring
    _ ≤ ε ^ (lam - ζ) * 1 := by gcongr
    _ = _ := mul_one _

end DG
end LQGMetric
