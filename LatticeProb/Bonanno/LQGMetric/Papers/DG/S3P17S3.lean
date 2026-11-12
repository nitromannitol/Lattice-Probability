/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17S3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17: the exponent algebra (DG:1543–1591) (P2-DG317S)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17. DG take
`β ∈ (0, 2/(2+γ)²)` ("e.g. `β = 1/(2+γ)²`", DG:1524), `δ = ε^β`, `δ_ε = 2^{-⌈log₂ ε^{-β}⌉}`,
and choose `ζ̃` small. Here `β = 1/(2+γ)²`, so `ε = δ^{(2+γ)²}`, and all small parameters are
`η = ζ/(16(2+γ)²)` (L3.13 and the lower bound `D^ε(K', ∂U') ≥ ε^{-1/(d+η)}`) and
`η' = η/(ξ+1)` (L3.5, L3.6). The rectangle bound of Step 2 becomes, with `t = 2^{-m}`,
`m = m_δ + 1`, `L = log δ⁻¹` (DG (eqn-use-rectangle-dist'), the `m³` term kept as a summand):
`N_S ≤ X e^{ξ ĥ_δ(v_S)}`, `X = ε^{-1/(d−η)} 2^{-(2+γ²/2−η)m/d} e^{ξη'L} + m³ δ^{-ξ(2+η')}`,
and `p17s_alg` is the comparison (eqn-lfpp-lower-last) ⇒ (eqn-lfpp-lower-show):
`6 δ^{λ+ζ} X ≤ ε^{-1/(d+η)} δ`.
-/

noncomputable section

open Set

namespace LQGMetric.DG

/-- DG's `ζ̃` for L3.13 and the lower bound: `η = ζ/(16(2+γ)²)` -/
def p17sEta (γ ζ : ℝ) : ℝ := ζ / (16 * (2 + γ) ^ 2)

/-- DG's `ζ̃` for L3.5 and L3.6: `η/(ξ+1)` -/
def p17sEta' (γ d ζ : ℝ) : ℝ := p17sEta γ ζ / (γ / d + 1)

/-- the deterministic factor of Step 2 (with `ε = δ^{(2+γ)²}`) -/
def p17sX (γ d ζ δ : ℝ) (m : ℕ) : ℝ :=
  (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - p17sEta γ ζ))) *
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - p17sEta γ ζ) * m / d)) *
      Real.exp (γ / d * (p17sEta' γ d ζ * Real.log δ⁻¹)) +
    (m : ℝ) ^ 3 * δ ^ (-(γ / d * (2 + p17sEta' γ d ζ)))

variable {γ d ζ : ℝ}

lemma p17sEta_pos (hγ : 0 < γ) (hζ : 0 < ζ) : 0 < p17sEta γ ζ := by
  unfold p17sEta; positivity

lemma p17sEta_le (hγ : 0 < γ) (hζ : 0 < ζ) : p17sEta γ ζ ≤ ζ / 64 := by
  unfold p17sEta
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : 64 ≤ 16 * (2 + γ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hζ.le]

lemma p17sEta'_pos (hγ : 0 < γ) (hd : 0 < d) (hζ : 0 < ζ) : 0 < p17sEta' γ d ζ := by
  unfold p17sEta'; have := p17sEta_pos hγ hζ; positivity

lemma p17sEta'_le (hγ : 0 < γ) (hd : 0 < d) (hζ : 0 < ζ) : p17sEta' γ d ζ ≤ p17sEta γ ζ := by
  unfold p17sEta'
  have := p17sEta_pos hγ hζ
  rw [div_le_iff₀ (by positivity)]
  have : 0 ≤ γ / d := by positivity
  nlinarith

lemma p17s_xi_eta' (hγ : 0 < γ) (hd : 0 < d) (hζ : 0 < ζ) :
    γ / d * p17sEta' γ d ζ ≤ p17sEta γ ζ := by
  unfold p17sEta'
  have := p17sEta_pos hγ hζ
  have h0 : 0 ≤ γ / d := by positivity
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- `m_δ = ⌈log₂ δ⁻¹⌉`: `2^{-m_δ} ≤ δ < 2 · 2^{-m_δ}`, `log₂ δ⁻¹ ≤ m_δ < log₂ δ⁻¹ + 1` -/
lemma p17s_dgM {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (2 : ℝ)⁻¹ ^ Blueprint.dgM δ ≤ δ ∧ δ < 2 * (2 : ℝ)⁻¹ ^ Blueprint.dgM δ ∧
      Real.logb 2 δ⁻¹ ≤ Blueprint.dgM δ ∧ (Blueprint.dgM δ : ℝ) < Real.logb 2 δ⁻¹ + 1 := by
  have hl : 0 < Real.logb 2 δ⁻¹ :=
    Real.logb_pos (by norm_num) ((one_lt_inv₀ hδ).2 hδ1)
  have h1 : Real.logb 2 δ⁻¹ ≤ Blueprint.dgM δ := Nat.le_ceil _
  have h2 : (Blueprint.dgM δ : ℝ) < Real.logb 2 δ⁻¹ + 1 := Nat.ceil_lt_add_one hl.le
  have e : ∀ x : ℝ, (2 : ℝ) ^ (-x) = (2 : ℝ)⁻¹ ^ x := fun x => by
    rw [Real.rpow_neg (by norm_num), Real.inv_rpow (by norm_num)]
  have eδ : (2 : ℝ) ^ (-Real.logb 2 δ⁻¹) = δ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.2 hδ),
      inv_inv]
  have eM : (2 : ℝ)⁻¹ ^ Blueprint.dgM δ = (2 : ℝ) ^ (-(Blueprint.dgM δ : ℝ)) := by
    rw [e, Real.rpow_natCast]
  refine ⟨?_, ?_, h1, h2⟩
  · rw [eM]
    calc (2 : ℝ) ^ (-(Blueprint.dgM δ : ℝ)) ≤ (2 : ℝ) ^ (-Real.logb 2 δ⁻¹) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = δ := eδ
  · have : (2 : ℝ) ^ (-Real.logb 2 δ⁻¹) < (2 : ℝ) ^ (1 - (Blueprint.dgM δ : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [eδ, Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast] at this
    rw [inv_pow]
    calc δ < 2 / 2 ^ Blueprint.dgM δ := this
      _ = _ := by ring

/-- `δ ≤ c^{1/g}` gives `δ^g ≤ c` -/
lemma p17s_rpow_small {δ g c : ℝ} (hg : 0 < g) (hc : 0 < c) (hδ : 0 < δ)
    (h : δ ≤ c ^ (1 / g)) : δ ^ g ≤ c := by
  calc δ ^ g ≤ (c ^ (1 / g)) ^ g := Real.rpow_le_rpow hδ.le h hg.le
    _ = c := by rw [← Real.rpow_mul hc.le, one_div_mul_cancel hg.ne', Real.rpow_one]

/-- the `m³` factor is beaten by a small power of `δ` -/
lemma p17s_m_small {δ m : ℝ} (hζ : 0 < ζ) (hδ : 0 < δ) (hδe : δ ≤ Real.exp (-1))
    (hm0 : 0 ≤ m) (hm : m ≤ Real.logb 2 δ⁻¹ + 2) (hs : δ ^ (ζ / 8) ≤ (ζ / 8) ^ 3 / 768) :
    12 * m ^ 3 * δ ^ (ζ / 2) ≤ 1 := by
  set u := Real.log δ⁻¹
  have hu : 1 ≤ u := by
    show 1 ≤ Real.log δ⁻¹
    rw [Real.log_inv, le_neg]
    exact (Real.log_le_log hδ hδe).trans_eq (Real.log_exp _)
  have hl2 : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlb : Real.logb 2 δ⁻¹ ≤ 2 * u := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]; nlinarith
  have hm4 : m ≤ 4 * u := by linarith
  set a := ζ / 8
  have ha : 0 < a := by positivity
  have hua : u ≤ δ ^ (-a) / a := by
    have := Real.log_le_rpow_div (inv_pos.2 hδ).le ha
    rwa [Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le] at this
  have hda : 0 < δ ^ (-a) := Real.rpow_pos_of_pos hδ _
  have hm' : m ≤ 4 * (δ ^ (-a) / a) := hm4.trans (by linarith)
  have hm3 : m ^ 3 ≤ (4 * (δ ^ (-a) / a)) ^ 3 := pow_le_pow_left₀ hm0 hm' 3
  have e : (4 * (δ ^ (-a) / a)) ^ 3 * δ ^ (ζ / 2) = 64 / a ^ 3 * δ ^ (ζ / 8) := by
    rw [mul_pow, div_pow, ← Real.rpow_natCast (δ ^ (-a)), ← Real.rpow_mul hδ.le]
    have : δ ^ (-a * ((3 : ℕ) : ℝ)) * δ ^ (ζ / 2) = δ ^ (ζ / 8) := by
      rw [← Real.rpow_add hδ]; congr 1; simp only [a]; push_cast; ring
    rw [← this]; ring
  have hδ2 : 0 ≤ δ ^ (ζ / 2) := Real.rpow_nonneg hδ.le _
  calc 12 * m ^ 3 * δ ^ (ζ / 2) ≤ 12 * ((4 * (δ ^ (-a) / a)) ^ 3 * δ ^ (ζ / 2)) := by
        rw [mul_assoc]; gcongr
    _ = 12 * (64 / a ^ 3) * δ ^ (ζ / 8) := by rw [e]; ring
    _ ≤ 12 * (64 / a ^ 3) * (a ^ 3 / 768) := by gcongr
    _ = 1 := by field_simp; norm_num

/-- the exponent comparison for the main term (DG:1588–1591) -/
lemma p17s_exp1 (hγ : 0 < γ) (hd : 1 ≤ d) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    1 - (2 + γ) ^ 2 / (d + p17sEta γ ζ) + ζ / 2 ≤
      (1 - 2 / d - γ ^ 2 / (2 * d) + ζ) - (2 + γ) ^ 2 / (d - p17sEta γ ζ) +
        (2 + γ ^ 2 / 2 - p17sEta γ ζ) / d - γ / d * p17sEta' γ d ζ := by
  set η := p17sEta γ ζ with hη
  have hη0 : 0 < η := p17sEta_pos hγ hζ
  have hη1 : η ≤ ζ / 64 := p17sEta_le hγ hζ
  have hd0 : 0 < d := by linarith
  have hx := p17s_xi_eta' hγ hd0 hζ
  have hB : 0 < (2 + γ) ^ 2 := by positivity
  have hBη : (2 + γ) ^ 2 * η = ζ / 16 := by
    rw [hη, p17sEta]; field_simp
  have hηd : η / d ≤ η := div_le_self hη0.le hd
  have hdm : 0 < d - η := by linarith
  have hdp : 0 < d + η := by linarith
  -- `B (1/(d−η) − 1/(d+η)) = 2Bη/((d−η)(d+η)) ≤ 4Bη = ζ/4`
  have hgap : (2 + γ) ^ 2 / (d - η) - (2 + γ) ^ 2 / (d + η) ≤ ζ / 4 := by
    rw [div_sub_div _ _ hdm.ne' hdp.ne', div_le_iff₀ (mul_pos hdm hdp)]
    have : (2 + γ) ^ 2 * (d + η) - (d - η) * (2 + γ) ^ 2 = 2 * ((2 + γ) ^ 2 * η) := by ring
    rw [this, hBη]
    have hprod : 1 / 2 ≤ (d - η) * (d + η) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hprod (by linarith : (0 : ℝ) ≤ ζ / 4)]
  have e : (2 + γ ^ 2 / 2 - η) / d = 2 / d + γ ^ 2 / (2 * d) - η / d := by
    field_simp
  rw [e]
  linarith

/-- the exponent comparison for the `m³` term (uses `β = 1/(2+γ)² < 2/(2+γ)²`, DG:1546) -/
lemma p17s_exp2 (hγ : 0 < γ) (hd : 1 ≤ d) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    1 - (2 + γ) ^ 2 / (d + p17sEta γ ζ) + ζ / 2 ≤
      (1 - 2 / d - γ ^ 2 / (2 * d) + ζ) - γ / d * (2 + p17sEta' γ d ζ) := by
  set η := p17sEta γ ζ with hη
  have hη0 : 0 < η := p17sEta_pos hγ hζ
  have hη1 : η ≤ ζ / 64 := p17sEta_le hγ hζ
  have hd0 : 0 < d := by linarith
  have hx := p17s_xi_eta' hγ hd0 hζ
  have hB : 0 < (2 + γ) ^ 2 := by positivity
  have hdp : 0 < d + η := by linarith
  have h2 : (2 + γ) ^ 2 / (2 * d) ≤ (2 + γ) ^ 2 / (d + η) :=
    div_le_div_of_nonneg_left hB.le hdp (by linarith)
  have e : 2 / d + γ ^ 2 / (2 * d) + γ / d * 2 = (2 + γ) ^ 2 / (2 * d) := by
    field_simp; ring
  have : γ / d * (2 + p17sEta' γ d ζ) = γ / d * 2 + γ / d * p17sEta' γ d ζ := by ring
  rw [this]
  linarith

lemma p17s_exp_log {δ a : ℝ} (hδ : 0 < δ) : Real.exp (a * Real.log δ⁻¹) = δ ^ (-a) := by
  rw [Real.rpow_def_of_pos hδ, Real.log_inv]; ring_nf

/-- **DG (eqn-lfpp-lower-last) ⇒ (eqn-lfpp-lower-show)** (DG:1586–1591): with
`T = 6 X` (Step 2) and `Lb = ε^{-1/(d+η)}`, `δ^{λ+ζ} T ≤ Lb δ` for small `δ` -/
lemma p17s_alg (hγ : 0 < γ) (hd : 1 ≤ d) (hζ : 0 < ζ) (hζ1 : ζ < 1) {δ : ℝ} (hδ : 0 < δ)
    (hδe : δ ≤ Real.exp (-1)) {m : ℕ} (ht : (2 : ℝ)⁻¹ ^ m ≤ δ)
    (hm : (m : ℝ) ≤ Real.logb 2 δ⁻¹ + 2) (hs1 : δ ^ (ζ / 2) ≤ 1 / 12)
    (hs2 : δ ^ (ζ / 8) ≤ (ζ / 8) ^ 3 / 768) :
    δ ^ ((1 - 2 / d - γ ^ 2 / (2 * d)) + ζ) * (6 * p17sX γ d ζ δ m) ≤
      (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d + p17sEta γ ζ))) * δ := by
  set η := p17sEta γ ζ with hη
  set η' := p17sEta' γ d ζ with hη'
  set lam := 1 - 2 / d - γ ^ 2 / (2 * d) with hlam
  have hη0 : 0 < η := p17sEta_pos hγ hζ
  have hη1 : η ≤ ζ / 64 := p17sEta_le hγ hζ
  have hd0 : 0 < d := by linarith
  set R := 1 - (2 + γ) ^ 2 / (d + η) with hR
  have eR : (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d + η))) * δ = δ ^ R := by
    rw [← Real.rpow_mul hδ.le, hR, Real.rpow_sub hδ, Real.rpow_one]
    have : (2 + γ) ^ 2 * -(1 / (d + η)) = -((2 + γ) ^ 2 / (d + η)) := by ring
    rw [this, Real.rpow_neg hδ.le]; field_simp
  rw [eR]
  have hδR : 0 < δ ^ R := Real.rpow_pos_of_pos hδ _
  have hδ1 : δ ≤ 1 := hδe.trans (by rw [Real.exp_le_one_iff]; norm_num)
  -- the main term
  set c := 2 + γ ^ 2 / 2 - η with hc
  have hc0 : 0 < c := by rw [hc]; nlinarith
  have hA2 : (2 : ℝ) ^ (-(c * m / d)) ≤ δ ^ (c / d) := by
    have e : (2 : ℝ) ^ (-(c * m / d)) = ((2 : ℝ)⁻¹ ^ m) ^ (c / d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.inv_rpow (by norm_num),
        ← Real.rpow_neg (by norm_num)]
      congr 1; ring
    rw [e]
    exact Real.rpow_le_rpow (by positivity) ht (by positivity)
  have hA1 : (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - η))) = δ ^ (-((2 + γ) ^ 2 / (d - η))) := by
    rw [← Real.rpow_mul hδ.le]; congr 1; ring
  have hA3 := p17s_exp_log (a := γ / d * η') hδ
  have hS : δ ^ (lam + ζ) * (δ ^ (-((2 + γ) ^ 2 / (d - η))) * δ ^ (c / d) *
      δ ^ (-(γ / d * η'))) ≤
      δ ^ R * δ ^ (ζ / 2) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ?_
    have := p17s_exp1 hγ hd hζ hζ1
    rw [← hη, ← hη'] at this
    rw [hlam, hR, hc]
    linarith
  have hT1 : δ ^ (lam + ζ) * (6 * ((δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - η))) *
      (2 : ℝ) ^ (-(c * m / d)) * Real.exp (γ / d * (η' * Real.log δ⁻¹)))) ≤ δ ^ R / 2 := by
    rw [hA1, show γ / d * (η' * Real.log δ⁻¹) = γ / d * η' * Real.log δ⁻¹ by ring, hA3]
    calc _ ≤ δ ^ (lam + ζ) * (6 * (δ ^ (-((2 + γ) ^ 2 / (d - η))) * δ ^ (c / d) *
          δ ^ (-(γ / d * η')))) := by
          gcongr
      _ = 6 * (δ ^ (lam + ζ) * (δ ^ (-((2 + γ) ^ 2 / (d - η))) * δ ^ (c / d) *
          δ ^ (-(γ / d * η')))) := by ring
      _ ≤ 6 * (δ ^ R * δ ^ (ζ / 2)) := by gcongr
      _ ≤ 6 * (δ ^ R * (1 / 12)) := by gcongr
      _ = δ ^ R / 2 := by ring
  -- the `m³` term
  have hT2 : δ ^ (lam + ζ) * (6 * ((m : ℝ) ^ 3 * δ ^ (-(γ / d * (2 + η'))))) ≤ δ ^ R / 2 := by
    have hS2 : δ ^ (lam + ζ) * δ ^ (-(γ / d * (2 + η'))) ≤ δ ^ R * δ ^ (ζ / 2) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ?_
      have := p17s_exp2 hγ hd hζ hζ1
      rw [← hη, ← hη'] at this
      rw [hlam, hR]
      linarith
    have hm12 := p17s_m_small hζ hδ hδe (Nat.cast_nonneg m) hm hs2
    have hm3 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
    calc _ = 6 * (m : ℝ) ^ 3 * (δ ^ (lam + ζ) * δ ^ (-(γ / d * (2 + η')))) := by ring
      _ ≤ 6 * (m : ℝ) ^ 3 * (δ ^ R * δ ^ (ζ / 2)) := by gcongr
      _ = δ ^ R * (12 * (m : ℝ) ^ 3 * δ ^ (ζ / 2)) / 2 := by ring
      _ ≤ δ ^ R * 1 / 2 := by gcongr
      _ = δ ^ R / 2 := by ring
  unfold p17sX
  rw [← hη, ← hη', ← hc]
  calc _ = δ ^ (lam + ζ) * (6 * ((δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - η))) *
      (2 : ℝ) ^ (-(c * m / d)) * Real.exp (γ / d * (η' * Real.log δ⁻¹)))) +
      δ ^ (lam + ζ) * (6 * ((m : ℝ) ^ 3 * δ ^ (-(γ / d * (2 + η'))))) := by ring
    _ ≤ δ ^ R / 2 + δ ^ R / 2 := add_le_add hT1 hT2
    _ = δ ^ R := by ring

end LQGMetric.DG
