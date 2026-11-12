/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_14Ratio at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.14: the Λ-bounds on `𝔠_{δr}/𝔠_r` (deterministic part)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:1096–1097): "The
bounds (eqn-scaling-constant') (in fact, substantially stronger bounds) are immediate from
[DDDF, Theorem 1, Equation (1.3)] and the fact the ratio of our `𝔞_ε` and the scaling factor
`λ_ε` from [DDDF] is bounded above and below by deterministic, `ε`-independent constants".

Here `a` stands for `𝔞_ε`, `lam` for `λ_ε`, `p = 1 − ξQ`. The bound needs, besides (1.3), the
quasi-multiplicativity DDDF (6.99) `λ_{δδ'} ≍ λ_δ λ_{δ'} e^{O(√|log δ ∨ δ'|)}` (DD:1615–1621):
(1.3) alone controls `λ_{δη}/λ_η` only up to `e^{O(√|log η|)}`, which blows up as `η → 0`
(DEV entry P2-DFB8-a). With (6.99) (`δ` fixed, `η → 0`, so `δ ∨ η = δ`):
`𝔞_{δη}/𝔞_η ≍ λ_δ e^{O(√|log δ|)} ≍ δ^p e^{O(√|log δ|)}` for `δ < δ₀`, and
`e^{K√L} ≤ e^{K²/4} e^{L}` turns the error into a power of `δ`. For `δ ∈ [δ₀, 1)` write
`δη = δ₁η` with `δ₁ = δδ₂`, `δ₂ = δ₀/2`, and divide two small-`δ` ratios (own bookkeeping).

* `ratio_bounds`: `∃ Λ > 1, ∀ δ ∈ (0,1)`, for small `η > 0`,
  `Λ⁻¹ δ^Λ ≤ 𝔞_{δη}/𝔞_η ≤ Λ δ^{−Λ}` (and `𝔞_η, 𝔞_{δη} > 0`);
* `scaling_const_bounds`: if `r 𝔞_{ε_n/r}/𝔞_{ε_n} → 𝔠_r` for all `r > 0`, then `𝔠_r > 0` and
  `Λ'⁻¹ δ^{Λ'} ≤ 𝔠_{δr}/𝔠_r ≤ Λ' δ^{−Λ'}` (T:1066).
-/

noncomputable section

open Filter Topology Set

namespace LQGMetric.DFGPS.L214

lemma exp_mul_sqrt_le (K L : ℝ) (hL : 0 ≤ L) :
    Real.exp (K * Real.sqrt L) ≤ Real.exp (K ^ 2 / 4) * Real.exp L := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [sq_nonneg (Real.sqrt L - K / 2), Real.sq_sqrt hL]

lemma exp_neg_mul_sqrt_ge (K L : ℝ) (hL : 0 ≤ L) :
    Real.exp (-K ^ 2 / 4) * Real.exp (-L) ≤ Real.exp (-(K * Real.sqrt L)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [sq_nonneg (Real.sqrt L - K / 2), Real.sq_sqrt hL]

/-- the small-`δ` ratio bound -/
theorem ratio_small {a lam : ℝ → ℝ} {p : ℝ}
    (hab : ∃ C > 0, ∃ εb > 0, ∀ ε, 0 < ε → ε < εb →
      0 < lam ε ∧ C⁻¹ * lam ε ≤ a ε ∧ a ε ≤ C * lam ε)
    (h13 : ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      δ ^ p * Real.exp (-C * Real.sqrt |Real.log δ|) ≤ lam δ ∧
        lam δ ≤ δ ^ p * Real.exp (C * Real.sqrt |Real.log δ|))
    (h699 : ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ δ' ∈ Ioo (0 : ℝ) 1,
      C⁻¹ * Real.exp (-C * Real.sqrt |Real.log (max δ δ')|) * (lam δ * lam δ') ≤ lam (δ * δ') ∧
        lam (δ * δ') ≤ C * Real.exp (C * Real.sqrt |Real.log (max δ δ')|) * (lam δ * lam δ')) :
    ∃ A m δ₁ : ℝ, 0 < A ∧ 0 ≤ m ∧ 0 < δ₁ ∧ δ₁ < 1 ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₁, ∃ η₀ > 0,
      ∀ η, 0 < η → η < η₀ → 0 < a η ∧ 0 < a (δ * η) ∧
        A⁻¹ * δ ^ m ≤ a (δ * η) / a η ∧ a (δ * η) / a η ≤ A * δ ^ (-m) := by
  obtain ⟨Ca, hCa, εb, hεb, hb⟩ := hab
  obtain ⟨C1, δ₀, hδ₀, h1⟩ := h13
  obtain ⟨C2, hC2, h2⟩ := h699
  set K := |C1| + C2
  set m := |p| + 1
  refine ⟨Ca ^ 2 * C2 * Real.exp (K ^ 2 / 4), m, min δ₀ (1 / 2), by positivity, by positivity,
    by positivity, lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδδ₀ : δ < δ₀ := lt_of_lt_of_le hδ.2 (min_le_left _ _)
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ.2 ((min_le_right _ _).trans (by norm_num))
  refine ⟨min εb δ, lt_min hεb hδ0, fun η hη hηη => ?_⟩
  have hηb : η < εb := lt_of_lt_of_le hηη (min_le_left _ _)
  have hηδ : η < δ := lt_of_lt_of_le hηη (min_le_right _ _)
  have hη1 : η < 1 := hηδ.trans hδ1
  have hδη : δ * η < η := by nlinarith
  obtain ⟨hlη, haη1, haη2⟩ := hb η hη hηb
  obtain ⟨hlδη, hδη1, hδη2⟩ := hb (δ * η) (by positivity) (hδη.trans hηb)
  have haη : 0 < a η := lt_of_lt_of_le (by positivity) haη1
  have haδη : 0 < a (δ * η) := lt_of_lt_of_le (by positivity) hδη1
  refine ⟨haη, haδη, ?_⟩
  set L := -Real.log δ
  have hL : 0 ≤ L := by
    have := Real.log_neg hδ0 hδ1; simp only [L]; linarith
  have habs : |Real.log δ| = L := by
    rw [abs_of_neg (Real.log_neg hδ0 hδ1)]
  have hexpL : Real.exp L = δ⁻¹ := by simp only [L]; rw [Real.exp_neg, Real.exp_log hδ0]
  have hexpL' : Real.exp (-L) = δ := by simp only [L, neg_neg]; rw [Real.exp_log hδ0]
  have hmax : max δ η = δ := max_eq_left hηδ.le
  obtain ⟨hl2, hu2⟩ := h2 δ ⟨hδ0, hδ1⟩ η ⟨hη, hη1⟩
  rw [hmax, habs] at hl2 hu2
  obtain ⟨hl1, hu1⟩ := h1 δ ⟨hδ0, hδδ₀⟩
  rw [habs] at hl1 hu1
  have hsL := Real.sqrt_nonneg L
  have hl1' : δ ^ p * Real.exp (-|C1| * Real.sqrt L) ≤ lam δ := by
    refine le_trans ?_ hl1
    gcongr
    nlinarith [le_abs_self C1, neg_abs_le C1]
  have hu1' : lam δ ≤ δ ^ p * Real.exp (|C1| * Real.sqrt L) := by
    refine hu1.trans ?_
    gcongr
    exact le_abs_self C1
  have hlδ : 0 < lam δ := lt_of_lt_of_le (by positivity) hl1'
  -- powers of `δ`
  have hpow_le : δ ^ p ≤ δ ^ (-|p|) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by linarith [neg_abs_le p])
  have hpow_ge : δ ^ |p| ≤ δ ^ p :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (le_abs_self p)
  have hm1 : δ ^ (-m) = δ ^ (-|p|) * δ⁻¹ := by
    rw [show -m = -|p| + (-1) by simp only [m]; ring, Real.rpow_add hδ0, Real.rpow_neg_one]
  have hm2 : δ ^ m = δ ^ |p| * δ := by
    rw [show m = |p| + 1 by rfl, Real.rpow_add hδ0, Real.rpow_one]
  have hK1 : Real.exp (C2 * Real.sqrt L) * Real.exp (|C1| * Real.sqrt L) ≤
      Real.exp (K ^ 2 / 4) * δ⁻¹ := by
    rw [← Real.exp_add, ← add_mul, add_comm, ← hexpL]
    exact exp_mul_sqrt_le K L hL
  have hK2 : Real.exp (-K ^ 2 / 4) * δ ≤
      Real.exp (-C2 * Real.sqrt L) * Real.exp (-|C1| * Real.sqrt L) := by
    rw [← Real.exp_add, ← add_mul, ← hexpL', show (-C2 + -|C1|) * Real.sqrt L =
      -(K * Real.sqrt L) by simp only [K]; ring]
    exact exp_neg_mul_sqrt_ge K L hL
  constructor
  · -- lower bound
    rw [le_div_iff₀ haη]
    have e1 : Ca⁻¹ * (C2⁻¹ * Real.exp (-C2 * Real.sqrt L) * (lam δ * lam η)) ≤ a (δ * η) :=
      le_trans (by gcongr) hδη1
    refine le_trans ?_ e1
    have e2 : (Ca ^ 2 * C2 * Real.exp (K ^ 2 / 4))⁻¹ * δ ^ m ≤
        Ca⁻¹ ^ 2 * C2⁻¹ * (Real.exp (-C2 * Real.sqrt L) * lam δ) := by
      calc (Ca ^ 2 * C2 * Real.exp (K ^ 2 / 4))⁻¹ * δ ^ m
          = Ca⁻¹ ^ 2 * C2⁻¹ * (δ ^ |p| * (Real.exp (-K ^ 2 / 4) * δ)) := by
            rw [hm2, show -K ^ 2 / 4 = -(K ^ 2 / 4) by ring, Real.exp_neg]
            field_simp
        _ ≤ Ca⁻¹ ^ 2 * C2⁻¹ * (δ ^ p *
              (Real.exp (-C2 * Real.sqrt L) * Real.exp (-|C1| * Real.sqrt L))) := by
            gcongr
        _ = Ca⁻¹ ^ 2 * C2⁻¹ * (Real.exp (-C2 * Real.sqrt L) *
              (δ ^ p * Real.exp (-|C1| * Real.sqrt L))) := by ring
        _ ≤ _ := by gcongr
    calc (Ca ^ 2 * C2 * Real.exp (K ^ 2 / 4))⁻¹ * δ ^ m * a η
        ≤ (Ca⁻¹ ^ 2 * C2⁻¹ * (Real.exp (-C2 * Real.sqrt L) * lam δ)) * (Ca * lam η) := by
          gcongr
      _ = _ := by field_simp
  · -- upper bound
    rw [div_le_iff₀ haη]
    have e1 : a (δ * η) ≤ Ca * (C2 * Real.exp (C2 * Real.sqrt L) * (lam δ * lam η)) :=
      hδη2.trans (by gcongr)
    refine e1.trans ?_
    have e2 : Ca ^ 2 * (C2 * Real.exp (C2 * Real.sqrt L) * lam δ) ≤
        Ca ^ 2 * C2 * Real.exp (K ^ 2 / 4) * δ ^ (-m) := by
      calc Ca ^ 2 * (C2 * Real.exp (C2 * Real.sqrt L) * lam δ)
          ≤ Ca ^ 2 * (C2 * Real.exp (C2 * Real.sqrt L) *
              (δ ^ p * Real.exp (|C1| * Real.sqrt L))) := by gcongr
        _ = Ca ^ 2 * C2 * (δ ^ p *
              (Real.exp (C2 * Real.sqrt L) * Real.exp (|C1| * Real.sqrt L))) := by ring
        _ ≤ Ca ^ 2 * C2 * (δ ^ (-|p|) * (Real.exp (K ^ 2 / 4) * δ⁻¹)) := by gcongr
        _ = _ := by rw [hm1]; ring
    calc Ca * (C2 * Real.exp (C2 * Real.sqrt L) * (lam δ * lam η))
        = Ca ^ 2 * (C2 * Real.exp (C2 * Real.sqrt L) * lam δ) * (Ca⁻¹ * lam η) := by
          field_simp
      _ ≤ (Ca ^ 2 * C2 * Real.exp (K ^ 2 / 4) * δ ^ (-m)) * a η := by gcongr

lemma weaken_bounds {A m Λ δ q : ℝ} (hA : 0 < A) (hAΛ : A ≤ Λ) (hmΛ : m ≤ Λ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (h1 : A⁻¹ * δ ^ m ≤ q) (h2 : q ≤ A * δ ^ (-m)) :
    Λ⁻¹ * δ ^ Λ ≤ q ∧ q ≤ Λ * δ ^ (-Λ) := by
  have hδ0 := hδ.1
  have hp1 : δ ^ Λ ≤ δ ^ m := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ.2.le hmΛ
  have hp2 : δ ^ (-m) ≤ δ ^ (-Λ) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ.2.le (by linarith)
  have hΛ0 : 0 ≤ Λ := hA.le.trans hAΛ
  constructor
  · refine le_trans ?_ h1
    gcongr
  · refine h2.trans ?_
    gcongr

/-- **The ratio bounds for all `δ ∈ (0,1)`** (DFGPS T:1096–1097 with DDDF (1.3), (6.99)). -/
theorem ratio_bounds {a lam : ℝ → ℝ} {p : ℝ}
    (hab : ∃ C > 0, ∃ εb > 0, ∀ ε, 0 < ε → ε < εb →
      0 < lam ε ∧ C⁻¹ * lam ε ≤ a ε ∧ a ε ≤ C * lam ε)
    (h13 : ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      δ ^ p * Real.exp (-C * Real.sqrt |Real.log δ|) ≤ lam δ ∧
        lam δ ≤ δ ^ p * Real.exp (C * Real.sqrt |Real.log δ|))
    (h699 : ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ δ' ∈ Ioo (0 : ℝ) 1,
      C⁻¹ * Real.exp (-C * Real.sqrt |Real.log (max δ δ')|) * (lam δ * lam δ') ≤ lam (δ * δ') ∧
        lam (δ * δ') ≤ C * Real.exp (C * Real.sqrt |Real.log (max δ δ')|) * (lam δ * lam δ')) :
    ∃ Λ : ℝ, 1 < Λ ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ η₀ > 0,
      ∀ η, 0 < η → η < η₀ → 0 < a η ∧ 0 < a (δ * η) ∧
        Λ⁻¹ * δ ^ Λ ≤ a (δ * η) / a η ∧ a (δ * η) / a η ≤ Λ * δ ^ (-Λ) := by
  obtain ⟨A, m, δ₁, hA, hm, hδ₁, hδ₁1, hS⟩ := ratio_small hab h13 h699
  set δ₂ := δ₁ / 2
  have hδ₂ : 0 < δ₂ := by positivity
  have hδ₂1 : δ₂ < δ₁ := by simp only [δ₂]; linarith
  set u := δ₂ ^ m
  have hu : 0 < u := Real.rpow_pos_of_pos hδ₂ m
  set B := A ^ 2 * (u⁻¹) ^ 2
  have hB : 0 < B := by positivity
  set Λ := max (max A B) m + 1
  have hAΛ : A ≤ Λ := by simp only [Λ]; linarith [le_max_left A B, le_max_left (max A B) m]
  have hBΛ : B ≤ Λ := by simp only [Λ]; linarith [le_max_right A B, le_max_left (max A B) m]
  have hmΛ : m ≤ Λ := by simp only [Λ]; linarith [le_max_right (max A B) m]
  refine ⟨Λ, by simp only [Λ]; linarith [le_max_left A B, le_max_left (max A B) m], fun δ hδ => ?_⟩
  rcases lt_or_ge δ δ₁ with hsm | hlg
  · obtain ⟨η₀, hη₀, h⟩ := hS δ ⟨hδ.1, hsm⟩
    refine ⟨η₀, hη₀, fun η hη hηη => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := h η hη hηη
    exact ⟨h1, h2, weaken_bounds hA hAΛ hmΛ hδ h3 h4⟩
  · have hδ0 := hδ.1
    have hδa : δ * δ₂ ∈ Ioo (0 : ℝ) δ₁ := ⟨by positivity, by nlinarith [hδ.2]⟩
    obtain ⟨ηa, hηa, ha⟩ := hS (δ * δ₂) hδa
    obtain ⟨ηb, hηb, hb⟩ := hS δ₂ ⟨hδ₂, hδ₂1⟩
    refine ⟨min ηa ηb, lt_min hηa hηb, fun η hη hηη => ?_⟩
    have hη1 : η < ηa := lt_of_lt_of_le hηη (min_le_left _ _)
    have hη2 : η < ηb := lt_of_lt_of_le hηη (min_le_right _ _)
    have hδη : δ * η < ηb := lt_of_le_of_lt (by nlinarith [hδ.2]) hη2
    obtain ⟨hX0, hX1, hX2, hX3⟩ := ha η hη hη1
    obtain ⟨hY0, hY1, hY2, hY3⟩ := hb (δ * η) (by positivity) hδη
    have he : δ₂ * (δ * η) = δ * δ₂ * η := by ring
    rw [he] at hY1 hY2 hY3
    set v := δ ^ m
    have hv : 0 < v := Real.rpow_pos_of_pos hδ0 m
    have e1 : (δ * δ₂) ^ m = v * u := Real.mul_rpow hδ0.le hδ₂.le
    have e2 : (δ * δ₂) ^ (-m) = (v * u)⁻¹ := by rw [Real.rpow_neg (by positivity), e1]
    have e3 : δ₂ ^ (-m) = u⁻¹ := Real.rpow_neg hδ₂.le m
    have e4 : δ ^ (-m) = v⁻¹ := Real.rpow_neg hδ0.le m
    rw [e1] at hX2; rw [e2] at hX3; rw [e3] at hY3
    set X := a (δ * δ₂ * η) / a η
    set Y := a (δ * δ₂ * η) / a (δ * η)
    have hq : a (δ * η) / a η = X / Y := by
      simp only [X, Y]; rw [div_div_div_cancel_left' _ _ hY1.ne']
    have hY : 0 < Y := by positivity
    refine ⟨hX0, hY0, weaken_bounds hB hBΛ hmΛ hδ ?_ ?_⟩
    · rw [hq]
      calc B⁻¹ * v = A⁻¹ * (v * u) / (A * u⁻¹) := by simp only [B]; field_simp
        _ ≤ X / Y := div_le_div₀ (by positivity) hX2 (by positivity) hY3
    · rw [hq, e4]
      calc X / Y ≤ A * (v * u)⁻¹ / (A⁻¹ * u) := div_le_div₀ (by positivity) hX3 (by positivity) hY2
        _ = B * v⁻¹ := by simp only [B]; field_simp

lemma eventually_div_lt {εn : ℕ → ℝ} (hεt : Tendsto εn atTop (𝓝 0)) (s : ℝ) {η₀ : ℝ}
    (hη₀ : 0 < η₀) : ∀ᶠ n in atTop, εn n / s < η₀ := by
  have := hεt.div_const s
  rw [zero_div] at this
  exact this.eventually (Iio_mem_nhds hη₀)

end LQGMetric.DFGPS.L214
