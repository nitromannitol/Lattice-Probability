/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bRate at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# GM L4.15 Step 1: the rate in (4.40)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 1, l. 2125–2131:
with `N = ⌊ε^{-ω}⌋` and `β` small depending on `ω` (here `2β < ωβ_C`), the union bound over
`k ∈ [0,K]`, `K ≤ Aε^{-β}`, of the T3.9 bounds `b₀ exp(−b₁N^{β_C})` is `o^∞_ε(ε)`.
`p412b_rate` gives, for every `M`, an `ε₁` such that for `ε < ε₁`: `N ≥ 1`,
`N^{-β_C} C' ≤ ε^{2β}` (the time condition of `p412b_step1_E`) and
`(Aε^{-β} + 1) b₀ exp(−b₁N^{β_C}) ≤ ε^M`. Elementary real analysis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace LQGMetric.GM

/-- **the rate of (4.40)** (GM l. 2125–2131) -/
theorem p412b_rate {b₀ b₁ βC ω₀ β A C' M : ℝ} (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hβC : 0 < βC)
    (hω₀ : 0 < ω₀) (hβ : 0 < β) (hβω : 2 * β < ω₀ * βC) (hA : 0 ≤ A) (hC' : 0 ≤ C') :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁,
      1 ≤ ⌊ε ^ (-ω₀)⌋₊ ∧ (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ (-βC) * C' ≤ ε ^ (2 * β) ∧
      (A * ε ^ (-β) + 1) * (b₀ * Real.exp (-b₁ * (⌊ε ^ (-ω₀)⌋₊ : ℝ) ^ βC)) ≤ ε ^ M := by
  set δ := ω₀ * βC with hδ
  have hδ0 : 0 < δ := mul_pos hω₀ hβC
  set b' := b₁ * (2 : ℝ)⁻¹ ^ βC with hb'
  have hb'0 : 0 < b' := by positivity
  -- eventual facts as `ε → 0+`
  have hX : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 ≤ ε ^ (-ω₀) :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.2 hω₀)).eventually (eventually_ge_atTop 2)
  have hgap : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (2 : ℝ) ^ βC * C' * ε ^ (δ - 2 * β) ≤ 1 := by
    have := (Real.continuousAt_rpow_const 0 (δ - 2 * β) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    have h2 : Tendsto (fun x : ℝ => (2 : ℝ) ^ βC * C' * x ^ (δ - 2 * β)) (𝓝[>] 0) (𝓝 0) := by
      have := (this.const_mul ((2 : ℝ) ^ βC * C')).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [mul_zero] at this
    exact h2.eventually (Iic_mem_nhds one_pos)
  have hexp : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (ε ^ (-δ)) ^ ((β + M) / δ) * Real.exp (-b' * ε ^ (-δ)) ≤ 1 / ((A + 1) * b₀) := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((β + M) / δ) b' hb'0).comp
      (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.2 hδ0))
    exact h1.eventually (Iic_mem_nhds (by positivity))
  have hlin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨ε₁, hε₁, hε₁'⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 (((hX.and hgap).and hexp).and hlin)
  refine ⟨ε₁, hε₁, fun ε hε => ?_⟩
  obtain ⟨⟨⟨hX2, hg⟩, he⟩, hε0, hε1⟩ := hε₁' hε
  set X := ε ^ (-ω₀) with hXdef
  set N := ⌊X⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.2 (by linarith)
  have hNX : X / 2 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one X; linarith
  have hX0 : 0 < X / 2 := by linarith
  -- `N^{βC} ≥ 2^{-βC} ε^{-δ}`
  have hXδ : X ^ βC = ε ^ (-δ) := by
    rw [hXdef, ← Real.rpow_mul hε0.le, hδ, neg_mul]
  have hNβ : (2 : ℝ)⁻¹ ^ βC * ε ^ (-δ) ≤ (N : ℝ) ^ βC := by
    have := Real.rpow_le_rpow hX0.le hNX hβC.le
    rw [div_eq_mul_inv, Real.mul_rpow (by linarith) (by norm_num), hXδ] at this
    linarith
  have hεδ : 0 < ε ^ (-δ) := Real.rpow_pos_of_pos hε0 _
  have hNpos : (0 : ℝ) < (N : ℝ) ^ βC := lt_of_lt_of_le (by positivity) hNβ
  refine ⟨hN1, ?_, ?_⟩
  · -- the time condition
    have hinv : (N : ℝ) ^ (-βC) ≤ (2 : ℝ) ^ βC * ε ^ δ := by
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
      rw [inv_le_iff_one_le_mul₀ hNpos]
      have h2 : (2 : ℝ) ^ βC * ε ^ δ * ((2 : ℝ)⁻¹ ^ βC * ε ^ (-δ)) = 1 := by
        rw [show (2 : ℝ) ^ βC * ε ^ δ * ((2 : ℝ)⁻¹ ^ βC * ε ^ (-δ)) =
          ((2 : ℝ) ^ βC * (2 : ℝ)⁻¹ ^ βC) * (ε ^ δ * ε ^ (-δ)) by ring,
          ← Real.mul_rpow (by norm_num) (by norm_num), ← Real.rpow_add hε0]
        simp
      calc (1 : ℝ) = (2 : ℝ) ^ βC * ε ^ δ * ((2 : ℝ)⁻¹ ^ βC * ε ^ (-δ)) := h2.symm
        _ ≤ (2 : ℝ) ^ βC * ε ^ δ * (N : ℝ) ^ βC :=
          mul_le_mul_of_nonneg_left hNβ (by positivity)
    have hsplit : ε ^ δ = ε ^ (2 * β) * ε ^ (δ - 2 * β) := by
      rw [← Real.rpow_add hε0]; ring_nf
    calc (N : ℝ) ^ (-βC) * C' ≤ (2 : ℝ) ^ βC * ε ^ δ * C' := mul_le_mul_of_nonneg_right hinv hC'
      _ = ε ^ (2 * β) * ((2 : ℝ) ^ βC * C' * ε ^ (δ - 2 * β)) := by rw [hsplit]; ring
      _ ≤ ε ^ (2 * β) * 1 := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = ε ^ (2 * β) := mul_one _
  · -- the rate
    have hεβ1 : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1.le (by linarith)
    have hpre : A * ε ^ (-β) + 1 ≤ (A + 1) * ε ^ (-β) := by nlinarith
    have hexpb : Real.exp (-b₁ * (N : ℝ) ^ βC) ≤ Real.exp (-b' * ε ^ (-δ)) := by
      refine Real.exp_le_exp.2 ?_
      rw [hb']; nlinarith
    have hpow : (ε ^ (-δ)) ^ ((β + M) / δ) = ε ^ (-(β + M)) := by
      rw [← Real.rpow_mul hε0.le]; congr 1; field_simp
    rw [hpow] at he
    have hsplit : ε ^ (-β) = ε ^ M * ε ^ (-(β + M)) := by
      rw [← Real.rpow_add hε0]; ring_nf
    have hAb : 0 < (A + 1) * b₀ := by positivity
    calc (A * ε ^ (-β) + 1) * (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC))
        ≤ ((A + 1) * ε ^ (-β)) * (b₀ * Real.exp (-b' * ε ^ (-δ))) := by
          refine mul_le_mul hpre (mul_le_mul_of_nonneg_left hexpb hb₀.le) (by positivity)
            (by positivity)
      _ = ε ^ M * (((A + 1) * b₀) * (ε ^ (-(β + M)) * Real.exp (-b' * ε ^ (-δ)))) := by
          rw [hsplit]; ring
      _ ≤ ε ^ M * (((A + 1) * b₀) * (1 / ((A + 1) * b₀))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hAb.le) (by positivity)
      _ = ε ^ M := by field_simp

/-- `c ε^{p} < 1` eventually as `ε → 0+`, for `p > 0` -/
theorem p412b_ev_small {c p : ℝ} (hp : 0 < p) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * ε ^ p < 1 := by
  have := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at this
  have h2 : Tendsto (fun x : ℝ => c * x ^ p) (𝓝[>] 0) (𝓝 0) := by
    have := (this.const_mul c).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [mul_zero] at this
  exact h2.eventually (Iio_mem_nhds one_pos)

/-- **GM l. 2266** ("for small enough `ε`"): the bound `A` of Lemma 4.16 plus `2r ≤ 2ε𝕣` is
below `ρ = (ε^κ/2)^{χ'/χ}𝕣` for small `ε`, when `κχ'/χ < min(χ/χ', 1)` (GM: `κ = ½(χ/χ')²`). -/
theorem p412b_small_A {χ χ' κ lam N : ℝ} (hχ : 0 < χ) (hχ' : 0 < χ')
    (he1 : κ * (χ' / χ) < χ / χ') (he2 : κ * (χ' / χ) < 1) (hN : 0 ≤ N) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₂, ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ r : ℝ, r ≤ ε * 𝕣 →
      2 * (𝕣 * (N * (ε / 4) ^ χ) ^ (1 / χ')) + 8 * lam * (ε * 𝕣) + 2 * r <
        (ε ^ κ / 2) ^ (χ' / χ) * 𝕣 := by
  set e := κ * (χ' / χ) with he
  set c₁ := (N + 1) ^ (1 / χ') with hc₁
  set c₃ := (1 / 2 : ℝ) ^ (χ' / χ) with hc₃
  have hc₃0 : 0 < c₃ := by positivity
  have h1 := p412b_ev_small (c := 4 * c₁ / c₃) (p := χ / χ' - e) (by linarith)
  have h2 := p412b_ev_small (c := 2 * (8 * lam + 2) / c₃) (p := 1 - e) (by linarith)
  have hlin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨ε₂, hε₂, hε₂'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 ((h1.and h2).and hlin)
  refine ⟨ε₂, hε₂, fun ε hε 𝕣 h𝕣 r hr => ?_⟩
  obtain ⟨⟨hs1, hs2⟩, hε0, hε1⟩ := hε₂' hε
  -- the Lemma 4.16 term
  have hA : (N * (ε / 4) ^ χ) ^ (1 / χ') ≤ c₁ * ε ^ (χ / χ') := by
    have hq : N * (ε / 4) ^ χ ≤ (N + 1) * ε ^ χ := by
      have : (ε / 4) ^ χ ≤ ε ^ χ :=
        Real.rpow_le_rpow (by positivity) (by linarith) hχ.le
      have h0 : 0 ≤ (ε / 4) ^ χ := by positivity
      nlinarith [Real.rpow_nonneg hε0.le χ]
    calc (N * (ε / 4) ^ χ) ^ (1 / χ') ≤ ((N + 1) * ε ^ χ) ^ (1 / χ') :=
          Real.rpow_le_rpow (by positivity) hq (by positivity)
      _ = c₁ * ε ^ (χ / χ') := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hε0.le]
          congr 2; field_simp
  have hρ : (ε ^ κ / 2) ^ (χ' / χ) = c₃ * ε ^ e := by
    rw [div_eq_mul_one_div, Real.mul_rpow (by positivity) (by norm_num), ← Real.rpow_mul hε0.le,
      mul_comm]
  have hsplit1 : ε ^ (χ / χ') = ε ^ e * ε ^ (χ / χ' - e) := by
    rw [← Real.rpow_add hε0]; ring_nf
  have hsplit2 : ε = ε ^ e * ε ^ (1 - e) := by
    rw [← Real.rpow_add hε0]; ring_nf; simp
  have hεe : 0 < ε ^ e := Real.rpow_pos_of_pos hε0 _
  have key : 2 * c₁ * ε ^ (χ / χ') + (8 * lam + 2) * ε < c₃ * ε ^ e := by
    have hs1' : 2 * c₁ * ε ^ (χ / χ' - e) < c₃ / 2 := by
      have := hs1; rw [div_mul_eq_mul_div, div_lt_one hc₃0] at this; linarith
    have hs2' : (8 * lam + 2) * ε ^ (1 - e) < c₃ / 2 := by
      have := hs2; rw [div_mul_eq_mul_div, div_lt_one hc₃0] at this; linarith
    have e1 : 2 * c₁ * ε ^ (χ / χ') = ε ^ e * (2 * c₁ * ε ^ (χ / χ' - e)) := by
      rw [hsplit1]; ring
    have e2 : (8 * lam + 2) * ε = ε ^ e * ((8 * lam + 2) * ε ^ (1 - e)) := by
      calc (8 * lam + 2) * ε = (8 * lam + 2) * (ε ^ e * ε ^ (1 - e)) := by rw [← hsplit2]
        _ = _ := by ring
    rw [e1, e2]
    nlinarith [mul_lt_mul_of_pos_left hs1' hεe, mul_lt_mul_of_pos_left hs2' hεe]
  rw [hρ]
  have hA' : 2 * (𝕣 * (N * (ε / 4) ^ χ) ^ (1 / χ')) ≤ 2 * c₁ * ε ^ (χ / χ') * 𝕣 := by
    nlinarith
  nlinarith

/-- `p412b_small_A` in the form of the hypothesis `hsmall` of `p412b_core` (the extra `2λ₂r`
of `p412b_ext_transfer`) -/
theorem p412b_small_A' {χ χ' κ lam lam2 N : ℝ} (hχ : 0 < χ) (hχ' : 0 < χ')
    (he1 : κ * (χ' / χ) < χ / χ') (he2 : κ * (χ' / χ) < 1) (hN : 0 ≤ N) (hlam2 : 0 ≤ lam2) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₂, ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ r ∈ Ioc 0 (ε * 𝕣),
      2 * (𝕣 * (N * (ε / 4) ^ χ) ^ (1 / χ')) + 8 * lam * (ε * 𝕣) + 2 * r <
        (ε ^ κ / 2) ^ (χ' / χ) * 𝕣 - 2 * (lam2 * r) := by
  obtain ⟨ε₂, hε₂, H⟩ := p412b_small_A (lam := lam + lam2 / 4) hχ hχ' he1 he2 hN
  refine ⟨ε₂, hε₂, fun ε hε 𝕣 h𝕣 r hr => ?_⟩
  have h1 := H ε hε 𝕣 h𝕣 r hr.2
  have h2 : lam2 * r ≤ lam2 * (ε * 𝕣) := mul_le_mul_of_nonneg_left hr.2 hlam2
  linarith

end LQGMetric.GM
