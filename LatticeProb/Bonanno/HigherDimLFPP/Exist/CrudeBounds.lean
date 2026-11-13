/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.CrudeBounds at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.SupBounds
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Quantile
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Scaling

/-!
# Lemma S, Lemma 3.4′ and the crude bounds on `λ_n` (packet P-X5b, targets T2 and T3)

Source: DGZ arXiv:2310.03996, Lemma 2.3(3),(4), (3.5), Lemma 3.4 and the first step of the proof
of Proposition 3.1 / Lemma 3.7(1); planning audit HA5, Details D4 (Lemma S, Lemma 3.4′, "Crude
bounds") and D10 (first step), finding G5.

Notation (HA5): `h_{m,n} = H_{2^{-n},2^{-m}}`, `h_n = h_{0,n}`, `B̄_r(0) = [-r, r]^d`
(`Osc.box 0 r`), `Ū = [-2,2]^d ⊇ closure U`, `D_n = D^ξ(h_n)` (`lfppDistance d ξ`),
`a^{(p)}_n` the lower `p`-quantile of the law of `D_n` (`LQGMetric.lowerQuantile`),
`λ_n = a^{(1/2)}_n`.

**Route.** HA5 derives Lemma S from a grid union bound and Lemma O, and Lemma 3.4′ from Lemma S by
the scaling of the field. Here both come directly from the band supremum bound of packet P-OSC
(`exists_bandSup_bounds`, expected supremum by chaining plus Borell–TIS), which applies to every
band on every box; with `V = log(b/a)`:

* for the band `h_{n-m,n}` (`1 ≤ m ≤ n`, `V = m log 2`) on `[-2,2]^d` (mesh `2^{-n}`,
  `ℓ = d log(4·2^n + 1) ≤ 4 d n log 2`) the expected-supremum term is `≤ K₀ √(mn)`
  (`Crude.supMean_band_le`), so for `s ≥ 2 K₀ √(mn)`
  `P(sup_{[-2,2]^d} |h_{n-m,n}| ≥ s) ≤ 2 exp(-s² / (32 m log 2))` (`exists_band_sup_tail`).

This bound has no `2^{nd}` prefactor; it implies the stated forms:

* `lemmaS` (HA5 Lemma S; DGZ (3.5)): `P[sup_{B̄₁(0)} h_m ≥ s] ≤ C 2^{md} e^{-s²/(Cm)}` for `s ≥ Cm`,
  and the same for `-h_m` (case `m = n`, `B̄₁ ⊆ B̄₂`);
* `lemma34'` (HA5 Lemma 3.4′, the free-parameter form of DGZ Lemma 3.4, finding G5):
  `P[sup_{B̄₂(0)} |h_{n-m,n}| ≥ t√(mn)] ≤ C 2^{nd} e^{-t²n/C}` for `t ≥ t₀`, `n > m ≥ 1`; its two
  corollaries `lemma34'_exp` (`≤ C e^{-n/C}` for `t ≥ t₁`) and `lemma34'_small` (`≤ δ` uniformly
  in `n > m ≥ 1` for `t ≥ t(δ)`); the sharper `lemma34'_sharp` (`≤ 2 exp(-t² n / (32 log 2))`,
  `n ≥ m ≥ 1`) and its event form `lemma34'_small_exists` (`∃ z ∈ [-2,2]^d` instead of a supremum);
* the crude bounds (HA5 D4 end, D10 first step; case `m = n`): `exists_crude_sup_tail`
  (`P[sup_{Ū} |h_n| ≥ A n] ≤ δ` for all `n ≥ 1`), `exists_crude_bounds` (packet form: some `A`
  with `P[sup_{Ū} |h_n| ≥ A n] < 1/4` for all `n ≥ 1`, hence `e^{-ξAn} ≤ λ_n ≤ e^{ξAn}`) and
  `exists_crude_lowerQuantile_bounds` (`e^{-|ξ|An} ≤ a^{(p)}_n ≤ e^{|ξ|An}` for each level
  `p ∈ (0,1)`).

The quantile step is the elementary `Crude.lowerQuantile_mem_Icc_of_measure_le`: if
`P(D ∉ [lo, hi]) ≤ δ` with `δ < p` and `δ ≤ 1 - p`, then `lo ≤ q_p(D) ≤ hi`. The weight comparison
`|log D(φ)| ≤ |ξ| sup_U |φ|` is packet P-X1's `exp_neg_le_lfppDistance`/`lfppDistance_le_exp`.

All statements quantify over every white noise and every continuous version, with constants
chosen before the realization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal

namespace HigherDimLFPP

namespace Crude

/-! ### Arithmetic -/

/-- `2 √(V/2) = √2 √V`. -/
theorem two_mul_sqrt_half (V : ℝ) : 2 * √(V / 2) = √2 * √V := by
  have e1 : (2 : ℝ) = √4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc 2 * √(V / 2) = √4 * √(V / 2) := by rw [← e1]
    _ = √(4 * (V / 2)) := (Real.sqrt_mul (by norm_num) _).symm
    _ = √(2 * V) := by congr 1; ring
    _ = √2 * √V := Real.sqrt_mul (by norm_num) _

/-- The constant `c₁ = 2 √(π² d L / 8)` of `SupB.supMean`. -/
def cOne (d : ℕ) (L : ℝ) : ℝ := 2 * √(π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8)

theorem cOne_nonneg (d : ℕ) (L : ℝ) : 0 ≤ cOne d L := by
  unfold cOne
  positivity

/-- `supMean` in factored form: `supMean d L V ℓ = (√2 √V + c₁) √(1+ℓ) + blockConst`. -/
theorem supMean_eq (d : ℕ) (L V ℓ : ℝ) :
    SupB.supMean d L V ℓ =
      (√2 * √V + cOne d L) * √(1 + ℓ) + Osc.blockConst d L √(d : ℝ) := by
  unfold SupB.supMean cOne
  rw [mul_assoc 2 (√(1 + ℓ)) (√(V / 2)), mul_comm (√(1 + ℓ)) (√(V / 2)), ← mul_assoc,
    two_mul_sqrt_half]
  ring

/-- The constant `K₀ = (√(2 log 2) + c₁) √(1 + 4 d log 2) + blockConst` of the band bound. -/
def bandConst (d : ℕ) (L : ℝ) : ℝ :=
  (√2 * √(Real.log 2) + cOne d L) * √(1 + 4 * d * Real.log 2) + Osc.blockConst d L √(d : ℝ)

theorem bandConst_pos (d : ℕ) (L : ℝ) : 0 < bandConst d L := by
  unfold bandConst
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : 0 < √2 * √(Real.log 2) := mul_pos (Real.sqrt_pos.2 two_pos) (Real.sqrt_pos.2 hlog)
  have h2 : 0 < √(1 + 4 * d * Real.log 2) := Real.sqrt_pos.2 (by positivity)
  have h3 := cOne_nonneg d L
  have h4 := Osc.blockConst_nonneg d (L := L) (Real.sqrt_nonneg (d : ℝ))
  have h5 : 0 < (√2 * √(Real.log 2) + cOne d L) * √(1 + 4 * d * Real.log 2) :=
    mul_pos (by linarith) h2
  linarith

/-- The grid exponent of `[-2,2]^d` at mesh `2^{-n}`: `d log(2·2/2^{-n} + 1) ≤ 4 d n log 2`
for `n ≥ 1`. -/
theorem ell_le (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (d : ℝ) * Real.log (2 * 2 / ((2 : ℝ) ^ n)⁻¹ + 1) ≤ 4 * d * n * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h1 : 2 * 2 / ((2 : ℝ) ^ n)⁻¹ + 1 ≤ (2 : ℝ) ^ (n + 3) := by
    rw [div_inv_eq_mul, pow_add]
    norm_num
    linarith
  have h2 : Real.log (2 * 2 / ((2 : ℝ) ^ n)⁻¹ + 1) ≤ ((n + 3 : ℕ) : ℝ) * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : ((n + 3 : ℕ) : ℝ) * Real.log 2 ≤ 4 * n * Real.log 2 := by
    push_cast
    nlinarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc (d : ℝ) * Real.log (2 * 2 / ((2 : ℝ) ^ n)⁻¹ + 1) ≤ d * (4 * n * Real.log 2) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hd0
    _ = 4 * d * n * Real.log 2 := by ring

/-- **The expected-supremum term for the band `h_{n-m,n}` on `[-2,2]^d`** (`1 ≤ m ≤ n`):
`supMean d L (m log 2) (d log(2·2/2^{-n} + 1)) ≤ K₀ √(mn)`. -/
theorem supMean_band_le (d : ℕ) (L : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    SupB.supMean d L (m * Real.log 2) (d * Real.log (2 * 2 / ((2 : ℝ) ^ n)⁻¹ + 1)) ≤
      bandConst d L * √((m : ℝ) * n) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn : 1 ≤ n := hm.trans hmn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set ℓ : ℝ := d * Real.log (2 * 2 / ((2 : ℝ) ^ n)⁻¹ + 1) with hℓ
  have hℓle := ell_le d hn
  rw [← hℓ] at hℓle
  have hsm : 1 ≤ √(m : ℝ) := Real.one_le_sqrt.2 hm'
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 hn'
  have hsmn : √((m : ℝ) * n) = √(m : ℝ) * √(n : ℝ) := Real.sqrt_mul (by positivity) _
  -- `√(1 + ℓ) ≤ √(1 + 4 d log 2) √n`
  have h1ℓ : √(1 + ℓ) ≤ √(1 + 4 * d * Real.log 2) * √(n : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : (0 : ℝ) ≤ 4 * d * Real.log 2 := by positivity
    nlinarith
  -- `√(m log 2) = √m √(log 2)`
  have hV : √((m : ℝ) * Real.log 2) = √(m : ℝ) * √(Real.log 2) :=
    Real.sqrt_mul (Nat.cast_nonneg m) _
  rw [supMean_eq, hV]
  have hc := cOne_nonneg d L
  have hB := Osc.blockConst_nonneg d (L := L) (Real.sqrt_nonneg (d : ℝ))
  have hs2 := Real.sqrt_nonneg (2 : ℝ)
  have hsl := Real.sqrt_nonneg (Real.log 2)
  have hsq := Real.sqrt_nonneg (1 + 4 * d * Real.log 2)
  set A : ℝ := √(1 + 4 * d * Real.log 2) with hA
  set x : ℝ := √(m : ℝ) with hx
  set y : ℝ := √(n : ℝ) with hy
  have hxy : 1 ≤ x * y := by nlinarith
  unfold bandConst
  rw [← hA, hsmn]
  -- `(√2 x √log2 + c₁) √(1+ℓ) + B ≤ ((√2 √log2 + c₁) A + B) x y`
  calc (√2 * (x * √(Real.log 2)) + cOne d L) * √(1 + ℓ) + Osc.blockConst d L √(d : ℝ)
      ≤ (√2 * (x * √(Real.log 2)) + cOne d L) * (A * y) + Osc.blockConst d L √(d : ℝ) := by
        gcongr
    _ ≤ ((√2 * √(Real.log 2) + cOne d L) * A + Osc.blockConst d L √(d : ℝ)) * (x * y) := by
        have e : (√2 * (x * √(Real.log 2)) + cOne d L) * (A * y) =
            √2 * √(Real.log 2) * A * (x * y) + cOne d L * A * y := by ring
        rw [e]
        have h1 : cOne d L * A * y ≤ cOne d L * A * (x * y) := by
          have : y ≤ x * y := by nlinarith
          exact mul_le_mul_of_nonneg_left this (mul_nonneg hc hsq)
        have h2 : Osc.blockConst d L √(d : ℝ) ≤ Osc.blockConst d L √(d : ℝ) * (x * y) :=
          le_mul_of_one_le_right hB hxy
        nlinarith

/-- The band `h_{n-m,n} = H_{2^{-n},2^{-(n-m)}}` has `b/a = 2^m`. -/
theorem band_div (m n : ℕ) (hmn : m ≤ n) :
    ((2 : ℝ) ^ (n - m))⁻¹ / ((2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left, pow_add]
  field_simp

/-- `2^{-n} ≤ 2^{-(n-m)}`. -/
theorem band_le (m n : ℕ) : ((2 : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ (n - m))⁻¹ :=
  inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n m))

/-- `log(b/a) = m log 2` for the band `h_{n-m,n}`. -/
theorem log_band_div (m n : ℕ) (hmn : m ≤ n) :
    Real.log (((2 : ℝ) ^ (n - m))⁻¹ / ((2 : ℝ) ^ n)⁻¹) = m * Real.log 2 := by
  rw [band_div m n hmn, Real.log_pow]

/-! ### Suprema over compact sets -/

/-- If `s ≤ sup_T f` for a continuous `f` on a nonempty compact `T`, then `s ≤ f z` for some
`z ∈ T` (the supremum is attained). -/
theorem exists_le_of_le_iSup {d : ℕ} {T : Set (Rd d)} (hT : IsCompact T) (hne : T.Nonempty)
    {f : Rd d → ℝ} (hf : Continuous f) {s : ℝ} (h : s ≤ ⨆ z : T, f z) : ∃ z ∈ T, s ≤ f z := by
  obtain ⟨x, hxT, hx⟩ := hT.exists_isMaxOn hne hf.continuousOn
  have : Nonempty T := ⟨⟨x, hxT⟩⟩
  exact ⟨x, hxT, h.trans (ciSup_le fun z => hx z.2)⟩

/-! ### Quantiles from two-sided bounds -/

section Quantile

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Quantiles from a two-sided bound**: if `P(D < lo or hi < D) ≤ δ` with `δ < p` and
`δ ≤ 1 - p`, then `lo ≤ q_p(D) ≤ hi`. -/
theorem lowerQuantile_mem_Icc_of_measure_le [IsProbabilityMeasure P] {D : Ω → ℝ}
    (hD : AEMeasurable D P) {lo hi : ℝ} {p δ : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1)
    (hδp : δ < p) (hδq : δ ≤ 1 - p) (hbad : P {ω | D ω < lo ∨ hi < D ω} ≤ δ) :
    lo ≤ LQGMetric.lowerQuantile (P.map D) p ∧ LQGMetric.lowerQuantile (P.map D) p ≤ hi := by
  set μ : Measure ℝ := P.map D with hμ
  constructor
  · by_contra hlt
    push Not at hlt
    have hq := LQGMetric.isQuantile_lowerQuantile (μ := μ) hp0 hp1
    have h1 : μ (Iic (LQGMetric.lowerQuantile μ p)) ≤ δ := by
      rw [hμ, Measure.map_apply_of_aemeasurable hD measurableSet_Iic]
      refine (measure_mono fun ω hω => ?_).trans hbad
      exact Or.inl (lt_of_le_of_lt hω hlt)
    exact absurd (hq.1.trans h1) (not_le.2 hδp)
  · refine (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1).1 ?_
    have hIoi : μ (Ioi hi) ≤ δ := by
      rw [hμ, Measure.map_apply_of_aemeasurable hD measurableSet_Ioi]
      refine (measure_mono fun ω hω => ?_).trans hbad
      exact Or.inr hω
    have hsum : μ (Iic hi) + μ (Ioi hi) = 1 := by
      rw [← compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ]
    have hpδ : p + δ ≤ 1 := by
      calc p + δ ≤ p + (1 - p) := add_le_add le_rfl hδq
        _ = 1 := add_tsub_cancel_of_le hp1.le
    have hδtop : δ ≠ ⊤ := (hδp.trans_le le_top).ne
    refine ENNReal.le_of_add_le_add_right (a := δ) hδtop ?_
    calc p + δ ≤ 1 := hpδ
      _ = μ (Iic hi) + μ (Ioi hi) := hsum.symm
      _ ≤ μ (Iic hi) + δ := add_le_add le_rfl hIoi

end Quantile

/-! ### Exponential tails -/

/-- For `c > 0` and `δ > 0` there is `T > 0` with `2 exp(-t² n / c) ≤ δ` for all `t ≥ T` and
`n ≥ 1`. -/
theorem exists_two_mul_exp_le {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → ∀ n : ℝ, 1 ≤ n → 2 * Real.exp (-(t ^ 2 * n / c)) ≤ δ := by
  set T : ℝ := √(c * |Real.log (2 / δ)|) + 1 with hT
  have hT0 : 0 < T := by positivity
  refine ⟨T, hT0, fun t ht n hn => ?_⟩
  have hT2 : c * Real.log (2 / δ) ≤ T ^ 2 := by
    have h1 : c * Real.log (2 / δ) ≤ c * |Real.log (2 / δ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hc.le
    have h2 : c * |Real.log (2 / δ)| = √(c * |Real.log (2 / δ)|) ^ 2 :=
      (Real.sq_sqrt (by positivity)).symm
    have h3 : √(c * |Real.log (2 / δ)|) ^ 2 ≤ T ^ 2 := by
      have := Real.sqrt_nonneg (c * |Real.log (2 / δ)|)
      nlinarith
    linarith
  have ht2 : T ^ 2 ≤ t ^ 2 * n := by
    have h1 : T ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hT0.le ht 2
    have h2 : t ^ 2 ≤ t ^ 2 * n := le_mul_of_one_le_right (sq_nonneg t) hn
    linarith
  have hlog : Real.log (2 / δ) ≤ t ^ 2 * n / c := by
    rw [le_div_iff₀ hc]
    linarith
  calc 2 * Real.exp (-(t ^ 2 * n / c)) ≤ 2 * Real.exp (-Real.log (2 / δ)) := by
        gcongr
    _ = δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
        field_simp

/-! ### Levels -/

/-- `ofReal δ < p` for `0 ≤ δ < p.toReal`. -/
theorem ofReal_lt_of_lt_toReal {p : ℝ≥0∞} (hp1 : p < 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : δ < p.toReal) : ENNReal.ofReal δ < p :=
  (ENNReal.ofReal_lt_iff_lt_toReal hδ (hp1.trans ENNReal.one_lt_top).ne).2 h

/-- `1 - p = ofReal (1 - p.toReal)` for `p < 1`. -/
theorem one_sub_eq_ofReal {p : ℝ≥0∞} (hp1 : p < 1) : 1 - p = ENNReal.ofReal (1 - p.toReal) := by
  rw [ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (hp1.trans ENNReal.one_lt_top).ne]

/-- `0 < p.toReal < 1` for `0 < p < 1`. -/
theorem toReal_mem_Ioo {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) : 0 < p.toReal ∧ p.toReal < 1 := by
  have hptop : p ≠ ⊤ := (hp1.trans ENNReal.one_lt_top).ne
  refine ⟨ENNReal.toReal_pos hp0.ne' hptop, ?_⟩
  have h := (ENNReal.toReal_lt_toReal hptop ENNReal.one_ne_top).2 hp1
  rwa [ENNReal.toReal_one] at h

/-- `log 2 ≤ 1`. -/
theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
  linarith

end Crude

open Crude

variable {d : ℕ}

/-! ### The band `h_{n-m,n}` on `[-2,2]^d` -/

/-- **Sup tail of the band `h_{n-m,n}` on `[-2,2]^d`** (HA5 D4, Lemma 3.4′ with explicit constants;
the case `m = n` gives Lemma S and the crude bounds): there is `K > 0`, depending only on `κ` and
`d`, such that for every white noise, `1 ≤ m ≤ n`, every continuous version `H` of
`h_{n-m,n} = H_{2^{-n},2^{-(n-m)}}` and `s ≥ K √(mn)`,
`P*(∃ z ∈ [-2,2]^d, s ≤ |H z|) ≤ 2 exp(-s² / (32 m log 2))`. -/
theorem exists_band_sup_tail [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → ∀ {H : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ ((2 : ℝ) ^ (n - m))⁻¹ H → ∀ {s : ℝ},
          K * √((m : ℝ) * n) ≤ s →
          P {ω | ∃ z ∈ Osc.box (0 : Rd d) 2, s ≤ |H z ω|} ≤
            ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / (32 * m * Real.log 2)))) := by
  obtain ⟨L, hL0, hL⟩ := exists_bandSup_bounds hκ
  refine ⟨2 * bandConst d L, by linarith [bandConst_pos d L], ?_⟩
  intro Ω _ P W hW m n hm hmn H hH s hs
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hm.trans hmn
  have hmn1 : 1 ≤ √((m : ℝ) * n) := Real.one_le_sqrt.2 (by nlinarith)
  have hK0 := bandConst_pos d L
  have hs0 : 0 < s := lt_of_lt_of_le (by nlinarith) hs
  set V : ℝ := m * Real.log 2 with hVdef
  have hV : 0 < V := by positivity
  have hbV : Real.log (((2 : ℝ) ^ (n - m))⁻¹ / ((2 : ℝ) ^ n)⁻¹) ≤ V :=
    (log_band_div m n hmn).le
  obtain ⟨-, -, -, htail⟩ := hL hW (by positivity) (band_le m n) hH hV hbV (0 : Rd d)
    (R := 2) (by norm_num)
  set M : ℝ := SupB.supMean d L V (d * Real.log (2 * 2 / ((2 : ℝ) ^ n)⁻¹ + 1)) with hM
  have hMle : M ≤ bandConst d L * √((m : ℝ) * n) := supMean_band_le d L hm hmn
  have hu : 0 ≤ s / 4 := by positivity
  have e : -(s / 4) ^ 2 / (2 * V) = -(s ^ 2 / (32 * m * Real.log 2)) := by
    rw [hVdef, div_pow, neg_div, div_div]
    congr 2
    ring
  refine (measure_mono fun ω hω => ?_).trans ((htail hu).trans (le_of_eq ?_))
  · obtain ⟨z, hz, hle⟩ := hω
    refine ⟨z, hz, lt_of_lt_of_le ?_ hle⟩
    linarith
  · rw [e]

/-! ### Lemma 3.4′ -/

/-- **Lemma 3.4′, sharp form** (HA5 D4): there is `t₀ > 0`, depending only on `κ` and `d`, such
that for every white noise, `1 ≤ m ≤ n`, every continuous version `H` of
`h_{n-m,n} = H_{2^{-n},2^{-(n-m)}}` and `t ≥ t₀`,
`P*(∃ z ∈ [-2,2]^d, t √(mn) ≤ |H z|) ≤ 2 exp(-t² n / (32 log 2))`. -/
theorem lemma34'_sharp [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → ∀ {H : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ ((2 : ℝ) ^ (n - m))⁻¹ H → ∀ {t : ℝ}, t₀ ≤ t →
          P {ω | ∃ z ∈ Osc.box (0 : Rd d) 2, t * √((m : ℝ) * n) ≤ |H z ω|} ≤
            ENNReal.ofReal (2 * Real.exp (-(t ^ 2 * n / (32 * Real.log 2)))) := by
  obtain ⟨K, hK0, hK⟩ := exists_band_sup_tail hκ
  refine ⟨K, hK0, ?_⟩
  intro Ω _ P W hW m n hm hmn H hH t ht
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : 0 ≤ √((m : ℝ) * n) := Real.sqrt_nonneg _
  have h := hK hW hm hmn hH (s := t * √((m : ℝ) * n)) (mul_le_mul_of_nonneg_right ht hsq)
  have e : (t * √((m : ℝ) * n)) ^ 2 / (32 * m * Real.log 2) = t ^ 2 * n / (32 * Real.log 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rwa [e] at h

/-- **Lemma 3.4′, small-probability form, `∃` version** (HA5 D4, finding G5): for every `δ > 0`
there is `t(δ) > 0` such that for every white noise, `1 ≤ m ≤ n`, every continuous version `H` of
`h_{n-m,n}` and `t ≥ t(δ)`, `P*(∃ z ∈ [-2,2]^d, t √(mn) ≤ |H z|) ≤ δ`. -/
theorem lemma34'_small_exists [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ tδ : ℝ, 0 < tδ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → ∀ {H : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ ((2 : ℝ) ^ (n - m))⁻¹ H → ∀ {t : ℝ}, tδ ≤ t →
          P {ω | ∃ z ∈ Osc.box (0 : Rd d) 2, t * √((m : ℝ) * n) ≤ |H z ω|} ≤
            ENNReal.ofReal δ := by
  obtain ⟨t₀, ht₀, h₀⟩ := lemma34'_sharp hκ
  have hc : (0 : ℝ) < 32 * Real.log 2 := by positivity
  obtain ⟨T, hT0, hT⟩ := exists_two_mul_exp_le hc hδ
  refine ⟨max t₀ T, lt_max_of_lt_left ht₀, ?_⟩
  intro Ω _ P W hW m n hm hmn H hH t ht
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hm.trans hmn
  exact (h₀ hW hm hmn hH ((le_max_left _ _).trans ht)).trans
    (ENNReal.ofReal_le_ofReal (hT t ((le_max_right _ _).trans ht) n hn))

/-! ### Lemma S -/

/-! ### Crude bounds -/

/-- **Crude supremum bound** (HA5 D4 end, D10 first step): for every `δ > 0` there is `A > 0`,
depending only on `κ`, `d` and `δ`, such that for every white noise, every `n ≥ 1` and every
continuous version `H` of `h_n = H_{2^{-n},1}`, `P*(∃ z ∈ [-2,2]^d, A n ≤ |H z|) ≤ δ`. -/
theorem exists_crude_sup_tail [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {n : ℕ}, 1 ≤ n → ∀ {H : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H →
          P {ω | ∃ z ∈ Osc.box (0 : Rd d) 2, A * n ≤ |H z ω|} ≤ ENNReal.ofReal δ := by
  obtain ⟨tδ, htδ, h⟩ := lemma34'_small_exists hκ hδ
  refine ⟨tδ, htδ, ?_⟩
  intro Ω _ P W hW n hn H hH
  have hH' : IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ ((2 : ℝ) ^ (n - n))⁻¹ H :=
    hH.congr_band rfl (by rw [Nat.sub_self, pow_zero, inv_one])
  have e : tδ * √((n : ℝ) * n) = tδ * n := by rw [Real.sqrt_mul_self (Nat.cast_nonneg n)]
  have h' := h hW hn le_rfl hH' le_rfl
  rwa [e] at h'

/-- On the event `|φ| < A n` on `[-2,2]^d`, the frozen distance satisfies
`e^{-|ξ| A n} ≤ D^ξ(φ) ≤ e^{|ξ| A n}`; contrapositive form for the bad event. -/
theorem Crude.bad_subset {Ω : Type*} {H : Rd d → Ω → ℝ} (hd : 0 < d)
    (hc : ∀ ω, Continuous fun z => H z ω) (ξ M : ℝ) :
    {ω | lfppDistance d ξ (fun z => H z ω) < Real.exp (-(|ξ| * M)) ∨
        Real.exp (|ξ| * M) < lfppDistance d ξ (fun z => H z ω)} ⊆
      {ω | ∃ z ∈ Osc.box (0 : Rd d) 2, M ≤ |H z ω|} := by
  intro ω hω
  by_contra hno
  have hM : ∀ z ∈ cube d, |H z ω| ≤ M := fun z hz =>
    le_of_not_ge fun h => hno ⟨z, Osc.closure_cube_subset_box (subset_closure hz), h⟩
  rcases hω with h | h
  · exact absurd (exp_neg_le_lfppDistance hd (hc ω) hM) (not_le.2 h)
  · exact absurd (lfppDistance_le_exp hd (hc ω) hM) (not_le.2 h)

/-- **Crude bounds for all quantiles** (HA5 D4/D10, D9 last paragraph): for every level
`p ∈ (0,1)` there is `A > 0`, depending only on `κ`, `d` and `p`, such that for every `ξ`, every
white noise, every `n ≥ 1` and every continuous version `H` of `h_n`,
`e^{-|ξ| A n} ≤ a^{(p)}_n ≤ e^{|ξ| A n}`. -/
theorem exists_crude_lowerQuantile_bounds [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ξ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WN d → Ω → ℝ}, IsWhiteNoise P W → ∀ {n : ℕ}, 1 ≤ n → ∀ {H : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H →
          Real.exp (-(|ξ| * A * n)) ≤
              LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p ∧
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p ≤
              Real.exp (|ξ| * A * n) := by
  obtain ⟨hr0, hr1⟩ := toReal_mem_Ioo hp0 hp1
  set δ : ℝ := min p.toReal (1 - p.toReal) / 2 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < min p.toReal (1 - p.toReal) := lt_min hr0 (by linarith)
    positivity
  have hδp : δ < p.toReal := by
    have := min_le_left p.toReal (1 - p.toReal)
    linarith
  have hδq : δ ≤ 1 - p.toReal := by
    have := min_le_right p.toReal (1 - p.toReal)
    have : 0 ≤ min p.toReal (1 - p.toReal) := le_min hr0.le (by linarith)
    linarith
  obtain ⟨A, hA0, hA⟩ := exists_crude_sup_tail hκ hδ0
  refine ⟨A, hA0, ?_⟩
  intro ξ Ω _ P W hW n hn H hH
  have := hW.isProbabilityMeasure
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hbad := (measure_mono (Crude.bad_subset hd hH.continuous ξ (A * n))).trans (hA hW hn hH)
  rw [← mul_assoc] at hbad
  exact lowerQuantile_mem_Icc_of_measure_le (hH.measurable_lfppDistance ξ).aemeasurable hp0 hp1
    (ofReal_lt_of_lt_toReal hp1 hδ0.le hδp)
    (by rw [one_sub_eq_ofReal hp1]; exact ENNReal.ofReal_le_ofReal hδq) hbad

/-- **The crude bounds** (HA5 D4 end and D10 first step; DGZ Lemma 3.7(1), crude form), packet
form: there is `A > 0`, depending only on `κ` and `d`, such that for every white noise, every
`n ≥ 1` and every continuous version `H` of `h_n = H_{2^{-n},1}`,
`P*[sup_{Ū} |h_n| ≥ A n] < 1/4` (`Ū = closure U`), hence for every `ξ > 0` the lower median
`λ_n` of `D_n = D^ξ(h_n)` satisfies `e^{-ξAn} ≤ λ_n ≤ e^{ξAn}`. -/
theorem exists_crude_bounds [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {n : ℕ}, 1 ≤ n → ∀ {H : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H →
          P {ω | A * n ≤ ⨆ z : closure (cube d), |H z ω|} < ENNReal.ofReal (1 / 4) ∧
          ∀ ξ : ℝ, 0 < ξ →
            Real.exp (-(ξ * A * n)) ≤
                LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) 2⁻¹ ∧
              LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) 2⁻¹ ≤
                Real.exp (ξ * A * n) := by
  obtain ⟨A, hA0, hA⟩ := exists_crude_sup_tail hκ (δ := 1 / 8) (by norm_num)
  refine ⟨A, hA0, ?_⟩
  intro Ω _ P W hW n hn H hH
  have := hW.isProbabilityMeasure
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hbox := hA hW hn hH
  have hcl : IsCompact (closure (cube d)) :=
    (Osc.isCompact_box (0 : Rd d) 2).of_isClosed_subset isClosed_closure
      Osc.closure_cube_subset_box
  have hne : (closure (cube d)).Nonempty := ⟨0, subset_closure (zero_mem_cube d)⟩
  refine ⟨?_, fun ξ hξ => ?_⟩
  · refine lt_of_le_of_lt ((measure_mono fun ω hω => ?_).trans hbox)
      ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num))
    obtain ⟨z, hz, hle⟩ := exists_le_of_le_iSup hcl hne (hH.continuous ω).abs hω
    exact ⟨z, Osc.closure_cube_subset_box hz, hle⟩
  · have hbad := (measure_mono (Crude.bad_subset hd hH.continuous ξ (A * n))).trans hbox
    rw [← mul_assoc, abs_of_pos hξ] at hbad
    have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    have hp0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
    have hp1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 (by norm_num)
    refine lowerQuantile_mem_Icc_of_measure_le (hH.measurable_lfppDistance ξ).aemeasurable hp0
      hp1 ?_ ?_ hbad
    · rw [h2]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
    · rw [ENNReal.one_sub_inv_two, h2]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

end HigherDimLFPP
