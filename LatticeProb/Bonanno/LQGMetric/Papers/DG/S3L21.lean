/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L21 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L21A
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13

/-!
# DG Lemma 3.21 (square-annulus distances, uniformly over the squares of side `δ_ε`) (P2-DG105i)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.21 (`lem-square-dist`,
DG:1678–1719). DG's proof:
1. (eqn-field-control') (DG:1693–1697) by Lemmas 3.5, 3.6 at `δ = ε^β`, `A = ε^β n_ε / δ_ε`;
2. by (3.7) and independence, the distance across `S(1) ∖ S` dominates the distance across
   `𝒜_{n_ε}` at `T_S ε` (DG:1699–1706), bounded below by Lemma 3.19 when `T_S ε ≤ ε_*`;
3. (eqn-square-dist-T) (DG:1708–1716; `l321_x_le`, `l321_tgt_le_thr`);
4. a union bound over `O(ε^{-2β})` squares (DG:1717–1718).

Step 2 (Lemma 3.19 transported to the annulus `S(1) ∖ S` at scale `δ_ε/n`, with DG's random
factor `T_S`) is the hypothesis `L321Hyp` (D105 item 1: Lemma 3.19 is stated for `δ𝒜_n + b`).
The squares are an abstract family (`u ∈ Λ ε`, `#Λ ε ≤ C ε^{-2β}`, `S1 ε u` = `S(1)` with
diameter `≤ C ε^β`).

Deviations: `n_ε = 2^{⌊log₂ ⌈log ε⁻¹⌉⌋ + J + 1} ≍ log ε⁻¹` (DG: `(log ε⁻¹)^{3/2}`; any `n_ε`
with `a₁ n_ε ≥ (2β+1) log ε⁻¹` and `n_ε = (log ε⁻¹)^{O(1)}` works), a power of `2` so that
`δ_ε/n_ε` is dyadic (needed by `ae_dgLGD_scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DG Lemma 3.19 at the annuli of Lemma 3.21** (DG:1699–1706): for each `ζ₁`, on
`{T_S ε ≤ ε_*}` the distance `D ε u` across `S(1) ∖ S` is `< e^{−√n} (T_S ε)^{-1/(d+ζ₁)}`,
`n = 2^k`, with probability `≤ a₀ e^{−a₁ n}` -/
def L321Hyp (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ d : ℝ) {ι : Type*} (Λ : ℝ → Finset ι)
    (Mf : ℝ → ℕ) (S1 : ℝ → ι → Set ℂ) (D : ℝ → ι → Ω → ℝ≥0∞) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ a₀ a₁ εs : ℝ, 0 < a₁ ∧ 0 < εs ∧ ∀ ε : ℝ, 0 < ε →
    ∀ u ∈ Λ ε, ∀ k : ℕ,
    P {ω | l321X γ ε (Mf ε) k
        (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (Mf ε + k)) 1 z ω) '' S1 ε u)) ≤ εs ∧
      D ε u ω < ENNReal.ofReal (l321Thr γ d ζ₁ ε (Mf ε) k
        (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (Mf ε + k)) 1 z ω) '' S1 ε u)))} ≤
      ENNReal.ofReal (a₀ * Real.exp (-(a₁ * 2 ^ k)))

/-- the event (eqn-field-control') gives DG's two bounds on `S(1)` (DG:1708–1712) -/
lemma l321_sup_inf {R : Set ℂ} (hne : R.Nonempty) {f g : ℂ → ℝ} {a b : ℝ}
    (hf : ∀ w ∈ R, |f w| ≤ a) (hfg : ∀ z ∈ R, ∀ w ∈ R, |g z - f w| ≤ b) :
    sSup (f '' R) - b ≤ sInf (g '' R) ∧ |sSup (f '' R)| ≤ a := by
  obtain ⟨w₀, hw₀⟩ := id hne
  have hbdd : BddAbove (f '' R) := ⟨a, by
    rintro _ ⟨w, hw, rfl⟩; linarith [le_abs_self (f w), hf w hw]⟩
  refine ⟨?_, abs_le.2 ⟨?_, csSup_le (hne.image f) ?_⟩⟩
  · have : sSup (f '' R) ≤ sInf (g '' R) + b := csSup_le (hne.image f) (by
      rintro _ ⟨w, hw, rfl⟩
      have : f w - b ≤ sInf (g '' R) := le_csInf (hne.image g) (by
        rintro _ ⟨z, hz, rfl⟩; linarith [neg_abs_le (g z - f w), hfg z hz w hw])
      linarith)
    linarith
  · exact le_trans (by linarith [neg_abs_le (f w₀), hf w₀ hw₀] : -a ≤ f w₀)
      (le_csSup hbdd ⟨w₀, hw₀, rfl⟩)
  · rintro _ ⟨w, hw, rfl⟩; linarith [le_abs_self (f w), hf w hw]

/-- DG's choice of `ζ̃` (DG:1716–1719): one small `t` serves as `ζ₁` and `ζ̃` -/
lemma l321_exists_param {γ d ζ β : ℝ} (hd : 1 ≤ d) (hζ : 0 < ζ)
    (hκ : 0 < 1 - β * (2 + γ ^ 2 / 2) - γ * 2 * β) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      1 / (d + t) * γ * t + t / d ^ 2 * (1 + γ * (2 + t) * β) ≤ ζ / 2 ∧
      0 < 1 - β * (2 + γ ^ 2 / 2) - γ * (2 + t) * β - γ * t := by
  have hd0 : 0 < d := by linarith
  have hc1 : ContinuousAt (fun t : ℝ => 1 / (d + t) * γ * t + t / d ^ 2 * (1 + γ * (2 + t) * β))
      0 := by
    have : (d + 0 : ℝ) ≠ 0 := by simpa using hd0.ne'
    have : d ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have hc2 : ContinuousAt (fun t : ℝ => 1 - β * (2 + γ ^ 2 / 2) - γ * (2 + t) * β - γ * t) 0 := by
    fun_prop
  have h1 := hc1.eventually (gt_mem_nhds (a := ζ / 2) (by simp; positivity))
  have h2 := hc2.eventually (lt_mem_nhds (a := 0) (by simpa [mul_comm, mul_assoc] using hκ))
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t ∧ t < 1 / 2 ∧
      1 / (d + t) * γ * t + t / d ^ 2 * (1 + γ * (2 + t) * β) < ζ / 2 ∧
      0 < 1 - β * (2 + γ ^ 2 / 2) - γ * (2 + t) * β - γ * t := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 2)), nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with t a b c e
    exact ⟨a, b, c, e⟩
  obtain ⟨t, a, b, c, e⟩ := hev.exists
  exact ⟨t, a, b.le, c.le, e⟩

/-- **DG Lemma 3.21** (DG:1678–1719), for an abstract family of squares: for
`β ∈ (0, 2/(2+γ)²)`, with polynomially high probability as `ε → 0`, for every `u ∈ Λ ε`,
`D ε u ≥ ε^{-1/d + β(2+γ²/2)/d + ζ} exp((γ/d) max_{S(1)} ĥ_{ε^β})` -/
theorem dg_lemma321_core (hW : IsWhiteNoise P W) {γ d β : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    (hβ : 0 < β) (hβγ : β < 2 / (2 + γ) ^ 2)
    {ι : Type*} {Λ : ℝ → Finset ι} {Cn : ℝ}
    (hΛ : ∀ ε, 0 < ε → ε < 1 → ((Λ ε).card : ℝ) ≤ Cn * ε ^ (-(2 * β)))
    {Mf : ℝ → ℕ} (hM1 : ∀ ε, 0 < ε → ε < 1 → (2 : ℝ)⁻¹ ^ Mf ε ≤ ε ^ β)
    (hM2 : ∀ ε, 0 < ε → ε < 1 → ε ^ β ≤ 2 * (2 : ℝ)⁻¹ ^ Mf ε)
    {S1 : ℝ → ι → Set ℂ} {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hSU : ∀ ε, ∀ u ∈ Λ ε, S1 ε u ⊆ U) (hSne : ∀ ε, ∀ u ∈ Λ ε, (S1 ε u).Nonempty)
    {Cd : ℝ} (hCd : 1 ≤ Cd)
    (hSd : ∀ ε, 0 < ε → ε < 1 → ∀ u ∈ Λ ε, ∀ z ∈ S1 ε u, ∀ w ∈ S1 ε u, ‖z - w‖ ≤ Cd * ε ^ β)
    {D : ℝ → ι → Ω → ℝ≥0∞} (hL : L321Hyp P W γ d Λ Mf S1 D) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P {ω | ∃ u ∈ Λ ε, D ε u ω < ENNReal.ofReal (l321Tgt γ d ζ β ε
        (sSup ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) '' S1 ε u)))} ≤
        ENNReal.ofReal (C * ε ^ p) := by
  have := hW.isProbabilityMeasure
  set ξ := 2 + γ ^ 2 / 2 with hξ
  have hβ2 : β * (2 + γ) ^ 2 < 2 := by rwa [lt_div_iff₀ (by positivity)] at hβγ
  have hκ0 : 0 < 1 - β * (2 + γ ^ 2 / 2) - γ * 2 * β := by
    have : β * (2 + γ) ^ 2 = 2 * (β * (2 + γ ^ 2 / 2) + γ * 2 * β) := by ring
    linarith
  obtain ⟨t, ht0, ht12, hpar, hκ⟩ := l321_exists_param (γ := γ) (β := β) hd hζ hκ0
  have ht1 : t < 1 := by linarith
  have hβξ : β * ξ ≤ 1 := by
    have : 0 ≤ γ * 2 * β := by positivity
    rw [hξ]; linarith
  have hβ1 : β ≤ 1 := by
    have h2 : 2 * β ≤ β * ξ := by
      have h2ξ : (2 : ℝ) ≤ ξ := le_add_of_nonneg_right (by positivity)
      calc 2 * β = β * 2 := by ring
        _ ≤ β * ξ := mul_le_mul_of_nonneg_left h2ξ hβ.le
    linarith
  obtain ⟨a₀, a₁, εs, ha₁, hεs, hLt⟩ := hL t ht0 ht1
  obtain ⟨K₅, δ₅, hδ₅, h35⟩ := dg_lemma35 hW hU ht0
  obtain ⟨K₆, δ₆, hδ₆, h36⟩ := dg_lemma36 hW hU ht0 ht1 hCd (p := 1) one_pos
  set L := Real.log 2 with hL_def
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt ((2 * β + 1) / a₁) (by norm_num : (1 : ℝ) < 2)
  have hJ' : 2 * β + 1 ≤ a₁ * 2 ^ J := by rw [div_lt_iff₀ ha₁] at hJ; linarith
  set c₂ : ℝ := 2 ^ (J + 3) with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  set κ := 1 - β * ξ - γ * (2 + t) * β - γ * t with hκdef
  set σ := min κ (ζ / 2) with hσ
  have hσ0 : 0 < σ := lt_min hκ (by positivity)
  set B := 1 + 2 * ξ with hB
  have hB0 : 0 < B := by positivity
  set B' := ξ * L + |Real.log εs| with hB'
  set ℓ₀ : ℝ := max (max (max 1 (1 / β)) (max (65 * c₂ / β ^ 2) (4 * B ^ 2 * c₂ / σ ^ 2)))
    (max (2 * B' / σ) (max (Real.log δ₅⁻¹ / β + 1) (Real.log δ₆⁻¹ / β + 1))) with hℓ₀
  refine ⟨β * t, |K₅| + |K₆| + |Cn| * |a₀|, Real.exp (-ℓ₀), by positivity, by positivity,
    fun ε hε hεlt => ?_⟩
  set ℓ := Real.log ε⁻¹ with hℓ
  have hℓgt : ℓ₀ < ℓ := by
    have := Real.log_lt_log hε hεlt
    rw [Real.log_exp] at this
    rw [hℓ, Real.log_inv]; linarith
  have hmax : ∀ x, x ≤ ℓ₀ → x < ℓ := fun x hx => hx.trans_lt hℓgt
  have h₀ : 1 ≤ ℓ₀ ∧ 1 / β ≤ ℓ₀ ∧ 65 * c₂ / β ^ 2 ≤ ℓ₀ ∧ 4 * B ^ 2 * c₂ / σ ^ 2 ≤ ℓ₀ ∧
      2 * B' / σ ≤ ℓ₀ ∧ Real.log δ₅⁻¹ / β + 1 ≤ ℓ₀ ∧ Real.log δ₆⁻¹ / β + 1 ≤ ℓ₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hℓ₀, le_max_iff, le_refl, true_or, or_true]
  obtain ⟨h01, h02, h03, h04, h05, h06, h07⟩ := h₀
  have hℓ1 : 1 < ℓ := hmax _ h01
  have hℓβ : 1 / β < ℓ := hmax _ h02
  have hℓ65 : 65 * c₂ / β ^ 2 < ℓ := hmax _ h03
  have hℓB : 4 * B ^ 2 * c₂ / σ ^ 2 < ℓ := hmax _ h04
  have hℓB' : 2 * B' / σ < ℓ := hmax _ h05
  have hℓ5 : Real.log δ₅⁻¹ / β + 1 < ℓ := hmax _ h06
  have hℓ6 : Real.log δ₆⁻¹ / β + 1 < ℓ := hmax _ h07
  have hlogε : Real.log ε = -ℓ := by rw [hℓ, Real.log_inv]; ring
  have hε1 : ε < 1 := by
    have : Real.log ε < 0 := by rw [hlogε]; linarith
    exact (Real.log_neg_iff hε).1 this
  have hεq : ∀ q : ℝ, ε ^ q = Real.exp (-(ℓ * q)) := fun q => by
    rw [Real.rpow_def_of_pos hε, hlogε]; ring_nf
  set M := Mf ε with hM
  -- `n = 2^k ≍ log ε⁻¹`
  set mℓ : ℕ := ⌈ℓ⌉₊ with hmℓ
  have hmℓ1 : 1 ≤ mℓ := Nat.one_le_ceil_iff.2 (by linarith)
  have hmℓ_ge : ℓ ≤ mℓ := Nat.le_ceil ℓ
  have hmℓ_le : (mℓ : ℝ) ≤ ℓ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  set k : ℕ := Nat.log 2 mℓ + (J + 1) with hk
  obtain ⟨hnlo, hnhi⟩ := l313_n_bounds J mℓ hmℓ1
  have hn_le : (2 : ℝ) ^ k ≤ 2 ^ (J + 2) * ℓ := by
    calc (2 : ℝ) ^ k ≤ 2 ^ (J + 1) * mℓ := hnhi
      _ ≤ 2 ^ (J + 1) * (2 * ℓ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hn_ge : (2 : ℝ) ^ J * ℓ ≤ 2 ^ k :=
    (mul_le_mul_of_nonneg_left hmℓ_ge (by positivity)).trans hnlo
  -- `δ = ε^β`
  set δ := ε ^ β with hδ
  have hδ0 : 0 < δ := by positivity
  have hlogδ : Real.log δ⁻¹ = β * ℓ := by
    rw [Real.log_inv, hδ, Real.log_rpow hε, hlogε]; ring
  have hδlt : ∀ δ' : ℝ, 0 < δ' → Real.log δ'⁻¹ / β + 1 < ℓ → δ < δ' := by
    intro δ' hδ' h
    rw [hδ, hεq, ← Real.exp_log hδ']
    refine Real.exp_lt_exp.2 ?_
    rw [div_add_one hβ.ne', div_lt_iff₀ hβ, Real.log_inv] at h
    linarith
  have hδ5 : δ < δ₅ := hδlt δ₅ hδ₅ hℓ5
  have hδ6 : δ < δ₆ := hδlt δ₆ hδ₆ hℓ6
  -- `A = ε^β n / δ_ε`
  set A : ℝ := δ * 2 ^ k * 2 ^ M with hA
  have h2M : (2 : ℝ)⁻¹ ^ M * 2 ^ M = 1 := by rw [← mul_pow]; norm_num
  have hδA : δ / A = (2 : ℝ)⁻¹ ^ (M + k) := by
    have : δ / (δ * 2 ^ k * 2 ^ M) = ((2 : ℝ) ^ (M + k))⁻¹ := by
      field_simp; ring
    rw [hA, this, inv_pow]
  have hδM1 : 1 ≤ δ * 2 ^ M := by
    have := mul_le_mul_of_nonneg_right (hM1 ε hε hε1) (by positivity : (0 : ℝ) ≤ 2 ^ M)
    rwa [h2M] at this
  have hδM2 : δ * 2 ^ M ≤ 2 := by
    have := mul_le_mul_of_nonneg_right (hM2 ε hε hε1) (by positivity : (0 : ℝ) ≤ 2 ^ M)
    rwa [mul_assoc, h2M, mul_one] at this
  have hA1 : 1 < A := by
    have h2k : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hA, mul_right_comm]
    calc (1 : ℝ) < 2 := by norm_num
      _ ≤ 1 * 2 ^ k := by rw [one_mul]; exact h2k
      _ ≤ δ * 2 ^ M * 2 ^ k := mul_le_mul_of_nonneg_right hδM1 (by positivity)
  have hA2 : A < Real.exp (Real.log δ⁻¹ ^ (1 - t)) := by
    have hAle : A ≤ c₂ * ℓ := by
      rw [hA, mul_right_comm]
      calc δ * 2 ^ M * 2 ^ k ≤ 2 * (2 ^ (J + 2) * ℓ) :=
            mul_le_mul hδM2 hn_le (by positivity) (by norm_num)
        _ = c₂ * ℓ := by rw [hc₂]; ring
    rw [hlogδ, mul_comm β ℓ]
    refine hAle.trans_lt (l313_lt_exp hc₂0 hβ ht12 ?_ ?_)
    · rw [div_lt_iff₀ hβ] at hℓβ; linarith
    · rw [div_lt_iff₀ (by positivity)] at hℓ65; linarith
  -- the deterministic inputs
  have hsqn : B * √((2 : ℝ) ^ k) ≤ σ * ℓ / 2 := by
    have h1 : B * √((2 : ℝ) ^ k) ≤ B * √(c₂ * ℓ) := by
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hB0.le
      have hJc : (2 : ℝ) ^ (J + 2) ≤ c₂ := by
        rw [hc₂]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc (2 : ℝ) ^ k ≤ 2 ^ (J + 2) * ℓ := hn_le
        _ ≤ c₂ * ℓ := mul_le_mul_of_nonneg_right hJc (by linarith)
    refine h1.trans ?_
    rw [div_lt_iff₀ (by positivity)] at hℓB
    have h2 : (B * √(c₂ * ℓ)) ^ 2 ≤ (σ * ℓ / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have : 4 * B ^ 2 * c₂ * ℓ ≤ σ ^ 2 * ℓ * ℓ :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      calc B ^ 2 * (c₂ * ℓ) = 4 * B ^ 2 * c₂ * ℓ / 4 := by ring
        _ ≤ σ ^ 2 * ℓ * ℓ / 4 := by linarith
        _ = (σ * ℓ / 2) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h2
  have hB'le : B' ≤ σ * ℓ / 2 := by
    rw [div_lt_iff₀ hσ0] at hℓB'; linarith
  have hkL : (k : ℝ) * L ≤ 2 * √((2 : ℝ) ^ k) := log_two_pow_le_sqrt k
  have hsn0 : 0 ≤ √((2 : ℝ) ^ k) := Real.sqrt_nonneg _
  have hσκ : σ ≤ κ := min_le_left _ _
  have hσζ : σ ≤ ζ / 2 := min_le_right _ _
  have hlogεs : -|Real.log εs| ≤ Real.log εs := neg_abs_le _
  have hξkL : ξ * (k * L) ≤ ξ * (2 * √((2 : ℝ) ^ k)) :=
    mul_le_mul_of_nonneg_left hkL (by positivity)
  have hσℓ : σ * ℓ ≤ ζ / 2 * ℓ := mul_le_mul_of_nonneg_right hσζ (by linarith)
  have hσℓ' : σ * ℓ ≤ κ * ℓ := mul_le_mul_of_nonneg_right hσκ (by linarith)
  have hn5 : √((2 : ℝ) ^ k) + ξ * (k * L) + ξ * L ≤ ζ / 2 * ℓ := by
    have : B * √((2 : ℝ) ^ k) = √((2 : ℝ) ^ k) + ξ * (2 * √((2 : ℝ) ^ k)) := by rw [hB]; ring
    have hL' : 0 ≤ |Real.log εs| := abs_nonneg _
    linarith
  have hs : -(κ * ℓ) + ξ * (k * L) + ξ * L ≤ Real.log εs := by
    have : B * √((2 : ℝ) ^ k) = √((2 : ℝ) ^ k) + ξ * (2 * √((2 : ℝ) ^ k)) := by rw [hB]; ring
    linarith
  -- events
  set E5 : Set Ω := {ω | ∃ z ∈ U, (2 + t) * Real.log δ⁻¹ < |DDDF.phiVer W P δ 1 z ω|}
  set E6 : Set Ω := {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ Cd * δ ∧
    t * Real.log δ⁻¹ < |DDDF.phiVer W P (δ / A) 1 z ω - DDDF.phiVer W P δ 1 w ω|}
  set Bv : ι → Set Ω := fun u => {ω | l321X γ ε M k
        (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (M + k)) 1 z ω) '' S1 ε u)) ≤ εs ∧
      D ε u ω < ENNReal.ofReal (l321Thr γ d t ε M k
        (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (M + k)) 1 z ω) '' S1 ε u)))}
  have hsub : {ω | ∃ u ∈ Λ ε, D ε u ω < ENNReal.ofReal (l321Tgt γ d ζ β ε
        (sSup ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) '' S1 ε u)))} ⊆
      E5 ∪ E6 ∪ ⋃ u ∈ Λ ε, Bv u := by
    rintro ω ⟨u, hu, hbad⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨h5, h6⟩, hB⟩ := hcon
    apply hB u hu
    simp only [E5, mem_ofPred_eq, not_exists, not_and, not_lt] at h5
    simp only [E6, mem_ofPred_eq, not_exists, not_and, not_lt] at h6
    rw [hlogδ] at h5 h6
    obtain ⟨hm, hMx⟩ := l321_sup_inf (hSne ε u hu)
      (f := fun z => DDDF.phiVer W P δ 1 z ω)
      (g := fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (M + k)) 1 z ω)
      (a := (2 + t) * β * ℓ) (b := t * ℓ)
      (fun w hw => by have := h5 w (hSU ε u hu hw); linarith)
      (fun z hz w hw => by
        have := h6 z (hSU ε u hu hz) w (hSU ε u hu hw) (hSd ε hε hε1 u hu z hz w hw)
        rw [hδA] at this
        have : t * (β * ℓ) ≤ t * ℓ :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (by linarith) hβ1) ht0.le
        linarith)
    refine ⟨l321_x_le hγ hβ.le hε hεs (hM2 ε hε hε1) hm hMx ?_, hbad.trans_le
      (ENNReal.ofReal_le_ofReal (l321_tgt_le_thr hγ hd ht0.le hβ.le hβξ hε hε1 (hM2 ε hε hε1) hm hMx
        hpar hn5))⟩
    convert hs using 3
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)).trans ?_
  have hεβt : ∀ q : ℝ, β * t ≤ q → ε ^ q ≤ ε ^ (β * t) := fun q hq =>
    Real.rpow_le_rpow_of_exponent_ge hε hε1.le hq
  have hβt1 : β * t ≤ β := mul_le_of_le_one_right hβ.le (by linarith)
  have hP5 : P E5 ≤ ENNReal.ofReal (|K₅| * ε ^ (β * t)) := by
    refine (h35 δ ⟨hδ0, hδ5⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hδ, ← Real.rpow_mul hε.le]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hP6 : P E6 ≤ ENNReal.ofReal (|K₆| * ε ^ (β * t)) := by
    refine (h36 δ ⟨hδ0, hδ6⟩ A hA1 hA2).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_one, hδ]
    exact mul_le_mul (le_abs_self _) (hεβt β hβt1) (by positivity) (abs_nonneg _)
  have hPB : ∑ u ∈ Λ ε, P (Bv u) ≤ ENNReal.ofReal (|Cn| * |a₀| * ε ^ (β * t)) := by
    have hb : ∀ u ∈ Λ ε, P (Bv u) ≤ ENNReal.ofReal (|a₀| * Real.exp (-(a₁ * 2 ^ k))) :=
      fun u hu => (hLt ε hε u hu k).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : ε ^ (-(2 * β)) * Real.exp (-(a₁ * 2 ^ k)) ≤ ε ^ (β * t) := by
      refine le_trans ?_ (hεβt 1 ((mul_le_of_le_one_right hβ.le ht1.le).trans hβ1))
      rw [hεq, hεq, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have e1 : a₁ * (2 ^ J * ℓ) ≤ a₁ * 2 ^ k := mul_le_mul_of_nonneg_left hn_ge ha₁.le
      have e2 : (2 * β + 1) * ℓ ≤ a₁ * 2 ^ J * ℓ :=
        mul_le_mul_of_nonneg_right hJ' (by linarith)
      have e3 : a₁ * (2 ^ J * ℓ) = a₁ * 2 ^ J * ℓ := by ring
      have e4 : -(ℓ * -(2 * β)) + -(a₁ * 2 ^ k) ≤ -(ℓ * 1) := by
        have : (2 * β + 1) * ℓ = 2 * β * ℓ + ℓ := by ring
        have : -(ℓ * -(2 * β)) = 2 * β * ℓ := by ring
        linarith
      linarith
    calc ((Λ ε).card : ℝ) * (|a₀| * Real.exp (-(a₁ * 2 ^ k)))
        ≤ |Cn| * ε ^ (-(2 * β)) * (|a₀| * Real.exp (-(a₁ * 2 ^ k))) :=
          mul_le_mul_of_nonneg_right ((hΛ ε hε hε1).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (by positivity))) (by positivity)
      _ = |Cn| * |a₀| * (ε ^ (-(2 * β)) * Real.exp (-(a₁ * 2 ^ k))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  calc P E5 + P E6 + ∑ u ∈ Λ ε, P (Bv u)
      ≤ ENNReal.ofReal (|K₅| * ε ^ (β * t)) + ENNReal.ofReal (|K₆| * ε ^ (β * t)) +
          ENNReal.ofReal (|Cn| * |a₀| * ε ^ (β * t)) := add_le_add (add_le_add hP5 hP6) hPB
    _ = ENNReal.ofReal ((|K₅| + |K₆| + |Cn| * |a₀|) * ε ^ (β * t)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end DG
end LQGMetric
