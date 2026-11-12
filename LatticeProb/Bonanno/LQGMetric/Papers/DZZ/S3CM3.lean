/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1

/-!
# DZZ (eq-very-crude-prime): `E (log D'_{γ,δ}(A, B))² = O((log δ⁻¹)²)` (P2-DZZCM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 849–853): "an argument similar to that employed in
the proof of Lemma 3.1 shows that the tail of the distribution of `log(S_δ)/log δ` decays at
least exponentially, where `S_δ` is the side length of the minimal cell in `𝒱_δ`. This implies
… (eq-very-crude-prime)". We follow this: with `K = j₀ + m`, `j₀ = ⌈2p log δ⁻¹/(q log 2)⌉`,
DZZ's union bound over the level-`K` boxes (eq-010518a) (as in `l31_min_level`, Chernoff exponent
`p = l31p γ`, gap `q = l31q γ > 0`) gives `P(∃ B of level K, M(B) ≥ δ²) ≤ e^{C₀} e^{-q m log 2}`;
off this event every cell has level `≤ K`, hence `D'(A, B) ≤ (K+1) 4^K ≤ 8^K` (a geodesic visits
distinct cells; `approxDistSet_toNat_le`). The tail sum is `lintegral_sq_le_of_geom`. The bound
holds for arbitrary sets `A, B` (the admissibility of the pair is not used).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma cm_succ_mul_le_eight_pow (K : ℕ) : (K + 1) * 2 ^ K * 2 ^ K ≤ 8 ^ K := by
  have h1 : K + 1 ≤ 2 ^ K := Nat.lt_two_pow_self
  calc (K + 1) * 2 ^ K * 2 ^ K ≤ 2 ^ K * 2 ^ K * 2 ^ K := by gcongr
    _ = 8 ^ K := by rw [← mul_pow, ← mul_pow]; norm_num

/-- the level-`K` union bound (DZZ (eq-010518a)): `P(∃ B of level K, M(B) ≥ δ²) ≤
`exp(-q K log 2 + 2p log δ⁻¹ + 2p(p-1)γ²)` -/
lemma cm_level_bound [IsProbabilityMeasure P] (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {δ : ℝ} (hδ0 : 0 < δ) (K : ℕ) :
    P.real {ω | ∃ b : DyBox, b.n = K ∧ ω ∈ {ω | δ ^ 2 ≤ approxLQG γ W ω b}} ≤
      Real.exp (-(l31q γ * (K * Real.log 2)) + 2 * l31p γ * Real.log δ⁻¹ +
        2 * l31p γ * (l31p γ - 1) * γ ^ 2) := by
  set p := l31p γ with hpdef
  have hp : 1 ≤ p := by
    rw [hpdef, l31p, le_div_iff₀ (by positivity)]; nlinarith
  set l := Real.log 2
  refine (measureReal_level_le K _ (B := Real.exp (2 * p * (-(K * l) - Real.log δ) +
      p * (p - 1) * γ ^ 2 / 2 * (-(-(K * l)) + 4))) fun b hb => ?_).trans ?_
  · refine (approxLQG_ge_tail hW hγ hδ0 hp b).trans (le_of_eq ?_)
    rw [Real.log_inv, log_side, hb]
  rw [two_pow_sq_eq, ← Real.exp_add, Real.exp_le_exp]
  have hq : l31q γ = 2 * p - 2 - p * (p - 1) * γ ^ 2 / 2 := by
    rw [hpdef]; unfold l31q l31p; field_simp; ring
  rw [hq, Real.log_inv]
  apply le_of_eq
  simp only [l]
  ring

/-- **DZZ (eq-very-crude-prime), `∫⁻` form**: `E (log D'_{γ,δ}(A, B))² ≤ a + b (log δ⁻¹)²`,
uniformly in the sets `A, B` and `δ ∈ (0, 1)`. -/
theorem lintegral_sq_logApproxLGD_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ (A B : Set ℂ) (δ : ℝ), 0 < δ → δ < 1 →
      ∫⁻ ω, ENNReal.ofReal (logApproxLGD γ W δ A B ω) ^ 2 ∂P ≤
        ENNReal.ofReal (a + b * Real.log δ⁻¹ ^ 2) := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  set p := l31p γ with hpdef
  set q := l31q γ with hqdef
  have hp : 1 ≤ p := by
    rw [hpdef, l31p, le_div_iff₀ (by positivity)]; nlinarith
  have hq0 : 0 < q := l31q_pos hγ hγ2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set l := Real.log 2 with hl
  set l8 := Real.log 8 with hl8
  have hl80 : 0 < l8 := Real.log_pos (by norm_num)
  set C₀ := 2 * p * (p - 1) * γ ^ 2 with hC₀
  set r := Real.exp (-(q * l / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by have := mul_pos hq0 hl2; linarith)
  have hr2 : r ^ 2 = Real.exp (-(q * l)) := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  set G := Real.exp C₀ * ((1 - r)⁻¹) ^ 2 with hG
  have hG0 : 0 ≤ G := by have : 0 < 1 - r := by linarith
                         positivity
  set κ := 2 * p * l8 / (q * l) with hκ
  refine ⟨4 * (2 * l8 ^ 2 + l8 ^ 2 * G), 8 * κ ^ 2, by positivity, by positivity,
    fun A B δ hδ0 hδ1 => ?_⟩
  set L := Real.log δ⁻¹ with hL
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hδ0).2 hδ1.le)
  set j₀ : ℕ := ⌈2 * p * L / (q * l)⌉₊ with hj₀
  set S : ℕ → Set Ω := fun K => {ω | ∃ b : DyBox, b.n = K ∧ ω ∈ {ω | δ ^ 2 ≤ approxLQG γ W ω b}}
    with hS
  set T : ℕ → Set Ω := fun m => toMeasurable P (S (j₀ + m)) with hT
  have hPq : ∀ m : ℕ, P (T m) ≤ ENNReal.ofReal (Real.exp C₀ * (r ^ 2) ^ m) := fun m => by
    rw [hT, measure_toMeasurable, ← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ((cm_level_bound hW hγ hγ2 hδ0 (j₀ + m)).trans ?_)
    rw [hr2, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have hc : 2 * p * L / (q * l) ≤ j₀ := Nat.le_ceil _
    have hc' : 2 * p * L ≤ j₀ * (q * l) := (div_le_iff₀ (by positivity)).1 hc
    push_cast
    nlinarith
  have hpt : ∀ ω (m : ℕ), ω ∉ T m → ENNReal.ofReal (logApproxLGD γ W δ A B ω) ≤
      ENNReal.ofReal (j₀ * l8 + l8 * m) := fun ω m hω => by
    have hgood : ∀ b : DyBox, b.n = j₀ + m → approxLQG γ W ω b < δ ^ 2 := by
      intro b hb
      by_contra hc
      push Not at hc
      exact hω (subset_toMeasurable P _ ⟨b, hb, hc⟩)
    have h1 := (approxDistSet_toNat_le (approxLQG γ W ω) δ hgood A B).trans
      (cm_succ_mul_le_eight_pow _)
    refine ENNReal.ofReal_le_ofReal ?_
    unfold logApproxLGD approxLGDSet
    have e : (j₀ : ℝ) * l8 + l8 * m = Real.log ((8 : ℝ) ^ (j₀ + m)) := by
      rw [Real.log_pow, hl8]; push_cast; ring
    rw [e]
    rcases Nat.eq_zero_or_pos (approxDistSet (approxLQG γ W ω) δ A B).toNat with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (one_le_pow₀ (by norm_num))
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast h1)
  have hmain := lintegral_sq_le_of_geom (P := P)
    (fun ω => ENNReal.ofReal (logApproxLGD γ W δ A B ω)) T
    (fun m => measurableSet_toMeasurable P _) (a₀ := j₀ * l8) (c := l8) (C := Real.exp C₀)
    (by positivity) hl80 (Real.exp_pos _).le hr0 hr1 hPq hpt
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hj : (j₀ : ℝ) ≤ 2 * p * L / (q * l) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have ha : (j₀ : ℝ) * l8 ≤ κ * L + l8 := by
    have := mul_le_mul_of_nonneg_right hj hl80.le
    have e : (2 * p * L / (q * l) + 1) * l8 = κ * L + l8 := by
      rw [hκ]; field_simp
    linarith
  have hsq : ((j₀ : ℝ) * l8) ^ 2 ≤ 2 * l8 ^ 2 + 2 * κ ^ 2 * L ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) ha 2
    nlinarith [sq_nonneg (κ * L - l8)]
  rw [← hG]
  nlinarith

end DZZ
end LQGMetric
