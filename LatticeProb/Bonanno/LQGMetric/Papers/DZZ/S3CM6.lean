/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM5

/-!
# DZZ (eq-very-crude) at `μIn`: the second moment (P2-DZZCM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 854–857): `E (log D_δ)² = O((log δ⁻¹)²)`, here for
`min_{A×B} D_δ(·,·; μIn)` with `u ∈ A`, `v ∈ B`, `u ≠ v ∈ 𝕍_{-ξ}`, uniformly, for `δ ≤ 1/2`.
The proof is that of `lintegral_sq_log_tilde_le` (P2-DZZ53b, S5L53B2): at the dyadic scales
`ε_j = 2^{-j}`, `j ≥ j₀ ≈ (2 log δ⁻¹ + |b|)/log 2`, off the bad event of DG L3.8 on `𝕍_{-ξ}`
(`cm_dgL38Upper_dzzVIn`, probability `≤ C ε_j^p`) the covering gives
`log min D_δ ≤ log 6 + β j log 2` (`cm_log_min_le_of_good`); the tail sum is
`lintegral_sq_le_of_geom`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option maxHeartbeats 400000 in
/-- **DZZ (eq-very-crude) at `μIn`, second moment, `∫⁻` form, for sets** -/
theorem lintegral_sq_logMin_dzzMuIn_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ a b' : ℝ, 0 ≤ a ∧ 0 ≤ b' ∧ ∀ (A B : Set ℂ) (u v : ℂ), u ∈ A → v ∈ B → u ∈ dzzVIn ξ →
      v ∈ dzzVIn ξ → u ≠ v → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∫⁻ ω, ENNReal.ofReal (logMinLGD (dzzMuIn γ W ω) δ A B) ^ 2 ∂P ≤
        ENNReal.ofReal (a + b' * Real.log δ⁻¹ ^ 2) := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hβ : 2 / (2 - γ) ^ 2 < 2 / (2 - γ) ^ 2 + 1 := by linarith
  have hβ1 : 1 ≤ 2 / (2 - γ) ^ 2 + 1 := by
    have : 0 < (2 - γ) ^ 2 := by nlinarith
    have : 0 ≤ 2 / (2 - γ) ^ 2 := by positivity
    linarith
  obtain ⟨p, C, ε₀, hp, hε₀, hbad⟩ := cm_dgL38Upper_dzzVIn (P := P) hW hγ hγ2 hξ hβ
  set β := 2 / (2 - γ) ^ 2 + 1 with hβdef
  have hβ0 : 0 < β := by linarith
  have hKsq : dzzVIn (ξ / 2) ⊆ openSquare := fun z hz => by
    obtain ⟨a1, a2, a3, a4⟩ := hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨b, hb⟩ := wickArea_le_of_compact γ (cm_isCompact_dzzVIn (ξ / 2)) hKsq
  obtain ⟨J₁, hJ₁⟩ := exists_pow_lt_of_lt_one (lt_min hε₀ (by positivity : (0 : ℝ) < ξ / 2))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set q : ℝ := (1 / 2 : ℝ) ^ p with hq
  set r : ℝ := (1 / 2 : ℝ) ^ (p / 2) with hr
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hr0 : 0 ≤ r := by positivity
  have hrq : r ^ 2 = q := by
    rw [hr, hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  set G : ℝ := |C| * ((1 - r)⁻¹) ^ 2 with hG
  have hG0 : 0 ≤ G := by
    have : 0 < 1 - r := by linarith
    positivity
  set a₁ : ℝ := Real.log 6 + β * Real.log 2 * (J₁ + 1) + β * |b| with ha₁
  have ha₁0 : 0 ≤ a₁ := by
    have : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨4 * (2 * a₁ ^ 2 + (β * Real.log 2) ^ 2 * G), 32 * β ^ 2, by positivity,
    by positivity, fun A B u v hu hv hu' hv' huv δ hδ hδ2 => ?_⟩
  set L := Real.log δ⁻¹ with hL
  have hL0 : 0 < L := by
    rw [hL, Real.log_inv]
    have := Real.log_lt_log hδ (show δ < 1 by linarith)
    rw [Real.log_one] at this; linarith
  set j₀ : ℕ := J₁ + ⌈(2 * L + |b|) / Real.log 2⌉₊ with hj₀
  set ε : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j with hε
  have hεpos : ∀ j, 0 < ε j := fun j => by positivity
  have hε1 : ∀ j, ε j ≤ 1 := fun j => pow_le_one₀ (by norm_num) (by norm_num)
  have hεlog : ∀ j, Real.log (ε j)⁻¹ = j * Real.log 2 := fun j => by
    simp only [hε, one_div, inv_pow, inv_inv, Real.log_pow]
  have hadm : ∀ j, j₀ ≤ j → ε j < ε₀ ∧ ε j ^ β ≤ ξ / 2 ∧
      ENNReal.ofReal (Real.exp b) * ENNReal.ofReal (ε j) ≤ ENNReal.ofReal (δ ^ 2) := by
    intro j hj
    have hlt : ε j < min ε₀ (ξ / 2) :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans_lt hJ₁
    refine ⟨hlt.trans_le (min_le_left _ _), ?_, ?_⟩
    · calc ε j ^ β ≤ ε j ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (hεpos j) (hε1 j) hβ1
        _ = ε j := Real.rpow_one _
        _ ≤ ξ / 2 := (hlt.trans_le (min_le_right _ _)).le
    rw [← ENNReal.ofReal_mul (Real.exp_pos b).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc : (2 * L + |b|) / Real.log 2 ≤ j := by
      have := Nat.le_ceil ((2 * L + |b|) / Real.log 2)
      have : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
      simp only [hj₀, Nat.cast_add] at this
      linarith [(Nat.cast_nonneg J₁ : (0 : ℝ) ≤ J₁)]
    have hεj : ε j = Real.exp (-(j * Real.log 2)) := by
      rw [← hεlog j, Real.log_inv, neg_neg, Real.exp_log (hεpos j)]
    have hδ2 : δ ^ 2 = Real.exp (-(2 * L)) := by
      have e : -(2 * L) = Real.log (δ ^ 2) := by
        rw [hL, Real.log_inv, Real.log_pow]; push_cast; ring
      rw [e, Real.exp_log (by positivity)]
    rw [hεj, hδ2, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := (div_le_iff₀ hl2).1 hc
    linarith [le_abs_self b]
  set S : ℕ → Set Ω := fun j => {ω | ¬ ∀ z ∈ dzzVIn ξ,
    DG.muHU W γ ω (ball z (ε j ^ β)) ≤ ENNReal.ofReal (ε j)} with hS
  set T : ℕ → Set Ω := fun m => toMeasurable P (S (j₀ + m)) with hT
  have hPq : ∀ m : ℕ, P (T m) ≤ ENNReal.ofReal (|C| * (r ^ 2) ^ m) := fun m => by
    rw [hT, measure_toMeasurable]
    refine (hbad (ε (j₀ + m)) (hεpos _) (hadm _ (Nat.le_add_right _ _)).1).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hrq]
    have h1 : ε (j₀ + m) ^ p ≤ q ^ m := by
      have e : q ^ m = (ε m) ^ p := by
        simp only [hq, hε]
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [e]
      exact Real.rpow_le_rpow (hεpos _).le (pow_le_pow_of_le_one (by norm_num) (by norm_num)
        le_add_self) hp.le
    have h2 : 0 ≤ ε (j₀ + m) ^ p := (Real.rpow_pos_of_pos (hεpos _) p).le
    calc C * ε (j₀ + m) ^ p ≤ |C| * ε (j₀ + m) ^ p :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h2
      _ ≤ |C| * q ^ m := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
  set a₀ : ℝ := Real.log 6 + β * Real.log 2 * j₀ with ha₀
  have ha₀0 : 0 ≤ a₀ := by
    have : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    positivity
  have hpt : ∀ ω (m : ℕ), ω ∉ T m → ENNReal.ofReal (logMinLGD (dzzMuIn γ W ω) δ A B) ≤
      ENNReal.ofReal (a₀ + β * Real.log 2 * m) := fun ω m hω => by
    have hgood : ∀ z ∈ dzzVIn ξ, DG.muHU W γ ω (ball z (ε (j₀ + m) ^ β)) ≤
        ENNReal.ofReal (ε (j₀ + m)) := by
      by_contra hc
      exact hω (subset_toMeasurable P _ hc)
    have hadm' := hadm (j₀ + m) (Nat.le_add_right _ _)
    have hlog := cm_log_min_le_of_good (W := W) (ω := ω) (b := b) hξ hu hv hu' hv' huv
      (fun S hS hSK => hb _ S hS hSK) (hεpos _) (hε1 _) hβ0 hadm'.2.1 hadm'.2.2 hgood
    rw [hεlog] at hlog
    refine ENNReal.ofReal_le_ofReal (hlog.trans_eq ?_)
    simp only [ha₀, Nat.cast_add]; ring
  have hmain := lintegral_sq_le_of_geom (P := P)
    (fun ω => ENNReal.ofReal (logMinLGD (dzzMuIn γ W ω) δ A B)) T
    (fun m => measurableSet_toMeasurable P _) ha₀0 (by positivity : 0 < β * Real.log 2)
    (abs_nonneg C) hr0 hr1 hPq hpt
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hj : (j₀ : ℝ) ≤ J₁ + ((2 * L + |b|) / Real.log 2 + 1) := by
    simp only [hj₀, Nat.cast_add]
    linarith [Nat.ceil_lt_add_one (show 0 ≤ (2 * L + |b|) / Real.log 2 by positivity)]
  have : β * Real.log 2 * j₀ ≤ β * Real.log 2 * (J₁ + 1) + β * |b| + 2 * β * L := by
    have h := mul_le_mul_of_nonneg_left hj (show 0 ≤ β * Real.log 2 by positivity)
    have e : β * Real.log 2 * (J₁ + ((2 * L + |b|) / Real.log 2 + 1)) =
        β * Real.log 2 * (J₁ + 1) + β * |b| + 2 * β * L := by
      field_simp; ring
    linarith
  have ha : a₀ ≤ a₁ + 2 * β * L := by simp only [ha₀, ha₁]; linarith
  have hsq : a₀ ^ 2 ≤ 2 * a₁ ^ 2 + 8 * β ^ 2 * L ^ 2 := by
    have h1 := pow_le_pow_left₀ ha₀0 ha 2
    have h2 : (a₁ + 2 * β * L) ^ 2 = 2 * a₁ ^ 2 + 8 * β ^ 2 * L ^ 2 - (a₁ - 2 * β * L) ^ 2 := by
      ring
    have h3 := sq_nonneg (a₁ - 2 * β * L)
    linarith
  rw [← hG]
  linarith

end DZZ
end LQGMetric
