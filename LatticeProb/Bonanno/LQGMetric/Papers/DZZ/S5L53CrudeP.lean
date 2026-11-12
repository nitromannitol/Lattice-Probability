/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53CrudeP at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Crude

/-!
# DZZ (eq-very-crude) for the tilde distance: `E log D̃_δ(u,v) ≤ A + B log δ⁻¹` (P2-DZZ53)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 854–857; "an analogue of (eq-very-crude)",
l. 2411): `E log D_δ(u,v) = O(log δ⁻¹)`, here for the tilde distance
`D̃_δ(u,v) = D_δ(u,v; dzzWall 𝕍̃_{u,v} μIn)`, uniformly in `u ≠ v ∈ 𝕍̄`.

Proof (DZZ's covering, l. 744–745, with DG Lemma 3.8's upper half as ball-mass input,
`DG.dgL38Upper_muHU`): at the dyadic scales `ε_j = 2^{-j}`, `j ≥ j₀(δ) ≈ (2 log δ⁻¹ + |b|)/log 2`,
the good event `G_j = {M_γ(B(z, ε_j^β)) ≤ ε_j ∀ z}` has `P(G_jᶜ) ≤ C ε_j^p` and on it
`log D̃_δ ≤ log 8 + β j log 2` (`log_tilde_le_of_good`); hence
`log D̃_δ ≤ log 8 + β log 2 · (j₀ + Σ_m 1_{G_{j₀+m}ᶜ})` and the geometric series gives the bound.
Only an upper bound of a (possibly non-measurable) `lintegral` is needed, so no measurability
of `D̃_δ` is used. Own elementary tail-sum argument.

* `lintegral_log_tilde_le`: the `∫⁻` bound;
* `chiDy_tilde_le`: the hypothesis `hM` of `dzzLem53Exp_of_subadd` for `μ = dzzMuIn γ W`.
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

/-- **DZZ (eq-very-crude) for `D̃`, `∫⁻` form**: `E log D̃_δ(u,v) ≤ A + B log δ⁻¹` for
`δ ≤ 1/2`, uniformly in `u ≠ v ∈ 𝕍̄`. -/
theorem lintegral_log_tilde_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ δ : ℝ, 0 < δ →
      δ ≤ 1 / 2 → ∫⁻ ω, ENNReal.ofReal
        (logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}) ∂P ≤
        ENNReal.ofReal (A + B * Real.log δ⁻¹) := by
  have hβ : 2 / (2 - γ) ^ 2 < 2 / (2 - γ) ^ 2 + 1 := by linarith
  have hβ0 : 0 < 2 / (2 - γ) ^ 2 + 1 := by
    have : 0 < (2 - γ) ^ 2 := by nlinarith
    positivity
  obtain ⟨p, C, ε₀, hp, hε₀, hbad⟩ := DG.dgL38Upper_muHU (P := P) hW hγ hγ2 (u := cZ)
    (R := 1 / 5) (by norm_num)
    (by rw [show (2 : ℝ) * (1 / 5) = 2 / 5 by norm_num]; exact closedBall_cZ_subset) hβ
  set β := 2 / (2 - γ) ^ 2 + 1 with hβdef
  obtain ⟨b, hb⟩ := wickArea_le_of_compact γ (isCompact_closedBall cZ (2 / 5))
    closedBall_cZ_subset
  obtain ⟨J₁, hJ₁⟩ := exists_pow_lt_of_lt_one hε₀ (show (1 / 2 : ℝ) < 1 by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set q : ℝ := (1 / 2 : ℝ) ^ p with hq
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hq0 : 0 ≤ q := by positivity
  set G : ℝ≥0∞ := ENNReal.ofReal (β * Real.log 2) * (ENNReal.ofReal |C| *
    (1 - ENNReal.ofReal q)⁻¹) with hG
  have hGt : G ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
    rw [ENNReal.inv_ne_top]
    exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq1)).ne'
  refine ⟨Real.log 8 + β * Real.log 2 * (J₁ + 1) + β * |b| + G.toReal, 2 * β, by positivity,
    by positivity, fun u hu v hv huv δ hδ hδ2 => ?_⟩
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
  -- the scales `j ≥ j₀` are admissible
  have hadm : ∀ j, j₀ ≤ j → ε j < ε₀ ∧
      ENNReal.ofReal (Real.exp b) * ENNReal.ofReal (ε j) ≤ ENNReal.ofReal (δ ^ 2) := by
    intro j hj
    refine ⟨(pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans_lt hJ₁, ?_⟩
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
  -- the bad events
  set S : ℕ → Set Ω := fun j => {ω | ¬ ∀ z ∈ closedBall cZ (1 / 5),
    DG.muHU W γ ω (ball z (ε j ^ β)) ≤ ENNReal.ofReal (ε j)} with hS
  set T : ℕ → Set Ω := fun j => toMeasurable P (S j) with hT
  have hPT : ∀ j, j₀ ≤ j → P (T j) ≤ ENNReal.ofReal (C * ε j ^ p) := fun j hj => by
    rw [hT, measure_toMeasurable]; exact hbad (ε j) (hεpos j) (hadm j hj).1
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}) with hf
  set a₀ : ℝ := Real.log 8 + β * Real.log 2 * j₀ with ha₀
  have ha₀0 : 0 ≤ a₀ := by
    have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    positivity
  -- pointwise bound
  have hpt : ∀ ω, f ω ≤ ENNReal.ofReal a₀ + ENNReal.ofReal (β * Real.log 2) *
      ∑' m : ℕ, (T (j₀ + m)).indicator 1 ω := by
    intro ω
    by_cases h : ∃ m, ω ∉ T (j₀ + m)
    · classical
      set m := Nat.find h
      have hm : ω ∉ T (j₀ + m) := Nat.find_spec h
      have hlt : ∀ i < m, ω ∈ T (j₀ + i) := fun i hi => by
        have := Nat.find_min h hi; push Not at this; exact this
      have hgood : ∀ z ∈ closedBall cZ (1 / 5), DG.muHU W γ ω (ball z (ε (j₀ + m) ^ β)) ≤
          ENNReal.ofReal (ε (j₀ + m)) := by
        by_contra hc
        exact hm (subset_toMeasurable P _ hc)
      have hlog := log_tilde_le_of_good hu hv huv (fun A hA hAK => hb _ A hA hAK)
        (hεpos _) (hε1 _) hβ0 (hadm _ (Nat.le_add_right _ _)).2 hgood
      rw [hεlog] at hlog
      have hsum : (m : ℝ≥0∞) ≤ ∑' i : ℕ, (T (j₀ + i)).indicator 1 ω := by
        calc (m : ℝ≥0∞) = ∑ i ∈ Finset.range m, (T (j₀ + i)).indicator 1 ω := by
              rw [Finset.sum_congr rfl fun i hi => by
                rw [indicator_of_mem (hlt i (Finset.mem_range.1 hi))]]
              simp
          _ ≤ _ := ENNReal.sum_le_tsum _
      calc f ω ≤ ENNReal.ofReal (a₀ + β * Real.log 2 * m) := by
            refine ENNReal.ofReal_le_ofReal (hlog.trans_eq ?_)
            simp only [ha₀, Nat.cast_add]; ring
        _ = ENNReal.ofReal a₀ + ENNReal.ofReal (β * Real.log 2) * (m : ℝ≥0∞) := by
            rw [ENNReal.ofReal_add ha₀0 (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast]
        _ ≤ _ := by gcongr
    · push Not at h
      have htop : ∑' m : ℕ, (T (j₀ + m)).indicator (1 : Ω → ℝ≥0∞) ω = ⊤ := by
        simp only [indicator_of_mem (h _), Pi.one_apply]
        exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
      have hne : ENNReal.ofReal (β * Real.log 2) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      rw [htop, ENNReal.mul_top hne]
      simp
  -- integrate
  have hgeo : ∑' m : ℕ, P (T (j₀ + m)) ≤ ENNReal.ofReal |C| * (1 - ENNReal.ofReal q)⁻¹ := by
    rw [← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun m => (hPT _ (Nat.le_add_right _ _)).trans ?_
    rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (abs_nonneg C)]
    refine ENNReal.ofReal_le_ofReal ?_
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
  have hint : ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal a₀ + G := by
    refine (lintegral_mono hpt).trans ?_
    have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (Measurable.ennreal_tsum fun m =>
        (measurable_one.indicator (measurableSet_toMeasurable P _))),
      lintegral_tsum fun m => (measurable_one.indicator
        (measurableSet_toMeasurable P _)).aemeasurable]
    simp only [lintegral_indicator_one (measurableSet_toMeasurable P _)]
    rw [hG]
    gcongr
  refine hint.trans ?_
  have hsplit : ENNReal.ofReal a₀ + G = ENNReal.ofReal (a₀ + G.toReal) := by
    rw [ENNReal.ofReal_add ha₀0 ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hGt]
  rw [hsplit]
  refine ENNReal.ofReal_le_ofReal ?_
  have hj : (j₀ : ℝ) ≤ J₁ + ((2 * L + |b|) / Real.log 2 + 1) := by
    simp only [hj₀, Nat.cast_add]
    linarith [Nat.ceil_lt_add_one (show 0 ≤ (2 * L + |b|) / Real.log 2 by positivity)]
  have : β * Real.log 2 * j₀ ≤ β * Real.log 2 * (J₁ + 1) + β * |b| + 2 * β * L := by
    have h := mul_le_mul_of_nonneg_left hj (show 0 ≤ β * Real.log 2 by positivity)
    have e : β * Real.log 2 * (J₁ + ((2 * L + |b|) / Real.log 2 + 1)) =
        β * Real.log 2 * (J₁ + 1) + β * |b| + 2 * β * L := by
      field_simp; ring
    linarith
  simp only [ha₀]
  linarith

end DZZ
end LQGMetric
