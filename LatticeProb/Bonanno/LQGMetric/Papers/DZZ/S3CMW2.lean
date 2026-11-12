/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CMW2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K3

/-!
# Walled DZZ (eq-very-crude) at `dzzWall K μIn` (P2-DZZMOMW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 854–857; l. 1521 "the general case follows by the
same proof"; Remark 5.2, l. 2281–2284) for the walled measure `dzzWall K μIn` (D117/D123, packet
P-317K-MOM): `E (log min_{A×B} D^K_δ)² = O((log δ⁻¹)²)` for `u ∈ A`, `v ∈ B`, `u ≠ v ∈ 𝕍_{-ξ}`
whose segment stays at distance `≥ ξ/2` from `Kᶜ`. The proof is P2-DZZCM's (S3CM5, S3CM6), the
only change being that the balls of the segment covering lie in `K`, so the wall does not change
their mass (`dzzWall_ball_of_subset`).

* `cmw_ball_sub_of_kXi`, `cmw_ball_lineMap_sub`: for a convex `K` and `u, v ∈ K^ξ`, the
  `ξ`-balls about the points of `[u, v]` lie in `K` (own elementary argument);
* `convex_closedBox`: dyadic closed boxes are convex;
* `cmw_log_min_le_of_good`: copy of `cm_log_min_le_of_good`;
* **`lintegral_sq_logMin_dzzWall_le`**: copy of `lintegral_sq_logMin_dzzMuIn_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

lemma cmw_ball_sub_of_kXi {K : Set ℂ} {ξ : ℝ} {u : ℂ} (hu : u ∈ kXi K ξ) : ball u ξ ⊆ K := by
  intro w hw
  by_contra h
  have := Metric.infDist_le_dist_of_mem (x := u) (show w ∈ Kᶜ from h)
  rw [mem_ball, dist_comm] at hw
  exact absurd (hu.trans this) (not_le.2 hw)

/-- for a convex `K` and `u, v ∈ K^ξ`, the `ξ`-ball about each point of `[u, v]` lies in `K` -/
lemma cmw_ball_lineMap_sub {K : Set ℂ} (hK : Convex ℝ K) {ξ : ℝ} {u v : ℂ} (hu : u ∈ kXi K ξ)
    (hv : v ∈ kXi K ξ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ball (AffineMap.lineMap u v t) ξ ⊆ K := by
  intro w hw
  set d := w - AffineMap.lineMap u v t with hd
  have hdn : ‖d‖ < ξ := by rw [hd, ← dist_eq_norm]; exact hw
  have hu' : u + d ∈ K := cmw_ball_sub_of_kXi hu (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hdn)
  have hv' : v + d ∈ K := cmw_ball_sub_of_kXi hv (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hdn)
  have e : AffineMap.lineMap (u + d) (v + d) t = w := by
    simp only [AffineMap.lineMap_apply_module, hd]
    module
  rw [← e]
  exact hK.lineMap_mem hu' hv' ht

lemma convex_closedBox (b : DyBox) : Convex ℝ b.closedBox := by
  intro x hx y hy a c ha hc hac
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have hre : (a • x + c • y).re = a * x.re + c * y.re := by simp
  have him : (a • x + c • y).im = a * x.im + c * y.im := by simp
  obtain rfl : c = 1 - a := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hre, him]
  · nlinarith [mul_le_mul_of_nonneg_left x1 ha, mul_le_mul_of_nonneg_left y1 hc]
  · nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hc]
  · nlinarith [mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left y3 hc]
  · nlinarith [mul_le_mul_of_nonneg_left x4 ha, mul_le_mul_of_nonneg_left y4 hc]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **the good event bounds `log min_{A×B} D^K_δ`** (copy of `cm_log_min_le_of_good`, P2-DZZCM,
for the walled measure; the covering balls lie in `K`) -/
lemma cmw_log_min_le_of_good {K : Set ℂ} {γ b β ε δ ξ : ℝ} {ω : Ω} {A B : Set ℂ} {u v : ℂ}
    (hξ : 0 < ξ)
    (hu : u ∈ A) (hv : v ∈ B) (hu' : u ∈ dzzVIn ξ) (hv' : v ∈ dzzVIn ξ) (huv : u ≠ v)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ball (AffineMap.lineMap u v t) (ξ / 2) ⊆ K)
    (hb : ∀ S : Set ℂ, MeasurableSet S → S ⊆ dzzVIn (ξ / 2) →
      wickQArea γ W ω S ≤ ENNReal.ofReal (Real.exp b) * DG.muHU W γ ω S)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hεξ : ε ^ β ≤ ξ / 2)
    (hδ : ENNReal.ofReal (Real.exp b) * ENNReal.ofReal ε ≤ ENNReal.ofReal (δ ^ 2))
    (hgood : ∀ z ∈ dzzVIn ξ, DG.muHU W γ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε) :
    logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ A B ≤ Real.log 6 + β * Real.log ε⁻¹ := by
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hD := lgdDZZ_le_segment (ν := dzzWall K (dzzMuIn γ W ω)) (δ := δ) hεβ huv (fun t ht => by
    have hx := cm_lineMap_mem_dzzVIn hu' hv' ht
    have hsub := cm_ball_sub_dzzVIn hεξ hx
    have hsubV : ball (AffineMap.lineMap u v t) (ε ^ β) ⊆ dzzV :=
      hsub.trans (dzzVIn_sub_dzzV (by positivity))
    rw [dzzWall_ball_of_subset _ ((ball_subset_ball hεξ).trans (hseg t ht)), dzzMuIn,
      dzzWall_apply_of_subset isClosed_dzzV.measurableSet hsubV]
    refine (hb _ isOpen_ball.measurableSet hsub).trans ?_
    refine le_trans ?_ hδ
    gcongr
    exact hgood _ hx)
  set N : ℕ := ⌈2 * dist u v / ε ^ β⌉₊ + 1 with hN
  have hNle : (N : ℝ) ≤ 6 * ε ^ (-β) := by
    have hinv : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
    have e1 : ε ^ (-β) = (ε ^ β)⁻¹ := Real.rpow_neg hε.le β
    have hd := cm_dist_le_two (by positivity) hu' hv'
    have hq : 2 * dist u v / ε ^ β ≤ 4 * ε ^ (-β) := by
      rw [e1, div_eq_mul_inv]
      have : 0 ≤ (ε ^ β)⁻¹ := by positivity
      nlinarith
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * dist u v / ε ^ β by positivity)
    simp only [hN, Nat.cast_add, Nat.cast_one]
    linarith
  have hmin : lgdMinSet (dzzWall K (dzzMuIn γ W ω)) δ A B ≤ (N : ℕ∞) :=
    (iInf₂_le_of_le u hu (iInf₂_le_of_le v hv le_rfl)).trans hD
  have hT : (lgdMinSet (dzzWall K (dzzMuIn γ W ω)) δ A B).toNat ≤ N :=
    ENat.toNat_le_of_le_natCast hmin
  have hN1 : (1 : ℝ) ≤ N := by simp only [hN]; exact_mod_cast Nat.le_add_left 1 _
  have hlogN : Real.log N ≤ Real.log 6 + β * Real.log ε⁻¹ := by
    calc Real.log N ≤ Real.log (6 * ε ^ (-β)) := Real.log_le_log (by linarith) hNle
      _ = Real.log 6 + β * Real.log ε⁻¹ := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε,
          Real.log_inv]; ring
  unfold logMinLGD
  rcases Nat.eq_zero_or_pos (lgdMinSet (dzzWall K (dzzMuIn γ W ω)) δ A B).toNat with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact (Real.log_nonneg hN1).trans hlogN
  · exact (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hT)).trans hlogN

set_option maxHeartbeats 400000 in
/-- **Walled DZZ (eq-very-crude) at `dzzWall K μIn`, second moment, `∫⁻` form, for sets**
(copy of `lintegral_sq_logMin_dzzMuIn_le`, P2-DZZCM, S3CM6; the constants do not depend on `K`) -/
theorem lintegral_sq_logMin_dzzWall_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ a b' : ℝ, 0 ≤ a ∧ 0 ≤ b' ∧ ∀ (K A B : Set ℂ) (u v : ℂ), u ∈ A → v ∈ B → u ∈ dzzVIn ξ →
      v ∈ dzzVIn ξ → u ≠ v → (∀ t ∈ Icc (0 : ℝ) 1, ball (AffineMap.lineMap u v t) (ξ / 2) ⊆ K) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∫⁻ ω, ENNReal.ofReal (logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ A B) ^ 2 ∂P ≤
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
    by positivity, fun K A B u v hu hv hu' hv' huv hseg δ hδ hδ2 => ?_⟩
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
  have hpt : ∀ ω (m : ℕ), ω ∉ T m → ENNReal.ofReal (logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ A B) ≤
      ENNReal.ofReal (a₀ + β * Real.log 2 * m) := fun ω m hω => by
    have hgood : ∀ z ∈ dzzVIn ξ, DG.muHU W γ ω (ball z (ε (j₀ + m) ^ β)) ≤
        ENNReal.ofReal (ε (j₀ + m)) := by
      by_contra hc
      exact hω (subset_toMeasurable P _ hc)
    have hadm' := hadm (j₀ + m) (Nat.le_add_right _ _)
    have hlog := cmw_log_min_le_of_good (W := W) (ω := ω) (b := b) hξ hu hv hu' hv' huv hseg
      (fun S hS hSK => hb _ S hS hSK) (hεpos _) (hε1 _) hβ0 hadm'.2.1 hadm'.2.2 hgood
    rw [hεlog] at hlog
    refine ENNReal.ofReal_le_ofReal (hlog.trans_eq ?_)
    simp only [ha₀, Nat.cast_add]; ring
  have hmain := lintegral_sq_le_of_geom (P := P)
    (fun ω => ENNReal.ofReal (logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ A B)) T
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
