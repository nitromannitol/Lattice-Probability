/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L4Mid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Max

/-!
# DG Lemma 3.6: comparison of `ĥ_{δ/A}` and `ĥ_δ` (task P2-DG3A, WP-118)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.6 (`lem-mid-scale-max`,
DG:1079–1085): "For each bounded domain `U ⊂ ℂ`, each `ζ ∈ (0,1)`, each `δ ∈ (0,1)`, each
`A ∈ (1, e^{(log δ⁻¹)^{1−ζ}})`, and each `C ≥ 1`,
`P[max_{z,w∈U : |z−w| ≤ Cδ} |ĥ_{δ/A}(z) − ĥ_δ(w)| ≤ ζ log δ⁻¹] ≥ 1 − O_δ(δ^p)` for all `p > 0`,
with the rate … uniform over all of the possible choices of `A`."

DG's proof (DG:1086–1094): the `ĥ_{δ/A}(z) − ĥ_δ(z)` are centred Gaussian with variance
`log A ≤ (log δ⁻¹)^{1−ζ}`; Gaussian tail and a union bound over a grid; then Lemma 3.4 for `ĥ_δ`
and for `ĥ_{δ/A}` and the triangle inequality. Bookkeeping here (own, same ingredients): the grid
has mesh `≤ δ/(2A)` (so that Lemma 3.4 at scale `δ/A` reaches every point; its
`(A/δ)² ≤ e^{2(log δ⁻¹)^{1−ζ}} δ^{-2}` points are absorbed by the tail
`e^{−ζ² (log δ⁻¹)^{1+ζ}/18}`), Lemma 3.4 at scale `δ/A` is used with `ζ/6`
(`log (A/δ) ≤ 2 log δ⁻¹`), and at scale `δ` with distance `(C+1)δ` (`dg_lemma34C`) and `ζ/3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DG

open WhiteNoise DZZ SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `Var φ_{a,b}(x) = log(b/a)` for `0 < a ≤ b` (DDDF l. 287 with `x = x'`) -/
theorem variance_phi_band (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (x : ℂ) : Var[phi W a b x; P] = Real.log (b / a) := by
  have := hW.isProbabilityMeasure
  have hm : MemLp (phi W a b x) 2 P := by
    unfold phi
    exact ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _
  rw [← covariance_self hm.aemeasurable, cov_phi hW ha]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    neg_zero, zero_div, Real.exp_zero, mul_one]
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hb : 0 < b := ha.trans_le hab
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab2]
  simp_rw [mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div hb.ne' ha.ne']
  push_cast
  ring

/-- the one-point tail of `ĥ_{δ/A}(g) − ĥ_δ(g)`: a centred Gaussian of variance `log A` -/
lemma phiVer_diff_point_tail (hW : IsWhiteNoise P W) {δ A : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : 1 < A) (g : ℂ) {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | y ≤ |DDDF.phiVer W P (δ / A) 1 g ω - DDDF.phiVer W P δ 1 g ω|} ≤
      2 * Real.exp (-y ^ 2 / (2 * Real.log A)) := by
  have := hW.isProbabilityMeasure
  have hA0 : 0 < A := by linarith
  have hδA : 0 < δ / A := div_pos hδ0 hA0
  have hδAδ : δ / A ≤ δ := div_le_self hδ0.le hA.le
  have hv1 := DDDF.isPhiVersion_phiVer hW hδA (hδAδ.trans hδ1)
  have hv2 := DDDF.isPhiVersion_phiVer hW hδ0 hδ1
  have hl := DDDF.hasLaw_phi hW (δ / A) δ g
  have hv : ((Real.pi * ‖phiKernelL2 (δ / A) δ g‖ ^ 2).toNNReal : ℝ) = Real.log A := by
    have e : δ / (δ / A) = A := by field_simp
    have h := variance_phi_band hW hδA hδAδ g
    rw [e, hl.variance_eq, variance_id_gaussianReal] at h
    exact h
  have hae : (fun ω => DDDF.phiVer W P (δ / A) 1 g ω - DDDF.phiVer W P δ 1 g ω) =ᵐ[P]
      phi W (δ / A) δ g := by
    filter_upwards [hv1.ae_eq g, hv2.ae_eq g, phi_add_ae hW hδA hδAδ hδ1 g] with ω h1 h2 h3
    rw [h1, h2, h3]; ring
  have h := DDDF.tail_abs_of_hasLaw (by rw [hv]; exact Real.log_pos hA) (hl.congr hae) hy
  rwa [hv] at h

/-- `L = L^{1−ζ} L^ζ` and `L^{1−ζ} ≤ L` for `L ≥ 1`, `0 < ζ < 1` -/
lemma rpow_split {L ζ : ℝ} (hL : 1 ≤ L) (hζ0 : 0 ≤ ζ) :
    L = L ^ (1 - ζ) * L ^ ζ ∧ L ^ (1 - ζ) ≤ L ∧ 0 < L ^ (1 - ζ) := by
  have hL0 : 0 < L := by linarith
  refine ⟨?_, ?_, Real.rpow_pos_of_pos hL0 _⟩
  · rw [← Real.rpow_add hL0, sub_add_cancel, Real.rpow_one]
  · calc L ^ (1 - ζ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      _ = L := Real.rpow_one L

/-- **DG Lemma 3.6** (`lem-mid-scale-max`, DG:1079–1085): for bounded `U`, `ζ ∈ (0,1)`,
`C ≥ 1` and `p > 0` there are `K, δ₀` such that for `δ ∈ (0, δ₀)` and **every**
`A ∈ (1, e^{(log δ⁻¹)^{1−ζ}})`,
`P[max_{z,w∈U, |z−w| ≤ Cδ} |ĥ_{δ/A}(z) − ĥ_δ(w)| > ζ log δ⁻¹] ≤ K δ^p`. -/
theorem dg_lemma36 (hW : IsWhiteNoise P W) {U : Set ℂ} (hU : Bornology.IsBounded U) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ < 1) {C : ℝ} (hC : 1 ≤ C) {p : ℝ} (hp : 0 < p) :
    ∃ K δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A : ℝ, 1 < A →
      A < Real.exp (Real.log δ⁻¹ ^ (1 - ζ)) →
      P {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ C * δ ∧
        ζ * Real.log δ⁻¹ < |DDDF.phiVer W P (δ / A) 1 z ω - DDDF.phiVer W P δ 1 w ω|} ≤
        ENNReal.ofReal (K * δ ^ p) := by
  have := hW.isProbabilityMeasure
  obtain ⟨x₀, s, hs1, hUs⟩ := exists_box_of_isBounded hU
  have hs : 0 < s := by linarith
  have hbox := (isCompact_ferniqueBox x₀ s).isBounded
  obtain ⟨δ₁, hδ₁, h1⟩ := dg_lemma34 hW hbox (by positivity : 0 < ζ / 6) hp
  obtain ⟨δ₂, hδ₂, h3⟩ := dg_lemma34C hW hbox (by positivity : 0 < ζ / 3)
    (by linarith : 1 ≤ C + 1) hp
  set M : ℝ := 18 * (4 + p) / ζ ^ 2
  set L₀ : ℝ := max 1 (M ^ ζ⁻¹)
  refine ⟨2 * (2 * s + 2) ^ 2 + 2, min (min δ₁ δ₂) (min (1 / 2) (Real.exp (-L₀))),
    lt_min (lt_min hδ₁ hδ₂) (lt_min (by norm_num) (Real.exp_pos _)), fun δ hδ A hA hAL => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδδ₁ : δ < δ₁ := (hδ.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hδδ₂ : δ < δ₂ := (hδ.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have hδ1 : δ < 1 := ((hδ.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)).trans
    (by norm_num)
  set L := Real.log δ⁻¹ with hL_def
  have hLL : L₀ < L := by
    have h := Real.log_lt_log hδ0 ((hδ.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))
    rw [Real.log_exp] at h
    rw [hL_def, Real.log_inv]; linarith
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLL.le
  have hL0 : 0 < L := by linarith
  have hA0 : 0 < A := by linarith
  set v := Real.log A with hv_def
  have hv0 : 0 < v := Real.log_pos hA
  obtain ⟨hsplit, hrL, hr0⟩ := rpow_split hL1 hζ.le
  set r := L ^ (1 - ζ)
  have hvr : v < r := by
    rw [hv_def, Real.log_lt_iff_lt_exp hA0]; exact hAL
  have hLζ : M ≤ L ^ ζ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
      ((le_max_right _ _).trans hLL.le) hζ.le
    rwa [Real.rpow_inv_rpow (by positivity) hζ.ne'] at h
  set δ' := δ / A with hδ'_def
  have hδ'0 : 0 < δ' := div_pos hδ0 hA0
  have hδ'δ : δ' ≤ δ := div_le_self hδ0.le hA.le
  have hlogδ' : Real.log δ'⁻¹ = v + L := by
    rw [hδ'_def, inv_div, Real.log_div hA0.ne' hδ0.ne', hL_def, Real.log_inv, hv_def]; ring
  set m := ⌈2 * s / δ'⌉₊
  set Y := DDDF.phiVer W P δ' 1
  set Z := DDDF.phiVer W P δ 1
  set F1 := {ω | ∃ z ∈ ferniqueBox x₀ s, ∃ w ∈ ferniqueBox x₀ s, ‖z - w‖ ≤ δ' ∧
        ζ / 6 * Real.log δ'⁻¹ < |Y z ω - Y w ω|}
  set F3 := {ω | ∃ z ∈ ferniqueBox x₀ s, ∃ w ∈ ferniqueBox x₀ s, ‖z - w‖ ≤ (C + 1) * δ ∧
        ζ / 3 * L < |Z z ω - Z w ω|}
  set E : Fin (m + 1) × Fin (m + 1) → Set Ω :=
    fun ij => {ω | ζ * L / 3 ≤ |Y (gridPt x₀ s m ij.1 ij.2) ω - Z (gridPt x₀ s m ij.1 ij.2) ω|}
  have hsub : {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ C * δ ∧ ζ * L < |Y z ω - Z w ω|} ⊆
      F1 ∪ (⋃ ij, E ij) ∪ F3 := by
    rintro ω ⟨z, hz, w, hw, hzw, hlt⟩
    obtain ⟨i, j, hg, hzg⟩ := exists_gridPt_near hs hδ'0 (hUs hz)
    set g := gridPt x₀ s m i j
    by_cases hF1 : ζ / 6 * Real.log δ'⁻¹ < |Y z ω - Y g ω|
    · exact Or.inl (Or.inl ⟨z, hUs hz, g, hg, hzg, hF1⟩)
    by_cases hE : ζ * L / 3 ≤ |Y g ω - Z g ω|
    · exact Or.inl (Or.inr (mem_iUnion.2 ⟨(i, j), hE⟩))
    refine Or.inr ⟨g, hg, w, hUs hw, ?_, ?_⟩
    · calc ‖g - w‖ ≤ ‖g - z‖ + ‖z - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ + C * δ := by rw [norm_sub_rev]; linarith
        _ = (C + 1) * δ := by ring
    · push Not at hF1 hE
      have ht : |Y z ω - Z w ω| ≤ |Y z ω - Y g ω| + |Y g ω - Z g ω| + |Z g ω - Z w ω| := by
        have e : Y z ω - Z w ω = (Y z ω - Y g ω) + (Y g ω - Z g ω) + (Z g ω - Z w ω) := by ring
        rw [e]
        exact abs_add_three _ _ _
      have hv2 : ζ / 6 * Real.log δ'⁻¹ ≤ ζ * L / 3 := by
        rw [hlogδ']
        have h2L : v + L ≤ 2 * L := by linarith
        have := mul_le_mul_of_nonneg_left h2L (by positivity : (0 : ℝ) ≤ ζ / 6)
        linarith
      linarith
  -- grid term
  have hy : 0 ≤ ζ * L / 3 := by positivity
  have hEi : ∀ ij, P (E ij) ≤ ENNReal.ofReal (2 * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v))) := by
    intro ij
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (phiVer_diff_point_tail hW hδ0 hδ1.le hA _ hy)
  have hm1 : ((m : ℝ) + 1) ≤ (2 * s + 2) * δ'⁻¹ := by
    have hc : (m : ℝ) < 2 * s / δ' + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : 1 ≤ δ'⁻¹ := one_le_inv_iff₀.2 ⟨hδ'0, hδ'δ.trans hδ1.le⟩
    have e : 2 * s / δ' = 2 * s * δ'⁻¹ := div_eq_mul_inv _ _
    rw [e] at hc
    nlinarith
  have hexp' : δ'⁻¹ = Real.exp (v + L) := by
    rw [← hlogδ', Real.exp_log (inv_pos.2 hδ'0)]
  have hpow : δ ^ p = Real.exp (-(p * L)) := by
    rw [Real.rpow_def_of_pos hδ0, hL_def, Real.log_inv]; ring_nf
  have hgrid : ((m : ℝ) + 1) ^ 2 * (2 * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v))) ≤
      2 * (2 * s + 2) ^ 2 * δ ^ p := by
    have h1 : ((m : ℝ) + 1) ^ 2 ≤ (2 * s + 2) ^ 2 * Real.exp (2 * (v + L)) := by
      rw [show 2 * (v + L) = (v + L) + (v + L) by ring, Real.exp_add, ← hexp']
      nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) hm1 2]
    have h2 : Real.exp (2 * (v + L)) * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v)) ≤
        Real.exp (-(p * L)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      -- `(2v + (2+p)L)·2v ≤ 2(4+p) L r ≤ ζ² L²/9`
      have hk1 : (2 * v + (2 + p) * L) * (2 * v) ≤ (4 + p) * L * (2 * r) := by
        have a1 : 2 * v + (2 + p) * L ≤ (4 + p) * L := by linarith
        exact mul_le_mul a1 (by linarith) (by positivity) (by positivity)
      have hk2 : 18 * (4 + p) ≤ ζ ^ 2 * L ^ ζ := by
        have e : M * ζ ^ 2 = 18 * (4 + p) := by simp only [M]; field_simp
        have := mul_le_mul_of_nonneg_right hLζ (sq_nonneg ζ)
        linarith
      have hk3 : 2 * (4 + p) * L * r * 9 ≤ ζ ^ 2 * L ^ 2 := by
        have e : L ^ 2 = L * r * L ^ ζ := by rw [sq]; nth_rewrite 2 [hsplit]; ring
        rw [e]
        have hLr : 0 ≤ L * r := by positivity
        have := mul_le_mul_of_nonneg_left hk2 hLr
        linarith
      have hq0 : (2 * (v + L) + p * L) * (2 * v) ≤ (ζ * L / 3) ^ 2 := by
        have e1 : 2 * (v + L) + p * L = 2 * v + (2 + p) * L := by ring
        have e2 : (ζ * L / 3) ^ 2 = ζ ^ 2 * L ^ 2 / 9 := by ring
        rw [e1, e2]
        linarith
      have hq : 2 * (v + L) + p * L ≤ (ζ * L / 3) ^ 2 / (2 * v) :=
        (le_div_iff₀ (by positivity)).2 hq0
      rw [neg_div]
      linarith
    rw [hpow]
    calc ((m : ℝ) + 1) ^ 2 * (2 * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v)))
        ≤ (2 * s + 2) ^ 2 * Real.exp (2 * (v + L)) *
            (2 * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * (2 * s + 2) ^ 2 *
          (Real.exp (2 * (v + L)) * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v))) := by ring
      _ ≤ 2 * (2 * s + 2) ^ 2 * Real.exp (-(p * L)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hF1 : P F1 ≤ ENNReal.ofReal (δ ^ p) := (h1 δ' ⟨hδ'0, hδ'δ.trans_lt hδδ₁⟩).trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hδ'0.le hδ'δ hp.le))
  have hF3 : P F3 ≤ ENNReal.ofReal (δ ^ p) := h3 δ ⟨hδ0, hδδ₂⟩
  calc P {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ C * δ ∧ ζ * L < |Y z ω - Z w ω|}
      ≤ P (F1 ∪ (⋃ ij, E ij) ∪ F3) := measure_mono hsub
    _ ≤ P F1 + ∑ ij, P (E ij) + P F3 := (measure_union_le _ _).trans
        (add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl
          (measure_iUnion_fintype_le _ _))) le_rfl)
    _ ≤ ENNReal.ofReal (δ ^ p) + ∑ _ij : Fin (m + 1) × Fin (m + 1),
          ENNReal.ofReal (2 * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v))) +
          ENNReal.ofReal (δ ^ p) :=
        add_le_add (add_le_add hF1 (Finset.sum_le_sum fun ij _ => hEi ij)) hF3
    _ = ENNReal.ofReal (δ ^ p + ((m : ℝ) + 1) ^ 2 *
          (2 * Real.exp (-(ζ * L / 3) ^ 2 / (2 * v))) + δ ^ p) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal ((2 * (2 * s + 2) ^ 2 + 2) * δ ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        linarith

end DG
end LQGMetric
