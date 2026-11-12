/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L9Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B4

/-!
# D117 packet P-SIM (a): DZZ Lemma 2.9 for similarities with the constant uniform in `b`
(P2-DZZSIM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) lem-scaling-coupling, l. 611–624: the constant is
`C = C(ξ, κ₁, κ₂)` (l. 619), i.e. it does not depend on the translation `b` of `θ v = a v + b`,
nor on the white noise. `dzz_lemma29_sim` (S5L53B5) produces its `C` after `b` and the noises;
its three ingredients are DZZ Lemma 2.8 (`dzz_lemma28_uncond`, `dzz_lemma28_scaled`, already
uniform) and the tail of `sup |ĥ_a^1|` (`dzz_hat_sup_tail`, S2HatTail, l. 628–633), whose
constant is explicit in its proof but hidden behind `∃`. This file:

* `hatTailC a b s` and `dzz_hat_sup_tail_le`: the proof of `dzz_hat_sup_tail` (copied verbatim)
  with its explicit constant `2 e^{M²/(2σ²)} + 4σ²`, `M = (2s/a) C_F`, `σ² = log(b/a) + 1`;
* `dzz_lemma29_simU`: `dzz_lemma29_sim` with `∃ C` moved in front of `b`, `V₁`, the noises and
  the versions (the proof of `dzz_lemma29_sim`, copied, with `dzz_hat_sup_tail_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail WNPush

universe u

/-- the explicit constant of `dzz_hat_sup_tail` -/
def hatTailC (a b s : ℝ) : ℝ :=
  2 * Real.exp (((a / (2 * s))⁻¹ * ferniqueCF) ^ 2 / (2 * (Real.log (b / a) + 1))) +
    4 * (Real.log (b / a) + 1)

lemma hatTailC_pos {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) : 0 < hatTailC a b s := by
  have hl : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).2 hab)
  unfold hatTailC; positivity

theorem dzz_hat_sup_tail_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {x₀ : ℂ} {s : ℝ} (hs : 0 < s) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hY : ∀ x, Y x =ᵐ[P] phi W a b x) :
    ∀ lam : ℝ, 0 ≤ lam →
      P.real {ω | lam ≤ ⨆ v : ferniqueBox x₀ s, |Y v ω|} ≤
        hatTailC a b s * Real.exp (-lam ^ 2 / hatTailC a b s) := by
  intro lam hlam
  have hP := hW.isProbabilityMeasure
  set B := ferniqueBox x₀ s
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox x₀ s)
  have : Nonempty B := ⟨⟨x₀, mem_ferniqueBox_self hs.le⟩⟩
  set X : B → Ω → ℝ := fun v => Y v
  have hX : IsGaussianProcess X P :=
    (isGaussianProcess_phi_comp hW a b (fun v : B => (v : ℂ))).congr fun v => (hY v).symm
  have hint0 : ∀ x, ∫ ω, Y x ω ∂P = 0 := fun x => by
    rw [integral_congr_ae (hY x)]; exact integral_phi hW a b x
  -- increments: `E (Y v − Y u)² ≤ |u − v|²/a²` (eq-hat-h-continuity)
  have hincY : ∀ u v : ℂ, ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ ‖u - v‖ ^ 2 / a ^ 2 := by
    intro u v
    have hm : AEMeasurable (fun ω => phi W a b v ω - phi W a b u ω) P :=
      ((measurable_phi hW a b v).sub (measurable_phi hW a b u)).aemeasurable
    have h0 : ∫ ω, (phi W a b v ω - phi W a b u ω) ∂P = 0 := by
      rw [integral_sub ((memLp_phi hW a b v).integrable one_le_two)
        ((memLp_phi hW a b u).integrable one_le_two), integral_phi hW, integral_phi hW, sub_zero]
    have hae2 : (fun ω => (Y v ω - Y u ω) ^ 2) =ᵐ[P]
        fun ω => (phi W a b v ω - phi W a b u ω) ^ 2 := by
      filter_upwards [hY u, hY v] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae2, ← variance_of_integral_eq_zero hm h0,
      norm_sub_rev]
    exact dzz_variance_hat_sub_le hW ha hab v u
  -- the rescaled fields `G = c Y`, `G' = -c Y` satisfy the hypothesis of DZZ Lemma 2.3
  set c : ℝ := a / (2 * s) with hc
  have hc0 : 0 < c := by positivity
  have hincG : ∀ (ε : ℝ), ε ^ 2 = 1 → ∀ u ∈ B, ∀ v ∈ B,
      ∫ ω, (ε * c * Y v ω - ε * c * Y u ω) ^ 2 ∂P ≤ ‖u - v‖ / s := by
    intro ε hε u hu v hv
    have e : (fun ω => (ε * c * Y v ω - ε * c * Y u ω) ^ 2) =
        fun ω => c ^ 2 * (Y v ω - Y u ω) ^ 2 := by
      funext ω; rw [← mul_sub, mul_pow, mul_pow, hε, one_mul]
    rw [e, integral_const_mul]
    have h1 := hincY u v
    have hr := norm_sub_le_of_mem_ferniqueBox hu hv
    have hr0 := norm_nonneg (u - v)
    calc c ^ 2 * ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ c ^ 2 * (‖u - v‖ ^ 2 / a ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
      _ = ‖u - v‖ * ‖u - v‖ / (4 * s ^ 2) := by rw [hc]; field_simp; ring
      _ ≤ ‖u - v‖ * (2 * s) / (4 * s ^ 2) := by gcongr
      _ ≤ ‖u - v‖ / s := by
          rw [div_le_div_iff₀ (by positivity) hs]; nlinarith [mul_nonneg hr0 hs.le]
  have hsupG : ∀ (ε : ℝ), ε ^ 2 = 1 →
      Integrable (fun ω => ⨆ v : B, ε * c * Y v ω) P ∧
        ∫ ω, (⨆ v : B, ε * c * Y v ω) ∂P ≤ ferniqueCF := by
    intro ε hε
    refine dzz_lemma23_continuous hs ?_ (fun v _ => ?_) (hincG ε hε)
      (fun ω => (continuous_const.mul (hYc ω)).continuousOn)
    · exact (hX.smul fun _ => ε * c).congr fun v => Eventually.of_forall fun ω => rfl
    · rw [integral_const_mul, hint0, mul_zero]
  -- back to `Y` and `-Y`
  have hsup_eq : ∀ (ε : ℝ) ω, (⨆ v : B, ε * Y v ω) = c⁻¹ * ⨆ v : B, ε * c * Y v ω := by
    intro ε ω
    rw [Real.mul_iSup_of_nonneg (inv_nonneg.2 hc0.le)]
    congr 1; funext v; field_simp
  have hYsup : ∀ (ε : ℝ), ε ^ 2 = 1 → Integrable (fun ω => ⨆ v : B, ε * Y v ω) P ∧
      ∫ ω, (⨆ v : B, ε * Y v ω) ∂P ≤ c⁻¹ * ferniqueCF := by
    intro ε hε
    obtain ⟨h1, h2⟩ := hsupG ε hε
    simp_rw [hsup_eq ε]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc0.le)
  obtain ⟨hi1, hM1⟩ := hYsup 1 (by norm_num)
  obtain ⟨hi2, hM2⟩ := hYsup (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hi1 hM1 hi2 hM2
  -- Borell–TIS
  set M : ℝ := c⁻¹ * ferniqueCF
  have hl : 0 ≤ Real.log (b / a) :=
    Real.log_nonneg ((one_le_div ha).2 hab)
  set σ : ℝ := Real.sqrt (Real.log (b / a) + 1)
  have hσ2 : σ ^ 2 = Real.log (b / a) + 1 := Real.sq_sqrt (by linarith)
  have hvar : ∀ v : B, Var[X v; P] ≤ σ ^ 2 := by
    intro v
    rw [hσ2, variance_congr (hY v), variance_phi hW ha hab]
    linarith
  have hσp : 0 < σ ^ 2 := by rw [hσ2]; linarith
  have hCe : hatTailC a b s = 2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) + 4 * σ ^ 2 := by
    rw [hσ2]; rfl
  rw [hCe]
  have h := tail_iSup_abs_le_gaussian hX (fun v => hint0 v) (fun ω => (hYc ω).comp
    continuous_subtype_val) hi1 hi2 hM1 hM2 hvar hlam
  refine h.trans ?_
  set C := 2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) + 4 * σ ^ 2
  have hC1 : 2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) ≤ C := by simp only [C]; linarith
  have hC2 : 2 * (2 * σ ^ 2) ≤ C := by simp only [C]; nlinarith [Real.exp_pos (M ^ 2 / (2 * σ ^ 2))]
  have hexp : Real.exp (-lam ^ 2 / (2 * (2 * σ ^ 2))) ≤ Real.exp (-lam ^ 2 / C) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (by positivity) hC2

  exact mul_le_mul hC1 hexp (Real.exp_pos _).le (by positivity)

/-- **DZZ Lemma 2.9 for similarities, constant uniform in the translation** (DZZ
lem-scaling-coupling, l. 611–624, `C = C(ξ, κ₁, κ₂)`, l. 619): `dzz_lemma29_sim` with `C`
depending on `(ξ, a)` only, chosen before `b`, the box `V₁`, the noises and the versions. -/
theorem dzz_lemma29_simU {ξ : ℝ} {a : ℂ} (hξ : 0 < ξ) (hξ2 : ξ < 1 / 2) (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℂ) {V₁ : Set ℂ}, V₁ ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) →
    simMap a b '' V₁ ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W W' : WNSpace → Ω → ℝ},
    IsWhiteNoise P W → IsWhiteNoise P W' →
    IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P →
    IsWhiteNoise P (coupledNoise (confHyp_simMap ha b) W W') ∧
    ∀ Z1 Z2 : ℕ → ℂ → Ω → ℝ, (∀ j ω, Continuous fun x => Z1 j x ω) →
      (∀ j ω, Continuous fun x => Z2 j x ω) →
      (∀ j x, Z1 j x =ᵐ[P] etaInf W ((1 / 2 : ℝ) ^ j) x) →
      (∀ j x, Z2 j x =ᵐ[P]
        etaInf (coupledNoise (confHyp_simMap ha b) W W') (‖a‖ * (1 / 2 : ℝ) ^ j) x) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ V₁, ∃ j : ℕ, lam ≤ |Z1 j v ω - Z2 j (simMap a b v) ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hs : (0 : ℝ) < 1 - 2 * ξ := by linarith
  obtain ⟨C1, hC1, h28⟩ := dzz_lemma28_uncond.{u} hξ hξ2
  obtain ⟨C2, hC2, h28s⟩ := dzz_lemma28_scaled.{u} hξ hξ2 hr ha1
  set C3 := hatTailC ‖a‖ 1 (1 - 2 * ξ) with hC3def
  have hC3 : 0 < C3 := hatTailC_pos hr ha1
  refine ⟨9 * max (max C1 C2) C3, by positivity, fun b V₁ hV₁ hV₂ Ω _ P W W' hW hW' hind => ?_⟩
  set Wt := coupledNoise (confHyp_simMap ha b) W W' with hWt_def
  have hWt : IsWhiteNoise P Wt := isWhiteNoise_coupledNoise _ hW hW' hind
  refine ⟨hWt, fun Z1 Z2 hZ1c hZ2c hZ1 hZ2 lam hlam => ?_⟩
  have := hW.isProbabilityMeasure
  set box := ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) with hbox
  set θ := simMap a b
  have hθc : Continuous θ := continuous_simMap a b
  have hj0 : ∀ j : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ j := fun j => by positivity
  have haj : ∀ j : ℕ, ‖a‖ * (1 / 2 : ℝ) ^ j ≤ ‖a‖ := fun j =>
    mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))
  -- continuous versions
  have e1 := fun j : ℕ => exists_continuous_phi hW (hj0 j) 1
  have e2 := fun j : ℕ => exists_continuous_phi hWt (mul_pos hr (hj0 j)) 1
  choose Φ1 hΦ1c hΦ1 using e1
  choose Φ2 hΦ2c hΦ2 using e2
  obtain ⟨H, hHc, hH⟩ := exists_continuous_phi hWt hr 1
  have h3 := dzz_hat_sup_tail_le hWt hr ha1 (x₀ := ⟨ξ, ξ⟩) hs hHc hH
  set D1 : ℕ → ℂ → Ω → ℝ := fun j x ω => Φ1 j x ω - Z1 j x ω
  set D2 : ℕ → ℂ → Ω → ℝ := fun j x ω => Φ2 j x ω - Z2 j x ω
  have hD1c : ∀ j ω, Continuous fun x => D1 j x ω := fun j ω => (hΦ1c j ω).sub (hZ1c j ω)
  have hD2c : ∀ j ω, Continuous fun x => D2 j x ω := fun j ω => (hΦ2c j ω).sub (hZ2c j ω)
  have hD1 : ∀ j x, D1 j x =ᵐ[P] fun ω => phi W ((1 / 2 : ℝ) ^ j) 1 x ω -
      etaInf W ((1 / 2 : ℝ) ^ j) x ω := fun j x => by
    filter_upwards [hΦ1 j x, hZ1 j x] with ω h1 h2
    simp only [D1, h1, h2]
  have hD2 : ∀ j x, D2 j x =ᵐ[P] fun ω => phi Wt (‖a‖ * (1 / 2 : ℝ) ^ j) 1 x ω -
      etaInf Wt (‖a‖ * (1 / 2 : ℝ) ^ j) x ω := fun j x => by
    filter_upwards [hΦ2 j x, hZ2 j x] with ω h1 h2
    simp only [D2, h1, h2]
  -- the coupling identity `ĥ^1_{a2^{-j}}[W̃](θv) − ĥ^1_a[W̃](θv) = ĥ^1_{2^{-j}}[W](v)`
  have hpt : ∀ j v, ∀ᵐ ω ∂P, Φ2 j (θ v) ω - H (θ v) ω = Φ1 j v ω := by
    intro j v
    have c1 := phi_coupledNoise_simMap ha b hW' (W := W) (hj0 j) 1 v
    rw [mul_one] at c1
    have c2 := phi_add_ae hWt (mul_pos hr (hj0 j)) (haj j) ha1 (θ v)
    filter_upwards [c1, c2, hΦ2 j (θ v), hH (θ v), hΦ1 j v] with ω h1 h2 h3 h4 h5
    rw [h3, h4, h5, h2, ← h1]
    ring
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ x : ℂ, Φ2 j (θ x) ω - H (θ x) ω = Φ1 j x ω := by
    have hq : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ q : ℚ × ℚ,
        Φ2 j (θ (ratPt q)) ω - H (θ (ratPt q)) ω = Φ1 j (ratPt q) ω := by
      rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro q; exact hpt j (ratPt q)
    filter_upwards [hq] with ω hω j
    have hS : Continuous fun x => Φ2 j (θ x) ω - H (θ x) ω :=
      ((hΦ2c j ω).comp hθc).sub ((hHc ω).comp hθc)
    have := denseRange_ratPt'.equalizer hS (hΦ1c j ω) (funext fun q => hω j q)
    exact fun x => congrFun this x
  set M := max (max C1 C2) C3 with hM
  have hM0 : 0 < M := lt_max_of_lt_right hC3
  set E1 := {ω | ∃ v ∈ box, ∃ j : ℕ, lam / 3 ≤ |D1 j v ω|}
  set E2 := {ω | ∃ v ∈ box, ∃ j : ℕ, lam / 3 ≤ |D2 j v ω|}
  set E3 := {ω | lam / 3 ≤ ⨆ v : box, |H v ω|}
  have hsub : {ω | ∃ v ∈ V₁, ∃ j : ℕ, lam ≤ |Z1 j v ω - Z2 j (θ v) ω|} ≤ᵐ[P] E1 ∪ E2 ∪ E3 := by
    filter_upwards [hall] with ω hω hE
    obtain ⟨v, hv, j, hj⟩ := hE
    have hθv : θ v ∈ box := hV₂ ⟨v, hv, rfl⟩
    have hid : Z1 j v ω - Z2 j (θ v) ω = -D1 j v ω + D2 j (θ v) ω - H (θ v) ω := by
      simp only [D1, D2]; rw [← hω j v]; ring
    rw [hid] at hj
    have hb1 := abs_sub (-D1 j v ω + D2 j (θ v) ω) (H (θ v) ω)
    have hb2 := abs_add_le (-D1 j v ω) (D2 j (θ v) ω)
    rw [abs_neg] at hb2
    have : CompactSpace box := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox _ _)
    have hbdd : BddAbove (range fun u : box => |H u ω|) :=
      (isCompact_range (continuous_abs.comp ((hHc ω).comp continuous_subtype_val))).bddAbove
    have hsup : |H (θ v) ω| ≤ ⨆ u : box, |H u ω| :=
      le_ciSup (f := fun u : box => |H u ω|) hbdd ⟨θ v, hθv⟩
    by_cases c1 : lam / 3 ≤ |D1 j v ω|
    · exact Or.inl (Or.inl ⟨v, hV₁ hv, j, c1⟩)
    by_cases c2 : lam / 3 ≤ |D2 j (θ v) ω|
    · exact Or.inl (Or.inr ⟨θ v, hθv, j, c2⟩)
    · exact Or.inr (show lam / 3 ≤ ⨆ u : box, |H u ω| by linarith)
  have hP1 : P.real E1 ≤ C1 * Real.exp (-(lam / 3) ^ 2 / C1) :=
    h28 hW D1 hD1c hD1 (lam / 3) (by linarith)
  have hP2 : P.real E2 ≤ C2 * Real.exp (-(lam / 3) ^ 2 / C2) :=
    h28s hWt D2 hD2c hD2 (lam / 3) (by linarith)
  have hP3 : P.real E3 ≤ C3 * Real.exp (-(lam / 3) ^ 2 / C3) := h3 (lam / 3) (by linarith)
  have hE : P.real {ω | ∃ v ∈ V₁, ∃ j : ℕ, lam ≤ |Z1 j v ω - Z2 j (θ v) ω|} ≤
      P.real E1 + P.real E2 + P.real E3 :=
    (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans
      ((measureReal_union_le _ _).trans (by linarith [measureReal_union_le (μ := P) E1 E2]))
  have hexp : ∀ c : ℝ, 0 < c → c ≤ M →
      c * Real.exp (-(lam / 3) ^ 2 / c) ≤ M * Real.exp (-lam ^ 2 / (9 * M)) := by
    intro c hc hcM
    refine mul_le_mul hcM (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0.le
    rw [div_pow, neg_div, neg_div, neg_le_neg_iff, div_div, div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcM (sq_nonneg lam)]
  have f1 := hexp C1 hC1 ((le_max_left _ _).trans (le_max_left _ _))
  have f2 := hexp C2 hC2 ((le_max_right _ _).trans (le_max_left _ _))
  have f3 := hexp C3 hC3 (le_max_right _ _)
  have hpos : 0 ≤ M * Real.exp (-lam ^ 2 / (9 * M)) := by positivity
  linarith

end DZZ
