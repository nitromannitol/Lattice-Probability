/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Mom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamLvl
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect

/-!
# DDDF Prop 28 Part 1 Step 1 for the family: moments of small crossings (task P2-DDDF28U)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1414–1424 ("the same bounds as those obtained in the
proof of Proposition 27", i.e. `eq:inequa`, l. 1356–1362, which uses scaling of the field and the
right tails), for the field `φ_δ` (l. 1648). Here:

* `moment_of_tail`: a right tail `P(L ≥ e^s a) ≤ C e^{-cs²/log s}` (`s > 2`) gives
  `E L^q ≤ K₀ a^q` with `K₀ = K₀(q, c, C)` (same computation as `s6_moment_L31`, DDDF l. 1218);
* `map_phiVer_motion`: the law of `φ_{a,b}` is invariant under `x ↦ u x + c`, `|u| = 1`
  (as `map_phiMN_motion`);
* `lintegral_len21V_pow`: `E L(u 2^{-K} R_{2,1} + c, φ_{δ,2^{-K}})^q =
  2^{-Kq} E L_{2,1}(φ_{2^K δ, 1})^q` (scaling, `map_modification_scale`, DDDF (2.30)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28U

open LFPP T20E Blueprint WhiteNoise S6D

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **moments from the right tail** (as in `s6_moment_L31`, DDDF l. 1218) -/
theorem moment_of_tail (q : ℕ) (hq : 1 ≤ q) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (L : Ω → ℝ) (a : ℝ), IsProbabilityMeasure P → Measurable L →
      (∀ ω, 0 ≤ L ω) → 0 < a →
      (∀ s : ℝ, 2 < s → P {ω | Real.exp s * a ≤ L ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s))) →
      ∫⁻ ω, ENNReal.ofReal (L ω ^ q) ∂P ≤ ENNReal.ofReal (K₀ * a ^ q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set x₀ : ℝ := max 2 ((2 * (q + 1) / c) ^ 2)
  have hx₀ : 2 ≤ x₀ := le_max_left _ _
  set K₀ : ℝ := Real.exp (q * x₀) + q * C * Real.exp (-1 * x₀) / 1
  refine ⟨K₀, by positivity, fun L a hP hLm hL0 ha0 t18 => ?_⟩
  set X : Ω → ℝ := fun ω => max 0 (Real.log (L ω / a))
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => le_max_left _ _
  have hXm : Measurable X :=
    measurable_const.max (Real.measurable_log.comp (hLm.div_const a))
  have hLX : ∀ ω, L ω ≤ a * Real.exp (X ω) := by
    intro ω
    rcases le_or_gt (L ω) a with h | h
    · exact h.trans (le_mul_of_one_le_right ha0.le (Real.one_le_exp (hX0 ω)))
    · have hpos : 0 < L ω / a := div_pos (ha0.trans h) ha0
      have : Real.log (L ω / a) ≤ X ω := le_max_right _ _
      have h2 := Real.exp_le_exp.2 this
      rw [Real.exp_log hpos] at h2
      rw [div_le_iff₀ ha0] at h2; linarith
  have htail : ∀ t, x₀ < t → (q : ℝ) * Real.exp (q * t) * P.real {ω | t ≤ X ω} ≤
      (q * C) * Real.exp (-1 * t) := by
    intro t ht
    have ht2 : 2 < t := lt_of_le_of_lt hx₀ ht
    have hsub : {ω | t ≤ X ω} ⊆ {ω | Real.exp t * a ≤ L ω} := by
      intro ω hω
      have hω' : t ≤ X ω := hω
      have hXpos : 0 < X ω := by linarith
      have hX : X ω = Real.log (L ω / a) := by
        rcases max_choice 0 (Real.log (L ω / a)) with h | h
        · exact absurd (h ▸ hXpos : (0 : ℝ) < 0) (lt_irrefl 0)
        · exact h
      have hLa : 0 < L ω / a := by
        by_contra hc
        rw [not_lt] at hc
        rw [hX] at hXpos
        rcases eq_or_lt_of_le hc with h0 | h0
        · rw [h0, Real.log_zero] at hXpos; exact lt_irrefl 0 hXpos
        · have : L ω / a ≥ 0 := div_nonneg (hL0 ω) ha0.le
          linarith
      have h1 : Real.exp t ≤ L ω / a := by
        rw [← Real.exp_log hLa]; exact Real.exp_le_exp.2 (hX ▸ hω')
      show Real.exp t * a ≤ L ω
      rw [le_div_iff₀ ha0] at h1; linarith
    have hP1 : P.real {ω | t ≤ X ω} ≤ C * Real.exp (-c * t ^ 2 / Real.log t) := by
      have := (measure_mono (μ := P) hsub).trans (t18 t ht2)
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hsq : 2 * (q + 1) / c ≤ √t := by
      have h1 : (2 * (q + 1) / c) ^ 2 < t := lt_of_le_of_lt (le_max_right _ _) ht
      exact (Real.lt_sqrt (by positivity)).2 h1 |>.le
    have hkey : (q : ℝ) * t + -c * t ^ 2 / Real.log t ≤ -1 * t := by
      have hl := T20B.log_le_two_sqrt (show 0 < t by linarith)
      have hst : 0 < √t := Real.sqrt_pos.2 (by linarith)
      have hss : √t * √t = t := Real.mul_self_sqrt (by linarith)
      have h3 : (q + 1) * Real.log t ≤ c * t := by
        have h4 : 2 * (q + 1) ≤ √t * c := (div_le_iff₀ hc).1 hsq
        nlinarith
      rw [neg_mul, neg_div, ← sub_eq_add_neg, sub_le_iff_le_add, div_eq_mul_inv]
      have : (q + 1) * t ≤ c * t ^ 2 * (Real.log t)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hlt]; nlinarith
      linarith
    calc (q : ℝ) * Real.exp (q * t) * P.real {ω | t ≤ X ω}
        ≤ (q : ℝ) * Real.exp (q * t) * (C * Real.exp (-c * t ^ 2 / Real.log t)) := by gcongr
      _ = (q * C) * Real.exp (q * t + -c * t ^ 2 / Real.log t) := by rw [Real.exp_add]; ring
      _ ≤ (q * C) * Real.exp (-1 * t) := by gcongr
  obtain ⟨hint, hbd⟩ := integral_exp_le_of_tail hX0 hXm.aemeasurable hq0 (by linarith)
    one_pos (by positivity) htail
  have hdom : ∀ ω, L ω ^ q ≤ a ^ q * Real.exp (q * X ω) := by
    intro ω
    calc L ω ^ q ≤ (a * Real.exp (X ω)) ^ q := pow_le_pow_left₀ (hL0 ω) (hLX ω) q
      _ = a ^ q * Real.exp (q * X ω) := by rw [mul_pow, ← Real.exp_nat_mul]
  have hintL : Integrable (fun ω => L ω ^ q) P := by
    refine (hint.const_mul (a ^ q)).mono' ((hLm.pow_const q).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hL0 ω) q)]; exact hdom ω
  rw [← ofReal_integral_eq_lintegral_ofReal hintL (Filter.Eventually.of_forall fun ω =>
    pow_nonneg (hL0 ω) q)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ ω, L ω ^ q ∂P ≤ ∫ ω, a ^ q * Real.exp (q * X ω) ∂P :=
        integral_mono hintL (hint.const_mul _) hdom
    _ = a ^ q * ∫ ω, Real.exp (q * X ω) ∂P := integral_const_mul _ _
    _ ≤ a ^ q * K₀ := by gcongr
    _ = K₀ * a ^ q := by ring

/-- the law of `φ_{a,b}` is invariant under motions (as `map_phiMN_motion`) -/
theorem map_phiVer_motion (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (u : Circle) (c : ℂ) :
    P.map (fun ω => (fun x => phiVer W P a b ((u : ℂ) * x + c) ω)) =
      P.map (fun ω => (phiVer W P a b · ω)) := by
  have hφ := isPhiVersion_phiVer hW ha hab
  refine (map_ker_eq hW (phiKernelL2 a b) (motionL2 u c)
    (Y := phiVer W P a b) (Y₂ := fun x => phiVer W P a b ((u : ℂ) * x + c)) hφ.meas
    (fun x => hφ.meas _) (fun x => hφ.ae_eq x) (fun x => ?_)).symm
  refine (hφ.ae_eq ((u : ℂ) * x + c)).trans (Filter.Eventually.of_forall fun ω => ?_)
  simp only [phi, phiKernelL2_motion ha]

/-- the crossing length of `u 2^{-K} R_{2,1} + c` as a scaled crossing of `R_{2,1}` -/
lemma len21_eq_scale (g : ℂ → ℝ) (K : ℕ) (j : Circle × ℂ) :
    len21 ξ g K j = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
      rectLen ξ (fun x => g ((j.1 : ℂ) * ((((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * x) + j.2)) (rectAB 2 1) := by
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  unfold len21
  rw [T20B.mot_image, T20B.mot_image, T20B.mot_image, crossLenIn_image_motion, image_mul_rectAB_toSet hr,
    image_mul_rectAB_side₁ hr, image_mul_rectAB_side₂ hr]
  have := rectLen_rectAB_mul (ξ := ξ) (fun x => g ((j.1 : ℂ) * x + j.2)) hr 2 1
  unfold rectLen at this ⊢
  rw [this]

/-- **scaling of the small crossings for `φ_δ`** (DDDF (2.30) for the family):
`E L(u 2^{-K} R_{2,1} + c, φ_{δ,2^{-K}})^q = 2^{-Kq} E L_{2,1}(φ_{2^K δ, 1})^q`. -/
theorem lintegral_len21V_pow (hW : IsWhiteNoise P W) {δ : ℝ} {K : ℕ} (hδ : 0 < δ)
    (hδK : δ ≤ (2 : ℝ)⁻¹ ^ K) (j : Circle × ℂ) (q : ℕ) :
    ∫⁻ ω, len21 ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ K) x ω) K j ^ q ∂P =
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ K) ^ q) *
        ∫⁻ ω, rectLen ξ (fun x => phiVer W P ((2 : ℝ) ^ K * δ) 1 x ω) (rectAB 2 1) ^ q ∂P := by
  have hP := hW.isProbabilityMeasure
  set r : ℝ := (2 : ℝ)⁻¹ ^ K with hr_def
  have hr : 0 < r := by positivity
  have hδ' : 0 < (2 : ℝ) ^ K * δ := by positivity
  have hδ1 : (2 : ℝ) ^ K * δ ≤ 1 := by
    calc (2 : ℝ) ^ K * δ ≤ (2 : ℝ) ^ K * r := by gcongr
      _ = 1 := by rw [hr_def, ← mul_pow]; norm_num
  have hφ := isPhiVersion_phiVer hW hδ hδK
  have hφ' := isPhiVersion_phiVer hW hδ' hδ1
  set φ := phiVer W P δ r
  set φ' := phiVer W P ((2 : ℝ) ^ K * δ) 1
  set u : ℂ := (j.1 : ℂ)
  set Y₁ : ℂ → Ω → ℝ := fun x ω => φ (u * ((r : ℂ) * x) + j.2) ω
  have hY₁c : ∀ ω, Continuous fun x => Y₁ x ω := fun ω =>
    (hφ.cont ω).comp ((continuous_const.mul (continuous_const.mul continuous_id)).add
      continuous_const)
  have hY₁m : ∀ x, Measurable (Y₁ x) := fun x => hφ.meas _
  -- the law of `Y₁` is that of `φ'`
  have hG : Measurable fun (g : ℂ → ℝ) (x : ℂ) => g ((r : ℂ) * x) :=
    measurable_pi_iff.2 fun x => measurable_pi_apply _
  have hm1 : Measurable fun ω => (fun z => φ (u * z + j.2) ω) :=
    measurable_pi_iff.2 fun z => hφ.meas _
  have hm2 : Measurable fun ω => (φ · ω) := measurable_pi_iff.2 fun z => hφ.meas _
  have hlawA : P.map (fun ω => (Y₁ · ω)) = P.map (fun ω => fun x => φ ((r : ℂ) * x) ω) := by
    have e1 : (fun ω => (Y₁ · ω)) = (fun (g : ℂ → ℝ) (x : ℂ) => g ((r : ℂ) * x)) ∘
        (fun ω => (fun z => φ (u * z + j.2) ω)) := rfl
    have e2 : (fun ω => fun x => φ ((r : ℂ) * x) ω) =
        (fun (g : ℂ → ℝ) (x : ℂ) => g ((r : ℂ) * x)) ∘ (fun ω => (φ · ω)) := rfl
    rw [e1, e2, ← Measure.map_map hG hm1, ← Measure.map_map hG hm2,
      map_phiVer_motion hW hδ hδK j.1 j.2]
  have hlawB := map_modification_scale hW hδ hδK hr
    (Y₁ := fun x ω => φ ((r : ℂ) * x) ω) (Y₂ := φ') (fun x => hφ.meas _) hφ'.meas
    (fun x => hφ.ae_eq _) (fun x => by
      have e1 : δ / r = (2 : ℝ) ^ K * δ := by rw [hr_def, inv_pow, div_inv_eq_mul, mul_comm]
      have e2 : r / r = 1 := div_self hr.ne'
      rw [e1, e2]; exact hφ'.ae_eq x) (F := id) measurable_id
  simp only [id] at hlawB
  have hlaw : P.map (fun ω => (Y₁ · ω)) = P.map (fun ω => (φ' · ω)) := hlawA.trans hlawB
  have hcpt := (rectAB 2 1).isCompact_toSet
  have hmL1 : Measurable fun ω => rectLen ξ (fun x => Y₁ x ω) (rectAB 2 1) :=
    measurable_crossLenIn hcpt hY₁c hY₁m
  have hmL2 : Measurable fun ω => rectLen ξ (fun x => φ' x ω) (rectAB 2 1) :=
    measurable_crossLenIn hcpt hφ'.cont hφ'.meas
  have hmapL : P.map (fun ω => rectLen ξ (fun x => Y₁ x ω) (rectAB 2 1)) =
      P.map (fun ω => rectLen ξ (fun x => φ' x ω) (rectAB 2 1)) := by
    ext S hS
    rw [Measure.map_apply hmL1 hS, Measure.map_apply hmL2 hS]
    exact measure_crossLenIn_eq hcpt hY₁c hY₁m hφ'.cont hφ'.meas hlaw hS
  have e : ∀ ω, len21 ξ (fun x => φ x ω) K j ^ q =
      ENNReal.ofReal r ^ q * rectLen ξ (fun x => Y₁ x ω) (rectAB 2 1) ^ q := fun ω => by
    rw [len21_eq_scale, mul_pow]
  simp_rw [e]
  rw [lintegral_const_mul _ (hmL1.pow_const q), ENNReal.ofReal_pow hr.le]
  congr 1
  have hpow : Measurable fun v : ℝ≥0∞ => v ^ q := measurable_id.pow_const q
  rw [← lintegral_map hpow hmL1, hmapL, lintegral_map hpow hmL2]

end S6P28U
end DDDF
end LQGMetric
