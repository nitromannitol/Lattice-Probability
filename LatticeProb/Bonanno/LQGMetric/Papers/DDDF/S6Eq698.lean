/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Eq698 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Sup
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldGrad

/-!
# DDDF (6.98): `e^{-C} λ_n ≤ λ_{n+r} ≤ e^{C} λ_n` (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1608–1613 (`eq:AprioriMul`). We follow DDDF's proof: with `a = 2^{-r}` and `δ = a 2^{-n}`,

* `φ_{δ,1} = φ_{a,1} + φ_{δ,a}` (DDDF's `φ_{0,r}` and `φ_{r,n+r}`), so a.s.
  `e^{-ξ sup|φ_{a,1}|} L(φ_{δ,a}) ≤ L(φ_{δ,1}) ≤ e^{ξ sup|φ_{a,1}|} L(φ_{δ,a})` (`S6.len_cmp`);
* "with high probability `sup_{[0,1]²} |φ_{0,r}| ≤ C`" (`S6.low_sup_tail`);
* "`L^{(r,n+r)}_{1,1} =ᵈ 2^{-r} L^{(n)}_{2^r,2^r}`" (`S6.law_hi`, scaling as in (2.30)) and
  "a.s. `L^{(n)}_{1,2} ≤ L^{(n)}_{2^r,2^r} ≤ L^{(n)}_{2,1}`" (`lenObs_rectAB_mono`; we use the
  shapes `(1,3)` and `(3,1)` of Cor 17 and Prop 18 directly);
* "by the tightness result, … with high probability `L_{1,2} ≥ e^{-C} λ_n`, `L_{2,1} ≤ e^{C} λ_n`":
  Cor 17 (`dddf_cor17`), Prop 18 (`dddf_prop18`) and `Λ_∞ < ∞` (Theorem 20, hypothesis `hΛ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

namespace S6

/-- `L(φ_{δ,a}(·)) =ᵈ a L^{(n)}_{1/a,1/a}` for `δ = a 2^{-n}` (scaling, DDDF (2.30) and l. 1613) -/
theorem law_hi (hW : IsWhiteNoise P W) (n : ℕ) {a : ℝ} (ha0 : 0 < a) {S : Set ℝ}
    (hS : MeasurableSet S) :
    P {ω | lenObs ξ (phiVer W P (a * (2 : ℝ)⁻¹ ^ n) a) (rectAB 1 1) ω ∈ S} =
      P {ω | a * lenObs ξ (phiMN W P 0 n) (rectAB a⁻¹ a⁻¹) ω ∈ S} := by
  have := hW.isProbabilityMeasure
  have hd0 : 0 < a * (2 : ℝ)⁻¹ ^ n := by positivity
  have hda : a * (2 : ℝ)⁻¹ ^ n ≤ a :=
    mul_le_of_le_one_right ha0.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hφ := isPhiVersion_phiVer hW hd0 hda
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le n)
  set Hi := phiVer W P (a * (2 : ℝ)⁻¹ ^ n) a
  set Y₁ : ℂ → Ω → ℝ := fun x ω => Hi ((a : ℂ) * x) ω
  have hra : a * (2 : ℝ)⁻¹ ^ n / a = (2 : ℝ)⁻¹ ^ n := by field_simp
  have hrb : a / a = (2 : ℝ)⁻¹ ^ 0 := by rw [div_self ha0.ne', pow_zero]
  have hlaw := map_modification_scale hW hd0 hda ha0 (Y₁ := Y₁) (Y₂ := phiMN W P 0 n)
    (fun x => hφ.meas _) hφ0.meas (fun x => hφ.ae_eq _)
    (fun x => by rw [hra, hrb]; exact hφ0.ae_eq x) (F := id) measurable_id
  simp only [id] at hlaw
  set R := rectAB a⁻¹ a⁻¹
  have hrR : rectAB 1 1 = rectAB (a * a⁻¹) (a * a⁻¹) := by rw [mul_inv_cancel₀ ha0.ne']
  set T : Set ℝ≥0∞ := {v | a * v.toReal ∈ S}
  have hT : MeasurableSet T := (measurable_const.mul ENNReal.measurable_toReal) hS
  have h1 : {ω | lenObs ξ Hi (rectAB 1 1) ω ∈ S} =
      {ω | crossLenIn ξ (fun x => Y₁ x ω) R.toSet R.side₁ R.side₂ ∈ T} := by
    ext ω
    show (rectLen ξ (fun x => Hi x ω) (rectAB 1 1)).toReal ∈ S ↔ _
    rw [hrR, rectLen_rectAB_mul _ ha0, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0.le]
    rfl
  have h2 : {ω | a * lenObs ξ (phiMN W P 0 n) R ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) R.toSet R.side₁ R.side₂ ∈ T} := rfl
  rw [h1, h2]
  exact measure_crossLenIn_eq (MarkedRect.isCompact_toSet R)
    (fun ω => (hφ.cont ω).comp (continuous_const.mul continuous_id)) (fun x => hφ.meas _)
    hφ0.cont hφ0.meas hlaw hT

omit [MeasurableSpace Ω] in
/-- pathwise comparison: if `Y = Lo + Hi` and `|Lo| ≤ M` on `[0,1]²` then
`e^{-|ξ|M} L(Hi) ≤ L(Y) ≤ e^{|ξ|M} L(Hi)` -/
theorem len_cmp {Y Lo Hi : ℂ → Ω → ℝ} {ω : Ω} (hYc : Continuous fun x => Y x ω)
    (hHc : Continuous fun x => Hi x ω) (hsum : ∀ x, Y x ω = Lo x ω + Hi x ω) {M : ℝ}
    (hM : ∀ x ∈ (rectAB 1 1).toSet, |Lo x ω| ≤ M) :
    Real.exp (-(|ξ| * M)) * lenObs ξ Hi (rectAB 1 1) ω ≤ lenObs ξ Y (rectAB 1 1) ω ∧
      lenObs ξ Y (rectAB 1 1) ω ≤ Real.exp (|ξ| * M) * lenObs ξ Hi (rectAB 1 1) ω := by
  have h01 : (0 : ℝ) ≤ (rectAB 1 1).w := by simp [rectAB]
  have h01' : (0 : ℝ) ≤ (rectAB 1 1).h := by simp [rectAB]
  have hY := rectLen_ne_top (ξ := ξ) (rectAB 1 1) h01 h01' hYc
  have hH := rectLen_ne_top (ξ := ξ) (rectAB 1 1) h01 h01' hHc
  have e1 : ∀ x ∈ (rectAB 1 1).toSet, |Y x ω - Hi x ω| ≤ M := fun x hx => by
    rw [hsum x, add_sub_cancel_right]; exact hM x hx
  have e2 : ∀ x ∈ (rectAB 1 1).toSet, |Hi x ω - Y x ω| ≤ M := fun x hx => by
    rw [abs_sub_comm]; exact e1 x hx
  have u1 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := (rectAB 1 1).side₁) (B := (rectAB 1 1).side₂) e1
  have u2 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := (rectAB 1 1).side₁) (B := (rectAB 1 1).side₂) e2
  change rectLen ξ _ _ ≤ _ * rectLen ξ _ _ at u1 u2
  have t1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH) u1
  have t2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY) u2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at t1 t2
  refine ⟨?_, t1⟩
  have hpos := Real.exp_pos (|ξ| * M)
  calc Real.exp (-(|ξ| * M)) * lenObs ξ Hi (rectAB 1 1) ω
      ≤ Real.exp (-(|ξ| * M)) * (Real.exp (|ξ| * M) * lenObs ξ Y (rectAB 1 1) ω) :=
        mul_le_mul_of_nonneg_left t2 (Real.exp_pos _).le
    _ = lenObs ξ Y (rectAB 1 1) ω := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- upper median bound: `P(X > m) < 1/2 ⇒ med X ≤ m` -/
theorem lowerMedian_le_of [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) {m : ℝ}
    (h : P {ω | m < X ω} < 2⁻¹) : lowerMedianLaw (P.map X) ≤ m := by
  have hA : 2⁻¹ ≤ P {ω | X ω ≤ m} := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : P univ ≤ P {ω | X ω ≤ m} + P {ω | m < X ω} := by
      refine (measure_mono fun ω _ => ?_).trans (measure_union_le _ _)
      rcases le_or_gt (X ω) m with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    rw [measure_univ] at h1
    have h2 := ENNReal.add_lt_add hlt h
    rw [ENNReal.inv_two_add_inv_two] at h2
    exact absurd h1 (not_le.2 h2)
  refine (le_measure_Iic_iff_lowerQuantile_le inv_two_pos' inv_two_lt_one').1 ?_
  rw [Measure.map_apply hX measurableSet_Iic]
  exact hA

/-- lower median bound: `P(X < m) < 1/2 ⇒ m ≤ med X` -/
theorem le_lowerMedian_of [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) {m : ℝ}
    (h : P {ω | X ω < m} < 2⁻¹) : m ≤ lowerMedianLaw (P.map X) := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := (le_measure_Iic_iff_lowerQuantile_le (μ := P.map X) inv_two_pos'
    inv_two_lt_one').2 le_rfl
  rw [Measure.map_apply hX measurableSet_Iic] at h1
  exact absurd (h1.trans (measure_mono fun ω hω => lt_of_le_of_lt (mem_preimage.1 hω) hlt))
    (not_le.2 h)

end S6

end DDDF
end LQGMetric
