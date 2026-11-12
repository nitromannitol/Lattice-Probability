/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6TailsAB2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB

/-!
# DDDF (6.102)/(6.103) for `[0,A] × [0,B]`: scaling and decoupling (task P2-DDDF6e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1608–1613, 1639–1647: `S6.law_hi`, `S6.len_cmp`,
`S6.tail_decomp` for `rectAB A B` (same proofs, general shape):
`L(φ_{δ,a}, R_{A,B}) =ᵈ a L^{(n)}_{A/a,B/a}` for `δ = a 2^{-n}` (DDDF (2.30)), and both tails of
`L^{(δ)}_{A,B}` are bounded by the Gaussian tail of `sup_{[0,m]²} |φ_{a,1}|` plus the tails of
`a L^{(n)}_{A/a,B/a}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6AB

open WhiteNoise SupTail S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- `L(φ_{δ,a}, R_{A,B}) =ᵈ a L^{(n)}_{A/a,B/a}` for `δ = a 2^{-n}` (DDDF (2.30), l. 1613) -/
theorem law_hi_AB (hW : IsWhiteNoise P W) (n : ℕ) {a : ℝ} (ha0 : 0 < a) (A B : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    P {ω | lenObs ξ (phiVer W P (a * (2 : ℝ)⁻¹ ^ n) a) (rectAB A B) ω ∈ S} =
      P {ω | a * lenObs ξ (phiMN W P 0 n) (rectAB (a⁻¹ * A) (a⁻¹ * B)) ω ∈ S} := by
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
  set R := rectAB (a⁻¹ * A) (a⁻¹ * B)
  have hrR : rectAB A B = rectAB (a * (a⁻¹ * A)) (a * (a⁻¹ * B)) := by
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul, one_mul]
  set T : Set ℝ≥0∞ := {v | a * v.toReal ∈ S}
  have hT : MeasurableSet T := (measurable_const.mul ENNReal.measurable_toReal) hS
  have h1 : {ω | lenObs ξ Hi (rectAB A B) ω ∈ S} =
      {ω | crossLenIn ξ (fun x => Y₁ x ω) R.toSet R.side₁ R.side₂ ∈ T} := by
    ext ω
    show (rectLen ξ (fun x => Hi x ω) (rectAB A B)).toReal ∈ S ↔ _
    rw [hrR, rectLen_rectAB_mul _ ha0, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0.le]
    rfl
  have h2 : {ω | a * lenObs ξ (phiMN W P 0 n) R ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) R.toSet R.side₁ R.side₂ ∈ T} := rfl
  rw [h1, h2]
  exact measure_crossLenIn_eq (MarkedRect.isCompact_toSet R)
    (fun ω => (hφ.cont ω).comp (continuous_const.mul continuous_id)) (fun x => hφ.meas _)
    hφ0.cont hφ0.meas hlaw hT

omit [MeasurableSpace Ω] in
/-- pathwise comparison on `R_{A,B}`: if `Y = Lo + Hi` and `|Lo| ≤ M` on `R_{A,B}` then
`e^{-|ξ|M} L(Hi) ≤ L(Y) ≤ e^{|ξ|M} L(Hi)` -/
theorem len_cmp_AB {Y Lo Hi : ℂ → Ω → ℝ} {ω : Ω} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hYc : Continuous fun x => Y x ω)
    (hHc : Continuous fun x => Hi x ω) (hsum : ∀ x, Y x ω = Lo x ω + Hi x ω) {M : ℝ}
    (hM : ∀ x ∈ (rectAB A B).toSet, |Lo x ω| ≤ M) :
    Real.exp (-(|ξ| * M)) * lenObs ξ Hi (rectAB A B) ω ≤ lenObs ξ Y (rectAB A B) ω ∧
      lenObs ξ Y (rectAB A B) ω ≤ Real.exp (|ξ| * M) * lenObs ξ Hi (rectAB A B) ω := by
  have h01 : (0 : ℝ) ≤ (rectAB A B).w := by simpa [rectAB] using hA
  have h01' : (0 : ℝ) ≤ (rectAB A B).h := by simpa [rectAB] using hB
  have hY := rectLen_ne_top (ξ := ξ) (rectAB A B) h01 h01' hYc
  have hH := rectLen_ne_top (ξ := ξ) (rectAB A B) h01 h01' hHc
  have e1 : ∀ x ∈ (rectAB A B).toSet, |Y x ω - Hi x ω| ≤ M := fun x hx => by
    rw [hsum x, add_sub_cancel_right]; exact hM x hx
  have e2 : ∀ x ∈ (rectAB A B).toSet, |Hi x ω - Y x ω| ≤ M := fun x hx => by
    rw [abs_sub_comm]; exact e1 x hx
  have u1 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := (rectAB A B).side₁)
    (B := (rectAB A B).side₂) e1
  have u2 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := (rectAB A B).side₁)
    (B := (rectAB A B).side₂) e2
  change rectLen ξ _ _ ≤ _ * rectLen ξ _ _ at u1 u2
  have t1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH) u1
  have t2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY) u2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at t1 t2
  refine ⟨?_, t1⟩
  calc Real.exp (-(|ξ| * M)) * lenObs ξ Hi (rectAB A B) ω
      ≤ Real.exp (-(|ξ| * M)) * (Real.exp (|ξ| * M) * lenObs ξ Y (rectAB A B) ω) :=
        mul_le_mul_of_nonneg_left t2 (Real.exp_pos _).le
    _ = lenObs ξ Y (rectAB A B) ω := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- **Decoupling** (DDDF l. 1613, 1639–1647): both tails of `L^{(δ)}_{A,B}`, `δ = a 2^{-n}` -/
theorem tail_decomp_AB (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) (n : ℕ) {a : ℝ} (ha12 : 1 / 2 ≤ a)
    (ha1 : a ≤ 1) {A B m : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : 0 < m) (hAm : A ≤ m)
    (hBm : B ≤ m) {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    P {ω | Real.exp (ξ * (ferniqueCF * Real.sqrt (8 * m * m) + u)) * t ≤
        lenObs ξ (phiVer W P (a * (2 : ℝ)⁻¹ ^ n) 1) (rectAB A B) ω} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) +
        P {ω | t ≤ a * lenObs ξ (phiMN W P 0 n) (rectAB (a⁻¹ * A) (a⁻¹ * B)) ω} ∧
    P {ω | lenObs ξ (phiVer W P (a * (2 : ℝ)⁻¹ ^ n) 1) (rectAB A B) ω ≤
        Real.exp (-(ξ * (ferniqueCF * Real.sqrt (8 * m * m) + u))) * t} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) +
        P {ω | a * lenObs ξ (phiMN W P 0 n) (rectAB (a⁻¹ * A) (a⁻¹ * B)) ω ≤ t} := by
  have hP := hW.isProbabilityMeasure
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha12
  have hd0 : 0 < a * (2 : ℝ)⁻¹ ^ n := by positivity
  have hda : a * (2 : ℝ)⁻¹ ^ n ≤ a :=
    mul_le_of_le_one_right ha0.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hY := isPhiVersion_phiVer hW hd0 (hda.trans ha1)
  have hLo := isPhiVersion_phiVer hW ha0 ha1
  have hHi := isPhiVersion_phiVer hW hd0 hda
  set Y := phiVer W P (a * (2 : ℝ)⁻¹ ^ n) 1
  set Lo := phiVer W P a 1
  set Hi := phiVer W P (a * (2 : ℝ)⁻¹ ^ n) a
  set M := ferniqueCF * Real.sqrt (8 * m * m) + u
  have hG : ∀ᵐ ω ∂P, ∀ x, Y x ω = Lo x ω + Hi x ω := by
    refine ae_eq_of_continuous_modification (Y₂ := fun x ω => Lo x ω + Hi x ω) hY.cont
      (fun ω => (hLo.cont ω).add (hHi.cont ω)) fun x => ?_
    filter_upwards [hY.ae_eq x, hLo.ae_eq x, hHi.ae_eq x, phi_add_ae hW hd0 hda ha1 x] with
      ω h1 h2 h3 h4
    rw [h1, h4, h2, h3]; ring
  have hGc : P {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} = 0 := ae_iff.1 hG
  set E1 := {ω | ¬ ∀ x ∈ ferniqueBox 0 m, |Lo x ω| ≤ M}
  have hE1 : P E1 ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) :=
    low_sup_tail_box hW hm hu ha12 ha1
  have hsubR := rectAB_toSet_sub hAm hBm
  have habs : |ξ| = ξ := abs_of_nonneg hξ
  constructor
  · have hlaw := law_hi_AB (ξ := ξ) hW n ha0 A B (S := Ici t) measurableSet_Ici
    simp only [mem_Ici] at hlaw
    have hsub : {ω | Real.exp (ξ * M) * t ≤ lenObs ξ Y (rectAB A B) ω} ⊆
        {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} ∪ E1 ∪ {ω | t ≤ lenObs ξ Hi (rectAB A B) ω} := by
      intro ω hω
      by_contra hn
      simp only [mem_union, not_or] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      simp only [mem_ofPred_eq, not_not, E1, not_le] at h1 h2 h3
      have hcmp := (len_cmp_AB (ξ := ξ) hA hB (hY.cont ω) (hHi.cont ω) h1
        (fun x hx => h2 x (hsubR hx))).2
      rw [habs] at hcmp
      have hω' : Real.exp (ξ * M) * t ≤ lenObs ξ Y (rectAB A B) ω := hω
      have := mul_lt_mul_of_pos_left h3 (Real.exp_pos (ξ * M))
      linarith
    calc _ ≤ P {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} + P E1 +
            P {ω | t ≤ lenObs ξ Hi (rectAB A B) ω} :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl))
      _ ≤ 0 + ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) +
            P {ω | t ≤ a * lenObs ξ (phiMN W P 0 n) (rectAB (a⁻¹ * A) (a⁻¹ * B)) ω} := by
          rw [hGc, hlaw]
          exact add_le_add (add_le_add le_rfl hE1) le_rfl
      _ = _ := by rw [zero_add]
  · have hlaw := law_hi_AB (ξ := ξ) hW n ha0 A B (S := Iic t) measurableSet_Iic
    simp only [mem_Iic] at hlaw
    have hsub : {ω | lenObs ξ Y (rectAB A B) ω ≤ Real.exp (-(ξ * M)) * t} ⊆
        {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} ∪ E1 ∪ {ω | lenObs ξ Hi (rectAB A B) ω ≤ t} := by
      intro ω hω
      by_contra hn
      simp only [mem_union, not_or] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      simp only [mem_ofPred_eq, not_not, E1, not_le] at h1 h2 h3
      have hcmp := (len_cmp_AB (ξ := ξ) hA hB (hY.cont ω) (hHi.cont ω) h1
        (fun x hx => h2 x (hsubR hx))).1
      rw [habs] at hcmp
      have hω' : lenObs ξ Y (rectAB A B) ω ≤ Real.exp (-(ξ * M)) * t := hω
      have := mul_lt_mul_of_pos_left h3 (Real.exp_pos (-(ξ * M)))
      linarith
    calc _ ≤ P {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} + P E1 +
            P {ω | lenObs ξ Hi (rectAB A B) ω ≤ t} :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl))
      _ ≤ 0 + ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) +
            P {ω | a * lenObs ξ (phiMN W P 0 n) (rectAB (a⁻¹ * A) (a⁻¹ * B)) ω ≤ t} := by
          rw [hGc, hlaw]
          exact add_le_add (add_le_add le_rfl hE1) le_rfl
      _ = _ := by rw [zero_add]

end S6AB
end DDDF
end LQGMetric
