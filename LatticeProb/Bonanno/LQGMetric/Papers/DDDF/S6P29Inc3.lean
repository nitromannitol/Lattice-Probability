/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Inc3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Inc2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Split3

/-!
# DDDF Prop 29 on `(−1,2)²`: the first-term increments, hence the proposition (task P2-DDDFP29c)

DDDF arXiv:1904.08021, `tightness.tex` DD:1571–1576 (first term of (6.97)): for
`x, x' ∈ [−1+d, 2−d]²`, uniformly in `t ∈ (0, 1/2)`,
`∫_0^1 ∫_D (firstKer t s x y − firstKer t s x' y)² dy ds ≤ C |x − x'|` (`p29FirstIncr`).

Own route (DEVIATIONS; the paper's sketch uses (6.96), which is not uniform near `∂D`):
`(ΔF)² ≤ 2M |ΔF|` with the uniform bound `M = firstConst d 3` (`HeatSq.abs_firstKer_le`), the
`L¹(D)` bound `∫_D |ΔF| dy ≤ 6 c₀ √2 |x − x'| / √s` (`lintegral_abs_firstKer_sub_le`), and
`∫_0^1 s^{-1/2} ds = 2`. With `dddfProp29Sq_of_firstIncr` this proves `DDDFProp29Sq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq

lemma firstConst_nonneg' {d L : ℝ} : 0 ≤ firstConst d L := by
  unfold firstConst
  have h2 := imgConst_nonneg (d / 2) L
  have h4 := imgConst_nonneg (d / 4) L
  have c2 := hkConst_nonneg (d / 2)
  have c4 := hkConst_nonneg (d / 4)
  exact add_nonneg (add_nonneg (mul_nonneg (by nlinarith) c2)
    (add_nonneg (by linarith) (mul_nonneg (by nlinarith) c4))) c2

/-- `∫_0^1 s^{-1/2} ds = 2`. -/
lemma lintegral_inv_sqrt_Ioc :
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt s)⁻¹ = ENNReal.ofReal 2 := by
  have e : EqOn (fun s : ℝ => ENNReal.ofReal (Real.sqrt s)⁻¹)
      (fun s => ENNReal.ofReal (s ^ (-(1 / 2 : ℝ)))) (Ioc 0 1) := by
    intro s hs; simp only; rw [Real.sqrt_eq_rpow, Real.rpow_neg hs.1.le]
  rw [setLIntegral_congr_fun measurableSet_Ioc e]
  have hi : IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi)
    ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun s hs => Real.rpow_nonneg hs.1.le _)),
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num)),
    show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, Real.one_rpow, Real.zero_rpow (by norm_num)]
  norm_num

/-- **DDDF Prop 29, first-term increments** (DD:1571–1576), uniformly in `t ∈ (0, 1/2)`. -/
theorem p29FirstIncr : P29FirstIncr := by
  intro d hd
  set M := firstConst d 3
  have hM : 0 ≤ M := firstConst_nonneg'
  set K0 := 2 * M * (6 * (incConst * Real.sqrt 2))
  have hK0 : 0 ≤ K0 :=
    mul_nonneg (by linarith) (mul_nonneg (by norm_num)
      (mul_nonneg (by linarith [two_le_incConst]) (Real.sqrt_nonneg _)))
  refine ⟨2 * K0 + 1, by linarith, fun t ht x x' hxre hxim hx're hx'im => ?_⟩
  set δ := ‖x - x'‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hD := measurableSet_sqOpen (-1) 3
  have hin : ∀ s ∈ Ioc (0 : ℝ) 1, ∫⁻ y in sqOpen (-1) 3,
      ENNReal.ofReal ((firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y) ^ 2) ≤
        ENNReal.ofReal (K0 * δ * (Real.sqrt s)⁻¹) := by
    intro s hs
    calc ∫⁻ y in sqOpen (-1) 3,
          ENNReal.ofReal ((firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y) ^ 2)
        ≤ ∫⁻ y in sqOpen (-1) 3, ENNReal.ofReal (2 * M) *
            ENNReal.ofReal |firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y| := by
          refine lintegral_mono_ae ((ae_restrict_iff' hD).mpr
            (Filter.Eventually.of_forall fun y hy => ?_))
          rw [← ENNReal.ofReal_mul (by linarith)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := abs_firstKer_le ht.1 hs.1 (by linarith [hs.2]) hd (by norm_num) hxre hxim hy
          have h2 := abs_firstKer_le ht.1 hs.1 (by linarith [hs.2]) hd (by norm_num) hx're hx'im hy
          have h3 : |firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y| ≤ 2 * M :=
            (abs_sub _ _).trans (by linarith)
          nlinarith [abs_nonneg (firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y),
            sq_abs (firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y)]
      _ = ENNReal.ofReal (2 * M) * ∫⁻ y in sqOpen (-1) 3,
            ENNReal.ofReal |firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y| :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * M) * ENNReal.ofReal (6 * (incConst / Real.sqrt (s / 2) * δ)) := by
          gcongr; exact lintegral_abs_firstKer_sub_le ht.1 hs.1 (by norm_num) x x'
      _ = ENNReal.ofReal (K0 * δ * (Real.sqrt s)⁻¹) := by
          rw [← ENNReal.ofReal_mul (by linarith)]
          congr 1
          have hs0 := Real.sqrt_pos.mpr hs.1
          have h20 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
          rw [Real.sqrt_div hs.1.le]
          field_simp
          ring
  calc ∫⁻ s in Ioc 0 1, ∫⁻ y in sqOpen (-1) 3,
        ENNReal.ofReal ((firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y) ^ 2)
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (K0 * δ) * ENNReal.ofReal (Real.sqrt s)⁻¹ := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall fun s hs => ?_))
        rw [← ENNReal.ofReal_mul (mul_nonneg hK0 hδ)]; exact hin s hs
    _ = ENNReal.ofReal (K0 * δ) * ENNReal.ofReal 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_inv_sqrt_Ioc]
    _ ≤ ENNReal.ofReal ((2 * K0 + 1) * δ) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK0 hδ)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- **DDDF Proposition 29 on `(−1,2)²`** (DDDF arXiv:1904.08021, `tightness.tex:1501–1601`). -/
theorem dddfProp29Sq : DDDFProp29Sq := dddfProp29Sq_of_firstIncr p29FirstIncr

end P29WN
end DDDF
end LQGMetric
