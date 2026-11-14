/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.CellScaling.Scaling and ConeDefs at commit fdb5cad;
   selected declarations and their proof closure, with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Pointwise

namespace MatedCRTHarmonic.CellScaling

/-- Brownian rescaling of the boundary-length pair: `t ↦ b^{-1/2} ω(bt)`. -/
def brownRescale (b₀ : ℝ) (ω : MatedCRT.Path2) : MatedCRT.Path2 :=
  ⟨fun t => (b₀ ^ (-(1 / 2 : ℝ))) • ω (b₀ * t), by fun_prop⟩

theorem mesh_mul_two_pow (k : ℕ) : CellFamily.mesh k * (2 : ℝ) ^ k = 1 := by
  unfold CellFamily.mesh
  rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]

theorem mesh_pos (k : ℕ) : 0 < CellFamily.mesh k := by
  unfold CellFamily.mesh; positivity

/-- `unitRescalePath (2^{-k}) (b^{-1/2} Z(b ·)) = Z` for `b = 2^k`. -/
theorem unitRescalePath_brownRescale (k : ℕ) (Z : MatedCRT.Path2) :
    MesoModel.unitRescalePath (CellFamily.mesh k) (brownRescale ((2 : ℝ) ^ k) Z) = Z := by
  ext t
  · simp only [MesoModel.unitRescalePath, brownRescale, ContinuousMap.coe_mk, Prod.smul_fst, smul_eq_mul]
    have hmul : (2 : ℝ) ^ k * (CellFamily.mesh k * t) = t := by
      rw [← mul_assoc, mul_comm ((2 : ℝ) ^ k), mesh_mul_two_pow, one_mul]
    rw [hmul, ← mul_assoc]
    have hsq : (Real.sqrt (CellFamily.mesh k))⁻¹ * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) = 1 := by
      have hm : CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
        unfold CellFamily.mesh; rw [zpow_neg, zpow_natCast]
      rw [hm, Real.sqrt_inv, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
      norm_num
    rw [hsq, one_mul]
  · simp only [MesoModel.unitRescalePath, brownRescale, ContinuousMap.coe_mk, Prod.smul_snd, smul_eq_mul]
    have hmul : (2 : ℝ) ^ k * (CellFamily.mesh k * t) = t := by
      rw [← mul_assoc, mul_comm ((2 : ℝ) ^ k), mesh_mul_two_pow, one_mul]
    rw [hmul, ← mul_assoc]
    have hsq : (Real.sqrt (CellFamily.mesh k))⁻¹ * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) = 1 := by
      have hm : CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
        unfold CellFamily.mesh; rw [zpow_neg, zpow_natCast]
      rw [hm, Real.sqrt_inv, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
      norm_num
    rw [hsq, one_mul]

/-- The mesh-`2^{-k}` cells of `η^b = c⁻¹ η(b ·)`, `b = 2^k`, are the unit cells of `η` shrunk by `c`
(the scaling argument step 5). -/
theorem meshCells_coneRescaleCurve (k : ℕ) (c : ℝ) (η : C(ℝ, ℂ)) :
    meshCells (CellFamily.mesh k) (coneRescaleCurve c ((2 : ℝ) ^ k) η) =
      fun x : ℤ => c⁻¹ • (η '' Icc ((x : ℝ) - 1) x) := by
  funext x
  have hb : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have himg : (fun t : ℝ => (2 : ℝ) ^ k * t) '' Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) =
      Icc ((x : ℝ) - 1) x := by
    rw [Set.image_mul_left_Icc' hb, ← mul_assoc, ← mul_assoc, mul_comm ((2 : ℝ) ^ k),
      mesh_mul_two_pow, one_mul, one_mul]
  ext w
  simp only [meshCells, coneRescaleCurve, ContinuousMap.coe_mk, Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨η ((2 : ℝ) ^ k * t), ⟨(2 : ℝ) ^ k * t, ?_, rfl⟩, ?_⟩
    · rw [← himg]; exact ⟨t, ht, rfl⟩
    · rw [Complex.real_smul]
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    rw [← himg] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t, ht, by rw [Complex.real_smul]⟩

end MatedCRTHarmonic.CellScaling
