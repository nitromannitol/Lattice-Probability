/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR3a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirGreen
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent2Circ
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqLip
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2GFF
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqKer
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSupp

/-!
# DGo (3.9) on the unit square (task P2-HEAT3, packet R3, part 1)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, (3.9) (DGo:702–704, citing Hu–Miller–Peres
Prop. 2.1): `Var(ĥ^𝒰_δ(u) − ĥ^𝒰_δ(w)) ≤ A |u − w| / δ`.

On `𝕍 = (0,1)² = sqOpen 0 1`:

* `measKer_circle_eq_dirCircFun`, `dirCircKernel_zero_one_eq`: the Dirichlet circle kernel
  `dirCircKernel 0 1 δ v` is the white-noise kernel `measKerL2 𝕍 (0,∞) σ_{v,δ}` of the circle
  measure used in the GMC identification (`GMCIdent`), via `p_𝕍 = p^D`
  (`KilledHeatSq.killedHeat_sqOpen`);
* `pi_norm_sq_dirCircKernel_sub_eq`: `π ‖K_u − K_w‖² = Var(h_δ(u) − h_δ(w))` for every QZ
  zero-boundary GFF on `𝕍` (`GMCIdent2.pi_inner_measKerL2_circle`, `circleCov_eq_kernel`);
* `pi_norm_sq_dirCircKernel_sub_le_unit`: `≤ (2/δ + 2C)‖u − w‖` — the near miss
  `variance_circle_sub_le` (GMCSqReg, own adaptation of QZ there: `−log max` part by
  LQGDimension's `aAvg_le`, harmonic part by the Lipschitz bound `exists_hS_lip`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq GMCIdent KilledHeat WhiteNoise DZZ

lemma sqOpen_zero_one : sqOpen 0 1 = openSquare := by
  ext z; simp [sqOpen, openSquare]

/-- the white-noise circle kernel of `GMCIdent` is the Dirichlet circle kernel -/
lemma measKer_circle_eq_dirCircFun {δ : ℝ} {v : ℂ} (hδ : 0 < δ) (hB : closedBall v δ ⊆ openSquare)
    (p : ℝ × ℂ) : measKer openSquare (Ioi 0) (circleUnif v δ) p = dirCircFun 0 1 δ v p := by
  unfold measKer wndKernel
  rcases le_or_gt p.1 0 with hs | hs
  · rw [dirCircFun_of_nonpos hs]
    simp [indicator_of_notMem (show p.1 ∉ Ioi (0 : ℝ) from not_lt.2 hs)]
  have ht : (p.1 / 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  simp only [indicator_of_mem (show p.1 ∈ Ioi (0 : ℝ) from hs)]
  rw [show p = (p.1, p.2) from rfl, dirCircFun_of_pos hs]
  by_cases hw : p.2 ∈ openSquare
  · rw [← sqOpen_zero_one] at hw ⊢
    rw [indicator_of_mem hw]
    have hae : (fun y => killedHeat (sqOpen 0 1) (p.1 / 2).toNNReal y p.2) =ᵐ[circleUnif v δ]
        fun y => sqDirKernel 0 1 (p.1 / 2) y p.2 := by
      filter_upwards [CoordReg.ae_mem_closedBall_circleUnif v hδ.le] with y hy
      have hy' : y ∈ sqOpen 0 1 := by
        rw [sqOpen_zero_one]; exact hB hy
      rw [KilledHeatSq.killedHeat_sqOpen one_pos _ ht y p.2 hy' hw, Real.coe_toNNReal _ (by positivity)]
    rw [integral_congr_ae hae, CoordReg.integral_circleUnif_Ico (measurable_sqDirKernel_left
      (by positivity) one_pos p.2), circFn, integral_Ico_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
  · rw [← sqOpen_zero_one] at hw
    rw [indicator_of_notMem hw]
    have : ∀ y, killedHeat (sqOpen 0 1) (p.1 / 2).toNNReal y p.2 = 0 := fun y =>
      killedHeat_eq_zero_of_not_mem_right (isOpen_sqOpen 0 1) ht y hw
    rw [sqOpen_zero_one] at this
    simp [this]

/-- `dirCircKernel 0 1 δ v = measKerL2 𝕍 (0,∞) σ_{v,δ}` -/
theorem dirCircKernel_zero_one_eq {δ : ℝ} {v : ℂ} (hδ : 0 < δ) (hB : closedBall v δ ⊆ openSquare) :
    dirCircKernel 0 1 δ v = measKerL2 openSquare (Ioi 0) (circleUnif v δ) := by
  have hB' : closedBall v δ ⊆ sqOpen 0 1 := sqOpen_zero_one ▸ hB
  have he : measKer openSquare (Ioi 0) (circleUnif v δ) = dirCircFun 0 1 δ v :=
    funext (measKer_circle_eq_dirCircFun hδ hB)
  have hm := memLp_dirCircFun one_pos hδ hB'
  have hm' : MemLp (measKer openSquare (Ioi 0) (circleUnif v δ)) 2 volume := he ▸ hm
  rw [dirCircKernel, dite_eq_left_of_eq_true (eq_true ⟨one_pos, hδ, hB'⟩), measKerL2,
    dite_eq_left_of_eq_true (eq_true hm')]
  exact MemLp.toLp_congr _ _ (ae_of_all _ fun p => (congrFun he p).symm)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- `π ‖K_u − K_w‖² = Var(h_δ(u) − h_δ(w))` for a zero-boundary GFF on `𝕍` -/
theorem pi_norm_sq_dirCircKernel_sub_eq [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) {δ : ℝ}
    {u w : ℂ} (hδ : 0 < δ) (hu : closedBall u δ ⊆ openSquare) (hw : closedBall w δ ⊆ openSquare) :
    π * ‖dirCircKernel 0 1 δ u - dirCircKernel 0 1 δ w‖ ^ 2 =
      Var[fun ω => X ω (foldedCircle u δ) - X ω (foldedCircle w δ); P] := by
  rw [variance_fun_sub (memLp_circle hX hδ hu) (memLp_circle hX hδ hw),
    ← covariance_self (memLp_circle hX hδ hu).aemeasurable,
    ← covariance_self (memLp_circle hX hδ hw).aemeasurable,
    circleCov_eq_kernel hX hδ hδ hu hu, circleCov_eq_kernel hX hδ hδ hu hw,
    circleCov_eq_kernel hX hδ hδ hw hw,
    ← GMCIdent2.pi_inner_measKerL2_circle hδ hδ hu hu,
    ← GMCIdent2.pi_inner_measKerL2_circle hδ hδ hu hw,
    ← GMCIdent2.pi_inner_measKerL2_circle hδ hδ hw hw,
    dirCircKernel_zero_one_eq hδ hu, dirCircKernel_zero_one_eq hδ hw, norm_sub_sq_real,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- **(3.9) on `𝕍`** (near miss `variance_circle_sub_le`): for circles in a set `K ⊆ 𝕍` on
which `hS` is `C`-Lipschitz in the second variable, `π ‖K_u − K_w‖² ≤ (2/δ + 2C)‖u − w‖` -/
theorem pi_norm_sq_dirCircKernel_sub_le_unit {K : Set ℂ} (hKU : K ⊆ openSquare) {C : ℝ}
    (hC : ∀ a ∈ K, ∀ b ∈ K, ∀ b' ∈ K, |hS a b - hS a b'| ≤ C * ‖b - b'‖) {δ : ℝ} {u w : ℂ}
    (hδ : 0 < δ) (hu : closedBall u δ ⊆ K) (hw : closedBall w δ ⊆ K) :
    π * ‖dirCircKernel 0 1 δ u - dirCircKernel 0 1 δ w‖ ^ 2 ≤ (2 / δ + 2 * C) * ‖u - w‖ := by
  obtain ⟨Ω, _, P, X, _, hX⟩ := K3.exists_zeroGFFOn openSquare
  rw [pi_norm_sq_dirCircKernel_sub_eq hX hδ (hu.trans hKU) (hw.trans hKU)]
  exact variance_circle_sub_le hX hKU hC hδ hu hw

end HeatDir
end DGo
end LQGMetric
