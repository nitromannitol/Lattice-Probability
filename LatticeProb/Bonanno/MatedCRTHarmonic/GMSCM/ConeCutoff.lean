/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.ConeCutoff at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.Normalized
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Transfer
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCM
import LatticeProb.Bonanno.LQGMetric.Field.MarkovZB

/-!
# A smooth cutoff of the cone logarithm away from its root

On a compactly contained observation region in the punctured unit disk, the
cone correction `γ(-log ‖z‖)` agrees with a compactly supported smooth test
function. The test function vanishes on the unit normalization circle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

namespace MatedCRTHarmonic.GMSCM

/-- A finite-energy cutoff of the cone logarithm on an observation region
strictly inside the punctured unit disk. -/
theorem exists_cone_log_cutoff (γ : ℝ) (V : Opens ℂ)
    (hK : IsCompact (closure (V : Set ℂ)))
    (hV : closure (V : Set ℂ) ⊆ ball (0 : ℂ) 1 \ {0}) :
    ∃ φ : TestC,
      (∀ z ∈ (V : Set ℂ), φ z = γ * (-Real.log ‖z‖)) ∧
      Real.circleAverage (testCont φ) 0 1 = 0 ∧
      tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 \ {0} := by
  let O : Set ℂ := ball (0 : ℂ) 1 \ {0}
  have hO : IsOpen O := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨χ, hχ, hχ1⟩ := exists_cutoff_of_isCompact hK hO hV
  let g : ℂ → ℝ := fun z => γ * (-Real.log ‖z‖)
  have hg : InnerProductSpace.HarmonicOnNhd g O := by
    intro z hz
    have hz0 : z ≠ 0 := by
      simpa using hz.2
    have heq : (-(γ : ℝ)) • (fun w : ℂ => Real.log ‖w‖) = g := by
      funext w
      simp only [Pi.smul_apply, smul_eq_mul, g]
      ring
    rw [← heq]
    exact (AnalyticAt.harmonicAt_log_norm
      (f := fun w : ℂ => w) analyticAt_id hz0).const_smul
  let F : ℂ → ℝ := fun z => χ z * g z
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    contDiff_mul_of_tsupport hO hχ.1 (contDiffOn_of_harmonicOnNhd hg) hχ.2.2
  have hFc : HasCompactSupport F := hχ.2.1.mul_right
  let φ : TestC := ⟨F, hFs, hFc, subset_univ _⟩
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro z hz
    have hzK : z ∈ closure (V : Set ℂ) := subset_closure hz
    simp only [φ, TestFunction.coe_mk, F, g, hχ1 z hzK, one_mul]
  · rw [Real.circleAverage_congr_sphere (f₂ := fun _ => (0 : ℝ))]
    · simp [Real.circleAverage]
    · intro z hz
      have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
      have hzO : z ∉ O := by
        intro hzO
        have hz' : ‖z‖ < 1 := by
          simpa [O, mem_ball, dist_zero_right] using hzO.1
        linarith
      have hFO : tsupport F ⊆ O := (tsupport_mul_subset_left).trans hχ.2.2
      exact image_eq_zero_of_notMem_tsupport (fun h => hzO (hFO h))
  · exact (tsupport_mul_subset_left).trans hχ.2.2

end MatedCRTHarmonic.GMSCM
