/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcI2L at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3D124
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# D124 packet I2L: the law of a white noise (P2-DZZI0)

Decision D124 (`decisions/DEC-124.md` §5 I2L, D124-4: law transfer). No DZZ content: the law
`wnLaw W P = P.map (wnPath W)` of a white noise on the path space `WNCanon = (WNSpace → ℝ)` does not
depend on `(Ω, P, W)`, and the coordinate process `wnCanon` is a white noise under it.

* **`isWhiteNoise_wnCanon`**: as `DDDF.isWhiteNoise_comp` (`Measure.map_map`).
* **`wnLaw_eq`**: uniqueness of the law. Adapted from `DDDF.map_restrict_phi_eq` /
  `DDDF.map_phi_eq` (Papers/DDDF/P10Law.lean: finite-dimensional laws by characteristic
  functionals, `Pitt.dual_apply_eq_sum`, then mathlib `IsProjectiveLimit.unique`), the same pattern
  as `IsZBGFFProcess.map_eq` (Field/ZeroBoundaryLaw.lean).
* `measure_path_le_wnLaw`, `measure_path_eq_wnLaw`: `P(wnPath W ∈ E) ≤ wnLaw W P E` for every
  `E` (outer measure, no measurability), with equality for measurable `E`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}

lemma measurable_wnPath (hW : IsWhiteNoise P W) : Measurable (wnPath W) :=
  measurable_pi_iff.2 hW.measurable

/-- **The coordinate process is a white noise under the law of a white noise.** -/
theorem isWhiteNoise_wnCanon (hW : IsWhiteNoise P W) : IsWhiteNoise (wnLaw W P) wnCanon := by
  refine ⟨fun f => measurable_pi_apply f, fun {ι} _ f c => ?_⟩
  have h := hW.hasLaw f c
  have hm : Measurable (fun x : WNCanon => ∑ i, c i * wnCanon (f i) x) :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply (f i)).const_mul _
  refine ⟨hm.aemeasurable, ?_⟩
  rw [wnLaw, Measure.map_map hm (measurable_wnPath hW), ← h.map_eq]
  rfl

open Classical in
/-- The law of `L((W f)_{f ∈ I})` for a linear functional `L` (as `DDDF.hasLaw_dual_phi`). -/
lemma hasLaw_dual_wn (hW : IsWhiteNoise P W) (I : Finset WNSpace)
    (L : StrongDual ℝ (I → ℝ)) :
    HasLaw (fun ω => L (fun i : I => W i ω))
      (gaussianReal 0 (‖∑ i : I, L (Pitt.unitVec i) • (i : WNSpace)‖ ^ 2).toNNReal) P := by
  refine (hW.hasLaw (fun i : I => (i : WNSpace)) (fun i => L (Pitt.unitVec i))).congr ?_
  refine Eventually.of_forall fun ω => ?_
  simp only
  rw [Pitt.dual_apply_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Equal finite-dimensional laws of two white noises (as `DDDF.map_restrict_phi_eq`). -/
lemma map_restrict_wnPath_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (I : Finset WNSpace) :
    P.map (fun ω => I.restrict (wnPath W ω)) = P'.map (fun ω => I.restrict (wnPath W' ω)) := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  have hm : Measurable (fun ω => I.restrict (wnPath W ω)) :=
    (Finset.measurable_restrict I).comp (measurable_wnPath hW)
  have hm' : Measurable (fun ω => I.restrict (wnPath W' ω)) :=
    (Finset.measurable_restrict I).comp (measurable_wnPath hW')
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.continuous.measurable hm, Measure.map_map L.continuous.measurable hm']
  congr 1
  exact (hasLaw_dual_wn hW I L).map_eq.trans (hasLaw_dual_wn hW' I L).map_eq.symm

/-- **The law of a white noise is unique** (as `DDDF.map_phi_eq`, `IsZBGFFProcess.map_eq`). -/
theorem wnLaw_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') :
    wnLaw W P = wnLaw W' P' := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  have h1 := isProjectiveLimit_map (P := P) (X := W) (measurable_wnPath hW).aemeasurable
  have h2 := isProjectiveLimit_map (P := P') (X := W') (measurable_wnPath hW').aemeasurable
  have e : (fun I : Finset WNSpace => P.map (fun ω => I.restrict (W · ω))) =
      fun I => P'.map (fun ω => I.restrict (W' · ω)) :=
    funext fun I => map_restrict_wnPath_eq hW hW' I
  rw [e] at h1
  exact h1.unique h2

/-- `P(wnPath W ∈ E) ≤ wnLaw W P E` for every `E ⊆ WNCanon`. -/
theorem measure_path_le_wnLaw (hW : IsWhiteNoise P W) (E : Set WNCanon) :
    P (wnPath W ⁻¹' E) ≤ wnLaw W P E :=
  Measure.le_map_apply (measurable_wnPath hW).aemeasurable E

theorem measure_path_eq_wnLaw (hW : IsWhiteNoise P W) {E : Set WNCanon}
    (hE : MeasurableSet E) : P (wnPath W ⁻¹' E) = wnLaw W P E :=
  (Measure.map_apply (measurable_wnPath hW) hE).symm

end DZZ
end LQGMetric
