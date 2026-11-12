/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P10Space at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law
import Mathlib.Probability.Independence.Basic

/-!
# The enlarged probability space of DDDF Prop 10

DDDF (arXiv:1904.08021, `tightness.tex` l. 541–543) couple `W` with `W̃` using an extra white
noise independent of `W` ("the rest of the white noises are chosen to be independent"). Given a
white noise `W` on `(Ω, P)`, the product `(Ω × Ω, P ⊗ P)` carries the two independent white noises
`W₁ = W ∘ fst`, `W₂ = W ∘ snd` (`isWhiteNoise_fst`, `isWhiteNoise_snd`, `indepFun_fst_snd_noise`).
By `measure_crossLenIn_phiVer_eq`, crossing-length probabilities of `φ_{a,b}` computed on the
enlarged space (with `W₁`, or with any other white noise such as the coupled `W̃`) agree with
those computed from `W` on `(Ω, P)` (`measure_crossLenIn_le_prod`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {P : Measure Ω}
  {P₂ : Measure Ω₂}

/-- A white noise pulled back by a measure-preserving map is a white noise. -/
lemma isWhiteNoise_comp {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {π : Ω₂ → Ω}
    (hπ : MeasurePreserving π P₂ P) : IsWhiteNoise P₂ (fun f ω => W f (π ω)) := by
  refine ⟨fun f => (hW.measurable f).comp hπ.measurable, fun {ι} _ f c => ?_⟩
  have h := hW.hasLaw f c
  have hm : Measurable (fun ω => ∑ i, c i * W (f i) ω) :=
    Finset.measurable_sum _ fun i _ => (hW.measurable (f i)).const_mul _
  refine ⟨(hm.comp hπ.measurable).aemeasurable, ?_⟩
  have e := Measure.map_map hm hπ.measurable (μ := P₂)
  rw [hπ.map_eq] at e
  rw [← h.map_eq, e]
  rfl

lemma isWhiteNoise_fst {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) :
    IsWhiteNoise (P.prod P) (fun f ω => W f ω.1) := by
  have := hW.isProbabilityMeasure
  exact isWhiteNoise_comp hW (measurePreserving_fst)

lemma isWhiteNoise_snd {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) :
    IsWhiteNoise (P.prod P) (fun f ω => W f ω.2) := by
  have := hW.isProbabilityMeasure
  exact isWhiteNoise_comp hW (measurePreserving_snd)

lemma indepFun_fst_snd_noise {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) :
    IndepFun (fun ω f => (fun f ω => W f ω.1) f ω) (fun ω f => (fun f ω => W f ω.2) f ω)
      (P.prod P) := by
  have := hW.isProbabilityMeasure
  exact indepFun_prod (X := fun ω f => W f ω) (Y := fun ω f => W f ω)
    (measurable_pi_iff.2 hW.measurable) (measurable_pi_iff.2 hW.measurable)

/-- Crossing-length probabilities of `φ_{0,n}` transfer to any white noise on any space. -/
theorem measure_crossLenIn_le_eq {ξ : ℝ} {K A B : Set ℂ} (hK : IsCompact K)
    {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ} (hW : IsWhiteNoise P W)
    (hV : IsWhiteNoise P₂ V) (n : ℕ) (c : ℝ≥0∞) :
    P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ c} =
      P₂ {ω | crossLenIn ξ (fun x => phiMN V P₂ 0 n x ω) K A B ≤ c} :=
  measure_crossLenIn_phiVer_eq (S := Iic c) hK hW hV (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le n)) measurableSet_Iic

end DDDF
end LQGMetric
