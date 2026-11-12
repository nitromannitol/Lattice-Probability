/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Shift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi

/-!
# DDDF Proposition 29: the time-shifted white noise (R2, coupling of `φ_t`)

DDDF arXiv:1904.08021, `tightness.tex` DD:1527–1531 ("Coupling"): for `t ∈ (0,1/2)`,
`φ_{√t}(x) = ∫_t^1 ∫ p_{s/2}(x − y) W(dy, ds) =ᵈ φ_t(x) := ∫_0^{1−t} ∫ p_{(t+s)/2}(x − y) W(dy, ds)`.
We realize `φ_t` as `φ_{√t}` of the white noise `W ∘ T_t`, where `T_t g = g(· + t, ·)` is the
linear isometry of `L²(ℝ × ℂ)` given by the measure-preserving shift `(s, y) ↦ (s + t, y)`
(`isWhiteNoise_shift`), so `φ_t` is built from the same `W` as `h` (DD:1532: "using the same
white noise `W`"). Own elementary bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DDDF
namespace P29WN

open WhiteNoise

/-- the time shift `(s, y) ↦ (s + t, y)` -/
def tShift (t : ℝ) (q : ℝ × ℂ) : ℝ × ℂ := (q.1 + t, q.2)

lemma measurePreserving_tShift (t : ℝ) :
    MeasurePreserving (tShift t) (volume : Measure (ℝ × ℂ)) volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) t).prod
    (MeasurePreserving.id (volume : Measure ℂ))
  rw [← Measure.volume_eq_prod] at h
  exact h

/-- `T_t g = g ∘ tShift t` as a linear isometry of `L²(ℝ × ℂ)` -/
def shiftL2 (t : ℝ) : WNSpace →ₗᵢ[ℝ] WNSpace :=
  Lp.compMeasurePreservingₗᵢ ℝ (tShift t) (measurePreserving_tShift t)

lemma coeFn_shiftL2 (t : ℝ) (g : WNSpace) : (shiftL2 t g : ℝ × ℂ → ℝ) =ᵐ[volume] g ∘ tShift t :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_tShift t)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **The shifted white noise** `W ∘ T_t` is a white noise. -/
theorem isWhiteNoise_shift (hW : IsWhiteNoise P W) (t : ℝ) :
    IsWhiteNoise P (fun f => W (shiftL2 t f)) where
  measurable f := hW.measurable _
  hasLaw {ι} _ f c := by
    have h := hW.hasLaw (fun i => shiftL2 t (f i)) c
    have e : ∑ i, c i • shiftL2 t (f i) = shiftL2 t (∑ i, c i • f i) := by
      simp [map_sum, map_smul]
    rwa [e, LinearIsometry.norm_map] at h

end P29WN
end DDDF
end LQGMetric
