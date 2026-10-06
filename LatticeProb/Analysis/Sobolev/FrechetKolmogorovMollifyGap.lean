/-
# The gap between the mollified family and the original family

`FrechetKolmogorovMollifiedCompact` (`FrechetKolmogorovReduce.lean:47`) concludes that the
mollified family `{f ⋆ ρ : f ∈ S}` admits a finite net whose centres lie in the original family
`S`.  The observation recorded in the audit is that the centres may be taken to be the original
functions themselves, because the only obstruction is the mollification error
`‖f ⋆ ρ - f‖_{H^s}`, which the triangle inequality converts into a doubled accuracy.

This file proves that triangle step as `mollifiedNet_centres_in_family`.  Its statement takes two
hypotheses that are not part of `FrechetKolmogorovMollifiedCompact`: first, a finite family
`F : Fin N → Space d → ℝ` with `F i ∈ S` that nets the mollified family through the mollified
centres `F i ⋆ ρ`; and second, the mollification error `‖F i ⋆ ρ - F i‖_{H^s} ≤ η / 4` at those
centres.  From these two hypotheses the theorem concludes that the same finite family `F`, now read
as centres in `S`, nets the mollified family at accuracy `η`.

The second hypothesis is the exact remaining step: it is the mollification approximation, whose
statement is `FrechetKolmogorovMollify` at `FrechetKolmogorovReduce.lean:34`, and whose proof
consumes the uniform translation-continuity supplied by `sobolevNormSq_translate_sub_le`
(`TranslationQuant.lean:25`).  This file does not add a hypothesis to the library statement; it
isolates the step that the library statement leaves implicit.
-/
import LatticeProb.Analysis.Sobolev.FrechetKolmogorovReduce
import LatticeProb.Analysis.Sobolev.Additivity

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The triangle step from mollified centres to original centres.**  Let `S` be a family of
integrable functions, let `ρ` be an integrable function, let `F : Fin N → Space d → ℝ` be a finite
family with `F i ∈ S`, and let `η` be a positive real number.  Assume two hypotheses: every `f ∈ S`
has its mollification `f ⋆ ρ` within `η / 4` in the `H^s` norm of the mollified centre
`F i ⋆ ρ` for some index `i`; and every mollified centre `F i ⋆ ρ` is within `η / 4` in the `H^s`
norm of the original function `F i`.  Then every `f ∈ S` has its mollification `f ⋆ ρ` within `η` in
the `H^s` norm of the original function `F i` for some index `i`. -/
theorem mollifiedNet_centres_in_family {d : ℕ} (s : ℝ) {S : Set (Space d → ℝ)} {ρ : Space d → ℝ}
    (hρint : Integrable ρ) {N : ℕ} (F : Fin N → Space d → ℝ) (hFS : ∀ i, F i ∈ S)
    (hint : ∀ f ∈ S, Integrable f) {η : ℝ} (hη : 0 < η)
    (hnet : ∀ f ∈ S, ∃ i : Fin N,
      sobolevNormSq d s (fun x => convReal f ρ x - convReal (F i) ρ x)
        ≤ ENNReal.ofReal (η / 4))
    (hmoll : ∀ i : Fin N,
      sobolevNormSq d s (fun x => convReal (F i) ρ x - F i x) ≤ ENNReal.ofReal (η / 4)) :
    ∀ f ∈ S, ∃ i : Fin N,
      sobolevNormSq d s (fun x => convReal f ρ x - F i x) ≤ ENNReal.ofReal η := by
  intro f hf
  obtain ⟨i, hi⟩ := hnet f hf
  refine ⟨i, ?_⟩
  have hfi : Integrable (fun x => (convReal f ρ x : ℂ)) :=
    (Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (hint f hf) hρint).ofReal
  have hFi : Integrable (fun x => (convReal (F i) ρ x : ℂ)) :=
    (Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (hint (F i) (hFS i)) hρint).ofReal
  have hFii : Integrable (fun x => (F i x : ℂ)) := (hint (F i) (hFS i)).ofReal
  have h1 : Integrable (fun x => ((convReal f ρ x - convReal (F i) ρ x : ℝ) : ℂ)) :=
    (hfi.sub hFi).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Complex.ofReal_sub])
  have h2 : Integrable (fun x => ((convReal (F i) ρ x - F i x : ℝ) : ℂ)) :=
    (hFi.sub hFii).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Complex.ofReal_sub])
  have htri := sobolevNormSq_add_le d s
    (fun x => convReal f ρ x - convReal (F i) ρ x)
    (fun x => convReal (F i) ρ x - F i x)
    h1 h2
  rw [show (fun x => (convReal f ρ x - convReal (F i) ρ x) + (convReal (F i) ρ x - F i x))
      = fun x => convReal f ρ x - F i x from funext fun x => by ring] at htri
  refine htri.trans ?_
  have hsum : (2 : ℝ≥0∞) * ENNReal.ofReal (η / 4) + 2 * ENNReal.ofReal (η / 4)
      = ENNReal.ofReal η := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 2 * (η / 4))
      (by positivity : (0 : ℝ) ≤ 2 * (η / 4))]
    congr 1
    ring
  calc 2 * sobolevNormSq d s (fun x => convReal f ρ x - convReal (F i) ρ x)
        + 2 * sobolevNormSq d s (fun x => convReal (F i) ρ x - F i x)
      ≤ 2 * ENNReal.ofReal (η / 4) + 2 * ENNReal.ofReal (η / 4) :=
        add_le_add (mul_le_mul_right hi 2) (mul_le_mul_right (hmoll i) 2)
    _ = ENNReal.ofReal η := hsum

end LatticeProb.Sobolev

