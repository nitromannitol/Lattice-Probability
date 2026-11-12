/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.PathLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Node W7 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), together with the de-integration lemma of
W5(ii). Both are steps of the proof of `WilliamsDriftDecomposition` (L14).

`map_eq_of_forall_finset`: if `P` on `Ω` and `P'` on `Ω'` are finite measures and
`X : Ω → (ℝ≥0 → ℝ)`, `X' : Ω' → (ℝ≥0 → ℝ)` are a.e. measurable path-valued maps, then
`P.map X = P'.map X'` on `ℝ≥0 → ℝ` as soon as all finite-dimensional restrictions have equal
laws. This is the assertion used to finish W6: equality of the finite-dimensional laws of
`Z_c` and `Ŷ` implies equality of the path laws. It generalizes `WedgeRes.map_path_eq` (which is
the case of pre-Brownian motions, using the known projective family of `BrownianReal`) to
arbitrary two-space pairs.

Source: Kolmogorov extension uniqueness, in the form available in mathlib —
`ProbabilityTheory.isProjectiveLimit_map`
(`Mathlib/Probability/Process/FiniteDimensionalLaws.lean`; the law of a process is the projective
limit of its finite-dimensional distributions) together with
`MeasureTheory.IsProjectiveLimit.unique`
(`Mathlib/MeasureTheory/Constructions/Projective.lean`: the projective limit of a family of
*finite* measures is unique). The one-space version is
`ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq`. Nothing here is original.

`eqOn_of_setIntegral_Ioc_eq`: a function `f : ℝ → ℝ` that is right-continuous at every `x ≥ 0`
(continuity within `[x, ∞)`) is determined on `[0, ∞)` by the values `∫_{(r,r']} f` of its
integrals over the intervals `(r, r'] ⊆ [0, ∞)`. This is W5(ii): the killed finite-dimensional
identities of W5(i) are equal for `p = Ŷ` and for the reversed path over every `(r, r']`, and the
integrands (which are right-continuous for continuous `g`) are recovered by de-integration.

Source: `blueprint/EXT_PP_BLUEPRINT.md` §A.1 W5(ii). Own elementary proof (the blueprint gives no
argument): right continuity of `f` and `g` at `x` makes `f - g` strictly positive on a
right-neighbourhood `(x, x + ε]`, and an integrable function that is strictly positive on an
interval of positive measure has positive integral there, contradicting the vanishing of
`∫_{(r,r']} (f - g)`.
-/

noncomputable section

open MeasureTheory Filter

open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

/-! ## W7 — path laws from finite-dimensional laws -/

/-- **W7.** Two finite measures on two spaces, carrying path-valued maps `X`, `X'` into
`ℝ≥0 → ℝ`, have the same path law as soon as every finite-dimensional restriction has the same
law. (`I.restrict (X ω)` is the function `i ↦ X ω i` on the finite set `I`.) -/
theorem map_eq_of_forall_finset {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {X : Ω → ℝ≥0 → ℝ} {X' : Ω' → ℝ≥0 → ℝ} (hX : AEMeasurable X P) (hX' : AEMeasurable X' P')
    (h : ∀ I : Finset ℝ≥0, P.map (fun ω => I.restrict (X ω)) = P'.map (fun ω => I.restrict (X' ω))) :
    P.map X = P'.map X' := by
  -- the law of a path-valued map is the projective limit of its finite-dimensional laws
  have h1 : IsProjectiveLimit (P.map X)
      (fun I : Finset ℝ≥0 => P.map fun ω => I.restrict (X ω)) :=
    ProbabilityTheory.isProjectiveLimit_map (P := P) (X := fun (t : ℝ≥0) (ω : Ω) => X ω t) hX
  have h2 : IsProjectiveLimit (P'.map X')
      (fun I : Finset ℝ≥0 => P'.map fun ω => I.restrict (X' ω)) :=
    ProbabilityTheory.isProjectiveLimit_map (P := P') (X := fun (t : ℝ≥0) (ω : Ω') => X' ω t) hX'
  have h2' : IsProjectiveLimit (P'.map X')
      (fun I : Finset ℝ≥0 => P.map fun ω => I.restrict (X ω)) := by
    intro I
    rw [h2 I]
    exact (h I).symm
  exact h1.unique h2'

/-! ## W5(ii) — de-integration -/

end QuantumZipper.Williams
