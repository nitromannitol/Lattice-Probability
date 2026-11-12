/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108K5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K4
import LatticeProb.Bonanno.LQGMetric.Meas.Internal

/-!
# S-cont-law in the frozen form of CONF Lemma 3.3, Step 3

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, C:667–669 and C:1239–1241: "the probability
that the supremum in (3.9) is exactly equal to `(c/100) e^{−ξA} 𝔠_r` is zero … using Axiom III and
the fact that adding a smooth compactly supported function to `h` affects its law in an absolutely
continuous way".

* `CONFZBShiftAC U φ`: the law of the zero-boundary GFF on `U` extended by `0`
  (`IsZBExtField`) is absolutely continuous with respect to its shift by `tφ`, for every `t`
  (Cameron–Martin; `φ` smooth with compact support in `U`, an element of the Cameron–Martin space
  `H¹₀(U)`; CONF C:1229 "a standard calculation for the GFF"). Open node: the statement of the
  Cameron–Martin theorem (Bogachev, *Gaussian Measures*, Thm 2.4.5; for the Dirichlet GFF,
  Berestycki–Powell arXiv:2404.16642, Prop. `lem:CMGFF`).
* `ae_ae_isLength`: Axiom I on the frozen product law.
* **`ae_ae_diam_ne`**: for a countable `A`, an open `V` and a shift `φ = 1` on `V` satisfying
  `CONFZBShiftAC`, for a.e. frozen `w` and a.e. `x`, `diam(A; D_{G w + x}(·,·;V)) ≠ T w` for every
  threshold `T w ∈ (0, ∞)`: the hypotheses `hneG`, `hneF` of `confProp2_8_diam` (S3D108K3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **Cameron–Martin for the zero-boundary GFF** (absolute continuity under the shift `tφ`) -/
def CONFZBShiftAC (U : TopologicalSpace.Opens ℂ) (φ : C(ℂ, ℝ)) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → DistC),
    IsZBExtField U X P → ∀ t : ℝ, P.map X ≪ (P.map X).map fun x => addFun x (t • φ)

variable {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P]

end LQGMetric.CONF
