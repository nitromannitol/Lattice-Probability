/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108A at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Changed: docstring wording of the module and of a section heading. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L33M
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# D108: the true statement forms of CONF Lemmas 3.3 and 3.6 (modulo additive constants)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`. Decision `decisions/DEC-108.md`.

CONF's field is normalized, `h_1(0) = 0` (C:347), and CONF conditions on fields "viewed modulo
additive constant" (C:1154, 1187). With `IsWholePlaneGFF` (any random additive constant) the
σ-algebras are read modulo additive constants, as in CONF's own proof (C:1431–1432:
"`(𝓑^•_τ, h|_{𝓑^•_τ})` is a.s. determined by `h|_{ℂ∖𝔘}`"), which uses that the set `𝓑^•_τ` is a
local set of the field modulo constants. This file has the mod-constant objects and the exact open nodes of D108:

* `hullSigma0`, `localSigma0`, `filledBallSigmaAt0` : `σ(A, h|_A)` modulo additive constants
  (D32's dyadic-hull form with the mean-zero pairings `GM.fieldSigma0On` of D79);
* `IsLocalSetDet0` : local set modulo constants (CONF Lemma 2.1 as used at C:1431);
* `CONFLem3_6AtAE0` : **CONF Lemma 3.6** modulo additive constants (D108 (a));
* `confFatEv`, `CONFLem3_3W` : the weakened **Lemma 3.3** (3.9′) that Lemma 3.6 consumes
  (D108 (b): C:1208 fails for one-square-wide corridors and circle slivers);
* `CONFFatChainA`, `CONFFatChainB` : the deterministic square-chain claims replacing C:1208;
* `CONFZBMetricN` (S3D108P1) : CONF Remark 1.2 (C:324–338), the metric of the zero-boundary
  part as a measurable function of `h̊^U` (D108 (c));
* `condFKG_freeze2` : the conditioning argument of Step 3 with `G^U` allowed to depend on the
  frozen outside field (proved).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-! ## σ-algebras modulo additive constants and CONF Lemma 3.6

D110 P1: `hullSigma0`, `localSigma0`, `IsLocalSetDet0` now live in `Blueprint/M2Defs.lean`,
`filledBallSigmaAt0` in `Blueprint/CONFDefs.lean` and `CONFLem3_6AtAE0` in
`Blueprint/CONFResults.lean` (text unchanged); the `CONF.` names are aliases. -/

export Blueprint (hullSigma0 localSigma0 filledBallSigmaAt0 IsLocalSetDet0 CONFLem3_6AtAE0)

/-! ## CONF Lemma 3.3, weakened form (D108 (b)) -/

section L33W
variable {Ω : Type} [MeasurableSpace Ω]

/-- the event (3.9′) (D108 (b)): for every component `V` of `U`,
`sup_{u,v ∈ V_{δr/3}} D_h(u, v; V_{δr/4}) ≤ (c/100) 𝔠_r e^{ξ h_r(z)}` (CONF (3.9), C:1205, has
`V_{δr/2}`; `V_{δr/3}` contains the centre of every full square of `V`) -/
def confFatEv (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (h : Ω → DistC)
    (p : CONFParams) (r : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) : Set Ω :=
  {ω | ∀ x ∈ confU r p.δ z T,
    internalDiam (D (h ω))
      (innerPart (connectedComponentIn (confU r p.δ z T) x) (p.δ * r / 3))
      (innerPart (connectedComponentIn (confU r p.δ z T) x) (p.δ * r / 4))
      ≤ ENNReal.ofReal (p.c / 100 * scaleFac ξ cc (h ω) r z)}

end L33W

/-! ## The square-chain claims replacing C:1208 -/

/-- `k, k'` index edge-adjacent squares of the grid -/
def SqAdj (k k' : ℤ × ℤ) : Prop :=
  (k'.1 - k.1) ^ 2 + (k'.2 - k.2) ^ 2 = 1

/-- a chain of at most `K + 1` edge-adjacent squares of `𝒮^z_ε(𝔸_{3r,4r}(z))` from the square
`k₀` to a square in `S` -/
def SqChain (ε : ℝ) (z : ℂ) (r : ℝ) (K : ℕ) (k₀ : ℤ × ℤ) (S : Set (ℤ × ℤ)) : Prop :=
  ∃ (m : ℕ) (k : ℕ → ℤ × ℤ), m ≤ K ∧ k 0 = k₀ ∧
    (∀ i ≤ m, k i ∈ confSqIdx ε z (annulus z (3 * r) (4 * r))) ∧
    (∀ i < m, SqAdj (k i) (k (i + 1))) ∧ k m ∈ S

/-! ## CONF Remark 1.2: the metric of the zero-boundary part (D108 (c)) -/

/-! ## The conditioning argument with `G^U` depending on the frozen outside field -/

section Freeze2

variable {Ω α β : Type} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {P : Measure Ω} [IsProbabilityMeasure P]

end Freeze2

end LQGMetric.CONF
