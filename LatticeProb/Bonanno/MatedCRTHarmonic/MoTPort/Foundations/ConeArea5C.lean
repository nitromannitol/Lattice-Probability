/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea5C at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea5B

/-!
# Cone area, part 12: (b3) and `ConeRefMeas` from the whole-plane sup-moment bound

The last input of (b3) is the whole-plane version at the origin of QZ's interior area
fractional-moment bound `AtomlessUncond.P3bBoundArea` (proved for the free-boundary GFF on `ℍ` by
QZ `AreaP3b.fracMoment_area_interior`; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.3
and §3.2 (14)–(15)):

  `WPSupMoment γ`: for a whole-plane GFF `X` normalized by `X_1(0)` and `0 < p ≤ 1`,
  `E (sup_{k ≥ n} μ_{2^{-k}}(B̄(0,2^{-n})))^p ≤ C 2^{n(γ²p²/2 − p(2 + γ²/2))}`.

From it:

* `ae_tight_logFactor`: a.s. the approximations weighted by `max(2^{-k},|w|)^{−γc}`, `c < Q`, are
  tight at `0` (QZ `AtomlessUncond.ae_tsum_ne_top_of_moments` — Borel–Cantelli with a geometric
  rate — and `AtomlessUncond.tight_of_balls`, exactly as in QZ `AreaNoAtom`);
* **`b3_of_supMoment`**: the cone-area tightness statement (b3), by ConeArea5 (comparison) and ConeArea5B
  (growth of the cone shift with `c = α + η < Q`);
* **`coneRefMeas_of_supMoment`**, **`exists_isQuantumCone_of_supMoment`**: `ConeRefMeas γ W` and
  quantum cones of every weight `W > 0` (via `ConeArea4.coneRefMeas_of_tight`,
  `Cone.exists_isQuantumCone`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea5

open QuantumZipper LQGMetric ConeArea4

end ConeArea5
end MatedCRTHarmonic.MoTPort
