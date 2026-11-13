/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.IG.GFF.AbsContMarkov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCore

/-!
# Markov decomposition of a zero-boundary GFF on a subdomain (task IGR-2a, part 3)

IG1 (arXiv:1201.1496) Prop. 3.1 (`gff::prop::markov`), in the form used in the proof of
Prop. 3.4 (l. 1261): for `Ũ ⊆ D`, the zero-boundary GFF `h` on `D` restricted to `Ũ` is
`h^Ũ + K` with `h^Ũ` a zero-boundary GFF on `Ũ` and `K` harmonic on `Ũ`, independent of `h^Ũ`.

`exists_zb_markov` builds such a triple on one probability space, for every open `D` disjoint
from some circle `∂B_ρ(z₀)`: from a whole-plane GFF `h` normalized by `h_ρ(z₀) = 0`, the
whole-plane Markov property (LQGMetric `DFGPS.markov_normAt`, i.e. LM Lemma 2.1 =
GMSh arXiv:1807.07511 Lemma 2.2 at a general circle; `MarkovFinal.lmLem2_1`) gives
`h = 𝔥_D + h̊_D` and `h = 𝔥_Ũ + h̊_Ũ`; then `h̊_D|_Ũ = h̊_Ũ|_Ũ + (𝔥_Ũ − 𝔥_D)|_Ũ`, where `𝔥_Ũ` and
`𝔥_D` are measurable for `σ(h|_{ℂ∖Ũ})` (`σ(h|_{ℂ∖D}) ⊆ σ(h|_{ℂ∖Ũ})`, `fieldSigmaClosed_mono`)
and hence independent of `h̊_Ũ` (Berestycki–Powell arXiv:2404.16642 Thm 1.52 proof: the
nested decomposition `H₀¹(D) = H₀¹(Ũ) ⊕ Harm`). The law of `h̊_D` is that of every zero-boundary
GFF on `D` (LQGMetric `IsZeroBoundaryGFF.map_eq`). Own assembly of these sourced facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

open LQGMetric QuantumZipper Blueprint

lemma resOn_add (U D : Opens ℂ) (a b : DistOn D) :
    resOn U D (a + b) = resOn U D a + resOn U D b := rfl

end MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
