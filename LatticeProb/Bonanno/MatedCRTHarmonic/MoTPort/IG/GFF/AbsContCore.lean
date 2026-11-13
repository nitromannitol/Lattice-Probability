/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCore at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCM
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFF

/-!
# IG1 Prop. 3.4, the Cameron–Martin argument given Markov decompositions (task IGR-2a, part 2)

Miller–Sheffield, *Imaginary geometry I*, arXiv:1201.1496, , Prop. 3.4
(`prop::gff_abs_continuity`, l. 1233–1238) and its proof (l. 1260–1264). The proof writes, on a
neighbourhood `Ũ` (here `V`) of `Ū`, `(hᵢ + Fᵢ)|_Ũ = hᵢ^Ũ + Kᵢ` with `hᵢ^Ũ` a zero-boundary GFF on
`Ũ` and `Kᵢ = (hᵢ^{Ũᶜ} + Fᵢ)|_Ũ` harmonic on `Ũ` and independent of `hᵢ^Ũ` (IG1 Prop. 3.1,
`gff::prop::markov`), puts `g = φ (K₂ − K₁)` with `φ ∈ C_0^∞(Ũ)`, `φ|_U ≡ 1`, so that
`(h₁^Ũ + K₁ + g)|_U = (h₁^Ũ + K₂)|_U`, and concludes by Cameron–Martin for the shift `g`.

* `absCont_resOn_of_markov` : the conclusion of Prop. 3.4 for any two fields given on `V` in the
  Markov form `Zᵢ + Kᵢ` (`Zᵢ` zero-boundary GFF on `V`, `Kᵢ` a.s. a harmonic function on `V`,
  `Zᵢ ⫫ Kᵢ`): `law((Z₁ + K₁)|_B) ≪ law((Z₂ + K₂)|_B)` whenever `B̄ ⊆ V` is compact;
  `mutuallyAbsCont_resOn_of_markov` : both directions.

Departure from the written proof (same mathematics, recorded for DEVIATIONS): IG1 couples `h₁, h₂`
so that `h₁^Ũ = h₂^Ũ` and reweights by the random density `𝒵⁻¹ exp((h₁, g)_∇)`. We instead
disintegrate over the harmonic parts: by independence, `law((Z + K)|_B)(A) = ∫ ν{k : (k + K)|_B ∈ A}`
(`ν` = the law of the zero-boundary GFF on `V`, unique by LQGMetric `IsZeroBoundaryGFF.map_eq`),
and for each pair of fixed harmonic parts the deterministic Cameron–Martin theorem
(`GFFAbsCont.map_add_absCont`) compares the integrands. This avoids the measurability of
`(h₁, g)_∇` that IG1 discusses (l. 1261).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

open LQGMetric QuantumZipper

/-- the restriction `𝒟'(V) → 𝒟'(B)` (composition with `𝓓(B) ⊆ 𝓓(V)`) -/
def resOn (B V : Opens ℂ) (k : DistOn V) : DistOn B := k.comp (GM.testIncl B V)

lemma resOn_apply (B V : Opens ℂ) (k : DistOn V) (φ : TestOn B) :
    resOn B V k φ = k (GM.testIncl B V φ) := rfl

lemma measurable_resOn (B V : Opens ℂ) : Measurable (resOn B V) :=
  measurable_distOn_iff.2 fun φ => measurable_distOn_apply (GM.testIncl B V φ)

/-- `resOn B V ∘ restrictTo V = restrictTo B` -/
lemma resOn_restrictTo {B V : Opens ℂ} (hBV : B ≤ V) (h : Field) :
    resOn B V (restrictTo V h) = restrictTo B h :=
  DFunLike.ext _ _ fun φ => (GM.restrictTo_apply_testIncl hBV h φ).symm

lemma measurable_add_distOn (V : Opens ℂ) :
    Measurable fun q : DistOn V × DistOn V => q.1 + q.2 :=
  measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp measurable_fst).add ((measurable_distOn_apply φ).comp measurable_snd)

lemma continuous_mul_test {V : Opens ℂ} {g : ℂ → ℝ} (hg : ContDiffOn ℝ 0 g (V : Set ℂ))
    (ψ : TestOn V) : Continuous fun x => ψ x * g x :=
  (contDiff_mul_of_tsupport V.isOpen (ψ.contDiff.of_le bot_le) hg ψ.tsupport_subset).continuous_zero

lemma integrable_mul_test {V : Opens ℂ} {g : ℂ → ℝ} (hg : ContDiffOn ℝ 0 g (V : Set ℂ))
    (ψ : TestOn V) : Integrable fun x => g x * ψ x := by
  have h := (continuous_mul_test hg ψ).integrable_of_hasCompactSupport (μ := volume)
    (ψ.hasCompactSupport.mul_right (f' := g))
  simpa only [mul_comm] using h

end MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
