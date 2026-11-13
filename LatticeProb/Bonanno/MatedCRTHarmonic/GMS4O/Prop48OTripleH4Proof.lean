/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OTripleH4Proof at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OSecondMomentTriple
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OCanonicalFar

/-!
# Proof of the -corrected H4

`p48o_goodEventSecondMomentTriple_holds` proves `Prop48GoodEventSecondMomentInputTriple D hγ q ζ H1`
for every Lemma 4.9 family `H1` and every family of thickened GMC readers `H2`:

* far pairs: `p48o_canonical_far_pair` ([18] (4.35)–(4.37), triple conditional mean);
* near pairs, Fubini and the rate: `p48o_secondMoment_triple_of_farPair` ([18] (4.30)–(4.34), (4.38));
* the good-event indicator: the unconditional bound restricts to any event `E`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4O

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4.Canonical

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **[18] (4.38) with the triple conditional mean, on the good event** — the corrected H4 of
The canonical Proposition 4.8, for arbitrary Lemma 4.9 moments `H1` and GMC readers `H2`. -/
theorem p48o_goodEventSecondMomentTriple_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ζ : ℝ} (hq : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100))
    (H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → Lemma49ConditionalMoments D hγ q ζ ρ)
    (H2 : ThickGMCReaders D) :
    Prop48GoodEventSecondMomentInputTriple D hγ q ζ H1 := by
  intro ρ hρ A hA hmean
  have hζq : 4 * ζ < q := by
    have h1 := hζ.2
    have h2 := hq.1
    linarith
  obtain ⟨Cf, hCf, ε₀, hε₀, hfar⟩ := p48o_canonical_far_pair D hγ H2 hζ.1 hζq H1 ρ hρ
  obtain ⟨C, hC, hbound⟩ := p48o_secondMoment_triple_of_farPair D hγ hζ.1.le hρ (H1 ρ hρ) hA.le
    hmean hCf hfar
  refine ⟨C, hC, ε₀, hε₀, fun ε hε E _hE _hEloc domain f hadm => ?_⟩
  exact (setLIntegral_le_lintegral _ _).trans (hbound ε hε domain f hadm)

end MatedCRTHarmonic.GMS4O
