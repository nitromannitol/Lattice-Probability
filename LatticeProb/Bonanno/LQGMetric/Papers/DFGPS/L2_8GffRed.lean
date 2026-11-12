/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffRed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8LimF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8 reduced to the whole-plane GFF case

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:897–898): "the case of a whole-plane
GFF implies the case of a whole-plane GFF plus a continuous function." `Lem2_8Gff` is the
whole-plane GFF case of Lemma 2.8, with "induce the Euclidean topology" in its equivalent form
"positive off the diagonal" (a continuous metric on the compact square, `L2_8.lean` docstring);
the length-metric property of the limits is proved for all `h` in `L2_8Lim.lean`.

`lem2_8_of_gff : Lem2_8Gff → Lem2_8` (continuity: `lem2_8_continuous`; tightness:
`lem2_8_tight_of_gff`; limits: `lem2_8_lim_of_gff`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.DFGPS

open Blueprint

/-- **DFGPS Lemma 2.8, whole-plane GFF case** (T:876–896): tightness of the laws of
`𝔞_ε⁻¹ D_g^ε(·,·;S)` and positivity off the diagonal of every subsequential limit. -/
def Lem2_8Gff : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (a : ℂ) (s : ℝ), 0 < s →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → DistC),
      IsWholePlaneGFF g P →
      IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
        μ = P.map fun ω => lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)} ∧
      ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
        (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ)),
        (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
          (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (g ω) (closedSq a s)) →
        Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), IsPosOffDiag d

/-- **DFGPS Lemma 2.8 from its whole-plane GFF case** (T:897–898). -/
theorem lem2_8_of_gff (hG : Lem2_8Gff) : Lem2_8 := by
  intro γ hγ hγ2 a s hs Ω _ P _ h hh
  exact ⟨lem2_8_continuous hs hh,
    lem2_8_tight_of_gff hs hh fun g hg => (hG γ hγ hγ2 a s hs P g hg).1,
    lem2_8_lim_of_gff hs hh (fun g hg => (hG γ hγ hγ2 a s hs P g hg).1)
      fun g hg => (hG γ hγ hγ2 a s hs P g hg).2⟩

end LQGMetric.DFGPS
