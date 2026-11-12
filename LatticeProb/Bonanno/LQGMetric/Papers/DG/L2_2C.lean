/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L2_2C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2B
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAsm

/-!
# Ding–Gwynne Lemma 2.2 with the Markov decomposition (task P2-DG3E)

DG (`metric-comparison-final.tex`, Lemma 2.2 `lem-whole-plane-compare`, DG:618–640, first
assertion (2.4)): "Write `h = h^U + 𝔥` where `h^U` is a zero-boundary GFF on `U` and `𝔥` is an
independent random harmonic function on `U`. There are constants `a₀, a₁ > 0` … such that for each
`A > 1`, `P[max_{z∈V̄} |𝔥(z)| ≤ A] ≥ 1 − a₀e^{−a₁A²}`."

**`dg_lemma22`**: the Markov decomposition of LM Lemma 2.1 (`MarkovAsm.lmLem2_1AE_bdd`, the
project's whole-plane Markov property; it needs `U` bounded and `U ∩ ∂𝔻 = ∅`) together with
the tail `L22.dg_lemma22_tail` for every compact `K ⊆ U` (DG: `K = V̄`). The bad event is
stated for every harmonic representative of `𝔥|_U` (all agree on `U`). The LGD/LFPP consequences
(2.5)–(2.6) are DG Lemma 3.2-type statements (`dg_lemma32_of_tail`) and are not restated here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric
namespace DG
namespace L22

open Blueprint MarkovAsm MarkovZBIndep

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **DG Lemma 2.2, (2.4)** (for `U` bounded, `U ∩ ∂𝔻 = ∅`, any compact `K ⊆ U`): the Markov
decomposition `h = 𝔥 + h^U` with `𝔥` a.s. harmonic on `U`, `𝔥 ⫫ h^U`, `h^U|_U` a zero-boundary
GFF on `U`, and `P[∃ z ∈ K, |𝔥(z)| > A] ≤ a₀ e^{−a₁A²}` for all `A ≥ 0`. -/
theorem dg_lemma22 {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) (hUb : Bornology.IsBounded (U : Set ℂ))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ hh' hz : Ω → DistC, (∀ ω, h ω = hh' ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
        ∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x) ∧
      IndepFun hh' hz P ∧ IsZeroBoundaryGFF U (fun ω => restrictTo U (hz ω)) P ∧
      ∃ a₀ a₁ : ℝ, 0 < a₁ ∧ ∀ A : ℝ, 0 ≤ A →
        P {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
          (∀ φ : TestOn U, restrictTo U (hh' ω) φ = ∫ x, g x * φ x) ∧ ∃ z ∈ K, A < |g z|} ≤
          ENNReal.ofReal (a₀ * Real.exp (-a₁ * A ^ 2)) := by
  obtain ⟨hh', hz, hdec, hharm, ⟨G, hGm, hGe⟩, hind, hzb, -, -⟩ :=
    lmLem2_1AE_bdd P h hh U hU hUb
  have hG : Measurable G := hGm.mono (fieldSigmaClosed_le hh.1 _) le_rfl
  have hdecG : ∀ᵐ ω ∂P, h ω = G ω + hz ω := by
    filter_upwards [hGe] with ω hω; rw [hdec ω, hω]
  have hindG : IndepFun G hz P := hind.congr hGe (ae_eq_refl _)
  obtain ⟨a₀, a₁, ha₁, hT⟩ := dg_lemma22_tail hh hG hdecG hindG hzb hK hKU
  refine ⟨hh', hz, hdec, hharm, hind, hzb, a₀, a₁, ha₁, fun A hA => ?_⟩
  refine le_trans (measure_mono_ae ?_) (hT A hA)
  filter_upwards [hGe] with ω hω
  intro hx
  obtain ⟨g, hg, hrep, hz'⟩ := hx
  exact ⟨g, hg, fun φ => by rw [← hω]; exact hrep φ, hz'⟩

end L22
end DG
end LQGMetric
