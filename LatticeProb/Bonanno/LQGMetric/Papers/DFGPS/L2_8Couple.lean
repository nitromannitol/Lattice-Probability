/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8Couple at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.ZBBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, first step: the Markov coupling `h ↔ h̊` with DDDF's process (DF-B4)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:877–878: "Let `h̊` be a
zero-boundary GFF on `(-1,2)²`. By the Markov property of the whole-plane GFF, we can couple `h`
and `h̊` in such a way that `h − h̊` is a.s. harmonic, hence continuous, on `(-1,2)²`."

`markov_zb_coupling`: for a whole-plane GFF `h` (any additive constant) and a bounded open `V`
disjoint from some circle `∂B_r(z)`, the recentred field `h − h_r(z)` splits as `𝔥 + h̊` with `𝔥`
harmonic on `V`, independent of `h̊`, and `h̊|_V` extends (same probability space) to the process
`Xh : BddOn V → Ω → ℝ` of `Blueprint.DDDFThm1_2`/`DDDFProp29` (`IsZBGFFProcessExt`), agreeing
with `h̊` on `𝓓(V)`. Sources: `Blueprint.LMLem2_1` via `markov_normAt` (MarkovNorm.lean) and the
extension `zbBdd` (ZBBridge.lean). The recentring by `h_r(z)` changes `h` by a random constant,
which the paper absorbs in "plus a continuous function" (T:897–898).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.DFGPS

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Markov coupling with DDDF's zero-boundary process** (DFGPS T:877–878). -/
theorem markov_zb_coupling (hLM : LMLem2_1) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) (V : Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) (hV : Disjoint (V : Set ℂ) (sphere z r)) :
    ∃ (hh hz : Ω → DistC) (Xh : BddOn (V : Set ℂ) → Ω → ℝ),
      (∀ ω, addConst (h ω) (-circleAvg (h ω) r z) = hh ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧
        ∀ φ : TestOn V, restrictTo V (hh ω) φ = ∫ x, g x * φ x) ∧
      IndepFun hh hz P ∧
      IsZBGFFProcessExt V Xh P ∧
      (∀ φ : TestOn V, Xh φ.toBddOn =ᵐ[P] fun ω => restrictTo V (hz ω) φ) := by
  obtain ⟨hW, hn⟩ := isNormalizedAt_recenter hh hr z
  obtain ⟨hh', hz, hsum, hharm, -, hind, hzb, -, -⟩ :=
    markov_normAt hLM P _ hW hr z hn V hV
  exact ⟨hh', hz, zbBdd hzb (zbAdmissible_of_isBounded hVb), hsum, hharm, hind,
    isZBGFFProcessExt_zbBdd hzb hVb, fun φ => zbBdd_toBddOn_ae hzb _ φ⟩

end LQGMetric.DFGPS
