/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MesoscopicControlWith at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsConnectedSet
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.PlaneDiam
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding

/-!
# Frozen definition: `CellularEmbedding.MesoscopicControlWith`

Constants `p, σ, ν` exposed; item 2 holds for every `R ≥ R₀`, and item 3 uses nets of `B_{2R}(0)` and
`[m(R), R/100]` inside the probability-`p` event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace CellularEmbedding

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- **Mesoscopic control** with constants `p, σ, ν`: `p ∈ (0,1)`, `σ, ν > 0`,
and there are `R₀`, `m, e, d > 0` on `[R₀, ∞)` with (1) `m(R) ≤ R^{1-σ}`, `(e+d)/m → 0`; (2) for `R ≥ R₀`, cells
meeting `B_{4R}(0)` have diameter `≤ d(R)`; (3) for `R ≥ R₀` there are finite `e(R)`-nets `Z_R ⊂ B_{2R}(0)` of
`B_{2R}(0)` and `Q_R ⊂ [m(R), R/100]` of `[m(R), R/100]` such that the annular event at every `(z, r) ∈ Z_R × Q_R`
has probability `≥ p` from every `x ∈ 𝒱_ℋ(∂B_r(z))`; (4) `D_ℋ(A) ≥ c_vol |A|^ν` for every sufficiently large finite
connected `A ∋ o`. -/
def MesoscopicControlWith (p σ ν : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧ 0 < σ ∧ 0 < ν ∧
  ∃ (R₀ : ℝ) (m e d : ℝ → ℝ),
    (∀ R, R₀ ≤ R → 0 < m R ∧ 0 < e R ∧ 0 < d R) ∧
    (∀ R, R₀ ≤ R → m R ≤ R ^ (1 - σ)) ∧
    Tendsto (fun R => (e R + d R) / m R) atTop (𝓝 0) ∧
    (∀ R, R₀ ≤ R → ∀ x, (H.cell x ∩ ball 0 (4 * R)).Nonempty → diam (H.cell x) ≤ d R) ∧
    (∀ R, R₀ ≤ R → ∃ (Z : Finset ℂ) (Q : Finset ℝ),
      (∀ z ∈ Z, z ∈ ball (0 : ℂ) (2 * R)) ∧ (∀ w ∈ ball (0 : ℂ) (2 * R), ∃ z ∈ Z, dist w z ≤ e R) ∧
      (∀ r ∈ Q, r ∈ Set.Icc (m R) (R / 100)) ∧
      (∀ s ∈ Set.Icc (m R) (R / 100), ∃ r ∈ Q, dist s r ≤ e R) ∧
      ∀ z ∈ Z, ∀ r ∈ Q, ∀ x ∈ verticesMeeting H.cell (sphere z r),
        ENNReal.ofReal p ≤ G.walkLaw x {ω | G.AnnularEvent H.cell z r (G.vertexPath ω)}) ∧
    ∃ cvol : ℝ, 0 < cvol ∧ ∃ N : ℕ, ∀ A : Finset V, o ∈ A → G.IsConnectedSet A → N ≤ A.card →
      cvol * (A.card : ℝ) ^ ν ≤ planeDiam H.cell A

end CellularEmbedding

end MatedCRTHarmonic
