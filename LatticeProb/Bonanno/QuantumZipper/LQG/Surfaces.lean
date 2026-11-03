/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.LQG.Surfaces at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures

/-!
# Quantum surfaces and convergence in law

`FOUNDATIONS.md` §5. `scaleParam`/`canonical` implement the rescaling (1.8) that normalizes a
field sample to have unit quantum area in `B₁(0)`. `AreaConvergesInLaw` is Proposition 1.6's
convergence in law of the (doubly-marked) canonical area measures, phrased through
finite-dimensional distributions against continuous compactly supported test functions
(Kallenberg's criterion for weak convergence of random measures on bounded subsets of `ℍ`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace QuantumZipper

/-- The scale `a` making `B_a(0) ∩ ℍ` have unit `γ`-quantum area: the infimum of the radii `a`
at which the quantum area measure of `x` first reaches mass `1`. -/
def scaleParam (γ : ℝ) (x : FieldSample) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ x (Metric.ball 0 a ∩ H)}

/-- The canonical description of `x` (Sheffield (1.8)): rescale by `scaleParam γ x` so that
`B₁(0)` carries unit `γ`-quantum area. -/
def canonical (γ : ℝ) (x : FieldSample) : FieldSample := rescale x (Qc γ) (scaleParam γ x)

/-- `canonical` unfolds to the coordinate change by the scaling map `z ↦ (scaleParam γ x) z`. -/
theorem canonical_eq_coordChange (γ : ℝ) (x : FieldSample) :
    canonical γ x = coordChange x (fun z => (scaleParam γ x : ℂ) * z) (Qc γ) := rfl

/-- Convergence in law of doubly-marked quantum surfaces (Proposition 1.6): the canonical area
measures `qAreaMeasure γ (Y c ω)` converge to `qAreaMeasure γ (Y' ω)` in the sense of weak
convergence of random measures on bounded subsets of `ℍ`, expressed through finite-dimensional
distributions (Kallenberg): for every finite family of continuous, compactly supported test
functions `f j : ℂ → ℝ`, the joint law of `(∫ f j d(qAreaMeasure γ (Y c ω)))_j` under `P`
converges, as `c → ∞`, to the corresponding joint law under `P'` for `Y'`, tested against every
bounded continuous functional `F`. -/
def AreaConvergesInLaw (γ : ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Y : ℝ → Ω → FieldSample) (P' : Measure Ω') (Y' : Ω' → FieldSample) : Prop :=
  ∀ (m : ℕ) (f : Fin m → ℂ → ℝ), (∀ j, Continuous (f j)) → (∀ j, HasCompactSupport (f j)) →
    ∀ F : (Fin m → ℝ) → ℝ, Continuous F → (∃ C, ∀ v, |F v| ≤ C) →
      Tendsto (fun c : ℝ => ∫ ω, F (fun j => ∫ z, f j z ∂(qAreaMeasure γ (Y c ω))) ∂P) atTop
        (𝓝 (∫ ω, F (fun j => ∫ z, f j z ∂(qAreaMeasure γ (Y' ω))) ∂P'))

end QuantumZipper
