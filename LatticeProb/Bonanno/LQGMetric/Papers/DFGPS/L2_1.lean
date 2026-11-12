/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Cont
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Bdd
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Ratio

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1 (`lem-localized-approx`, T:688–699), assembled

For `h` a whole-plane GFF plus a bounded continuous function and `U` bounded, a.s.:
(1) `(ε, z) ↦ ĥ*_ε(z)` is continuous (`lem2_1_cont`, for every `h`);
(2) (eqn-localized-approx) `sup_{z ∈ Ū} |h*_ε(z) − ĥ*_ε(z)| → 0` (`lem2_1_approx_of_gff`, from the
GFF case `Lem2_1GffApprox`, which is still open — see `handoff/P2-DFB2b.md`);
(3) (eqn-localized-lfpp-approx) `D̂^ε_h(·,·;U)/D^ε_h(·,·;U) → 1` uniformly, in the two-sided form
of `lem2_1_ratio` (DEV-DFGPS-3).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS

open LFPP

/-- **DFGPS Lemma 2.1**, modulo the GFF case `Lem2_1GffApprox` (open node). -/
theorem lem2_1.{u} (HG : Lem2_1GffApprox.{u}) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) {U : Set ℂ} (hU : Bornology.IsBounded U)
    (ξ : ℝ) :
    ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × ℂ => if hp : 0 < p.1 then locMollify p.1 hp (h ω) p.2 else 0)
        (Ioi 0 ×ˢ univ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
        |heatMollify ε (h ω) z - locMollify ε hε (h ω) z| ≤ δ) ∧
      ∀ c : ℝ, 1 < c → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z w : ℂ,
        lfppLocOn ξ ε hε (h ω) U z w ≤ ENNReal.ofReal c * lfppDOn ξ (heatMollify ε (h ω)) U z w ∧
        lfppDOn ξ (heatMollify ε (h ω)) U z w ≤ ENNReal.ofReal c * lfppLocOn ξ ε hε (h ω) U z w := by
  filter_upwards [lem2_1_approx_of_gff HG hh hU] with ω hω
  refine ⟨lem2_1_cont (h ω), hω, fun c hc => lem2_1_ratio ξ (h ω) U ?_ hc⟩
  intro δ hδ
  filter_upwards [hω δ hδ] with ε hε hε' z hz
  exact hε hε' z (subset_closure hz)

end LQGMetric.DFGPS
