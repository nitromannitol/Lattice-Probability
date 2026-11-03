/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.HarmonicInfinity.Mesoscopic at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Walk
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Bound
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Times
import LatticeProb.Bonanno.MatedCRTHarmonic.CellularFacts.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MesoscopicControlWith
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsConnectedSet

/-!
# The crossing lemma along graph walks

* `exists_mem_support_sphere`: the crossing lemma along a graph walk (plane data).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace MatedCRTHarmonic.HarmonicInfinity

open Markov Harmonic

variable {V E : Type*} {G : LFMultigraph V E}

/-! ### The crossing lemma along graph walks -/

/-- **Crossing lemma along a walk.** For plane data `J`, a graph walk from `u` to `v`, where `J u`
has a point at distance `≥ ρ` from `z` and `J v` a point at distance `≤ ρ`, visits a vertex whose
plane set meets the circle `∂B_ρ(z)`. -/
theorem exists_mem_support_sphere {J : V → Set ℂ} (hJ : G.IsPlaneData J) {z : ℂ} {ρ : ℝ} {u v : V}
    (w : G.adj.Walk u v) (hu : ∃ q ∈ J u, ρ ≤ dist q z) (hv : ∃ q ∈ J v, dist q z ≤ ρ) :
    ∃ t ∈ w.support, t ∈ verticesMeeting J (sphere z ρ) := by
  induction w with
  | nil =>
    obtain ⟨q₁, hq₁, h₁⟩ := hu
    obtain ⟨q₂, hq₂, h₂⟩ := hv
    exact ⟨_, SimpleGraph.Walk.start_mem_support _,
      GoodScales.inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hq₁ hq₂
        h₁ h₂⟩
  | @cons a b c h q ih =>
    obtain ⟨q₁, hq₁, h₁⟩ := hu
    by_cases hnear : ∃ q ∈ J a, dist q z ≤ ρ
    · obtain ⟨q₂, hq₂, h₂⟩ := hnear
      exact ⟨a, SimpleGraph.Walk.start_mem_support _,
        GoodScales.inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hq₁
          hq₂ h₁ h₂⟩
    · push Not at hnear
      obtain ⟨q', hqa, hqb⟩ := hJ.inter_of_adj a b h
      obtain ⟨t, ht, hts⟩ := ih ⟨q', hqb, (hnear q' hqa).le⟩ hv
      refine ⟨t, ?_, hts⟩
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ ht

end MatedCRTHarmonic.HarmonicInfinity
