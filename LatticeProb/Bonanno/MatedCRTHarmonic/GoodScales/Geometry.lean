/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GoodScales.Geometry at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Walk
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Annulus
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent

/-!
# Plane geometry of good scales (the good-scales estimate, the geometric argument)

* the crossing lemma A1: along an admissible vertex path, the plane sets `J (X m)` form a chain of
  connected sets with consecutive members intersecting; if the chain starts with a point at distance
  `≥ ρ` from `z` and ends with a point at distance `≤ ρ`, some member meets the circle `∂B_ρ(z)`
  (`exists_mem_sphere_of_cross`);
* elementary consequences of the good-scale conditions for the radii and the plane sets near `z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GoodScales

variable {V E : Type*} {G : LFMultigraph V E} {J : V → Set ℂ}

/-! ### The crossing lemma -/

/-- A preconnected set with a point at distance `≥ ρ` and a point at distance `≤ ρ` from `z` meets
the circle `∂B_ρ(z)` (intermediate value theorem for `w ↦ |w - z|`). -/
theorem inter_sphere_nonempty_of_isPreconnected {s : Set ℂ} (hs : IsPreconnected s) {z : ℂ}
    {ρ : ℝ} {w₁ w₂ : ℂ} (hw₁ : w₁ ∈ s) (hw₂ : w₂ ∈ s) (h₁ : ρ ≤ dist w₁ z)
    (h₂ : dist w₂ z ≤ ρ) : (s ∩ sphere z ρ).Nonempty := by
  have hf : ContinuousOn (fun w => dist w z) s :=
    (continuous_id.dist continuous_const).continuousOn
  obtain ⟨w, hw, hwρ⟩ := hs.intermediate_value hw₂ hw₁ hf ⟨h₂, h₁⟩
  exact ⟨w, hw, mem_sphere.mpr hwρ⟩

/-- The plane sets of the two ends of an admissible step intersect. -/
theorem inter_nonempty_of_stepOK (hJ : G.IsPlaneData J) {x y : V} (h : StepOK G x y) :
    (J x ∩ J y).Nonempty := by
  rcases h with rfl | h
  · rw [Set.inter_self]
    exact (hJ.isConnected _).nonempty
  · exact hJ.inter_of_adj x y h

/-- **Crossing lemma (the good-scale argument §5(a) A1).** Along an admissible vertex path `X`, if `J (X a)` has a point
at distance `≥ ρ` from `z` and `J (X (a + k))` a point at distance `≤ ρ`, then some `J (X m)` with
`a ≤ m ≤ a + k` meets the circle `∂B_ρ(z)`. -/
theorem exists_mem_sphere_of_cross (hJ : G.IsPlaneData J) {X : ℕ → V}
    (hX : ∀ n, StepOK G (X n) (X (n + 1))) {z : ℂ} {ρ : ℝ} :
    ∀ (k a : ℕ), (∃ w ∈ J (X a), ρ ≤ dist w z) → (∃ w ∈ J (X (a + k)), dist w z ≤ ρ) →
      ∃ m, a ≤ m ∧ m ≤ a + k ∧ (J (X m) ∩ sphere z ρ).Nonempty := by
  intro k
  induction k with
  | zero =>
    rintro a ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
    exact ⟨a, le_rfl, le_rfl,
      inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hw₁ hw₂ h₁ h₂⟩
  | succ k ih =>
    rintro a ⟨w₁, hw₁, h₁⟩ hend
    by_cases hnear : ∃ w ∈ J (X a), dist w z ≤ ρ
    · obtain ⟨w₂, hw₂, h₂⟩ := hnear
      exact ⟨a, le_rfl, by omega,
        inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hw₁ hw₂ h₁ h₂⟩
    · push Not at hnear
      obtain ⟨w, hwa, hwb⟩ := inter_nonempty_of_stepOK hJ (hX a)
      have hfar : ∃ w ∈ J (X (a + 1)), ρ ≤ dist w z := ⟨w, hwb, (hnear w hwa).le⟩
      have hend' : ∃ w ∈ J (X (a + 1 + k)), dist w z ≤ ρ := by
        rw [show a + 1 + k = a + (k + 1) by omega]
        exact hend
      obtain ⟨m, hm1, hm2, hm⟩ := ih (a + 1) hfar hend'
      exact ⟨m, by omega, by omega, hm⟩

/-! ### Consequences of the good-scale conditions -/

variable {A : Finset V} {v : V} {K : ℕ} {p : ℝ} {z : ℂ} {r : ℕ → ℝ}

namespace IsGoodScalesFacts

end IsGoodScalesFacts

end MatedCRTHarmonic.GoodScales
