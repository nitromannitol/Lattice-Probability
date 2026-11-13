/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.WalkLindeberg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.WalkLindebergRows
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayWalk
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoercivitySmallJumps

/-!
# Conditional Lindeberg at the actual walk (manuscript `p:lem:lindeberg`, tex:1599)

`Limit/WalkLindebergRows` reduces the two walk-level Lindeberg atoms — **(i)** small increments
in probability and **(iii)** uniform square tails of the terminal increment — for EVERY rescaled
stopped row of the harmonic-coordinate path `M`, to three properties of `M` itself:

* càdlàg paths;
* `SmallJumpsFromBoundedRegion` — every possible jump from `B̄(0, R/ε)` is `o(1/ε)`
  (`p:eq:allpossiblejumps`);
* `RescaledCompactContainment` — the first half of `p:lem:lindeberg`.

This module proves all three at the actual walk:

* `smallJumpsFromBoundedRegion_of_ordinaryJumps` — deterministic: `HasOnlyOrdinaryJumps` makes
  every jump of `M` a neighbour increment `Φ(w) - Φ(v)` issued from the pre-jump vertex, the
  pre-jump value `Φ(v)` lies in `B̄(0, R/ε)`, coercivity
  (`CoercivitySmallJumps.exists_coercivity_constant`) puts `z_v` in `B̄(0, (2R+1)/ε)`, and
  `CoercivitySmallJumps.exists_pos_forall_neighbor_smallJump` bounds every neighbour increment
  from there.  Only the geometric side conditions `hz`, `hsub`, `hdiam` enter.
* `walkLindebergInputs` — at `areaSampleLaw`: càdlàg from `IsSpatialExtension`, jumps from
  `HasOnlyOrdinaryJumps` (both inside `PathwiseClockClauses`), containment from the checked
  `harray` producer `ActualThresholdArray.harray_of_canonicalBracket` through
  `WalkLindeberg.rescaledCompactContainment_of_arrays`.
  `walkLindebergInputs_completion` — the same on the completed sample space, where the CLT
  lane's arrays live.
* `lindeberg_of_rescaledStopRows_walk` — **the Lindeberg field of `LocalizedBracketArray` at the
  walk, for arbitrary rescaled stopped rows**, in particular for the doubly-stopped rows of the
  local CLT lane (`lindeberg_twice_walk`).
* `stoppedRescaledSmallIncrements_walk`, `stoppedRescaledTerminalSquareTail_walk` — the two named
  atoms of `Limit/StoppedRescaledLindeberg` at the walk's bracket-stopped rescaled projection,
  under that consumer's own structural hypotheses; `rescaledIncrementCharFunLimit_walk_of_bracket_data`
  — that consumer at the walk with both atoms gone.

## Cost (the honest list)

Every hypothesis below is either held by every walk consumer or owned by a live lane:
`hclock : PathwiseClockClauses …` (held by every consumer), `hbr : CanonicalBracket …` (bracket
lane), `hLLN` (diagonal bracket LLN, regeneration lane), and the geometric side conditions
`hz : IsCellRepresentative z`, `hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e)`,
`hdiam : SubmacroscopicDiameters (decode e)` — free a.e. from `hmt`/`hFE`/`hΦ`
(`InvarianceAssembly.ae_submacroscopicDiameters`,
`HarmonicCoordinateAssembly.uniformlySublinearError_of_representatives`).  The row hypotheses of
`lindeberg_of_rescaledStopRows_walk` (martingale, compensator in `[0, K]`, right continuity) are
the other fields of the array the local lane is building, not new inputs.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.WalkLindeberg

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement MartingaleIngredients
open ReflectedWalk QuenchedFormulation ProcessFiltration
open ReflectedGMS.InvarianceAssembly ReflectedGMS.DirectionalNondegeneracy
open ReflectedGMS.MartingaleLimit ReflectedGMS.ApproximateBracketCLT
open ReflectedGMS.RescaledFddCharFun ReflectedGMS.GaussianLimitIdentification

/-! ## Small jumps from bounded regions, deterministically -/

/-- **`p:eq:allpossiblejumps` along the paths, from ordinary jumps.**  If almost every path of
`M` jumps only across ordinary edges, from the value `Φ v` of the vertex held just before to the
value `Φ w` of its neighbour, then `M` has small jumps from bounded regions.  Deterministic in the
environment: coercivity and the small-neighbour-jump lemma give one scale threshold `ε₀` for
every path. -/
theorem smallJumpsFromBoundedRegion_of_ordinaryJumps {V : Type*} [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (Φ z : V → Plane) (hz : CellRepresentatives F z)
    (hsub : UniformlySublinearError F Φ z) (hdiam : SubmacroscopicDiameters F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → State F}
    {M : ℝ≥0 → Ω → Plane}
    (hjumps : ∀ᵐ ω ∂P, HasOnlyOrdinaryJumps F Φ (fun t => X t ω) (fun t => M t ω)) :
    SmallJumpsFromBoundedRegion P M := by
  intro R hR δ hδ
  obtain ⟨K₀, hK₀, hcoer⟩ := CoercivitySmallJumps.exists_coercivity_constant F Φ z hz hsub
  obtain ⟨ε₁, hε₁, hsmall⟩ := CoercivitySmallJumps.exists_pos_forall_neighbor_smallJump F hF
    Φ z hz hsub hdiam (R := 2 * R + 1) (by linarith) hδ
  have hK1 : (0 : ℝ) < K₀ + 1 := by linarith
  refine ⟨min ε₁ (1 / (K₀ + 1)), lt_min hε₁ (by positivity), ?_⟩
  filter_upwards [hjumps] with ω hω e he he0 u hu
  by_cases hne : Function.leftLim (fun r => M r ω) u = M u ω
  · rw [hne, sub_self, norm_zero, mul_zero]
    exact hδ.le
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hupos
  · exfalso
    apply hne
    rw [← hu0]
    exact leftLim_zero _
  obtain ⟨s, v, w, hhold, hl, hr⟩ := hω u hupos hne
  have hl' : Function.leftLim (fun r => M r ω) u = Φ v := hl
  have hr' : M u ω = Φ w := hr
  have hadj : 0 < F.graph.c v w := F.graph.toSimpleGraph_adj.mp hhold.2.2.2.1
  have hΦv : e * ‖Φ v‖ ≤ R := by
    rw [← hl']
    exact hu
  have heε₁ : e ≤ ε₁ := he0.trans (min_le_left _ _)
  have heK : e * (K₀ + 1) ≤ 1 := (le_div_iff₀ hK1).1 (he0.trans (min_le_right _ _))
  have hzv : ‖z v‖ ≤ (2 * R + 1) / e := by
    rw [le_div_iff₀ he]
    have h1 := mul_le_mul_of_nonneg_left (hcoer v) he.le
    nlinarith
  have hfin := hsmall e he heε₁ v w hadj hzv
  rw [hr', hl']
  exact hfin

/-! ## The three properties of `M` at the walk -/

/-- **The three inputs of `Limit/WalkLindebergRows` at the actual walk**, on `areaSampleLaw`:
càdlàg paths, small jumps from bounded regions and compact containment of the harmonic-coordinate
spatial extension `M`. -/
theorem walkLindebergInputs (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (C : Fin 2 → ℝ)
    (hLLN : ∀ k : Fin 2, RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
      (ordinaryEdgeBracket (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) k k) (C k))
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e)) :
    (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), IsCadlag fun r => M r ω) ∧
      SmallJumpsFromBoundedRegion (areaSampleLaw (decode e) D hG start) M ∧
      RescaledCompactContainment (areaSampleLaw (decode e) D hG start) M := by
  have : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start) :=
    BracketClausesScalarReduction.isProbabilityMeasure_areaSampleLaw e D hG start
  refine ⟨hclock.mono fun ω h => h.2.2.2.2.2.2.2.2.2.1.1, ?_, ?_⟩
  · exact smallJumpsFromBoundedRegion_of_ordinaryJumps (decode e) (decode_geometry e)
      (Φ.at e) (z.at e) (fun v => hz e v) hsub hdiam
      (hclock.mono fun ω h => h.2.2.2.2.2.2.2.2.2.2.2.2)
  · exact rescaledCompactContainment_of_arrays
      (ActualThresholdArray.harray_of_canonicalBracket e D hG Φ start Xexp Xexact M hclock hbr
        C hLLN)

/-- **The same three inputs on the completed sample space**, where the CLT lane's arrays live
(the `null` field of the arrays forces the completion).  The completed law agrees with the
original law on every set, so each clause transfers definitionally. -/
theorem walkLindebergInputs_completion (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (C : Fin 2 → ℝ)
    (hLLN : ∀ k : Fin 2, RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
      (ordinaryEdgeBracket (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) k k) (C k))
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e)) :
    (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion, IsCadlag fun r => M r ω) ∧
      SmallJumpsFromBoundedRegion
        (Ω := NullMeasurableSpace (Existence.Sample (Vertex e.val))
          (areaSampleLaw (decode e) D hG start))
        (areaSampleLaw (decode e) D hG start).completion M ∧
      RescaledCompactContainment
        (Ω := NullMeasurableSpace (Existence.Sample (Vertex e.val))
          (areaSampleLaw (decode e) D hG start))
        (areaSampleLaw (decode e) D hG start).completion M := by
  obtain ⟨hc, hj, hk⟩ :=
    walkLindebergInputs e D hG z Φ start Xexp Xexact M hclock hbr C hLLN hz hsub hdiam
  exact ⟨hc, fun R hR δ hδ => hj R hR δ hδ, fun ε hε H γ hγ => hk ε hε H γ hγ⟩

/-! ## The Lindeberg field at the walk -/

/-! ## The atoms of `StoppedRescaledLindeberg` at the walk -/

end ReflectedGMS.WalkLindeberg
