/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.InterpolatedConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.WeakConvergenceTransfer
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainStatement

/-!
# Weak convergence of the interpolation through an arbitrary point of each cell

The conclusion of `GMS.Theorem1_16` is `ConvergesWeaklyInC` for the rescaled **linear interpolation
of the walk through an arbitrary point `p(K) ∈ K` of each cell**, over each holding interval from
the current cell's point to the next cell's point.  The corpus (`FixedStartConclusions`) proves weak
convergence in `C(ℝ≥0, Plane)` of the rescaled continuous interpolation `Iexact` of the
exact-holding-time path through a *measurable representative field* — for **every** measurable
representative field `z` (`IsCellRepresentative z`).

At one fixed environment `e₀` no closeness estimate is needed: any point choice `p` at `e₀` is the
restriction of a measurable representative field, namely `z` modified on the single environment
`e₀` (`replaceAt`; singletons of the trace σ-algebra on `Env` are measurable).  Applying the corpus
conclusion to that field gives the interpolation through `p` itself (`exists_interpolation_through_points`).

`convergesWeaklyInC_interpolated` packages this for the walk-identification step: any path `Y`
which, almost surely, follows `lineMap (p v) (p w)` over every complete holding interval `[s, t]` of
the canonical exact-holding-time path `exactAreaPath` (read with its `Option`-valued states,
`IsOptionHoldingInterval`), when that path takes only vertex states, has rescalings
`t ↦ ε • Y(t / ε²)` (`scaledBrownianPath ε⁻¹`, see
`WeakConvergenceTransfer.scaledBrownianPath_inv_apply_div`) converging weakly in `C` to the target.
The interpolation formula is exactly the corpus's `IsContinuousInterpolation` formula: on the
holding interval `[s, t)` at `v`, followed by the jump to `w` at `t`, the path moves from `p v` at
time `s` to `p w` at time `t`.

Two structural facts about the exact path, useful for identifying it with GMS's jump-chain walk,
are exported in the same `Option` form: every vertex time lies in a complete holding interval
(`ae_hasCompleteOptionHoldingIntervals`), and every complete holding interval at `v` has length
`Area(v)/π(v)` (`ae_optionHoldingInterval_length`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.GMS.InterpolatedConvergence

open Code EnvironmentFields StatementIngredients AreaClocks SpatialEnds InvarianceMainStatement
open ReflectedWalk WeakConvergenceTransfer

/-! ## A point choice at one environment is the restriction of a measurable field -/

/-- A point choice at the environment `e₀`, extended by zero to all labels. -/
noncomputable def extendPoints (e₀ : Env) (p : Vertex e₀.val → Plane) (n : ℕ) : Plane :=
  if h : (e₀.val.1 n).isSome then p ⟨n, h⟩ else 0

open Classical in
/-- The field `z` with its values at the single environment `e₀` replaced by the point choice
`p`. -/
noncomputable def replaceAt (z : CellField) (e₀ : Env) (p : Vertex e₀.val → Plane) :
    CellField where
  value e := if e = e₀ then extendPoints e₀ p else z.value e
  measurable_value :=
    Measurable.ite (measurableSet_singleton e₀) measurable_const z.measurable_value
  absent_zero e n hn := by
    show (if e = e₀ then extendPoints e₀ p else z.value e) n = 0
    split_ifs with he
    · subst he
      simp [extendPoints, hn]
    · exact z.absent_zero e n hn

open Classical in
theorem replaceAt_value_self (z : CellField) (e₀ : Env) (p : Vertex e₀.val → Plane) :
    (replaceAt z e₀ p).value e₀ = extendPoints e₀ p :=
  if_pos rfl

open Classical in
theorem replaceAt_value_of_ne (z : CellField) {e₀ e : Env} (p : Vertex e₀.val → Plane)
    (he : e ≠ e₀) : (replaceAt z e₀ p).value e = z.value e :=
  if_neg he

/-- At `e₀` the modified field is the point choice. -/
theorem replaceAt_at (z : CellField) (e₀ : Env) (p : Vertex e₀.val → Plane) :
    (replaceAt z e₀ p).at e₀ = p := by
  funext v
  show (replaceAt z e₀ p).value e₀ v.val = p v
  rw [replaceAt_value_self]
  unfold extendPoints
  rw [dif_pos v.property]

/-- The modified field is again a measurable cell representative. -/
theorem isCellRepresentative_replaceAt (z : CellField) (hz : IsCellRepresentative z) (e₀ : Env)
    (p : Vertex e₀.val → Plane) (hp : ∀ v, p v ∈ ((decode e₀).cell v : Set Plane)) :
    IsCellRepresentative (replaceAt z e₀ p) := by
  intro e v
  by_cases he : e = e₀
  · subst he
    rw [replaceAt_at]
    exact hp v
  · show (replaceAt z e₀ p).value e v.val ∈ ((decode e).cell v : Set Plane)
    rw [replaceAt_value_of_ne z p he]
    exact hz e v

/-! ## Holding intervals read through the collapsed path -/

/-- A complete maximal holding interval `[s, t)` at `v` of an `Option`-valued path, followed by the
ordinary edge jump to `w` at `t`: `IsHoldingInterval` read through `collapse`. -/
def IsOptionHoldingInterval {V : Type*} (F : IndexedCells V) (Y : ℝ≥0 → Option V)
    (v w : V) (s t : ℝ≥0) : Prop :=
  s < t ∧ (∀ r ∈ Ico s t, Y r = some v) ∧ Y t = some w ∧ F.graph.toSimpleGraph.Adj v w ∧
    (s = 0 ∨ ∀ r < s, ∃ q ∈ Ioo r s, Y q ≠ some v)

theorem collapse_eq_some_iff {V : Type*} {F : IndexedCells V} (x : State F) (v : V) :
    collapse x = some v ↔ x = Sum.inl v := by
  cases x with
  | inl a => simp [collapse]
  | inr b => simp [collapse]

theorem isHoldingInterval_iff_isOptionHoldingInterval {V : Type*} (F : IndexedCells V)
    (X : ℝ≥0 → State F) (v w : V) (s t : ℝ≥0) :
    IsHoldingInterval F X v w s t ↔
      IsOptionHoldingInterval F (fun r => collapse (X r)) v w s t := by
  simp only [IsHoldingInterval, IsOptionHoldingInterval, collapse_eq_some_iff, ne_eq]

/-! ## The interpolation through an arbitrary point choice -/

/-- **The corpus conclusions for an arbitrary point choice.**  At an environment with the corpus
fixed-start conclusions, and for any point choice `p v ∈ cell v`, there is a measurable continuous
interpolation `Ip` of the exact-holding-time path through the points `p v`, whose diffusive
rescalings converge weakly in `C(ℝ≥0, Plane)` to the target. -/
theorem exists_interpolation_through_points (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (hfix : FixedStartConclusions e D hG Φ target start)
    (z : CellField) (hz : IsCellRepresentative z)
    (p : Vertex e.val → Plane) (hp : ∀ v, p v ∈ ((decode e).cell v : Set Plane)) :
    ∃ (Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
      (Zp : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
      (Ip : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
      Measurable Ip ∧
      (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
        (∀ t, collapse (Xexact t ω) = exactAreaPath (decode e) D t ω) ∧
        (∀ v w s t, IsHoldingInterval (decode e) (fun t => Xexact t ω) v w s t →
          (t : ℝ) - s = areaHoldingLength (decode e) v) ∧
        RegularSpatialExtension (decode e) p (fun t => Xexact t ω) (fun t => Zp t ω) ∧
        IsContinuousInterpolation (decode e) p (fun t => Xexact t ω) (fun t => Zp t ω) (Ip ω)) ∧
      ConvergesWeaklyInC (areaSampleLaw (decode e) D hG start)
        (fun ε ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Ip ω)) target := by
  obtain ⟨Xexp, Xexact, M, hae, -, -, -, hrep⟩ := hfix
  obtain ⟨Zexp, Zexact, Iexp, Iexact, hae2, hlim⟩ :=
    hrep (replaceAt z e p) (isCellRepresentative_replaceAt z hz e p hp)
  obtain ⟨-, hmeas, -, hq⟩ := hlim
  rw [replaceAt_at] at hae2
  refine ⟨Xexact, Zexact, Iexact, hmeas, ?_,
    convergesWeaklyInC_of_quenched _ Iexact hmeas target hq⟩
  filter_upwards [hae, hae2] with ω h1 h2
  obtain ⟨-, hcol, -, -, -, -, -, -, hhold, -⟩ := h1
  exact ⟨hcol, hhold, h2.2.1, h2.2.2.2⟩

/-- Almost surely every vertex time of the exact-holding-time path lies in a complete holding
interval (`Option` form). -/
theorem ae_hasCompleteOptionHoldingIntervals (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (hfix : FixedStartConclusions e D hG Φ target start)
    (z : CellField) (hz : IsCellRepresentative z) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ r v,
      exactAreaPath (decode e) D r ω = some v →
        ∃ s t w, IsOptionHoldingInterval (decode e)
          (fun r => exactAreaPath (decode e) D r ω) v w s t ∧ r ∈ Ico s t := by
  obtain ⟨Xexact, Zp, Ip, -, hae, -⟩ :=
    exists_interpolation_through_points e D hG Φ target start hfix z hz (z.at e) (hz e)
  filter_upwards [hae] with ω h
  obtain ⟨hcol, -, -, hint⟩ := h
  intro r v hr
  obtain ⟨s, t, w, hhold, hrst⟩ :=
    hint.2.1 r v ((collapse_eq_some_iff _ _).mp ((hcol r).trans hr))
  refine ⟨s, t, w, ?_, hrst⟩
  have h' := (isHoldingInterval_iff_isOptionHoldingInterval _ _ v w s t).mp hhold
  simpa only [hcol] using h'

/-- Almost surely every complete holding interval at `v` of the exact-holding-time path has length
`Area(v)/π(v)` (`Option` form). -/
theorem ae_optionHoldingInterval_length (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (hfix : FixedStartConclusions e D hG Φ target start)
    (z : CellField) (hz : IsCellRepresentative z) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ v w s t,
      IsOptionHoldingInterval (decode e) (fun r => exactAreaPath (decode e) D r ω) v w s t →
        (t : ℝ) - s = areaHoldingLength (decode e) v := by
  obtain ⟨Xexact, Zp, Ip, -, hae, -⟩ :=
    exists_interpolation_through_points e D hG Φ target start hfix z hz (z.at e) (hz e)
  filter_upwards [hae] with ω h
  obtain ⟨hcol, hlen, -, -⟩ := h
  intro v w s t hhold
  apply hlen v w s t
  rw [isHoldingInterval_iff_isOptionHoldingInterval]
  simpa only [hcol] using hhold

/-- **Weak convergence in `C` of the rescaled interpolation through an arbitrary point choice.**
At an environment with the corpus fixed-start conclusions, whose exact-holding-time path almost
surely takes only vertex states, let `p v ∈ cell v` be any point choice and `Y` any path which,
almost surely, runs linearly from `p v` to `p w` over every complete holding interval `[s, t]` of
the exact path (at `v`, then jumping to `w`).  Then the rescalings `t ↦ ε • Y(t / ε²)` converge
weakly in `C(ℝ≥0, Plane)` to the target.  No measurability of `Y` is assumed: `Y` agrees almost
surely with the corpus interpolation through `p`. -/
theorem convergesWeaklyInC_interpolated (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (hfix : FixedStartConclusions e D hG Φ target start)
    (z : CellField) (hz : IsCellRepresentative z)
    (p : Vertex e.val → Plane) (hp : ∀ v, p v ∈ ((decode e).cell v : Set Plane))
    (hvert : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t,
      exactAreaPath (decode e) D t ω ≠ none)
    (Y : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hY : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ v w s t,
      IsOptionHoldingInterval (decode e) (fun r => exactAreaPath (decode e) D r ω) v w s t →
        ∀ r ∈ Icc s t, Y ω r = AffineMap.lineMap (p v) (p w) (((r : ℝ) - s) / ((t : ℝ) - s))) :
    ConvergesWeaklyInC (areaSampleLaw (decode e) D hG start)
      (fun ε ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Y ω)) target := by
  obtain ⟨Xexact, Zp, Ip, -, hae, hconv⟩ :=
    exists_interpolation_through_points e D hG Φ target start hfix z hz p hp
  refine convergesWeaklyInC_congr_ae (fun ε => ?_) hconv
  filter_upwards [hae, hvert, hY] with ω h1 hv hYω
  obtain ⟨hcol, -, -, hint⟩ := h1
  have hIpY : Ip ω = Y ω := by
    ext r : 1
    obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp (hv r)
    have hX : Xexact r ω = Sum.inl v :=
      (collapse_eq_some_iff _ _).mp ((hcol r).trans hv')
    obtain ⟨s, t, w, hhold, hr⟩ := hint.2.1 r v hX
    have hhold' : IsOptionHoldingInterval (decode e)
        (fun r => exactAreaPath (decode e) D r ω) v w s t := by
      have h' := (isHoldingInterval_iff_isOptionHoldingInterval _ _ v w s t).mp hhold
      simpa only [hcol] using h'
    rw [hint.2.2.1 v w s t hhold r ⟨hr.1, hr.2.le⟩, hYω v w s t hhold' r ⟨hr.1, hr.2.le⟩]
  rw [hIpY]

end ReflectedGMS.GMS.InterpolatedConvergence

assert_no_sorry ReflectedGMS.GMS.InterpolatedConvergence.replaceAt_at
assert_no_sorry ReflectedGMS.GMS.InterpolatedConvergence.isCellRepresentative_replaceAt
assert_no_sorry ReflectedGMS.GMS.InterpolatedConvergence.isHoldingInterval_iff_isOptionHoldingInterval
assert_no_sorry ReflectedGMS.GMS.InterpolatedConvergence.exists_interpolation_through_points
assert_no_sorry ReflectedGMS.GMS.InterpolatedConvergence.ae_hasCompleteOptionHoldingIntervals
assert_no_sorry ReflectedGMS.GMS.InterpolatedConvergence.ae_optionHoldingInterval_length
assert_no_sorry ReflectedGMS.GMS.InterpolatedConvergence.convergesWeaklyInC_interpolated

#print axioms ReflectedGMS.GMS.InterpolatedConvergence.isCellRepresentative_replaceAt
#print axioms ReflectedGMS.GMS.InterpolatedConvergence.exists_interpolation_through_points
#print axioms ReflectedGMS.GMS.InterpolatedConvergence.ae_hasCompleteOptionHoldingIntervals
#print axioms ReflectedGMS.GMS.InterpolatedConvergence.ae_optionHoldingInterval_length
#print axioms ReflectedGMS.GMS.InterpolatedConvergence.convergesWeaklyInC_interpolated
