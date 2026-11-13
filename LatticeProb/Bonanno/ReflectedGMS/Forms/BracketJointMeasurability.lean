/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BracketJointMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClocks
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Joint measurability of the ordinary-edge bracket integral

`MartingaleIngredients.ordinaryEdgeBracket cells Φ X i j t ω` is the running
Lebesgue integral `∫₀ᵗ Γ(X_s ω) ds` of `p:eq:fastPhibracket`.  The consumer
`PredictableCompletionModification.isStronglyPredictable_ordinaryEdgeBracket_completedNaturalFiltration`
carries exactly one analytic hypothesis, `hjoint : Measurable (uncurry (ordinaryEdgeBracket …))`,
and the trace computation of that module shows the hypothesis cannot be removed:
no completion of the filtration makes an a.e. modification with a wild time
section predictable.  This module discharges `hjoint`.

## The two halves

* **The reduction** (`measurable_uncurry_runningIntegral`,
  `measurable_uncurry_ordinaryEdgeBracket`).  For any *jointly* measurable
  `X : ℝ≥0 → Ω → S` and measurable `g : S → ℝ`, the running interval integral
  `(t, ω) ↦ ∫₀ᵗ g (X s ω) ds` is jointly measurable.  No integrability is
  needed: the Bochner integral of a non-integrable function is `0`, and
  `MeasureTheory.StronglyMeasurable.integral_prod_right'` carries no
  integrability hypothesis either.  Specialised to
  `g = stateBracketDensity cells Φ · i j` with the project idiom
  `measurable_of_countable` for the discrete state type `Option V`.

* **The path** (`measurable_uncurry_process`,
  `measurable_uncurry_exponentialAreaPath`,
  `measurable_uncurry_processFamily_X`).  `ReflectedWalk.ProcessFamily` records
  only the per-time measurability `measurable_X`, and joint measurability is
  *not* a consequence of `IsReflectedWalk`: right continuity there holds only
  almost surely, so on the exceptional null set the path is arbitrary.  For the
  *concrete* process `ReflectedWalk.Existence.process` — the one behind
  `AreaClocks.exponentialAreaPath` and `Existence.processFamily` — joint
  measurability does hold everywhere, and is already implicit in the checked
  fibre computation `ReflectedWalk.PathProperties.measurableSet_prod_process`,
  which exhibits `{(ω, s) | X_s ω = x}` as a product-measurable set.  All that is
  missing is the repackaging, which is what this module supplies.

The end product is `measurable_uncurry_ordinaryEdgeBracket_processFamily`: the
hypothesis `hjoint` of
`isStronglyPredictable_ordinaryEdgeBracket_completedNaturalFiltration`, for the
concrete reflected process family of Theorem 1.6.

Consumer: the third clause of `MartingaleIngredients.HasOrdinaryEdgeBracket`,
i.e. `p:eq:fastPhibracket` of `p:lem:localharm`.
-/

set_option autoImplicit false

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace ReflectedGMS.BracketJointMeasurability

open MartingaleIngredients
open ReflectedWalk ReflectedWalk.Theorem16

universe u

/-! ## The Mathlib-only reduction -/

section Reduction

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Mathlib-only reduction.**  A running interval integral of a measurable
function of a *jointly* measurable process is jointly measurable in the upper
limit and the sample point.

The proof rewrites the value at `(t, ω)` as a full Lebesgue integral of the
indicator of the product set `{((t, ω), s) | 0 < s ≤ t}`, which is measurable on
`(ℝ≥0 × Ω) × ℝ`, and then applies
`MeasureTheory.StronglyMeasurable.integral_prod_right'` for the (s-finite)
Lebesgue measure on `ℝ`. -/
theorem measurable_uncurry_runningIntegral
    {S : Type*} [MeasurableSpace S] {X : ℝ≥0 → Ω → S} {g : S → ℝ}
    (hX : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) (hg : Measurable g) :
    Measurable (uncurry fun (t : ℝ≥0) (ω : Ω) =>
      ∫ s in (0 : ℝ)..(t : ℝ), g (X s.toNNReal ω)) := by
  classical
  have hset : MeasurableSet {q : (ℝ≥0 × Ω) × ℝ | q.2 ∈ Set.Ioc (0 : ℝ) (q.1.1 : ℝ)} := by
    have h1 : MeasurableSet {q : (ℝ≥0 × Ω) × ℝ | (0 : ℝ) < q.2} :=
      measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet {q : (ℝ≥0 × Ω) × ℝ | q.2 ≤ (q.1.1 : ℝ)} :=
      measurableSet_le measurable_snd measurable_fst.fst.coe_nnreal_real
    exact h1.inter h2
  have hprod : Measurable fun q : (ℝ≥0 × Ω) × ℝ =>
      Set.indicator (Set.Ioc (0 : ℝ) (q.1.1 : ℝ))
        (fun s : ℝ => g (X s.toNNReal q.1.2)) q.2 := by
    have e : (fun q : (ℝ≥0 × Ω) × ℝ =>
        Set.indicator (Set.Ioc (0 : ℝ) (q.1.1 : ℝ))
          (fun s : ℝ => g (X s.toNNReal q.1.2)) q.2) =
        Set.indicator {q : (ℝ≥0 × Ω) × ℝ | q.2 ∈ Set.Ioc (0 : ℝ) (q.1.1 : ℝ)}
          (fun q : (ℝ≥0 × Ω) × ℝ => g (X q.2.toNNReal q.1.2)) := by
      funext q
      by_cases hq : q.2 ∈ Set.Ioc (0 : ℝ) (q.1.1 : ℝ)
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem
            (show q ∈ {q : (ℝ≥0 × Ω) × ℝ | q.2 ∈ Set.Ioc (0 : ℝ) (q.1.1 : ℝ)} from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem
            (show q ∉ {q : (ℝ≥0 × Ω) × ℝ | q.2 ∈ Set.Ioc (0 : ℝ) (q.1.1 : ℝ)} from hq)]
    rw [e]
    exact (hg.comp (hX.comp
      (measurable_snd.real_toNNReal.prodMk measurable_fst.snd))).indicator hset
  have hfinal : Measurable fun p : ℝ≥0 × Ω => ∫ s : ℝ,
      Set.indicator (Set.Ioc (0 : ℝ) (p.1 : ℝ))
        (fun r : ℝ => g (X r.toNNReal p.2)) s :=
    (hprod.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have e2 : (uncurry fun (t : ℝ≥0) (ω : Ω) =>
        ∫ s in (0 : ℝ)..(t : ℝ), g (X s.toNNReal ω)) =
      fun p : ℝ≥0 × Ω => ∫ s : ℝ,
        Set.indicator (Set.Ioc (0 : ℝ) (p.1 : ℝ))
          (fun r : ℝ => g (X r.toNNReal p.2)) s := by
    funext p
    show (∫ s in (0 : ℝ)..(p.1 : ℝ), g (X s.toNNReal p.2)) = _
    rw [intervalIntegral.integral_of_le p.1.coe_nonneg,
      MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [e2]
  exact hfinal

/-- **`hjoint` from joint measurability of the path.**  The manuscript's
ordinary-edge bracket integral is jointly measurable in `(t, ω)` as soon as the
underlying state process is.  This is exactly the hypothesis that
`isStronglyPredictable_ordinaryEdgeBracket_completedNaturalFiltration` leaves to
its caller. -/
theorem measurable_uncurry_ordinaryEdgeBracket {V : Type u} [Countable V]
    (cells : IndexedCells V) (Φ : V → Plane) {X : ℝ≥0 → Ω → Option V} (i j : Fin 2)
    (hX : Measurable fun p : ℝ≥0 × Ω => X p.1 p.2) :
    Measurable (uncurry (ordinaryEdgeBracket cells Φ X i j)) :=
  measurable_uncurry_runningIntegral hX
    (measurable_of_countable fun q : Option V => stateBracketDensity cells Φ q i j)

end Reduction

/-! ## Joint measurability of the concrete constructed path -/

section Path

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- **Joint measurability of the path (3.26).**  The process
`ReflectedWalk.PathProperties.process` is measurable for the product σ-algebra
`Borel(ℝ≥0) ⊗ 𝓕`, at *every* sample point — no null set is discarded.  This is a
repackaging of the checked fibre computation
`ReflectedWalk.PathProperties.measurableSet_prod_process`, which exhibits each
fibre `{(ω, s) | X_s ω = o}` as a product-measurable set; the set is built from
the clocks `τ_η`, the holding times `T_η` and the discrete path, none of which
depend on the time argument, with the time entering only through the two
comparisons `τ_η ≤ s < τ_η + T_η`. -/
theorem measurable_uncurry_pathProcess {Ω : Type u} [MeasurableSpace Ω]
    (Gs : ℕ → Set V) (w : V → ℝ) {Y : Ω → ℕ → ℕ → V} {En : Ω → (ℕ →₀ ℕ) → ℝ}
    (hY : Measurable Y) (hE : Measurable En) (hGs : Monotone Gs)
    (hcov : ∀ x : V, ∃ n, x ∈ Gs n) :
    Measurable fun p : ℝ≥0 × Ω => PathProperties.process Gs w Y En p.1 p.2 := by
  have hbase : Measurable fun q : Ω × ℝ =>
      PathProperties.process Gs w Y En (Real.toNNReal q.2) q.1 :=
    measurable_to_countable' fun o =>
      PathProperties.measurableSet_prod_process Gs w hY hE hGs hcov o
  have hswap : Measurable fun p : ℝ≥0 × Ω => ((p.2, (p.1 : ℝ)) : Ω × ℝ) :=
    measurable_snd.prodMk measurable_fst.coe_nnreal_real
  have e : (fun p : ℝ≥0 × Ω => PathProperties.process Gs w Y En p.1 p.2) =
      (fun q : Ω × ℝ => PathProperties.process Gs w Y En (Real.toNNReal q.2) q.1) ∘
        (fun p : ℝ≥0 × Ω => ((p.2, (p.1 : ℝ)) : Ω × ℝ)) := by
    funext p
    simp only [Function.comp_apply, Real.toNNReal_coe]
  rw [e]
  exact hbase.comp hswap

set_option maxHeartbeats 1000000 in
/-- **Joint measurability of the constructed reflected process.**  The process
family of Theorem 1.6 reads its base exhaustion level off the starting vertex
`Y⁰₀` of the sample; decomposing along the countably many values of that vertex
(exactly as in the per-time `ReflectedWalk.Existence.measurable_process`)
transports `measurable_uncurry_pathProcess`. -/
theorem measurable_uncurry_process {G : ConductanceGraph V} (D : G.Exhaustion)
    (w : V → ℝ) :
    Measurable fun p : ℝ≥0 × Existence.Sample V => Existence.process D w p.1 p.2 := by
  have h : (fun p : ℝ≥0 × Existence.Sample V => Existence.process D w p.1 p.2) =
      fun p : ℝ≥0 × Existence.Sample V =>
        (fun q : (ℝ≥0 × Existence.Sample V) × V =>
          PathProperties.process (D.levelSets (D.nz q.2)) w Prod.fst Prod.snd q.1.1 q.1.2)
          (p, p.2.1 0 0) :=
    rfl
  rw [h]
  have hpair : Measurable fun p : ℝ≥0 × Existence.Sample V => (p, p.2.1 0 0) :=
    measurable_id.prodMk ((Existence.measurable_Y (V := V) 0 0).comp measurable_snd)
  have hF : Measurable fun q : (ℝ≥0 × Existence.Sample V) × V =>
      PathProperties.process (D.levelSets (D.nz q.2)) w Prod.fst Prod.snd q.1.1 q.1.2 := by
    refine measurable_from_prod_countable_left fun v => ?_
    exact measurable_uncurry_pathProcess (D.levelSets (D.nz v)) w
      (measurable_fst : Measurable (Prod.fst : Existence.Sample V → ℕ → ℕ → V))
      (measurable_snd : Measurable (Prod.snd : Existence.Sample V → (ℕ →₀ ℕ) → ℝ))
      (D.levelSets_mono _) (D.exists_mem_levelSets _)
  exact hF.comp hpair

variable [Nontrivial V]

/-- Joint measurability of the process of `ReflectedWalk.Existence.processFamily`,
the concrete family for which `IsReflectedWalk` is proved. -/
theorem measurable_uncurry_processFamily_X {G : ConductanceGraph V} (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) :
    Measurable fun p : ℝ≥0 × (Existence.processFamily D hG w).Ω =>
      (Existence.processFamily D hG w).X p.1 p.2 :=
  measurable_uncurry_process D w

end Path

/-! ## The discharged hypothesis -/

section Discharge

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

variable [Nontrivial V]

/-- **The hypothesis `hjoint`, discharged for the concrete reflected process
family.**  This is literally the last argument of
`PredictableCompletionModification.isStronglyPredictable_ordinaryEdgeBracket_completedNaturalFiltration`
at `PF := ReflectedWalk.Existence.processFamily D hG w`. -/
theorem measurable_uncurry_ordinaryEdgeBracket_processFamily
    {G : ConductanceGraph V} (D : G.Exhaustion) (hG : G.toSimpleGraph.Connected)
    (w : V → ℝ) (cells : IndexedCells V) (Φ : V → Plane) (i j : Fin 2) :
    Measurable (uncurry
      (ordinaryEdgeBracket cells Φ (Existence.processFamily D hG w).X i j)) :=
  measurable_uncurry_ordinaryEdgeBracket cells Φ i j
    (measurable_uncurry_processFamily_X D hG w)

end Discharge

end ReflectedGMS.BracketJointMeasurability
