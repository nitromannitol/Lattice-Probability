/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ClockCrossClosenessPathwise at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ExactHoldingIntervalLength
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ExactAreaClockCollapse
import LatticeProb.Bonanno.ReflectedGMS.Limit.InterpolatedTwoClockReduction

/-!
# The two interpolations agree after the clock time change (`p:thm:exactclt`, last paragraph)

The manuscript closes `p:thm:exactclt` with: *"Both interpolations move linearly over each
holding interval, so time change respects them."*  This file proves that sentence, pathwise
and at **every** time, for any pair of interpolations admitted by
`InterpolatedTwoClockReduction.PathwiseInterpolationClauses`:

```
  Iexact(r) = Iexp(φ(r))     for all r ≥ 0,
```

where `φ = HoldingTimeChange.timeChange Gs Y w E 1` is the explicit clock carrying elapsed
exact time to elapsed exponential time on the same coupled chain.

## Why the identity is exact, not approximate

`φ` is affine on each holding interval `[τ¹_η, τ¹_η̂)` of the exact path
(`HoldingTimeChange.clock_of_inInterval`), and a *maximal* constancy interval of the exact
path is exactly one such holding interval (`exists_index_of_isCollapsedHoldingInterval`: the
chain never repeats a vertex in one step, `ExactHoldingIntervalLength.Yxi_succ_ne`).  Both
interpolations are affine in time on corresponding maximal intervals, so they agree at every
vertex time.  At the remaining (end-valued) times both sides are continuous and the vertex
times are dense (Lemma 3.7, `HoldingTimeChange.exists_inOpenInterval_between`), so they agree
there too.  No property of the spatial extensions `Zexp`, `Zexact` at end times is used.

## Main results

* `isCollapsedHoldingInterval_of_comp` — maximal holding intervals transport along any
  order-isomorphic time change;
* `exists_index_of_isCollapsedHoldingInterval` — a maximal holding interval of the
  constructed path is one index interval `[τ_η, τ_η̂]`, for any holding family;
* `timeChange_eq_affine` — the clock is affine across that closed interval;
* `interpolation_eq_comp_timeChange` — the deterministic identity;
* `ae_interpolation_exact_eq_comp` — the identity almost surely, for the actual walk, from
  `EnvironmentWalkData` and the two sets of pathwise clauses alone.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.ClockCrossClosenessPathwise

open AreaClocks SpatialEnds StatementIngredients
open ReflectedWalk ReflectedWalk.IndexSet
open ReflectedGMS.PathwiseClockClauseLift
open ReflectedGMS.HoldingTimeChange

universe u

/-! ## Maximal holding intervals along an order-isomorphic time change -/

section Transport

variable {V : Type*}

/-- **Maximal holding intervals transport along a time change.**  If `Xb = Xa ∘ φ` for a
strictly increasing surjection `φ` of `[0,∞)` fixing `0`, then every maximal holding interval
`[s,t]` of `Xb` is carried to the maximal holding interval `[φ s, φ t]` of `Xa`, with the same
vertex and the same following vertex. -/
theorem isCollapsedHoldingInterval_of_comp {F : IndexedCells V} {Xa Xb : ℝ≥0 → Option V}
    {φ : ℝ≥0 → ℝ≥0} (hmono : StrictMono φ) (hsurj : Function.Surjective φ) (h0 : φ 0 = 0)
    (hXb : ∀ t, Xb t = Xa (φ t)) {v w : V} {s t : ℝ≥0}
    (h : IsCollapsedHoldingInterval F Xb v w s t) :
    IsCollapsedHoldingInterval F Xa v w (φ s) (φ t) := by
  obtain ⟨hst, hconst, hend, hadj, hleft⟩ := h
  refine ⟨hmono hst, fun r' hr' => ?_, by rw [← hXb]; exact hend, hadj, ?_⟩
  · obtain ⟨r, rfl⟩ := hsurj r'
    rw [← hXb]
    exact hconst r ⟨hmono.le_iff_le.1 hr'.1, hmono.lt_iff_lt.1 hr'.2⟩
  · rcases hleft with hs0 | hmax
    · exact Or.inl (by rw [hs0, h0])
    · refine Or.inr fun r' hr' => ?_
      obtain ⟨r, rfl⟩ := hsurj r'
      obtain ⟨q, hq, hqv⟩ := hmax r (hmono.lt_iff_lt.1 hr')
      exact ⟨φ q, ⟨hmono hq.1, hmono hq.2⟩, by rw [← hXb]; exact hqv⟩

end Transport

/-! ## A maximal holding interval is one index interval -/

section Index

variable {V : Type u}

/-- **A maximal constancy interval of the constructed path is one holding interval of
(3.26)**, for an arbitrary positive holding family `E`.  This is the argument of
`ExactHoldingIntervalLength.sub_eq_areaHoldingLength_of_isCollapsedHoldingInterval` with the
unit family replaced by `E`, and with the index itself returned rather than only the length:
the left end is `τ_η` by maximality, the right end is `τ_η̂` because the following vertex is a
neighbour (hence different) and the chain never repeats a vertex in one step. -/
theorem exists_index_of_isCollapsedHoldingInterval (F : IndexedCells V) {Gs : ℕ → Set V}
    {Y : ℕ → ℕ → V} {w : V → ℝ} {E : (ℕ →₀ ℕ) → ℝ}
    (hcd : ChainData Gs Y w) (hd : ClockData Gs Y w E)
    (hne : ∀ m j : ℕ, Y m (j + 1) ≠ Y m j) {v u : V} {s t : ℝ≥0}
    (hI : IsCollapsedHoldingInterval F (X Gs Y w E) v u s t) :
    ∃ η, Realized Gs Y η ∧ Yxi Gs Y η = v ∧ (s : ℝ≥0∞) = tau Gs Y w E η ∧
      (t : ℝ≥0∞) = tau Gs Y w E (succ Gs Y η) := by
  obtain ⟨hst, hconst, hend, hadj, hleft⟩ := hI
  have hsv : X Gs Y w E s = some v := hconst s ⟨le_rfl, hst⟩
  obtain ⟨η, hIη, hYη⟩ := Existence.exists_inInterval_of_X_eq_some Gs Y w E hsv
  obtain ⟨hηR, hη1, hη2⟩ := hIη
  have hfin : tau Gs Y w E η ≠ ⊤ := hd.tau_ne_top hηR
  have hsuccR : Realized Gs Y (succ Gs Y η) := hcd.realized_succ hηR
  have hsuccF : tau Gs Y w E (succ Gs Y η) ≠ ⊤ := hd.tau_ne_top hsuccR
  have hsucc : tau Gs Y w E (succ Gs Y η) = tau Gs Y w E η + holding Gs Y w E η :=
    hcd.tau_succ hηR
  -- the left endpoint is `τ_η`
  have hsτ : (s : ℝ≥0∞) = tau Gs Y w E η := by
    refine le_antisymm ?_ hη1
    rcases hleft with h0 | hgap
    · rw [h0]
      exact zero_le
    · by_contra hcon
      have hlt : tau Gs Y w E η < (s : ℝ≥0∞) := not_le.1 hcon
      have hr : (tau Gs Y w E η).toNNReal < s := by
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin]
        exact hlt
      obtain ⟨q, hq, hqv⟩ := hgap _ hr
      refine hqv ?_
      have hq1 : tau Gs Y w E η ≤ (q : ℝ≥0∞) := by
        rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe]
        exact hq.1.le
      have hq2 : (q : ℝ≥0∞) < tau Gs Y w E (succ Gs Y η) :=
        lt_trans (by exact_mod_cast hq.2) hη2
      rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover ⟨hηR, hq1, hq2⟩,
        hYη]
  -- the right endpoint is `τ_η̂`
  have htτ : (t : ℝ≥0∞) = tau Gs Y w E (succ Gs Y η) := by
    refine le_antisymm ?_ ?_
    · by_contra hcon
      have hlt : tau Gs Y w E (succ Gs Y η) < (t : ℝ≥0∞) := not_le.1 hcon
      have hp : ((tau Gs Y w E (succ Gs Y η)).toNNReal : ℝ≥0∞)
          = tau Gs Y w E (succ Gs Y η) :=
        ENNReal.coe_toNNReal hsuccF
      have hps : s ≤ (tau Gs Y w E (succ Gs Y η)).toNNReal := by
        rw [← ENNReal.coe_le_coe, hp, hsτ, hsucc]
        exact le_self_add
      have hpt : (tau Gs Y w E (succ Gs Y η)).toNNReal < t := by
        rw [← ENNReal.coe_lt_coe, hp]
        exact hlt
      have hXp := hconst _ ⟨hps, hpt⟩
      have hInt : InInterval Gs Y w E (succ Gs Y η)
          (((tau Gs Y w E (succ Gs Y η)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
        refine ⟨hsuccR, le_of_eq hp.symm, ?_⟩
        rw [hp, hcd.tau_succ hsuccR]
        exact ENNReal.lt_add_right hsuccF
          (Existence.holding_pos Gs Y w E hcd.ratePos (a := succ Gs Y η) (hd.pos _)).ne'
      rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover hInt] at hXp
      have hveq : Yxi Gs Y (succ Gs Y η) = v := Option.some_injective V hXp
      exact absurd (hveq.trans hYη.symm) (ExactHoldingIntervalLength.Yxi_succ_ne hcd hne)
    · by_contra hcon
      have hlt : (t : ℝ≥0∞) < tau Gs Y w E (succ Gs Y η) := not_le.1 hcon
      have hInt : InInterval Gs Y w E η ((t : ℝ≥0) : ℝ≥0∞) := by
        refine ⟨hηR, ?_, hlt⟩
        rw [← hsτ, ENNReal.coe_le_coe]
        exact hst.le
      rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover hInt, hYη] at hend
      exact absurd (Option.some_injective V hend) hadj.ne
  exact ⟨η, hηR, hYη, hsτ, htτ⟩

end Index

/-! ## The clock is affine across a closed holding interval -/

section Affine

variable {V : Type u} {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ} {E₁ E₂ : (ℕ →₀ ℕ) → ℝ}

/-- **The clock is affine across the closed holding interval `[τ²_η, τ²_η̂]`**, with slope
`E₁_η / E₂_η`.  On the half-open interval this is `HoldingTimeChange.clock_of_inInterval`; at
the right end it is `clock_tau` at `η̂` together with `τ_η̂ = τ_η + T_η` for both families. -/
theorem timeChange_eq_affine (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η) {s t r : ℝ≥0}
    (hs : (s : ℝ≥0∞) = tau Gs Y w E₂ η) (ht : (t : ℝ≥0∞) = tau Gs Y w E₂ (succ Gs Y η))
    (hr : r ∈ Icc s t) :
    ((timeChange Gs Y w E₁ E₂ r : ℝ≥0) : ℝ)
      = (timeChange Gs Y w E₁ E₂ s : ℝ) + E₁ η / E₂ η * ((r : ℝ) - s) := by
  have hρ : (0 : ℝ) ≤ E₁ η / E₂ η := (div_pos (hd₁.pos η) (hd₂.pos η)).le
  have hcs : clock Gs Y w E₁ E₂ (s : ℝ≥0∞) = tau Gs Y w E₁ η := by
    rw [hs]
    exact clock_tau hcd hd₁ hd₂ hη
  have hkey : clock Gs Y w E₁ E₂ (r : ℝ≥0∞)
      = clock Gs Y w E₁ E₂ (s : ℝ≥0∞)
        + ENNReal.ofReal (E₁ η / E₂ η) * ((r : ℝ≥0∞) - (s : ℝ≥0∞)) := by
    rcases eq_or_lt_of_le hr.2 with hrt | hrt
    · rw [hrt, ht, clock_tau hcd hd₁ hd₂ (hcd.realized_succ hη), hcd.tau_succ (E := E₁) hη,
        hcs, hcd.tau_succ (E := E₂) hη, ← hs,
        ENNReal.add_sub_cancel_left ENNReal.coe_ne_top, ofReal_ratio_mul_holding hcd hd₁ hd₂ η]
    · have hI : InInterval Gs Y w E₂ η (r : ℝ≥0∞) := by
        refine ⟨hη, ?_, ?_⟩
        · rw [← hs]
          exact_mod_cast hr.1
        · rw [← ht]
          exact_mod_cast hrt
      rw [clock_of_inInterval hcd hd₁ hd₂ hI, hcs, ← hs]
  have hsub : ((r : ℝ≥0∞) - (s : ℝ≥0∞)) = ((r - s : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_sub.symm
  rw [← coe_timeChange hcd hd₁ hd₂ r, ← coe_timeChange hcd hd₁ hd₂ s, hsub, ENNReal.ofReal,
    ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_inj] at hkey
  rw [hkey, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hr.1, Real.coe_toNNReal _ hρ]

end Affine

/-! ## The deterministic identity -/

section Identity

variable {V : Type u}

/-- **The time-changed interpolations coincide.**  For the constructed path on one coupled
chain with two positive holding families `E₁`, `E₂` satisfying (3.16), and any two continuous
interpolations of lifts of the two paths, the `E₂`-interpolation is the `E₁`-interpolation
read through the clock `φ = timeChange Gs Y w E₁ E₂` — at every time. -/
theorem interpolation_eq_comp_timeChange (F : IndexedCells V) (z : V → Plane)
    {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ} {E₁ E₂ : (ℕ →₀ ℕ) → ℝ}
    (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁) (hd₂ : ClockData Gs Y w E₂)
    (hne : ∀ m j : ℕ, Y m (j + 1) ≠ Y m j)
    {Xa Xb : ℝ≥0 → State F} {Za Zb Ia Ib : ℝ≥0 → Plane}
    (hca : ∀ t, collapse (Xa t) = X Gs Y w E₁ t) (hcb : ∀ t, collapse (Xb t) = X Gs Y w E₂ t)
    (hIa : IsContinuousInterpolation F z Xa Za Ia)
    (hIb : IsContinuousInterpolation F z Xb Zb Ib) :
    ∀ r, Ib r = Ia (timeChange Gs Y w E₁ E₂ r) := by
  have hsm : StrictMono (timeChange Gs Y w E₁ E₂) := strictMono_timeChange hcd hd₁ hd₂
  have hsurj : Function.Surjective (timeChange Gs Y w E₁ E₂) :=
    surjective_timeChange hcd hd₁ hd₂
  have hφ0 : timeChange Gs Y w E₁ E₂ 0 = 0 := timeChange_zero hcd hd₁ hd₂
  have hφc : Continuous (timeChange Gs Y w E₁ E₂) := by
    have h := (hsm.orderIsoOfSurjective (timeChange Gs Y w E₁ E₂) hsurj).toHomeomorph.continuous
    simp only [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective] at h
    exact h
  have hXX : ∀ t, X Gs Y w E₂ t = X Gs Y w E₁ (timeChange Gs Y w E₁ E₂ t) :=
    X_eq_X_timeChange hcd hd₁ hd₂
  -- the vertex times of the `E₂`-path are dense (Lemma 3.7)
  have hdense : Dense {r : ℝ≥0 | ∃ v, X Gs Y w E₂ r = some v} := by
    rw [dense_iff_exists_between]
    intro a b hab
    obtain ⟨ρ, h1, h2, η, hη, hlo, hhi⟩ :=
      exists_inOpenInterval_between hcd hd₂ (s := (a : ℝ≥0∞)) (t := (b : ℝ≥0∞))
        (by exact_mod_cast hab) ENNReal.coe_ne_top
    have hρtop : ρ ≠ ⊤ := ne_top_of_lt h2
    refine ⟨ρ.toNNReal, ⟨Yxi Gs Y η, ?_⟩, ?_, ?_⟩
    · have hI : InInterval Gs Y w E₂ η ((ρ.toNNReal : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_toNNReal hρtop]
        exact ⟨hη, hlo.le, by rw [hcd.tau_succ (E := E₂) hη]; exact hhi⟩
      exact hcd.consistent.X_eq_of_inInterval Gs Y w E₂ hcd.monotone hcd.cover hI
    · rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hρtop]
      exact h1
    · rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hρtop]
      exact h2
  have hext : Ib = Ia ∘ timeChange Gs Y w E₁ E₂ := by
    refine Continuous.ext_on hdense hIb.1 (hIa.1.comp hφc) ?_
    rintro r ⟨v, hv⟩
    have hXbr : Xb r = Sum.inl v :=
      EndLabelConstruction.collapse_eq_some_iff.1 ((hcb r).trans hv)
    obtain ⟨s, t, u', hHI, hmem⟩ := hIb.2.1 r v hXbr
    have hcoll : IsCollapsedHoldingInterval F (X Gs Y w E₂) v u' s t :=
      (isHoldingInterval_iff_isCollapsedHoldingInterval hcb v u' s t).1 hHI
    have hcollA : IsCollapsedHoldingInterval F (X Gs Y w E₁) v u'
        (timeChange Gs Y w E₁ E₂ s) (timeChange Gs Y w E₁ E₂ t) :=
      isCollapsedHoldingInterval_of_comp hsm hsurj hφ0 hXX hcoll
    have hHIa : IsHoldingInterval F Xa v u'
        (timeChange Gs Y w E₁ E₂ s) (timeChange Gs Y w E₁ E₂ t) :=
      (isHoldingInterval_iff_isCollapsedHoldingInterval hca v u' _ _).2 hcollA
    obtain ⟨η, hη, -, hs, ht⟩ := exists_index_of_isCollapsedHoldingInterval F hcd hd₂ hne hcoll
    have hrI : r ∈ Icc s t := ⟨hmem.1, hmem.2.le⟩
    have htI : t ∈ Icc s t := ⟨hHI.1.le, le_rfl⟩
    have hφrI : timeChange Gs Y w E₁ E₂ r ∈
        Icc (timeChange Gs Y w E₁ E₂ s) (timeChange Gs Y w E₁ E₂ t) :=
      ⟨hsm.monotone hmem.1, hsm.monotone hmem.2.le⟩
    show Ib r = Ia (timeChange Gs Y w E₁ E₂ r)
    rw [hIb.2.2.1 v u' s t hHI r hrI, hIa.2.2.1 v u' _ _ hHIa _ hφrI]
    have hρpos : 0 < E₁ η / E₂ η := div_pos (hd₁.pos η) (hd₂.pos η)
    rw [timeChange_eq_affine hcd hd₁ hd₂ hη hs ht hrI,
      timeChange_eq_affine hcd hd₁ hd₂ hη hs ht htI, add_sub_cancel_left, add_sub_cancel_left,
      mul_div_mul_left _ _ hρpos.ne']
  exact fun r => congrFun hext r

end Identity

/-! ## Almost surely, for the actual walk -/

section Walk

open Code EnvironmentFields EnvironmentLaws QuenchedFormulation
open InvarianceMainStatement ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction

/-- The exact-to-exponential clock of the constructed reflected walk from `start`, at one
sample: elapsed exponential-clock time as a function of elapsed exact-clock time. -/
noncomputable def exactToExpClock (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (start : Vertex e.val)
    (ω : Existence.Sample (Vertex e.val)) (r : ℝ≥0) : ℝ≥0 :=
  timeChange (D.levelSets (D.nz start)) ω.1 (areaRate (decode e)) ω.2 (fun _ => 1) r

/-- **`Iexact = Iexp ∘ φ` almost surely, for the actual walk.**  The only inputs are the walk
data (which give (3.16) for both holding families,
`AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData` and
`ExactAreaClockCollapse.exactAreaClockReachesLevelZeroIndices_of_environmentWalkData`), the
first two pathwise clock clauses (identification of the collapsed lifts) and the two
interpolation clauses.  No clock homeomorphism is taken from clause 8: the explicit clock of
`HoldingTimeChange` is used, because its values are known. -/
theorem ae_interpolation_exact_eq_comp (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hpath : PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ r,
      Iexact ω r = Iexp ω (exactToExpClock e D start ω r) := by
  have h3 := AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
    e D hG hdat
  have h4 :=
    ExactAreaClockCollapse.exactAreaClockReachesLevelZeroIndices_of_environmentWalkData e D hG
      hdat
  have hexp := EnvironmentWalkDataProducer.areaClock_holdingTimesSummable e D hG h3 start
  have hone := ExactExponentialTimeChange.ae_holdingTimesSummable_one D hG
    (areaRate (decode e)) (EnvironmentWalkDataProducer.areaRate_pos e) start (h4 start)
  unfold PathwiseClockClauses at hclock
  unfold PathwiseInterpolationClauses at hpath
  filter_upwards [hclock, hpath, Existence.sampleLaw_ae_consistent D hG start,
    Existence.sampleLaw_ae_start D hG start, Existence.sampleLaw_ae_pos D hG start, hexp, hone,
    ExactHoldingIntervalLength.sampleLaw_ae_forall_ne D hG start]
    with ω hc hp hcons h0 hpos hs1 hs2 hne
  obtain ⟨hc1, hc2, -⟩ := hc
  obtain ⟨-, -, hIexp, hIexact⟩ := hp
  have hcd : ChainData (D.levelSets (D.nz start)) ω.1 (areaRate (decode e)) :=
    ⟨hcons, D.levelSets_mono _, D.exists_mem_levelSets _, EnvironmentWalkDataProducer.areaRate_pos e⟩
  have hd₁ : ClockData (D.levelSets (D.nz start)) ω.1 (areaRate (decode e)) ω.2 :=
    ⟨hpos, hs1⟩
  have hd₂ : ClockData (D.levelSets (D.nz start)) ω.1 (areaRate (decode e)) (fun _ => 1) :=
    ⟨fun _ => one_pos, hs2⟩
  have hca : ∀ t, collapse (Xexp t ω)
      = X (D.levelSets (D.nz start)) ω.1 (areaRate (decode e)) ω.2 t := fun t =>
    (hc1 t).trans (Existence.process_eq D (areaRate (decode e)) (h0 0) hcons t)
  have hcb : ∀ t, collapse (Xexact t ω)
      = X (D.levelSets (D.nz start)) ω.1 (areaRate (decode e)) (fun _ => 1) t := fun t =>
    (hc2 t).trans (Existence.process_eq D (areaRate (decode e)) (z := start)
      (ω := exactHoldingSample ω) (h0 0) hcons t)
  exact interpolation_eq_comp_timeChange (decode e) (z.at e) hcd hd₁ hd₂ (fun m j => hne m j)
    hca hcb hIexp hIexact

end Walk

end ReflectedGMS.ClockCrossClosenessPathwise
