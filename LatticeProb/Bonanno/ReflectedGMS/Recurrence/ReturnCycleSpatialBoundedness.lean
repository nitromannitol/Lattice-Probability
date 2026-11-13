/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.ReturnCycleSpatialBoundedness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ExcursionBoundedRange
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceHoldingDivergence

/-!
# Spatial boundedness on every compact time interval (manuscript `r:prop:criterion`)

`Recurrence/ExcursionBoundedRange.lean` proves the **one-excursion** half of the spatial
cutoff criterion: under `VanishingFarEnergy` the spatial radius `rho` is almost surely
bounded along the first excursion away from the root `o`.  What it explicitly leaves open is
the extension to *every* excursion completed before a fixed time, which needs the successive
returns to `o` to be finite and to diverge.

Both missing inputs are supplied here from **actual** results about the reflected walk, with
no new clock, no spatial local finiteness and no assumed spatial extension:

* the successive returns to the singleton target `{o}` are the already-constructed
  `TargetReturnRecursion.targetReturnTime PF.X {o} n`; they are a.s. finite and attained at
  `o` (`ae_forall_targetReturnTime_finite_mem`), and the holding times they retain diverge by
  `FiniteTraceHoldingDivergence.targetReturnHolding_ae_tsum_eq_top`, whose proof goes through
  the exact actual law `TargetReturnPairProcessLaw.map_targetReturnPair`.  Hence
  `targetReturnTime PF.X {o} n → ∞` (`ae_forall_exists_targetReturnTime_gt`), and the
  half-lines `[τ_n, τ_{n+1})` cover all of `[0, T]` with finitely many indices;
* on `[τ_n, b_n)` (where `b_n = exitAfter PF.X τ_n` is the departure time) the path *is* at
  `o`, and on `[b_n, τ_{n+1})` it avoids `o`, so each such window is an excursion of exactly
  the shape used by `MemFirstExcursion`;
* the one-excursion bound is transported to the `n`-th excursion by the vertex-valued strong
  Markov property (`strongMarkov_completed`) at `τ_n`, whose value is `o`.  Lemma 3.10 needs
  a *measurable* path-space event, so the unbounded-excursion event is realised on
  `Trajectory V` as `badExcursionTraj`, built from the countable dense time set `denseTimes`
  and the measurable hitting surrogate `dhit`; `RightRegularAt` identifies it with the true
  event both at `τ_n` (giving the transport) and at time `0` (giving that it is null, by
  `measure_excursionRangeUnbounded_eq_zero`).

The conclusion `ae_forall_bddAbove_rho_on_boundedTime` is the manuscript statement: almost
surely the `rho`-values at vertex-valued times are bounded on every bounded time interval,
simultaneously for all finite horizons `T`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open ReflectedWalk ReflectedWalk.Theorem16
open scoped NNReal ENNReal

namespace ReflectedGMS.ReturnCycleSpatialBoundedness

open ReflectedGMS.TargetReturnRecursion ReflectedGMS.TargetReturnPairProcessLaw
open ReflectedGMS.ExcursionBoundedRange ReflectedGMS.CountableTargetExcursion

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-! ## The root return cycle

The `n`-th return to the root is `targetReturnTime PF.X {o} n` and the `n`-th departure is
`exitAfter PF.X (targetReturnTime PF.X {o} n)`; both are the actual objects of
`Forms/TargetReturnRecursion.lean`, so the divergence and law results apply verbatim. -/

/-- The exit time from the position at `τ` is the hitting time of `{≠ o}` after `τ`, whenever
`τ` is finite with value `o`. -/
theorem exitAfter_eq_hittingAfter_of_eq {Ω : Type u} {X : ℝ≥0 → Ω → Option V}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} {a : ℝ≥0} {o : V}
    (ha : τ ω = ((a : ℝ≥0) : WithTop ℝ≥0)) (hXa : X a ω = some o) :
    exitAfter X τ ω = hittingAfter X {q : Option V | q ≠ some o} a ω := by
  have hsv : stoppedValue X τ ω = some o := by
    show X (τ ω).untopA ω = some o
    rw [ha]
    exact hXa
  show hitAfter X {q : Option V | q ≠ stoppedValue X τ ω} τ ω = _
  rw [hsv]
  exact hitAfter_coe ha

/-- **The holding interval at the root.**  Strictly before the departure the path sits at the
root. -/
theorem eq_root_of_lt_exitAfter {Ω : Type u} {X : ℝ≥0 → Ω → Option V}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} {a t : ℝ≥0} {o : V}
    (ha : τ ω = ((a : ℝ≥0) : WithTop ℝ≥0)) (hXa : X a ω = some o) (hat : a ≤ t)
    (ht : ((t : ℝ≥0) : WithTop ℝ≥0) < exitAfter X τ ω) : X t ω = some o := by
  rw [exitAfter_eq_hittingAfter_of_eq ha hXa] at ht
  have h := notMem_of_lt_hittingAfter ht hat
  simpa using h

/-- **The excursion interval.**  Between the departure and the next return the path avoids the
root. -/
theorem ne_root_of_lt_targetReturnTime_succ {Ω : Type u} {X : ℝ≥0 → Ω → Option V}
    {ω : Ω} {b s : ℝ≥0} {o : V} {n : ℕ}
    (hb : exitAfter X (targetReturnTime X ({o} : Finset V) n) ω = ((b : ℝ≥0) : WithTop ℝ≥0))
    (hbs : b ≤ s)
    (hs : ((s : ℝ≥0) : WithTop ℝ≥0) < targetReturnTime X ({o} : Finset V) (n + 1) ω) :
    X s ω ≠ some o := by
  have hret : targetReturnTime X ({o} : Finset V) (n + 1) ω
      = hittingAfter X (some '' ((({o} : Finset V) : Finset V) : Set V)) b ω := hitAfter_coe hb
  rw [hret] at hs
  have h := notMem_of_lt_hittingAfter hs hbs
  intro hcon
  exact h ⟨o, by simp, hcon.symm⟩

/-! The stopping times take values in `WithTop ℝ≥0` while the holding-time divergence is
stated in `ℝ≥0∞`; the two are the same type, and these three transport lemmas make the
identification explicit so that the `ℝ≥0∞` ordered-arithmetic instances can be used. -/

/-- The identity map onto `ℝ≥0∞`, which is the same type; it makes the `ℝ≥0∞` ordered
arithmetic available for the `WithTop ℝ≥0`-valued stopping times. -/
def toENNReal (x : WithTop ℝ≥0) : ℝ≥0∞ := x

theorem toENNReal_le_toENNReal {a b : WithTop ℝ≥0} (h : a ≤ b) :
    toENNReal a ≤ toENNReal b := h

theorem toENNReal_ne_top {a : WithTop ℝ≥0} (h : a ≠ ⊤) : toENNReal a ≠ ⊤ := h

/-- The retained holding times up to index `n` are dominated by the `n`-th return time. -/
theorem sum_targetReturnHolding_le_targetReturnTime {Ω : Type u} {X : ℝ≥0 → Ω → Option V}
    {ω : Ω} {o : V} (hfin : ∀ n : ℕ, targetReturnTime X ({o} : Finset V) n ω ≠ ⊤) (n : ℕ) :
    (∑ j ∈ Finset.range n,
        ENNReal.ofReal (targetReturnHoldingSeq X ({o} : Finset V) ω j))
      ≤ toENNReal (targetReturnTime X ({o} : Finset V) n ω) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact zero_le
  | succ n ih =>
      have hle1 : toENNReal (targetReturnTime X ({o} : Finset V) n ω)
          ≤ toENNReal (exitAfter X (targetReturnTime X ({o} : Finset V) n) ω) :=
        toENNReal_le_toENNReal (le_hitAfter ω)
      have hle2 : toENNReal (exitAfter X (targetReturnTime X ({o} : Finset V) n) ω)
          ≤ toENNReal (targetReturnTime X ({o} : Finset V) (n + 1) ω) :=
        toENNReal_le_toENNReal (exitAfter_targetReturnTime_le_succ X ({o} : Finset V) n ω)
      have hexne :
          toENNReal (exitAfter X (targetReturnTime X ({o} : Finset V) n) ω) ≠ ⊤ :=
        ne_top_of_le_ne_top (toENNReal_ne_top (hfin (n + 1))) hle2
      have hHeq : toENNReal (targetReturnHolding X ({o} : Finset V) n ω)
          = toENNReal (exitAfter X (targetReturnTime X ({o} : Finset V) n) ω)
            - toENNReal (targetReturnTime X ({o} : Finset V) n ω) := rfl
      have hHne : toENNReal (targetReturnHolding X ({o} : Finset V) n ω) ≠ ⊤ := by
        rw [hHeq]
        exact ne_top_of_le_ne_top hexne tsub_le_self
      have hH : ENNReal.ofReal (targetReturnHoldingSeq X ({o} : Finset V) ω n)
          = toENNReal (targetReturnHolding X ({o} : Finset V) n ω) := by
        rw [targetReturnHoldingSeq]
        exact ENNReal.ofReal_toReal hHne
      rw [Finset.sum_range_succ, hH]
      calc
        (∑ j ∈ Finset.range n,
              ENNReal.ofReal (targetReturnHoldingSeq X ({o} : Finset V) ω j))
              + toENNReal (targetReturnHolding X ({o} : Finset V) n ω)
            ≤ toENNReal (targetReturnTime X ({o} : Finset V) n ω)
              + toENNReal (targetReturnHolding X ({o} : Finset V) n ω) :=
              add_le_add ih le_rfl
        _ = toENNReal (exitAfter X (targetReturnTime X ({o} : Finset V) n) ω) := by
              rw [hHeq]
              exact add_tsub_cancel_of_le hle1
        _ ≤ toENNReal (targetReturnTime X ({o} : Finset V) (n + 1) ω) := hle2

section Process

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}

/-- **The actual returns to the root diverge.**  The retained holding times at `o` diverge by
`targetReturnHolding_ae_tsum_eq_top` — an identity for the *actual* reflected walk, obtained
from the exact target-return pair law — and they are dominated by the return times. -/
theorem ae_forall_exists_targetReturnTime_gt (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v) (o : V) :
    ∀ᵐ ω ∂PF.P o, ∀ T : ℝ≥0, ∃ n : ℕ,
      ((T : ℝ≥0) : WithTop ℝ≥0) < targetReturnTime PF.X ({o} : Finset V) n ω := by
  have hA : ({o} : Finset V).Nonempty := ⟨o, Finset.mem_singleton_self o⟩
  have hx : o ∈ ({o} : Finset V) := Finset.mem_singleton_self o
  filter_upwards [ReflectedGMS.targetReturnHolding_ae_tsum_eq_top h hG hw hA hx,
    ae_forall_targetReturnTime_finite_mem h hG hA hx] with ω hdiv hall
  intro T
  have hfin : ∀ n : ℕ, targetReturnTime PF.X ({o} : Finset V) n ω ≠ ⊤ := fun n => (hall n).1
  have hsup : ((T : ℝ≥0) : ℝ≥0∞) < ⨆ n : ℕ, ∑ j ∈ Finset.range n,
      ENNReal.ofReal (targetReturnHoldingSeq PF.X ({o} : Finset V) ω j) := by
    rw [← ENNReal.tsum_eq_iSup_nat, hdiv]
    exact ENNReal.coe_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hsup
  exact ⟨n, lt_of_lt_of_le hn (sum_targetReturnHolding_le_targetReturnTime hfin n)⟩

end Process

/-- Every time before the `N`-th return lies in one of the first `N` return cycles. -/
theorem exists_cycle_index {Ω : Type u} {X : ℝ≥0 → Ω → Option V} {ω : Ω} {o : V} (t : ℝ≥0) :
    ∀ N : ℕ, ((t : ℝ≥0) : WithTop ℝ≥0) < targetReturnTime X ({o} : Finset V) N ω →
      ∃ j : ℕ, j < N ∧ targetReturnTime X ({o} : Finset V) j ω ≤ ((t : ℝ≥0) : WithTop ℝ≥0) ∧
        ((t : ℝ≥0) : WithTop ℝ≥0) < targetReturnTime X ({o} : Finset V) (j + 1) ω := by
  intro N
  induction N with
  | zero =>
      intro hlt
      rw [show targetReturnTime X ({o} : Finset V) 0 ω = ((0 : ℝ≥0) : WithTop ℝ≥0) from rfl] at hlt
      have hlt' : t < (0 : ℝ≥0) := WithTop.coe_lt_coe.1 hlt
      exact absurd hlt' (by simp)
  | succ N ih =>
      intro hlt
      by_cases hN : ((t : ℝ≥0) : WithTop ℝ≥0) < targetReturnTime X ({o} : Finset V) N ω
      · obtain ⟨j, hjN, hj1, hj2⟩ := ih hN
        exact ⟨j, hjN.trans (Nat.lt_succ_self N), hj1, hj2⟩
      · exact ⟨N, Nat.lt_succ_self N, not_lt.1 hN, hlt⟩

/-! ## The measurable path-space surrogate of one unbounded excursion -/

/-- **The path-space form of "the first excursion reaches spatial radius above `R`".**  The
departure time is the measurable surrogate `dhit {q | q ≠ some o}` of the exit time, and the
visit and the absence of a return are tested only at the countable dense set `denseTimes`;
this makes the event measurable for the cylinder σ-algebra, which is what Lemma 3.10 needs.
At a right-regular trajectory the surrogate is the true event. -/
def farExcursionTraj (o : V) (rho : V → ℝ) (R : ℝ) : Set (Trajectory V) :=
  ⋃ t ∈ denseTimes,
    ({γ : Trajectory V | dhit {q : Option V | q ≠ some o} γ ≤ ((t : ℝ≥0) : WithTop ℝ≥0)} ∩
        {γ : Trajectory V | ∃ y : V, R < rho y ∧ γ t = some y} ∩
      ⋂ s ∈ denseTimes, {γ : Trajectory V |
        dhit {q : Option V | q ≠ some o} γ ≤ ((s : ℝ≥0) : WithTop ℝ≥0) → s ≤ t →
          γ s ≠ some o})

/-- The path-space form of an unbounded first excursion: the radius exceeds every level. -/
def badExcursionTraj (o : V) (rho : V → ℝ) : Set (Trajectory V) :=
  ⋂ n : ℕ, farExcursionTraj o rho (rho o + n)

theorem measurableSet_farExcursionTraj (o : V) (rho : V → ℝ) (R : ℝ) :
    MeasurableSet (farExcursionTraj o rho R) := by
  refine MeasurableSet.biUnion denseTimes_countable fun t _ => ?_
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact measurable_dhit _ measurableSet_Iic
  · show MeasurableSet
      (evalProc V t ⁻¹' {q : Option V | ∃ y : V, R < rho y ∧ q = some y})
    exact measurable_evalProc t (measurableSet_option _)
  · refine MeasurableSet.biInter denseTimes_countable fun s _ => ?_
    have hset : {γ : Trajectory V |
          dhit {q : Option V | q ≠ some o} γ ≤ ((s : ℝ≥0) : WithTop ℝ≥0) → s ≤ t →
            γ s ≠ some o}
        = {γ : Trajectory V |
              dhit {q : Option V | q ≠ some o} γ ≤ ((s : ℝ≥0) : WithTop ℝ≥0)}ᶜ ∪
            (({_γ : Trajectory V | ¬ (s ≤ t)}) ∪
              (evalProc V s ⁻¹' {q : Option V | q ≠ some o})) := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage]
      tauto
    rw [hset]
    exact ((measurable_dhit _ measurableSet_Iic).compl).union
      ((MeasurableSet.const _).union (measurable_evalProc s (measurableSet_option _)))

theorem measurableSet_badExcursionTraj (o : V) (rho : V → ℝ) :
    MeasurableSet (badExcursionTraj o rho) :=
  MeasurableSet.iInter fun n => measurableSet_farExcursionTraj o rho _

/-- The exit time of the trajectory shifted to a finite exit time of the original path. -/
theorem exists_dhit_shiftedPath_eq {Ω : Type u} {X : ℝ≥0 → Ω → Option V}
    {o : V} {ω : Ω} (hω : RightRegularAt X ω) {a b : ℝ≥0}
    (hb : hittingAfter X {q : Option V | q ≠ some o} a ω = ((b : ℝ≥0) : WithTop ℝ≥0)) :
    ∃ r : ℝ≥0, r + a = b ∧
      dhit {q : Option V | q ≠ some o} (shiftedPath X a ω) = ((r : ℝ≥0) : WithTop ℝ≥0) := by
  have hγ : RightRegularAt (evalProc V) (shiftedPath X a ω) := rightRegularAt_shiftedPath hω a
  have hd : dhit {q : Option V | q ≠ some o} (shiftedPath X a ω)
      = hittingAfter (evalProc V) {q : Option V | q ≠ some o} 0 (shiftedPath X a ω) :=
    dhit_eq_hittingAfter (admissibleTarget_ne o) hγ
  cases hr : hittingAfter (evalProc V) {q : Option V | q ≠ some o} 0 (shiftedPath X a ω) with
  | top =>
      have htop : hittingAfter X {q : Option V | q ≠ some o} a ω = ⊤ :=
        (hittingAfter_shift_eq_top_iff _ a ω).2 hr
      rw [hb] at htop
      exact absurd htop WithTop.coe_ne_top
  | coe r =>
      refine ⟨r, ?_, by rw [hd, hr]⟩
      have hsh := hittingAfter_shift_eq (admissibleTarget_ne o) hω hr
      rw [hb] at hsh
      exact_mod_cast hsh.symm

/-- **From an unbounded excursion to the measurable surrogate.**  A single vertex-valued time
of an excursion started at the finite time `a` (where the path is at `o`) with radius above
`R ≥ rho o` puts the shifted trajectory in `farExcursionTraj`. -/
theorem mem_farExcursionTraj_futureAt {Ω : Type u} {X : ℝ≥0 → Ω → Option V}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} {o : V} {rho : V → ℝ} {R : ℝ}
    (hω : RightRegularAt X ω) {a : ℝ≥0} (ha : τ ω = ((a : ℝ≥0) : WithTop ℝ≥0))
    (hXa : X a ω = some o) (hRo : rho o ≤ R) {b t : ℝ≥0}
    (hb : exitAfter X τ ω = ((b : ℝ≥0) : WithTop ℝ≥0)) (hbt : b ≤ t)
    (hno : ∀ s : ℝ≥0, b ≤ s → s ≤ t → X s ω ≠ some o)
    {y : V} (hy : R < rho y) (hXt : X t ω = some y) :
    futureAt X τ ω ∈ farExcursionTraj o rho R := by
  have hyo : y ≠ o := by
    intro hcon
    rw [hcon] at hy
    exact absurd hRo (not_le.2 hy)
  rw [exitAfter_eq_hittingAfter_of_eq ha hXa] at hb
  obtain ⟨r, hra, hdhit⟩ := exists_dhit_shiftedPath_eq hω hb
  have hab : a ≤ b := by
    have := le_hittingAfter (u := X) (s := {q : Option V | q ≠ some o}) (n := a) ω
    rw [hb] at this
    exact_mod_cast this
  have hat : a ≤ t := hab.trans hbt
  set γ : Trajectory V := shiftedPath X a ω with hγdef
  have hγreg : RightRegularAt (evalProc V) γ := rightRegularAt_shiftedPath hω a
  have hfut : futureAt X τ ω = γ := futureAt_of_eq ha
  set u : ℝ≥0 := t - a with hudef
  have hua : u + a = t := tsub_add_cancel_of_le hat
  have hγu : γ u = some y := by
    show X (u + a) ω = some y
    rw [hua]; exact hXt
  have hru : r ≤ u := by
    have : r + a ≤ u + a := by rw [hra, hua]; exact hbt
    exact le_of_add_le_add_right this
  obtain ⟨ε, hε, hεs⟩ := hγreg.1 u ⟨y, hγu⟩
  obtain ⟨t', ht'D, ht'u, ht'ε⟩ := denseTimes_dense.exists_between (lt_add_of_pos_right u hε)
  have hγt' : γ t' = some y := (hεs t' ⟨ht'u.le, ht'ε⟩).trans hγu
  rw [hfut]
  simp only [farExcursionTraj]
  refine Set.mem_biUnion ht'D ?_
  refine ⟨⟨?_, ⟨y, hy, hγt'⟩⟩, ?_⟩
  · show dhit {q : Option V | q ≠ some o} γ ≤ ((t' : ℝ≥0) : WithTop ℝ≥0)
    rw [hdhit]
    exact_mod_cast hru.trans ht'u.le
  · refine Set.mem_biInter fun s hsD => ?_
    show dhit {q : Option V | q ≠ some o} γ ≤ ((s : ℝ≥0) : WithTop ℝ≥0) → s ≤ t' →
      γ s ≠ some o
    intro hds hst'
    have hrs : r ≤ s := by rw [hdhit] at hds; exact_mod_cast hds
    rcases le_or_gt s u with hsu | hus
    · show X (s + a) ω ≠ some o
      refine hno (s + a) ?_ ?_
      · rw [← hra]; exact add_le_add hrs le_rfl
      · rw [← hua]; exact add_le_add hsu le_rfl
    · have hsε : s < u + ε := lt_of_le_of_lt hst' ht'ε
      have hγs : γ s = some y := (hεs s ⟨hus.le, hsε⟩).trans hγu
      rw [hγs]
      simpa using hyo

/-- **From the measurable surrogate back to the excursion event.**  At a right-regular
outcome the surrogate is contained in the pathwise excursion event of
`CountableTargetExcursion`, so the vanishing-energy bound applies to it. -/
theorem mem_visitsTargetBeforeReturn_of_mem_farExcursionTraj {PF : ProcessFamily V}
    {ω : PF.Ω} {o : V} {rho : V → ℝ} {R : ℝ} (hω : RightRegularAt PF.X ω) (hRo : rho o ≤ R)
    (hmem : PF.trajectory ω ∈ farExcursionTraj o rho R) :
    ω ∈ visitsTargetBeforeReturn PF o (farTarget rho R) := by
  have hshift : PF.trajectory ω = shiftedPath PF.X 0 ω := (shiftedPath_zero ω).symm
  have hval : ∀ s : ℝ≥0, PF.trajectory ω s = PF.X s ω := fun s => rfl
  simp only [farExcursionTraj] at hmem
  obtain ⟨t, ht, hmemt⟩ := Set.mem_iUnion₂.1 hmem
  obtain ⟨⟨hdt0, hB⟩, hnor⟩ := hmemt
  obtain ⟨y, hy, hγt⟩ := hB
  have hdt : dhit {q : Option V | q ≠ some o} (PF.trajectory ω) ≤ ((t : ℝ≥0) : WithTop ℝ≥0) :=
    hdt0
  -- the exit time is finite
  have hexne : exitTime PF.X o ω ≠ ⊤ := by
    intro htop
    have htop' : hittingAfter PF.X {q : Option V | q ≠ some o} 0 ω = ⊤ := htop
    have h0 : hittingAfter (evalProc V) {q : Option V | q ≠ some o} 0 (shiftedPath PF.X 0 ω)
        = ⊤ := (hittingAfter_shift_eq_top_iff _ 0 ω).1 htop'
    have hd : dhit {q : Option V | q ≠ some o} (PF.trajectory ω) = ⊤ := by
      rw [hshift, dhit_eq_hittingAfter (admissibleTarget_ne o)
        (rightRegularAt_shiftedPath hω 0), h0]
    rw [hd] at hdt
    exact absurd (top_le_iff.1 hdt) WithTop.coe_ne_top
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hexne
  have hbb : hittingAfter PF.X {q : Option V | q ≠ some o} 0 ω = ((b : ℝ≥0) : WithTop ℝ≥0) :=
    hb.symm
  obtain ⟨r, hr0, hdhit⟩ := exists_dhit_shiftedPath_eq hω hbb
  have hrb : r = b := by rw [← hr0, add_zero]
  have hdtraj : dhit {q : Option V | q ≠ some o} (PF.trajectory ω) = ((b : ℝ≥0) : WithTop ℝ≥0) := by
    rw [hshift, hdhit, hrb]
  have huntop : (exitTime PF.X o ω).untopA = b := by rw [← hb]; rfl
  have hbt : b ≤ t := by
    rw [hdtraj] at hdt
    exact_mod_cast hdt
  -- the dense no-return condition, transported to all real times
  have hdense : ∀ s : ℝ≥0, s ∈ denseTimes → b ≤ s → s ≤ t → PF.X s ω ≠ some o := by
    intro s hsD hbs hst
    have hds : dhit {q : Option V | q ≠ some o} (PF.trajectory ω) ≤ ((s : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hdtraj]; exact_mod_cast hbs
    have hmemi : dhit {q : Option V | q ≠ some o} (PF.trajectory ω) ≤ ((s : ℝ≥0) : WithTop ℝ≥0) →
        s ≤ t → PF.trajectory ω s ≠ some o := Set.mem_iInter₂.1 hnor s hsD
    have hne : PF.trajectory ω s ≠ some o := hmemi hds hst
    rwa [hval s] at hne
  refine ⟨t, by rw [huntop]; exact hbt, ⟨y, hy, by rw [← hval t]; exact hγt⟩, ?_⟩
  intro s hs hst hcon
  rw [huntop] at hs
  rcases eq_or_lt_of_le hst with rfl | hlt
  · have : PF.X s ω = some y := by rw [← hval s]; exact hγt
    rw [hcon] at this
    have : y = o := (Option.some_inj.1 this).symm
    rw [this] at hy
    exact absurd hRo (not_le.2 hy)
  · obtain ⟨ε, hε, hεs⟩ := hω.1 s ⟨o, hcon⟩
    obtain ⟨s', hs'D, hss', hs'lt⟩ :=
      denseTimes_dense.exists_between (lt_min (lt_add_of_pos_right s hε) hlt)
    have hXs' : PF.X s' ω = some o := by
      rw [hεs s' ⟨hss'.le, lt_of_lt_of_le hs'lt (min_le_left _ _)⟩]
      exact hcon
    exact hdense s' hs'D (hs.trans hss'.le) (le_of_lt (lt_of_lt_of_le hs'lt (min_le_right _ _))) hXs'

section Transport

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}

/-- The unbounded-excursion path event is null for the law started at the root: on the
right-regular set it is contained in `excursionRangeUnbounded`, whose probability vanishes by
the arbitrary-target excursion bound of `ExcursionBoundedRange`. -/
theorem law_badExcursionTraj_eq_zero (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {o : V} {rho : V → ℝ}
    (hvan : VanishingFarEnergy G o rho) :
    PF.law o (badExcursionTraj o rho) = 0 := by
  have hmeas : Measurable PF.trajectory := Measurable.of_eval fun t => PF.measurable_X t
  have hsub : PF.trajectory ⁻¹' badExcursionTraj o rho ≤ᵐ[PF.P o]
      excursionRangeUnbounded PF o rho := by
    filter_upwards [ae_rightRegularAt (h o).2.2.1 (h o).2.2.2.1] with ω hω hmem
    have hmem' : PF.trajectory ω ∈ ⋂ n : ℕ, farExcursionTraj o rho (rho o + n) := hmem
    refine Set.mem_iInter.2 fun R => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (R - rho o)
    have hRle : R ≤ rho o + n := by linarith [hn]
    have hmemn : PF.trajectory ω ∈ farExcursionTraj o rho (rho o + n) :=
      Set.mem_iInter.1 hmem' n
    have hRo : rho o ≤ rho o + n := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact visitsTargetBeforeReturn_mono PF o (farTarget_antitone rho hRle)
      (mem_visitsTargetBeforeReturn_of_mem_farExcursionTraj hω hRo hmemn)
  show ((PF.P o).map PF.trajectory) (badExcursionTraj o rho) = 0
  rw [Measure.map_apply hmeas (measurableSet_badExcursionTraj o rho)]
  refine le_antisymm ?_ zero_le
  calc PF.P o (PF.trajectory ⁻¹' badExcursionTraj o rho)
      ≤ PF.P o (excursionRangeUnbounded PF o rho) := measure_mono_ae hsub
    _ = 0 := measure_excursionRangeUnbounded_eq_zero h hG hvan

/-- **The strong Markov transport.**  At the `n`-th return the walk is at `o`, so Lemma 3.10
gives the shifted trajectory the law started at `o`, under which the unbounded-excursion event
is null. -/
theorem measure_futureAt_badExcursionTraj_eq_zero (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {o : V} {rho : V → ℝ}
    (hvan : VanishingFarEnergy G o rho) (n : ℕ) :
    PF.P o (futureAt PF.X (targetReturnTime PF.X ({o} : Finset V) n) ⁻¹'
      badExcursionTraj o rho) = 0 := by
  have hA : ({o} : Finset V).Nonempty := ⟨o, Finset.mem_singleton_self o⟩
  have hx : o ∈ ({o} : Finset V) := Finset.mem_singleton_self o
  have hτm := aemeasurable_targetReturnTime h hG hA hx n
  have hτs := isAEStoppingTime_targetReturnTime h hG hA hx n
  have hSM := strongMarkov_completed h o (h o).2.2.2.1 hτm hτs o
    (aemeasurableSetStopped_univ hτs) (measurableSet_badExcursionTraj o rho)
  rw [law_badExcursionTraj_eq_zero h hG hvan, mul_zero] at hSM
  have hstop : ∀ᵐ ω ∂PF.P o,
      ω ∈ stopEvent PF.X (targetReturnTime PF.X ({o} : Finset V) n) o := by
    filter_upwards [ae_forall_targetReturnTime_finite_mem h hG hA hx] with ω hω
    obtain ⟨v, hv, hvv⟩ := (hω n).2
    have hvo : v = o := by simpa using hv
    exact ⟨(hω n).1, by rw [← hvv, hvo]⟩
  have hcongr : futureAt PF.X (targetReturnTime PF.X ({o} : Finset V) n) ⁻¹'
      badExcursionTraj o rho
      =ᵐ[PF.P o] Set.univ ∩ stopEvent PF.X (targetReturnTime PF.X ({o} : Finset V) n) o ∩
        (futureAt PF.X (targetReturnTime PF.X ({o} : Finset V) n) ⁻¹' badExcursionTraj o rho) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hstop] with ω hω
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and]
    exact ⟨fun hmem => ⟨hω, hmem⟩, fun hmem => hmem.2⟩
  rw [measure_congr hcongr]
  exact hSM

/-- **Every excursion has bounded spatial range.**  Simultaneously for all `n`, the radius is
bounded along the `n`-th excursion away from the root. -/
theorem ae_forall_exists_bound_rho_on_excursion (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {o : V} {rho : V → ℝ}
    (hvan : VanishingFarEnergy G o rho) :
    ∀ᵐ ω ∂PF.P o, ∀ n : ℕ, ∃ C : ℝ, ∀ b t : ℝ≥0,
      exitAfter PF.X (targetReturnTime PF.X ({o} : Finset V) n) ω = ((b : ℝ≥0) : WithTop ℝ≥0) →
      b ≤ t → (∀ s : ℝ≥0, b ≤ s → s ≤ t → PF.X s ω ≠ some o) →
      ∀ y : V, PF.X t ω = some y → rho y ≤ C := by
  have hA : ({o} : Finset V).Nonempty := ⟨o, Finset.mem_singleton_self o⟩
  have hx : o ∈ ({o} : Finset V) := Finset.mem_singleton_self o
  have hnull : ∀ᵐ ω ∂PF.P o, ∀ n : ℕ,
      ω ∉ futureAt PF.X (targetReturnTime PF.X ({o} : Finset V) n) ⁻¹'
        badExcursionTraj o rho := by
    rw [ae_all_iff]
    intro n
    exact measure_eq_zero_iff_ae_notMem.1
      (measure_futureAt_badExcursionTraj_eq_zero h hG hvan n)
  filter_upwards [hnull, ae_rightRegularAt (h o).2.2.1 (h o).2.2.2.1,
    ae_forall_targetReturnTime_finite_mem h hG hA hx] with ω hω hreg hret
  intro n
  obtain ⟨a, haa⟩ := WithTop.ne_top_iff_exists.1 (hret n).1
  have ha : targetReturnTime PF.X ({o} : Finset V) n ω = ((a : ℝ≥0) : WithTop ℝ≥0) := haa.symm
  have hXa : PF.X a ω = some o := by
    obtain ⟨v, hv, hvv⟩ := (hret n).2
    have hvo : v = o := by simpa using hv
    rw [← stoppedValue_of_eq (X := PF.X) ha, ← hvv, hvo]
  have hnotall : ¬ (futureAt PF.X (targetReturnTime PF.X ({o} : Finset V) n) ω ∈
      ⋂ k : ℕ, farExcursionTraj o rho (rho o + k)) := hω n
  rw [Set.mem_iInter] at hnotall
  push_neg at hnotall
  obtain ⟨k, hk⟩ := hnotall
  refine ⟨rho o + k, fun b t hb hbt hno y hXt => ?_⟩
  by_contra hcon
  exact hk (mem_farExcursionTraj_futureAt hreg ha hXa
    (by have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith) hb hbt hno
    (not_le.1 hcon) hXt)

/-- **Manuscript Proposition `r:prop:criterion` (spatial cutoff criterion).**  Under the
vanishing-energy hypothesis for the complements of spatial balls, `P_o`-almost surely the
`rho`-values at vertex-valued times are bounded on every bounded time interval, simultaneously
for all finite horizons.

The bound is obtained from the finitely many return cycles met by `[0, T]`: the holding
intervals at the root contribute `rho o`, and each excursion contributes its own bound. -/
theorem ae_forall_bddAbove_rho_on_boundedTime (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v) {o : V} {rho : V → ℝ}
    (hvan : VanishingFarEnergy G o rho) :
    ∀ᵐ ω ∂PF.P o, ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ T →
      ∀ y : V, PF.X t ω = some y → rho y ≤ C := by
  have hA : ({o} : Finset V).Nonempty := ⟨o, Finset.mem_singleton_self o⟩
  have hx : o ∈ ({o} : Finset V) := Finset.mem_singleton_self o
  filter_upwards [ae_forall_exists_targetReturnTime_gt h hG hw o,
    ae_forall_exists_bound_rho_on_excursion h hG hvan,
    ae_forall_targetReturnTime_finite_mem h hG hA hx] with ω hdiv hexc hret
  intro T
  obtain ⟨N, hN⟩ := hdiv T
  choose C hC using hexc
  have hne : ((Finset.range (N + 1)).image C).Nonempty :=
    ⟨C 0, Finset.mem_image_of_mem C (Finset.mem_range.2 (Nat.succ_pos N))⟩
  set M : ℝ := ((Finset.range (N + 1)).image C).sup' hne id with hM
  have hCM : ∀ j : ℕ, j ≤ N → C j ≤ M := by
    intro j hj
    exact Finset.le_sup' id (Finset.mem_image_of_mem C (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine ⟨max M (rho o), fun t hT y hXt => ?_⟩
  have htN : ((t : ℝ≥0) : WithTop ℝ≥0) < targetReturnTime PF.X ({o} : Finset V) N ω :=
    lt_of_le_of_lt (by exact_mod_cast hT) hN
  obtain ⟨j, hjN, hjt, hjt'⟩ := exists_cycle_index (X := PF.X) (ω := ω) (o := o) t N htN
  obtain ⟨a, haa⟩ := WithTop.ne_top_iff_exists.1 (hret j).1
  have ha : targetReturnTime PF.X ({o} : Finset V) j ω = ((a : ℝ≥0) : WithTop ℝ≥0) := haa.symm
  have hXa : PF.X a ω = some o := by
    obtain ⟨v, hv, hvv⟩ := (hret j).2
    have hvo : v = o := by simpa using hv
    rw [← stoppedValue_of_eq (X := PF.X) ha, ← hvv, hvo]
  have hat : a ≤ t := by rw [ha] at hjt; exact_mod_cast hjt
  by_cases hdep : ((t : ℝ≥0) : WithTop ℝ≥0) <
      exitAfter PF.X (targetReturnTime PF.X ({o} : Finset V) j) ω
  · have hXo : PF.X t ω = some o := eq_root_of_lt_exitAfter ha hXa hat hdep
    rw [hXo] at hXt
    have : y = o := (Option.some_inj.1 hXt).symm
    rw [this]
    exact le_max_right M (rho o)
  · have hdle : exitAfter PF.X (targetReturnTime PF.X ({o} : Finset V) j) ω
        ≤ ((t : ℝ≥0) : WithTop ℝ≥0) := not_lt.1 hdep
    have hdne : exitAfter PF.X (targetReturnTime PF.X ({o} : Finset V) j) ω ≠ ⊤ :=
      ne_top_of_le_ne_top (by exact WithTop.coe_ne_top) hdle
    obtain ⟨b, hbb⟩ := WithTop.ne_top_iff_exists.1 hdne
    have hb : exitAfter PF.X (targetReturnTime PF.X ({o} : Finset V) j) ω
        = ((b : ℝ≥0) : WithTop ℝ≥0) := hbb.symm
    have hbt : b ≤ t := by rw [hb] at hdle; exact_mod_cast hdle
    have hno : ∀ s : ℝ≥0, b ≤ s → s ≤ t → PF.X s ω ≠ some o := by
      intro s hbs hst
      refine ne_root_of_lt_targetReturnTime_succ hb hbs ?_
      exact lt_of_le_of_lt (by exact_mod_cast hst) hjt'
    have := hC j b t hb hbt hno y hXt
    exact this.trans ((hCM j hjN.le).trans (le_max_left M (rho o)))

end Transport

end ReflectedGMS.ReturnCycleSpatialBoundedness
