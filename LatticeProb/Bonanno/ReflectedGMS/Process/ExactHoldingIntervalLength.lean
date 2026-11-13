/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ExactHoldingIntervalLength at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ExactExponentialTimeChange
import LatticeProb.Bonanno.ReflectedGMS.Process.PathwiseClockClauseLift

/-!
# `hhold`: the exact-holding path holds exactly `a_v / π(v)` at `v`

Clause (9) of `InvarianceAssembly.PathwiseClockClauses`, transported to the
collapsed path by `PathwiseClockClauseLift.isHoldingInterval_iff_isCollapsedHoldingInterval`,
says that every maximal constancy interval `[s,t)` of the exact-holding area path
ending in a jump to a *neighbour* has length exactly
`AreaClocks.areaHoldingLength F v = a_v / π(v)`.

For the constructed process `IndexSet.X Gs Y w E` this is a statement about the
holding intervals `[τ_η, τ_η̂)` of (3.26), whose lengths are `T_η = E_η / w(Y_η)`
— with the unit family `E ≡ 1` and `w = areaRate F = π/a` that is exactly
`a_{Y_η} / π(Y_η)`.  What has to be proved is that a maximal constancy interval
*is* a single holding interval:

* its left endpoint is `τ_η` — otherwise the maximality clause
  (`s = 0 ∨ ∀ r < s, ∃ q ∈ (r,s), X q ≠ v`) is contradicted by constancy of `X`
  on `[τ_η, τ_η̂)`;
* its right endpoint is not *before* `τ_η̂`, because `X t = some u` with
  `Adj v u` forces `u ≠ v`;
* its right endpoint is not *after* `τ_η̂`, because that would force
  `Y_η̂ = Y_η`, i.e. the embedded chain would repeat a vertex in one step.

The last point is the only genuinely new ingredient, and it is unconditional:
the transition probabilities (3.2)–(3.3) of `Yⁿ` vanish on the diagonal
(`transProb_self_eq_zero` — `c(x,x) = 0` inside `VGₙ`, and the harmonic measure
from outside `VGₙ` is supported on `VGₙ`), so almost surely no level chain ever
repeats a vertex in one step (`sampleLaw_ae_forall_ne`), and consecutive classes
of `Ξ` are read off one level chain at consecutive times
(`Yxi_succ_ne`).

Consequently `hhold` costs **exactly the same single named input** as `hexact`,
namely `ExactExponentialTimeChange.ExactAreaClockReachesLevelZeroIndices`; it
adds no obligation of its own.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.ExactHoldingIntervalLength

open Code EnvironmentFields StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet QuenchedFormulation
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.ExactExponentialTimeChange

universe u

/-! ## The embedded chain never repeats a vertex in one step -/

section Chain

/-- A Markov chain whose kernel gives no mass to staying put never repeats a
state in one step, almost surely.  The Markov property at a deterministic time
(`MarkovChain.chainLaw_map_walkShift`) reduces every index to the first. -/
theorem chainLaw_ae_forall_ne {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (κ : Kernel S S) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x {x} = 0) (z : S) :
    ∀ᵐ ω ∂MarkovChain.chainLaw κ z, ∀ j : ℕ, ω (j + 1) ≠ ω j := by
  have hA : MeasurableSet {ω : ℕ → S | ω 1 = ω 0} := by
    have hrw : {ω : ℕ → S | ω 1 = ω 0}
        = ⋃ x : S, ((fun f : ℕ → S => f 1) ⁻¹' {x} ∩ (fun f : ℕ → S => f 0) ⁻¹' {x}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_iUnion,
        Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨ω 0, h, rfl⟩
      · rintro ⟨x, h1, h0⟩
        rw [h1, h0]
    rw [hrw]
    exact MeasurableSet.iUnion fun x =>
      ((measurable_pi_apply 1) (measurableSet_singleton x)).inter
        ((measurable_pi_apply 0) (measurableSet_singleton x))
  have hbase : ∀ y : S, MarkovChain.chainLaw κ y {ω : ℕ → S | ω 1 = ω 0} = 0 := by
    intro y
    have hm : (MarkovChain.chainLaw κ y).map (fun ω => ω 1) {y} = 0 := by
      rw [MarkovChain.chainLaw_marginal_one]
      exact hκ y
    rw [Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton y)] at hm
    have hm' : MarkovChain.chainLaw κ y {ω : ℕ → S | ω 1 = y} = 0 := hm
    have h1 : ∀ᵐ ω ∂MarkovChain.chainLaw κ y, ω 1 ≠ y := by
      rw [ae_iff]
      simpa using hm'
    have h0 : ∀ᵐ ω ∂MarkovChain.chainLaw κ y, ω 0 = y := MarkovChain.chainLaw_ae_start κ y
    have hne : ∀ᵐ ω ∂MarkovChain.chainLaw κ y, ω 1 ≠ ω 0 := by
      filter_upwards [h0, h1] with ω hω0 hω1
      rw [hω0]
      exact hω1
    simpa using ae_iff.1 hne
  rw [ae_all_iff]
  intro j
  have hmapzero : ((MarkovChain.chainLaw κ z).map (MarkovChain.walkShift j))
      {ω : ℕ → S | ω 1 = ω 0} = 0 := by
    rw [MarkovChain.chainLaw_map_walkShift,
      Measure.bind_apply hA (Kernel.aemeasurable _)]
    have hzero : ∀ y : S, MarkovChain.pathKernel κ y {ω : ℕ → S | ω 1 = ω 0} = 0 := by
      intro y
      rw [MarkovChain.pathKernel_apply]
      exact hbase y
    simp only [hzero]
    exact lintegral_zero
  rw [Measure.map_apply (MarkovChain.measurable_walkShift j) hA] at hmapzero
  have hpre : MarkovChain.chainLaw κ z {ω : ℕ → S | ω (j + 1) = ω j} = 0 := hmapzero
  rw [ae_iff]
  simpa using hpre

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V}

/-- The transition probabilities (3.2)–(3.3) vanish on the diagonal: inside
`VGₙ` because `c(x,x) = 0`, outside because the harmonic-measure jump lands in
`VGₙ`. -/
theorem transProb_self_eq_zero (hG : G.toSimpleGraph.Connected) (S : Finset V)
    (x : V) : G.transProb hG S x x = 0 := by
  unfold ConductanceGraph.transProb
  split_ifs <;> simp [G.c_self]

theorem stepKernel_self_eq_zero (D : G.Exhaustion) (hG : G.toSimpleGraph.Connected)
    (n : ℕ) (x : V) : D.stepKernel hG n x {x} = 0 := by
  rw [ConductanceGraph.Exhaustion.stepKernel_singleton]
  show ENNReal.ofReal (G.transProb hG (D.Gsub n) x x) = 0
  rw [transProb_self_eq_zero hG (D.Gsub n) x, ENNReal.ofReal_zero]

/-- **No level chain repeats a vertex in one step**, almost surely under the
canonical sample law. -/
theorem sampleLaw_ae_forall_ne (D : G.Exhaustion) (hG : G.toSimpleGraph.Connected)
    (z : V) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ i j : ℕ, ω.1 i (j + 1) ≠ ω.1 i j := by
  rw [ae_all_iff]
  intro i
  refine Existence.sampleLaw_ae_level (z := z)
    (q := fun p : ℕ → V => ∀ j : ℕ, p (j + 1) ≠ p j) D hG i ?_
  exact chainLaw_ae_forall_ne (D.stepKernel hG (D.nz z + i))
    (fun x => stepKernel_self_eq_zero D hG (D.nz z + i) x) z

end Chain

/-! ## Consecutive classes of `Ξ` carry distinct vertices -/

section Classes

variable {V : Type u}

/-- **Consecutive classes of `Ξ` never repeat a vertex.**  The successor `η̂` of
(3.24) is read at a level `m` with `Y_η ∈ G_m`, where `Y_η = Yᵐ_j` and
`Y_η̂ = Yᵐ_{j+1}` are consecutive states of one level chain. -/
theorem Yxi_succ_ne {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ}
    (hcd : HoldingTimeChange.ChainData Gs Y w)
    (hne : ∀ m j : ℕ, Y m (j + 1) ≠ Y m j) {η : ℕ →₀ ℕ} :
    Yxi Gs Y (succ Gs Y η) ≠ Yxi Gs Y η := by
  have hx := exists_level_le_mem Gs Y hcd.monotone hcd.cover η
  have key : ∃ m, level η ≤ m ∧ succ Gs Y η = succAt Gs Y m η := by
    refine ⟨Classical.choose hx, (Classical.choose_spec hx).1, ?_⟩
    unfold IndexSet.succ
    rw [dif_pos hx]
  obtain ⟨m, hlev, hsucc⟩ := key
  have h1 : Yxi Gs Y (succ Gs Y η) = Y m (tm Gs Y m η + 1) := by
    rw [hsucc]
    show Yxi Gs Y (addr Gs Y m (tm Gs Y m η + 1)) = Y m (tm Gs Y m η + 1)
    exact hcd.consistent.Yxi_addr Gs Y m (tm Gs Y m η + 1)
  have h2 : Yxi Gs Y η = Y m (tm Gs Y m η) := hcd.consistent.Yxi_eq Gs Y hlev
  rw [h1]
  intro hcon
  exact hne m (tm Gs Y m η) (hcon.trans h2)

end Classes

/-! ## The deterministic length of a maximal constancy interval -/

section Deterministic

variable {V : Type u}

/-- `a_v / π(v)` is the reciprocal of the area rate `π(v) / a_v`. -/
theorem areaHoldingLength_eq_one_div (F : IndexedCells V) (v : V) :
    areaHoldingLength F v = 1 / areaRate F v := by
  simp only [areaHoldingLength, areaRate, one_div, inv_div]

/-- **Clause (9), pathwise.**  A maximal constancy interval of the exact-holding
process that ends in a jump to a neighbour is exactly one holding interval of
(3.26), hence has length `a_v / π(v)`. -/
theorem sub_eq_areaHoldingLength_of_isCollapsedHoldingInterval
    (F : IndexedCells V) {Gs : ℕ → Set V} {Y : ℕ → ℕ → V}
    (hcd : HoldingTimeChange.ChainData Gs Y (areaRate F))
    (hd : HoldingTimeChange.ClockData Gs Y (areaRate F) (fun _ => 1))
    (hne : ∀ m j : ℕ, Y m (j + 1) ≠ Y m j) {v u : V} {s t : ℝ≥0}
    (hI : PathwiseClockClauseLift.IsCollapsedHoldingInterval F
      (X Gs Y (areaRate F) (fun _ => 1)) v u s t) :
    (t : ℝ) - (s : ℝ) = areaHoldingLength F v := by
  obtain ⟨hst, hconst, hend, hadj, hleft⟩ := hI
  have hsv : X Gs Y (areaRate F) (fun _ => 1) s = some v := hconst s ⟨le_rfl, hst⟩
  obtain ⟨η, hIη, hYη⟩ :=
    Existence.exists_inInterval_of_X_eq_some Gs Y (areaRate F) (fun _ => 1) hsv
  obtain ⟨hηR, hη1, hη2⟩ := hIη
  have hfin : tau Gs Y (areaRate F) (fun _ => 1) η ≠ ⊤ := hd.tau_ne_top hηR
  have hsuccR : Realized Gs Y (succ Gs Y η) := hcd.realized_succ hηR
  have hsuccF : tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η) ≠ ⊤ :=
    hd.tau_ne_top hsuccR
  have hsucc : tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η)
      = tau Gs Y (areaRate F) (fun _ => 1) η + holding Gs Y (areaRate F) (fun _ => 1) η :=
    hcd.tau_succ hηR
  -- the left endpoint is `τ_η`
  have hsτ : (s : ℝ≥0∞) = tau Gs Y (areaRate F) (fun _ => 1) η := by
    refine le_antisymm ?_ hη1
    rcases hleft with h0 | hgap
    · rw [h0]
      exact zero_le
    · by_contra hcon
      have hlt : tau Gs Y (areaRate F) (fun _ => 1) η < (s : ℝ≥0∞) := not_le.1 hcon
      have hr : (tau Gs Y (areaRate F) (fun _ => 1) η).toNNReal < s := by
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin]
        exact hlt
      obtain ⟨q, hq, hqv⟩ := hgap _ hr
      refine hqv ?_
      have hq1 : tau Gs Y (areaRate F) (fun _ => 1) η ≤ (q : ℝ≥0∞) := by
        rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe]
        exact hq.1.le
      have hq2 : (q : ℝ≥0∞) < tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η) :=
        lt_trans (by exact_mod_cast hq.2) hη2
      rw [hcd.consistent.X_eq_of_inInterval Gs Y (areaRate F) (fun _ => 1)
        hcd.monotone hcd.cover ⟨hηR, hq1, hq2⟩, hYη]
  -- the right endpoint is `τ_η̂`
  have htτ : (t : ℝ≥0∞) = tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η) := by
    refine le_antisymm ?_ ?_
    · by_contra hcon
      have hlt : tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η) < (t : ℝ≥0∞) :=
        not_le.1 hcon
      have hp : ((tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η)).toNNReal : ℝ≥0∞)
          = tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η) :=
        ENNReal.coe_toNNReal hsuccF
      have hps : s ≤ (tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η)).toNNReal := by
        rw [← ENNReal.coe_le_coe, hp, hsτ, hsucc]
        exact le_self_add
      have hpt : (tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η)).toNNReal < t := by
        rw [← ENNReal.coe_lt_coe, hp]
        exact hlt
      have hXp := hconst _ ⟨hps, hpt⟩
      have hInt : InInterval Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η)
          (((tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
        refine ⟨hsuccR, le_of_eq hp.symm, ?_⟩
        rw [hp, hcd.tau_succ hsuccR]
        exact ENNReal.lt_add_right hsuccF
          (Existence.holding_pos Gs Y (areaRate F) (fun _ => 1) hcd.ratePos
            (a := succ Gs Y η) one_pos).ne'
      rw [hcd.consistent.X_eq_of_inInterval Gs Y (areaRate F) (fun _ => 1)
        hcd.monotone hcd.cover hInt] at hXp
      have hveq : Yxi Gs Y (succ Gs Y η) = v := Option.some_injective V hXp
      exact absurd (hveq.trans hYη.symm) (Yxi_succ_ne hcd hne)
    · by_contra hcon
      have hlt : (t : ℝ≥0∞) < tau Gs Y (areaRate F) (fun _ => 1) (succ Gs Y η) :=
        not_le.1 hcon
      have hInt : InInterval Gs Y (areaRate F) (fun _ => 1) η ((t : ℝ≥0) : ℝ≥0∞) := by
        refine ⟨hηR, ?_, hlt⟩
        rw [← hsτ, ENNReal.coe_le_coe]
        exact hst.le
      rw [hcd.consistent.X_eq_of_inInterval Gs Y (areaRate F) (fun _ => 1)
        hcd.monotone hcd.cover hInt, hYη] at hend
      exact absurd (Option.some_injective V hend) hadj.ne
  -- the length
  have hcpos : (0 : ℝ) < 1 / areaRate F v := by
    have := hcd.ratePos v
    positivity
  have hkey : (t : ℝ≥0∞) = (s : ℝ≥0∞) + ENNReal.ofReal (1 / areaRate F v) := by
    rw [htτ, hsucc, ← hsτ]
    congr 1
    simp only [holding, hYη]
  have hreal := congrArg ENNReal.toReal hkey
  rw [ENNReal.coe_toReal, ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.ofReal_ne_top,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal hcpos.le] at hreal
  rw [hreal, add_sub_cancel_left, areaHoldingLength_eq_one_div]

end Deterministic

/-! ## The almost-sure statement -/

section Probabilistic

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V]

/-- **Clause (9) of `PathwiseClockClauses` for one cell field, one exhaustion and
one start**, from (3.16) for the unit holding family alone. -/
theorem ae_sub_eq_areaHoldingLength (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (hrate : ∀ v, 0 < areaRate F v) (z : V)
    (hone : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1)) :
    ∀ᵐ ω ∂(areaSampleLaw F D hG z), ∀ (v u : V) (s t : ℝ≥0),
      PathwiseClockClauseLift.IsCollapsedHoldingInterval F
          (fun r => exactAreaPath F D r ω) v u s t →
        (t : ℝ) - (s : ℝ) = areaHoldingLength F v := by
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, sampleLaw_ae_forall_ne D hG z, hone]
    with ω hc h0 hne hs2
  have hcd : HoldingTimeChange.ChainData (D.levelSets (D.nz z)) ω.1 (areaRate F) :=
    ⟨hc, D.levelSets_mono (D.nz z), D.exists_mem_levelSets (D.nz z), hrate⟩
  have hd : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F)
      (fun _ => 1) := ⟨fun _ => one_pos, hs2⟩
  have heq : (fun r => exactAreaPath F D r ω)
      = X (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) := by
    funext r
    show Existence.process D (areaRate F) r (exactHoldingSample ω) = _
    exact Existence.process_eq D (areaRate F) (z := z) (ω := exactHoldingSample ω)
      (h0 0) hc r
  intro v u s t hI
  rw [heq] at hI
  exact sub_eq_areaHoldingLength_of_isCollapsedHoldingInterval F hcd hd
    (fun m j => hne m j) hI

end Probabilistic

/-! ## The environment level -/

section Environment

/-- **Clause (9) at one environment**, from the exact-holding area-clock
residual. -/
theorem ae_sub_eq_areaHoldingLength_env (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h4 : ExactAreaClockReachesLevelZeroIndices e D hG) (z : Vertex e.val) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG z), ∀ (v u : Vertex e.val) (s t : ℝ≥0),
      PathwiseClockClauseLift.IsCollapsedHoldingInterval (decode e)
          (fun r => exactAreaPath (decode e) D r ω) v u s t →
        (t : ℝ) - (s : ℝ) = areaHoldingLength (decode e) v :=
  ae_sub_eq_areaHoldingLength (decode e) D hG (areaRate_pos e) z
    (ae_holdingTimesSummable_one D hG (areaRate (decode e)) (areaRate_pos e) z (h4 z))

/-- **The `hhold` input of `PathwiseClockClauseLift.ae_hlift_of_atomic_inputs`,
reduced to the *same* single residual as `hexact`.**  No obligation beyond
`ExactAreaClockReachesLevelZeroIndices` is created. -/
theorem ae_hhold_of_exact_clock_residual (ν : Measure Env)
    (hexactclock : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → ExactAreaClockReachesLevelZeroIndices e D hG) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            ∀ v u s t, PathwiseClockClauseLift.IsCollapsedHoldingInterval (decode e)
                (fun r => exactAreaPath (decode e) D r ω) v u s t →
              (t : ℝ) - (s : ℝ) = areaHoldingLength (decode e) v := by
  intro n
  filter_upwards [hexactclock] with e hx
  intro hn hnt D hG hdat
  letI := hnt
  exact ae_sub_eq_areaHoldingLength_env e D hG (hx hnt D hG hdat) ⟨n, hn⟩

end Environment

end ReflectedGMS.ExactHoldingIntervalLength
