/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ExactExponentialTimeChange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.HoldingTimeChange
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.EnvironmentWalkDataProducer

/-!
# `hexact`: the exact-holding area path is a time change of the exponential one

`AreaClocks.exactAreaPath F D t ω` and `AreaClocks.exponentialAreaPath F D t ω`
are the *same* constructed process `Existence.process D (areaRate F)` on the
*same* coupled chain `ω.1`, evaluated at two holding families: the unit family
`fun _ => 1` and the sample's own exponential family `ω.2`.  So
`Process/HoldingTimeChange.lean` applies verbatim, and clause (8) of
`InvarianceAssembly.PathwiseClockClauses` — the `hexact` input of
`PathwiseClockClauseLift.ae_hlift_of_atomic_inputs` — follows from (3.16) for
each of the two families.

* For the exponential family (3.16) is the project's existing residual
  `EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices`, through the
  checked `EnvironmentWalkDataProducer.areaClock_holdingTimesSummable`.
* For the unit family the **divergence** half is unconditional
  (`ae_tsum_holding_one_addr_zero_eq_top`): the level-`0` chain returns to its
  starting cell infinitely often, and each such visit contributes the same
  positive exact holding length `a_z / π(z)`.  The **finiteness** half is the
  named input `ExactAreaClockReachesLevelZeroIndices`, the exact-holding twin of
  the exponential residual.

## Why the twin is a genuine new input

`AreaClockReachesLevelZeroIndices` says `∑_{ξ < [(0,K)]} E_ξ a_{Y_ξ}/π(Y_ξ) < ∞`;
its twin says `∑_{ξ < [(0,K)]} a_{Y_ξ}/π(Y_ξ) < ∞`.  Conditionally on the chain
these are almost surely equivalent, because for independent unit exponentials
`E_ξ` one has `∑ c_ξ E_ξ < ∞` a.s. iff `∑ c_ξ < ∞` (the Laplace transform
`∏ (1+c_ξ)⁻¹` is positive iff `∑ c_ξ < ∞`).  But that equivalence is a
probabilistic producer — it is *not* a deterministic consequence, and it is not
proved here: nothing in this file certifies either residual.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.ExactExponentialTimeChange

open Code EnvironmentFields StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet QuenchedFormulation
open ReflectedGMS.EnvironmentWalkDataProducer

universe u

/-! ## (3.16) for the unit holding family -/

section Unit

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V}

/-- **The exact holding times diverge along the level-`0` chain**, unconditionally.
Remark 3.1 gives infinitely many returns of `Y⁰` to the starting vertex `z`, and
each of them contributes the same positive exact holding length `1/w(z)`. -/
theorem ae_tsum_holding_one_addr_zero_eq_top (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      ∑' k, holding (D.levelSets (D.nz z)) ω.1 w (fun _ => 1)
        (addr (D.levelSets (D.nz z)) ω.1 0 k) = ⊤ := by
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_rec D hG z] with ω hc hrec
  have hS : {k | ω.1 0 k = z}.Infinite :=
    Set.infinite_of_forall_exists_gt fun N => let ⟨k, hk, h⟩ := hrec N; ⟨k, h, hk⟩
  refine HoldingTimeChange.tsum_eq_top_of_infinite_le hS
    (ENNReal.ofReal_pos.2 (div_pos one_pos (hw z))).ne' ?_
  intro k hk
  have hkz : ω.1 0 k = z := hk
  have hval : holding (D.levelSets (D.nz z)) ω.1 w (fun _ => 1)
      (addr (D.levelSets (D.nz z)) ω.1 0 k) = ENNReal.ofReal (1 / w z) := by
    simp only [holding, hc.Yxi_addr, hkz]
  exact hval.ge

/-- **(3.16) for the unit holding family**, from its finiteness half alone.  The
reduction is the same one `EnvironmentWalkDataProducer.areaClock_holdingTimesSummable`
performs for the exponential family. -/
theorem ae_holdingTimesSummable_one (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V)
    (hfin : ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
      tau (D.levelSets (D.nz z)) ω.1 w (fun _ => 1)
        (addr (D.levelSets (D.nz z)) ω.1 0 K) < ⊤) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w (fun _ => 1) := by
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    ae_tsum_holding_one_addr_zero_eq_top D hG w hw z, hfin] with ω hc h0 hτ
  refine holdingTimesSummable_of _ _ _ _ hc (D.levelSets_mono (D.nz z))
    (D.exists_mem_levelSets (D.nz z)) h0 fun K => ?_
  exact (tau_addr_zero_lt_top_iff _ _ _ _ hc (D.levelSets_mono (D.nz z))
    (D.exists_mem_levelSets (D.nz z)) K).mp (hτ K)

end Unit

/-! ## The two area paths -/

section AreaPaths

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V]

/-- **Clause (8) of `PathwiseClockClauses`, for one cell field, one exhaustion and
one start.**  The two area paths are the same constructed process on the same
chain, with the unit and the exponential holding family respectively. -/
theorem ae_isHomeomorphicTimeChange_exactAreaPath (F : IndexedCells V)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected)
    (hrate : ∀ v, 0 < areaRate F v) (z : V)
    (hexp : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2)
    (hone : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1)) :
    ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      IsHomeomorphicTimeChange (fun t => exactAreaPath F D t ω)
        (fun t => exponentialAreaPath F D t ω) := by
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, Existence.sampleLaw_ae_pos D hG z,
    hexp, hone] with ω hc h0 hpos hs1 hs2
  have hcd : HoldingTimeChange.ChainData (D.levelSets (D.nz z)) ω.1 (areaRate F) :=
    ⟨hc, D.levelSets_mono (D.nz z), D.exists_mem_levelSets (D.nz z), hrate⟩
  have hd₁ : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 :=
    ⟨hpos, hs1⟩
  have hd₂ : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F)
      (fun _ => 1) := ⟨fun _ => one_pos, hs2⟩
  have heq1 : (fun t => exactAreaPath F D t ω)
      = X (D.levelSets (D.nz z)) ω.1 (areaRate F) (fun _ => 1) := by
    funext t
    show Existence.process D (areaRate F) t (exactHoldingSample ω) = _
    exact Existence.process_eq D (areaRate F) (z := z) (ω := exactHoldingSample ω)
      (h0 0) hc t
  have heq2 : (fun t => exponentialAreaPath F D t ω)
      = X (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 := by
    funext t
    exact Existence.process_eq D (areaRate F) (h0 0) hc t
  rw [heq1, heq2]
  exact HoldingTimeChange.isHomeomorphicTimeChange_X hcd hd₁ hd₂

end AreaPaths

/-! ## The environment level -/

section Environment

/-- **The exact-holding twin of
`EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices`**: for every
starting cell, almost surely the *exact* area time elapsed before the level-`0`
index `[(0,K)]` is finite, for every `K`.  This is the finiteness half of (3.16)
for the unit holding family; its divergence half is proved above. -/
def ExactAreaClockReachesLevelZeroIndices (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) : Prop :=
  ∀ z : Vertex e.val, ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
    tau (D.levelSets (D.nz z)) ω.1 (areaRate (decode e)) (fun _ => 1)
      (addr (D.levelSets (D.nz z)) ω.1 0 K) < ⊤

/-- **Clause (8) of `PathwiseClockClauses` at one environment**, from the two
area-clock residuals. -/
theorem ae_isHomeomorphicTimeChange_areaPaths (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG)
    (h4 : ExactAreaClockReachesLevelZeroIndices e D hG) (z : Vertex e.val) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG z),
      IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
        (fun t => exponentialAreaPath (decode e) D t ω) :=
  ae_isHomeomorphicTimeChange_exactAreaPath (decode e) D hG (areaRate_pos e) z
    (areaClock_holdingTimesSummable e D hG h3 z)
    (ae_holdingTimesSummable_one D hG (areaRate (decode e)) (areaRate_pos e) z (h4 z))

/-- **The `hexact` input of `PathwiseClockClauseLift.ae_hlift_of_atomic_inputs`,
reduced to the two area-clock residuals.**

`hclock` is *verbatim* an existing input of
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`,
so it costs nothing new; `hexactclock` is its exact-holding twin, and is the only
new obligation this reduction creates.  Nothing here certifies either. -/
theorem ae_hexact_of_clock_residuals (ν : Measure Env)
    (hclock : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → AreaClockReachesLevelZeroIndices e D hG)
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
            IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
              (fun t => exponentialAreaPath (decode e) D t ω) := by
  intro n
  filter_upwards [hclock, hexactclock] with e hc hx
  intro hn hnt D hG hdat
  letI := hnt
  exact ae_isHomeomorphicTimeChange_areaPaths e D hG (hc hnt D hG hdat)
    (hx hnt D hG hdat) ⟨n, hn⟩

end Environment

end ReflectedGMS.ExactExponentialTimeChange
