/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AreaFastClockIdentificationPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaFastClockIdentificationOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaFastClockIdentificationStopping
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionEnvironment

/-!
# Step (b) of bracket atom 1: the area path IS the fast path read at the inverse area clock

Manuscript `p:eq:timechanged`: `X^{area}_t = Y_{A⁻¹(t)}`, with `Y` the fast walk of the summable
fast rate `w` (speed `m = π/w`) and `A` its area clock `A_u = ∫₀^u (cellArea/m)(Y_s) ds`.
This file proves it **almost surely, for every `t` simultaneously**, for the canonical inverse
`A⁻¹ = AreaTimeChangeJumpLaw.inverseAreaClock` — the only clock that can be a stopping time —
and, on the way, the good event `AreaFastClockStopping.ClockGood` that
`AreaFastClockStopping.isStoppingTime_fastClock` consumes as `hgood`.

**No geometric input.**  `ClockGood` was previously available only through
`AreaClockContinuity.ae_exists_homeomorph_areaClock`, which needs `VanishingFarEnergy` and a
maximal-diameter bound.  Here it follows from **(3.16) for the two rates on the same sample**
together with the chain-time identity `A(τ^w_η) = τ^{area}_η`
(`AreaFastClockIdentification.setLIntegral_areaClockDensity_tau_eq_tau_areaRate`):

* finiteness: every `T` lies below some finite `τ^w_{[(0,K)]}` (first clause of (3.16) for `w`,
  `PathProperties.exists_lt_tau_addr_zero`), and `A` there equals the finite `τ^{area}_{[(0,K)]}`;
* divergence: every finite level lies below some `τ^{area}_{[(0,K)]} = A(τ^w_{[(0,K)]})`
  (first clause of (3.16) for the area rate);
* strict increase: `AreaClockContinuity.strictMono_areaClock_of_path`, whose null-`∞`-sojourn
  input is property (i) of the fast walk.

(3.16) for the fast rate is Lemma 3.5 (`ae_holdingTimesSummable_of_rateFunction_le`) and for
the area rate it is `EnvironmentWalkDataProducer.areaClock_holdingTimesSummable`, discharged
from `EnvironmentWalkData` by `areaClockReachesLevelZeroIndices_of_environmentWalkData`.

**The path identity** is then deterministic (`X_eq_X_symm_of_orderIso`): an order isomorphism
`e` carrying every `w`-chain time to the `w'`-chain time carries each holding interval
`[τ^w_η, τ^w_η̂)` onto `[τ^{w'}_η, τ^{w'}_η̂)`, so `X^{w'}_t = X^w_{e⁻¹ t}`, including at the
`none` times.  Both sides are the actual constructed process (`Existence.process`) on the same
sample; nothing is changed of measure.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.AreaFastClockPath

open StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet ReflectedWalk.Theorem16
open ReflectedGMS.PositiveOccupationClock ReflectedGMS.AreaClockLocalFiniteness
open ReflectedGMS.AreaClockContinuity ReflectedGMS.AreaTimeChangeJumpLaw
open ReflectedGMS.AreaFastClockStopping ReflectedGMS.AreaClockFastSpeedOccupation
open ReflectedGMS.AreaFastClockIdentification

universe u

/-! ## Deterministic core: a clock carrying chain times to chain times carries the path -/

section Deterministic

variable {V : Type u} {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w w' : V → ℝ}
  {E : (ℕ →₀ ℕ) → ℝ}

/-- One chain time: if `e` carries the finite `w`-chain time of `η` to its `w'`-chain time, then
`τ^{w'}_η ≤ t ↔ τ^w_η ≤ e⁻¹ t`. -/
theorem tau_le_coe_iff_of_orderIso (e : ℝ≥0 ≃o ℝ≥0) {η : ℕ →₀ ℕ}
    (hfin : tau Gs Y w E η ≠ ⊤)
    (hτ : ((e (tau Gs Y w E η).toNNReal : ℝ≥0) : ℝ≥0∞) = tau Gs Y w' E η) (t : ℝ≥0) :
    tau Gs Y w' E η ≤ (t : ℝ≥0∞) ↔ tau Gs Y w E η ≤ ((e.symm t : ℝ≥0) : ℝ≥0∞) := by
  have hσ : (((tau Gs Y w E η).toNNReal : ℝ≥0) : ℝ≥0∞) = tau Gs Y w E η :=
    ENNReal.coe_toNNReal hfin
  rw [← hτ, ENNReal.coe_le_coe, ← e.le_symm_apply]
  constructor
  · intro h
    rw [← hσ]
    exact ENNReal.coe_le_coe.2 h
  · intro h
    rw [← hσ] at h
    exact ENNReal.coe_le_coe.1 h

/-- The holding intervals correspond: `t ∈ [τ^{w'}_η, τ^{w'}_η̂) ↔ e⁻¹ t ∈ [τ^w_η, τ^w_η̂)`. -/
theorem inInterval_iff_of_orderIso (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (e : ℝ≥0 ≃o ℝ≥0)
    (hfin : ∀ η, Realized Gs Y η → tau Gs Y w E η ≠ ⊤)
    (hτ : ∀ η, Realized Gs Y η →
      ((e (tau Gs Y w E η).toNNReal : ℝ≥0) : ℝ≥0∞) = tau Gs Y w' E η)
    (η : ℕ →₀ ℕ) (t : ℝ≥0) :
    InInterval Gs Y w' E η (t : ℝ≥0∞) ↔
      InInterval Gs Y w E η ((e.symm t : ℝ≥0) : ℝ≥0∞) := by
  constructor
  · intro hI
    have hη : Realized Gs Y η := hI.1
    have hs : Realized Gs Y (succ Gs Y η) := (hc.succ_spec Gs Y hGm hcov hη).1
    refine ⟨hη, (tau_le_coe_iff_of_orderIso e (hfin η hη) (hτ η hη) t).1 hI.2.1, ?_⟩
    exact not_le.1 fun h =>
      not_le.2 hI.2.2 ((tau_le_coe_iff_of_orderIso e (hfin _ hs) (hτ _ hs) t).2 h)
  · intro hI
    have hη : Realized Gs Y η := hI.1
    have hs : Realized Gs Y (succ Gs Y η) := (hc.succ_spec Gs Y hGm hcov hη).1
    refine ⟨hη, (tau_le_coe_iff_of_orderIso e (hfin η hη) (hτ η hη) t).2 hI.2.1, ?_⟩
    exact not_le.1 fun h =>
      not_le.2 hI.2.2 ((tau_le_coe_iff_of_orderIso e (hfin _ hs) (hτ _ hs) t).1 h)

/-- **The time-change identity of the process (3.26).**  If an order isomorphism `e` of `[0,∞)`
carries every (finite) `w`-chain time to the `w'`-chain time, then `X^{w'}_t = X^w_{e⁻¹ t}` for
every `t`, including the times lying in no holding interval. -/
theorem X_eq_X_symm_of_orderIso (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (e : ℝ≥0 ≃o ℝ≥0)
    (hfin : ∀ η, Realized Gs Y η → tau Gs Y w E η ≠ ⊤)
    (hτ : ∀ η, Realized Gs Y η →
      ((e (tau Gs Y w E η).toNNReal : ℝ≥0) : ℝ≥0∞) = tau Gs Y w' E η) (t : ℝ≥0) :
    X Gs Y w' E t = X Gs Y w E (e.symm t) := by
  have hiff := inInterval_iff_of_orderIso hc hGm hcov e hfin hτ
  by_cases hex : ∃ η, InInterval Gs Y w' E η (t : ℝ≥0∞)
  · obtain ⟨η, hη⟩ := hex
    rw [hc.X_eq_of_inInterval Gs Y w' E hGm hcov hη,
      hc.X_eq_of_inInterval Gs Y w E hGm hcov ((hiff η t).1 hη)]
  · have hex2 : ¬ ∃ η, InInterval Gs Y w E η ((e.symm t : ℝ≥0) : ℝ≥0∞) := by
      rintro ⟨η, hη⟩
      exact hex ⟨η, (hiff η t).2 hη⟩
    rw [(X_eq_none_iff Gs Y w' E t).2 hex, (X_eq_none_iff Gs Y w E (e.symm t)).2 hex2]

end Deterministic

/-! ## The actual clock on one sample -/

section Sample

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V] [DecidableEq V]

/-- **The chain-time identity for the actual process.**  On a consistent sample started at `z`,
the area clock of the fast walk, read at the finite fast chain time `τ^w_η`, is the area chain
time `τ^{area}_η`. -/
theorem areaClock_toNNReal_tau_eq (F : IndexedCells V) (hF : Geometry F)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected) (w : V → ℝ)
    (hw : ∀ v, 0 < w v) {z : V} {ω : Existence.Sample V} (h0 : ω.1 0 0 = z)
    (hc : Consistent (D.levelSets (D.nz z)) ω.1) {η : ℕ →₀ ℕ}
    (hη : Realized (D.levelSets (D.nz z)) ω.1 η)
    (hfin : tau (D.levelSets (D.nz z)) ω.1 w ω.2 η ≠ ⊤) :
    areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w)
        (tau (D.levelSets (D.nz z)) ω.1 w ω.2 η).toNNReal ω
      = tau (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 η := by
  rw [← setLIntegral_areaClockDensity_tau_eq_tau_areaRate F hF hG (D.levelSets (D.nz z)) ω.1 w
    hw ω.2 hc (D.levelSets_mono (D.nz z)) (D.exists_mem_levelSets (D.nz z)) hη hfin]
  show (∫⁻ s in Icc (0 : ℝ)
      (((tau (D.levelSets (D.nz z)) ω.1 w ω.2 η).toNNReal : ℝ≥0) : ℝ),
      (Existence.process D w (Real.toNNReal s) ω).elim 0
        (areaClockDensity F (fun v => F.graph.pi v / w v))) = _
  rw [ENNReal.coe_toNNReal_eq_toReal]
  refine lintegral_congr fun s => ?_
  rw [Existence.process_eq D w h0 hc]

/-- A finite, strictly increasing, divergent area clock is a good clock. -/
theorem clockGood_of_clock (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (ω : PF.Ω) (hfin : ∀ T : ℝ≥0, areaClock F m PF T ω < ∞)
    (hstrict : StrictMono fun t : ℝ≥0 => areaClock F m PF t ω)
    (htop : (⨆ t : ℝ≥0, areaClock F m PF t ω) = ⊤) : ClockGood F m PF ω := by
  have hsm := strictMono_areaClockNN F m PF ω hfin hstrict
  have hsurj := surjective_areaClockNN F m PF ω hfin htop
  refine ⟨(hsm.orderIsoOfSurjective (areaClockNN F m PF ω) hsurj).toHomeomorph,
    ?_, ?_, fun t => ?_⟩
  · simp only [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
    exact hsm
  · simp only [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
    exact areaClockNN_zero F m PF ω
  · simp only [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
    exact coe_areaClockNN F m PF ω (hfin t).ne

/-- **Good clock and path identity on one sample.**  On a consistent sample started at `z` on
which (3.16) holds for both the fast rate `w` and the area rate, and on which the fast path is
measurable in time with null `∞`-sojourn, the area clock of the fast walk is a good clock and
the area path is the fast path read at the canonical inverse clock, at every time. -/
theorem clockGood_and_path_eq_of_sample (F : IndexedCells V) (hF : Geometry F)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected) (w : V → ℝ)
    (hw : ∀ v, 0 < w v) {z : V} {ω : Existence.Sample V} (h0 : ω.1 0 0 = z)
    (hc : Consistent (D.levelSets (D.nz z)) ω.1)
    (hsw : HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w ω.2)
    (hsa : HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2)
    (hX : Measurable fun r : ℝ => (Existence.processFamily D hG w).X (Real.toNNReal r) ω)
    (hnull : ∀ T : ℝ≥0, sojournNone (Existence.processFamily D hG w).X T ω = 0) :
    ClockGood F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) ω ∧
      ∀ t : ℝ≥0, Existence.process D (areaRate F) t ω =
        areaTimeChangedPath F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) t ω := by
  have hGm : Monotone (D.levelSets (D.nz z)) := D.levelSets_mono (D.nz z)
  have hcov : ∀ x, ∃ n, x ∈ D.levelSets (D.nz z) n := D.exists_mem_levelSets (D.nz z)
  have hfinw : ∀ η, Realized (D.levelSets (D.nz z)) ω.1 η →
      tau (D.levelSets (D.nz z)) ω.1 w ω.2 η ≠ ⊤ := fun η hη => (hsw.2 η hη).ne
  have hτ : ∀ η, Realized (D.levelSets (D.nz z)) ω.1 η →
      areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w)
          (tau (D.levelSets (D.nz z)) ω.1 w ω.2 η).toNNReal ω
        = tau (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 η :=
    fun η hη => areaClock_toNNReal_tau_eq F hF D hG w hw h0 hc hη (hfinw η hη)
  have hmono : Monotone fun t : ℝ≥0 =>
      areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) t ω :=
    timeClock_mono (areaClockPathDensity F (fun v => F.graph.pi v / w v)
      (Existence.processFamily D hG w) ω)
  -- finiteness at every horizon
  have hfinA : ∀ T : ℝ≥0,
      areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) T ω < ∞ := by
    intro T
    obtain ⟨K, hK⟩ := PathProperties.exists_lt_tau_addr_zero (D.levelSets (D.nz z)) ω.1 w ω.2
      hsw.1 (ENNReal.coe_ne_top (r := T))
    have hr := realized_addr (D.levelSets (D.nz z)) ω.1 0 K
    have hle : T ≤ (tau (D.levelSets (D.nz z)) ω.1 w ω.2
        (addr (D.levelSets (D.nz z)) ω.1 0 K)).toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hfinw _ hr)]
      exact hK.le
    calc areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) T ω
        ≤ areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w)
            (tau (D.levelSets (D.nz z)) ω.1 w ω.2
              (addr (D.levelSets (D.nz z)) ω.1 0 K)).toNNReal ω := hmono hle
      _ = tau (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2
            (addr (D.levelSets (D.nz z)) ω.1 0 K) := hτ _ hr
      _ < ⊤ := hsa.2 _ hr
  have hstrict : StrictMono fun t : ℝ≥0 =>
      areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) t ω :=
    strictMono_areaClock_of_path F hF (fun v => pi_div_pos hG w hw v)
      (Existence.processFamily D hG w) ω hX hfinA hnull
  have htop : (⨆ t : ℝ≥0,
      areaClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) t ω) = ⊤ := by
    refine iSup_eq_top.2 fun b hb => ?_
    obtain ⟨K, hK⟩ := PathProperties.exists_lt_tau_addr_zero (D.levelSets (D.nz z)) ω.1
      (areaRate F) ω.2 hsa.1 hb.ne
    have hr := realized_addr (D.levelSets (D.nz z)) ω.1 0 K
    exact ⟨(tau (D.levelSets (D.nz z)) ω.1 w ω.2
      (addr (D.levelSets (D.nz z)) ω.1 0 K)).toNNReal, hK.trans_eq (hτ _ hr).symm⟩
  have hgood : ClockGood F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) ω :=
    clockGood_of_clock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) ω
      hfinA hstrict htop
  refine ⟨hgood, fun t => ?_⟩
  have hτ' : ∀ η, Realized (D.levelSets (D.nz z)) ω.1 η →
      ((goodOrderIso hgood (tau (D.levelSets (D.nz z)) ω.1 w ω.2 η).toNNReal : ℝ≥0) : ℝ≥0∞)
        = tau (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 η :=
    fun η hη => (goodOrderIso_apply hgood _).trans (hτ η hη)
  have hpath : areaTimeChangedPath F (fun v => F.graph.pi v / w v)
      (Existence.processFamily D hG w) t ω
        = Existence.process D w ((goodOrderIso hgood).symm t) ω :=
    congrArg (fun s => Existence.process D w s ω) (inverseAreaClock_eq_symm_of_good hgood t)
  refine ((Existence.process_eq D (areaRate F) h0 hc t).trans ?_).trans hpath.symm
  rw [Existence.process_eq D w h0 hc]
  exact X_eq_X_symm_of_orderIso hc hGm hcov (goodOrderIso hgood) hfinw hτ' t

/-- **Good clock and path identity, almost surely**, for any fast rate `w` dominating the
Lemma 3.5 rate function, given (3.16) for the area rate. -/
theorem ae_clockGood_and_path_eq (F : IndexedCells V) (hF : Geometry F)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected)
    (hmin : F.graph.EnergyMinimizer) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hdom : ∀ v, D.rateFunction hG v ≤ w v) (z : V)
    (harea : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      ClockGood F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) ω ∧
      ∀ t : ℝ≥0, Existence.process D (areaRate F) t ω =
        areaTimeChangedPath F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) t ω := by
  have hwalk : IsReflectedWalk F.graph w hmin (Existence.processFamily D hG w) :=
    canonical_isReflectedWalk_of_rate_le D hG hmin w hw hdom
  have hdy : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      (∀ s : ℝ≥0, dyadicLimit (Existence.processFamily D hG w).X s ω
          = (Existence.processFamily D hG w).X s ω) ∧
        ∀ T : ℝ≥0, sojournNone (Existence.processFamily D hG w).X T ω = 0 :=
    ae_dyadicLimit_eq_and_sojournNone_eq_zero hwalk z
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z, Existence.sampleLaw_ae_start D hG z,
    ae_holdingTimesSummable_of_rateFunction_le D hG w hw hdom z, harea, hdy]
    with ω hc h0 hsw hsa hpath
  obtain ⟨hv, hnull⟩ := hpath
  have hX : Measurable fun r : ℝ =>
      (Existence.processFamily D hG w).X (Real.toNNReal r) ω := by
    have hm' := measurable_section
      (measurable_uncurry_dyadicLimit (Existence.processFamily D hG w).measurable_X) ω
    rw [show (fun r : ℝ => (Existence.processFamily D hG w).X (Real.toNNReal r) ω) =
        fun r : ℝ => dyadicLimit (Existence.processFamily D hG w).X (Real.toNNReal r) ω from
      funext fun r => (hv (Real.toNNReal r)).symm]
    exact hm'
  exact clockGood_and_path_eq_of_sample F hF D hG w hw (h0 0) hc hsw hsa hX hnull

end Sample

/-! ## The environment level: the canonical summable fast rate -/

section Environment

open Code EnvironmentFields QuenchedFormulation ReflectedGMS.InvarianceAssembly
open ReflectedGMS.SpatialExtensionConstruction ReflectedGMS.EnvironmentWalkDataProducer

/-- **Step (b), with the good event.**  Given the environment walk data, almost surely under the
canonical sample law the area clock of the canonical summable fast walk is a good clock, and the
exponential area path is that fast walk read at the canonical inverse area clock, at every
time. -/
theorem ae_clockGood_and_exponentialAreaPath_eq (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (start : Vertex e.val) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ClockGood (decode e) (fastSpeed e D hG)
          (Existence.processFamily D hG (summableFastRate e D hG)) ω ∧
        ∀ t : ℝ≥0, exponentialAreaPath (decode e) D t ω =
          areaTimeChangedPath (decode e) (fastSpeed e D hG)
            (Existence.processFamily D hG (summableFastRate e D hG)) t ω := by
  obtain ⟨hmin, -, -, -⟩ := id hdat
  obtain ⟨hw, hdom, -, -⟩ := summableFastRate_spec e D hG
  exact ae_clockGood_and_path_eq (decode e) (decode_geometry e) D hG hmin
    (summableFastRate e D hG) hw hdom start
    (areaClock_holdingTimesSummable e D hG
      (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
        e D hG hdat) start)

/-- **The `hgood` input of `AreaFastClockStopping.isStoppingTime_fastClock`**, at the canonical
summable fast walk, from the environment walk data alone. -/
theorem ae_clockGood_fastSpeed (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (start : Vertex e.val) :
    ∀ᵐ ω ∂(Existence.processFamily D hG (summableFastRate e D hG)).P start,
      ClockGood (decode e) (fastSpeed e D hG)
        (Existence.processFamily D hG (summableFastRate e D hG)) ω :=
  (ae_clockGood_and_exponentialAreaPath_eq e D hG hdat start).mono fun _ h => h.1

end Environment

end ReflectedGMS.AreaFastClockPath
