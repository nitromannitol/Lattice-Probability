/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.ConditionalTemporalAveraging at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TemporalMassTransport
import LatticeProb.Bonanno.ReflectedGMS.Limit.ReverseRationalAE
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral

/-! # Conditional temporal averaging over the paper's time blocks

This module formalizes `p:lem:timeconditional` of the manuscript (section
`p:sec:timeblocks`) and the use that `p:lem:timeconverge` makes of it.

The manuscript fixes a covariant family of time blocks `J_m(s)` (the largest
dyadic interval through `s` with `κ(J) ≤ m`), sets

  `A_m = |J_m(0)|⁻¹ ∫_{J_m(0)} F(θ_t Ω) dt`,

and asserts `A_m = 𝔼[F | 𝒢_m]`, where `𝒢_m` is the σ-field of events invariant
under time re-rooting inside the origin block (and under common scaling).  Its
proof applies the temporal mass-transport principle to the single kernel

  `V(Ω, 𝒟, s, t) = |J_m(s)|⁻¹ · 1_{t ∈ J_m(s)} · U(θ_t Ω, 𝒟 - t)`,

whose outgoing integral is the block average of `U` and whose incoming integral
is `U` itself; testing with `U = 1_B F`, `B ∈ 𝒢_m`, gives the conditional
expectation identity.

Everything here follows that proof.

* `TemporalBlockSystem` collects the *pointwise* structure the manuscript
  establishes for `J_m`: it is a partition of the time axis into blocks of
  positive finite length, jointly measurable, and covariant under the time flow
  `θ`.  It does **not** contain any probabilistic assumption.
* `blockTransportReal` is the manuscript kernel `V`; `blockAverageReal` is `A_m`.
* `integral_blockAverageReal` is the manuscript's "averaging `U` over the origin
  block preserves its expectation".  It is obtained from the already proved
  temporal mass transport
  `ReflectedGMS.TemporalMassTransport.integral_integral_timeTransport`; the MTP
  itself is not reproved here.
* `reRootSigma` *constructs* `𝒢_m` as the σ-algebra of measurable sets invariant
  under re-rooting within the origin block, and
  `blockAverageReal_ae_eq_condExp` is `p:eq:timeconditional`.
* `reRootSigma_mono` is the manuscript's nesting clause, and the `Convergence`
  section connects the family to the already checked reverse-martingale limits
  (`ReflectedGMS.ReverseRationalAE.tendsto_condExp_iInf_rat_ae` and
  `ReflectedGMS.MartingaleLimit.tendsto_eLpNorm_one_condExp_iInf`), including the
  statement along the full root dyadic ancestor chain.

Scope kept deliberately explicit:

* `P` is the **rooted probability law** and `F` an **unmarked** integrable
  functional.  This is *not* the σ-finite area-biased mixture that carries the
  temporal mass transport; the mass-transport lemmas used below only need
  `SFinite`, so no finiteness of an area bias is smuggled in.
* Two-sided stationarity of `P` under the time flow appears as the explicit
  hypothesis `∀ r : ℝ, MeasurePreserving (θ r) P P`.  It is supplied by the
  separate area transition-reversibility / two-sided stationary law work and is
  deliberately *not* proved here.
* Nothing below identifies the tail σ-field, and no ergodicity or regenerative
  invariance is claimed.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ReflectedGMS.ConditionalTemporalAveraging

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- **The covariant temporal block system of `p:sec:timeblocks`.**

`θ` is the time flow on configurations and `blk ω s` is the block `J_m(s)` of the
configuration `ω`, for one fixed parameter `m`.  The fields record exactly the
pointwise properties the manuscript establishes for `J_m`: the blocks partition
the time axis, have positive finite length, are jointly measurable, and are
covariant under the flow (`J_m^{θ_r ω}(s) = J_m^ω(s + r) - r`).

No probabilistic hypothesis appears here; the invariance of the law is a
separate hypothesis of the theorems below. -/
structure TemporalBlockSystem (θ : ℝ → Ω → Ω) (blk : Ω → ℝ → Set ℝ) : Prop where
  /-- The flow at time `0` is the identity. -/
  flow_zero : ∀ ω : Ω, θ 0 ω = ω
  /-- The shifts compose. -/
  flow_add : ∀ (a b : ℝ) (ω : Ω), θ a (θ b ω) = θ (a + b) ω
  /-- The flow is jointly measurable. -/
  measurable_flow : Measurable fun p : Ω × ℝ => θ p.2 p.1
  /-- Every time lies in its own block. -/
  self_mem : ∀ (ω : Ω) (s : ℝ), s ∈ blk ω s
  /-- The blocks form a partition of the time axis. -/
  block_eq : ∀ (ω : Ω) (s t : ℝ), t ∈ blk ω s → blk ω t = blk ω s
  /-- Covariance of the blocks under the time flow. -/
  shift : ∀ (ω : Ω) (r s : ℝ), blk (θ r ω) s = {x : ℝ | x + r ∈ blk ω (s + r)}
  /-- The blocks are jointly measurable in the configuration and the time. -/
  measurableSet_graph : MeasurableSet {p : Ω × ℝ × ℝ | p.2.2 ∈ blk p.1 p.2.1}
  /-- Blocks have positive length at almost every time.  This is the manuscript's "defines
  nested covariant partitions for almost every `s`" (singular-set manuscript, Section 17): at a
  nonvertex time where holding intervals accumulate there is no good block, the block is a null
  set and its transport vanishes.  Positivity at the origin time enters the averaging identities
  below as a separate almost-sure hypothesis on the law (`h0`).  (Generalised 2026-09-23 from the
  pointwise `∀ ω s, 0 < volume (blk ω s)`; every earlier producer supplies the pointwise form, see
  `FlowSpaceBlockSystem.volume_pos_gatedBlock`.) -/
  volume_pos_ae : ∀ ω : Ω, ∀ᵐ s ∂volume, 0 < volume (blk ω s)
  /-- Blocks have finite length. -/
  volume_lt_top : ∀ (ω : Ω) (s : ℝ), volume (blk ω s) < ⊤

namespace TemporalBlockSystem

variable {θ : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ}

theorem measurableSet_block (h : TemporalBlockSystem θ blk) (ω : Ω) (s : ℝ) :
    MeasurableSet (blk ω s) := by
  have hmap : Measurable fun t : ℝ => ((ω, s, t) : Ω × ℝ × ℝ) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  exact hmap h.measurableSet_graph

theorem volume_ne_top (h : TemporalBlockSystem θ blk) (ω : Ω) (s : ℝ) :
    volume (blk ω s) ≠ ⊤ := (h.volume_lt_top ω s).ne

/-- The normalising length is positive at a time whose block has positive length. -/
theorem toReal_volume_pos (h : TemporalBlockSystem θ blk) {ω : Ω} {s : ℝ}
    (h0 : 0 < volume (blk ω s)) : 0 < (volume (blk ω s)).toReal :=
  ENNReal.toReal_pos h0.ne' (h.volume_ne_top ω s)

/-- The origin belongs to the block through `s` exactly when `s` belongs to the
origin block.  This is the partition step of the manuscript computation of the
incoming transport. -/
theorem mem_zero_iff (h : TemporalBlockSystem θ blk) (ω : Ω) (s : ℝ) :
    (0 : ℝ) ∈ blk ω s ↔ s ∈ blk ω 0 := by
  constructor
  · intro hs
    rw [h.block_eq ω s 0 hs]
    exact h.self_mem ω s
  · intro hs
    rw [h.block_eq ω 0 s hs]
    exact h.self_mem ω 0

/-- Re-rooting at a time of the origin block translates the origin block. -/
theorem shift_zero_of_mem (h : TemporalBlockSystem θ blk) (ω : Ω) {r : ℝ}
    (hr : r ∈ blk ω 0) : blk (θ r ω) 0 = (fun x : ℝ => x + r) ⁻¹' blk ω 0 := by
  have h1 := h.shift ω r 0
  rw [zero_add] at h1
  rw [h1, h.block_eq ω 0 r hr]
  rfl

/-! ### The manuscript transport kernel and the block average -/

end TemporalBlockSystem

/-- The average of `F ∘ θ` over a time set, `|S|⁻¹ ∫_S F(θ_t ω) dt`. -/
noncomputable def setAverageReal (θ : ℝ → Ω → Ω) (S : Set ℝ) (F : Ω → ℝ) (ω : Ω) : ℝ :=
  (volume S).toReal⁻¹ * ∫ t in S, F (θ t ω)

/-- **The average `A_m` of `p:eq:timeconditional`**: the average of `F` along the
flow over the origin block. -/
noncomputable def blockAverageReal (θ : ℝ → Ω → Ω) (blk : Ω → ℝ → Set ℝ) (F : Ω → ℝ)
    (ω : Ω) : ℝ :=
  setAverageReal θ (blk ω 0) F ω

/-- **The transport kernel `V` of the proof of `p:lem:timeconditional`**,
`V(ω, s, t) = |J_m(s)|⁻¹ 1_{t ∈ J_m(s)} F(θ_t ω)`. -/
noncomputable def blockTransportReal (θ : ℝ → Ω → Ω) (blk : Ω → ℝ → Set ℝ) (F : Ω → ℝ)
    (ω : Ω) (s t : ℝ) : ℝ :=
  (volume (blk ω s)).toReal⁻¹ * (blk ω s).indicator (fun u : ℝ => F (θ u ω)) t

namespace TemporalBlockSystem

variable {θ : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ}

/-- The block length is jointly measurable. -/
theorem measurable_blockVolume (h : TemporalBlockSystem θ blk) :
    Measurable fun q : Ω × ℝ => volume (blk q.1 q.2) := by
  have hmap : Measurable fun p : (Ω × ℝ) × ℝ => ((p.1.1, p.1.2, p.2) : Ω × ℝ × ℝ) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hgraph : MeasurableSet {p : (Ω × ℝ) × ℝ | p.2 ∈ blk p.1.1 p.1.2} :=
    hmap h.measurableSet_graph
  have hind : Measurable
      (Set.indicator {p : (Ω × ℝ) × ℝ | p.2 ∈ blk p.1.1 p.1.2} (1 : (Ω × ℝ) × ℝ → ℝ≥0∞)) :=
    measurable_one.indicator hgraph
  have hlint : Measurable fun q : Ω × ℝ =>
      ∫⁻ t : ℝ, Set.indicator {p : (Ω × ℝ) × ℝ | p.2 ∈ blk p.1.1 p.1.2}
        (1 : (Ω × ℝ) × ℝ → ℝ≥0∞) (q, t) := hind.lintegral_prod_right'
  have hEq : (fun q : Ω × ℝ => volume (blk q.1 q.2))
      = fun q : Ω × ℝ => ∫⁻ t : ℝ, Set.indicator {p : (Ω × ℝ) × ℝ | p.2 ∈ blk p.1.1 p.1.2}
        (1 : (Ω × ℝ) × ℝ → ℝ≥0∞) (q, t) := by
    funext q
    have hsimp : (fun t : ℝ => Set.indicator {p : (Ω × ℝ) × ℝ | p.2 ∈ blk p.1.1 p.1.2}
        (1 : (Ω × ℝ) × ℝ → ℝ≥0∞) (q, t)) = (blk q.1 q.2).indicator (1 : ℝ → ℝ≥0∞) := by
      funext t
      by_cases ht : t ∈ blk q.1 q.2
      · rw [Set.indicator_of_mem (show ((q, t) : (Ω × ℝ) × ℝ) ∈
          {p : (Ω × ℝ) × ℝ | p.2 ∈ blk p.1.1 p.1.2} from ht), Set.indicator_of_mem ht,
          Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem (show ((q, t) : (Ω × ℝ) × ℝ) ∉
          {p : (Ω × ℝ) × ℝ | p.2 ∈ blk p.1.1 p.1.2} from ht), Set.indicator_of_notMem ht]
    rw [hsimp]
    exact (lintegral_indicator_one (h.measurableSet_block q.1 q.2)).symm
  rw [hEq]
  exact hlint

/-- The normalizing factor of the block average is jointly measurable. -/
theorem measurable_invBlockVolume (h : TemporalBlockSystem θ blk) :
    Measurable fun q : Ω × ℝ => (volume (blk q.1 q.2)).toReal⁻¹ := by
  have hrw : (fun q : Ω × ℝ => (volume (blk q.1 q.2)).toReal⁻¹)
      = fun q : Ω × ℝ => ((volume (blk q.1 q.2))⁻¹).toReal := by
    funext q
    rw [ENNReal.toReal_inv]
  rw [hrw]
  exact h.measurable_blockVolume.inv.ennreal_toReal

theorem measurable_flow_apply (h : TemporalBlockSystem θ blk) {F : Ω → ℝ} (hF : Measurable F) :
    Measurable fun p : Ω × ℝ × ℝ => F (θ p.2.2 p.1) :=
  hF.comp (h.measurable_flow.comp (measurable_fst.prodMk measurable_snd.snd))

/-- The manuscript transport kernel is jointly measurable. -/
theorem measurable_blockTransportReal (h : TemporalBlockSystem θ blk) {F : Ω → ℝ}
    (hF : Measurable F) :
    Measurable fun p : Ω × ℝ × ℝ => blockTransportReal θ blk F p.1 p.2.1 p.2.2 := by
  have hfac : Measurable fun p : Ω × ℝ × ℝ => (volume (blk p.1 p.2.1)).toReal⁻¹ :=
    h.measurable_invBlockVolume.comp (measurable_fst.prodMk measurable_snd.fst)
  have hind : Measurable fun p : Ω × ℝ × ℝ =>
      (blk p.1 p.2.1).indicator (fun u : ℝ => F (θ u p.1)) p.2.2 := by
    have hgen : Measurable (Set.indicator {p : Ω × ℝ × ℝ | p.2.2 ∈ blk p.1 p.2.1}
        (fun p : Ω × ℝ × ℝ => F (θ p.2.2 p.1))) :=
      (h.measurable_flow_apply hF).indicator h.measurableSet_graph
    have hEq : (fun p : Ω × ℝ × ℝ => (blk p.1 p.2.1).indicator (fun u : ℝ => F (θ u p.1)) p.2.2)
        = Set.indicator {p : Ω × ℝ × ℝ | p.2.2 ∈ blk p.1 p.2.1}
          (fun p : Ω × ℝ × ℝ => F (θ p.2.2 p.1)) := by
      funext p
      by_cases hp : p.2.2 ∈ blk p.1 p.2.1
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p ∈ {p : Ω × ℝ × ℝ | p.2.2 ∈ blk p.1 p.2.1} from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p ∉ {p : Ω × ℝ × ℝ | p.2.2 ∈ blk p.1 p.2.1} from hp)]
    rw [hEq]
    exact hgen
  exact hfac.mul hind

/-- **Covariance of the manuscript transport kernel.**  This is the hypothesis of
the temporal mass-transport principle, verified for the specific kernel `V` of
the proof of `p:lem:timeconditional`. -/
theorem timeShiftCovariant_blockTransportReal (h : TemporalBlockSystem θ blk) (F : Ω → ℝ) :
    TemporalMassTransport.TimeShiftCovariant θ (blockTransportReal θ blk F) := by
  intro r s t ω
  have harith : s - r + r = s := by ring
  have hset : blk (θ r ω) (s - r) = (fun x : ℝ => x + r) ⁻¹' blk ω s := by
    have h1 := h.shift ω r (s - r)
    rw [harith] at h1
    rw [h1]
    rfl
  have hvol : volume (blk (θ r ω) (s - r)) = volume (blk ω s) := by
    rw [hset]
    exact measure_preimage_add_right volume r _
  simp only [blockTransportReal]
  rw [hvol, hset]
  congr 1
  by_cases hmem : t - r ∈ (fun x : ℝ => x + r) ⁻¹' blk ω s
  · have hmem' : t ∈ blk ω s := by
      have : t - r + r ∈ blk ω s := hmem
      rwa [sub_add_cancel] at this
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', h.flow_add (t - r) r ω,
      sub_add_cancel]
  · have hmem' : t ∉ blk ω s := by
      intro hc
      exact hmem (by
        show t - r + r ∈ blk ω s
        rwa [sub_add_cancel])
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']

/-! ### Outgoing and incoming transports -/

/-- **The outgoing transport is the block average**, the first half of the
manuscript's block-partition identity. -/
theorem integral_blockTransportReal_outgoing (h : TemporalBlockSystem θ blk) (F : Ω → ℝ)
    (ω : Ω) :
    ∫ t : ℝ, blockTransportReal θ blk F ω 0 t = blockAverageReal θ blk F ω := by
  simp only [blockTransportReal, blockAverageReal, setAverageReal]
  rw [integral_const_mul, integral_indicator (h.measurableSet_block ω 0)]

/-- Pointwise form of the incoming transport: it is an indicator of the origin
block, by the partition identity `0 ∈ J_m(s) ↔ s ∈ J_m(0)`. -/
theorem blockTransportReal_incoming (h : TemporalBlockSystem θ blk) (F : Ω → ℝ) (ω : Ω)
    (s : ℝ) :
    blockTransportReal θ blk F ω s 0 =
      (blk ω 0).indicator (fun _ : ℝ => (volume (blk ω 0)).toReal⁻¹ * F ω) s := by
  simp only [blockTransportReal]
  by_cases hs : s ∈ blk ω 0
  · have hb : blk ω s = blk ω 0 := h.block_eq ω 0 s hs
    rw [Set.indicator_of_mem hs, hb, Set.indicator_of_mem (h.self_mem ω 0), h.flow_zero]
  · have hs0 : (0 : ℝ) ∉ blk ω s := fun hc => hs ((h.mem_zero_iff ω s).1 hc)
    rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs0, mul_zero]

/-- **The incoming transport integrates to `F`**, the second half of the
manuscript's block-partition identity, at every configuration whose origin block has positive
length. -/
theorem integral_blockTransportReal_incoming (h : TemporalBlockSystem θ blk) (F : Ω → ℝ)
    (ω : Ω) (h0 : 0 < volume (blk ω 0)) :
    ∫ s : ℝ, blockTransportReal θ blk F ω s 0 = F ω := by
  simp only [h.blockTransportReal_incoming F ω]
  rw [integral_indicator (h.measurableSet_block ω 0), setIntegral_const, smul_eq_mul,
    measureReal_def, ← mul_assoc, mul_inv_cancel₀ (h.toReal_volume_pos h0).ne', one_mul]

/-- The norm of the incoming transport is the incoming transport of `‖F‖`. -/
theorem norm_blockTransportReal_incoming (h : TemporalBlockSystem θ blk) (F : Ω → ℝ) (ω : Ω)
    (s : ℝ) :
    ‖blockTransportReal θ blk F ω s 0‖ =
      blockTransportReal θ blk (fun x => ‖F x‖) ω s 0 := by
  rw [h.blockTransportReal_incoming F ω s, h.blockTransportReal_incoming (fun x => ‖F x‖) ω s]
  by_cases hs : s ∈ blk ω 0
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, norm_mul,
      Real.norm_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]

/-- The incoming transport of `‖F‖` integrates to at most `‖F ω‖` (to exactly `‖F ω‖` when the
origin block has positive length, to `0` otherwise). -/
theorem integral_norm_blockTransportReal_incoming_le (h : TemporalBlockSystem θ blk) (F : Ω → ℝ)
    (ω : Ω) : ∫ s : ℝ, ‖blockTransportReal θ blk F ω s 0‖ ≤ ‖F ω‖ := by
  have hpt : (fun s : ℝ => ‖blockTransportReal θ blk F ω s 0‖)
      = fun s : ℝ => blockTransportReal θ blk (fun x => ‖F x‖) ω s 0 := by
    funext s
    exact h.norm_blockTransportReal_incoming F ω s
  rw [hpt]
  simp only [h.blockTransportReal_incoming (fun x => ‖F x‖) ω]
  rw [integral_indicator (h.measurableSet_block ω 0), setIntegral_const, smul_eq_mul,
    measureReal_def, ← mul_assoc]
  by_cases hv : (volume (blk ω 0)).toReal = 0
  · rw [hv, zero_mul, zero_mul]
    exact norm_nonneg _
  · rw [mul_inv_cancel₀ hv, one_mul]

/-! ### The averaging identity, from the temporal mass transport -/

section Law

variable {P : Measure Ω} {F : Ω → ℝ}

/-- The incoming transport is integrable on the product: it is an explicit
indicator of a block of finite length, of total mass `‖F ω‖`. -/
theorem integrable_blockTransportReal_incoming [SFinite P] (h : TemporalBlockSystem θ blk)
    (hFm : Measurable F) (hF : Integrable F P) :
    Integrable (fun p : Ω × ℝ => blockTransportReal θ blk F p.1 p.2 0) (P.prod volume) := by
  have hmeas : Measurable fun p : Ω × ℝ => blockTransportReal θ blk F p.1 p.2 0 :=
    (h.measurable_blockTransportReal hFm).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨Eventually.of_forall ?_, ?_⟩
  · intro ω
    have hfin : volume (blk ω 0) ≠ ⊤ := h.volume_ne_top ω 0
    have : Integrable ((blk ω 0).indicator
        (fun _ : ℝ => (volume (blk ω 0)).toReal⁻¹ * F ω)) volume :=
      (integrable_indicator_iff (h.measurableSet_block ω 0)).2 (integrableOn_const hfin)
    refine this.congr ?_
    filter_upwards with s
    exact (h.blockTransportReal_incoming F ω s).symm
  · have hsm : StronglyMeasurable fun ω : Ω => ∫ s : ℝ, ‖blockTransportReal θ blk F ω s 0‖ :=
      hmeas.norm.stronglyMeasurable.integral_prod_right'
    refine hF.norm.mono' hsm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun s => norm_nonneg _)]
    exact h.integral_norm_blockTransportReal_incoming_le F ω

end Law

/-! ### Invariance of the block average under re-rooting -/

/-- **The block average is invariant under re-rooting inside the origin block.**
This is the manuscript's "`A_m` is invariant under re-rooting within that same
block". -/
theorem blockAverageReal_shift (h : TemporalBlockSystem θ blk) (F : Ω → ℝ) (ω : Ω) {r : ℝ}
    (hr : r ∈ blk ω 0) :
    blockAverageReal θ blk F (θ r ω) = blockAverageReal θ blk F ω := by
  have hset := h.shift_zero_of_mem ω hr
  have hvol : volume (blk (θ r ω) 0) = volume (blk ω 0) := by
    rw [hset]
    exact measure_preimage_add_right volume r _
  simp only [blockAverageReal, setAverageReal, hvol]
  congr 1
  rw [← integral_indicator (h.measurableSet_block (θ r ω) 0),
    ← integral_indicator (h.measurableSet_block ω 0)]
  have hfun : (fun t : ℝ => (blk (θ r ω) 0).indicator (fun u : ℝ => F (θ u (θ r ω))) t)
      = fun t : ℝ => (blk ω 0).indicator (fun u : ℝ => F (θ u ω)) (t + r) := by
    funext t
    by_cases ht : t ∈ blk (θ r ω) 0
    · have ht' : t + r ∈ blk ω 0 := by
        rw [hset] at ht
        exact ht
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht', h.flow_add t r ω]
    · have ht' : t + r ∉ blk ω 0 := by
        rw [hset] at ht
        exact ht
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  rw [hfun]
  exact integral_add_right_eq_self (fun u : ℝ => (blk ω 0).indicator
    (fun v : ℝ => F (θ v ω)) u) r

/-- The block average is measurable for the ambient σ-field. -/
theorem measurable_blockAverageReal (h : TemporalBlockSystem θ blk) {F : Ω → ℝ}
    (hF : Measurable F) : Measurable (blockAverageReal θ blk F) := by
  have hfac : Measurable fun ω : Ω => (volume (blk ω 0)).toReal⁻¹ :=
    h.measurable_invBlockVolume.comp (measurable_id.prodMk measurable_const)
  have hmap : Measurable fun p : Ω × ℝ => ((p.1, 0, p.2) : Ω × ℝ × ℝ) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ blk p.1 0} := hmap h.measurableSet_graph
  have hbody : Measurable fun p : Ω × ℝ => F (θ p.2 p.1) :=
    hF.comp h.measurable_flow
  have hind : Measurable fun p : Ω × ℝ =>
      (blk p.1 0).indicator (fun u : ℝ => F (θ u p.1)) p.2 := by
    have hgen : Measurable (Set.indicator {p : Ω × ℝ | p.2 ∈ blk p.1 0}
        (fun p : Ω × ℝ => F (θ p.2 p.1))) := hbody.indicator hgraph
    have hEq : (fun p : Ω × ℝ => (blk p.1 0).indicator (fun u : ℝ => F (θ u p.1)) p.2)
        = Set.indicator {p : Ω × ℝ | p.2 ∈ blk p.1 0} (fun p : Ω × ℝ => F (θ p.2 p.1)) := by
      funext p
      by_cases hp : p.2 ∈ blk p.1 0
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p ∈ {p : Ω × ℝ | p.2 ∈ blk p.1 0} from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p ∉ {p : Ω × ℝ | p.2 ∈ blk p.1 0} from hp)]
    rw [hEq]
    exact hgen
  have hint : Measurable fun ω : Ω =>
      ∫ t : ℝ, (blk ω 0).indicator (fun u : ℝ => F (θ u ω)) t := by
    have := (hind.stronglyMeasurable).integral_prod_right' (ν := (volume : Measure ℝ))
    exact this.measurable
  have hrw : blockAverageReal θ blk F = fun ω : Ω => (volume (blk ω 0)).toReal⁻¹ *
      ∫ t : ℝ, (blk ω 0).indicator (fun u : ℝ => F (θ u ω)) t := by
    funext ω
    simp only [blockAverageReal, setAverageReal]
    rw [integral_indicator (h.measurableSet_block ω 0)]
  rw [hrw]
  exact hfac.mul hint

end TemporalBlockSystem

/-! ### The re-rooting sigma-field `𝒢_m` -/

namespace TemporalBlockSystem

variable {θ : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ}

/-- Testing the block average with an indicator of a re-rooting invariant event:
this is the manuscript's step "test the expectation identity with `U = 1_B F`". -/
theorem blockAverageReal_indicator (h : TemporalBlockSystem θ blk) (F : Ω → ℝ) {B : Set Ω}
    (hB : ∀ ω : Ω, ∀ t ∈ blk ω 0, (θ t ω ∈ B ↔ ω ∈ B)) (ω : Ω) :
    blockAverageReal θ blk (B.indicator F) ω = B.indicator (blockAverageReal θ blk F) ω := by
  by_cases hω : ω ∈ B
  · rw [Set.indicator_of_mem hω]
    simp only [blockAverageReal, setAverageReal]
    congr 1
    refine setIntegral_congr_fun (h.measurableSet_block ω 0) ?_
    intro t ht
    exact Set.indicator_of_mem ((hB ω t ht).2 hω) F
  · rw [Set.indicator_of_notMem hω]
    simp only [blockAverageReal, setAverageReal]
    have hzero : Set.EqOn (fun t : ℝ => B.indicator F (θ t ω)) (fun _ : ℝ => (0 : ℝ))
        (blk ω 0) := by
      intro t ht
      exact Set.indicator_of_notMem (fun hc => hω ((hB ω t ht).1 hc)) F
    rw [setIntegral_congr_fun (h.measurableSet_block ω 0) hzero, integral_zero, mul_zero]

section Law

variable {P : Measure Ω} {F : Ω → ℝ}

end Law

end TemporalBlockSystem

/-! ## The complete dyadic chain: `p:lem:timeconverge`

The averages along the manuscript's rational parameter family are the
conditional expectations of the decreasing family `𝒢_m`, so the already checked
reverse-martingale limits apply verbatim. -/

section Convergence

variable {θ : ℝ → Ω → Ω} {blkFam : ℚ → Ω → ℝ → Set ℝ} {P : Measure Ω} {F : Ω → ℝ}

end Convergence

end ReflectedGMS.ConditionalTemporalAveraging
