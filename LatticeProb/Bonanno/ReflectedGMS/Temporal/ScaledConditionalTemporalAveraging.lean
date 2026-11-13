/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.ScaledConditionalTemporalAveraging at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ParabolicTemporalTransport
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ConditionalTemporalAveraging

/-!
# Conditional temporal averaging from the degree `-2` transport (the manuscript's version)

`ReflectedGMS/Temporal/ConditionalTemporalAveraging.lean` proves `p:lem:timeconditional` and
the convergence clauses of `p:lem:timeconverge` from **full stationarity**
`hθP : ∀ r, MeasurePreserving (θ r) P P` of the rooted law, for **every** integrable
functional `F`, with the σ-field `reRootSigma` of events invariant under re-rooting inside the
origin block.

The manuscript is weaker on both counts (tex:1440-1487).  `p:lem:timeconditional` is stated
"for an integrable unmarked functional `F(Ω)` invariant under `S_C`", its σ-field `𝒢_m` is
"the completed sigma-field of events invariant under common parabolic scaling and under time
re-rooting within the origin block", and the only probabilistic input of its proof is the
temporal mass transport `p:lem:timeMTP` applied to the kernel
`V(Ω,𝒟,s,t) = |J_m(s)|⁻¹ 1_{t ∈ J_m(s)} U(θ_t Ω, 𝒟 − t)` with `U` scale invariant — a kernel
of parabolic degree `-2`.  No stationarity of the annealed law under a fixed shift is used.

This module redoes the averaging lemma **exactly as the manuscript does**: the hypothesis is
`ParabolicTransport.ParabolicTemporalTransport P θ S` (the conclusion of `p:lem:timeMTP`), the
block system is parabolically covariant (`ScaleCovariantBlocks`), the flow intertwines with
the scaling (`FlowScaleIntertwine`), the functional is scale invariant (`ScaleInvariant`), and
the σ-field is `reRootScaleSigma`, which adds invariance under every `S_C` to `reRootSigma`.

## What is proved

* `parabolicCovariantReal_blockTransportReal` — the manuscript kernel `V` has degree `-2`
  when the blocks are parabolically covariant and `F` is scale invariant: the block length
  contributes `C²`, the indicator and `F ∘ θ` are unchanged.
* `blockAverageReal_scale` — `A_m` is invariant under `S_C` ("scaling leaves the averages
  unchanged", tex:1486), by the change of variables `t ↦ C²t` in the outgoing transport.
* `reRootScaleSigma` — the manuscript's `𝒢_m`, constructed as a σ-algebra; it is coarser than
  `reRootSigma` (`reRootScaleSigma_le_reRootSigma`) and antitone in the blocks.
* `integral_blockAverageReal_of_transport` — "averaging `U` over the origin block preserves
  its expectation", from the degree `-2` transport applied to `V`.
* `blockAverageReal_ae_eq_condExp_of_transport` — `p:eq:timeconditional`,
  `A_m = 𝔼[F ∣ 𝒢_m]`, for scale-invariant `F`.
* `tendsto_blockAverageReal_ae_of_transport`, `tendsto_eLpNorm_one_blockAverageReal_of_transport`,
  `tendsto_setAverageReal_chain_ae_of_transport` — the almost-sure, `L¹` and full-root-chain
  clauses of `p:lem:timeconverge`, with the limit `𝔼[F ∣ ⋂_m 𝒢_m]`.

Every theorem is the corresponding theorem of `ConditionalTemporalAveraging` with `hθP`
replaced by the transport predicate and the parabolic data, and `reRootSigma` replaced by
`reRootScaleSigma`.  The deterministic block machinery (`TemporalBlockSystem`, the kernel, its
measurability and time-shift covariance, the partition identity) is reused, not reproved.

Nothing here certifies `p:lem:timeMTP`, `p:lem:regeninvariant`, `p:prop:timeergodic`,
`p:lem:bracketlimit`, `p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ReflectedGMS.ScaledConditionalTemporalAveraging

open ReflectedGMS.ConditionalTemporalAveraging ReflectedGMS.TemporalMassTransport
open ReflectedGMS.ParabolicTransport

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-! ### The parabolic data -/

/-- **The flow and the scaling intertwine parabolically**: `θ_{C²t} ∘ S_C = S_C ∘ θ_t`, which
is the manuscript's `S_C Ω = (C𝓗, (C X_{t/C²})_t)`. -/
def FlowScaleIntertwine (θ S : ℝ → Ω → Ω) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ (t : ℝ) (ω : Ω), θ (C ^ 2 * t) (S C ω) = S C (θ t ω)

/-- A functional invariant under the parabolic scaling. -/
def ScaleInvariant (S : ℝ → Ω → Ω) (F : Ω → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ω : Ω, F (S C ω) = F ω

omit m0 in
theorem scaleInvariant_indicator {S : ℝ → Ω → Ω} {F : Ω → ℝ} (hF : ScaleInvariant S F)
    {B : Set Ω} (hB : ∀ C : ℝ, 0 < C → ∀ ω : Ω, (S C ω ∈ B ↔ ω ∈ B)) :
    ScaleInvariant S (B.indicator F) := by
  intro C hC ω
  by_cases hω : ω ∈ B
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem ((hB C hC ω).2 hω), hF C hC ω]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem fun h => hω ((hB C hC ω).1 h)]

/-! ### Dilated sets on the time axis -/

theorem mul_mem_image_mul_iff {C : ℝ} (hC : C ≠ 0) (B : Set ℝ) (t : ℝ) :
    C * t ∈ (fun x : ℝ => C * x) '' B ↔ t ∈ B :=
  (mul_right_injective₀ hC).mem_set_image

theorem volume_image_mul {C : ℝ} (hC : 0 < C) (B : Set ℝ) :
    volume ((fun x : ℝ => C * x) '' B) = ENNReal.ofReal C * volume B := by
  have himg : (fun x : ℝ => C * x) '' B = (fun x : ℝ => C⁻¹ * x) ⁻¹' B :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun x : ℝ => C * x)
      (g := fun x : ℝ => C⁻¹ * x) (fun x => inv_mul_cancel_left₀ hC.ne' x)
      (fun x => mul_inv_cancel_left₀ hC.ne' x)) B
  rw [himg, Real.volume_preimage_mul_left (inv_ne_zero hC.ne'), inv_inv, abs_of_pos hC]

/-! ### The manuscript kernel has degree `-2` -/

section Kernel

variable {θ S : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ}

end Kernel

/-! ### The re-rooting and scaling σ-field `𝒢_m` -/

/-- **The manuscript's `𝒢_m`**: the measurable events invariant under time re-rooting inside
the origin block *and* under every parabolic scaling `S_C`.  Constructed, not postulated. -/
def reRootScaleSigma (θ S : ℝ → Ω → Ω) (blk : Ω → ℝ → Set ℝ) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet s ∧ (∀ ω : Ω, ∀ t ∈ blk ω 0, (θ t ω ∈ s ↔ ω ∈ s)) ∧
    (∀ C : ℝ, 0 < C → ∀ ω : Ω, (S C ω ∈ s ↔ ω ∈ s))
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl s hs :=
    ⟨hs.1.compl, fun ω t ht => not_congr (hs.2.1 ω t ht), fun C hC ω => not_congr (hs.2.2 C hC ω)⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion fun i => (hf i).1, fun ω t ht => by
      simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2.1 ω t ht, fun C hC ω => by
      simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2.2 C hC ω⟩

theorem reRootScaleSigma_le (θ S : ℝ → Ω → Ω) (blk : Ω → ℝ → Set ℝ) :
    reRootScaleSigma θ S blk ≤ m0 := fun _ hs => hs.1

/-- Larger blocks give a smaller σ-field. -/
theorem reRootScaleSigma_mono {θ S : ℝ → Ω → Ω} {blk blk' : Ω → ℝ → Set ℝ}
    (hsub : ∀ ω : Ω, blk ω 0 ⊆ blk' ω 0) :
    reRootScaleSigma θ S blk' ≤ reRootScaleSigma θ S blk :=
  fun _ hs => ⟨hs.1, fun ω t ht => hs.2.1 ω t (hsub ω ht), hs.2.2⟩

/-- A measurable function invariant under re-rooting and scaling is `𝒢_m`-measurable. -/
theorem measurable_reRootScaleSigma_of_invariant {θ S : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ}
    {α : Type*} [MeasurableSpace α] {f : Ω → α} (hf : Measurable f)
    (hinv : ∀ ω : Ω, ∀ t ∈ blk ω 0, f (θ t ω) = f ω)
    (hscale : ∀ C : ℝ, 0 < C → ∀ ω : Ω, f (S C ω) = f ω) :
    Measurable[reRootScaleSigma θ S blk] f := by
  intro T hT
  refine ⟨hf hT, fun ω t ht => ?_, fun C hC ω => ?_⟩
  · show f (θ t ω) ∈ T ↔ f ω ∈ T
    rw [hinv ω t ht]
  · show f (S C ω) ∈ T ↔ f ω ∈ T
    rw [hscale C hC ω]

section Averaging

variable {θ S : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ}

section Law

variable {P : Measure Ω} {F : Ω → ℝ}

end Law

end Averaging

/-! ## The complete dyadic chain: `p:lem:timeconverge` for scale-invariant functionals -/

section Convergence

variable {θ S : ℝ → Ω → Ω} {blkFam : ℚ → Ω → ℝ → Set ℝ} {P : Measure Ω} {F : Ω → ℝ}

/-- The manuscript's decreasing family `𝒢_m`, `m` rational. -/
theorem antitone_reRootScaleSigma
    (hmono : ∀ q q' : ℚ, q ≤ q' → ∀ ω : Ω, blkFam q ω 0 ⊆ blkFam q' ω 0) :
    Antitone fun q : ℚ => reRootScaleSigma θ S (blkFam q) :=
  fun _ _ hqq' => reRootScaleSigma_mono (hmono _ _ hqq')

end Convergence

end ReflectedGMS.ScaledConditionalTemporalAveraging
