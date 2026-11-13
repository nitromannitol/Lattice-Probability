/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedHarmonicAdaptedness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFullEnergyPathL1Limit
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedDynkinFullDomain
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedOccupationCorePairing
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyPotentialPathLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactProcessFiltration
import Mathlib.MeasureTheory.Function.Floor

/-!
# Adaptedness of the full-energy potential path limit

`fullEnergyPotentialPathLimit G m hm PF default U t` is `limUnder atTop` of the
approximants `fullEnergyPotentialApprox … U n t`, each of which is a finite sum of
continuous functions of the compact process `reflectedCompactProcess … t` and of
`reflectedCompactProcess … 0`.  The compact process is strongly adapted to the
right continuation `PF.naturalFiltration.rightCont` of the raw natural filtration
(`stronglyAdapted_reflectedCompactProcess_rightCont`: its defining sample sequence
lives strictly after `t`, which is exactly what `rightCont` absorbs).  Hence every
approximant is `rightCont t`-strongly measurable, and mathlib's
`StronglyMeasurable.limUnder` transfers that index, with no convergence hypothesis,
to the path limit.  This is the adaptedness lemma
`stronglyAdapted_fullEnergyPotentialPathLimit_rightCont`; it needs none of the
walk hypotheses.

The stopped path `stoppedProcess (fullEnergyPotentialPathLimit …) tau s` is **not**
claimed to be exactly `rightCont s`-measurable: the paths are càdlàg only almost
surely, so no progressive measurability is available.  Instead
`aestronglyMeasurable_stoppedProcess_of_ae_isRightContinuous` shows, for any
filtration on `ℝ≥0`, that the stopped value of a strongly adapted process with
a.s. right-continuous paths is a.e. equal to an `F s`-strongly measurable
function: it is the limit of the values at the countably valued right grid
approximations `rightGridTime s k (min s tau)`, each `F s`-measurable.

Combined with the checked set-integral identity
`localHarmonic_stopped_fullEnergyPath_integrable_and_increment_eq_zero` this gives
the conditional-expectation form of the drift elimination in `p:lem:localharm`:
`localHarmonic_stopped_fullEnergyPath_condExp_rightCont_eq`.  The pre-exit
restriction of that identity to the event `B` is replaced by the hypothesis that
the path stays in `A` strictly before `tau` for every `ω` (the case of an exit
time of `A`), so that the identity holds on every `rightCont s`-event.
-/

-- Merged from `ReflectedGMS/Forms/StoppedHarmonicLimitIntegration.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_StoppedHarmonicLimitIntegration

/-!
# The actual stopped locally harmonic path carries no drift

`ReflectedGMS.LocalHarmonicBoundaryBracket.localHarmonic_stopped_corePotential_increment_tendsto_zero`
shows that the stopped **core-potential** increments of the canonical geometric
approximation of a locally harmonic full-domain coordinate `U` vanish in the
limit.  Its `hpotential` input is the actual stopped Dynkin identity
`resolventCore_actualStoppedOccupation_pairing_eq_stoppedPotential`.

This module performs the missing passage to the *actual* path.  Three existing
checked ingredients are combined, and nothing new is assumed:

* the even-index normalization of `fullEnergyPotentialApprox`, so that passing
  to the subsequence `n ↦ 2 * n` matches the approximants of the path limit,
  the two core time-zero values cancelling between times `t` and `s`;
* `stopped_centeredCorePotential_memLp_two`, giving integrability of each
  stopped approximant so the increment integral splits;
* `stopped_fullEnergyPotentialPathLimit_setIntegral_tendsto`, the fixed-start
  stopped `L¹` set-integral convergence to `fullEnergyPotentialPathLimit`.

The conclusion is the actual identity used in `p:lem:localharm`: on a pre-exit
event `B` of the right-continuous natural filtration at time `s`, the stopped
full-energy path of a locally harmonic coordinate has equal expectations at `s`
and at `t`, together with the integrability that makes this statement the
martingale increment identity rather than a formal limit.

No uniform-integrability, no all-time envelope, no area-speed substitution and
no finite-support closure is used: `hmsum : Summable m` is the exact speed
hypothesis inherited from the producers, `U` is an arbitrary element of
`hilbertDomain G m`, `A` may be infinite and `tau` may be infinite.

## Still open downstream

Identification of the ordinary-edge predictable bracket `p:eq:fastPhibracket`
and the exclusion of an extra contribution on the reflection times remain
separate; only the drift elimination is closed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default z : V)
  {B : Set PF.Ω} {tau : PF.Ω → WithTop ℝ≥0}
  (htau : IsStoppingTime PF.naturalFiltration.rightCont tau)
  {s t : ℝ≥0} (hst : s ≤ t)
  (hB : MeasurableSet[PF.naturalFiltration.rightCont s] B)
  (U : hilbertDomain G m) (A : Set V)

include h hG hm hmsum htau

/-- **Cancellation of the core time-zero centering.**

`fullEnergyPotentialApprox … U n` is the core potential of the even index
`fullEnergyCoreIndex G m hm U (2 * n)` centered at time `0`.  Since the centering
is time independent, it disappears from any increment, so the even-index
approximant increments are literally the stopped core-potential increments
appearing in `localHarmonic_stopped_corePotential_increment_tendsto_zero`.  The
integral splits because each stopped approximant is integrable. -/
theorem stopped_fullEnergyPotentialApprox_increment_setIntegral_eq (n : ℕ) :
    (∫ ω in B,
        stoppedProcess (compactResolventCorePotential G m hm PF default
          (fullEnergyCoreIndex G m hm U (2 * n))) tau t ω -
        stoppedProcess (compactResolventCorePotential G m hm PF default
          (fullEnergyCoreIndex G m hm U (2 * n))) tau s ω ∂PF.P z) =
      (∫ ω in B,
        stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau t ω ∂PF.P z) -
      ∫ ω in B,
        stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau s ω ∂PF.P z := by
  have hint : ∀ r : ℝ≥0,
      Integrable (stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau r)
        (PF.P z) := fun r ↦
    (stopped_centeredCorePotential_memLp_two h hG hm hmsum default z htau
      (fullEnergyCoreIndex G m hm U (2 * n)) r).integrable (by norm_num)
  rw [← integral_sub (hint t).integrableOn (hint s).integrableOn]
  apply integral_congr_ae
  filter_upwards [] with ω
  dsimp only [stoppedProcess, fullEnergyPotentialApprox]
  ring

include hst hB

end ReflectedGMS

end Merged_StoppedHarmonicLimitIntegration

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS

/-! ### Countably valued right approximation of a bounded random time -/

/-- Right approximation of a time in `[0, s]` on the grid of mesh `1 / (k + 1)`,
truncated at `s`. It takes countably many values and decreases to its argument. -/
noncomputable def rightGridTime (s : ℝ≥0) (k : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  min s ((⌈r * ((k : ℝ≥0) + 1)⌉₊ : ℝ≥0) / ((k : ℝ≥0) + 1))

theorem le_rightGridTime (s : ℝ≥0) (k : ℕ) {r : ℝ≥0} (hr : r ≤ s) :
    r ≤ rightGridTime s k r := by
  refine le_min hr ?_
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem rightGridTime_le (s : ℝ≥0) (k : ℕ) (r : ℝ≥0) :
    rightGridTime s k r ≤ r + 1 / ((k : ℝ≥0) + 1) := by
  have hk : (0 : ℝ≥0) < (k : ℝ≥0) + 1 := by positivity
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ hk]
  calc ((⌈r * ((k : ℝ≥0) + 1)⌉₊ : ℕ) : ℝ≥0) ≤ r * ((k : ℝ≥0) + 1) + 1 :=
        (Nat.ceil_lt_add_one zero_le).le
    _ = (r + 1 / ((k : ℝ≥0) + 1)) * ((k : ℝ≥0) + 1) := by
        rw [add_mul, div_mul_cancel₀ _ hk.ne']

theorem tendsto_rightGridTime (s : ℝ≥0) {r : ℝ≥0} (hr : r ≤ s) :
    Tendsto (fun k ↦ rightGridTime s k r) atTop (𝓝[≥] r) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ le_rightGridTime s k hr⟩
  rw [← NNReal.tendsto_coe]
  have hupper : Tendsto (fun k : ℕ ↦ (r : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 ((r : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun k ↦ NNReal.coe_le_coe.2 (le_rightGridTime s k hr)) (fun k ↦ ?_)
  have h := NNReal.coe_le_coe.2 (rightGridTime_le s k r)
  push_cast at h
  exact h

section StoppedTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The `[0, s]`-valued random time `min s τ` at which a stopped process is evaluated. -/
noncomputable def stoppedTime (τ : Ω → WithTop ℝ≥0) (s : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (s : WithTop ℝ≥0) (τ ω)).untopA

theorem stoppedProcess_eq_stoppedTime {β : Type*} (u : ℝ≥0 → Ω → β)
    (τ : Ω → WithTop ℝ≥0) (s : ℝ≥0) (ω : Ω) :
    stoppedProcess u τ s ω = u (stoppedTime τ s ω) ω := rfl

theorem stoppedTime_le (τ : Ω → WithTop ℝ≥0) (s : ℝ≥0) (ω : Ω) : stoppedTime τ s ω ≤ s :=
  WithTop.untopA_le (min_le_left _ _)

theorem measurable_stoppedTime {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (s : ℝ≥0) : Measurable[F s] (stoppedTime τ s) := by
  have hmin : Measurable[F s] (fun ω ↦ min (τ ω) (s : WithTop ℝ≥0)) :=
    (hτ.min_const s).measurable_of_le fun ω ↦ min_le_right _ _
  have heq : stoppedTime τ s = fun ω ↦ (min (τ ω) (s : WithTop ℝ≥0)).untopA := by
    funext ω
    simp only [stoppedTime, min_comm]
  rw [heq]
  exact WithTop.measurable_untopA.comp hmin

/-- **Almost-sure adaptedness of a stopped process.** A real process strongly adapted
to a filtration `F` on `ℝ≥0`, with `μ`-almost surely right-continuous paths, has, at every
`F`-stopping time `τ` and deterministic `s`, a stopped value `stoppedProcess Φ τ s` that is
`μ`-a.e. equal to an `F s`-strongly measurable function: it is the pointwise limit of the
values at the countably valued grid approximations of `min s τ` from the right, each of
which is `F s`-measurable. No progressive measurability and no everywhere path regularity
is required. -/
theorem aestronglyMeasurable_stoppedProcess_of_ae_isRightContinuous
    {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {Φ : ℝ≥0 → Ω → ℝ}
    (hΦ : StronglyAdapted F Φ)
    (hrc : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ Φ t ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (s : ℝ≥0) :
    AEStronglyMeasurable[F s] (stoppedProcess Φ τ s) μ := by
  letI : MeasurableSpace Ω := F s
  let g : ℕ → Ω → ℝ := fun k ω ↦ Φ (rightGridTime s k (stoppedTime τ s ω)) ω
  have hg : ∀ k, StronglyMeasurable (g k) := by
    intro k
    have hceil : Measurable (fun ω ↦ ⌈stoppedTime τ s ω * ((k : ℝ≥0) + 1)⌉₊) :=
      Nat.measurable_ceil.comp ((measurable_stoppedTime hτ s).mul_const _)
    have hsec : ∀ j : ℕ,
        Measurable (fun ω ↦ Φ (min s ((j : ℝ≥0) / ((k : ℝ≥0) + 1))) ω) := fun j ↦
      ((hΦ (min s ((j : ℝ≥0) / ((k : ℝ≥0) + 1)))).mono
        (F.mono (min_le_left _ _))).measurable
    have hprod : Measurable
        (fun p : Ω × ℕ ↦ Φ (min s ((p.2 : ℝ≥0) / ((k : ℝ≥0) + 1))) p.1) :=
      measurable_from_prod_countable_left hsec
    exact (hprod.comp (measurable_id.prodMk hceil)).stronglyMeasurable
  refine ⟨fun ω ↦ limUnder atTop (fun k ↦ g k ω), StronglyMeasurable.limUnder hg, ?_⟩
  filter_upwards [hrc] with ω hω
  have hle := stoppedTime_le τ s ω
  have hlim : Tendsto (fun k ↦ g k ω) atTop (𝓝 (Φ (stoppedTime τ s ω) ω)) :=
    (continuousWithinAt_Ioi_iff_Ici.1 (hω (stoppedTime τ s ω))).tendsto.comp
      (tendsto_rightGridTime s hle)
  rw [stoppedProcess_eq_stoppedTime]
  exact hlim.limUnder_eq.symm

end StoppedTime

/-! ### Adaptedness of the full-energy potential path limit -/

open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

section Adaptedness

variable (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
  (PF : ProcessFamily V) (default : V)

/-- Each finite core potential is strongly adapted to the right-continuous natural
filtration, being a finite sum of continuous functions of the adapted compact process. -/
theorem stronglyAdapted_compactResolventCorePotential_rightCont
    (q : CountableResolventCoreIndex V) :
    StronglyAdapted PF.naturalFiltration.rightCont
      (compactResolventCorePotential G m hm PF default q) := by
  classical
  intro t
  letI : MeasurableSpace PF.Ω := PF.naturalFiltration.rightCont t
  have hX : StronglyMeasurable (reflectedCompactProcess G m hm PF default t) :=
    stronglyAdapted_reflectedCompactProcess_rightCont G m hm PF default t
  unfold compactResolventCorePotential Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.stronglyMeasurable_sum
  intro y _
  exact ((ResolventCompactSpace.potentialCoordinate G m hm y).continuous.comp_stronglyMeasurable
    hX).const_smul _

/-- Each centered approximant of the path limit is strongly adapted to the
right-continuous natural filtration (the time-zero centering is `rightCont 0`-measurable). -/
theorem stronglyAdapted_fullEnergyPotentialApprox_rightCont
    (U : hilbertDomain G m) (n : ℕ) :
    StronglyAdapted PF.naturalFiltration.rightCont
      (fullEnergyPotentialApprox G m hm PF default U n) := by
  intro t
  have h0 : StronglyMeasurable[PF.naturalFiltration.rightCont t]
      (compactResolventCorePotential G m hm PF default
        (fullEnergyCoreIndex G m hm U (2 * n)) 0) :=
    (stronglyAdapted_compactResolventCorePotential_rightCont G m hm PF default
      (fullEnergyCoreIndex G m hm U (2 * n)) 0).mono
      (PF.naturalFiltration.rightCont.mono (zero_le : (0 : ℝ≥0) ≤ t))
  have ht := stronglyAdapted_compactResolventCorePotential_rightCont G m hm PF default
    (fullEnergyCoreIndex G m hm U (2 * n)) t
  exact ht.sub h0

/-- **Adaptedness of the full-energy potential path limit.** The locally uniform
limit `fullEnergyPotentialPathLimit` is strongly adapted to the right continuation of
the raw natural filtration of the reflected walk: each approximant is, and
`limUnder` preserves the index without any convergence hypothesis.  No walk
hypothesis is needed. -/
theorem stronglyAdapted_fullEnergyPotentialPathLimit_rightCont (U : hilbertDomain G m) :
    StronglyAdapted PF.naturalFiltration.rightCont
      (fullEnergyPotentialPathLimit G m hm PF default U) := by
  intro t
  letI : MeasurableSpace PF.Ω := PF.naturalFiltration.rightCont t
  unfold fullEnergyPotentialPathLimit
  exact StronglyMeasurable.limUnder fun n ↦
    stronglyAdapted_fullEnergyPotentialApprox_rightCont G m hm PF default U n t

end Adaptedness

/-! ### The stopped path limit and the conditional-expectation drift elimination -/

section Stopped

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default z : V)
  {tau : PF.Ω → WithTop ℝ≥0}
  (htau : IsStoppingTime PF.naturalFiltration.rightCont tau)
  (U : hilbertDomain G m)

include h hG hmsum htau

/-- The stopped full-energy path is, under each starting law, a.e. equal to a
`rightCont s`-strongly measurable function. -/
theorem aestronglyMeasurable_stopped_fullEnergyPotentialPathLimit_rightCont (s : ℝ≥0) :
    AEStronglyMeasurable[PF.naturalFiltration.rightCont s]
      (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) tau s) (PF.P z) := by
  apply aestronglyMeasurable_stoppedProcess_of_ae_isRightContinuous
    (stronglyAdapted_fullEnergyPotentialPathLimit_rightCont G m hm PF default U) _ htau s
  filter_upwards [fullEnergyPotentialPathLimit_ae_cadlag_and_uniform
    h hG hm hmsum default U z] with ω hω
  exact hω.1.isRightContinuous

end Stopped

end ReflectedGMS
