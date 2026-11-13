/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedFormAssociationFastStopped at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedHarmonicAdaptedness
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationExitTime
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationCompletedMartingale
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedAdaptedness
import LatticeProb.Bonanno.ReflectedGMS.Limit.CommonSquareLocalizer

/-!
# The stopped locally harmonic fast path is a martingale of the completed fast filtration

**Fast-side association on the stopped process.**  This is the drift-elimination clause of
`p:lem:localharm`, packaged as an honest `Martingale` for the *actual spatial exit time* of a
(possibly infinite) vertex region `A`, on the completed natural filtration of the
summable-speed fast walk.

The fast-side producers (`Forms/LocalHarmonicBoundaryBracket`,
`Forms/StoppedHarmonicLimitIntegration`, `Forms/StoppedHarmonicAdaptedness`) need an
**exact** stopping time of the right continuation of the raw natural filtration and a
pre-exit hypothesis holding at **every** sample.  The actual exit time
`exitHitting PF A = hittingAfter PF.X (some '' Aᶜ) 0` satisfies the second requirement for
every sample (`StoppedFormAssociationExitTime.mem_of_lt_exitHitting`) but is a stopping time
only up to null sets, while its dyadic version `dyadicExit PF A` is an exact stopping time
but violates the pre-exit condition on a null set.  The two are almost surely equal, and the
pre-exit condition enters the producers only through the support of the expected stopped
occupation density, which does not see null sets.  So the chain is re-derived here with the
support statement `actualStoppedOccupationDensity … = 0` off `A` in place of the pointwise
pre-exit hypothesis (`actualStoppedOccupationDensity_dyadicExit_eq_zero_off`), for the
exact dyadic exit; the completed-filtration transfer
`StoppedFormAssociationCompletedMartingale` then gives the `Martingale` structure, and the
almost-sure equality of the two exit times moves it to the actual exit time.

Main results, for `U : hilbertDomain G m` with the full spatial variational harmonicity
`hU` on `A` (the `hilbertDomain` form of clause H5c consumed by
`Forms/LocalHarmonicBoundaryBracket`):

* `stopped_fullEnergyPath_integrable_and_increment_eq_zero_dyadicExit` — the raw
  set-integral increment identity for the exact dyadic exit;
* `martingale_stopped_fullEnergyPath_exit_completed` — the stopped full-energy potential
  path, stopped at the actual exit time of `A`, is a `Martingale` of the completed natural
  filtration of the (injectively encoded) fast path under the completed starting law;
* `isStoppingTime_completed_exitHitting` — the actual exit time is an exact stopping time of
  that completed filtration.

The speed `m` here is the **fast** speed of `p:lem:localharm`, summable by construction
(`Process/SpatialExtensionEnvironment.fastSpeed`, `summableFastRate_spec`); the area speed
never appears.  Nothing here concerns the area clock: the transfer to the area-clock
filtration is the clock change of `StoppedFormAssociationOptionalSampling`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace ReflectedGMS.StoppedFormAssociation

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## The two exit times -/

/-- The spatial exit time of the vertex region `A`: the first time at a vertex outside `A`.
Reflection times inside `A` do not stop it. -/
noncomputable def exitHitting (PF : ProcessFamily V) (A : Set V) (ω : PF.Ω) : WithTop ℝ≥0 :=
  hittingAfter PF.X (some '' Aᶜ) 0 ω

/-- The dyadic version of the exit time: an exact stopping time of the right-continuous raw
natural filtration. -/
noncomputable def dyadicExit (PF : ProcessFamily V) (A : Set V) (ω : PF.Ω) : WithTop ℝ≥0 :=
  dyadicHitting PF.X (some '' Aᶜ) ω

theorem isStoppingTime_rightCont_dyadicExit (PF : ProcessFamily V) (A : Set V) :
    IsStoppingTime PF.naturalFiltration.rightCont (dyadicExit PF A) :=
  isStoppingTime_rightCont_dyadicHitting PF.X PF.measurable_X _

theorem ae_dyadicExit_eq_exitHitting {G : ConductanceGraph V} {w : V → ℝ}
    {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}
    (h : IsReflectedWalk G w hmin PF) (A : Set V) (z : V) :
    ∀ᵐ ω ∂PF.P z, dyadicExit PF A ω = exitHitting PF A ω :=
  ae_dyadicHitting_eq_hittingAfter h z (none_notMem_some_image Aᶜ)

/-- A stopping time of a filtration containing the null events may be modified on a null
set. -/
theorem isStoppingTime_of_ae_eq_of_null_events {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {P : Measure Ω'} {F : Filtration ℝ≥0 m'} {τ τ' : Ω' → WithTop ℝ≥0}
    (hτ' : IsStoppingTime F τ')
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω'), P A = 0 → MeasurableSet[F t] A)
    (heq : ∀ᵐ ω ∂P, τ ω = τ' ω) : IsStoppingTime F τ := by
  intro t
  let N : Set Ω' := {ω | ¬ τ ω = τ' ω}
  have hN : P N = 0 := ae_iff.1 heq
  have hdecomp : {ω | τ ω ≤ (t : WithTop ℝ≥0)} =
      ({ω | τ' ω ≤ (t : WithTop ℝ≥0)} ∩ Nᶜ) ∪ ({ω | τ ω ≤ (t : WithTop ℝ≥0)} ∩ N) := by
    ext ω
    by_cases hωN : ω ∈ N
    · simp only [mem_union, mem_inter_iff, mem_compl_iff, hωN, not_true_eq_false, and_false,
        false_or, and_true]
    · have hτω : τ ω = τ' ω := not_not.1 hωN
      simp only [mem_union, mem_inter_iff, mem_compl_iff, hωN, not_false_eq_true, and_true,
        and_false, or_false, mem_ofPred_eq, hτω]
  rw [hdecomp]
  exact ((hτ' t).inter (hnull t _ hN).compl).union
    (hnull t _ (measure_mono_null inter_subset_right hN))

/-! ## The fast-side chain for the dyadic exit -/

section Chain

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (z : V) (A : Set V)

include h hG hm hmsum

/-- **The expected stopped occupation before the dyadic exit is supported in `A`.**  The
dyadic exit coincides almost surely with the actual exit time, before which every vertex
visited lies in `A`. -/
theorem actualStoppedOccupationDensity_dyadicExit_eq_zero_off (B : Set PF.Ω)
    {s t : ℝ≥0} (hst : s ≤ t) {x : V} (hx : x ∉ A) :
    actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst x = 0 := by
  change actualStoppedOccupationMass PF z B (dyadicExit PF A) s t x / Real.sqrt (m x) = 0
  suffices actualStoppedOccupationMass PF z B (dyadicExit PF A) s t x = 0 by rw [this, zero_div]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro r _
  have hnull : PF.P z {ω | ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < dyadicExit PF A ω ∧
      PF.X r.toNNReal ω = some x} = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (ae_dyadicExit_eq_exitHitting h A z))
    intro ω hω hτω
    have hlt : (r.toNNReal : WithTop ℝ≥0) < exitHitting PF A ω := by
      have h1 := hω.2.1
      rw [hτω] at h1
      exact h1
    exact hx (mem_of_lt_exitHitting PF.X A ω r.toNNReal x hlt hω.2.2)
  rw [hnull, ENNReal.toReal_zero]

variable (U : hilbertDomain G m) (B : Set PF.Ω) {s t : ℝ≥0} (hst : s ≤ t)

/-- Dual drift estimate for the dyadic exit (the analogue of
`LocalHarmonicBoundaryBracket.localHarmonic_stopped_occupation_drift_pairing_abs_le`, with
the pre-exit hypothesis replaced by the support statement). -/
theorem drift_pairing_abs_le_dyadicExit
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (W : hilbertDomain G m)
    (hW : valueInclusion G m W =
      actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst)
    (q : CountableResolventCoreIndex V) :
    |⟪valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q,
      actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst⟫_ℝ| ≤
      ‖countableResolventCoreVector G m q - U‖ * ‖W‖ := by
  have hsupp : ∀ x ∉ A, unweight m (valueInclusion G m W) x = 0 := by
    intro x hx
    rw [hW]
    change actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst x /
      Real.sqrt (m x) = 0
    rw [actualStoppedOccupationDensity_dyadicExit_eq_zero_off h hG hm hmsum z A B hst hx,
      zero_div]
  have hbound :=
    local_variational_resolventCore_generator_bound G m U A hU q W hsupp
  rwa [hW] at hbound

theorem drift_pairing_tendsto_zero_dyadicExit
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (W : hilbertDomain G m)
    (hW : valueInclusion G m W =
      actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst) :
    Tendsto (fun n : ℕ ↦
        ⟪valueInclusion G m
            (countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U n)) -
          countableResolventCoreInput G m (fullEnergyCoreIndex G m hm U n),
          actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst⟫_ℝ)
      atTop (𝓝 0) := by
  have hb : ∀ n : ℕ,
      ‖⟪valueInclusion G m
            (countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U n)) -
          countableResolventCoreInput G m (fullEnergyCoreIndex G m hm U n),
          actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst⟫_ℝ‖ ≤
        (1 / 2 : ℝ) ^ n * ‖W‖ := by
    intro n
    rw [Real.norm_eq_abs]
    exact (drift_pairing_abs_le_dyadicExit h hG hm hmsum z A U B hst hU W hW
      (fullEnergyCoreIndex G m hm U n)).trans
        (mul_le_mul_of_nonneg_right (fullEnergyCoreIndex_bound G m hm U n)
          (norm_nonneg W))
  have hg : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * ‖W‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖W‖
  exact squeeze_zero_norm hb hg

theorem corePotential_increment_tendsto_zero_dyadicExit (default : V)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (W : hilbertDomain G m)
    (hW : valueInclusion G m W =
      actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst)
    (hpotential : ∀ q : CountableResolventCoreIndex V,
      ⟪valueInclusion G m (countableResolventCoreVector G m q) -
          countableResolventCoreInput G m q,
        actualStoppedOccupationDensity h hG hm hmsum z B (dyadicExit PF A) hst⟫_ℝ =
        ∫ ω in B,
          stoppedProcess (compactResolventCorePotential G m hm PF default q)
            (dyadicExit PF A) t ω -
          stoppedProcess (compactResolventCorePotential G m hm PF default q)
            (dyadicExit PF A) s ω ∂PF.P z) :
    Tendsto (fun n : ℕ ↦
        ∫ ω in B,
          stoppedProcess (compactResolventCorePotential G m hm PF default
            (fullEnergyCoreIndex G m hm U n)) (dyadicExit PF A) t ω -
          stoppedProcess (compactResolventCorePotential G m hm PF default
            (fullEnergyCoreIndex G m hm U n)) (dyadicExit PF A) s ω ∂PF.P z)
      atTop (𝓝 0) := by
  have hpair := drift_pairing_tendsto_zero_dyadicExit h hG hm hmsum z A U B hst hU W hW
  simpa only [hpotential] using hpair

/-- **The raw set-integral increment identity for the exact dyadic exit** (the analogue of
`localHarmonic_stopped_fullEnergyPath_integrable_and_increment_eq_zero`). -/
theorem stopped_fullEnergyPath_integrable_and_increment_eq_zero_dyadicExit (default : V)
    (hst : s ≤ t)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (hB : MeasurableSet[PF.naturalFiltration.rightCont s] B) :
    Integrable (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
        (dyadicExit PF A) t) (PF.P z) ∧
    Integrable (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
        (dyadicExit PF A) s) (PF.P z) ∧
    (∫ ω in B, stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
        (dyadicExit PF A) t ω ∂PF.P z) =
      ∫ ω in B, stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
        (dyadicExit PF A) s ω ∂PF.P z := by
  have htau : IsStoppingTime PF.naturalFiltration.rightCont (dyadicExit PF A) :=
    isStoppingTime_rightCont_dyadicExit PF A
  obtain ⟨W, hW⟩ := actualStoppedOccupation_exists_fullDomain h hG hm hmsum z htau hst hB
  have hzero := corePotential_increment_tendsto_zero_dyadicExit h hG hm hmsum z A U B hst
    default hU W hW
    (fun q ↦ resolventCore_actualStoppedOccupation_pairing_eq_stoppedPotential
      h hG hm hmsum default z htau hst hB q)
  have hmul : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by show n ≤ 2 * n; omega) tendsto_id
  have heven := hzero.comp hmul
  simp only [Function.comp_def] at heven
  have hdiff : Tendsto (fun n : ℕ ↦
      (∫ ω in B,
        stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n)
          (dyadicExit PF A) t ω ∂PF.P z) -
      ∫ ω in B,
        stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n)
          (dyadicExit PF A) s ω ∂PF.P z)
      atTop (𝓝 0) :=
    heven.congr fun n ↦
      stopped_fullEnergyPotentialApprox_increment_setIntegral_eq h hG hm hmsum default z htau U n
  have hlimT := stopped_fullEnergyPotentialPathLimit_setIntegral_tendsto
    h hG hm hmsum default z htau U t B
  have hlimS := stopped_fullEnergyPotentialPathLimit_setIntegral_tendsto
    h hG hm hmsum default z htau U s B
  have hsub := tendsto_nhds_unique (hlimT.sub hlimS) hdiff
  exact ⟨(stopped_fullEnergyPotentialPathLimit_integrable_and_L1_convergence
      h hG hm hmsum default z htau U t).1,
    (stopped_fullEnergyPotentialPathLimit_integrable_and_L1_convergence
      h hG hm hmsum default z htau U s).1,
    by linarith⟩

end Chain

/-! ## The completed-filtration martingale at the actual exit time -/

section Completed

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default z : V) (U : hilbertDomain G m) (A : Set V)
  {enc : Option V → ℕ} (henc : Function.Injective enc)
  (X' : ℝ≥0 → PF.Ω → ℕ) (hX'e : ∀ t ω, X' t ω = enc (PF.X t ω))
  (hX' : ∀ t, Measurable (X' t))

include henc hX'e

/-- The right continuation of mathlib's natural filtration of the encoded fast path is the
right continuation of the walk's own natural filtration. -/
theorem rightCont_natural_enc_eq_naturalFiltration_rightCont (t : ℝ≥0) :
    (Filtration.natural X' (fun t => (hX' t).stronglyMeasurable)).rightCont t =
      PF.naturalFiltration.rightCont t := by
  rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
  exact iInf_congr fun u => iInf_congr fun _ =>
    natural_enc_eq_pastSigma henc PF.X X' hX'e hX' u

/-- The dyadic exit is an exact stopping time of the completed fast filtration. -/
theorem isStoppingTime_completed_dyadicExit :
    IsStoppingTime (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX')
      (dyadicExit PF A) := fun t =>
  rightCont_naturalFiltration_le_completedNaturalFiltration (PF.P z) henc PF.X PF.measurable_X
    X' hX'e hX' t _ (isStoppingTime_rightCont_dyadicExit PF A t)

include h

/-- **The actual exit time is an exact stopping time of the completed fast filtration.** -/
theorem isStoppingTime_completed_exitHitting :
    IsStoppingTime (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX')
      (exitHitting PF A) :=
  isStoppingTime_of_ae_eq_of_null_events (isStoppingTime_completed_dyadicExit z A henc X' hX'e hX')
    (ProcessFiltration.measurableSet_completedNaturalFiltration_of_null (PF.P z) X' hX')
    (ae_completion_of_ae ((ae_dyadicExit_eq_exitHitting h A z).mono fun _ hω => hω.symm))

include hG hm hmsum

/-- **The stopped locally harmonic fast path is a martingale of the completed fast
filtration, stopped at the actual spatial exit time of `A`.**  This is the drift elimination
of `p:lem:localharm` in `Martingale` form; `hU` is the full spatial variational harmonicity
of `U` on `A`. -/
theorem martingale_stopped_fullEnergyPath_exit_completed
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0) :
    Martingale (fun t (ω : NullMeasurableSpace PF.Ω (PF.P z)) =>
        stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
          (exitHitting PF A) t ω)
      (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX') (PF.P z).completion := by
  have htau : IsStoppingTime PF.naturalFiltration.rightCont (dyadicExit PF A) :=
    isStoppingTime_rightCont_dyadicExit PF A
  have hFeq := rightCont_natural_enc_eq_naturalFiltration_rightCont henc X' hX'e hX'
  -- the martingale stopped at the dyadic exit
  have hM' : Martingale (fun t (ω : NullMeasurableSpace PF.Ω (PF.P z)) =>
        stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
          (dyadicExit PF A) t ω)
      (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX') (PF.P z).completion := by
    refine martingale_completedNaturalFiltration_of_rightCont_setIntegral hX'
      (Y := stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (dyadicExit PF A))
      ?_ ?_ ?_ ?_
    · exact fun t => (stopped_fullEnergyPotentialPathLimit_integrable_and_L1_convergence
        h hG hm hmsum default z htau U t).1
    · intro t
      rw [hFeq t]
      exact aestronglyMeasurable_stopped_fullEnergyPotentialPathLimit_rightCont
        h hG hm hmsum default z htau U t
    · filter_upwards [fullEnergyPotentialPathLimit_ae_cadlag_and_uniform h hG hm hmsum default U z]
        with ω hω
      exact MartingaleLimit.isRightContinuous_stoppedProcess_common ω hω.1.isRightContinuous _
    · intro s t hst B hB
      rw [hFeq s] at hB
      exact (stopped_fullEnergyPath_integrable_and_increment_eq_zero_dyadicExit
        h hG hm hmsum z A U B default hst hU hB).2.2
  -- replace the dyadic exit by the actual exit time
  have hae : ∀ t, (fun ω : NullMeasurableSpace PF.Ω (PF.P z) =>
        stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
          (dyadicExit PF A) t ω) =ᵐ[(PF.P z).completion]
      (fun ω => stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
          (exitHitting PF A) t ω) := by
    intro t
    refine ae_completion_of_ae ?_
    filter_upwards [ae_dyadicExit_eq_exitHitting h A z] with ω hω
    simp only [stoppedProcess, hω]
  refine hM'.congr (fun t => ?_) hae
  exact LocalMartingaleCombination.stronglyMeasurable_of_ae_eq_of_null_events
    ((ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX').le t)
    (ProcessFiltration.measurableSet_completedNaturalFiltration_of_null (PF.P z) X' hX' t)
    (hM'.stronglyMeasurable t) (hae t)

end Completed

end ReflectedGMS.StoppedFormAssociation
