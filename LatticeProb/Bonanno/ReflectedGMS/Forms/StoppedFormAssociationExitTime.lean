/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedFormAssociationExitTime at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessSkeleton
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicDensity
import LatticeProb.Bonanno.ReflectedGMS.Process.NaturalFiltration
import Mathlib.Probability.Process.Stopping

/-!
# Exact stopping times for the spatial exit of the reflected walk

The localizer of `p:lem:localharm` is the first time the walk sits at a vertex outside a
(possibly infinite) vertex region `A`: `hittingAfter X (some '' Aᶜ) 0`.  Three facts about
it are needed by the stopped-martingale packaging and are supplied here.

* **An exact right-continuous stopping time.**  The paths of the reflected walk are only
  almost surely right regular, so the hitting time of a vertex set is a stopping time of
  the raw natural filtration only up to null sets (`Theorem16.isAEStoppingTime_hitAfter`,
  and only for *finite* targets).  The infimum over the countable dyadic times
  `dyadicHitting` is an **exact** stopping time of the right continuation of the raw
  natural filtration, for every target set, and it coincides with `hittingAfter` on every
  right regular path whenever the target contains no nonvertex state
  (`dyadicHitting_eq_hittingAfter`).  This is what the fast-side producers
  (`Forms/StoppedHarmonicAdaptedness`, `Forms/StoppedFullEnergyPathL1Limit`) consume.
* **Pre-exit region.**  Strictly before `hittingAfter X (some '' Aᶜ) 0` every vertex visited
  lies in `A`, for every sample (`mem_of_lt_exitHitting`).
* **The completed filtration.**  `Process/NaturalFiltration.completedNaturalFiltration` is
  built on mathlib's `Filtration.natural` of an injectively encoded observation, whereas the
  walk's own filtration is `Theorem16.naturalFiltration = pastSigma`; the two agree
  (`natural_enc_eq_pastSigma`).  Every almost-sure stopping time of the raw natural
  filtration is an exact stopping time of the completed one
  (`isStoppingTime_completedNaturalFiltration_of_isAEStoppingTime`), and the right
  continuation of the raw filtration is contained in the completed one
  (`rightCont_naturalFiltration_le_completedNaturalFiltration`).

No `Summable` hypothesis and no walk law appear except in the almost-sure identification,
which uses only properties (ii) and (ii at `∞`) of `IsReflectedWalk`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.StoppedFormAssociation

open ReflectedWalk ReflectedWalk.Theorem16

universe u

variable {V : Type u} {Ω : Type u} [MeasurableSpace Ω]

/-! ## The natural filtration of an injectively encoded observation -/

section Encoding

variable [Countable V]

/-- Pulling back the product σ-algebra along a coordinatewise injective encoding into a
discrete space returns the product σ-algebra of the discrete vertex space. -/
theorem comap_piMap_eq_pi_of_injective {ι : Type*} {enc : Option V → ℕ}
    (henc : Function.Injective enc) :
    MeasurableSpace.comap (fun p : ι → Option V => fun j => enc (p j))
      (MeasurableSpace.pi : MeasurableSpace (ι → ℕ)) =
      (MeasurableSpace.pi : MeasurableSpace (ι → Option V)) := by
  refine le_antisymm ?_ ?_
  · exact Measurable.comap_le
      (measurable_pi_iff.2 fun j => (measurable_of_countable enc).comp (measurable_pi_apply j))
  · refine iSup_le fun j => ?_
    intro s hs
    obtain ⟨T, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    refine MeasurableSpace.measurableSet_comap.2
      ⟨(fun q : ι → ℕ => q j) ⁻¹' (enc '' T), measurable_pi_apply j MeasurableSet.of_discrete, ?_⟩
    ext p
    simp only [mem_preimage, henc.mem_set_image]

/-- **Mathlib's natural filtration of an injectively encoded observation of the path is the
walk's `pastSigma`.**  The observation `X'` is any function agreeing with `enc ∘ X`. -/
theorem natural_enc_eq_pastSigma {enc : Option V → ℕ} (henc : Function.Injective enc)
    (X : ℝ≥0 → Ω → Option V) (X' : ℝ≥0 → Ω → ℕ) (hX'e : ∀ t ω, X' t ω = enc (X t ω))
    (hX' : ∀ t, Measurable (X' t)) (t : ℝ≥0) :
    Filtration.natural X' (fun t => (hX' t).stronglyMeasurable) t = pastSigma X t := by
  rw [Filtration.natural_eq_comap]
  have hcomp : (fun ω (j : Iic t) => X' j ω) =
      (fun p : Iic t → Option V => fun j => enc (p j)) ∘ pastPath X t := by
    funext ω j
    exact hX'e j ω
  rw [hcomp]
  change MeasurableSpace.comap
      ((fun p : Iic t → Option V => fun j => enc (p j)) ∘ pastPath X t) _ =
    MeasurableSpace.comap (pastPath X t) MeasurableSpace.pi
  rw [← MeasurableSpace.comap_comp, comap_piMap_eq_pi_of_injective henc]

end Encoding

/-! ## The dyadic hitting time -/

/-- The first dyadic time at which the path lies in `S`: an exact stopping time of the
right-continuous natural filtration, for every target set. -/
noncomputable def dyadicHitting (X : ℝ≥0 → Ω → Option V) (S : Set (Option V)) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ (d : globalDyadicSupport) (_ : X d.1 ω ∈ S), ((d.1 : ℝ≥0) : WithTop ℝ≥0)

theorem hittingAfter_le_dyadicHitting (X : ℝ≥0 → Ω → Option V) (S : Set (Option V))
    (ω : Ω) : hittingAfter X S 0 ω ≤ dyadicHitting X S ω :=
  le_iInf₂ fun d hd => hittingAfter_le_of_mem zero_le hd

theorem dyadicHitting_le_of_mem (X : ℝ≥0 → Ω → Option V) (S : Set (Option V)) (ω : Ω)
    {d : ℝ≥0} (hd : d ∈ globalDyadicSupport) (hS : X d ω ∈ S) :
    dyadicHitting X S ω ≤ ((d : ℝ≥0) : WithTop ℝ≥0) :=
  iInf₂_le (⟨d, hd⟩ : globalDyadicSupport) hS

/-- The strict sublevel sets of the dyadic hitting time belong to the raw natural
filtration: they are countable unions of vertex-fibre events at earlier dyadic times. -/
theorem measurableSet_dyadicHitting_lt (X : ℝ≥0 → Ω → Option V) (S : Set (Option V))
    (t : ℝ≥0) :
    MeasurableSet[pastSigma X t] {ω | dyadicHitting X S ω < t} := by
  have hset : {ω | dyadicHitting X S ω < t} =
      ⋃ (d : globalDyadicSupport) (_ : (d.1 : ℝ≥0) < t), {ω | X d.1 ω ∈ S} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hlt
      obtain ⟨d, hd⟩ := iInf_lt_iff.1 hlt
      obtain ⟨hdS, hdt⟩ := iInf_lt_iff.1 hd
      exact ⟨d, WithTop.coe_lt_coe.1 hdt, hdS⟩
    · rintro ⟨d, hdt, hdS⟩
      exact iInf_lt_iff.2 ⟨d, iInf_lt_iff.2 ⟨hdS, WithTop.coe_lt_coe.2 hdt⟩⟩
  rw [hset]
  have : Countable globalDyadicSupport := globalDyadicSupport_countable.to_subtype
  exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun hd =>
    pastSigma_mono X hd.le _ (measurableSet_pastSigma_eval d.1 S)

/-- **The dyadic hitting time is an exact stopping time of the right continuation of the
raw natural filtration**, with no path regularity and no law. -/
theorem isStoppingTime_rightCont_dyadicHitting (X : ℝ≥0 → Ω → Option V)
    (hX : ∀ t, Measurable (X t)) (S : Set (Option V)) :
    IsStoppingTime (naturalFiltration X hX).rightCont (dyadicHitting X S) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t =>
    Filtration.le_rightCont _ t _ (measurableSet_dyadicHitting_lt X S t)

/-- A dyadic time strictly to the right of `r`, within a prescribed distance. -/
theorem exists_dyadic_between (r η : ℝ≥0) (hη : 0 < η) :
    ∃ d ∈ globalDyadicSupport, r < d ∧ d < r + η := by
  have := globalDyadicSupport_nhdsWithin_Ioi_neBot r
  have h1 : ∀ᶠ d in 𝓝[globalDyadicSupport ∩ Ioi r] r, d ∈ globalDyadicSupport ∩ Ioi r :=
    self_mem_nhdsWithin
  have h2 : ∀ᶠ d in 𝓝[globalDyadicSupport ∩ Ioi r] r, d < r + η :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_of_pos_right r hη))
  obtain ⟨d, ⟨hdD, hdr⟩, hdlt⟩ := (h1.and h2).exists
  exact ⟨d, hdD, hdr, hdlt⟩

/-- **On a right regular path the dyadic hitting time of a vertex target is the hitting
time.**  A visit to a vertex of `S` lasts for a positive time, which contains a dyadic
time. -/
theorem dyadicHitting_eq_hittingAfter {X : ℝ≥0 → Ω → Option V} {S : Set (Option V)}
    {ω : Ω} (hω : RightRegularAt X ω) (hS : none ∉ S) :
    dyadicHitting X S ω = hittingAfter X S 0 ω := by
  refine le_antisymm ?_ (hittingAfter_le_dyadicHitting X S ω)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  have hcne : c ≠ ⊤ := ne_top_of_lt hc2
  lift c to ℝ≥0 using hcne
  rw [hittingAfter_lt_iff] at hc1
  obtain ⟨r, ⟨-, hrc⟩, hrS⟩ := hc1
  obtain ⟨v, hv⟩ : ∃ v, X r ω = some v := by
    cases hXr : X r ω with
    | none =>
        rw [hXr] at hrS
        exact absurd hrS hS
    | some v => exact ⟨v, rfl⟩
  obtain ⟨ε, hε, hεS⟩ := hω.1 r ⟨v, hv⟩
  have hη : 0 < min ε (c - r) := lt_min hε (tsub_pos_of_lt hrc)
  obtain ⟨d, hdD, hrd, hdlt⟩ := exists_dyadic_between r _ hη
  have hdε : d ∈ Ico r (r + ε) :=
    ⟨hrd.le, hdlt.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hXd : X d ω ∈ S := by
    rw [hεS d hdε]
    exact hrS
  have hdc : d < c := by
    have hle : r + min ε (c - r) ≤ c := by
      calc r + min ε (c - r) ≤ r + (c - r) := add_le_add le_rfl (min_le_right _ _)
        _ = c := add_tsub_cancel_of_le hrc.le
    exact hdlt.trans_le hle
  have hle := dyadicHitting_le_of_mem X S ω hdD hXd
  exact absurd (hle.trans_lt (WithTop.coe_lt_coe.2 hdc)) (not_lt.2 hc2.le)

/-- The almost-sure identification under every starting law of a reflected walk. -/
theorem ae_dyadicHitting_eq_hittingAfter [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable V] [Nontrivial V]
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF) (z : V)
    {S : Set (Option V)} (hS : none ∉ S) :
    ∀ᵐ ω ∂PF.P z, dyadicHitting PF.X S ω = hittingAfter PF.X S 0 ω :=
  (ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1).mono fun _ hω =>
    dyadicHitting_eq_hittingAfter hω hS

/-! ## The pre-exit region -/

/-- Strictly before the first visit to a vertex outside `A`, every vertex visited lies in
`A`; this holds for every sample. -/
theorem mem_of_lt_exitHitting (X : ℝ≥0 → Ω → Option V) (A : Set V) (ω : Ω)
    (r : ℝ≥0) (x : V) (hr : (r : WithTop ℝ≥0) < hittingAfter X (some '' Aᶜ) 0 ω)
    (hx : X r ω = some x) : x ∈ A := by
  have hnot := notMem_of_lt_hittingAfter hr zero_le
  rw [hx] at hnot
  by_contra hxA
  exact hnot ⟨x, hxA, rfl⟩

/-- The target of the spatial exit contains no nonvertex state. -/
theorem none_notMem_some_image (A : Set V) : (none : Option V) ∉ some '' A := by
  rintro ⟨x, -, hx⟩
  exact Option.some_ne_none x hx

/-! ## Stopping times of the completed natural filtration -/

section Completed

variable [Countable V]

/-- The right continuation of the raw natural filtration is contained in the completed
natural filtration of any injectively encoded observation. -/
theorem rightCont_naturalFiltration_le_completedNaturalFiltration
    (P : Measure Ω) {enc : Option V → ℕ} (henc : Function.Injective enc)
    (X : ℝ≥0 → Ω → Option V) (hX : ∀ t, Measurable (X t))
    (X' : ℝ≥0 → Ω → ℕ) (hX'e : ∀ t ω, X' t ω = enc (X t ω))
    (hX' : ∀ t, Measurable (X' t)) (t : ℝ≥0) :
    (naturalFiltration X hX).rightCont t ≤
      ProcessFiltration.completedNaturalFiltration P X' hX' t := by
  unfold ProcessFiltration.completedNaturalFiltration
  dsimp only
  rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
  refine iInf₂_mono fun u _ => ?_
  have hu : pastSigma X u = Filtration.natural X' (fun t => (hX' t).stronglyMeasurable) u :=
    (natural_enc_eq_pastSigma henc X X' hX'e hX' u).symm
  refine le_trans (le_of_eq ?_) le_sup_left
  exact hu

end Completed

end ReflectedGMS.StoppedFormAssociation
