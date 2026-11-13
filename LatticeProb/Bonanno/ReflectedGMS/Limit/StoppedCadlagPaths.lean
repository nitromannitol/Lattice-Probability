/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppedCadlagPaths at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ThresholdStoppedMartingaleMoments

/-!
# Càdlàg paths after exact indicator stopping

Stopping a càdlàg path at an arbitrary extended nonnegative time preserves its
càdlàg property.  Applying the project's `{τ > 0}` indicator then either keeps
that stopped path or gives the constant zero path.  The final theorem adds this
path input to the exact martingale-and-moment tuple consumed by interpolation
tightness.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A càdlàg path remains càdlàg after stopping at an arbitrary extended time. -/
theorem isCadlag_stoppedProcess
    {M : ℝ≥0 → Ω → ℝ} (ω : Ω) (hM : IsCadlag (fun t => M t ω))
    (τ : Ω → WithTop ℝ≥0) :
    IsCadlag (fun t => stoppedProcess M τ t ω) := by
  refine ⟨isRightContinuous_stoppedProcess_common ω hM.isRightContinuous τ, ?_⟩
  by_cases hτtop : τ ω = ⊤
  · have heq : (fun t => stoppedProcess M τ t ω) = fun t => M t ω := by
      funext t
      exact stoppedProcess_eq_of_le (by rw [hτtop]; exact le_top)
    rw [heq]
    exact hM.tendsto_nhdsLT
  let c := (τ ω).untop hτtop
  have hτcoe : (c : WithTop ℝ≥0) = τ ω := WithTop.coe_untop (τ ω) hτtop
  have heq : (fun t => stoppedProcess M τ t ω) = fun t => M (min t c) ω := by
    funext t
    rw [stoppedProcess, ← hτcoe, ← WithTop.coe_min]
    rfl
  rw [heq]
  intro x
  by_cases hxc : x ≤ c
  · obtain ⟨l, hl⟩ := hM.tendsto_nhdsLT x
    refine ⟨l, Tendsto.congr' ?_ hl⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [min_eq_left (ht.le.trans hxc)]
  · have hcx : c < x := lt_of_not_ge hxc
    refine ⟨M c ω, Tendsto.congr' ?_ tendsto_const_nhds⟩
    filter_upwards [Ioo_mem_nhdsLT hcx] with t ht
    rw [min_eq_right ht.1.le]

/-- The exact `{τ > 0}` indicator-stopped path is càdlàg whenever the original
path is càdlàg.  This includes zero and infinite stopping times. -/
theorem isCadlag_indicator_stoppedProcess
    {M : ℝ≥0 → Ω → ℝ} (ω : Ω) (hM : IsCadlag (fun t => M t ω))
    (τ : Ω → WithTop ℝ≥0) :
    IsCadlag (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t ω) := by
  have heq : (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t ω) =
      fun t => {ω | ⊥ < τ ω}.indicator (stoppedProcess M τ t) ω := by
    funext t
    exact congrFun (stoppedProcess_indicator_comm' (u := M) (τ := τ)) t ▸ rfl
  rw [heq]
  by_cases hωτ : ⊥ < τ ω
  · have hind : (fun t => {ω | ⊥ < τ ω}.indicator
        (stoppedProcess M τ t) ω) = fun t => stoppedProcess M τ t ω := by
      funext t
      rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    exact isCadlag_stoppedProcess ω hM τ
  · have hind : (fun t => {ω | ⊥ < τ ω}.indicator
        (stoppedProcess M τ t) ω) = fun _ => (0 : ℝ) := by
      funext t
      rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    exact IsCadlag.const

/-- Almost-sure càdlàg paths transfer to the exact indicator-stopped process. -/
theorem ae_isCadlag_indicator_stoppedProcess
    {P : Measure Ω} {M : ℝ≥0 → Ω → ℝ} (τ : Ω → WithTop ℝ≥0)
    (hM : ∀ᵐ ω ∂P, IsCadlag (fun t => M t ω)) :
    ∀ᵐ ω ∂P, IsCadlag (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t ω) := by
  filter_upwards [hM] with ω hω
  exact isCadlag_indicator_stoppedProcess ω hω τ

/-- The exact stopped tuple needed by
`isTightMeasureSet_interpolated_martingale_laws`: the existing martingale,
compensated-square, `L²`, and terminal-moment conclusions together with the
missing càdlàg-path conclusion. -/
theorem threshold_stopped_martingale_tightness_inputs_with_cadlag
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hcM : ∀ᵐ ω ∂P, IsCadlag (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2 : ∀ t, MemLp (M t) 2 P)
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hB0 : ∀ᵐ ω ∂P, B 0 ω = 0)
    (T : ℝ≥0) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P,
      |stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ T ω| ≤ K) :
    let N := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ
    let A := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ
    Martingale N F P ∧
      Martingale (fun t ω => N t ω * N t ω - A t ω) F P ∧
      (∀ t, MemLp (N t) 2 P) ∧
      (∀ᵐ ω ∂P, IsCadlag (fun t => N t ω)) ∧
      (∫ ω, (N T ω) ^ 2 ∂P) ≤ K := by
  dsimp only
  obtain ⟨hN, hcomp, hN2, hterminal⟩ :=
    threshold_stopped_martingale_tightness_inputs hM hC hτ hnull
      (hcM.mono fun _ hω => hω.isRightContinuous) hrC h2 hM0 hB0 T hK hbound
  exact ⟨hN, hcomp, hN2, ae_isCadlag_indicator_stoppedProcess τ hcM, hterminal⟩

end ReflectedGMS.MartingaleLimit
