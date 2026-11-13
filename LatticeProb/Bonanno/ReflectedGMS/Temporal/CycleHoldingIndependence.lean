/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CycleHoldingIndependence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CycleHoldingStraddle
import LatticeProb.Bonanno.ReflectedGMS.Forms.SojournExitLaw

/-!
# (R4) at the actual walk: the first holding is independent of the excursion

`CycleDecompositionLaw.HoldExcIndep ν := IndepFun holdTime (withHold 1) ν`.  At the actual
first-cycle law `ν = firstCycleLaw G hwalk n e` (environment on the gate, slot `n` present) it is
proved here with no hypothesis.

* **`indepFun_exitTime_futureAt`** (any reflected walk on a connected graph): the property-(iii)
  exit time `σ = exitTime X z` is independent of the WHOLE post-exit path `X_{σ+·}` under `P_z`.
  Proof: the checked one-step law `measure_exitPair_completed` at the start time gives the joint
  law of `(σ, X_σ)` on stopped-past events, `aemeasurableSetStopped_exitPair_history` puts the
  exit event in `𝓕_σ`, and the completed strong Markov property at `σ` then gives
  `P(σ ∈ B, X_σ = v, X_{σ+·} ∈ D) = Exp(B)·p(z,v)·P_v(D)`; summing over the (a.s. vertex) exit
  position, `P(σ ∈ B, X_{σ+·} ∈ D) = Exp(B)·K(D)`, which factorizes.
* `exitCycle v y` — hold `1` at `v`, then the post-exit path `y` up to its first complete return;
  measurable on the regularity subtype.  `exitCycle_eq_withHold` (pathwise): if the post-exit
  path of a good path is `y`, then `exitCycle v y = withHold 1 (firstCycle v x)`.
* **`holdExcIndep_firstCycleLaw`**: (R4) at the actual first-cycle law, by transporting the
  sample-space independence through the lift of `exists_sample_lift` and a second lift of the
  post-exit label path.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleHolding

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.FirstCycleLaw
open ReflectedGMS.RegenerativeInvarianceFiberwise
open ReflectedGMS.CycleDecomposition
open ReflectedGMS.Temporal.ActualExcursionErgodicIdentification
open ReflectedGMS.TargetReturnConditional

/-! ### 1. The exit time is independent of the post-exit path (sample space) -/

/-- The deterministic start time `0`. -/
noncomputable def startTime (Ω : Type*) : Ω → WithTop ℝ≥0 := fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)

section Exit

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- **Joint law of the exit time and the post-exit path.** -/
theorem measure_exit_future (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected)
    (z : V) {B : Set (WithTop ℝ≥0)} (hB : MeasurableSet B) {D : Set (Trajectory V)}
    (hD : MeasurableSet D) :
    PF.P z (exitTime PF.X z ⁻¹' B ∩ futureAt PF.X (exitTime PF.X z) ⁻¹' D) =
      ((expMeasure (w z)).map toWithTop) B *
        ∑' v : V, ENNReal.ofReal (G.c z v / G.pi z) * PF.law v D := by
  have hii : RightContinuous (PF.P z) PF.X := (h z).2.2.1
  have hR : RightContinuousAtInfty (PF.P z) PF.X := (h z).2.2.2.1
  have hτm : AEMeasurable (startTime PF.Ω) (PF.P z) := aemeasurable_const
  have hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) (startTime PF.Ω) :=
    isAEStoppingTime_const PF.measurable_X 0
  have hρm : AEMeasurable (exitTime PF.X z) (PF.P z) :=
    SojournExitLaw.aemeasurable_exitTime h z z hτm
  have hρ : IsAEStoppingTime PF.naturalFiltration (PF.P z) (exitTime PF.X z) :=
    isAEStoppingTime_hitAfter PF.measurable_X hii hR (admissibleTarget_ne z) hτ
  have hLm : AEMeasurable (fun ω => exitTime PF.X z ω - startTime PF.Ω ω) (PF.P z) :=
    SojournExitLaw.aemeasurable_holding h z z hτm
  have hfm : AEMeasurable (futureAt PF.X (exitTime PF.X z)) (PF.P z) :=
    aemeasurable_futureAt' PF.measurable_X hii hR hρm
  have hstart : stopEvent PF.X (startTime PF.Ω) z =ᵐ[PF.P z] (univ : Set PF.Ω) := by
    refine Filter.eventuallyEqSet_univ.2 ?_
    filter_upwards [(h z).1] with ω hω
    exact ⟨WithTop.coe_ne_top, hω⟩
  have hFuniv : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) (startTime PF.Ω) univ :=
    fun t => ⟨univ, MeasurableSet.univ, EventuallyEq.of_eq
      (Set.eq_univ_of_forall fun _ => ⟨mem_univ _, WithTop.coe_le_coe.2 zero_le⟩)⟩
  -- one exit vertex
  have hEv : ∀ v : V, PF.P z ((univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
      ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩ stopEvent PF.X (exitTime PF.X z) v)) ∩
        futureAt PF.X (exitTime PF.X z) ⁻¹' D) =
      ((expMeasure (w z)).map toWithTop) B * (ENNReal.ofReal (G.c z v / G.pi z) * PF.law v D) := by
    intro v
    have hF : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) (exitTime PF.X z)
        (univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
          ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩
            stopEvent PF.X (exitTime PF.X z) v)) :=
      aemeasurableSetStopped_exitPair_history h z hτ hFuniv hB v
    have hsm := strongMarkov_completed h z hR hρm hρ v hF hD
    have hsub : univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
        ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩
          stopEvent PF.X (exitTime PF.X z) v) ∩ stopEvent PF.X (exitTime PF.X z) v =
        univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
          ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩
            stopEvent PF.X (exitTime PF.X z) v) :=
      inter_eq_left.2 fun _ hω => hω.2.2
    rw [hsub] at hsm
    have hex : PF.P z (univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
        ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩
          stopEvent PF.X (exitTime PF.X z) v)) =
        PF.P z (univ ∩ stopEvent PF.X (startTime PF.Ω) z) *
          (((expMeasure (w z)).map toWithTop) B * ENNReal.ofReal (G.c z v / G.pi z)) :=
      measure_exitPair_completed h hG z hτm hτ hFuniv (Finset.singleton_nonempty z)
        (Finset.mem_singleton_self z) hB v
    rw [hsm, hex, univ_inter, measure_congr hstart, measure_univ, one_mul, mul_assoc]
  -- the exit position is a.s. a vertex
  have hexit := SojournExitLaw.ae_exit_vertex_of_stopEvent h hG z z hτm hτ
  have hae : exitTime PF.X z ⁻¹' B ∩ futureAt PF.X (exitTime PF.X z) ⁻¹' D =ᵐ[PF.P z]
      ⋃ v : V, (univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
        ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩
          stopEvent PF.X (exitTime PF.X z) v)) ∩ futureAt PF.X (exitTime PF.X z) ⁻¹' D := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [Filter.eventuallyEqSet_univ.1 hstart, hexit] with ω h0 hω
    have hsubB : exitTime PF.X z ω - startTime PF.Ω ω ∈ B ↔ exitTime PF.X z ω ∈ B := by
      show exitTime PF.X z ω - ((0 : ℝ≥0) : WithTop ℝ≥0) ∈ B ↔ _
      rw [WithTop.coe_zero, tsub_zero]
    constructor
    · rintro ⟨hB', hD'⟩
      obtain ⟨hne, v, hv⟩ := hω h0
      exact mem_iUnion.2 ⟨v, ⟨⟨mem_univ _, h0⟩, hsubB.2 hB', hne, hv⟩, hD'⟩
    · intro hmem
      obtain ⟨v, ⟨-, hB', -⟩, hD'⟩ := mem_iUnion.1 hmem
      exact ⟨hsubB.1 hB', hD'⟩
  have hnull : ∀ v : V, NullMeasurableSet ((univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
      ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩ stopEvent PF.X (exitTime PF.X z) v)) ∩
        futureAt PF.X (exitTime PF.X z) ⁻¹' D) (PF.P z) := fun v =>
    ((MeasurableSet.univ.nullMeasurableSet.inter
      (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm z)).inter
      ((hLm.nullMeasurable hB).inter
        (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hρm v))).inter
      (hfm.nullMeasurable hD)
  have hdisj : Pairwise (Function.onFun (AEDisjoint (PF.P z)) fun v : V =>
      (univ ∩ stopEvent PF.X (startTime PF.Ω) z ∩
        ({ω | exitTime PF.X z ω - startTime PF.Ω ω ∈ B} ∩
          stopEvent PF.X (exitTime PF.X z) v)) ∩ futureAt PF.X (exitTime PF.X z) ⁻¹' D) :=
    fun v v' hvv' => ((disjoint_stopEvent hvv').mono (fun _ hω => hω.1.2.2)
      (fun _ hω => hω.1.2.2)).aedisjoint
  rw [measure_congr hae, measure_iUnion₀ hdisj hnull]
  simp_rw [hEv]
  rw [ENNReal.tsum_mul_left]

/-- **The exit time is independent of the whole post-exit path** (property (iii) + the completed
strong Markov property at the exit time). -/
theorem indepFun_exitTime_futureAt (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (z : V) :
    IndepFun (exitTime PF.X z) (futureAt PF.X (exitTime PF.X z)) (PF.P z) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro B D hB hD
  have hBD := measure_exit_future h hG z hB hD
  have hBU := measure_exit_future h hG z hB MeasurableSet.univ
  have hUD := measure_exit_future h hG z MeasurableSet.univ hD
  have hUU := measure_exit_future h hG z MeasurableSet.univ MeasurableSet.univ
  simp only [preimage_univ, inter_univ, univ_inter] at hBU hUD hUU
  rw [measure_univ, map_toWithTop_expMeasure_univ h z, one_mul] at hUU
  rw [map_toWithTop_expMeasure_univ h z, one_mul] at hUD
  rw [hBD, hBU, hUD, ← hUU, mul_one]

end Exit

/-! ### 2. The unit-holding cycle of a post-exit path (pathwise) -/

variable {v : ℕ}

/-- Hold `1` at `v`, then `y`. -/
noncomputable def holdOnePath (v : ℕ) (y : Trajectory ℕ) : Trajectory ℕ := glue (constPath v) 1 y

theorem isRegLL_holdOnePath (v : ℕ) {y : Trajectory ℕ} (hy : IsRegLL y) :
    IsRegLL (holdOnePath v y) :=
  isRegLL_glue (isRegLL_constPath v) hy 1

/-- **The unit-holding cycle read from a post-exit path**: hold `1` at `v`, then `y` up to its
first complete return to `v`. -/
noncomputable def exitCycle (v : ℕ) (y : RegLL) : Cyc v :=
  firstCycle v ⟨holdOnePath v y.1, isRegLL_holdOnePath v y.2⟩

theorem measurable_exitCycle (v : ℕ) : Measurable (exitCycle v) := by
  refine (measurable_firstCycle v).comp (Measurable.subtype_mk ?_)
  refine measurable_pi_iff.2 fun s => ?_
  show Measurable fun y : RegLL => holdOnePath v y.1 s
  by_cases hs : s < 1
  · have he : (fun y : RegLL => holdOnePath v y.1 s) = fun _ => some v := by
      funext y
      rw [holdOnePath, glue_of_lt hs]
      rfl
    rw [he]
    exact measurable_const
  · have he : (fun y : RegLL => holdOnePath v y.1 s) = fun y : RegLL => y.1 (s - 1) := by
      funext y
      rw [holdOnePath, glue_of_le (not_lt.1 hs)]
    rw [he]
    exact (measurable_pi_apply _).comp measurable_subtype_coe

theorem glue_excPath_cem (c : Cyc v) :
    glue (excPath c) (c.1.2 - holdTime c) cem = excPath c := by
  funext s
  by_cases hs : s < c.1.2 - holdTime c
  · exact glue_of_lt hs
  · rw [glue_of_le (not_lt.1 hs)]
    symm
    show c.1.1 (s + holdTime c) = none
    apply c.2.killed
    have hle : c.1.2 - holdTime c + holdTime c ≤ s + holdTime c :=
      add_le_add (not_lt.1 hs) le_rfl
    rwa [tsub_add_cancel_of_le (cyc_hold c).2.1.le] at hle

theorem holdOnePath_shift_eq (c : Cyc v) (q : Trajectory ℕ) :
    holdOnePath v (shiftBy (holdTime c) (glue c.1.1 c.1.2 q)) =
      glue (withHold 1 c).1.1 (withHold 1 c).1.2 q := by
  rw [withHold_val one_pos c, shiftBy_glue_le _ _ (cyc_hold c).2.1.le, holdOnePath, glue_glue]
  show glue (glue (constPath v) 1 (glue (excPath c) (c.1.2 - holdTime c) cem))
      (1 + (c.1.2 - holdTime c)) q =
    glue (glue (constPath v) 1 (excPath c)) (1 + (c.1.2 - holdTime c)) q
  rw [glue_excPath_cem]

theorem glue_glue_cem_self {p q : Trajectory ℕ} {L : ℝ≥0} (hp : ∀ t, L ≤ t → p t = none) :
    glue (glue p L q) L cem = p := by
  funext s
  by_cases hs : s < L
  · rw [glue_of_lt hs, glue_of_lt hs]
  · rw [glue_of_le (not_lt.1 hs), hp s (not_lt.1 hs)]
    rfl

/-- **The unit-holding cycle of the post-exit path is the first cycle with unit holding.** -/
theorem exitCycle_eq_withHold (c : Cyc v) {q : Trajectory ℕ} (hq : q 0 = some v) {y : RegLL}
    (hy : y.1 = shiftBy (holdTime c) (glue c.1.1 c.1.2 q)) :
    exitCycle v y = withHold 1 c := by
  have hp : holdOnePath v y.1 = glue (withHold 1 c).1.1 (withHold 1 c).1.2 q := by
    rw [hy, holdOnePath_shift_eq]
  have hret : fwdReturn (holdOnePath v y.1) = (withHold 1 c).1.2 := by
    rw [hp]
    exact fwdReturn_glue (withHold 1 c).2 hq
  have h0 : holdOnePath v y.1 0 = some v := by
    rw [holdOnePath, glue_of_lt one_pos]
    rfl
  have hlen : retLen (holdOnePath v y.1) = (withHold 1 c).1.2 := by
    rw [retLen, hret]
    rfl
  apply Subtype.ext
  show (firstCycle v ⟨holdOnePath v y.1, isRegLL_holdOnePath v y.2⟩).1 = (withHold 1 c).1
  rw [firstCycle_of_good (x := ⟨holdOnePath v y.1, isRegLL_holdOnePath v y.2⟩) h0
    (by rw [hret]; exact WithTop.coe_ne_top)]
  show (glue (holdOnePath v y.1) (retLen (holdOnePath v y.1)) cem,
    retLen (holdOnePath v y.1)) = (withHold 1 c).1
  rw [hlen, hp, glue_glue_cem_self (withHold 1 c).2.killed]

/-! ### 3. Transport to the first-cycle law: (R4) -/

theorem indepFun_of_val_right {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {q : β → Prop} {μ : Measure Ω} {f : Ω → α} {g : Ω → {b // q b}}
    (h : IndepFun f (fun ω => (g ω).1) μ) : IndepFun f g μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  obtain ⟨C, hC, rfl⟩ := ht
  exact h s C hs hC

theorem measurable_withHold_one : Measurable (withHold (v := v) 1) :=
  (measurable_withHold (v := v)).comp (measurable_const.prodMk measurable_id)

/-- **(R4) at the actual first-cycle law**: the holding at the start slot is independent of the
excursion. -/
theorem holdExcIndep_firstCycleLaw (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env} (he : e ∈ G) {n : ℕ}
    (hn : (e.val.1 n).isSome) : HoldExcIndep (firstCycleLaw G hwalk n e) := by
  classical
  have := nontrivial_vertex e
  have hw := isReflectedWalk_areaFamily e (hwalk e he)
  have hconn := decode_connected e
  obtain ⟨g, hgm, hg, hμ, hν⟩ := exists_sample_lift G hwalk he hn
  have hgood := ae_good_pair_of_lift G hwalk he hn hgm hμ
  have hhold := ae_exitTime_eq_holdTime hn hg (hgood.mono fun _ h => h.1)
  have hρm : AEMeasurable (exitTime (areaFamily e).X ⟨n, hn⟩) ((areaFamily e).P ⟨n, hn⟩) :=
    (hw ⟨n, hn⟩).2.2.2.2.1.1
  have hfm : AEMeasurable (futureAt (areaFamily e).X (exitTime (areaFamily e).X ⟨n, hn⟩))
      ((areaFamily e).P ⟨n, hn⟩) :=
    aemeasurable_futureAt' (areaFamily e).measurable_X (hw ⟨n, hn⟩).2.2.1 (hw ⟨n, hn⟩).2.2.2.1 hρm
  -- the post-exit label path is a.s. regular
  have hreg : ∀ᵐ ω ∂(areaFamily e).P ⟨n, hn⟩, IsRegLL (labelTraj (hfm.mk _ ω)) := by
    filter_upwards [hfm.ae_eq_mk, ae_isRegLL_label e (hwalk e he) ⟨n, hn⟩] with ω h1 h2
    rw [← h1]
    exact isRegLL_shiftBy h2 (exitTime (areaFamily e).X ⟨n, hn⟩ ω).untopA
  obtain ⟨g', hg'm, hg'⟩ := exists_lift_fun ((areaFamily e).P ⟨n, hn⟩)
    (f := fun ω => labelTraj (hfm.mk _ ω)) (measurable_labelTraj.comp hfm.measurable_mk) hreg
    isRegLL_cem
  -- the sample-space independence, carried to the lifts
  have hind := indepFun_exitTime_futureAt hw hconn (⟨n, hn⟩ : Vertex e.val)
  have h1 : IndepFun (exitTime (areaFamily e).X ⟨n, hn⟩)
      (fun ω => labelTraj (futureAt (areaFamily e).X (exitTime (areaFamily e).X ⟨n, hn⟩) ω))
      ((areaFamily e).P ⟨n, hn⟩) :=
    hind.comp measurable_id measurable_labelTraj
  have h2 : IndepFun (exitTime (areaFamily e).X ⟨n, hn⟩) (fun ω => (g' ω).1)
      ((areaFamily e).P ⟨n, hn⟩) := by
    refine h1.congr EventuallyEq.rfl ?_
    filter_upwards [hfm.ae_eq_mk, hg'] with ω ha hb
    rw [hb, ← ha]
  have h3 : IndepFun (fun ω => (exitTime (areaFamily e).X ⟨n, hn⟩ ω).untopA)
      (fun ω => exitCycle n (g' ω)) ((areaFamily e).P ⟨n, hn⟩) :=
    (indepFun_of_val_right h2).comp WithTop.measurable_untopA (measurable_exitCycle n)
  have h4 : IndepFun (holdTime ∘ (firstCycle n ∘ g)) (withHold 1 ∘ (firstCycle n ∘ g))
      ((areaFamily e).P ⟨n, hn⟩) := by
    refine h3.congr ?_ ?_
    · filter_upwards [hhold] with ω hω
      show (exitTime (areaFamily e).X ⟨n, hn⟩ ω).untopA = holdTime (firstCycle n (g ω))
      rw [hω]
      rfl
    · filter_upwards [hgood, hhold, hfm.ae_eq_mk, hg', hg] with ω hgd hω ha hb hc
      show exitCycle n (g' ω) = withHold 1 (firstCycle n (g ω))
      refine exitCycle_eq_withHold (firstCycle n (g ω)) hgd.2.1 ?_
      rw [← path_eq_glue_of_good hgd.1, hb, ← ha]
      funext s
      show ((areaFamily e).X (s + (exitTime (areaFamily e).X ⟨n, hn⟩ ω).untopA) ω).map
          Subtype.val = (g ω).1 (s + holdTime (firstCycle n (g ω)))
      rw [hω, hc]
      rfl
  rw [HoldExcIndep, hν]
  exact indepFun_map_of_comp ((measurable_firstCycle n).comp hgm) measurable_holdTime
    measurable_withHold_one h4

end ReflectedGMS.CycleHolding
