/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CycleHoldingStraddle at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CycleDecompositionRegeneration

/-!
# (R5) at the actual walk: the first-cycle holding is exponential, and the straddle is `≪`

`CycleDecompositionLaw.StraddleAbsCont ν` asks that the law of the sum of two independent
holdings of `ν` be absolutely continuous w.r.t. the law of one holding.  At the actual first-cycle
law `ν = firstCycleLaw G hwalk n e` (environment on the gate, slot `n` present) this is proved
here, with no hypothesis:

* `straddle_absCont_expNN` (generic): for `r > 0`, with `expNN r` the rate-`r` exponential law
  carried to `ℝ≥0`, `(expNN r ⊗ expNN r).map (+) ≪ expNN r` (`Exp ∗ Exp = Γ(2)` is `≪` Lebesgue on
  `[0,∞)`, which is `≪ Exp`; proved by Tonelli and translation invariance, no Gamma density);
* `hittingAfter_exit_eq_holdTime` (pathwise): on a good path, the holding time of the first cycle
  is the first exit time from the start;
* `ae_exitTime_eq_holdTime`: under the sample law, the property-(iii) exit time `exitTime X z`
  equals the holding of the first cycle of the lifted label path, a.s.;
* `map_holdTime_firstCycleLaw`: `ν.map holdTime = expNN (areaRate (decode e) z)` (property (iii));
* **`straddleAbsCont_firstCycleLaw`**: (R5) at the actual first-cycle law.
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

/-! ### 1. The exponential straddle (generic) -/

/-- The exponential law of rate `r`, carried to `ℝ≥0`. -/
noncomputable def expNN (r : ℝ) : Measure ℝ≥0 := (expMeasure r).map Real.toNNReal

theorem aemeasurable_exponentialPDF (r : ℝ) : AEMeasurable (exponentialPDF r) volume :=
  (ENNReal.measurable_ofReal.comp (measurable_exponentialPDFReal r)).aemeasurable

/-- The exponential law lives on `[0,∞)` and is `≪` Lebesgue there. -/
theorem expMeasure_absCont_restrict_Ici (r : ℝ) :
    expMeasure r ≪ volume.restrict (Ici (0 : ℝ)) := by
  intro s hs
  rw [Measure.restrict_apply' measurableSet_Ici] at hs
  show (volume.withDensity (exponentialPDF r)) s = 0
  rw [withDensity_apply_eq_zero' (aemeasurable_exponentialPDF r)]
  refine measure_mono_null ?_ hs
  intro x hx
  refine ⟨hx.2, ?_⟩
  show (0 : ℝ) ≤ x
  by_contra hneg
  exact hx.1 (exponentialPDF_of_neg (not_le.1 hneg))

/-- Lebesgue on `[0,∞)` is `≪` the exponential law of a positive rate. -/
theorem volume_inter_Ici_eq_zero {r : ℝ} (hr : 0 < r) {s : Set ℝ} (hs : expMeasure r s = 0) :
    volume (s ∩ Ici (0 : ℝ)) = 0 := by
  have hs' : (volume.withDensity (exponentialPDF r)) s = 0 := hs
  have h := (withDensity_apply_eq_zero' (aemeasurable_exponentialPDF r)).1 hs'
  refine measure_mono_null ?_ h
  intro x hx
  refine ⟨?_, hx.1⟩
  show exponentialPDF r x ≠ 0
  rw [exponentialPDF_of_nonneg hx.2]
  exact (ENNReal.ofReal_pos.2 (mul_pos hr (Real.exp_pos _))).ne'

/-- **`Exp ∗ Exp ≪ Exp` on `ℝ≥0`.** -/
theorem straddle_absCont_expNN {r : ℝ} (hr : 0 < r) :
    ((expNN r).prod (expNN r)).map (fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2) ≪ expNN r := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have : IsFiniteMeasure (expNN r) := by unfold expNN; infer_instance
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  have hadd : Measurable fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2 := measurable_fst.add measurable_snd
  have hA'0 : expMeasure r (Real.toNNReal ⁻¹' A) = 0 := by
    rw [expNN, Measure.map_apply measurable_real_toNNReal hA] at hA0
    exact hA0
  have hvol := volume_inter_Ici_eq_zero hr hA'0
  rw [Measure.map_apply hadd hA, Measure.prod_apply (hadd hA)]
  have h0 : ∀ a : ℝ≥0,
      expNN r (Prod.mk a ⁻¹' ((fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2) ⁻¹' A)) = 0 := by
    intro a
    have hm : MeasurableSet (Prod.mk a ⁻¹' ((fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2) ⁻¹' A)) :=
      measurable_prodMk_left (hadd hA)
    rw [expNN, Measure.map_apply measurable_real_toNNReal hm]
    refine expMeasure_absCont_restrict_Ici r ?_
    rw [Measure.restrict_apply' measurableSet_Ici]
    refine measure_mono_null (fun y hy => ?_)
      ((measure_preimage_add volume (a : ℝ) (Real.toNNReal ⁻¹' A ∩ Ici (0 : ℝ))).trans hvol)
    have hy0 : (0 : ℝ) ≤ y := hy.2
    have hyA : a + y.toNNReal ∈ A := hy.1
    refine ⟨?_, ?_⟩
    · show ((a : ℝ) + y).toNNReal ∈ A
      rw [Real.toNNReal_add (NNReal.coe_nonneg a) hy0, Real.toNNReal_coe]
      exact hyA
    · show (0 : ℝ) ≤ (a : ℝ) + y
      exact add_nonneg (NNReal.coe_nonneg a) hy0
  simp only [h0, lintegral_zero]

/-! ### 2. The holding of the first cycle is the first exit (pathwise) -/

variable {v : ℕ}

theorem firstCycle_apply_of_lt {x : RegLL} (h0 : x.1 0 = some v) (hr : fwdReturn x.1 ≠ ⊤)
    {t : ℝ≥0} (ht : t < (firstCycle v x).1.2) : (firstCycle v x).1.1 t = x.1 t := by
  have hc := firstCycle_of_good h0 hr
  rw [hc] at ht ⊢
  exact glue_of_lt ht

/-- **On a good path the first-cycle holding is the first exit time from the start.** -/
theorem hittingAfter_exit_eq_holdTime {x : RegLL} (h0 : x.1 0 = some v)
    (hr : fwdReturn x.1 ≠ ⊤) :
    MeasureTheory.hittingAfter (coord (V := ℕ)) {s : Option ℕ | s ≠ some v} 0 x.1 =
      ((holdTime (firstCycle v x) : ℝ≥0) : WithTop ℝ≥0) := by
  obtain ⟨-, hHL, hbef, haft⟩ := cyc_hold (firstCycle v x)
  refine hittingAfter_eq zero_le ?_ ?_
  · show x.1 (holdTime (firstCycle v x)) ≠ some v
    rw [← firstCycle_apply_of_lt h0 hr hHL]
    exact haft _ le_rfl hHL
  · intro j _ hj hmem
    apply hmem
    rw [← firstCycle_apply_of_lt h0 hr (hj.trans hHL)]
    exact hbef j hj

/-! ### 3. The exit time of the actual walk in the label coding -/

theorem exitTime_eq_hittingAfter_label {e : Env} {n : ℕ} (hn : (e.val.1 n).isSome)
    (ω : (areaFamily e).Ω) :
    exitTime (areaFamily e).X ⟨n, hn⟩ ω =
      MeasureTheory.hittingAfter (coord (V := ℕ)) {s : Option ℕ | s ≠ some n} 0
        (labelTraj ((areaFamily e).trajectory ω)) := by
  have hiff : ∀ t, (areaFamily e).trajectory ω t ∈
      {s : Option (Vertex e.val) | s ≠ some ⟨n, hn⟩} ↔
      labelTraj ((areaFamily e).trajectory ω) t ∈ {s : Option ℕ | s ≠ some n} := by
    intro t
    show (areaFamily e).trajectory ω t ≠ some ⟨n, hn⟩ ↔
      ((areaFamily e).trajectory ω t).map Subtype.val ≠ some n
    rcases (areaFamily e).trajectory ω t with _ | u
    · simp
    · simp [Subtype.ext_iff]
  rw [hittingAfter_label hiff 0]
  rfl

/-- The a.s. good-pair event of a lift of the slot law (the path and its post-cycle shift are
both good). -/
theorem ae_good_pair_of_lift (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    {e : Env} (he : e ∈ G) {n : ℕ} (hn : (e.val.1 n).isSome) {g : (areaFamily e).Ω → RegLL}
    (hgm : Measurable g) (hμ : regSlotLaw G hwalk n e = ((areaFamily e).P ⟨n, hn⟩).map g) :
    ∀ᵐ ω ∂(areaFamily e).P ⟨n, hn⟩, Good n (g ω) ∧ Good n (nx (g ω)) := by
  have hFR := forwardRegeneration_regSlotLaw G hwalk he hn
  have h2 : ∀ᵐ x ∂regSlotLaw G hwalk n e, Good n (nx x) := by
    have h := hFR.good
    rw [← hFR.shift] at h
    exact ae_of_ae_map measurable_nx.aemeasurable h
  have h12 : ∀ᵐ x ∂regSlotLaw G hwalk n e, Good n x ∧ Good n (nx x) := by
    filter_upwards [hFR.good, h2] with x h1 h2 using ⟨h1, h2⟩
  rw [hμ] at h12
  exact ae_of_ae_map hgm.aemeasurable h12

/-- **The property-(iii) exit time is the first-cycle holding, a.s.** -/
theorem ae_exitTime_eq_holdTime {e : Env} {n : ℕ} (hn : (e.val.1 n).isSome)
    {g : (areaFamily e).Ω → RegLL}
    (hg : ∀ᵐ ω ∂(areaFamily e).P ⟨n, hn⟩, (g ω).1 = labelTraj ((areaFamily e).trajectory ω))
    (hgood : ∀ᵐ ω ∂(areaFamily e).P ⟨n, hn⟩, Good n (g ω)) :
    ∀ᵐ ω ∂(areaFamily e).P ⟨n, hn⟩, exitTime (areaFamily e).X ⟨n, hn⟩ ω =
      ((holdTime (firstCycle n (g ω)) : ℝ≥0) : WithTop ℝ≥0) := by
  filter_upwards [hg, hgood] with ω h1 h2
  rw [exitTime_eq_hittingAfter_label hn ω, ← h1]
  exact hittingAfter_exit_eq_holdTime h2.1 h2.2

/-! ### 4. The holding law of the first cycle, and (R5) -/

/-- **The first-cycle holding law is the exponential law of the exit rate** (property (iii)). -/
theorem map_holdTime_firstCycleLaw (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env} (he : e ∈ G) {n : ℕ}
    (hn : (e.val.1 n).isSome) :
    (firstCycleLaw G hwalk n e).map (holdTime (v := n)) =
      expNN (areaRate (decode e) ⟨n, hn⟩) := by
  have := nontrivial_vertex e
  have hw := isReflectedWalk_areaFamily e (hwalk e he)
  obtain ⟨g, hgm, hg, hμ, hν⟩ := exists_sample_lift G hwalk he hn
  have hgood := ae_good_pair_of_lift G hwalk he hn hgm hμ
  have hhold := ae_exitTime_eq_holdTime hn hg (hgood.mono fun _ h => h.1)
  obtain ⟨hρm, -, -, hlaw, -⟩ := (hw ⟨n, hn⟩).2.2.2.2.1
  have hcomp : Measurable (firstCycle n ∘ g) := (measurable_firstCycle n).comp hgm
  rw [hν, Measure.map_map measurable_holdTime hcomp]
  have hae : (holdTime ∘ (firstCycle n ∘ g)) =ᵐ[(areaFamily e).P ⟨n, hn⟩]
      (WithTop.untopA ∘ exitTime (areaFamily e).X ⟨n, hn⟩) := by
    filter_upwards [hhold] with ω hω
    show holdTime (firstCycle n (g ω)) = (exitTime (areaFamily e).X ⟨n, hn⟩ ω).untopA
    rw [hω]
    rfl
  rw [Measure.map_congr hae,
    ← AEMeasurable.map_map_of_aemeasurable WithTop.measurable_untopA.aemeasurable hρm, hlaw,
    Measure.map_map WithTop.measurable_untopA measurable_toWithTop]
  rfl

/-- **(R5) at the actual first-cycle law.** -/
theorem straddleAbsCont_firstCycleLaw (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env} (he : e ∈ G) {n : ℕ}
    (hn : (e.val.1 n).isSome) : StraddleAbsCont (firstCycleLaw G hwalk n e) := by
  have := nontrivial_vertex e
  unfold StraddleAbsCont
  rw [map_holdTime_firstCycleLaw G hwalk he hn]
  exact straddle_absCont_expNN (areaRate_pos e ⟨n, hn⟩)

end ReflectedGMS.CycleHolding
