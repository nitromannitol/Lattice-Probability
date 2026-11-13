/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CompactProcessFiltration at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedCompactProcess
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompensatedPotentialL2
import Mathlib.Probability.Process.Adapted

/-!
# Adaptedness of the compact reflected process

The compact process is defined by right limits of raw samples.  At time `t`,
the defining sample sequence is eventually earlier than every `u > t`.
Consequently its limit is measurable for every `PF.naturalFiltration u`, and
hence for mathlib's right continuation of the natural filtration.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

private theorem measurable_X_naturalFiltration_of_le
    (PF : ProcessFamily V) {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[PF.naturalFiltration t] (PF.X s) := by
  have hs : Measurable[PF.naturalFiltration s] (PF.X s) := by
    change Measurable[pastSigma PF.X s] (PF.X s)
    intro A hA
    apply measurableSet_pastSigma_iff.mpr
    refine ⟨{p | p ⟨s, by simp⟩ ∈ A}, ?_, rfl⟩
    exact hA.preimage (measurable_pi_apply _)
  exact hs.mono (PF.naturalFiltration.mono hst) le_rfl

private theorem stronglyMeasurable_reflectedCompactSample_of_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) {s t : ℝ≥0} (hst : s ≤ t) :
    StronglyMeasurable[PF.naturalFiltration t]
      (reflectedCompactSample G m hm PF default s) := by
  let E := ResolventCompactSpace.Space G m hm
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have he : Measurable (fun q : Option V ↦
      (ResolventCompactSpace.vertex G m hm (q.getD default) : E)) :=
    measurable_of_countable _
  exact (he.comp (measurable_X_naturalFiltration_of_le PF hst)).stronglyMeasurable

private theorem stronglyMeasurable_reflectedCompactProcess_before
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) {t u : ℝ≥0} (htu : t < u) :
    StronglyMeasurable[PF.naturalFiltration u]
      (reflectedCompactProcess G m hm PF default t) := by
  let E := ResolventCompactSpace.Space G m hm
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : Nonempty E := ⟨ResolventCompactSpace.vertex G m hm default⟩
  let q : ℕ → ℝ≥0 := supportedRightSequence globalDyadicSupport
    globalDyadicSupport_nhdsWithin_Ioi_neBot t
  let g : ℕ → PF.Ω → E := fun n ↦
    if h : q n < u then reflectedCompactSample G m hm PF default (q n)
    else fun _ ↦ ResolventCompactSpace.vertex G m hm default
  letI : MeasurableSpace PF.Ω := PF.naturalFiltration u
  have hg : ∀ n, StronglyMeasurable (g n) := by
    intro n
    dsimp only [g]
    split_ifs with h
    · exact stronglyMeasurable_reflectedCompactSample_of_le G m hm PF default h.le
    · exact stronglyMeasurable_const
  have hq_tendsto : Tendsto q atTop (𝓝 t) :=
    (tendsto_supportedRightSequence globalDyadicSupport
      globalDyadicSupport_nhdsWithin_Ioi_neBot t).mono_right nhdsWithin_le_nhds
  have hq : ∀ᶠ n in atTop, q n < u := hq_tendsto.eventually_lt_const htu
  have hlim : StronglyMeasurable
      (fun ω ↦ limUnder atTop (fun n ↦ g n ω)) :=
    StronglyMeasurable.limUnder hg
  change StronglyMeasurable[PF.naturalFiltration u]
    (supportedRightExtension globalDyadicSupport
      globalDyadicSupport_nhdsWithin_Ioi_neBot
      (reflectedCompactSample G m hm PF default) t)
  unfold supportedRightExtension
  have heq : (fun ω ↦ limUnder atTop
      (fun n ↦ reflectedCompactSample G m hm PF default (q n) ω)) =
      fun ω ↦ limUnder atTop (fun n ↦ g n ω) := by
    funext ω
    unfold limUnder
    congr 1
    apply Filter.map_congr
    filter_upwards [hq] with n hn
    simp [g, hn]
  simpa only [q, heq] using hlim

/-- The law-independent compact reflected process is strongly adapted to
mathlib's right continuation of its raw natural filtration. -/
theorem stronglyAdapted_reflectedCompactProcess_rightCont
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) :
    StronglyAdapted PF.naturalFiltration.rightCont
      (reflectedCompactProcess G m hm PF default) := by
  intro t
  let E := ResolventCompactSpace.Space G m hm
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  apply Measurable.stronglyMeasurable
  intro A hA
  rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro u
  rw [MeasurableSpace.measurableSet_iInf]
  intro htu
  exact (stronglyMeasurable_reflectedCompactProcess_before
    G m hm PF default htu).measurable hA

end ReflectedGMS
