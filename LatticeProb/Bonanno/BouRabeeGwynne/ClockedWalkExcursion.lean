/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ClockedWalkExcursion at commit fdb5cad;
   local imports and toolchain compatibility details are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkExcursionKernel
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStoppedHistory

/-! The actual walk excursion retains its integer duration and all embedded
vertices. Its normalized-curve and endpoint pushforwards are the previously
defined genuine laws; first vertex exit remains available after coupling. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval BigOperators

namespace BouRabeeGwynne

abbrev ClockedWalkExcursion (d : ℕ) := ℕ × (ℕ → Euc d)

namespace ClockedWalkExcursion

variable {d : ℕ}

def start (e : ClockedWalkExcursion d) : Euc d := e.2 0

def endPoint (e : ClockedWalkExcursion d) : Euc d := e.2 e.1

noncomputable def curve (e : ClockedWalkExcursion d) : C(unitInterval, Euc d) :=
  polygonalCurve id e.2 e.1

def constant (z : Euc d) : ClockedWalkExcursion d := (0, fun _ => z)

lemma measurable_start : Measurable (start (d := d)) :=
  (measurable_pi_apply 0).comp measurable_snd

lemma measurable_endPoint : Measurable (endPoint (d := d)) :=
  measurable_from_prod_countable_right fun n => measurable_pi_apply n

lemma measurable_curve : Measurable (curve (d := d)) := by
  apply measurable_from_prod_countable_right
  intro n
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun ω : ℕ → Euc d => ω 0 + ∑ k ∈ Finset.range n,
    max (0 : ℝ) (min 1 ((n : ℝ) * (t : ℝ) - (k : ℝ))) • (ω (k + 1) - ω k))
  fun_prop

lemma measurable_constant : Measurable (constant (d := d)) :=
  measurable_const.prodMk (Measurable.of_eval fun _ => measurable_id)

@[simp] lemma curve_start (e : ClockedWalkExcursion d) : curve e 0 = start e :=
  polygonalCurve_start id e.2 e.1

@[simp] lemma curve_endPoint (e : ClockedWalkExcursion d) : curve e 1 = endPoint e :=
  polygonalCurve_end id e.2 e.1

@[simp] lemma constant_start (z : Euc d) : start (constant z) = z := rfl

lemma polygonalCurve_congr_prefix {ω ξ : ℕ → Euc d} {m : ℕ}
    (h : ∀ k ≤ m, ω k = ξ k) : polygonalCurve id ω m = polygonalCurve id ξ m := by
  apply ContinuousMap.ext
  intro t
  change ω 0 + ∑ k ∈ Finset.range m,
      max (0 : ℝ) (min 1 ((m : ℝ) * (t : ℝ) - (k : ℝ))) • (ω (k + 1) - ω k) =
    ξ 0 + ∑ k ∈ Finset.range m,
      max (0 : ℝ) (min 1 ((m : ℝ) * (t : ℝ) - (k : ℝ))) • (ξ (k + 1) - ξ k)
  rw [h 0 (Nat.zero_le m)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k < m := Finset.mem_range.mp hk
  rw [h k hkm.le, h (k + 1) (Nat.succ_le_of_lt hkm)]

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def ofWalk (pos : V → Euc d) (B : Set V) (ω : ℕ → V) :
    ClockedWalkExcursion d :=
  let m := (FiniteConductanceNetwork.exitTime B ω).untopD 0
  (m, fun k => pos (ω (min k m)))

lemma measurable_ofWalk (pos : V → Euc d) (B : Set V) : Measurable (ofWalk pos B) := by
  have hp : Measurable pos := measurable_of_finite _
  have hm : Measurable (fun p : ℕ × (ℕ → V) => (p.1, fun k => pos (p.2 k))) :=
    measurable_fst.prodMk (Measurable.of_eval fun k =>
      hp.comp ((measurable_pi_apply k).comp measurable_snd))
  exact hm.comp (FiniteConductanceNetwork.measurable_observedHistory
    (FiniteConductanceNetwork.exitTime_isStoppingTime B).measurable')

set_option linter.unusedSectionVars false in
@[simp] lemma start_ofWalk (pos : V → Euc d) (B : Set V) (ω : ℕ → V) :
    start (ofWalk pos B ω) = pos (ω 0) := by simp [start, ofWalk]

set_option linter.unusedSectionVars false in
@[simp] lemma endPoint_ofWalk (pos : V → Euc d) (B : Set V) (ω : ℕ → V) :
    endPoint (ofWalk pos B ω) = pos (FiniteConductanceNetwork.exitVertex B ω) := by
  simp [endPoint, ofWalk, FiniteConductanceNetwork.exitVertex]

set_option linter.unusedSectionVars false in
lemma curve_ofWalk (pos : V → Euc d) (B : Set V) (ω : ℕ → V) :
    curve (ofWalk pos B ω) = stoppedPolygonalRepresentative pos B ω := by
  let m := (FiniteConductanceNetwork.exitTime B ω).untopD 0
  change polygonalCurve id (fun k => pos (ω (min k m))) m = polygonalCurve pos ω m
  calc
    _ = polygonalCurve id (fun k => pos (ω k)) m :=
      polygonalCurve_congr_prefix (fun k hk => by rw [min_eq_left hk])
    _ = _ := rfl

end ClockedWalkExcursion

namespace FiniteConductanceNetwork

variable {d : ℕ} {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (N : FiniteConductanceNetwork V)

noncomputable def clockedWalkExcursionKernel (pos : V → Euc d) (B : Set V)
    (hpos : ∀ v ∈ B, 0 < N.totalConductance v) : Kernel V (ClockedWalkExcursion d) where
  toFun v := (N.trajectoryLaw B hpos v).map (ClockedWalkExcursion.ofWalk pos B)
  measurable' := measurable_of_finite _

instance clockedWalkExcursionKernel_isMarkov (pos : V → Euc d) (B : Set V)
    (hpos : ∀ v ∈ B, 0 < N.totalConductance v) :
    IsMarkovKernel (N.clockedWalkExcursionKernel pos B hpos) where
  isProbabilityMeasure _v :=
    (Measure.isProbabilityMeasure_map_iff
      (ClockedWalkExcursion.measurable_ofWalk pos B).aemeasurable).mpr inferInstance

lemma clockedWalkExcursionKernel_curve (pos : V → Euc d) (B : Set V)
    (hpos : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    (N.clockedWalkExcursionKernel pos B hpos v).map ClockedWalkExcursion.curve =
      N.walkExcursionKernel pos B hpos v := by
  change ((N.trajectoryLaw B hpos v).map (ClockedWalkExcursion.ofWalk pos B)).map
    ClockedWalkExcursion.curve =
      (N.trajectoryLaw B hpos v).map (stoppedPolygonalRepresentative pos B)
  rw [Measure.map_map ClockedWalkExcursion.measurable_curve
    (ClockedWalkExcursion.measurable_ofWalk pos B)]
  congr 1
  funext ω
  exact ClockedWalkExcursion.curve_ofWalk pos B ω

lemma clockedWalkExcursionKernel_ae_start (pos : V → Euc d) (B : Set V)
    (hpos : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ e ∂N.clockedWalkExcursionKernel pos B hpos v, ClockedWalkExcursion.start e = pos v := by
  change ∀ᵐ e ∂(N.trajectoryLaw B hpos v).map (ClockedWalkExcursion.ofWalk pos B), _
  apply (ae_map_iff (ClockedWalkExcursion.measurable_ofWalk pos B).aemeasurable
    (measurableSet_eq_fun ClockedWalkExcursion.measurable_start measurable_const)).mpr
  filter_upwards [N.trajectoryLaw_ae_start B hpos v] with ω hω
  simp only [ClockedWalkExcursion.start_ofWalk, hω]

lemma clockedWalkExcursionKernel_endPoint (pos : V → Euc d) (B : Set V)
    (hpos : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    (N.clockedWalkExcursionKernel pos B hpos v).map ClockedWalkExcursion.endPoint =
      (N.discreteHarmonicMeasure B hpos v).map pos := by
  change ((N.trajectoryLaw B hpos v).map (ClockedWalkExcursion.ofWalk pos B)).map
    ClockedWalkExcursion.endPoint = ((N.trajectoryLaw B hpos v).map (exitVertex B)).map pos
  rw [Measure.map_map ClockedWalkExcursion.measurable_endPoint
      (ClockedWalkExcursion.measurable_ofWalk pos B),
    Measure.map_map (measurable_of_finite pos) (measurable_exitVertex B)]
  congr 1
  funext ω
  exact ClockedWalkExcursion.endPoint_ofWalk pos B ω

end FiniteConductanceNetwork
end BouRabeeGwynne
