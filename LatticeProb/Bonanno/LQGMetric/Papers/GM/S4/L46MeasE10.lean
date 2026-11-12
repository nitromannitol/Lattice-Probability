/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE9
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det7
import Mathlib.Data.Rat.Denumerable
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Sel

/-!
# `hnullE`, `hnullW`, `hnullGW` of `gm_L4_5_of_null'` (task P2-E3d)

GM = Gwynne–Miller, arXiv:1905.00383v3, Lemma 4.5 (l. 1655–1688). The events `gmEmSet`,
`gmWSet`, `gmGeodWSet` (P2-E2R, P2-E2S) intersected with the hull events are preimages under
`D` of sets of metrics that are analytic on `lenSet` (`gm_arcRelAn`, `gm_arcOfRelAn`, geodesics
as `C([0,1], ℂ)` witnesses, `gmE_hullAn`), hence null-measurable for the law of `h`
(`gmE_nullMeas_of_an`). Own descriptive-set-theory argument (D65); GM do not discuss
measurability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

lemma gmE_measurableSet_half (j : Bool × ℚ) : MeasurableSet (gmHalf j) := by
  unfold gmHalf
  split_ifs
  · exact measurableSet_lt measurable_const Complex.measurable_re
  · exact measurableSet_lt measurable_const Complex.measurable_im

theorem gmE_GWAn (𝕫 𝕨 : ℂ) (R c₀ c : ℝ) (u : unitInterval) (j : Bool × ℚ) :
    GMAnalyticOn lenSet {d : ContMetric | 𝕨 ∈ filledBall d 𝕫 (tauD d 𝕫 R * c) ∧
      ∃ Q : C(unitInterval, ℂ), IsGeod01 d 𝕫 𝕨 Q ∧
        geodL d 𝕫 𝕨 Q (tauD d 𝕫 R * c₀ * u) ∈ gmHalf j} := by
  have hτ := gm_measurable_tauB 𝕫 R
  have hcl : IsClosed {q : ContMetric × C(unitInterval, ℂ) | IsGeod01 q.1 𝕫 𝕨 q.2} := by
    have e : {q : ContMetric × C(unitInterval, ℂ) | IsGeod01 q.1 𝕫 𝕨 q.2} =
        {q | q.2 0 = 𝕫} ∩ ({q | q.2 1 = 𝕨} ∩ ⋂ s : unitInterval, ⋂ t : unitInterval,
          {q | q.1.1 (q.2 s, q.2 t) = |(t : ℝ) - s| * q.1.1 (𝕫, 𝕨)}) := by
      ext q; simp only [IsGeod01, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [e]
    refine (isClosed_eq ((continuous_eval_const 0).comp continuous_snd) continuous_const).inter
      ((isClosed_eq ((continuous_eval_const 1).comp continuous_snd) continuous_const).inter
        (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_eq ?_ ?_))
    · exact continuous_contMetric_apply.comp (continuous_fst.prodMk
        (((continuous_eval_const s).comp continuous_snd).prodMk
          ((continuous_eval_const t).comp continuous_snd)))
    · exact continuous_const.mul (continuous_contMetric_apply.comp
        (continuous_fst.prodMk continuous_const))
  have hg : Measurable fun q : ContMetric × C(unitInterval, ℂ) =>
      geodL q.1 𝕫 𝕨 q.2 (gmTauB 𝕫 R q.1 * c₀ * u) :=
    continuous_eval.measurable.comp (measurable_snd.prodMk
      ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).measurable.comp
      ((((hτ.comp measurable_fst).mul_const c₀).mul_const _).div
        ((measurable_apply (𝕫, 𝕨)).comp measurable_fst))))
  have A1 := gmAn_exists (L := lenSet) (gmAn_of_measurableSet
    (L := {q : ContMetric × C(unitInterval, ℂ) | q.1 ∈ lenSet})
    (A := {q : ContMetric × C(unitInterval, ℂ) | IsGeod01 q.1 𝕫 𝕨 q.2 ∧
      geodL q.1 𝕫 𝕨 q.2 (gmTauB 𝕫 R q.1 * c₀ * u) ∈ gmHalf j})
    (hcl.measurableSet.inter (hg (gmE_measurableSet_half j))))
  have A2 := gmAn_inter (gmAn_of_measurableSet (L := lenSet)
    (A := {d : ContMetric | 𝕨 ∈ filledBall d 𝕫 (gmTauB 𝕫 R d * c)})
    ((gmE_measurableSet_filledBall 𝕫).preimage
      (measurable_id'.prodMk ((hτ.mul_const c).prodMk measurable_const)))) A1
  refine gmAn_congr A2 fun d hd => ?_
  simp only [mem_ofPred_eq, mem_inter_iff, gm_tauD_eq_tauB hd]

/-- **`hnullGW`** (input of `gm_L4_5_of_null'`) -/
theorem gm_hnullGW (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (𝕫 𝕨 : ℂ) (R c₀ c : ℝ) (u : unitInterval) (j : Bool × ℚ)
    (n : ℕ) (s : Finset (ℤ × ℤ)) :
    NullMeasurableSet (gmGeodWSet D 𝕫 𝕨 R c₀ c u j ∩
      {g | dyadicHull n (gmKt D 𝕫 R c g) = LocalEvent.hullFin n s}) (P.map h) :=
  gmE_nullMeas_of_an hD.measurable hh.measurable.aemeasurable
    (ae_mem_lenSet h38 hγ hγ2 hD P h hh)
    (gmAn_inter (gmE_GWAn 𝕫 𝕨 R c₀ c u j) (gmE_hullAn 𝕫 R c n _))

end LQGMetric.GM
