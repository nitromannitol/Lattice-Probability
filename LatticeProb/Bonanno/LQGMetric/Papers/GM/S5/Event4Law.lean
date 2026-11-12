/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event4Law at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Main

/-!
# GM Lemma 5.6: the probability of `F_r(z)` does not depend on the GFF (task P2-M2M7)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`.
GM Lemma 5.6 (l. 2940–2958) gives a *deterministic* tube `V_r(z)` (decision D92); in the proof
(l. 2975–2979) `𝒦_r(z)` is chosen by pigeonhole for "the" whole-plane GFF `h`. In our convention
the probability bound is required for every whole-plane GFF on every probability space, so we need
that `P[h ∈ F_r(z)]` is the same for all of them: GM's argument of l. 1200–1203 and l. 3001–3004
("the occurrence of `F_r(z)` is unaffected by scaling each of `D_h` and `D̃_h` by the same constant
factor … `F_r(z)` is determined by `h`, viewed modulo additive constant"), for the event
`tubeEvent`, exactly as `prob_attainedLow_eq` (`GoodRadiiLaw.lean`):

* `F_r(z)` is invariant under adding constants (`mem_tubeEvent_of_scale` and Weyl scaling);
* it agrees with its universally measurable Borel form `tubeEventB` when `D̃_g ∈ lenSet`
  (`mem_tubeEvent_iff_B`, `uMeasurableSet_tubeEventB`), which holds a.s. for the recentred field
  (`ae_mem_lenSet`, from GM.S1.1);
* the law of `h` recentred by `⟨h, ρ⟩` is unique (`map_comp_eq_of_sigma0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent GFFInv GFFLaw

/-- `P[h ∈ F_r(z)]` through the law of the recentred field -/
lemma prob_tubeEvent_eq_map (h38 : DFGPSLem3_8) {γ : ℝ} {D D' : DistC → ContMetric}
    {c : ℝ → ℝ} (hPS : PairSetting γ D D' c) (cs Cs c₁ η b ε r : ℝ) (z : ℂ) {V : Set ℂ}
    (hV : IsOpen V) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    P (h ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V) =
      P.map (recenter detRho ∘ h) (tubeEventB D D' cs Cs c₁ η b ε r z V) := by
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := hPS
  have hle : sigma0 ≤ (inferInstance : MeasurableSpace DistC) := by
    rw [sigma0, ← measurable_iff_comap_le]
    exact measurable_pi_iff.2 fun φ => measurable_pair φ.1
  have hrm : Measurable (recenter detRho) :=
    (measurable_recenter_sigma0 integral_detRho).mono hle le_rfl
  have hk : IsWholePlaneGFF (fun ω => addConst (h ω) (-(h ω detRho))) P :=
    hh.addConst ((measurable_pair detRho).comp hh.measurable).neg
  have hgp := Tight.isGFFPlusCont_of_wp hh
  have e1 : P (h ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V) =
      P ((recenter detRho ∘ h) ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V) := by
    refine measure_congr ?_
    filter_upwards [hD.ae_dist_addConst hgp, hD'.ae_dist_addConst hgp] with ω h1 h2
    exact propext (mem_tubeEvent_of_scale (Real.exp_pos _) (h1 _) (h2 _)).symm
  have e2 : P ((recenter detRho ∘ h) ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V) =
      P ((recenter detRho ∘ h) ⁻¹' tubeEventB D D' cs Cs c₁ η b ε r z V) := by
    refine measure_congr ?_
    filter_upwards [ae_mem_lenSet h38 hγ0 hγ2 hD' P _ hk] with ω hω
    exact propext (mem_tubeEvent_iff_B hV hω)
  rw [e1, e2, Measure.map_apply₀ (hrm.comp hh.measurable).aemeasurable
    (uMeasurableSet_tubeEventB hD.measurable hD'.measurable cs Cs c₁ η b ε r z hV _ inferInstance)]

/-- **`P[h ∈ F_r(z)]` is the same for all whole-plane GFFs** (GM l. 1200–1203, 3001–3004), for
every open `V` -/
theorem prob_tubeEvent_eq (h38 : DFGPSLem3_8) {γ : ℝ} {D D' : DistC → ContMetric}
    {c : ℝ → ℝ} (hPS : PairSetting γ D D' c) (cs Cs c₁ η b ε r : ℝ) (z : ℂ) {V : Set ℂ}
    (hV : IsOpen V) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : IsWholePlaneGFF h' P') :
    P (h ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V) =
      P' (h' ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V) := by
  rw [prob_tubeEvent_eq_map h38 hPS cs Cs c₁ η b ε r z hV P h hh,
    prob_tubeEvent_eq_map h38 hPS cs Cs c₁ η b ε r z hV P' h' hh',
    map_comp_eq_of_sigma0 (measurable_recenter_sigma0 integral_detRho) hh hh']

end LQGMetric.GM
