/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bEvt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bCond4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.WeakStrong

/-!
# The events of Prop 4.3 at centre `z`: conditions (2) for `E`, invariance, conclusion
(task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Prop 4.3, l. 2846–2858.
* `aeEventIn_eventAt` : Prop 5.2 (A) for `h(· + z)` gives condition (2) of `GeoIterateHyp` for
  `E_r(z) = {g | g(· + z) ∈ E_r}` (`λ₁ = 1/4`, `λ₄ = 4`, `λ₅ = 5`): GM l. 2855, "By Property (A)".
* `eventAt_addConst_iff` : `E_r(z)` is unaffected by constants if `E_r` is (GM l. 2801).
* `frkE_concl` : on `𝔈_r^{𝕫,𝕨}(z)` the conclusion (4.4) of Prop 4.3 holds with `b = min(b₀, 1/2)`
  (GM l. 2852: "the conditions (4.4) hold on `𝔈` with `b = b₀`"; DV-B10: `P(s), P(t) ∈ B_{3r/2}(z)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `E_r(z) := {g | g(· + z) ∈ E_r}` -/
def eventAt (E : Set DistC) (z : ℂ) : Set DistC := {g | affineComp 1 z g ∈ E}

/-- condition (2) of `GeoIterateHyp` for `E_r(z)` from Prop 5.2 (A) for `h(· + z)` -/
theorem aeEventIn_eventAt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (E : Set DistC) (z : ℂ) (r : ℝ)
    (hA : AEEventIn P (fieldSigma (fun ω => addConst (affineComp 1 z (h ω))
        (-circleAvg (affineComp 1 z (h ω)) (5 * r) 0)) (annulus 0 (r / 4) (4 * r)))
      ((fun ω => affineComp 1 z (h ω)) ⁻¹' E)) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (5 * r) z))
      (annulus z (r / 4) (4 * r))) (h ⁻¹' eventAt E z) := by
  have hUV : ∀ y : ℂ, y ∈ annulus z (r / 4) (4 * r) ↔
      (1 : ℝ) • y + -z ∈ annulus 0 (r / 4) (4 * r) := fun y => by
    simp only [one_smul, annulus, TopologicalSpace.Opens.mem_mk, mem_ofPred_eq, sub_zero,
      ← sub_eq_add_neg]
    exact Iff.rfl
  have hle : fieldSigma (fun ω => addConst (affineComp 1 z (h ω))
        (-circleAvg (affineComp 1 z (h ω)) (5 * r) 0)) (annulus 0 (r / 4) (4 * r)) ≤
      fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (5 * r) z))
        (annulus z (r / 4) (4 * r)) := by
    refine (fieldSigma_le_affineComp one_pos hUV _).trans (le_of_eq ?_)
    congr 1
    funext ω
    rw [affineComp_addConst one_pos, affineComp_one_comp, neg_add_cancel, affineComp_one_zero,
      Tight.circleAvg_affineComp_one]
  obtain ⟨F, hF, hAF⟩ := hA
  exact ⟨F, hle F hF, hAF⟩

/-- the conclusion (4.4) of Prop 4.3 on `𝔈_r^{𝕫,𝕨}(z)` -/
lemma frkE_concl {D D' : DistC → ContMetric} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    {cs Cs c₂ b₀ Λ r : ℝ} (hr : 0 < r) {G : Set TestC} {z a a' : ℂ} {g : DistC}
    (hg : g ∈ frkE D D' sel cs Cs c₂ b₀ Λ r G z a a') :
    ∃ s t : unitInterval, s < t ∧
      sel a a' g s ∈ Metric.ball z (3 / 2 * r) ∧ sel a a' g t ∈ Metric.ball z (3 / 2 * r) ∧
      min b₀ (1 / 2) * r ≤ ‖sel a a' g s - sel a a' g t‖ ∧
      (D' g).1 (sel a a' g s, sel a a' g t) ≤ c₂ * (D g).1 (sel a a' g s, sel a a' g t) := by
  obtain ⟨s, t, -, hst, -, hs, ht, hb, hc, -⟩ := hg.1
  exact ⟨s, t, hst, hs, ht, le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le) hb, hc⟩

end LQGMetric.GM
