/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepShift at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepData
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-!
# GM Lemma 2.7: moving the configuration away from the unit circle

`Blueprint.LMLem2_1` (LM Lemma 2.1, case `V ∩ ∂𝔻 = ∅`) needs a field normalized by
`h_1(0) = 0` and a Markov domain disjoint from `∂𝔻`. GM apply the Markov property to
`U = ⋃_z B_{1+s}(z)` for an arbitrary configuration (l. 974). We translate: for
`h' = h(· + a) + k` (any random constant `k`), an event determined by
`(h − h_R(z))|_{B_1(z)}` is determined by `(h' − h'_R(z − a))|_{B_1(z − a)}`
(`aeEventIn_shift`). Own elementary bookkeeping (translation invariance of the whole-plane GFF is
`IsWholePlaneGFF.affineComp`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric

namespace LQGMetric.GM

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

lemma aeEventIn_of_ae_eq {X X' : Ω → DistC} (hXX : ∀ᵐ ω ∂P, X ω = X' ω) (V : Opens ℂ)
    {E : Set Ω} (hE : AEEventIn P (fieldSigma X V) E) : AEEventIn P (fieldSigma X' V) E := by
  obtain ⟨S, hS, hES⟩ := exists_preimage_of_aeEventIn hE
  refine ⟨(fun ω => restrictTo V (X' ω)) ⁻¹' S, ⟨S, hS, rfl⟩, hES.trans ?_⟩
  filter_upwards [hXX] with ω hω
  simp [hω]

lemma addConst_addConst (T : DistC) (a b : ℝ) : addConst (addConst T a) b = addConst T (a + b) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFInv.addConst_apply, GFFInv.addConst_apply, GFFInv.addConst_apply]
  ring

lemma testAffinePull_one_comp (a w : ℂ) (φ : TestC) :
    testAffinePull 1 a (testAffinePull 1 w φ) = testAffinePull 1 (w + a) φ := by
  ext y
  rw [testAffinePull_apply 1 a one_ne_zero, testAffinePull_apply 1 w one_ne_zero,
    testAffinePull_apply 1 (w + a) one_ne_zero]
  congr 1
  simp only [Complex.ofReal_one, div_one]; ring

lemma affineComp_one_comp (a w : ℂ) (g : DistC) :
    affineComp 1 w (affineComp 1 a g) = affineComp 1 (w + a) g := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFInv.affineComp_apply, GFFInv.affineComp_apply, GFFInv.affineComp_apply,
    testAffinePull_one_comp]
  simp

/-- `(g(· + a))_r(w) = g_r(w + a)` -/
lemma circleAvg_affineComp_one_at (g : DistC) (r : ℝ) (a w : ℂ) :
    circleAvg (affineComp 1 a g) r w = circleAvg g r (w + a) := by
  rw [← Tight.circleAvg_affineComp_one, affineComp_one_comp, Tight.circleAvg_affineComp_one]

/-- **translation of the determining σ-algebra** -/
theorem aeEventIn_shift {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {R : ℝ} (hR : 0 < R)
    (z a : ℂ) (k : Ω → ℝ) {E : Set Ω}
    (hE : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) R z)) (ballO z 1)) E) :
    AEEventIn P (fieldSigma (fun ω => addConst (addConst (affineComp 1 a (h ω)) (k ω))
      (-circleAvg (addConst (affineComp 1 a (h ω)) (k ω)) R (z - a))) (ballO (z - a) 1)) E := by
  have hUV : ∀ y : ℂ, y ∈ ballO (z - a) 1 ↔ (1 : ℝ) • y + a ∈ ballO z 1 := fun y => by
    show y ∈ ball (z - a) 1 ↔ (1 : ℝ) • y + a ∈ ball z 1
    rw [one_smul, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm]
    ring_nf
  obtain ⟨F, hF, hEF⟩ := hE
  have h1 : AEEventIn P (fieldSigma (fun ω => affineComp 1 a
      (addConst (h ω) (-circleAvg (h ω) R z))) (ballO (z - a) 1)) E :=
    ⟨F, fieldSigma_le_affineComp one_pos hUV
      (fun ω => addConst (h ω) (-circleAvg (h ω) R z)) F hF, hEF⟩
  refine aeEventIn_of_ae_eq ?_ _ h1
  have hh' := hh.affineComp one_pos a
  filter_upwards [CircleAvg.ae_circleAvg_addConst hh' (z - a) hR] with ω hω
  rw [hω, affineComp_addConst one_pos, addConst_addConst, circleAvg_affineComp_one_at,
    sub_add_cancel]
  congr 1; ring

end LQGMetric.GM
