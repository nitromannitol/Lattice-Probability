/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistKerId at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistFTC

/-!
# The kernel identity `∫ ∂_re ∂_im φ(x) kerFun 1_{[0,x]} dx = kerFun φ` (task P2-EXIST)

Pointwise in `(t, y)`: Fubini over `(x, u) ∈ ℂ × ℂ` and `integral_d12_mul_rectInd`. This is the
deterministic half of the identification `∫ F ∂_re ∂_im φ = W(kerFun φ)` a.s. Own elementary
proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric

namespace LQGMetric
namespace GFFExist

open WhiteNoise

lemma measurable_sgnInd₂ : Measurable fun p : ℝ × ℝ => sgnInd p.1 p.2 := by
  unfold sgnInd
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  · exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)

lemma measurable_rectInd₂ : Measurable fun p : ℂ × ℂ => rectInd p.1 p.2 := by
  unfold rectInd
  exact (measurable_sgnInd₂.comp ((Complex.measurable_re.comp measurable_fst).prodMk
    (Complex.measurable_re.comp measurable_snd))).mul
    (measurable_sgnInd₂.comp ((Complex.measurable_im.comp measurable_fst).prodMk
    (Complex.measurable_im.comp measurable_snd)))

/-- test functions satisfy the standing hypotheses -/
lemma testC_bddSupp (φ : TestC) : ∃ M R, 0 ≤ R ∧ BddSupp φ M R := by
  obtain ⟨C, hC⟩ := testC_bounded φ
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish φ
  exact ⟨C, L, hL0, ⟨φ.continuous.measurable, hC, hL⟩⟩

lemma rectInd_eq_zero_of {x u : ℂ} (hu : 2 * ‖x‖ < ‖u‖) : rectInd x u = 0 :=
  (rectInd_bddSupp x).supp u (lt_of_le_of_lt (by
    have h1 := Complex.abs_re_le_norm x
    have h2 := Complex.abs_im_le_norm x
    linarith) hu)

/-- **Kernel identity.** -/
theorem integral_d12_mul_kerFun (φ : TestC) (q : ℝ × ℂ) :
    ∫ x, d12 φ x * kerFun (rectInd x) q = kerFun φ q := by
  unfold kerFun
  by_cases ht : q.1 ∈ Ioi (0 : ℝ)
  swap
  · simp [indicator_of_notMem ht]
  simp only [indicator_of_mem ht]
  have ht0 : 0 < q.1 := ht
  have hs : 0 < q.1 / 2 := by linarith
  set c := (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (q.1 / 2) 0 q.2) q.1 with hc
  set K : ℂ → ℝ := fun u => heatKernel (q.1 / 2) u q.2 - c with hK
  have hKm : Measurable K := by simp only [hK]; unfold heatKernel; fun_prop
  have hKb : ∀ u, |K u| ≤ (2 * Real.pi * (q.1 / 2))⁻¹ + |c| := fun u => by
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_of_nonneg (heatKernel_nonneg _ hs.le _ _)]; exact heatKernel_le _ hs u q.2
  have hinner : ∀ g : ℂ → ℝ, kerInner g q.1 q.2 = ∫ u, g u * K u := fun g => rfl
  simp_rw [hinner]
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 φ)
  set H : ℂ × ℂ → ℝ := fun p => d12 φ p.1 * (rectInd p.1 p.2 * K p.2) with hH
  have hHm : Measurable H :=
    ((d12 φ).continuous.measurable.comp measurable_fst).mul
      (measurable_rectInd₂.mul (hKm.comp measurable_snd))
  set Kb := (2 * Real.pi * (q.1 / 2))⁻¹ + |c| with hKbdef
  have hdom : Integrable (fun p : ℂ × ℂ => |d12 φ p.1| *
      (closedBall (0 : ℂ) (2 * L)).indicator (fun _ => Kb) p.2) (volume.prod volume) :=
    (GFFInv.integrable_test (d12 φ)).abs.mul_prod
      ((integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne))
  have hHi : Integrable H (volume.prod volume) := by
    refine hdom.mono' hHm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [hH, Real.norm_eq_abs, abs_mul]
    by_cases hx : L < ‖p.1‖
    · rw [hL _ hx]; simp
    · push_neg at hx
      by_cases hu : p.2 ∈ closedBall (0 : ℂ) (2 * L)
      · rw [indicator_of_mem hu]
        have h1 := (rectInd_bddSupp p.1).bdd p.2
        gcongr
        calc |rectInd p.1 p.2| * |K p.2| ≤ 1 * Kb := by
              gcongr
              exact hKb _
          _ = Kb := one_mul _
      · have hu' : 2 * ‖p.1‖ < ‖p.2‖ := by
          rw [mem_closedBall, dist_zero_right, not_le] at hu; linarith
        rw [rectInd_eq_zero_of hu', indicator_of_notMem hu]; simp
  have e1 : ∀ x, d12 φ x * (Real.sqrt Real.pi * ∫ u, rectInd x u * K u) =
      Real.sqrt Real.pi * ∫ u, H (x, u) := fun x => by
    simp only [hH]; rw [integral_const_mul]; ring
  simp_rw [e1]
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap (f := fun x u => H (x, u)) hHi]
  congr 1; funext u
  simp only [hH]
  have e2 : ∀ x, d12 φ x * (rectInd x u * K u) = (d12 φ x * rectInd x u) * K u := fun x => by ring
  simp_rw [e2]
  rw [integral_mul_const, integral_d12_mul_rectInd]

end GFFExist
end LQGMetric
