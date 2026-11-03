/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MeasurableAvg at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Group.Integral

/-!
# Measurability of circle averages and heat-kernel mollifications (FOUNDATIONS §9 item 3)

* `continuous_bumpTest`: `x ↦ ψ_{n,x}` is continuous into `𝓓(ℂ)` (`ψ_{n,x} = ψ_{n,0}(· − x)`);
* `continuous_heatTrunc`: `z ↦ p_s(z, ·) χ_n` is continuous into `𝓓(ℂ)`;
* hence `(h, x) ↦ ⟨h, ψ_{n,x}⟩`, `(h, z) ↦ ⟨h, p_s(z,·)χ_n⟩` are jointly measurable
  (Carathéodory functions: mathlib `measurable_uncurry_of_continuous_of_measurable`);
* `measurable_circleAvg`: `(h, r, z) ↦ h_r(z)` is jointly measurable, and
  `measurable_heatMollify`: `(h, z) ↦ h*_ε(z)` is jointly measurable, both via mathlib's
  `StronglyMeasurable.limUnder` (QZ_REUSE.md item 10) and `StronglyMeasurable.integral_prod_right'`.

Standard facts without a specific published source; own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace LQGMetric

/-- the inclusion `𝓓_K ⊆ 𝓓(ℂ)` -/
def ofSuppC (K : Compacts ℂ) : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] TestC :=
  TestFunction.ofSupportedInCLM ℝ (subset_univ _)

/-! ### The mollifiers `ψ_{n,x}` -/

theorem normed_eq_translate {c : ℂ} (f : ContDiffBump c) (f₀ : ContDiffBump (0 : ℂ))
    (h1 : f.rIn = f₀.rIn) (h2 : f.rOut = f₀.rOut) (y : ℂ) :
    f.normed volume y = f₀.normed volume (y + -c) := by
  have key : ∀ w, f w = f₀ (w + -c) := fun w => by
    simp [ContDiffBump.apply, h1, h2, sub_eq_add_neg]
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, key]
  simp only [key]
  rw [integral_add_right_eq_self (fun w => f₀ w) (-c)]

theorem bumpTest_apply_eq (n : ℕ) (x y : ℂ) : bumpTest n x y = bumpTest n 0 (y + -x) := by
  show ContDiffBump.normed _ volume y = ContDiffBump.normed _ volume (y + -x)
  exact normed_eq_translate (c := x) _ _ rfl rfl y

theorem bumpTest_zero_eq_zero (n : ℕ) {w : ℂ} (hw : 1 ≤ ‖w‖) : bumpTest n 0 w = 0 := by
  show ContDiffBump.normed _ volume w = 0
  by_contra hne
  have hmem : w ∈ Function.support (ContDiffBump.normed _ volume) := hne
  rw [ContDiffBump.support_normed_eq, mem_ball, dist_zero_right] at hmem
  have : ((2 : ℝ)⁻¹ ^ n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact absurd (hmem.trans_le this) (not_lt.2 hw)

theorem continuous_bumpTest (n : ℕ) : Continuous (bumpTest n) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let S := closedBall x₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : Compacts ℂ := ⟨closedBall 0 (‖x₀‖ + 2), isCompact_closedBall _ _⟩
  let g := bumpTest n 0
  have hs : ∀ x : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => g (y + -(x : ℂ)) :=
    fun x => g.contDiff.comp (contDiff_id.add contDiff_const)
  have hK : ∀ x : S, ∀ y ∉ (K : Set ℂ), g (y + -(x : ℂ)) = 0 := by
    intro x y hy
    apply bumpTest_zero_eq_zero
    have hx : ‖(x : ℂ) - x₀‖ ≤ 1 := by rw [← dist_eq_norm]; exact mem_closedBall.1 x.2
    have hy' : ‖x₀‖ + 2 < ‖y‖ := by simpa [K] using hy
    have h1 : ‖y‖ ≤ ‖y + -(x : ℂ)‖ + ‖(x : ℂ) - x₀‖ + ‖x₀‖ := by
      calc ‖y‖ = ‖(y + -(x : ℂ)) + ((x : ℂ) - x₀) + x₀‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ =>
      iteratedFDeriv ℝ i (fun y => g (y + -(p.1 : ℂ))) p.2 := by
    intro i
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (g.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := continuous_testFamK K (fun (x : S) y => g (y + -(x : ℂ))) hs hK hD
  have e : (fun x : S => bumpTest n x) = ofSuppC K ∘ testFamK K _ hs hK := by
    funext x
    ext y
    exact bumpTest_apply_eq n x y
  have h2 : Continuous fun x : S => bumpTest n x := by
    rw [e]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- `(h, x) ↦ ⟨h, ψ_{n,x}⟩` is jointly measurable -/
theorem measurable_apply_bumpTest (n : ℕ) :
    Measurable fun p : DistC × ℂ => p.1 (bumpTest n p.2) := by
  have := measurable_uncurry_of_continuous_of_measurable (u := fun (x : ℂ) (h : DistC) =>
      h (bumpTest n x)) (fun h => (map_continuous h).comp (continuous_bumpTest n))
    (fun x => measurable_distOn_apply _)
  exact this.comp measurable_swap

/-- `(h, r, z) ↦ h_r(z)` is jointly measurable -/
theorem measurable_circleAvg :
    Measurable fun p : DistC × ℝ × ℂ => circleAvg p.1 p.2.1 p.2.2 := by
  have hn : ∀ n : ℕ, StronglyMeasurable fun p : DistC × ℝ × ℂ =>
      Real.circleAverage (fun x => p.1 (bumpTest n x)) p.2.2 p.2.1 := by
    intro n
    have hm : Measurable fun q : (DistC × ℝ × ℂ) × ℝ =>
        q.1.1 (bumpTest n (circleMap q.1.2.2 q.1.2.1 q.2)) := by
      refine (measurable_apply_bumpTest n).comp ((measurable_fst.comp measurable_fst).prodMk ?_)
      fun_prop
    have := (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).const_smul (2 * Real.pi)⁻¹
    convert this using 1
    funext p
    simp only [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rfl
  exact (StronglyMeasurable.limUnder (l := atTop) hn).measurable

theorem measurable_circleAvg_left (r : ℝ) (z : ℂ) : Measurable fun h : DistC => circleAvg h r z :=
  measurable_circleAvg.comp (f := fun h : DistC => (h, r, z))
    (measurable_id.prodMk (measurable_const (a := ((r, z) : ℝ × ℂ))))

/-! ### The truncated heat kernels -/

theorem contDiff_heatTrunc_uncurry (s : ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry fun (z w : ℂ) => heatKernel s z w * cutoff n w) := by
  unfold heatKernel
  refine (contDiff_const.mul (Real.contDiff_exp.comp
    (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).neg.div_const _))).mul
    ((cutoff n).contDiff.comp contDiff_snd)

theorem continuous_heatTrunc (s : ℝ) (n : ℕ) : Continuous fun z => heatTrunc s z n := by
  let K : Compacts ℂ := ⟨closedBall 0 (n + 2), isCompact_closedBall _ _⟩
  have hK : ∀ z : ℂ, ∀ w ∉ (K : Set ℂ), heatKernel s z w * cutoff n w = 0 := by
    intro z w hw
    have : cutoff n w = 0 := by
      by_contra hne
      have hmem : w ∈ Function.support (cutoff n) := hne
      rw [ContDiffBump.support_eq] at hmem
      exact hw (ball_subset_closedBall hmem)
    simp [this]
  have hc := continuous_testFamK K (fun z w => heatKernel s z w * cutoff n w)
    (fun z => (heatTrunc s z n).contDiff) hK
    (continuous_iteratedFDeriv_snd (contDiff_heatTrunc_uncurry s n))
  convert (ofSuppC K).continuous.comp hc using 1
  funext z
  ext w
  rfl

/-- `(h, z) ↦ h*_ε(z)` is jointly measurable -/
theorem measurable_heatMollify (ε : ℝ) :
    Measurable fun p : DistC × ℂ => heatMollify ε p.1 p.2 := by
  have hn : ∀ n : ℕ, StronglyMeasurable fun p : DistC × ℂ =>
      p.1 (heatTrunc (ε ^ 2 / 2) p.2 n) := by
    intro n
    have := measurable_uncurry_of_continuous_of_measurable (u := fun (z : ℂ) (h : DistC) =>
        h (heatTrunc (ε ^ 2 / 2) z n))
      (fun h => (map_continuous h).comp (continuous_heatTrunc _ n))
      (fun x => measurable_distOn_apply _)
    exact (this.comp measurable_swap).stronglyMeasurable
  exact (StronglyMeasurable.limUnder (l := atTop) hn).measurable

theorem measurable_heatMollify_left (ε : ℝ) (z : ℂ) :
    Measurable fun h : DistC => heatMollify ε h z :=
  (measurable_heatMollify ε).comp (f := fun h : DistC => (h, z))
    (measurable_id.prodMk (measurable_const (a := z)))

end LQGMetric
