/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.ScaleCont at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleBump
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
For a distribution `T` on `ℂ`, the mollified field `(s, x) ↦ T(bumpS s x)` is
continuous on `{s > 0}` (`continuous_pair_bumpS_exp`, parametrized by `s = e^u`), and so is its
circle average `(s, w, ρ) ↦ mollAvgS T s w ρ` (`continuous_mollAvgS_exp`). Proof: the family
`(u, x, y) ↦ e^{-2u} ψ₀(e^{-u}(y − x))` is jointly smooth, so on a compact parameter set it is a
continuous curve in `𝓓_K` (LQGMetric `continuous_testFamK`, the argument of LQGMetric's
`continuous_bumpTest` and MoTPort's `continuous_dilTest`); a distribution is continuous on `𝓓`, and
the circle average is a parametric interval integral of a jointly continuous integrand. Own
bookkeeping only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped Distributions Real

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg

/-- copy of LQGMetric `continuous_iteratedFDeriv_snd` with a parameter in a general normed space -/
theorem continuous_iteratedFDeriv_snd_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E → ℂ → ℝ} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Ψ)) (i : ℕ) :
    Continuous fun p : E × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
  let ι : ℂ →L[ℝ] E × ℂ := ContinuousLinearMap.inr ℝ E ℂ
  have key : ∀ p : E × ℂ, iteratedFDeriv ℝ i (Ψ p.1) p.2 =
      (iteratedFDeriv ℝ i (Function.uncurry Ψ) p).compContinuousLinearMap fun _ => ι := by
    intro p
    have h1 : Ψ p.1 = (fun w => Function.uncurry Ψ (w + (p.1, 0))) ∘ ι := by
      funext y; simp [ι]
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w => Function.uncurry Ψ (w + (p.1, 0)) :=
      hΨ.comp (contDiff_id.add contDiff_const)
    rw [h1, ι.iteratedFDeriv_comp_right hg _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    congr 2
    simp [ι]
  simp_rw [key]
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
    (E := fun _ : Fin i => ℂ) (E₁ := fun _ : Fin i => E × ℂ) (F := ℝ) (fun _ => ι)
  exact L.continuous.comp (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

/-- the jointly smooth family `((u, x), y) ↦ e^{-2u} ψ₀(e^{-u} (y − x))` -/
def bumpE (p : ℝ × ℂ) (y : ℂ) : ℝ :=
  Real.exp (-2 * p.1) * psi0 (Complex.ofRealCLM (Real.exp (-p.1)) * (y - p.2))

lemma bumpS_exp_apply (u : ℝ) (x y : ℂ) : bumpS (Real.exp u) x y = bumpE (u, x) y := by
  rw [bumpS_apply (Real.exp_pos u).ne', bumpE]
  congr 1
  · rw [← Real.exp_nat_mul, ← Real.exp_neg]; push_cast; ring_nf
  · congr 1
    rw [Complex.ofRealCLM_apply, Real.exp_neg, Complex.ofReal_inv, div_eq_inv_mul]

lemma contDiff_uncurry_bumpE :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry bumpE) := by
  show ContDiff ℝ _ fun q : (ℝ × ℂ) × ℂ =>
    Real.exp (-2 * q.1.1) * psi0 (Complex.ofRealCLM (Real.exp (-q.1.1)) * (q.2 - q.1.2))
  refine (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst.fst)).mul ?_
  refine psi0.contDiff.comp (ContDiff.mul ?_ (contDiff_snd.sub contDiff_fst.snd))
  exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_fst.fst.neg)

lemma contDiff_bumpE (p : ℝ × ℂ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bumpE p) := by
  have h := contDiff_uncurry_bumpE.comp ((contDiff_const (c := p)).prodMk contDiff_id)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using h

/-- **`(u, x) ↦ bumpS (e^u) x` is continuous into `𝓓(ℂ)`.** -/
theorem continuous_bumpS_exp : Continuous fun p : ℝ × ℂ => bumpS (Real.exp p.1) p.2 := by
  rw [continuous_iff_continuousAt]
  intro p₀
  let S := closedBall p₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : Compacts ℂ := ⟨closedBall 0 (‖p₀.2‖ + 1 + Real.exp (p₀.1 + 1)), isCompact_closedBall _ _⟩
  let Ψ : S → ℂ → ℝ := fun p y => bumpE p.1 y
  have hs : ∀ p : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ p) := fun p => contDiff_bumpE p.1
  have hK : ∀ p : S, ∀ y ∉ (K : Set ℂ), Ψ p y = 0 := by
    intro p y hy
    have hp := p.2
    rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_eq_norm] at hp
    obtain ⟨hu, hx⟩ := hp
    have hy' : ‖p₀.2‖ + 1 + Real.exp (p₀.1 + 1) < ‖y‖ := by
      simpa [K] using hy
    have hu1 : p.1.1 ≤ p₀.1 + 1 := by linarith [le_abs_self (p.1.1 - p₀.1)]
    have hxn : ‖p.1.2‖ ≤ ‖p₀.2‖ + 1 := by
      have := norm_le_norm_add_norm_sub' p.1.2 p₀.2
      linarith
    show bumpE p.1 y = 0
    rw [bumpE, psi0_eq_zero, mul_zero]
    rw [norm_mul, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_of_nonneg
      (Real.exp_pos _).le, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _), one_mul]
    have h1 : Real.exp p.1.1 ≤ Real.exp (p₀.1 + 1) := Real.exp_le_exp.2 hu1
    have h2 : ‖y‖ - ‖p.1.2‖ ≤ ‖y - p.1.2‖ := norm_sub_norm_le _ _
    linarith
  have hD : ∀ i : ℕ, Continuous fun q : S × ℂ => iteratedFDeriv ℝ i (Ψ q.1) q.2 := fun i =>
    (continuous_iteratedFDeriv_snd_gen contDiff_uncurry_bumpE i).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hc := continuous_testFamK K Ψ hs hK hD
  have e : (fun p : S => bumpS (Real.exp p.1.1) p.1.2) = ofSuppC K ∘ testFamK K Ψ hs hK := by
    funext p
    ext y
    exact bumpS_exp_apply p.1.1 p.1.2 y
  have h2 : Continuous fun p : S => bumpS (Real.exp p.1.1) p.1.2 := by
    rw [e]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- the mollified field `(u, x) ↦ T(bumpS (e^u) x)` is continuous -/
theorem continuous_pair_bumpS_exp (T : DistC) :
    Continuous fun p : ℝ × ℂ => T (bumpS (Real.exp p.1) p.2) :=
  (map_continuous T).comp continuous_bumpS_exp

/-- **the mollified circle averages `(u, w, ρ) ↦ mollAvgS T (e^u) w ρ` are continuous** -/
theorem continuous_mollAvgS_exp (T : DistC) :
    Continuous fun q : ℝ × ℂ × ℝ => mollAvgS T (Real.exp q.1) q.2.1 q.2.2 := by
  have hf : Continuous (Function.uncurry fun (q : ℝ × ℂ × ℝ) (θ : ℝ) =>
      T (bumpS (Real.exp q.1) (circleMap q.2.1 q.2.2 θ))) := by
    have hcm : Continuous fun p : (ℝ × ℂ × ℝ) × ℝ => circleMap p.1.2.1 p.1.2.2 p.2 := by
      simp only [circleMap]
      fun_prop
    exact (continuous_pair_bumpS_exp T).comp (continuous_fst.fst.prodMk hcm)
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hf 0 (2 * π)
  simp only [mollAvgS, Real.circleAverage_def, smul_eq_mul]
  exact continuous_const.mul hi

/-- the mollified circle averages are continuous on `{s > 0}` -/
theorem continuousOn_mollAvgS (T : DistC) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => mollAvgS T q.1 q.2.1 q.2.2) (Ioi 0 ×ˢ univ) := by
  have h := (continuous_mollAvgS_exp T).comp_continuousOn
    (s := Ioi (0 : ℝ) ×ˢ (univ : Set (ℂ × ℝ)))
    (f := fun q : ℝ × ℂ × ℝ => (Real.log q.1, q.2))
    ((Real.continuousOn_log.comp continuous_fst.continuousOn fun q hq =>
      (ne_of_gt (show (0 : ℝ) < q.1 from hq.1))).prodMk continuous_snd.continuousOn)
  refine h.congr fun q hq => ?_
  simp only [Function.comp_apply, Real.exp_log (show (0 : ℝ) < q.1 from hq.1)]

end MatedCRTHarmonic.LQGCoord
