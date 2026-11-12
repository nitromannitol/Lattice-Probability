/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1Cont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.LocalizedCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1, first claim: joint continuity of `(ε, z) ↦ ĥ*_ε(z)`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:691: "a.s. `(z, ε) ↦ ĥ*_ε(z)` is
continuous". With `ĥ*_ε(z) = ⟨h, ψ_ε(z − ·) p_{ε²/2}(z, ·)⟩` (DFGPS (eqn-localized-def)), the
map `(ε, z) ↦ ψ_ε(z − ·) p_{ε²/2}(z, ·)` is continuous into the test functions on `ε > 0`, so the
claim holds for *every* distribution `h` (the paper argues via the polar formula and a continuous
modification, T:723; for our definition no modification is needed, as in
`LFPP.continuous_locTest`, which this file extends to a moving `ε`). Own argument (routine
smooth dependence on parameters); the parameter `ε = e^u` makes the dependence globally smooth.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

open LFPP

/-- the profile of `ψ_{e^u}`: `y ↦ ψ_{e^u}(y)` written through mathlib's radial bump base -/
def locProf (u : ℝ) (y : ℂ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((Real.exp (u / 2) / 2)⁻¹ • y)

lemma sqrt_exp_eq (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  have : Real.exp u = Real.exp (u / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [this, Real.sqrt_sq (Real.exp_pos _).le]

lemma locBump_exp (u : ℝ) (y : ℂ) :
    locBump (Real.exp u) (Real.exp_pos u) y = locProf u y := by
  simp only [locBump, sqrt_exp_eq, locProf]

lemma contDiff_locProf :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun p : ℝ × ℂ => locProf p.1 p.2 := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun p : ℝ × ℂ => ((2 : ℝ), (Real.exp (p.1 / 2) / 2)⁻¹ • p.2) := by
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun p : ℝ × ℂ => (Real.exp (p.1 / 2) / 2)⁻¹ :=
      ((Real.contDiff_exp.comp (contDiff_fst.div_const _)).div_const _).inv
        fun p => (by positivity : Real.exp (p.1 / 2) / 2 ≠ 0)
    exact contDiff_const.prodMk (hc.smul contDiff_snd)
  exact (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hf
    fun p => ⟨by norm_num, mem_univ _⟩

-- keep the profile folded downstream (unfolding the radial base makes `whnf` time out)
attribute [irreducible] locProf

/-- the kernel `(u, z, w) ↦ ψ_{e^u}(z − w) p_{e^{2u}/2}(z, w)` -/
def locKer (q : ℝ × ℂ) (w : ℂ) : ℝ :=
  locProf q.1 (q.2 - w) * heatKernel (Real.exp q.1 ^ 2 / 2) q.2 w

lemma contDiff_locKer :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry locKer) := by
  unfold Function.uncurry locKer heatKernel
  refine (contDiff_locProf.comp ((contDiff_fst.comp contDiff_fst).prodMk
    ((contDiff_snd.comp contDiff_fst).sub contDiff_snd))).mul ?_
  refine ContDiff.mul ?_ (Real.contDiff_exp.comp ?_)
  · refine ContDiff.inv (contDiff_const.mul
      (((Real.contDiff_exp.comp (contDiff_fst.comp contDiff_fst)).pow 2).div_const _))
      fun p => by positivity
  · refine ContDiff.div (((contDiff_norm_sq ℝ).comp
      ((contDiff_snd.comp contDiff_fst).sub contDiff_snd)).neg) (contDiff_const.mul
      (((Real.contDiff_exp.comp (contDiff_fst.comp contDiff_fst)).pow 2).div_const _))
      fun p => by positivity

lemma locTest_exp_apply (q : ℝ × ℂ) (w : ℂ) :
    locTest (Real.exp q.1) (Real.exp_pos q.1) q.2 w = locKer q w := by
  show locBump _ _ (q.2 - w) * heatKernel _ q.2 w = _
  rw [locBump_exp]; rfl

/-- the `w`-derivatives of a jointly smooth kernel with parameter in `ℝ × ℂ` are jointly
continuous (as `continuous_iteratedFDeriv_snd`, Field/Measurable.lean) -/
theorem continuous_iteratedFDeriv_snd_rc {Ψ : ℝ × ℂ → ℂ → ℝ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Ψ)) (i : ℕ) :
    Continuous fun p : (ℝ × ℂ) × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
  let ι : ℂ →L[ℝ] (ℝ × ℂ) × ℂ := ContinuousLinearMap.inr ℝ (ℝ × ℂ) ℂ
  have key : ∀ p : (ℝ × ℂ) × ℂ, iteratedFDeriv ℝ i (Ψ p.1) p.2 =
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
    (E := fun _ : Fin i => ℂ) (E₁ := fun _ : Fin i => (ℝ × ℂ) × ℂ) (F := ℝ) (fun _ => ι)
  exact L.continuous.comp (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

/-- `(u, z) ↦ ψ_{e^u}(z − ·) p_{e^{2u}/2}(z, ·)` is continuous into the test functions. -/
def locTestE (q : ℝ × ℂ) : TestC := locTest (Real.exp q.1) (Real.exp_pos q.1) q.2

lemma locKer_eq_zero (q : ℝ × ℂ) {w : ℂ} (hw : Real.sqrt (Real.exp q.1) < dist w q.2) :
    locKer q w = 0 := by
  rw [← locTest_exp_apply]
  have hw' : w ∉ closedBall q.2 (Real.sqrt (Real.exp q.1)) := by
    rw [mem_closedBall, not_le]; exact hw
  show locBump _ _ (q.2 - w) * _ = 0
  rw [locBump_comp_eq_zero _ _ _ hw', zero_mul]

lemma contDiff_locKer_snd (q : ℝ × ℂ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (locKer q) :=
  contDiff_locKer.comp (contDiff_const.prodMk contDiff_id)

lemma locKer_eq_zero_of_mem (q0 : ℝ × ℂ) (x : closedBall q0 1) (w : ℂ)
    (hw : w ∉ closedBall q0.2 (1 + Real.exp ((q0.1 + 1) / 2))) : locKer x.1 w = 0 := by
  have hx := x.2
  rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hx
  have hu : x.1.1 ≤ q0.1 + 1 := by
    have := hx.1; rw [Real.dist_eq, abs_le] at this; linarith
  have hsq : Real.sqrt (Real.exp x.1.1) ≤ Real.exp ((q0.1 + 1) / 2) := by
    rw [sqrt_exp_eq]; exact Real.exp_le_exp.2 (by linarith)
  refine locKer_eq_zero _ ?_
  rw [mem_closedBall, not_le] at hw
  linarith [dist_triangle w x.1.2 q0.2, hx.2]

/-- `(u, z) ↦ ψ_{e^u}(z − ·) p_{e^{2u}/2}(z, ·)` is continuous into the test functions. -/
theorem continuous_locTestE : Continuous locTestE := by
  rw [continuous_iff_continuousAt]
  intro q0
  let K : TopologicalSpace.Compacts ℂ :=
    ⟨closedBall q0.2 (1 + Real.exp ((q0.1 + 1) / 2)), isCompact_closedBall _ _⟩
  have hD : ∀ i : ℕ, Continuous fun p : closedBall q0 1 × ℂ =>
      iteratedFDeriv ℝ i (locKer p.1.1) p.2 := by
    intro i
    have h1 := continuous_iteratedFDeriv_snd_rc contDiff_locKer i
    have h2 : Continuous fun p : closedBall q0 1 × ℂ => ((p.1 : ℝ × ℂ), p.2) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have := h1.comp h2
    exact this
  have hc := continuous_testFamK K (fun x : closedBall q0 1 => locKer x.1)
    (fun x => contDiff_locKer_snd x.1) (locKer_eq_zero_of_mem q0) hD
  have he : (fun x : closedBall q0 1 => locTestE x.1) =
      (ofSuppC K) ∘ testFamK K (fun x : closedBall q0 1 => locKer x.1)
        (fun x => contDiff_locKer_snd x.1) (locKer_eq_zero_of_mem q0) := by
    funext x; ext w; exact locTest_exp_apply x.1 w
  have hB : Continuous fun x : closedBall q0 1 => locTestE x.1 := by
    rw [he]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 hB).continuousAt
    (closedBall_mem_nhds q0 one_pos)

lemma locTest_congr {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a = b) (z : ℂ) :
    locTest a ha z = locTest b hb z := by subst hab; rfl

/-- **DFGPS Lemma 2.1, first claim** (T:691): `(ε, z) ↦ ĥ*_ε(z)` is continuous on `ε > 0`, for
every distribution `h`. -/
theorem lem2_1_cont (h : DistC) :
    ContinuousOn (fun p : ℝ × ℂ => if hp : 0 < p.1 then locMollify p.1 hp h p.2 else 0)
      (Ioi 0 ×ˢ univ) := by
  have hg : ContinuousOn (fun p : ℝ × ℂ =>
      h (locTestE (Real.log p.1, p.2))) (Ioi 0 ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℝ × ℂ => (Real.log p.1, p.2)) (Ioi 0 ×ˢ univ) :=
      ((Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
        (ne_of_gt (mem_prod.1 hp).1 : p.1 ≠ 0)).prodMk continuous_snd.continuousOn)
    exact (map_continuous h).comp_continuousOn (continuous_locTestE.comp_continuousOn h1)
  refine hg.congr fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  show (if hp : 0 < p.1 then locMollify p.1 hp h p.2 else 0) = _
  simp only [hp1, ↓reduceDIte]
  show h _ = h _
  rw [locTest_congr hp1 (Real.exp_pos _) (Real.exp_log hp1).symm]
  rfl

end LQGMetric.DFGPS
