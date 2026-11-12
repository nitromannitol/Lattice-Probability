/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1PolarJointKolm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarJointLip
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Cont
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Uniform-in-`(s, z)` bounds for the GFF truncation differences

The three-parameter version of `Field/HeatMollifyKolm` (P2-FHEAT): with `s = e^u` and the index
`q ∈ ℝ³ ↦ (u, z) = (q₀, q₁ + i q₂)`, the mean-zero parts
`G_n(q) = ⟨g, meanZeroPart D_n(e^{q₀}, q₁ + i q₂)⟩` satisfy, a.s., for every `R`, eventually in `n`,
`sup_{q ∈ [−R,R]³} |G_n(q)| ≤ 25 e^{−n/2}` (`ae_eventually_gaussDiff3_le`). Inputs: the joint
Lipschitz bound `abs_heatDiff_sub_sz_le`, Gaussian fourth moments, the quantitative dyadic
Kolmogorov bound `QuantumZipper.Thm18Asm.G1FM.kolm_sup_tail_N` (`d = 3`, `p = a = 4`, `θ = 7/8`)
and Borel–Cantelli. Own argument along the route of FOUNDATIONS §3 (as `HeatMollifyKolm`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

/-! ### Continuity of `(u, z) ↦ p_{e^u}(z, ·) χ_m` in `𝓓(ℂ)` -/

lemma contDiff_heatTruncE (m : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (Function.uncurry fun (q : ℝ × ℂ) (w : ℂ) =>
      heatKernel (Real.exp q.1) q.2 w * cutoff m w) := by
  unfold Function.uncurry heatKernel
  refine ContDiff.mul (ContDiff.mul ?_ ?_) ((cutoff m).contDiff.comp contDiff_snd)
  · exact (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_fst.comp contDiff_fst))).inv
      fun p => (by positivity : (0 : ℝ) < 2 * Real.pi * Real.exp p.1.1).ne'
  · refine Real.contDiff_exp.comp (ContDiff.div ?_ ?_ fun p => by positivity)
    · exact ((contDiff_norm_sq ℝ).comp ((contDiff_snd.comp contDiff_fst).sub contDiff_snd)).neg
    · exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_fst.comp contDiff_fst))

theorem continuous_heatTruncE (m : ℕ) :
    Continuous fun q : ℝ × ℂ => heatTrunc (Real.exp q.1) q.2 m := by
  let K : TopologicalSpace.Compacts ℂ := ⟨closedBall 0 (m + 2), isCompact_closedBall _ _⟩
  have hK : ∀ q : ℝ × ℂ, ∀ w ∉ (K : Set ℂ), heatKernel (Real.exp q.1) q.2 w * cutoff m w = 0 := by
    intro q w hw
    have : cutoff m w = 0 := by
      by_contra hne
      have hmem : w ∈ Function.support (cutoff m) := hne
      rw [ContDiffBump.support_eq] at hmem
      exact hw (ball_subset_closedBall hmem)
    simp [this]
  have hc := continuous_testFamK K
    (fun (q : ℝ × ℂ) (w : ℂ) => heatKernel (Real.exp q.1) q.2 w * cutoff m w)
    (fun q : ℝ × ℂ => by exact (heatTrunc (Real.exp q.1) q.2 m).contDiff) hK
    (continuous_iteratedFDeriv_snd_rc (contDiff_heatTruncE m))
  have he : (fun q : ℝ × ℂ => heatTrunc (Real.exp q.1) q.2 m) =
      (LQGMetric.ofSuppC K) ∘ testFamK K
        (fun (q : ℝ × ℂ) (w : ℂ) => heatKernel (Real.exp q.1) q.2 w * cutoff m w)
        (fun q : ℝ × ℂ => by exact (heatTrunc (Real.exp q.1) q.2 m).contDiff) hK := by
    funext q; ext w; rfl
  rw [he]
  exact (LQGMetric.ofSuppC K).continuous.comp hc

/-! ### The three-parameter process -/

/-- `q ↦ (q₀, q₁ + i q₂)` -/
def sz3 (q : Fin 3 → ℝ) : ℝ × ℂ := (q 0, ⟨q 1, q 2⟩)

lemma continuous_sz3 : Continuous sz3 := by
  have : sz3 = fun q => (q 0, Complex.equivRealProdCLM.symm (q 1, q 2)) := by
    funext q; simp only [sz3, Prod.mk.injEq, true_and]; apply Complex.ext <;> simp
  rw [this]; fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `G_n(q) = ⟨h, meanZeroPart D_n(e^{q₀}, q₁ + i q₂)⟩` -/
def gaussDiff3 (h : Ω → DistC) (n : ℕ) (q : Fin 3 → ℝ) (ω : Ω) : ℝ :=
  h ω (meanZeroPart (heatDiff (Real.exp (sz3 q).1) (sz3 q).2 n)).1

lemma pair_meanZeroPart_heatDiff (T : DistC) (s : ℝ) (z : ℂ) (n : ℕ) :
    T (meanZeroPart (heatDiff s z n)).1 =
      (T (heatTrunc s z (n + 1)) - T (heatTrunc s z n)) -
        (ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatTrunc s z (n + 1)) -
          ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatTrunc s z n)) * T refTest := by
  have e := pair_eq_meanZeroPart T (heatDiff s z n)
  have e2 : ∫ x, heatDiff s z n x =
      ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatDiff s z n) := by
    rw [ofCont_apply_heat]; simp
  rw [e2] at e
  simp only [heatDiff, map_sub] at e ⊢
  linarith

lemma continuous_gaussDiff3 (n : ℕ) (ω : Ω) : Continuous fun q => gaussDiff3 h n q ω := by
  have hT : ∀ m, Continuous fun p : ℝ × ℂ => h ω (heatTrunc (Real.exp p.1) p.2 m) := fun m =>
    (h ω).continuous.comp (continuous_heatTruncE m)
  have hI : ∀ m, Continuous fun p : ℝ × ℂ =>
      ofCont (ContinuousMap.const ℂ (1 : ℝ)) (heatTrunc (Real.exp p.1) p.2 m) :=
    fun m => (ofCont _).continuous.comp (continuous_heatTruncE m)
  simp only [gaussDiff3]
  simp_rw [pair_meanZeroPart_heatDiff]
  exact (((hT _).sub (hT _)).sub (((hI _).sub (hI _)).mul continuous_const)).comp continuous_sz3

lemma measurable_gaussDiff3 (hh : IsWholePlaneGFF h P) (n : ℕ) (q : Fin 3 → ℝ) :
    Measurable (gaussDiff3 h n q) :=
  (measurable_distOn_apply _).comp hh.measurable

lemma gaussDiff3_sub (n : ℕ) (q q' : Fin 3 → ℝ) (ω : Ω) :
    gaussDiff3 h n q ω - gaussDiff3 h n q' ω =
      h ω (meanZeroPart (heatDiff (Real.exp (sz3 q).1) (sz3 q).2 n -
        heatDiff (Real.exp (sz3 q').1) (sz3 q').2 n)).1 := by
  simp only [gaussDiff3, meanZeroPart_sub, map_sub]

/-! ### Box geometry -/

lemma norm_sz3_le {R : ℕ} {q : Fin 3 → ℝ} (hq : q ∈ QuantumZipper.KolmD.boxD R) :
    ‖(sz3 q).2‖ ≤ 2 * R := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [sz3]
  linarith [hq 1, hq 2]

lemma exp_sz3_mem {R : ℕ} {q : Fin 3 → ℝ} (hq : q ∈ QuantumZipper.KolmD.boxD R) :
    Real.exp (sz3 q).1 ∈ Icc (Real.exp (-(R : ℝ))) (Real.exp R) := by
  have := abs_le.1 (hq 0)
  exact ⟨Real.exp_le_exp.2 this.1, Real.exp_le_exp.2 this.2⟩

lemma abs_exp_sub_exp_le {R x y : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |Real.exp x - Real.exp y| ≤ Real.exp R * |x - y| := by
  have hder : ∀ t ∈ Icc (-R) R, HasDerivWithinAt Real.exp (Real.exp t) (Icc (-R) R) t :=
    fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt
  have hb : ∀ t ∈ Icc (-R) R, ‖Real.exp t‖ ≤ Real.exp R := fun t ht => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 ht.2
  have := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le hder hb
    (abs_le.1 hy) (abs_le.1 hx)
  simpa [Real.norm_eq_abs] using this

lemma dist_sz3_le {R : ℕ} {q q' : Fin 3 → ℝ} (hq : q ∈ QuantumZipper.KolmD.boxD R)
    (hq' : q' ∈ QuantumZipper.KolmD.boxD R) :
    |Real.exp (sz3 q).1 - Real.exp (sz3 q').1| + ‖(sz3 q).2 - (sz3 q').2‖ ≤
      (Real.exp R + 2) * ‖q - q'‖ := by
  have h0 := norm_le_pi_norm (q - q') 0
  have h1 := norm_le_pi_norm (q - q') 1
  have h2 := norm_le_pi_norm (q - q') 2
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h0 h1 h2
  have he := abs_exp_sub_exp_le (hq 0) (hq' 0)
  have hz : ‖(sz3 q).2 - (sz3 q').2‖ ≤ |q 1 - q' 1| + |q 2 - q' 2| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp [sz3]
  simp only [sz3] at he hz ⊢
  have := mul_le_mul_of_nonneg_left h0 (Real.exp_pos (R : ℝ)).le
  nlinarith

end LQGMetric.DFGPS
