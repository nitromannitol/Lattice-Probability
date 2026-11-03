/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg2Lap at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg

/-!
# Laplace transform of discrete GMC sums: the decoupling step (P2-NEGMOM)

* `DGMC.kahaneFun_exp_neg` : `y ↦ e^{-ty}` (`t ≥ 0`) is admissible for Kahane's inequality;
* `DGMC.kahane_laplace_shift` : Kahane's inequality for the Laplace transform when
  `Cov X ≤ Cov Y + c`, with the common factor `e^{g − c/2}` (`g ~ N(0,c)`) removed by an
  exponential Markov bound: `E e^{-t M_X} ≤ e^{λ(λ+1)c/2 − λa} + E e^{-t e^{-a} M_Y}`;
* `DGMC.LogCorr.integral_exp_neg_gM_le` : the recursion for the Laplace transform of
  `gM_n([0,1]²)`:
  `E e^{-t gM_{m+l}} ≤ e^{λ(λ+1)(β m log 2 + 2c)/2 − λa} + (E e^{-t e^{-a} 4^{-m} gM_l})^N`,
  `N = (grp0 m).card`.

This is the Laplace-transform form of Molchan's argument for negative moments (Molchan,
*Scaling exponents and multifractal dimensions for independent random cascades*, CMP 179
(1996)), which Robert–Vargas (arXiv:0807.1030, proof of Proposition 3.6, `main.tex`
l. 1031–1037) adapt to Gaussian multiplicative chaos via Kahane's convexity inequality; the
decoupling of one checkerboard group is the one of `LogCorr.integral_group_rpow_le`
(Berestycki–Powell arXiv:2404.16642, l. 1719–1745), with the convex function `e^{-t·}` in place
of `y^q`.  Decision D63.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

lemma hasDerivAt_neg_mul_exp (t y : ℝ) :
    HasDerivAt (fun y => Real.exp (-(t * y))) (Real.exp (-(t * y)) * -t) y := by
  have h : HasDerivAt (fun y : ℝ => -(t * y)) (-t) y := by
    have := (hasDerivAt_id' y).const_mul (-t)
    rw [mul_one] at this
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun z => by ring)
  exact h.exp

/-- `y ↦ e^{-ty}` is an admissible convex function for Kahane's inequality -/
lemma kahaneFun_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    Kahane.KahaneFun (fun y => Real.exp (-(t * y))) (fun y => -t * Real.exp (-(t * y)))
      (fun y => t ^ 2 * Real.exp (-(t * y))) (1 + t + t ^ 2) 0 where
  hasDerivAt y _ := (hasDerivAt_neg_mul_exp t y).congr_deriv (by ring)
  hasDerivAt' y _ := ((hasDerivAt_neg_mul_exp t y).const_mul (-t)).congr_deriv (by ring)
  continuousOn'' := by fun_prop
  nonneg'' y _ := by positivity
  growth y hy := by
    have h1 : Real.exp (-(t * y)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ht hy.le))
    rw [pow_zero, mul_one, abs_of_pos (Real.exp_pos _)]
    nlinarith [sq_nonneg t]
  growth' y hy := by
    have h1 : Real.exp (-(t * y)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ht hy.le))
    rw [pow_zero, mul_one, abs_mul, abs_neg, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
    nlinarith [sq_nonneg t, Real.exp_pos (-(t * y))]
  growth'' y hy := by
    have h1 : Real.exp (-(t * y)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ht hy.le))
    rw [pow_zero, mul_one, abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_pos (Real.exp_pos _)]
    nlinarith [sq_nonneg t, Real.exp_pos (-(t * y))]

/-- the pointwise splitting of the common log-normal factor -/
lemma exp_neg_mul_exp_le {t S lam : ℝ} (ht : 0 ≤ t) (hS : 0 ≤ S) (hlam : 0 ≤ lam) (a g : ℝ) :
    Real.exp (-(t * (Real.exp g * S))) ≤
      Real.exp (lam * (-a - g)) + Real.exp (-(t * Real.exp (-a) * S)) := by
  by_cases h : -a ≤ g
  · refine le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 ?_)
    have := Real.exp_le_exp.2 h
    have : t * Real.exp (-a) * S ≤ t * (Real.exp g * S) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hS) ht
    linarith
  · refine le_add_of_le_of_nonneg ?_ (Real.exp_pos _).le
    rw [Real.exp_le_exp]
    have : 0 ≤ lam * (-a - g) := mul_nonneg hlam (by linarith)
    have : 0 ≤ t * (Real.exp g * S) := mul_nonneg ht (mul_nonneg (Real.exp_pos _).le hS)
    linarith

variable {ι : Type*} [Fintype ι]
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- **Kahane's inequality for the Laplace transform, covariance up to `+ c`** -/
theorem kahane_laplace_shift [Nonempty ι] {t : ℝ} (ht : 0 ≤ t) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0) (c : ℝ≥0)
    (hcov : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
      cov[fun ω => Y ω i, fun ω => Y ω j; P'] + c) {lam : ℝ} (hlam : 0 ≤ lam) (a : ℝ) :
    ∫ ω, Real.exp (-(t * ∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2))) ∂P ≤
      Real.exp (lam * (lam + 1) * c / 2 - lam * a) +
        ∫ ω, Real.exp (-(t * Real.exp (-a) *
          ∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2))) ∂P' := by
  have := hY.isProbabilityMeasure
  have hK := Kahane.kahane_convexity (kahaneFun_exp_neg ht) hp hX
    (Kahane.hasGaussianLaw_shiftVec hY c) hXm (Kahane.integral_shiftVec hY hYm c)
    fun i j => by rw [Kahane.cov_shiftVec hY hYm c]; exact hcov i j
  refine hK.trans ?_
  set S : Ω' → ℝ := fun ω => ∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2)
  have hS : ∀ ω, 0 ≤ S ω := fun ω =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i).le (Real.exp_pos _).le
  have hpt : ∀ z : Ω' × ℝ, (∑ i, p i * Real.exp (Kahane.shiftVec Y z i -
      Var[fun z => Kahane.shiftVec Y z i; Kahane.shiftMeas P' c] / 2)) =
      Real.exp (z.2 - c / 2) * S z.1 := by
    intro z
    simp_rw [Kahane.variance_shiftVec hY hYm c]
    simp only [S, Finset.mul_sum, Kahane.shiftVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hpt]
  have hSm : AEMeasurable S P' :=
    Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hY.aemeasurable.eval i).sub_const _).exp.const_mul _
  have hB : Integrable (fun ω => Real.exp (-(t * Real.exp (-a) * S ω))) P' := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (mul_nonneg ht (Real.exp_pos _).le) (hS ω)
  have hG : Integrable (fun y : ℝ => Real.exp (lam * (-a - (y - c / 2)))) (gaussianReal 0 c) := by
    have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := c) (-lam)).const_mul
      (Real.exp (lam * (c / 2 - a)))
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [← Real.exp_add]; congr 1; ring
  have hR : Integrable (fun z : Ω' × ℝ => Real.exp (lam * (-a - (z.2 - c / 2))) +
      Real.exp (-(t * Real.exp (-a) * S z.1))) (Kahane.shiftMeas P' c) := by
    unfold Kahane.shiftMeas
    exact (hG.comp_snd P').add (hB.comp_fst _)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun z => (Real.exp_pos _).le) hR
    (Eventually.of_forall fun z => exp_neg_mul_exp_le ht (hS z.1) hlam a _)).trans_eq ?_
  rw [integral_add (by unfold Kahane.shiftMeas; exact hG.comp_snd P')
      (by unfold Kahane.shiftMeas; exact hB.comp_fst _),
    Kahane.integral_snd_shiftMeas c (fun y => Real.exp (lam * (-a - (y - c / 2)))),
    Kahane.integral_fst_shiftMeas c (fun ω => Real.exp (-(t * Real.exp (-a) * S ω)))]
  congr 1
  have h1 : (fun y : ℝ => Real.exp (lam * (-a - (y - c / 2)))) =
      fun y => Real.exp (lam * (c / 2 - a)) * Real.exp (-lam * y) := by
    funext y; rw [← Real.exp_add]; congr 1; ring
  have h2 := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := c)) (-lam)
  rw [mgf] at h2
  rw [h1, integral_const_mul, h2, ← Real.exp_add]
  congr 1; ring

section Group

variable {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

/-- **recursion for the Laplace transform** of `gM_n([0,1]²)` (Molchan/Robert–Vargas, D63) -/
theorem LogCorr.integral_exp_neg_gM_le (hZ : LogCorr Z P β c) (hβ : 0 ≤ β) {t : ℝ} (ht : 0 ≤ t)
    {lam : ℝ} (hlam : 0 ≤ lam) (a : ℝ) (m l k : ℕ) :
    ∫ ω, Real.exp (-(t * gM (Z (m + l)) P (m + k) (grid (m + k)) ω)) ∂P ≤
      Real.exp (lam * (lam + 1) * (β * (m * Real.log 2) + 2 * c) / 2 - lam * a) +
        (∫ ω, Real.exp (-(t * Real.exp (-a) * (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) ω)) ∂P) ^
          (grp0 m).card := by
  have hP := hZ.isProb
  have hc := hZ.c_nonneg
  set G := grp0 m
  have hG : G ⊆ grid m := filter_subset _ _
  have hpar : ∀ u ∈ G, ∀ v ∈ G, par u = par v := fun u hu v hv => by
    rw [(mem_filter.1 hu).2, (mem_filter.1 hv).2]
  have hne : G.Nonempty := grp0_nonempty m
  have hne' : Nonempty (↥G × ↥(grid k)) :=
    ⟨(⟨_, hne.choose_spec⟩, ⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩)⟩
  set Q := Measure.pi fun _ : ↥G => P
  set c' : ℝ≥0 := ⟨β * (m * Real.log 2) + 2 * c, by positivity⟩
  -- the two Gaussian vectors (as in `integral_group_rpow_le`)
  set f : Ω → ↥(grid k) → ℝ := fun ω a => Z l (cpt k a) ω
  have hfm : Measurable f := measurable_pi_iff.mpr fun a => hZ.meas l _
  have hfG : HasGaussianLaw f P := hasGaussianLaw_fintype (hZ.gauss l) (fun a : ↥(grid k) => cpt k a)
  have hmap : ∀ u : ↥G, Q.map (fun ω' : ↥G → Ω => ω' u) = P := fun u =>
    (measurePreserving_eval (fun _ : ↥G => P) u).map_eq
  have hB : ∀ u : ↥G, HasGaussianLaw (fun ω' : ↥G → Ω => f (ω' u)) Q := fun u =>
    ⟨(hfm.comp (measurable_pi_apply u)).aemeasurable, by
      rw [show (fun ω' : ↥G → Ω => f (ω' u)) = f ∘ (fun ω' => ω' u) from rfl,
        ← Measure.map_map hfm (measurable_pi_apply u), hmap u]
      exact hfG.isGaussian_map⟩
  have hind : iIndepFun (fun (u : ↥G) (ω' : ↥G → Ω) => f (ω' u)) Q :=
    iIndepFun_pi (X := fun _ => f) fun _ => hfm.aemeasurable
  have hYb : HasGaussianLaw (fun ω' (u : ↥G) => f (ω' u)) Q := hind.hasGaussianLaw hB
  let L : (↥G → ↥(grid k) → ℝ) →L[ℝ] (↥G × ↥(grid k) → ℝ) :=
    ContinuousLinearMap.pi fun p =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(grid k) => ℝ) p.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥G => ↥(grid k) → ℝ) p.1)
  have hY : HasGaussianLaw (fun (ω' : ↥G → Ω) (p : ↥G × ↥(grid k)) =>
      Z l (cpt k p.2) (ω' p.1)) Q := hYb.map L
  have hX : HasGaussianLaw (fun ω (p : ↥G × ↥(grid k)) =>
      Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω) P :=
    hasGaussianLaw_fintype (hZ.gauss (m + l)) (fun p : ↥G × ↥(grid k) => cpt (m + k) (sh k p.1 p.2))
  have hYm : ∀ p : ↥G × ↥(grid k), ∫ ω', Z l (cpt k p.2) (ω' p.1) ∂Q = 0 := fun p => by
    rw [integral_comp_eval (f := Z l (cpt k p.2)) (hZ.meas l _) p.1]; exact hZ.mean _ _
  have hmem : ∀ x, MemLp (Z l x) 2 P := fun x => (hZ.hasGaussianLaw l x).memLp_two
  have hcov : ∀ p p' : ↥G × ↥(grid k),
      cov[fun ω => Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω,
        fun ω => Z (m + l) (cpt (m + k) (sh k p'.1 p'.2)) ω; P] ≤
      cov[fun ω' => Z l (cpt k p.2) (ω' p.1), fun ω' => Z l (cpt k p'.2) (ω' p'.1); Q] + c' := by
    rintro ⟨u, a⟩ ⟨v, b⟩
    show _ ≤ _ + (β * (m * Real.log 2) + 2 * c)
    by_cases huv : u = v
    · subst huv
      rw [covariance_comp_eval (G := ↥G) (hZ.meas l _) (hZ.meas l _) u]
      exact hZ.cov_sh_le m l k (hG u.2) a.2 b.2
    · have hi : IndepFun (fun ω' : ↥G → Ω => Z l (cpt k a) (ω' u))
          (fun ω' : ↥G → Ω => Z l (cpt k b) (ω' v)) Q :=
        (hind.indepFun huv).comp (measurable_pi_apply a) (measurable_pi_apply b)
      have hu' : (u : ℕ × ℕ) ≠ v := fun h => huv (Subtype.ext h)
      rw [hi.covariance_eq_zero
        ((hmem _).comp_measurePreserving (measurePreserving_eval (fun _ : ↥G => P) u))
        ((hmem _).comp_measurePreserving (measurePreserving_eval (fun _ : ↥G => P) v)), zero_add]
      have := cov_sh_le_of_par hZ hβ (n := m + l) (hG u.2) (hG v.2) hu' (hpar _ u.2 _ v.2) a.2 b.2
      linarith
  have hK := kahane_laplace_shift ht
    (p := fun _ : ↥G × ↥(grid k) => (4 : ℝ)⁻¹ ^ m * (4 : ℝ)⁻¹ ^ k)
    (fun _ => by positivity) hX hY (fun p => hZ.mean _ _) hYm c' hcov hlam a
  -- identify both sides
  have hL : ∀ ω, ∑ u ∈ G, gM (Z (m + l)) P (m + k) (sub k u) ω =
      ∑ p : ↥G × ↥(grid k), (4 : ℝ)⁻¹ ^ m * (4 : ℝ)⁻¹ ^ k *
        Real.exp (Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω -
          Var[fun ω => Z (m + l) (cpt (m + k) (sh k p.1 p.2)) ω; P] / 2) := fun ω => by
    rw [← Finset.sum_coe_sort G, Fintype.sum_prod_type]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [gM_sub, Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun a => ?_
    rw [mul_assoc]
  have hR : ∀ ω' : ↥G → Ω, ∑ p : ↥G × ↥(grid k), (4 : ℝ)⁻¹ ^ m * (4 : ℝ)⁻¹ ^ k *
        Real.exp (Z l (cpt k p.2) (ω' p.1) -
          Var[fun ω' : ↥G → Ω => Z l (cpt k p.2) (ω' p.1); Q] / 2) =
      ∑ u : ↥G, (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) (ω' u) := fun ω' => by
    rw [Fintype.sum_prod_type]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [gM_grid, Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun a => ?_
    rw [variance_comp_eval (G := ↥G) (hZ.meas l _) u, mul_assoc]
  simp_rw [← hL] at hK
  simp_rw [hR] at hK
  -- monotonicity: the mass of the group is at most the total mass
  set T : Ω → ℝ := fun ω => ∑ u ∈ G, gM (Z (m + l)) P (m + k) (sub k u) ω
  have hTle : ∀ ω, T ω ≤ gM (Z (m + l)) P (m + k) (grid (m + k)) ω := fun ω => by
    rw [gM_grid_eq_sum_sub]
    exact sum_le_sum_of_subset_of_nonneg hG fun _ _ _ => gM_nonneg _ _ _ _
  have hTint : Integrable (fun ω => Real.exp (-(t * T ω))) P := by
    refine Integrable.of_bound (((Finset.measurable_sum _ fun u _ =>
      hZ.measurable_gM _ _ _).const_mul t).neg.exp.aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg ht (sum_nonneg fun u _ => gM_nonneg _ _ _ _)
  have h1 : ∫ ω, Real.exp (-(t * gM (Z (m + l)) P (m + k) (grid (m + k)) ω)) ∂P ≤
      ∫ ω, Real.exp (-(t * T ω)) ∂P :=
    integral_mono_of_nonneg (Eventually.of_forall fun ω => (Real.exp_pos _).le) hTint
      (Eventually.of_forall fun ω => Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_left (hTle ω) ht)))
  refine h1.trans (hK.trans_eq ?_)
  congr 1
  -- the product structure
  have hprod : ∀ ω' : ↥G → Ω, Real.exp (-(t * Real.exp (-a) *
      ∑ u : ↥G, (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) (ω' u))) =
      ∏ u : ↥G, Real.exp (-(t * Real.exp (-a) * (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) (ω' u))) := by
    intro ω'
    rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_pow
    (fun ω => Real.exp (-(t * Real.exp (-a) * (4 : ℝ)⁻¹ ^ m * gM (Z l) P k (grid k) ω))),
    Fintype.card_coe]

end Group

end DGMC

end LQGMetric
