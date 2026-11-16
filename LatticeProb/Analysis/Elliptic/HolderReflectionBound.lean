import LatticeProb.Analysis.Elliptic.HolderReflection

/-!
# Hölder estimates for reflection

Quantitative estimates for the coordinate reflection across a half-space boundary.
-/

namespace LatticeProb.Elliptic.HolderExtension

open LatticeProb.Euclidean.Lattice
open scoped BigOperators ENNReal

noncomputable section

private theorem radius_reflect_sub_le {d : ℕ} (i : Fin d) {a : ℝ} (ha : 1 ≤ a)
    (x y : E d) : radius (reflect i a x - reflect i a y) ≤ radius (x - y) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  apply (sq_le_sq₀ (radius_nonneg _) (radius_nonneg _)).mp
  rw [radius_sq, radius_sq]
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    have habs : |(-x i / a) - (-y i / a)| ≤ |x i - y i| := by
      rw [← sub_div, show -x i - -y i = -(x i - y i) by ring,
        abs_div, abs_neg, abs_of_pos ha0]
      exact div_le_self (abs_nonneg _) ha
    have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 habs
    simpa [reflect, sq_abs] using hs
  · simp [reflect, Function.update_of_ne hji]

private def reflectionLinear {d : ℕ} (i : Fin d) (a : ℝ) : E d →L[ℝ] E d :=
  ContinuousLinearMap.id ℝ (E d) + (-1 / a - 1) •
    ((ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).comp
      (ContinuousLinearMap.proj i))

private theorem reflectionLinear_apply {d : ℕ} (i : Fin d) (a : ℝ) (x : E d) :
    reflectionLinear i a x = reflect i a x := by
  ext j
  by_cases h : j = i
  · subst j
    simp [reflectionLinear, reflect]
    ring
  · simp [reflectionLinear, reflect, h]

private def reflectionFactor {d : ℕ} (i j : Fin d) (a : ℝ) : ℝ :=
  if j = i then -1 / a else 1

private theorem reflectionLinear_single {d : ℕ} (i j : Fin d) (a : ℝ) :
    reflectionLinear i a (Pi.single j 1) = reflectionFactor i j a • Pi.single j 1 := by
  ext k
  by_cases hji : j = i <;> by_cases hkj : k = j <;> by_cases hki : k = i <;>
    simp [reflectionLinear, reflectionFactor, hji, hkj, hki] at *

private theorem partialDeriv_reflect {d : ℕ} (i j : Fin d) (a : ℝ)
    (u : E d → ℝ) (x : E d) (hu : DifferentiableAt ℝ u (reflect i a x)) :
    partialDeriv j (fun y => u (reflect i a y)) x =
      reflectionFactor i j a * partialDeriv j u (reflect i a x) := by
  have hu' : DifferentiableAt ℝ u (reflectionLinear i a x) := by
    simpa only [reflectionLinear_apply] using hu
  have hd := hu'.hasFDerivAt.comp x (reflectionLinear i a).hasFDerivAt
  have heq : (fun y => u (reflect i a y)) = u ∘ reflectionLinear i a := by
    funext y
    simp only [Function.comp_apply, reflectionLinear_apply]
  rw [heq, partialDeriv, hd.fderiv]
  rw [ContinuousLinearMap.comp_apply, reflectionLinear_single, map_smul]
  simp only [reflectionLinear_apply, partialDeriv, smul_eq_mul]

private theorem secondPartial_eq_partial {d : ℕ} (u : E d → ℝ) (j k : Fin d)
    (x : E d) (hu : ContDiffAt ℝ 2 u x) :
    secondPartial j k u x = partialDeriv j (partialDeriv k u) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [secondPartial, partialDeriv, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change ((fderiv ℝ (fderiv ℝ u) x) (Pi.single j 1)) (Pi.single k 1) =
    (fderiv ℝ (fun y => (fderiv ℝ u y) (Pi.single k 1)) x) (Pi.single j 1)
  rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single k 1))]
  simp

private theorem secondPartial_reflect {d : ℕ} (i j k : Fin d) (a : ℝ)
    (u : E d → ℝ) (x : E d) (hu : ContDiffAt ℝ 2 u (reflect i a x)) :
    secondPartial j k (fun y => u (reflect i a y)) x =
      reflectionFactor i k a * reflectionFactor i j a *
        secondPartial j k u (reflect i a x) := by
  have hL : (⇑(reflectionLinear i a) : E d → E d) = reflect i a := by
    funext y
    exact reflectionLinear_apply i a y
  have hR : ContDiff ℝ 2 (reflect i a) := by
    rw [← hL]
    exact (reflectionLinear i a).contDiff
  have hcomp : ContDiffAt ℝ 2 (fun y => u (reflect i a y)) x := by
    simpa only [Function.comp_def] using hu.comp x hR.contDiffAt
  have hloc : ∀ᶠ y in nhds x, DifferentiableAt ℝ u (reflect i a y) := by
    have h := (hR.continuous.tendsto x).eventually (hu.eventually (by norm_num))
    filter_upwards [h] with y hy
    exact hy.differentiableAt (by norm_num)
  have heq : partialDeriv k (fun y => u (reflect i a y)) =ᶠ[nhds x]
      (fun y => reflectionFactor i k a * partialDeriv k u (reflect i a y)) := by
    filter_upwards [hloc] with y hy
    exact partialDeriv_reflect i k a u y hy
  have hdu : DifferentiableAt ℝ (partialDeriv k u) (reflect i a x) := by
    exact ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hducomp : DifferentiableAt ℝ (fun y => partialDeriv k u (reflect i a y)) x := by
    simpa only [Function.comp_def] using hdu.comp x (hR.differentiable (by norm_num) x)
  rw [secondPartial_eq_partial _ _ _ _ hcomp, secondPartial_eq_partial _ _ _ _ hu]
  change (fderiv ℝ (partialDeriv k (fun y => u (reflect i a y))) x) (Pi.single j 1) = _
  rw [heq.fderiv_eq, fderiv_const_mul hducomp]
  simp only [smul_apply, smul_eq_mul]
  change reflectionFactor i k a * partialDeriv j (fun y => partialDeriv k u (reflect i a y)) x = _
  rw [partialDeriv_reflect i j a (partialDeriv k u) x hdu]
  ring

private theorem secondPartial_add {d : ℕ} (j k : Fin d) (f g : E d → ℝ) (x : E d)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    secondPartial j k (fun y => f y + g y) x = secondPartial j k f x +
      secondPartial j k g x := by
  simp only [secondPartial, fun_iteratedFDeriv_add_apply hf hg, add_apply]

private theorem secondPartial_sub {d : ℕ} (j k : Fin d) (f g : E d → ℝ) (x : E d)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    secondPartial j k (fun y => f y - g y) x = secondPartial j k f x -
      secondPartial j k g x := by
  simp only [secondPartial, fun_iteratedFDeriv_sub_apply hf hg, sub_apply]

private theorem secondPartial_const_mul {d : ℕ} (j k : Fin d) (c : ℝ) (f : E d → ℝ)
    (x : E d) (hf : ContDiffAt ℝ 2 f x) :
    secondPartial j k (fun y => c * f y) x = c * secondPartial j k f x := by
  simp only [secondPartial, ← smul_eq_mul, iteratedFDeriv_const_smul_apply' hf,
    smul_apply]

private theorem reflect_mem_halfSpace {d : ℕ} (i : Fin d) {a : ℝ} (ha : 0 < a)
    {x : E d} (hx : x i < 0) : reflect i a x ∈ halfSpace i := by
  change 0 < (reflect i a x) i
  simp only [reflect, Function.update_self]
  exact div_pos (neg_pos.mpr hx) ha

private theorem contDiffAt_reflect_comp {d : ℕ} (i : Fin d) {a : ℝ} (ha : 0 < a)
    (u : E d → ℝ) (hu : ContDiffOn ℝ 2 u (halfSpace i))
    {x : E d} (hx : x i < 0) : ContDiffAt ℝ 2 (fun y => u (reflect i a y)) x := by
  have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
  have hl := hu.contDiffAt (hopen.mem_nhds (reflect_mem_halfSpace i ha hx))
  have hR : ContDiff ℝ 2 (reflect i a) := by
    have he : (⇑(reflectionLinear i a) : E d → E d) = reflect i a := by
      funext y
      exact reflectionLinear_apply i a y
    rw [← he]
    exact (reflectionLinear i a).contDiff
  simpa only [Function.comp_def] using hl.comp x hR.contDiffAt

private theorem secondPartial_reflection_lower {d : ℕ} (i j k : Fin d)
    (u v : E d → ℝ) (hu : ContDiffOn ℝ 2 u (halfSpace i))
    (hv : ∀ x, x i < 0 → v x = 6 * u (reflect i 1 x) -
      32 * u (reflect i 2 x) + 27 * u (reflect i 3 x))
    {x : E d} (hx : x i < 0) :
    secondPartial j k v x =
      6 * (reflectionFactor i k 1 * reflectionFactor i j 1 *
        secondPartial j k u (reflect i 1 x)) -
      32 * (reflectionFactor i k 2 * reflectionFactor i j 2 *
        secondPartial j k u (reflect i 2 x)) +
      27 * (reflectionFactor i k 3 * reflectionFactor i j 3 *
        secondPartial j k u (reflect i 3 x)) := by
  let f : ℝ → E d → ℝ := fun a y => u (reflect i a y)
  have h1 : ContDiffAt ℝ 2 (f 1) x := contDiffAt_reflect_comp i (by norm_num) u hu hx
  have h2 : ContDiffAt ℝ 2 (f 2) x := contDiffAt_reflect_comp i (by norm_num) u hu hx
  have h3 : ContDiffAt ℝ 2 (f 3) x := contDiffAt_reflect_comp i (by norm_num) u hu hx
  have hlocal : v =ᶠ[nhds x] (fun y => 6 * f 1 y - 32 * f 2 y + 27 * f 3 y) := by
    have hopen : IsOpen {y : E d | y i < 0} := isOpen_lt (continuous_apply i) continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hv y hy
  have hsec : secondPartial j k v x = secondPartial j k
      (fun y => 6 * f 1 y - 32 * f 2 y + 27 * f 3 y) x := by
    unfold secondPartial
    rw [(hlocal.iteratedFDeriv ℝ 2).eq_of_nhds]
  have hc1 : ContDiffAt ℝ 2 (fun y => 6 * f 1 y) x := contDiffAt_const.mul h1
  have hc2 : ContDiffAt ℝ 2 (fun y => 32 * f 2 y) x := contDiffAt_const.mul h2
  have hc3 : ContDiffAt ℝ 2 (fun y => 27 * f 3 y) x := contDiffAt_const.mul h3
  rw [hsec, secondPartial_add _ _ _ _ _ (hc1.sub hc2) hc3,
    secondPartial_sub _ _ _ _ _ hc1 hc2,
    secondPartial_const_mul _ _ _ _ _ h1, secondPartial_const_mul _ _ _ _ _ h2,
    secondPartial_const_mul _ _ _ _ _ h3]
  have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
  have hdu (a : ℝ) (ha : 0 < a) : ContDiffAt ℝ 2 u (reflect i a x) :=
    hu.contDiffAt (hopen.mem_nhds (reflect_mem_halfSpace i ha hx))
  rw [secondPartial_reflect i j k 1 u x (hdu 1 (by norm_num)),
    secondPartial_reflect i j k 2 u x (hdu 2 (by norm_num)),
    secondPartial_reflect i j k 3 u x (hdu 3 (by norm_num))]

private theorem partialDeriv_reflection_lower {d : ℕ} (i j : Fin d)
    (u v : E d → ℝ) (hu : ContDiffOn ℝ 2 u (halfSpace i))
    (hv : ∀ x, x i < 0 → v x = 6 * u (reflect i 1 x) -
      32 * u (reflect i 2 x) + 27 * u (reflect i 3 x))
    {x : E d} (hx : x i < 0) :
    partialDeriv j v x =
      6 * (reflectionFactor i j 1 * partialDeriv j u (reflect i 1 x)) -
      32 * (reflectionFactor i j 2 * partialDeriv j u (reflect i 2 x)) +
      27 * (reflectionFactor i j 3 * partialDeriv j u (reflect i 3 x)) := by
  let f : ℝ → E d → ℝ := fun a y => u (reflect i a y)
  have h1 : DifferentiableAt ℝ (f 1) x :=
    (contDiffAt_reflect_comp i (by norm_num) u hu hx).differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (f 2) x :=
    (contDiffAt_reflect_comp i (by norm_num) u hu hx).differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ (f 3) x :=
    (contDiffAt_reflect_comp i (by norm_num) u hu hx).differentiableAt (by norm_num)
  have hlocal : v =ᶠ[nhds x] (fun y => 6 * f 1 y - 32 * f 2 y + 27 * f 3 y) := by
    have hopen : IsOpen {y : E d | y i < 0} := isOpen_lt (continuous_apply i) continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hv y hy
  have hsec : partialDeriv j v x = partialDeriv j
      (fun y => 6 * f 1 y - 32 * f 2 y + 27 * f 3 y) x := by
    simp only [partialDeriv, hlocal.fderiv_eq]
  rw [hsec]
  unfold partialDeriv at ⊢
  change (fderiv ℝ (((fun y => 6 * f 1 y) - (fun y => 32 * f 2 y)) +
    (fun y => 27 * f 3 y)) x) (Pi.single j 1) = _
  rw [fderiv_add ((h1.const_mul 6).sub (h2.const_mul 32)) (h3.const_mul 27),
    fderiv_sub (h1.const_mul 6) (h2.const_mul 32), fderiv_const_mul h1,
    fderiv_const_mul h2, fderiv_const_mul h3]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  change 6 * partialDeriv j (f 1) x - 32 * partialDeriv j (f 2) x +
    27 * partialDeriv j (f 3) x = _
  have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
  have hdu (a : ℝ) (ha : 0 < a) : DifferentiableAt ℝ u (reflect i a x) :=
    (hu.contDiffAt (hopen.mem_nhds (reflect_mem_halfSpace i ha hx))).differentiableAt
      (by norm_num)
  rw [partialDeriv_reflect i j 1 u x (hdu 1 (by norm_num)),
    partialDeriv_reflect i j 2 u x (hdu 2 (by norm_num)),
    partialDeriv_reflect i j 3 u x (hdu 3 (by norm_num))]
  rfl

private theorem reflectionFactor_abs_le {d : ℕ} (i j : Fin d) {a : ℝ} (ha : 1 ≤ a) :
    |reflectionFactor i j a| ≤ 1 := by
  by_cases h : j = i
  · simp only [reflectionFactor, h, ↓reduceIte, abs_div, abs_neg, abs_one,
      abs_of_pos (lt_of_lt_of_le zero_lt_one ha)]
    exact (div_le_one₀ (lt_of_lt_of_le zero_lt_one ha)).2 ha
  · simp [reflectionFactor, h]

private theorem reflectionFactor_moment {d : ℕ} (i j k : Fin d) :
    6 * (reflectionFactor i k 1 * reflectionFactor i j 1) -
      32 * (reflectionFactor i k 2 * reflectionFactor i j 2) +
      27 * (reflectionFactor i k 3 * reflectionFactor i j 3) = 1 := by
  by_cases hji : j = i <;> by_cases hki : k = i <;>
    norm_num [reflectionFactor, hji, hki]

private theorem radius_reflect_sub_upper_le {d : ℕ} (i : Fin d) {a : ℝ} (ha : 1 ≤ a)
    (x y : E d) (hx : x i ≤ 0) (hy : 0 ≤ y i) :
    radius (reflect i a x - y) ≤ radius (x - y) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  apply (sq_le_sq₀ (radius_nonneg _) (radius_nonneg _)).mp
  rw [radius_sq, radius_sq]
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    have hxi : 0 ≤ -x i / a := div_nonneg (neg_nonneg.mpr hx) ha0.le
    have hxa : -x i / a ≤ -x i := div_le_self (neg_nonneg.mpr hx) ha
    have habs : |(-x i / a) - y i| ≤ |x i - y i| := by
      rw [abs_le]
      have hxy : x i - y i ≤ 0 := sub_nonpos.mpr (hx.trans hy)
      rw [abs_of_nonpos hxy]
      constructor <;> linarith
    have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 habs
    simpa [reflect, sq_abs] using hs
  · simp [reflect, Function.update_of_ne hji]

private theorem weighted_three_bound {a b c p q r M : ℝ}
    (_hM : 0 ≤ M) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1)
    (hp : |p| ≤ M) (hq : |q| ≤ M) (hr : |r| ≤ M) :
    |6 * (a * p) - 32 * (b * q) + 27 * (c * r)| ≤ 65 * M := by
  have hap : |a * p| ≤ M := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg p]
  have hbq : |b * q| ≤ M := by
    rw [abs_mul]
    nlinarith [abs_nonneg b, abs_nonneg q]
  have hcr : |c * r| ≤ M := by
    rw [abs_mul]
    nlinarith [abs_nonneg c, abs_nonneg r]
  calc
    |6 * (a * p) - 32 * (b * q) + 27 * (c * r)| ≤
        |6 * (a * p)| + |32 * (b * q)| + |27 * (c * r)| :=
      calc
        _ ≤ |6 * (a * p) - 32 * (b * q)| + |27 * (c * r)| := abs_add_le _ _
        _ ≤ _ := by
          gcongr
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (6 * (a * p)) (-(32 * (b * q))))
    _ = 6 * |a * p| + 32 * |b * q| + 27 * |c * r| := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 27)]
    _ ≤ 65 * M := by linarith

private theorem reflectionFactor_product_abs_le {d : ℕ} (i j k : Fin d) {a : ℝ}
    (ha : 1 ≤ a) : |reflectionFactor i k a * reflectionFactor i j a| ≤ 1 := by
  rw [abs_mul]
  nlinarith [reflectionFactor_abs_le i j ha, reflectionFactor_abs_le i k ha,
    abs_nonneg (reflectionFactor i j a), abs_nonneg (reflectionFactor i k a)]

private theorem halfSpace_closure_eq {d : ℕ} (i : Fin d) :
    closure (halfSpace i) = {x : E d | 0 ≤ x i} := by
  change closure ((fun x : E d => x i) ⁻¹' Set.Ioi (0 : ℝ)) = _
  rw [← (isOpenMap_eval i).preimage_closure_eq_closure_preimage (continuous_apply i),
    closure_Ioi]
  rfl

private theorem bound_of_halfSpaces {d : ℕ} (i : Fin d) (f : E d → ℝ)
    (hf : Continuous f) (M : ℝ) (hupper : ∀ x ∈ halfSpace i, |f x| ≤ M)
    (hlower : ∀ x : E d, x i < 0 → |f x| ≤ M) : ∀ x, |f x| ≤ M := by
  have hclosed : IsClosed {x : E d | |f x| ≤ M} :=
    isClosed_le hf.abs continuous_const
  have hclosure : closure (halfSpace i) ⊆ {x : E d | |f x| ≤ M} :=
    hclosed.closure_subset_iff.mpr hupper
  intro x
  by_cases hx : x i < 0
  · exact hlower x hx
  · exact hclosure (by rw [halfSpace_closure_eq]; exact le_of_not_gt hx)

private theorem holder_bound_of_off_boundary {d : ℕ} (i : Fin d) (f : E d → ℝ)
    (hf : Continuous f) {σ M : ℝ} (hσ : 0 ≤ σ)
    (h : ∀ x y : E d, x i ≠ 0 → y i ≠ 0 →
      |f x - f y| ≤ M * radius (x - y) ^ σ) :
    ∀ x y : E d, |f x - f y| ≤ M * radius (x - y) ^ σ := by
  let S : Set (E d) := {x | x i ≠ 0}
  have hd : Dense S := (dense_compl_singleton (0 : ℝ)).preimage (isOpenMap_eval i)
  have hdprod : Dense (S ×ˢ S) := hd.prod hd
  let T : Set (E d × E d) := {p | |f p.1 - f p.2| ≤ M * radius (p.1 - p.2) ^ σ}
  have hclosed : IsClosed T := by
    apply isClosed_le ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).abs
    exact continuous_const.mul ((Real.continuous_rpow_const hσ).comp
      ((radius_continuous d).comp (continuous_fst.sub continuous_snd)))
  have hsub : S ×ˢ S ⊆ T := by
    intro p hp
    exact h p.1 p.2 hp.1 hp.2
  have hall : closure (S ×ˢ S) ⊆ T := hclosed.closure_subset_iff.mpr hsub
  intro x y
  change (x, y) ∈ T
  apply hall
  rw [hdprod.closure_eq]
  exact Set.mem_univ _

private theorem radius_sub_comm {d : ℕ} (x y : E d) : radius (x - y) = radius (y - x) := by
  simp only [radius, Pi.sub_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem reflection_scalar_holder_bound {d : ℕ} (i : Fin d)
    (f g : E d → ℝ) (hf : Continuous f) {σ H A B C : ℝ}
    (hσ : 0 ≤ σ) (hH : 0 ≤ H) (hA : |A| ≤ 1) (hB : |B| ≤ 1) (hC : |C| ≤ 1)
    (hm : 6 * A - 32 * B + 27 * C = 1)
    (hpos : ∀ x ∈ halfSpace i, f x = g x)
    (hneg : ∀ x : E d, x i < 0 → f x = 6 * (A * g (reflect i 1 x)) -
      32 * (B * g (reflect i 2 x)) + 27 * (C * g (reflect i 3 x)))
    (hg : ∀ x ∈ halfSpace i, ∀ y ∈ halfSpace i,
      |g x - g y| ≤ H * radius (x - y) ^ σ) :
    ∀ x y : E d, |f x - f y| ≤ 65 * H * radius (x - y) ^ σ := by
  apply holder_bound_of_off_boundary i f hf hσ
  intro x y hx hy
  have hnonneg : 0 ≤ H * radius (x - y) ^ σ :=
    mul_nonneg hH (Real.rpow_nonneg (radius_nonneg _) _)
  have hrpow {s t : E d} (hst : radius s ≤ radius t) :
      H * radius s ^ σ ≤ H * radius t ^ σ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (radius_nonneg _) hst hσ) hH
  have hsame (x y : E d) (hx : x i < 0) (hy : y i < 0) :
      |f x - f y| ≤ 65 * H * radius (x - y) ^ σ := by
    have hi (a : ℝ) (ha : 1 ≤ a) :
        |g (reflect i a x) - g (reflect i a y)| ≤ H * radius (x - y) ^ σ :=
      (hg _ (reflect_mem_halfSpace i (lt_of_lt_of_le zero_lt_one ha) hx)
        _ (reflect_mem_halfSpace i (lt_of_lt_of_le zero_lt_one ha) hy)).trans
          (hrpow (radius_reflect_sub_le i ha x y))
    have hw := weighted_three_bound
      (mul_nonneg hH (Real.rpow_nonneg (radius_nonneg (x - y)) σ)) hA hB hC
      (hi 1 (by norm_num)) (hi 2 (by norm_num)) (hi 3 (by norm_num))
    have he : f x - f y =
        6 * (A * (g (reflect i 1 x) - g (reflect i 1 y))) -
        32 * (B * (g (reflect i 2 x) - g (reflect i 2 y))) +
        27 * (C * (g (reflect i 3 x) - g (reflect i 3 y))) := by
      rw [hneg x hx, hneg y hy]
      ring
    rw [he]
    convert hw using 1; ring
  have hcross (x y : E d) (hx : x i < 0) (hy : 0 < y i) :
      |f x - f y| ≤ 65 * H * radius (x - y) ^ σ := by
    have hi (a : ℝ) (ha : 1 ≤ a) :
        |g (reflect i a x) - g y| ≤ H * radius (x - y) ^ σ :=
      (hg _ (reflect_mem_halfSpace i (lt_of_lt_of_le zero_lt_one ha) hx) _ hy).trans
        (hrpow (radius_reflect_sub_upper_le i ha x y hx.le hy.le))
    have hw := weighted_three_bound
      (mul_nonneg hH (Real.rpow_nonneg (radius_nonneg (x - y)) σ)) hA hB hC
      (hi 1 (by norm_num)) (hi 2 (by norm_num)) (hi 3 (by norm_num))
    have he : f x - f y =
        6 * (A * (g (reflect i 1 x) - g y)) -
        32 * (B * (g (reflect i 2 x) - g y)) +
        27 * (C * (g (reflect i 3 x) - g y)) := by
      rw [hneg x hx, hpos y hy]
      have hm' := congrArg (fun t : ℝ => t * g y) hm
      nlinarith [hm']
    rw [he]
    convert hw using 1; ring
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · exact hsame x y hx' hy'
  · exact hcross x y hx' hy'
  · simpa only [abs_sub_comm, radius_sub_comm y x] using hcross y x hy' hx'
  · rw [hpos x hx', hpos y hy']
    have hb := hg x hx' y hy'
    nlinarith

private theorem holderSeminorm_le_of_increment {d : ℕ} {S : Set (E d)}
    {g : E d → ℝ} {σ B : ℝ}
    (hg : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ B * radius (x - y) ^ σ) :
    holderSeminorm σ S g ≤ ENNReal.ofReal B := by
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => ENNReal.ofReal_le_ofReal ?_
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (radius_pos (sub_ne_zero.mpr hxy)) σ)).mpr
    (hg x hx y hy)

private theorem secondPartial_reflection_holder {d : ℕ} (i j k : Fin d) {σ : ℝ}
    (hσ : 0 < σ) (u v : E d → ℝ) (hu : ContDiffOn ℝ 2 u (halfSpace i))
    (hv : ContDiff ℝ 2 v) (heq : Set.EqOn v u (halfSpace i))
    (href : ∀ x, x i < 0 → v x = 6 * u (reflect i 1 x) -
      32 * u (reflect i 2 x) + 27 * u (reflect i 3 x))
    (hn : c0HolderNorm σ (halfSpace i) (secondPartial j k u) < ⊤) :
    holderSeminorm σ Set.univ (secondPartial j k v) ≤
      ENNReal.ofReal 65 * holderSeminorm σ (halfSpace i) (secondPartial j k u) := by
  let H := (holderSeminorm σ (halfSpace i) (secondPartial j k u)).toReal
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hf : Continuous (secondPartial j k v) := by
    unfold secondPartial
    exact hv.continuous_iteratedFDeriv'.eval continuous_const
  have hpos : ∀ x ∈ halfSpace i, secondPartial j k v x = secondPartial j k u x := by
    intro x hx
    have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
    have hlocal : v =ᶠ[nhds x] u := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact heq hy
    simp only [secondPartial, (hlocal.iteratedFDeriv ℝ 2).eq_of_nhds]
  have hneg : ∀ x : E d, x i < 0 → secondPartial j k v x =
      6 * ((reflectionFactor i k 1 * reflectionFactor i j 1) *
        secondPartial j k u (reflect i 1 x)) -
      32 * ((reflectionFactor i k 2 * reflectionFactor i j 2) *
        secondPartial j k u (reflect i 2 x)) +
      27 * ((reflectionFactor i k 3 * reflectionFactor i j 3) *
        secondPartial j k u (reflect i 3 x)) := by
    intro x hx
    rw [secondPartial_reflection_lower i j k u v hu href hx]
  have hinc : ∀ x y : E d, |secondPartial j k v x - secondPartial j k v y| ≤
      65 * H * radius (x - y) ^ σ := by
    apply reflection_scalar_holder_bound i _ _ hf hσ.le hH
      (reflectionFactor_product_abs_le i j k (by norm_num : (1 : ℝ) ≤ 1))
      (reflectionFactor_product_abs_le i j k (by norm_num : (1 : ℝ) ≤ 2))
      (reflectionFactor_product_abs_le i j k (by norm_num : (1 : ℝ) ≤ 3))
      (reflectionFactor_moment i j k) hpos hneg
    intro x hx y hy
    exact abs_sub_le_holderSeminorm_toReal hn hx hy
  have hfinite : holderSeminorm σ (halfSpace i) (secondPartial j k u) ≠ ⊤ :=
    (lt_of_le_of_lt le_add_self hn).ne
  calc
    _ ≤ ENNReal.ofReal (65 * H) := holderSeminorm_le_of_increment (fun x _ y _ => hinc x y)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfinite]

private theorem supNorm_reflection_le {d : ℕ} (i : Fin d)
    (f g : E d → ℝ) (hf : Continuous f) {A B C : ℝ}
    (hA : |A| ≤ 1) (hB : |B| ≤ 1) (hC : |C| ≤ 1)
    (hpos : ∀ x ∈ halfSpace i, f x = g x)
    (hneg : ∀ x : E d, x i < 0 → f x = 6 * (A * g (reflect i 1 x)) -
      32 * (B * g (reflect i 2 x)) + 27 * (C * g (reflect i 3 x)))
    (hn : supNorm (halfSpace i) g < ⊤) :
    supNorm Set.univ f ≤ ENNReal.ofReal 65 * supNorm (halfSpace i) g := by
  let M := (supNorm (halfSpace i) g).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hbound : ∀ x : E d, |f x| ≤ 65 * M := by
    apply bound_of_halfSpaces i f hf
    · intro x hx
      rw [hpos x hx]
      have hh := abs_le_supNorm_toReal hn hx
      dsimp [M] at *
      linarith
    · intro x hx
      rw [hneg x hx]
      apply weighted_three_bound hM hA hB hC
      · exact abs_le_supNorm_toReal hn (reflect_mem_halfSpace i (by norm_num) hx)
      · exact abs_le_supNorm_toReal hn (reflect_mem_halfSpace i (by norm_num) hx)
      · exact abs_le_supNorm_toReal hn (reflect_mem_halfSpace i (by norm_num) hx)
  calc
    _ ≤ ENNReal.ofReal (65 * M) := iSup_le fun x => iSup_le fun _ =>
      ENNReal.ofReal_le_ofReal (hbound x)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hn.ne]

/-- The three-term reflection is bounded in the coordinate Hölder norm. -/
theorem halfSpace_reflection_bound {d : ℕ} (i : Fin d) {σ : ℝ}
    (hσ : 0 < σ) (_hσ' : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u v : E d → ℝ),
      ContDiffOn ℝ 2 u (halfSpace i) →
      c2HolderNorm σ (halfSpace i) u < ⊤ → ContDiff ℝ 2 v →
      Set.EqOn v u (halfSpace i) →
      (∀ x, x i < 0 → v x = 6 * u (reflect i 1 x) -
        32 * u (reflect i 2 x) + 27 * u (reflect i 3 x)) →
      c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C *
        c2HolderNorm σ (halfSpace i) u := by
  refine ⟨65, by norm_num, ?_⟩
  intro u v hu hn hv heq href
  have hn' := hn
  simp only [c2HolderNorm, ENNReal.add_lt_top, ENNReal.sum_lt_top,
    Finset.mem_univ, true_implies] at hn'
  have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
  have hlocal (x : E d) (hx : x ∈ halfSpace i) : v =ᶠ[nhds x] u := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact heq hy
  have hpos1 (j : Fin d) : ∀ x ∈ halfSpace i, partialDeriv j v x = partialDeriv j u x := by
    intro x hx
    simp only [partialDeriv, (hlocal x hx).fderiv_eq]
  have hpos2 (j k : Fin d) : ∀ x ∈ halfSpace i,
      secondPartial j k v x = secondPartial j k u x := by
    intro x hx
    simp only [secondPartial, ((hlocal x hx).iteratedFDeriv ℝ 2).eq_of_nhds]
  have hb0 : supNorm Set.univ v ≤ ENNReal.ofReal 65 * supNorm (halfSpace i) u := by
    apply supNorm_reflection_le i v u hv.continuous (A := 1) (B := 1) (C := 1)
      (by norm_num) (by norm_num) (by norm_num) (fun x hx => heq hx) ?_ hn'.1.1.1
    intro x hx
    simpa only [one_mul] using href x hx
  have hb1 (j : Fin d) : supNorm Set.univ (partialDeriv j v) ≤
      ENNReal.ofReal 65 * supNorm (halfSpace i) (partialDeriv j u) := by
    have hc : Continuous (partialDeriv j v) :=
      ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous
    apply supNorm_reflection_le i _ _ hc
      (reflectionFactor_abs_le i j (by norm_num : (1 : ℝ) ≤ 1))
      (reflectionFactor_abs_le i j (by norm_num : (1 : ℝ) ≤ 2))
      (reflectionFactor_abs_le i j (by norm_num : (1 : ℝ) ≤ 3)) (hpos1 j) ?_ (hn'.1.1.2 j)
    intro x hx
    exact partialDeriv_reflection_lower i j u v hu href hx
  have hb2 (j k : Fin d) : supNorm Set.univ (secondPartial j k v) ≤
      ENNReal.ofReal 65 * supNorm (halfSpace i) (secondPartial j k u) := by
    have hc : Continuous (secondPartial j k v) := by
      unfold secondPartial
      exact hv.continuous_iteratedFDeriv'.eval continuous_const
    apply supNorm_reflection_le i _ _ hc
      (reflectionFactor_product_abs_le i j k (by norm_num : (1 : ℝ) ≤ 1))
      (reflectionFactor_product_abs_le i j k (by norm_num : (1 : ℝ) ≤ 2))
      (reflectionFactor_product_abs_le i j k (by norm_num : (1 : ℝ) ≤ 3))
      (hpos2 j k) ?_ (hn'.1.2 j k)
    intro x hx
    exact secondPartial_reflection_lower i j k u v hu href hx
  have hbH (j k : Fin d) : holderSeminorm σ Set.univ (secondPartial j k v) ≤
      ENNReal.ofReal 65 * holderSeminorm σ (halfSpace i) (secondPartial j k u) :=
    secondPartial_reflection_holder i j k hσ u v hu hv heq href
      (ENNReal.add_lt_top.mpr ⟨hn'.1.2 j k, hn'.2 j k⟩)
  unfold c2HolderNorm
  calc
    _ ≤ ENNReal.ofReal 65 * supNorm (halfSpace i) u +
        (∑ j, ENNReal.ofReal 65 * supNorm (halfSpace i) (partialDeriv j u)) +
        (∑ j, ∑ k, ENNReal.ofReal 65 * supNorm (halfSpace i) (secondPartial j k u)) +
        (∑ j, ∑ k, ENNReal.ofReal 65 * holderSeminorm σ (halfSpace i) (secondPartial j k u)) :=
      add_le_add (add_le_add (add_le_add hb0 (Finset.sum_le_sum fun j _ => hb1 j))
        (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hb2 j k))
        (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hbH j k)
    _ = _ := by simp only [mul_add, Finset.mul_sum]

end
end LatticeProb.Elliptic.HolderExtension
