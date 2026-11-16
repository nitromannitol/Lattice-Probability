import LatticeProb.Analysis.Schauder.Statement
import LatticeProb.Analysis.Schauder.MaxPrinciple
import LatticeProb.Analysis.Schauder.SineSum

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.ContinuumC2`.

# Second-order bounds of the Dirichlet inverse

The bound `|u| + ‖∇u‖ + ‖∇²u‖ ≤ C c3Norm f / D` on `ℝ^d` for `u = (−DΔ_Q)⁻¹ f`, granting
the interior Schauder estimate `SchauderInterior`: the maximum principle on the cube and the
reflection symmetry give the sup bound, the Schauder estimate with `α = 1/2` the Hessian, and the
mean value inequality the gradient.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- A product of signs `±1` has absolute value `1`. -/
theorem abs_prod_ite_neg_one_eq_one (σ : Fin d → Bool) :
    |∏ i, if σ i then (-1 : ℝ) else 1| = 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp

/-- The Dirichlet inverse of a test function is odd in each coordinate and `2`-periodic, since
each of its sine modes is. -/
theorem dirichletInverse_flipIso_add (D : ℝ) (f : Euc d → ℝ) (σ : Fin d → Bool) (n : Fin d → ℤ)
    (z : Euc d) :
    dirichletInverse D f (flipIso σ z + evenShift n) =
      (∏ i, if σ i then (-1 : ℝ) else 1) * dirichletInverse D f z := by
  unfold dirichletInverse
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [sineMode_flipIso_add]
  ring

/-- A test function is bounded in absolute value by `c3Norm`. -/
theorem abs_le_c3Norm {f : Euc d → ℝ} (hf : Sobolev.IsTestFn (unitCube d) f) (z : Euc d) :
    |f z| ≤ c3Norm f := by
  have h := norm_iteratedFDeriv_le_c3Norm hf (m := 0) (by norm_num) z
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

/-- The Laplacian of the Dirichlet inverse is `−F/D`, where `F` is the sine series of `f`. -/
theorem laplacianSum_dirichletInverse_eq (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (z : Euc d) :
    laplacianSum (dirichletInverse D f) z = -(sineSum f z) / D := by
  have h := neg_mul_laplacianSum_dirichletInverse hd hD f hf z
  field_simp
  linarith

/-- **Sup bound of the Dirichlet inverse**: `|u| ≤ c3Norm f / (8D)` on `ℝ^d`, by the maximum
principle on the closed cube (`|Δu| = |f|/D` in the open cube) and the reflection symmetry of the
sine series. -/
theorem abs_dirichletInverse_le (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (z : Euc d) :
    |dirichletInverse D f z| ≤ c3Norm f / D / 8 := by
  obtain ⟨hsm, hlap, hzero, -⟩ := dirichletInverse_spec hd D hD f hf
  have hclosure : ∀ w ∈ closure (unitCube d),
      |dirichletInverse D f w| ≤ c3Norm f / D / 8 := by
    refine abs_le_of_abs_laplacian_le hd _ (hsm 2) _ hzero fun w hw => ?_
    show |laplacianSum (dirichletInverse D f) w| ≤ c3Norm f / D
    have h2 : laplacianSum (dirichletInverse D f) w = -(f w) / D := by
      have := hlap w hw
      field_simp
      linarith
    rw [h2, abs_div, abs_neg, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (abs_le_c3Norm hf w) hD.le
  obtain ⟨σ, n, hmem⟩ := exists_flipIso_add_mem_closedCube z
  have h := hclosure _ (closedCube_subset_closure_unitCube hmem)
  rwa [dirichletInverse_flipIso_add, abs_mul, abs_prod_ite_neg_one_eq_one, one_mul] at h

/-- The sine series of a test function is bounded in absolute value by `c3Norm`. -/
theorem abs_sineSum_le_c3Norm (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (z : Euc d) : |sineSum f z| ≤ c3Norm f := by
  have h := (sineSum_spec hd 1 one_pos f hf).2.2 0 (by norm_num) z
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

/-- The sine series of a test function is `c3Norm`-Lipschitz on `ℝ^d`, since its first
derivative is bounded by `c3Norm`. -/
theorem abs_sineSum_sub_le (hd : 1 ≤ d) (f : Euc d → ℝ) (hf : Sobolev.IsTestFn (unitCube d) f)
    (x y : Euc d) : |sineSum f x - sineSum f y| ≤ c3Norm f * dist x y := by
  obtain ⟨hsm, -, hbd⟩ := sineSum_spec hd 1 one_pos f hf
  have h := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := sineSum f) (C := c3Norm f) (x := y) (y := x)
    (fun w _ => ((hsm 1).differentiable (by norm_num)).differentiableAt) (fun w _ => by
      rw [← norm_iteratedFDeriv_one]
      exact hbd 1 (by norm_num) w) (Set.mem_univ _) (Set.mem_univ _)
  rwa [Real.norm_eq_abs, ← dist_eq_norm] at h

/-- On a set of diameter at most `4`, a distance is at most twice its square root. -/
theorem le_two_mul_rpow_half_of_le_four {r : ℝ} (h0 : 0 ≤ r) (h4 : r ≤ 4) :
    r ≤ 2 * r ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  have h1 : Real.sqrt r ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  have h2 := Real.mul_self_sqrt h0
  have h3 := Real.sqrt_nonneg r
  nlinarith

/-- **Hessian bound of the Dirichlet inverse**: granting the interior Schauder estimate with
`α = 1/2` on balls of radius `2`, `‖D²u‖ ≤ C c3Norm f / D` on `ℝ^d`, with `C` independent of `D`
and `f`. -/
theorem exists_norm_iteratedFDeriv_two_dirichletInverse_le (hd : 1 ≤ d)
    (hSch : LatticeProb.Analysis.Schauder.SchauderInterior d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : ℝ), 0 < D → ∀ f : Euc d → ℝ, Sobolev.IsTestFn (unitCube d) f →
      ∀ z : Euc d, ‖iteratedFDeriv ℝ 2 (dirichletInverse D f) z‖ ≤ C * c3Norm f / D := by
  obtain ⟨C₀, hC₀⟩ := hSch (1 / 2) (by norm_num) (by norm_num)
  refine ⟨3 * max C₀ 0, by positivity, fun D hD f hf x₀ => ?_⟩
  have hc : 0 ≤ c3Norm f := (abs_nonneg _).trans (abs_le_c3Norm hf 0)
  have hcD : 0 ≤ c3Norm f / D := div_nonneg hc hD.le
  have hLap : ∀ x, laplacianSum (dirichletInverse D f) x = -(sineSum f x) / D :=
    laplacianSum_dirichletInverse_eq hd hD f hf
  have hsch := hC₀ (dirichletInverse D f) x₀ (c3Norm f / D / 8) (2 * c3Norm f / D)
    ((dirichletInverse_spec hd D hD f hf).1 2)
    (fun x _ => abs_dirichletInverse_le hd hD f hf x) (fun x hx y hy => by
      change |laplacianSum (dirichletInverse D f) x| ≤ _ ∧
        |laplacianSum (dirichletInverse D f) x - laplacianSum (dirichletInverse D f) y| ≤ _
      rw [hLap x, hLap y]
      have hxy : dist x y ≤ 4 := by
        have h1 := Metric.mem_closedBall.1 hx
        have h2 := Metric.mem_closedBall.1 hy
        have := dist_triangle_right x y x₀
        linarith
      refine ⟨?_, ?_⟩
      · rw [abs_div, abs_neg, abs_of_pos hD]
        have := abs_sineSum_le_c3Norm hd f hf x
        calc |sineSum f x| / D ≤ c3Norm f / D := div_le_div_of_nonneg_right this hD.le
          _ ≤ 2 * c3Norm f / D := div_le_div_of_nonneg_right (by linarith) hD.le
      · have e : -(sineSum f x) / D - -(sineSum f y) / D = (sineSum f y - sineSum f x) / D := by
          ring
        rw [e, abs_div, abs_of_pos hD]
        have h1 := abs_sineSum_sub_le hd f hf y x
        have h2 := le_two_mul_rpow_half_of_le_four dist_nonneg hxy
        rw [dist_comm y x] at h1
        calc |sineSum f y - sineSum f x| / D ≤ c3Norm f * dist x y / D :=
              div_le_div_of_nonneg_right h1 hD.le
          _ ≤ c3Norm f * (2 * dist x y ^ (1 / 2 : ℝ)) / D :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc) hD.le
          _ = 2 * c3Norm f / D * dist x y ^ (1 / 2 : ℝ) := by ring)
    x₀ (Metric.mem_closedBall_self zero_le_one)
  calc ‖iteratedFDeriv ℝ 2 (dirichletInverse D f) x₀‖
      ≤ C₀ * (c3Norm f / D / 8 + 2 * c3Norm f / D) := hsch
    _ ≤ max C₀ 0 * (c3Norm f / D / 8 + 2 * c3Norm f / D) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C₀ 0 * (3 * (c3Norm f / D)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
        have : 2 * c3Norm f / D = 2 * (c3Norm f / D) := by ring
        linarith
    _ = 3 * max C₀ 0 * c3Norm f / D := by ring

/-- **Gradient from sup and Hessian bounds**: a `C²` function on `ℝ^d` bounded by `M₀` whose
second derivative is bounded by `M₂` has `‖∇g‖ ≤ 2 M₀ + M₂`: along a unit segment from `z`,
`g(z + x) − g(z) − ∇g(z) x` has gradient `∇g(w) − ∇g(z)` of norm at most `M₂`. -/
theorem norm_fderiv_le_of_abs_le_of_norm_iteratedFDeriv_two_le {g : Euc d → ℝ}
    (hg : ContDiff ℝ 2 g) {M₀ M₂ : ℝ} (h0 : ∀ z, |g z| ≤ M₀)
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ M₂) (z : Euc d) :
    ‖fderiv ℝ g z‖ ≤ 2 * M₀ + M₂ := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h0 z)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h2 z)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hG : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hGb : ∀ w, ‖fderiv ℝ (fderiv ℝ g) w‖ ≤ M₂ := fun w => by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact h2 w
  have hlip : ∀ w, ‖fderiv ℝ g w - fderiv ℝ g z‖ ≤ M₂ * ‖w - z‖ := fun w =>
    (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ g) (C := M₂) (x := z) (y := w) (fun w _ => (hG w)) (fun w _ => hGb w)
      (Set.mem_univ _) (Set.mem_univ _)
  set h : Euc d → ℝ := fun w => g w - fderiv ℝ g z w with hh
  have hhd : ∀ w, HasFDerivAt h (fderiv ℝ g w - fderiv ℝ g z) w := fun w =>
    (hgd w).hasFDerivAt.sub (fderiv ℝ g z).hasFDerivAt
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun x hx => ?_
  have hmv := (convex_closedBall z 1).norm_image_sub_le_of_norm_fderiv_le (f := h) (C := M₂)
    (x := z) (y := z + x) (fun w _ => (hhd w).differentiableAt) (fun w hw => by
      rw [(hhd w).fderiv]
      have h1 := hlip w
      have h2 : ‖w - z‖ ≤ 1 := mem_closedBall_iff_norm.1 hw
      nlinarith) (Metric.mem_closedBall_self zero_le_one)
    (mem_closedBall_iff_norm.2 (by rw [add_sub_cancel_left, hx]))
  have e : h (z + x) - h z = g (z + x) - g z - fderiv ℝ g z x := by
    simp only [hh, map_add]
    ring
  have key : fderiv ℝ g z x = (g (z + x) - g z) - (h (z + x) - h z) := by
    rw [e]
    ring
  rw [Real.norm_eq_abs, key]
  rw [add_sub_cancel_left, hx, mul_one] at hmv
  calc |(g (z + x) - g z) - (h (z + x) - h z)|
      ≤ |g (z + x) - g z| + |h (z + x) - h z| := abs_sub _ _
    _ ≤ (|g (z + x)| + |g z|) + M₂ :=
        add_le_add (abs_sub _ _) (by rwa [← Real.norm_eq_abs])
    _ ≤ 2 * M₀ + M₂ := by linarith [h0 (z + x), h0 z]

/-- **Second-order bounds of the Dirichlet inverse**: granting the interior Schauder estimate
(`SchauderInterior`), there is `C(d)` such that for every test function `f` of the unit cube and
`D > 0`, `u = (−DΔ_Q)⁻¹ f`
satisfies `|u| + ‖∇u‖ + ‖∇²u‖ ≤ C c3Norm f / D` on `ℝ^d`. Route: `|u| ≤ c3Norm f/(8D)` on the closed
cube by the maximum principle (`|Δu| = |f|/D`), hence everywhere by the reflection symmetry of the
sine series; then the Schauder estimate with `α = 1/2` on balls of radius `2`, since
`−DΔu = sineSum f` with `|sineSum f| ≤ c3Norm f` and `|∇ sineSum f| ≤ c3Norm f`; and the gradient by
Taylor's formula along unit segments, `|∂_i u| ≤ 2 sup|u| + sup‖∇²u‖/2`. -/
theorem exists_norm_iteratedFDeriv_dirichletInverse_le_two (hd : 1 ≤ d)
    (hSch : LatticeProb.Analysis.Schauder.SchauderInterior d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : ℝ), 0 < D → ∀ f : Euc d → ℝ, Sobolev.IsTestFn (unitCube d) f →
      ∀ z : Euc d, |dirichletInverse D f z| ≤ C * c3Norm f / D ∧
        ‖fderiv ℝ (dirichletInverse D f) z‖ ≤ C * c3Norm f / D ∧
        ‖iteratedFDeriv ℝ 2 (dirichletInverse D f) z‖ ≤ C * c3Norm f / D := by
  obtain ⟨C₂, hC₂, hH⟩ := exists_norm_iteratedFDeriv_two_dirichletInverse_le hd hSch
  refine ⟨1 + C₂, by positivity, fun D hD f hf z => ?_⟩
  have hc : 0 ≤ c3Norm f := (abs_nonneg _).trans (abs_le_c3Norm hf 0)
  have hcD : 0 ≤ c3Norm f / D := div_nonneg hc hD.le
  have hCt : 0 ≤ C₂ * (c3Norm f / D) := mul_nonneg hC₂ hcD
  have e1 : (1 + C₂) * c3Norm f / D = (1 + C₂) * (c3Norm f / D) := by ring
  have e2 : C₂ * c3Norm f / D = C₂ * (c3Norm f / D) := by ring
  have hs := abs_dirichletInverse_le hd hD f hf z
  have hg := norm_fderiv_le_of_abs_le_of_norm_iteratedFDeriv_two_le
    ((dirichletInverse_spec hd D hD f hf).1 2) (M₀ := c3Norm f / D / 8)
    (M₂ := C₂ * c3Norm f / D) (fun w => abs_dirichletInverse_le hd hD f hf w)
    (fun w => hH D hD f hf w) z
  have hh := hH D hD f hf z
  rw [e1]
  rw [e2] at hg hh
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end LatticeProb.Analysis.Schauder

end
