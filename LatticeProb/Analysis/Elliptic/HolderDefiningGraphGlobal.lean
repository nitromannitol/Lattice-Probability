import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import LatticeProb.Analysis.Elliptic.HolderCompositionConvex

/-!
# Global graphs from local Hölder bounds

A twice differentiable function that does not depend on one coordinate, and whose second
coordinate derivatives have Hölder increments on a ball, agrees on a smaller ball with a function
of the same kind whose global coordinate `C^{2,σ}` norm is finite.

The new function is the composition with a smooth map acting on each coordinate separately: it is
the identity near the center and takes values in the original ball. The composition estimate for
the coordinate Hölder norm then gives the global bound.
-/

open scoped Topology ContDiff

namespace LatticeProb.Elliptic.HolderExtension

/-- An increment that is Lipschitz and between bounded values is a Hölder increment at every
scale. -/
private theorem abs_sub_le_rpow_of_bound_of_lipschitz {σ M L ρ a b : ℝ}
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hab : |a - b| ≤ L * ρ) :
    |a - b| ≤ (L + 2 * M) * ρ ^ σ := by
  have hpow : 0 ≤ ρ ^ σ := Real.rpow_nonneg hρ σ
  by_cases h1 : ρ ≤ 1
  · have hρσ : ρ ≤ ρ ^ σ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hρ h1 hσ hσ'
    calc
      |a - b| ≤ L * ρ := hab
      _ ≤ L * ρ ^ σ := mul_le_mul_of_nonneg_left hρσ hL
      _ ≤ (L + 2 * M) * ρ ^ σ := by nlinarith
  · have hone : 1 ≤ ρ ^ σ := Real.one_le_rpow (le_of_lt (not_le.mp h1)) hσ
    have h2 : |a - b| ≤ 2 * M := by
      obtain ⟨ha1, ha2⟩ := abs_le.mp ha
      obtain ⟨hb1, hb2⟩ := abs_le.mp hb
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith

/-- Values, coordinate derivatives and Hölder increments bounded by real constants give a finite
coordinate Hölder norm. -/
private theorem c2HolderNorm_lt_top_of_bounds {d : ℕ} {σ : ℝ} {S : Set (Fin d → ℝ)}
    {u : (Fin d → ℝ) → ℝ} {B₀ B₁ B₂ H : ℝ}
    (h₀ : ∀ x ∈ S, |u x| ≤ B₀)
    (h₁ : ∀ i x, x ∈ S → |partialDeriv i u x| ≤ B₁)
    (h₂ : ∀ i j x, x ∈ S → |secondPartial i j u x| ≤ B₂)
    (hH : ∀ i j x, x ∈ S → ∀ y ∈ S,
      |secondPartial i j u x - secondPartial i j u y| ≤
        H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) :
    c2HolderNorm σ S u < ⊤ := by
  refine lt_of_le_of_lt (c2HolderNorm_le_of_bounds h₀ h₁ h₂ hH) ?_
  have hs : ∀ B : ℝ, ∑ _ : Fin d, ENNReal.ofReal B < ⊤ := fun B =>
    ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top
  have hss : ∀ B : ℝ, ∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal B < ⊤ := fun B =>
    ENNReal.sum_lt_top.2 fun _ _ => hs B
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
    ⟨ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hs _⟩, hss _⟩, hss _⟩

/-- The coordinate vectors have supremum norm at most one. -/
private theorem norm_single_one_le {d : ℕ} (i : Fin d) :
    ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  rw [Pi.single_apply]
  split_ifs <;> simp

/-- A twice differentiable function with Hölder second derivatives on a ball has a finite
coordinate Hölder norm on that ball. -/
private theorem c2HolderNorm_ball_lt_top {d : ℕ} {σ : ℝ} {g : (Fin d → ℝ) → ℝ}
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) {r H : ℝ}
    (hH : ∀ j k, ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      |secondPartial j k g x - secondPartial j k g y| ≤
        H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) :
    c2HolderNorm σ (Metric.ball p r) g < ⊤ := by
  have hK := isCompact_closedBall p r
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn
    (hg.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn
    (hg.continuous_iteratedFDeriv (m := 2) le_rfl).continuousOn
  have hsub := Metric.ball_subset_closedBall (x := p) (ε := r)
  refine c2HolderNorm_lt_top_of_bounds (B₀ := B₀) (B₁ := B₁) (B₂ := B₂) ?_ ?_ ?_ hH
  · intro x hx
    simpa only [Real.norm_eq_abs] using hB₀ x (hsub hx)
  · intro i x hx
    have hB : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ x (hsub hx))
    calc
      |partialDeriv i g x| = ‖fderiv ℝ g x (Pi.single i 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ g x‖ * ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ :=
        (fderiv ℝ g x).le_opNorm _
      _ ≤ B₁ * 1 := mul_le_mul (hB₁ x (hsub hx)) (norm_single_one_le i) (norm_nonneg _) hB
      _ = B₁ := mul_one _
  · intro i j x hx
    have hB : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ x (hsub hx))
    have hprod : ∏ k : Fin 2,
        ‖(![Pi.single i (1 : ℝ), Pi.single j 1] : Fin 2 → Fin d → ℝ) k‖ ≤ 1 := by
      rw [Fin.prod_univ_two]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_single_one_le i)).trans (norm_single_one_le j)
    calc
      |secondPartial i j g x| =
          ‖iteratedFDeriv ℝ 2 g x ![Pi.single i 1, Pi.single j 1]‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ 2 g x‖ *
          ∏ k : Fin 2, ‖(![Pi.single i (1 : ℝ), Pi.single j 1] : Fin 2 → Fin d → ℝ) k‖ :=
        (iteratedFDeriv ℝ 2 g x).le_opNorm _
      _ ≤ B₂ * 1 :=
        mul_le_mul (hB₂ x (hsub hx)) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB
      _ = B₂ := mul_one _

/-- The derivative of a scalar function of one shifted coordinate. -/
private theorem fderiv_coord_apply {d : ℕ} {ζ : ℝ → ℝ} (hζ : Differentiable ℝ ζ)
    (a c b : ℝ) (j : Fin d) (x v : Fin d → ℝ) :
    fderiv ℝ (fun y : Fin d → ℝ => a + c * ζ (y j - b)) x v = c * deriv ζ (x j - b) * v j := by
  have h1 : HasFDerivAt (fun y : Fin d → ℝ => y j - b)
      (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ) x :=
    (hasFDerivAt_sub_const_iff b).2 (hasFDerivAt_apply j x)
  have h2 : HasFDerivAt (fun y : Fin d → ℝ => ζ (y j - b))
      (deriv ζ (x j - b) • ContinuousLinearMap.proj j) x :=
    (hζ (x j - b)).hasDerivAt.comp_hasFDerivAt x h1
  rw [((h2.const_mul c).const_add a).fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

/-- The coordinate derivatives of a scalar function of one shifted coordinate. -/
private theorem partialDeriv_coord {d : ℕ} {ζ : ℝ → ℝ} (hζ : Differentiable ℝ ζ)
    (a c b : ℝ) (j k : Fin d) :
    partialDeriv k (fun y : Fin d → ℝ => a + c * ζ (y j - b)) =
      fun y => 0 + (c * (Pi.single k (1 : ℝ) : Fin d → ℝ) j) * deriv ζ (y j - b) := by
  funext y
  rw [partialDeriv, fderiv_coord_apply hζ]
  ring

/-- A smooth compactly supported function of one shifted coordinate has finite global coordinate
Hölder norm. -/
private theorem c2HolderNorm_coord_lt_top {d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hcs : HasCompactSupport η) (a b : ℝ) (j : Fin d) :
    c2HolderNorm σ Set.univ (fun x : Fin d → ℝ => a + η (x j - b)) < ⊤ := by
  obtain ⟨h1, h1'⟩ := contDiff_infty_iff_deriv.1 hη
  obtain ⟨h2, h2'⟩ := contDiff_infty_iff_deriv.1 h1'
  obtain ⟨h3, h3'⟩ := contDiff_infty_iff_deriv.1 h2'
  obtain ⟨M₀, hM₀⟩ := hη.continuous.bounded_above_of_compact_support hcs
  obtain ⟨M₁, hM₁⟩ := h1'.continuous.bounded_above_of_compact_support hcs.deriv
  obtain ⟨M₂, hM₂⟩ := h2'.continuous.bounded_above_of_compact_support hcs.deriv.deriv
  obtain ⟨M₃, hM₃⟩ := h3'.continuous.bounded_above_of_compact_support hcs.deriv.deriv.deriv
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ 0)
  have he : ∀ k : Fin d, |(Pi.single k (1 : ℝ) : Fin d → ℝ) j| ≤ 1 := by
    intro k
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hfun : (fun x : Fin d → ℝ => a + η (x j - b)) = fun x => a + 1 * η (x j - b) := by
    simp only [one_mul]
  rw [hfun]
  have hF : ContDiff ℝ 2 (fun y : Fin d → ℝ => a + 1 * η (y j - b)) :=
    contDiff_const.add (contDiff_const.mul
      ((hη.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
        ((contDiff_apply ℝ ℝ j).sub contDiff_const)))
  have hS : ∀ k l x, secondPartial l k (fun y : Fin d → ℝ => a + 1 * η (y j - b)) x =
      (1 * (Pi.single k (1 : ℝ) : Fin d → ℝ) j) * deriv (deriv η) (x j - b) *
        (Pi.single l (1 : ℝ) : Fin d → ℝ) j := by
    intro k l x
    have hu : DifferentiableAt ℝ (fderiv ℝ (fun y : Fin d → ℝ => a + 1 * η (y j - b))) x :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
    rw [← fderiv_partialDeriv_apply hu k l, partialDeriv_coord h1]
    exact fderiv_coord_apply h2 _ _ _ _ _ _
  refine c2HolderNorm_lt_top_of_bounds (B₀ := |a| + M₀) (B₁ := M₁) (B₂ := M₂)
    (H := M₃ + 2 * M₂) ?_ ?_ ?_ ?_
  · intro x _
    calc
      |a + 1 * η (x j - b)| ≤ |a| + |1 * η (x j - b)| := abs_add_le _ _
      _ ≤ |a| + M₀ := by
        rw [one_mul, ← Real.norm_eq_abs (η _)]
        linarith [hM₀ (x j - b)]
  · intro k x _
    rw [partialDeriv_coord h1]
    calc
      |0 + 1 * (Pi.single k (1 : ℝ) : Fin d → ℝ) j * deriv η (x j - b)| =
          |(Pi.single k (1 : ℝ) : Fin d → ℝ) j| * ‖deriv η (x j - b)‖ := by
        rw [zero_add, one_mul, abs_mul, Real.norm_eq_abs]
      _ ≤ 1 * M₁ := mul_le_mul (he k) (hM₁ _) (norm_nonneg _) zero_le_one
      _ = M₁ := one_mul _
  · intro l k x _
    rw [hS k l x]
    calc
      |1 * (Pi.single k (1 : ℝ) : Fin d → ℝ) j * deriv (deriv η) (x j - b) *
          (Pi.single l (1 : ℝ) : Fin d → ℝ) j| =
          (|(Pi.single k (1 : ℝ) : Fin d → ℝ) j| * |(Pi.single l (1 : ℝ) : Fin d → ℝ) j|) *
            ‖deriv (deriv η) (x j - b)‖ := by
        rw [Real.norm_eq_abs, one_mul, abs_mul, abs_mul]
        ring
      _ ≤ 1 * M₂ :=
        mul_le_mul ((mul_le_of_le_one_left (abs_nonneg _) (he k)).trans (he l)) (hM₂ _) (norm_nonneg _)
          zero_le_one
      _ = M₂ := one_mul _
  · intro l k x _ y _
    rw [hS k l x, hS k l y]
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv η))
      (s := Set.univ) (fun z _ => h3 z) (fun z _ => hM₃ z) convex_univ
      (Set.mem_univ (y j - b)) (Set.mem_univ (x j - b))
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hcoord : |x j - b - (y j - b)| ≤ LatticeProb.Euclidean.Lattice.radius (x - y) := by
      simpa only [sub_sub_sub_cancel_right, Pi.sub_apply] using
        LatticeProb.Euclidean.Lattice.abs_coord_le_radius (x - y) j
    have hkey := abs_sub_le_rpow_of_bound_of_lipschitz hσ hσ' hM₂0 hM₃0
      (LatticeProb.Euclidean.Lattice.radius_nonneg (x - y))
      (by simpa only [Real.norm_eq_abs] using hM₂ (x j - b))
      (by simpa only [Real.norm_eq_abs] using hM₂ (y j - b))
      (hmv.trans (mul_le_mul_of_nonneg_left hcoord hM₃0))
    have hpow : 0 ≤ LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ :=
      Real.rpow_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg _) σ
    calc
      |1 * (Pi.single k (1 : ℝ) : Fin d → ℝ) j * deriv (deriv η) (x j - b) *
            (Pi.single l (1 : ℝ) : Fin d → ℝ) j -
          1 * (Pi.single k (1 : ℝ) : Fin d → ℝ) j * deriv (deriv η) (y j - b) *
            (Pi.single l (1 : ℝ) : Fin d → ℝ) j| =
          (|(Pi.single k (1 : ℝ) : Fin d → ℝ) j| * |(Pi.single l (1 : ℝ) : Fin d → ℝ) j|) *
            |deriv (deriv η) (x j - b) - deriv (deriv η) (y j - b)| := by
        rw [← abs_mul, ← abs_mul]
        congr 1
        ring
      _ ≤ 1 * ((M₃ + 2 * M₂) * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) :=
        mul_le_mul ((mul_le_of_le_one_left (abs_nonneg _) (he k)).trans (he l)) hkey (abs_nonneg _) zero_le_one
      _ = (M₃ + 2 * M₂) * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := one_mul _

/-- A smooth compactly supported function on the line that is the identity near zero and takes
values in a bounded interval. -/
private theorem exists_smooth_clamp {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ ContDiff ℝ 2 η ∧ HasCompactSupport η ∧
      (∀ s, |s| < r / 4 → η s = s) ∧ ∀ s, |η s| ≤ r / 2 := by
  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump (0 : ℝ), β.rIn = r / 4 ∧ β.rOut = r / 2 :=
    ⟨⟨r / 4, r / 2, by positivity, by linarith⟩, rfl, rfl⟩
  refine ⟨fun s => β s * s, β.contDiff.mul contDiff_id, β.contDiff.mul contDiff_id,
    β.hasCompactSupport.mul_right, ?_, ?_⟩
  · intro s hs
    have h1 : β s = 1 := by
      apply β.one_of_mem_closedBall
      rw [hβin, Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact hs.le
    simp only [h1, one_mul]
  · intro s
    rw [abs_mul, abs_of_nonneg β.nonneg]
    by_cases hs : |s| < r / 2
    · calc
        β s * |s| ≤ 1 * |s| := mul_le_mul_of_nonneg_right β.le_one (abs_nonneg s)
        _ ≤ r / 2 := by linarith
    · have hns : s ∉ Function.support β := by
        rw [β.support_eq, hβout, Metric.mem_ball, Real.dist_eq, sub_zero]
        exact hs
      rw [Function.notMem_support.mp hns, zero_mul]
      positivity

/-- **Globalization of a local Hölder graph.** A twice differentiable function that does not
depend on the coordinate `i`, and whose second coordinate derivatives have Hölder increments on a
ball around `p`, agrees on a smaller ball with a twice differentiable function that does not
depend on the coordinate `i` and has finite global coordinate `C^{2,σ}` norm. -/
theorem exists_global_graph_of_local_holder {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1)
    (g : (Fin d → ℝ) → ℝ) (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i : Fin d)
    (hinv : ∀ x t, g (Function.update x i t) = g x) {r H : ℝ} (hr : 0 < r)
    (hH : ∀ j k, ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      |secondPartial j k g x - secondPartial j k g y| ≤
        H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) :
    ∃ (g' : (Fin d → ℝ) → ℝ) (r' : ℝ), 0 < r' ∧ r' ≤ r ∧ ContDiff ℝ 2 g' ∧
      c2HolderNorm σ Set.univ g' < ⊤ ∧
      (∀ x t, g' (Function.update x i t) = g' x) ∧ ∀ x ∈ Metric.ball p r', g' x = g x := by
  obtain ⟨η, hη, hη2, hcs, hid, hbound⟩ := exists_smooth_clamp hr
  obtain ⟨h1, -⟩ := contDiff_infty_iff_deriv.1 hη
  obtain ⟨M₁, hM₁⟩ := (contDiff_infty_iff_deriv.1 hη).2.continuous.bounded_above_of_compact_support
    hcs.deriv
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin d → ℝ) → Fin d → ℝ, ψ = fun x j => p j + η (x j - p j) :=
    ⟨_, rfl⟩
  have hψx : ∀ x j, ψ x j = p j + η (x j - p j) := fun x j => by rw [hψ]
  have hψ2 : ContDiff ℝ 2 ψ := by
    rw [hψ]
    exact contDiff_pi.2 fun j => contDiff_const.add
      (hη2.comp ((contDiff_apply ℝ ℝ j).sub contDiff_const))
  have hmaps : Set.MapsTo ψ Set.univ (Metric.ball p r) := by
    intro x _
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro j
    rw [Real.dist_eq, hψx, show p j + η (x j - p j) - p j = η (x j - p j) by ring]
    linarith [hbound (x j - p j)]
  have hLip : LipschitzWith ⟨M₁, hM₁0⟩ ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_pi_le_iff (by positivity)]
    intro j
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := η) (s := Set.univ)
      (fun z _ => h1 z) (fun z _ => hM₁ z) convex_univ
      (Set.mem_univ (y j - p j)) (Set.mem_univ (x j - p j))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_sub_sub_cancel_right] at hmv
    have hxy : |x j - y j| ≤ dist x y := by
      simpa only [Real.dist_eq] using dist_le_pi_dist x y j
    rw [Real.dist_eq, hψx, hψx,
      show p j + η (x j - p j) - (p j + η (y j - p j)) = η (x j - p j) - η (y j - p j) by ring]
    exact hmv.trans (mul_le_mul_of_nonneg_left hxy hM₁0)
  have hcoord : ∀ j, c2HolderNorm σ Set.univ (fun x => ψ x j) < ⊤ := by
    intro j
    simp only [hψx]
    exact c2HolderNorm_coord_lt_top hσ.le hσ'.le hη hcs (p j) (p j) j
  obtain ⟨C, -, hC⟩ := c2HolderNorm_comp hσ hσ' Set.univ (Metric.ball p r) isOpen_univ
    Metric.isOpen_ball convex_univ (convex_ball p r) ψ hψ2.contDiffOn hmaps hcoord _
    hLip.lipschitzOnWith
  have hball := c2HolderNorm_ball_lt_top hg p hH
  have hnorm := (hC g hg.contDiffOn hball).2
  refine ⟨g ∘ ψ, r / 4, by positivity, by linarith, hg.comp hψ2,
    lt_of_le_of_lt hnorm (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hball), ?_, ?_⟩
  · intro x t
    have hupd : ψ (Function.update x i t) = Function.update (ψ x) i (p i + η (t - p i)) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hψx]
      · simp [hψx, Function.update_of_ne hj]
    simp only [Function.comp_apply, hupd, hinv]
  · intro x hx
    have hfix : ψ x = x := by
      funext j
      have hj : |x j - p j| < r / 4 := by
        rw [← Real.dist_eq]
        exact lt_of_le_of_lt (dist_le_pi_dist x p j) hx
      rw [hψx, hid _ hj]
      ring
    simp only [Function.comp_apply, hfix]

end LatticeProb.Elliptic.HolderExtension
