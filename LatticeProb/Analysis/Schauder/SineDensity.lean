import LatticeProb.Analysis.Schauder.UnitCube
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.SineDensity`.

# Density of the weighted sine monomials

The sine monomials `Π_i sin(π j_i z_i)` with integer frequencies `j_i` span a subspace `sineSpan d`
of the functions on `ℝ^d`. Multiplying a monomial by `cos(π z_i)` stays in the span, so, weighted by
`cubeWeight z = Π_i sin(π z_i)` (positive on the open cube), every polynomial in the `cos(π z_i)`
lies in `sineSpan d`. These polynomials separate the points of the closed cube, so by
Stone–Weierstrass a continuous function `u` has `cubeWeight * u` approximated on the closed cube,
relative to the weight, by elements of `sineSpan d` (`exists_sineSpan_approx`). No sine series
appears here; `SineSeries` uses the approximation to show that the remainder of the series vanishes.
-/

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- The product of one-variable sines `Π_i sin (π j_i z_i)` with integer frequencies `j_i`. -/
def sineMonomial (j : Fin d → ℤ) (z : Euc d) : ℝ := ∏ i, Real.sin (Real.pi * (j i : ℝ) * z i)

/-- The span of the sine monomials. -/
def sineSpan (d : ℕ) : Submodule ℝ (Euc d → ℝ) := Submodule.span ℝ (Set.range sineMonomial)

/-- A sine monomial is continuous. -/
theorem continuous_sineMonomial (j : Fin d → ℤ) : Continuous (sineMonomial j) := by
  unfold sineMonomial
  exact continuous_finsetProd _ fun i _ =>
    Real.continuous_sin.comp (continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)

/-- Changing one frequency of a sine monomial changes one factor. -/
theorem sineMonomial_update (j : Fin d → ℤ) (i : Fin d) (m : ℤ) (z : Euc d) :
    sineMonomial (Function.update j i m) z =
      Real.sin (Real.pi * (m : ℝ) * z i) *
        ∏ s ∈ Finset.univ.erase i, Real.sin (Real.pi * (j s : ℝ) * z s) := by
  unfold sineMonomial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [Function.update_of_ne (Finset.mem_erase.1 hs).1]

/-- Multiplying a sine monomial by `cos (π z_i)` gives a combination of two sine monomials. -/
theorem cos_mul_sineMonomial (i : Fin d) (j : Fin d → ℤ) (z : Euc d) :
    Real.cos (Real.pi * z i) * sineMonomial j z =
      (sineMonomial (Function.update j i (j i + 1)) z +
        sineMonomial (Function.update j i (j i - 1)) z) / 2 := by
  have h0 : sineMonomial j z = Real.sin (Real.pi * (j i : ℝ) * z i) *
      ∏ s ∈ Finset.univ.erase i, Real.sin (Real.pi * (j s : ℝ) * z s) := by
    simpa using sineMonomial_update j i (j i) z
  rw [sineMonomial_update, sineMonomial_update, h0]
  have e1 : Real.pi * ((j i + 1 : ℤ) : ℝ) * z i =
      Real.pi * (j i : ℝ) * z i + Real.pi * z i := by push_cast; ring
  have e2 : Real.pi * ((j i - 1 : ℤ) : ℝ) * z i =
      Real.pi * (j i : ℝ) * z i - Real.pi * z i := by push_cast; ring
  rw [e1, e2, Real.sin_add, Real.sin_sub]
  ring

/-- The span of the sine monomials is stable under multiplication by `cos (π z_i)`. -/
theorem mul_cos_mem_sineSpan (i : Fin d) {g : Euc d → ℝ} (hg : g ∈ sineSpan d) :
    (fun z => Real.cos (Real.pi * z i) * g z) ∈ sineSpan d := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    have : (fun z : Euc d => Real.cos (Real.pi * z i) * sineMonomial j z) =
        (1 / 2 : ℝ) • sineMonomial (Function.update j i (j i + 1)) +
          (1 / 2 : ℝ) • sineMonomial (Function.update j i (j i - 1)) := by
      funext z
      rw [cos_mul_sineMonomial]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  | zero =>
    have : (fun z : Euc d => Real.cos (Real.pi * z i) * (0 : Euc d → ℝ) z) = 0 := by
      funext z
      simp
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun z : Euc d => Real.cos (Real.pi * z i) * (x + y) z) =
        (fun z => Real.cos (Real.pi * z i) * x z) + fun z => Real.cos (Real.pi * z i) * y z := by
      funext z
      simp only [Pi.add_apply]
      ring
    rw [this]
    exact add_mem hx hy
  | smul a x _ hx =>
    have : (fun z : Euc d => Real.cos (Real.pi * z i) * (a • x) z) =
        a • fun z => Real.cos (Real.pi * z i) * x z := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ hx

/-- Elements of the span of the sine monomials are continuous. -/
theorem continuous_of_mem_sineSpan {g : Euc d → ℝ} (hg : g ∈ sineSpan d) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact continuous_sineMonomial j
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/-- The weight `Π_i sin (π z_i)`, positive on the open cube. -/
def cubeWeight (z : Euc d) : ℝ := sineMonomial (fun _ => 1) z

/-- The weight is positive on the open cube. -/
theorem cubeWeight_pos {z : Euc d} (hz : z ∈ unitCube d) : 0 < cubeWeight z := by
  unfold cubeWeight sineMonomial
  exact Finset.prod_pos fun i _ => Real.sin_pos_of_pos_of_lt_pi (by
    have := (hz i).1
    simp only [Int.cast_one, mul_one]
    positivity) (by
    have := (hz i).2
    simp only [Int.cast_one, mul_one]
    nlinarith [Real.pi_pos])

/-- The weight is nonnegative on the closed cube. -/
theorem cubeWeight_nonneg {z : Euc d} (hz : z ∈ closedCube d) : 0 ≤ cubeWeight z := by
  unfold cubeWeight sineMonomial
  exact Finset.prod_nonneg fun i _ => Real.sin_nonneg_of_nonneg_of_le_pi (by
    have := (hz i).1
    simp only [Int.cast_one, mul_one]
    positivity) (by
    have := (hz i).2
    simp only [Int.cast_one, mul_one]
    nlinarith [Real.pi_pos])

/-- The weight lies in the span of the sine monomials. -/
theorem cubeWeight_mem_sineSpan : (cubeWeight : Euc d → ℝ) ∈ sineSpan d :=
  Submodule.subset_span ⟨_, rfl⟩

/-- The coordinate function `z ↦ cos (π z_i)` on the closed cube. -/
def cosCoordinate (i : Fin d) : C(closedCube d, ℝ) :=
  ⟨fun z => Real.cos (Real.pi * z.1 i), Real.continuous_cos.comp
    (continuous_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      continuous_subtype_val))⟩

/-- The algebra of polynomials in the coordinate functions `cos (π z_i)`. -/
def cosAlgebra (d : ℕ) : Subalgebra ℝ C(closedCube d, ℝ) :=
  Algebra.adjoin ℝ (Set.range cosCoordinate)

/-- Weighted by `Π_i sin (π z_i)`, a polynomial in the `cos (π z_i)` is a combination of sine
monomials. -/
theorem exists_mem_sineSpan_of_mem_cosAlgebra {q : C(closedCube d, ℝ)} (hq : q ∈ cosAlgebra d) :
    ∃ g ∈ sineSpan d, ∀ z : closedCube d, cubeWeight z.1 * q z = g z.1 := by
  have hq' : q ∈ Submodule.span ℝ (Submonoid.closure (Set.range (cosCoordinate (d := d)))) := by
    rw [← Algebra.adjoin_eq_span]
    exact hq
  clear hq
  induction hq' using Submodule.span_induction with
  | mem x hx =>
    induction hx using Submonoid.closure_induction_left with
    | one => exact ⟨cubeWeight, cubeWeight_mem_sineSpan, fun z => by simp⟩
    | mul_left x hx y hy ih =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨g, hg, hgy⟩ := ih
      refine ⟨fun z => Real.cos (Real.pi * z i) * g z, mul_cos_mem_sineSpan i hg, fun z => ?_⟩
      show cubeWeight z.1 * (Real.cos (Real.pi * z.1 i) * y z) = Real.cos (Real.pi * z.1 i) * g z.1
      rw [← hgy z]
      ring
  | zero => exact ⟨0, zero_mem _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨g1, hg1, h1⟩ := hx
    obtain ⟨g2, hg2, h2⟩ := hy
    exact ⟨g1 + g2, add_mem hg1 hg2, fun z => by simp [mul_add, h1 z, h2 z]⟩
  | smul a x _ hx =>
    obtain ⟨g, hg, h⟩ := hx
    exact ⟨a • g, Submodule.smul_mem _ _ hg, fun z => by
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, Pi.smul_apply]
      rw [← h z]
      ring⟩

/-- The polynomials in the `cos (π z_i)` separate the points of the closed cube. -/
theorem cosAlgebra_separatesPoints : (cosAlgebra d).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x.1 i ≠ y.1 i := by
    by_contra h
    exact hxy (Subtype.ext (PiLp.ext fun i => by_contra fun hi => h ⟨i, hi⟩))
  refine ⟨_, ⟨cosCoordinate i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩, ?_⟩
  show Real.cos (Real.pi * x.1 i) ≠ Real.cos (Real.pi * y.1 i)
  intro h
  have hx := x.2 i
  have hy := y.2 i
  refine hi (mul_left_cancel₀ Real.pi_ne_zero (Real.injOn_cos ?_ ?_ h))
  · exact ⟨by have := hx.1; positivity, by nlinarith [hx.2, Real.pi_pos]⟩
  · exact ⟨by have := hy.1; positivity, by nlinarith [hy.2, Real.pi_pos]⟩

/-- A continuous function is uniformly approximated on the closed cube by polynomials in the
`cos (π z_i)` (Stone-Weierstrass). -/
theorem exists_cosAlgebra_approx (u : Euc d → ℝ) (hu : Continuous u) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ cosAlgebra d, ∀ z : closedCube d, |u z.1 - q z| ≤ ε := by
  have : CompactSpace (closedCube d) := isCompact_iff_compactSpace.1 isCompact_closedCube
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (cosAlgebra d) cosAlgebra_separatesPoints
  set uK : C(closedCube d, ℝ) := ⟨fun z => u z.1, hu.comp continuous_subtype_val⟩ with huK
  have hmem : uK ∈ ((cosAlgebra d).topologicalClosure : Set C(closedCube d, ℝ)) := by
    rw [htop]
    trivial
  rw [Subalgebra.topologicalClosure_coe] at hmem
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  refine ⟨b, hb, fun z => ?_⟩
  have := ContinuousMap.dist_apply_le_dist (f := uK) (g := b) z
  rw [Real.dist_eq] at this
  exact this.trans hdist.le

/-- Weighted by `Π_i sin (π z_i)`, a continuous function is uniformly approximated on the closed
cube, relative to the weight, by combinations of sine monomials. -/
theorem exists_sineSpan_approx (u : Euc d → ℝ) (hu : Continuous u) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ sineSpan d, ∀ z ∈ closedCube d, |cubeWeight z * u z - g z| ≤ ε * cubeWeight z := by
  obtain ⟨q, hq, hqu⟩ := exists_cosAlgebra_approx u hu hε
  obtain ⟨g, hg, hgq⟩ := exists_mem_sineSpan_of_mem_cosAlgebra hq
  refine ⟨g, hg, fun z hz => ?_⟩
  have h1 := hgq ⟨z, hz⟩
  have h2 := hqu ⟨z, hz⟩
  have hw := cubeWeight_nonneg hz
  simp only at h1 h2
  rw [← h1, ← mul_sub, abs_mul, abs_of_nonneg hw, mul_comm]
  exact mul_le_mul_of_nonneg_right h2 hw

end LatticeProb.Analysis.Schauder

end
