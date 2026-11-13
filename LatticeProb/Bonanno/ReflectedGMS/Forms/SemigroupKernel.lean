/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupMarkov
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupConservation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventEquation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Vertex coefficients of the full-form semigroup

The checked full-form semigroup acts on the atomic `L²(m)` coordinates
`sqrt (m x) * f x`. Applying it to a weighted vertex indicator and decoding at
another vertex therefore gives its actual vertex transition coefficient.

These are analytic semigroup identities only. No association with a path
process and no Chapman--Kolmogorov sum formula is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace NNReal Topology

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- The vertex coefficient obtained by applying the full-form semigroup to the
atomic weighted delta at `y` and decoding at `x`. -/
noncomputable def semigroupKernel (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (t : ℝ≥0) (x y : V) : ℝ :=
  unweight m
    (fullFormSemigroup G m t
      (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))) x

@[simp] theorem semigroupKernel_zero
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (x y : V) :
    semigroupKernel G m 0 x y = G.indic y x := by
  rw [semigroupKernel, fullFormSemigroup_zero]
  simpa [ReflectedWalk.ConductanceGraph.indic] using
    congrFun (unweight_weightedValue m hm (G.indic y)
      (VertexTest.indic_hasSpeedL2 G m y)) x

/-- Every vertex coefficient is nonnegative. -/
theorem semigroupKernel_nonneg
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    0 ≤ semigroupKernel G m t x y := by
  classical
  apply fullFormSemigroup_nonneg G m hm t _ _ x
  intro z
  rw [unweight_weightedValue m hm]
  by_cases hzy : z = y <;> simp [ReflectedWalk.ConductanceGraph.indic, hzy]

/-- Each vertex coefficient is continuous in nonnegative time. -/
theorem continuous_semigroupKernel
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (x y : V) :
    Continuous (fun t : ℝ≥0 ↦ semigroupKernel G m t x y) := by
  unfold semigroupKernel unweight
  exact (((lp.evalCLM ℝ (fun _ : V ↦ ℝ) 2 x).continuous.comp
    (fullFormSemigroup_continuous G m hm
      (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)))).div_const _)

private theorem inner_semigroup_indic_eq_mass_mul_kernel [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    ⟪fullFormSemigroup G m t
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)),
      weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)⟫_ℝ =
      m x * semigroupKernel G m t x y := by
  rw [weightedValue_indic_eq_single G m x, lp.inner_single_right]
  simp only [Real.inner_apply, semigroupKernel, unweight]
  have hs : Real.sqrt (m x) ≠ 0 := (Real.sqrt_pos.2 (hm x)).ne'
  field_simp [hs]
  rw [Real.sq_sqrt (hm x).le]

/-- The vertex coefficients satisfy exact detailed balance for the atomic speed. -/
theorem semigroupKernel_detailedBalance [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    m x * semigroupKernel G m t x y =
      m y * semigroupKernel G m t y x := by
  rw [← inner_semigroup_indic_eq_mass_mul_kernel G m hm t x y,
    ← inner_semigroup_indic_eq_mass_mul_kernel G m hm t y x]
  have hself := fullFormSemigroup_isSelfAdjoint G m t
  calc
    _ = ⟪weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y),
        fullFormSemigroup G m t
          (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x))⟫_ℝ :=
      hself.isSymmetric _ _
    _ = ⟪fullFormSemigroup G m t
          (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)),
        weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)⟫_ℝ :=
      real_inner_comm _ _

private theorem hasSpeedL2_sum_indic [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (A : Finset V) :
    HasSpeedL2 m (∑ y ∈ A, G.indic y) := by
  unfold HasSpeedL2
  apply (memℓp_zero ?_).of_exponent_ge (by norm_num)
  refine A.finite_toSet.subset ?_
  intro z hz
  simp only [Set.mem_ofPred_eq, Finset.mem_coe] at hz ⊢
  by_contra hzA
  apply hz
  change Real.sqrt (m z) * (∑ y ∈ A, G.indic y) z = 0
  rw [Finset.sum_apply, Finset.sum_eq_zero]
  · simp
  · intro y hy
    have hzy : z ≠ y := by
      intro h
      subst y
      exact hzA hy
    simp [ReflectedWalk.ConductanceGraph.indic, hzy]

private theorem weightedValue_sum_indic [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (A : Finset V) :
    weightedValue m (∑ y ∈ A, G.indic y) (hasSpeedL2_sum_indic G m A) =
      ∑ y ∈ A, weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y) := by
  apply lp.ext
  funext z
  simp only [weightedValue_apply, Finset.sum_apply, lp.coeFn_sum]
  rw [Finset.mul_sum]

private theorem sum_indic_mem_Icc [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (A : Finset V) (z : V) :
    (∑ y ∈ A, G.indic y) z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Finset.sum_apply]
  by_cases hz : z ∈ A
  · rw [Finset.sum_eq_single z]
    · simp [ReflectedWalk.ConductanceGraph.indic]
    · intro y hy hyz
      simp [ReflectedWalk.ConductanceGraph.indic, Ne.symm hyz]
    · exact fun h ↦ (h hz).elim
  · rw [Finset.sum_eq_zero]
    · simp
    · intro y hy
      have hzy : z ≠ y := by
        intro h
        subst y
        exact hz hy
      simp [ReflectedWalk.ConductanceGraph.indic, hzy]

/-- Every finite partial row sum is at most one. -/
theorem semigroupKernel_finset_sum_le_one [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x : V) (A : Finset V) :
    ∑ y ∈ A, semigroupKernel G m t x y ≤ 1 := by
  let f : V → ℝ := ∑ y ∈ A, G.indic y
  let hf : HasSpeedL2 m f := hasSpeedL2_sum_indic G m A
  have hweighted : weightedValue m f hf =
      ∑ y ∈ A, weightedValue m (G.indic y)
        (VertexTest.indic_hasSpeedL2 G m y) :=
    weightedValue_sum_indic G m A
  have hsum : ∑ y ∈ A, semigroupKernel G m t x y =
      unweight m (fullFormSemigroup G m t (weightedValue m f hf)) x := by
    rw [hweighted, map_sum]
    simp only [semigroupKernel, unweight, Finset.sum_div, lp.coeFn_sum,
      Finset.sum_apply]
  rw [hsum]
  exact (fullFormSemigroup_mem_Icc G m hm t (weightedValue m f hf)
    (fun z ↦ by
      rw [unweight_weightedValue m hm]
      exact sum_indic_mem_Icc G A z) x).2

/-- A kernel row is summable, already without assuming finite total speed. -/
theorem summable_semigroupKernel [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x : V) :
    Summable (fun y ↦ semigroupKernel G m t x y) := by
  apply summable_of_sum_le (fun y ↦ semigroupKernel_nonneg G m hm t x y)
  intro A
  exact semigroupKernel_finset_sum_le_one G m hm t x A

private theorem semigroup_indic_apply_eq_sqrt_mul_kernel
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    fullFormSemigroup G m t
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x =
      Real.sqrt (m x) * semigroupKernel G m t x y := by
  simp only [semigroupKernel, unweight]
  have hs : Real.sqrt (m x) ≠ 0 := (Real.sqrt_pos.2 (hm x)).ne'
  field_simp [hs]

/-- For summable positive speed, every kernel row has total mass exactly one. -/
theorem tsum_semigroupKernel_eq_one [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (t : ℝ≥0) (x : V) :
    ∑' y, semigroupKernel G m t x y = 1 := by
  let wx := weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)
  let one := weightedValue m (fun _ : V ↦ (1 : ℝ)) (hasSpeedL2_const hm hmsum 1)
  have hweighted : ∑' y, m y * semigroupKernel G m t y x = m x := by
    have hinner :
        ⟪fullFormSemigroup G m t wx, one⟫_ℝ =
          ∑' y, m y * semigroupKernel G m t y x := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro y
      simp only [Real.inner_apply, one, weightedValue_apply]
      rw [semigroup_indic_apply_eq_sqrt_mul_kernel G m hm t y x, mul_one]
      calc
        Real.sqrt (m y) * semigroupKernel G m t y x * Real.sqrt (m y) =
            (Real.sqrt (m y) * Real.sqrt (m y)) *
              semigroupKernel G m t y x := by ring
        _ = m y * semigroupKernel G m t y x := by
          rw [Real.mul_self_sqrt (hm y).le]
    rw [← hinner]
    calc
      ⟪fullFormSemigroup G m t wx, one⟫_ℝ =
          ⟪wx, fullFormSemigroup G m t one⟫_ℝ :=
        (fullFormSemigroup_isSelfAdjoint G m t).isSymmetric _ _
      _ = ⟪wx, one⟫_ℝ := by
        rw [show fullFormSemigroup G m t one = one by
          exact fullFormSemigroup_weightedValue_const_fixed G m hm hmsum 1 t]
      _ = m x := by
        rw [show wx = lp.single 2 x (Real.sqrt (m x)) by
          exact weightedValue_indic_eq_single G m x, lp.inner_single_left]
        simp only [one, weightedValue_apply, Real.inner_apply, mul_one]
        exact Real.mul_self_sqrt (hm x).le
  have hbalance :
      ∑' y, m y * semigroupKernel G m t y x =
        m x * ∑' y, semigroupKernel G m t x y := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro y
    exact (semigroupKernel_detailedBalance G m hm t x y).symm
  have hmul : m x * ∑' y, semigroupKernel G m t x y = m x * 1 := by
    calc
      m x * ∑' y, semigroupKernel G m t x y =
          ∑' y, m y * semigroupKernel G m t y x := hbalance.symm
      _ = m x := hweighted
      _ = m x * 1 := (mul_one (m x)).symm
  exact (mul_left_cancel₀ (hm x).ne' hmul)

end ReflectedGMS.FullNetworkForm
