/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupKernelComposition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupKernel

/-!
# Chapman--Kolmogorov identity for the full-form semigroup kernel

The actual vertex coefficients of the full-form semigroup compose by convolution.
The proof takes the weighted `L²(m)` inner product of two semigroup images of
atomic indicators.  Its coordinate series is genuinely summable by the existing
`lp.summable_inner` theorem, and detailed balance removes the atomic speed from
each summand.

This is an analytic semigroup identity only.  It does not assert association
with a reflected path process.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace NNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

private theorem semigroup_indic_apply_eq_sqrt_mul_kernel
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    fullFormSemigroup G m t
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x =
      Real.sqrt (m x) * semigroupKernel G m t x y := by
  simp only [semigroupKernel, unweight]
  have hs : Real.sqrt (m x) ≠ 0 := (Real.sqrt_pos.2 (hm x)).ne'
  field_simp [hs]

private theorem inner_semigroup_indic_eq_mass_mul_kernel [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    ⟪fullFormSemigroup G m t
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)),
      weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)⟫_ℝ =
      m x * semigroupKernel G m t x y := by
  rw [weightedValue_indic_eq_single G m x, lp.inner_single_right]
  simp only [Real.inner_apply]
  rw [semigroup_indic_apply_eq_sqrt_mul_kernel G m hm t x y]
  calc
    Real.sqrt (m x) * semigroupKernel G m t x y * Real.sqrt (m x) =
        (Real.sqrt (m x) * Real.sqrt (m x)) *
          semigroupKernel G m t x y := by ring
    _ = m x * semigroupKernel G m t x y := by
      rw [Real.mul_self_sqrt (hm x).le]

/-- The Chapman--Kolmogorov summand is summable.  This follows from the
coordinatewise inner-product summability of the two weighted semigroup images,
with detailed balance supplying the exact `sqrt (m z)` normalization. -/
theorem summable_semigroupKernel_mul [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (s t : ℝ≥0) (x y : V) :
    Summable (fun z ↦
      semigroupKernel G m s x z * semigroupKernel G m t z y) := by
  let uy := fullFormSemigroup G m t
    (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))
  let ux := fullFormSemigroup G m s
    (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x))
  have hinner : Summable (fun z ↦ ⟪uy z, ux z⟫_ℝ) := lp.summable_inner uy ux
  have hscaled : Summable (fun z ↦ m x *
      (semigroupKernel G m s x z * semigroupKernel G m t z y)) := by
    refine hinner.congr (fun z ↦ ?_)
    simp only [uy, ux, Real.inner_apply]
    rw [semigroup_indic_apply_eq_sqrt_mul_kernel G m hm t z y,
      semigroup_indic_apply_eq_sqrt_mul_kernel G m hm s z x]
    have hbalance := semigroupKernel_detailedBalance G m hm s x z
    have hsqrt : Real.sqrt (m z) * Real.sqrt (m z) = m z :=
      Real.mul_self_sqrt (hm z).le
    calc
      Real.sqrt (m z) * semigroupKernel G m t z y *
          (Real.sqrt (m z) * semigroupKernel G m s z x) =
          (Real.sqrt (m z) * Real.sqrt (m z)) *
            (semigroupKernel G m s z x * semigroupKernel G m t z y) := by ring
      _ = (m z * semigroupKernel G m s z x) *
            semigroupKernel G m t z y := by rw [hsqrt]; ring
      _ = m x * (semigroupKernel G m s x z *
            semigroupKernel G m t z y) := by rw [← hbalance]; ring
  exact (summable_mul_left_iff (hm x).ne').mp hscaled

/-- Exact Chapman--Kolmogorov convolution for the actual full-form semigroup
kernel. -/
theorem tsum_semigroupKernel_mul_eq_semigroupKernel_add [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (s t : ℝ≥0) (x y : V) :
    ∑' z, semigroupKernel G m s x z * semigroupKernel G m t z y =
      semigroupKernel G m (s + t) x y := by
  let dy := weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)
  let dx := weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)
  let uy := fullFormSemigroup G m t dy
  let ux := fullFormSemigroup G m s dx
  have hsummable := summable_semigroupKernel_mul G m hm s t x y
  have hseries :
      ⟪uy, ux⟫_ℝ = m x *
        ∑' z, semigroupKernel G m s x z * semigroupKernel G m t z y := by
    rw [lp.inner_eq_tsum, ← hsummable.tsum_mul_left (m x)]
    apply tsum_congr
    intro z
    simp only [uy, ux, dy, dx, Real.inner_apply]
    rw [semigroup_indic_apply_eq_sqrt_mul_kernel G m hm t z y,
      semigroup_indic_apply_eq_sqrt_mul_kernel G m hm s z x]
    have hbalance := semigroupKernel_detailedBalance G m hm s x z
    have hsqrt : Real.sqrt (m z) * Real.sqrt (m z) = m z :=
      Real.mul_self_sqrt (hm z).le
    calc
      Real.sqrt (m z) * semigroupKernel G m t z y *
          (Real.sqrt (m z) * semigroupKernel G m s z x) =
          (Real.sqrt (m z) * Real.sqrt (m z)) *
            (semigroupKernel G m s z x * semigroupKernel G m t z y) := by ring
      _ = (m z * semigroupKernel G m s z x) *
            semigroupKernel G m t z y := by rw [hsqrt]; ring
      _ = m x * (semigroupKernel G m s x z *
            semigroupKernel G m t z y) := by rw [← hbalance]; ring
  have hsemigroup : ⟪uy, ux⟫_ℝ =
      m x * semigroupKernel G m (s + t) x y := by
    calc
      ⟪uy, ux⟫_ℝ = ⟪fullFormSemigroup G m s uy, dx⟫_ℝ :=
        ((fullFormSemigroup_isSelfAdjoint G m s).isSymmetric uy dx).symm
      _ = ⟪fullFormSemigroup G m (s + t) dy, dx⟫_ℝ := by
        rw [show uy = fullFormSemigroup G m t dy from rfl,
          fullFormSemigroup_add]
        rfl
      _ = m x * semigroupKernel G m (s + t) x y :=
        inner_semigroup_indic_eq_mass_mul_kernel G m hm (s + t) x y
  apply (mul_left_cancel₀ (hm x).ne')
  calc
    m x * (∑' z, semigroupKernel G m s x z * semigroupKernel G m t z y) =
        ⟪uy, ux⟫_ℝ := hseries.symm
    _ = m x * semigroupKernel G m (s + t) x y := hsemigroup

end ReflectedGMS.FullNetworkForm
