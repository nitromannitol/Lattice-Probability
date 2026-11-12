/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareGreen5 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Orthogonality of the Dirichlet sine and cosine modes of `(a, a+L)` (task P2-KHSQ)

`∫_a^{a+L} sin(πj(t−a)/L) sin(πk(t−a)/L) dt = (L/2) δ_{jk}` and the same for cosines
(`k ≥ 1`): product-to-sum formulas and `∫_a^{a+L} cos(πm(t−a)/L) dt = L·1_{m=0}`
(`m ∈ ℤ`, fundamental theorem of calculus, `sin(mπ) = 0`). Standard; own elementary proof.
-/

noncomputable section

open Real MeasureTheory Set

namespace LQGMetric
namespace HeatSq

lemma integral_Ioo_cos_int {a L : ℝ} (hL : 0 < L) (m : ℤ) :
    ∫ t in Ioo a (a + L), Real.cos (π * m * (t - a) / L) = if m = 0 then L else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  split_ifs with hm
  · subst hm; simp
  · have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hpi := Real.pi_pos
    have hd : ∀ t ∈ uIcc a (a + L), HasDerivAt
        (fun t => L / (π * m) * Real.sin (π * m * (t - a) / L))
        (Real.cos (π * m * (t - a) / L)) t := by
      intro t _
      have h1 : HasDerivAt (fun t => π * m * (t - a) / L) (π * m / L) t := by
        have := ((hasDerivAt_id t).sub_const a).const_mul (π * m) |>.div_const L
        simpa using this
      refine (((Real.hasDerivAt_sin _).comp t h1).const_mul (L / (π * m))).congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t => Real.cos (π * m * (t - a) / L)).intervalIntegrable _ _)]
    have e : π * m * (a + L - a) / L = m * π := by rw [add_sub_cancel_left]; field_simp
    simp only [e, Real.sin_int_mul_pi, sub_self, mul_zero, zero_div, Real.sin_zero]

lemma integrableOn_Ioo_of_continuous {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Ioo a b) :=
  hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- **Orthogonality of the sine modes.** -/
theorem integral_sinMode_mul_sinMode {a L : ℝ} (hL : 0 < L) {j k : ℕ} (hk : k ≠ 0) :
    ∫ t in Ioo a (a + L), sinMode a L j t * sinMode a L k t = if j = k then L / 2 else 0 := by
  have e : ∀ t, sinMode a L j t * sinMode a L k t =
      (Real.cos (π * ((j : ℤ) - k : ℤ) * (t - a) / L) -
        Real.cos (π * ((j : ℤ) + k : ℤ) * (t - a) / L)) / 2 := by
    intro t
    have h1 : π * (((j : ℤ) - k : ℤ) : ℝ) * (t - a) / L =
        π * j * (t - a) / L - π * k * (t - a) / L := by push_cast; ring
    have h2 : π * (((j : ℤ) + k : ℤ) : ℝ) * (t - a) / L =
        π * j * (t - a) / L + π * k * (t - a) / L := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add, sinMode, sinMode]; ring
  simp_rw [e]
  rw [integral_div, integral_sub (integrableOn_Ioo_of_continuous (by fun_prop))
    (integrableOn_Ioo_of_continuous (by fun_prop)), integral_Ioo_cos_int hL,
    integral_Ioo_cos_int hL]
  have hjk : ((j : ℤ) + k : ℤ) ≠ 0 := by omega
  rw [if_neg hjk]
  by_cases h : j = k
  · subst h; simp
  · have : ((j : ℤ) - k : ℤ) ≠ 0 := by omega
    rw [if_neg this, if_neg h]; simp

/-- the cosine modes `cos(πk(u−a)/L)` -/
def cosMode (a L : ℝ) (k : ℕ) (u : ℝ) : ℝ := Real.cos (π * k * (u - a) / L)

/-- **Orthogonality of the cosine modes** (`k ≥ 1`). -/
theorem integral_cosMode_mul_cosMode {a L : ℝ} (hL : 0 < L) {j k : ℕ} (hk : k ≠ 0) :
    ∫ t in Ioo a (a + L), cosMode a L j t * cosMode a L k t = if j = k then L / 2 else 0 := by
  have e : ∀ t, cosMode a L j t * cosMode a L k t =
      (Real.cos (π * ((j : ℤ) - k : ℤ) * (t - a) / L) +
        Real.cos (π * ((j : ℤ) + k : ℤ) * (t - a) / L)) / 2 := by
    intro t
    have h1 : π * (((j : ℤ) - k : ℤ) : ℝ) * (t - a) / L =
        π * j * (t - a) / L - π * k * (t - a) / L := by push_cast; ring
    have h2 : π * (((j : ℤ) + k : ℤ) : ℝ) * (t - a) / L =
        π * j * (t - a) / L + π * k * (t - a) / L := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add, cosMode, cosMode]; ring
  simp_rw [e]
  rw [integral_div, integral_add (integrableOn_Ioo_of_continuous (by fun_prop))
    (integrableOn_Ioo_of_continuous (by fun_prop)), integral_Ioo_cos_int hL,
    integral_Ioo_cos_int hL]
  have hjk : ((j : ℤ) + k : ℤ) ≠ 0 := by omega
  rw [if_neg hjk]
  by_cases h : j = k
  · subst h; simp
  · have : ((j : ℤ) - k : ℤ) ≠ 0 := by omega
    rw [if_neg this, if_neg h]; simp

/-- **Orthogonality of the square modes** on `(a,a+L)²` (`j, k, j', k' ≥ 1`). -/
theorem integral_sqOpen_sqMode_mul {a L : ℝ} (hL : 0 < L) {p q : ℕ × ℕ} (hq1 : q.1 ≠ 0)
    (hq2 : q.2 ≠ 0) :
    ∫ z in sqOpen a L, sqMode a L p z * sqMode a L q z = if p = q then (L / 2) ^ 2 else 0 := by
  have e : ∀ z : ℂ, sqMode a L p z * sqMode a L q z =
      (sinMode a L p.1 z.re * sinMode a L q.1 z.re) *
        (sinMode a L p.2 z.im * sinMode a L q.2 z.im) := fun z => by
    unfold sqMode; ring
  simp_rw [e]
  rw [integral_sqOpen_re_mul_im a L (fun t => sinMode a L p.1 t * sinMode a L q.1 t)
    (fun t => sinMode a L p.2 t * sinMode a L q.2 t),
    integral_sinMode_mul_sinMode hL hq1, integral_sinMode_mul_sinMode hL hq2]
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all [sq]

end HeatSq
end LQGMetric
