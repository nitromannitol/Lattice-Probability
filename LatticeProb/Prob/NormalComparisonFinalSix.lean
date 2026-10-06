/-
# Li--Shao normal comparison: the boundary bound along the smart path (route item 5)

Continuing `LatticeProb/Prob/NormalComparisonFinalFive.lean`.  The boundary integral of the density
`covDensity S_t` along the corner `pairCorner σ b` is nonnegative and at most the bivariate
Gaussian density at correlation `t * S (σ 0) (σ 1) / v`.  This file supplies the corner map
`pairCorner`, its nonnegativity, and the reduction of the boundary bound to the marginal fact
`∫_{x'' ≤ b} covDensity S_t (pairCorner σ b x'') ≤ covDensity M₂ ![b (σ 0), b (σ 1)]`:
the `2 × 2` submatrix `M₂` with `c = t * S (σ 0) (σ 1)` equals `!![v, c; c, v]`, and
`covDensity_two_cov` turns its density into `bivariateGaussDensity v (c / v)`.

No `External` is touched, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/
import LatticeProb.Prob.NormalComparisonFinalFive

open MeasureTheory Matrix

namespace LatticeProb

/-! ### The corner point -/

/-- The point of `Fin (m+2) → ℝ` whose coordinates `σ 0`, `σ 1` equal `b (σ 0)`, `b (σ 1)`
and whose remaining coordinates `σ (k+2)` are `x'' k`. -/
def pairCorner {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ)
    (x'' : Fin m → ℝ) :
    Fin (m + 2) → ℝ :=
  fun l => (Fin.cons (α := fun _ : Fin (m + 2) => ℝ) (b (σ 0))
    (Fin.cons (b (σ 1)) x'') : Fin (m + 2) → ℝ) (σ.symm l)

/-- The coordinate `σ 0` of the corner point is `b (σ 0)`. -/
theorem pairCorner_apply_zero {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ)
    (x'' : Fin m → ℝ) : pairCorner σ b x'' (σ 0) = b (σ 0) := by
  simp [pairCorner]

/-- The coordinate `σ 1` of the corner point is `b (σ 1)`. -/
theorem pairCorner_apply_one {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ)
    (x'' : Fin m → ℝ) : pairCorner σ b x'' (σ 1) = b (σ 1) := by
  simp [pairCorner]

/-- The coordinate `σ (k + 2)` of the corner point is `x'' k`. -/
theorem pairCorner_apply_succ_succ {m : ℕ} (σ : Equiv.Perm (Fin (m + 2)))
    (b : Fin (m + 2) → ℝ) (x'' : Fin m → ℝ) (k : Fin m) :
    pairCorner σ b x'' (σ k.succ.succ) = x'' k := by
  simp [pairCorner]

/-! ### Nonnegativity of the boundary integral -/

/-- The boundary integral is nonnegative: it integrates the positive density `covDensity S` along
the corner `pairCorner σ b`. -/
theorem integral_Iic_pairCorner_covDensity_nonneg {m : ℕ}
    {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hS : S.PosDef)
    (b : Fin (m + 2) → ℝ) (σ : Equiv.Perm (Fin (m + 2))) :
    0 ≤ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
      covDensity S (pairCorner σ b x'') :=
  integral_nonneg fun x'' => (covDensity_pos hS (pairCorner σ b x'')).le

/-! ### The boundary bound from the marginal fact -/

/-- **Route item 5 from the marginal fact.**  Given the marginal bound `hmarg` for the `2 × 2`
corner density, the boundary integral of `covDensity S_t` along `pairCorner σ b` is nonnegative
and at most the bivariate density at correlation `t * S (σ 0) (σ 1) / v`.  The `2 × 2` submatrix
of the smart path is `!![v, c; c, v]` with `c = t * S (σ 0) (σ 1)`, and `covDensity_two_cov`
identifies its density with `bivariateGaussDensity v (c / v)`. -/
theorem boundary_covDensity_path_le_of_marginal {m : ℕ} {v : ℝ}
    {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hv : 0 < v) (hS : S.PosSemidef)
    (hdiag : ∀ i, S i i = v) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hmarg : ∀ (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ),
      ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
          covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'')
        ≤ covDensity (!![normalComparisonSmartPath v S t (σ 0) (σ 0),
              normalComparisonSmartPath v S t (σ 0) (σ 1);
              normalComparisonSmartPath v S t (σ 1) (σ 0),
              normalComparisonSmartPath v S t (σ 1) (σ 1)] : Matrix (Fin 2) (Fin 2) ℝ)
            ![b (σ 0), b (σ 1)])
    (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ) :
    0 ≤ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
        covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'')
    ∧ ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)),
        covDensity (normalComparisonSmartPath v S t) (pairCorner σ b x'')
      ≤ bivariateGaussDensity v (t * S (σ 0) (σ 1) / v) (b (σ 0)) (b (σ 1)) := by
  have hM := normalComparisonSmartPath_posDef hS hv ht
  have hne : σ 0 ≠ σ 1 := fun h => Fin.zero_ne_one (σ.injective h)
  have hsym : S (σ 1) (σ 0) = S (σ 0) (σ 1) := by
    simpa using hS.isHermitian.apply (σ 0) (σ 1)
  have hc : |t * S (σ 0) (σ 1)| < v := by
    have hb := abs_apply_le_of_posSemidef_diag hv hS hdiag (σ 0) (σ 1)
    rw [abs_mul, abs_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, abs_nonneg (S (σ 0) (σ 1))]
  have hmat : (!![normalComparisonSmartPath v S t (σ 0) (σ 0),
        normalComparisonSmartPath v S t (σ 0) (σ 1);
        normalComparisonSmartPath v S t (σ 1) (σ 0),
        normalComparisonSmartPath v S t (σ 1) (σ 1)] : Matrix (Fin 2) (Fin 2) ℝ)
      = !![v, t * S (σ 0) (σ 1); t * S (σ 0) (σ 1), v] := by
    rw [normalComparisonSmartPath_diag hdiag, normalComparisonSmartPath_diag hdiag,
      normalComparisonSmartPath_apply_of_ne v S t hne,
      normalComparisonSmartPath_apply_of_ne v S t hne.symm, hsym]
  refine ⟨integral_Iic_pairCorner_covDensity_nonneg hM b σ, ?_⟩
  refine (hmarg σ b).trans ?_
  rw [hmat, covDensity_two_cov hv hc]

end LatticeProb
