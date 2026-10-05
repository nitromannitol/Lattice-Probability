/-
# The band-limited `C^m` net: the uniform-bound packaging

Half of the `rkLowFreqNet` residual: the **band-limited Bernstein bound** together with the
**finite `C^m` ε-net** (Arzelà–Ascoli).  The two analytic ingredients already exist in this
worktree — `bandLimitedCmBound_holds` (`BandLimitedCmBound.lean`: a uniform bound on
the `k`-th derivative of the truncation `P_Λ` over the `H^s` unit ball, for each `k`) and
`exists_finite_supNet_of_uniformLip` (`RellichCmNetReduction.lean`: Arzelà–Ascoli, a finite
sup-net with centres in the family).

What is landed here is the packaging those two need to be composable: `BandLimitedCmBound`
gives one constant per order `k`, whereas `exists_finite_supNet_of_uniformLip` wants a
**single** uniform bound and a uniform Lipschitz bound.  `exists_uniform_iteratedFDeriv_le`
collapses the first into one constant valid for all `k ≤ m` by a finite maximum.

## The exact missing pieces

1. **The uniform Lipschitz bound.**  `exists_finite_supNet_of_uniformLip` also needs
   `dist (f x) (f y) ≤ C * dist x y` for every member of the family `S`, i.e. the `k = 1` case of
   the Bernstein bound transferred from `iteratedFDeriv ℝ 1` to `BoundedContinuousFunction`
   distance (`‖f x - f y‖ ≤ ‖fderiv f‖ * ‖x - y‖`); not landed here.
2. **The compactness of the domain.**  Arzelà–Ascoli is instantiated on a compact space; the
   band-limited functions are *not* compactly supported, so one must either restrict to a compact
   carrier or use the support/mollification repair (**ds1's half**) to place the centres in
   `IsTestFn D`.
3. **The multi-index form.**  `sobolevNormSq`-based statements use `iteratedFDeriv ℝ k`; a `C^m`
   net in the paper's sense is a bound on all multi-indices of order `≤ m`, which is a finite
   max over `k ≤ m` of the operator norms (the step below), plus the translation between the two.
-/
import LatticeProb.Analysis.Sobolev.BandLimitedCmBound

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Sobolev

/-- **The uniform `C^m` bound.**  `BandLimitedCmBound` gives one constant per order; a single
constant works for all orders `k ≤ m`, which is the form Arzelà–Ascoli consumes. -/
theorem exists_uniform_iteratedFDeriv_le {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) {s : ℝ}
    (hs : 0 ≤ s) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ) (x : Space d),
      sobolevNormSq d s φ ≤ 1 →
        ∀ k ≤ m, ‖iteratedFDeriv ℝ k
            (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y)
              x‖ ≤ C := by
  choose C hCpos hC using fun k : ℕ => bandLimitedCmBound_holds (d := d) Λ hΛ hs k
  set S : ℝ := Finset.sup' (Finset.range (m + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩ C with hS
  have hle0 : C 0 ≤ S := Finset.le_sup' C (Finset.mem_range.mpr (Nat.succ_pos m))
  refine ⟨S + 1, by linarith [hCpos 0, hle0], ?_⟩
  intro φ hcont hcs x hφ k hk
  have hle : C k ≤ S := Finset.le_sup' C (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  calc ‖iteratedFDeriv ℝ k
        (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y) x‖
      ≤ C k := hC k φ hcont hcs x hφ
    _ ≤ S := hle
    _ ≤ S + 1 := le_add_of_nonneg_right zero_le_one

/-- **The multi-index form.**  The order-`k` operator bound above controls every partial
derivative of order `k ≤ m`; evaluated on a tuple `v : Fin k → Space d` it gives
`‖D^k f x (v)‖ ≤ C ∏ i, ‖v i‖`.  This is the form in which a `C^m` bound is read off a family of
multi-indices. -/
theorem exists_uniform_iteratedFDeriv_apply_le {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) {s : ℝ}
    (hs : 0 ≤ s) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ) (x : Space d),
      sobolevNormSq d s φ ≤ 1 →
        ∀ (k : ℕ), k ≤ m → ∀ v : Fin k → Space d,
          ‖iteratedFDeriv ℝ k
              (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y)
              x v‖ ≤ C * ∏ i, ‖v i‖ := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_iteratedFDeriv_le (d := d) Λ hΛ hs m
  refine ⟨C, hCpos, fun φ hcont hcs x hφ k hk v => ?_⟩
  exact (ContinuousMultilinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (hC φ hcont hcs x hφ k hk)
      (Finset.prod_nonneg fun i _ => norm_nonneg _))

end LatticeProb.Sobolev

#print axioms LatticeProb.Sobolev.exists_uniform_iteratedFDeriv_le
#print axioms LatticeProb.Sobolev.exists_uniform_iteratedFDeriv_apply_le
