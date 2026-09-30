/-
The insertion inequality on `ℤ^d`: for `d ≥ 2` and any injective enumeration
`x 0, …, x (M-1)` of `M ≥ 1` sites, with `A_i` the set of the sites before `x i`,

  `∑ i, (h_{A_i}(x i) + u_{A_i ∪ {x i}}(x i)) ≤ C M^{1 + 1/d}`,

with `C` depending only on `d`.

`insertion_inequality_of` derives this from the exit time bounds and the resistance packing
bound, taken as hypotheses.  `one_point_insertion` gives, at each step, `u = Reff * h` and
`T(A_{i+1}) - T(A_i) = h u`, hence `h^2 ≤ 2d (T(A_{i+1}) - T(A_i))` from `Reff ≥ 1/(2d)`, and
`u^2 = Reff (T(A_{i+1}) - T(A_i))`.  The differences telescope to `T(A_M)`, and two
Cauchy-Schwarz inequalities turn the two sums into `M^{1+1/d}`.  `insertion_inequality`
discharges the two hypotheses with `exit_time_bounds` and `resistance_packing`.

Moved from the ORRW formalization (`nitromannitol/ORRW-Lower-Bound`,
`ORRW/Support/InsertionSum.lean`), where it proves the insertion inequality
`lem:insertion` of Bou-Rabee and Peres on once-reinforced random walk.
-/
import Mathlib
import LatticeProb.Walk.Harmonic
import LatticeProb.Walk.ExitTime
import LatticeProb.Walk.ResistancePacking

open Finset
open scoped Matrix

namespace LatticeProb

variable {d : ℕ}

/-- The insertion inequality, given the exit time bounds (in the form of
`LatticeProb.exit_time_bounds`) and the resistance packing bound (in the form of
`LatticeProb.resistance_packing`) as hypotheses. -/
theorem insertion_inequality_of (hd : 2 ≤ d)
    (hmax : ∃ C : ℝ, 0 < C ∧ ∀ A : Finset (Site d), A.Nonempty →
      (∀ y ∈ A, u A y ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      (∀ y ∉ A, LatticeProb.h A y ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      T A ≤ C * (A.card : ℝ) ^ (1 + (2 : ℝ) / (d : ℝ)))
    (hpack : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, Reff ((Finset.Iio i).image x) (x i) ≤ C * (M : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, (LatticeProb.h ((Finset.Iio i).image x) (x i)
            + u (insert (x i) ((Finset.Iio i).image x)) (x i))
        ≤ C * (M : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := by
  classical
  obtain ⟨C₁, hC₁, hmax'⟩ := hmax
  obtain ⟨C₂, hC₂, hpack'⟩ := hpack
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
  refine ⟨Real.sqrt (2*(d:ℝ)*C₁) + Real.sqrt (C₁*C₂), by positivity, ?_⟩
  intro M hM x hinj
  simp only [pref_Iio]
  set P : ℝ := (M:ℝ) ^ (1 + (1:ℝ)/(d:ℝ)) with hP
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hPpos : 0 < P := Real.rpow_pos_of_pos hMR _
  have hPP : P * P = (M:ℝ) * (M:ℝ) ^ (1 + (2:ℝ)/(d:ℝ)) := by
    have h1 : P * P = (M:ℝ) ^ ((1 + (1:ℝ)/(d:ℝ)) + (1 + (1:ℝ)/(d:ℝ))) :=
      (Real.rpow_add hMR _ _).symm
    have h2 : (M:ℝ) * (M:ℝ) ^ (1 + (2:ℝ)/(d:ℝ)) = (M:ℝ) ^ ((1:ℝ) + (1 + (2:ℝ)/(d:ℝ))) := by
      rw [Real.rpow_add hMR (1:ℝ) (1 + (2:ℝ)/(d:ℝ)), Real.rpow_one]
    rw [h1, h2]
    congr 1
    ring
  have key : ∀ i : Fin M,
      u (insert (x i) (pref x (i:ℕ))) (x i)
          = Reff (pref x (i:ℕ)) (x i) * LatticeProb.h (pref x (i:ℕ)) (x i)
      ∧ T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))
          = LatticeProb.h (pref x (i:ℕ)) (x i) * u (insert (x i) (pref x (i:ℕ))) (x i)
      ∧ 1/(2*(d:ℝ)) ≤ Reff (pref x (i:ℕ)) (x i) := by
    intro i
    obtain ⟨e1, e2, e3⟩ :=
      one_point_insertion hd1 (pref x (i:ℕ)) (x i) (pref_notMem x hinj i)
    refine ⟨e1, ?_, e3⟩
    rw [← pref_succ x i]
    exact e2
  have hRnn : ∀ i : Fin M, 0 ≤ Reff (pref x (i:ℕ)) (x i) := by
    intro i
    exact le_trans (by positivity) (key i).2.2
  have hdTnn : ∀ i : Fin M, 0 ≤ T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ)) := by
    intro i
    obtain ⟨e1, e2, _⟩ := key i
    rw [e2, e1]
    have hh0 : (0:ℝ) ≤ LatticeProb.h (pref x (i:ℕ)) (x i) :=
      le_trans zero_le_one (one_le_h hd1 _ _)
    exact mul_nonneg hh0 (mul_nonneg (hRnn i) hh0)
  have hhsq : ∀ i : Fin M, (LatticeProb.h (pref x (i:ℕ)) (x i))^2
      ≤ 2*(d:ℝ)*(T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
    intro i
    obtain ⟨e1, e2, e3⟩ := key i
    rw [e2, e1]
    rw [div_le_iff₀ (by positivity)] at e3
    nlinarith [sq_nonneg (LatticeProb.h (pref x (i:ℕ)) (x i)), e3]
  have huabs : ∀ i : Fin M, u (insert (x i) (pref x (i:ℕ))) (x i)
      ≤ Real.sqrt (Reff (pref x (i:ℕ)) (x i))
        * Real.sqrt (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
    intro i
    obtain ⟨e1, e2, _⟩ := key i
    have hsq : (u (insert (x i) (pref x (i:ℕ))) (x i))^2
        = Reff (pref x (i:ℕ)) (x i) * (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
      rw [e2, e1]; ring
    calc u (insert (x i) (pref x (i:ℕ))) (x i)
        ≤ |u (insert (x i) (pref x (i:ℕ))) (x i)| := le_abs_self _
      _ = Real.sqrt ((u (insert (x i) (pref x (i:ℕ))) (x i))^2) := (Real.sqrt_sq_eq_abs _).symm
      _ = Real.sqrt (Reff (pref x (i:ℕ)) (x i)
            * (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ)))) := by rw [hsq]
      _ = Real.sqrt (Reff (pref x (i:ℕ)) (x i))
            * Real.sqrt (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := Real.sqrt_mul (hRnn i) _
  have htel : ∑ i : Fin M, (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) = T (pref x M) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => T (pref x (k+1)) - T (pref x k)) M,
      Finset.sum_range_sub (fun k => T (pref x k)) M, pref_zero]
    simp [T]
  have hTM : T (pref x M) ≤ C₁ * (M:ℝ) ^ (1 + (2:ℝ)/(d:ℝ)) := by
    have hne : (pref x M).Nonempty := by
      rw [← Finset.card_pos, pref_card x hinj]
      omega
    have hb := (hmax' (pref x M) hne).2.2
    rwa [pref_card x hinj] at hb
  have hRsum : ∑ i : Fin M, Reff (pref x (i:ℕ)) (x i) ≤ C₂ * (M:ℝ) := by
    have hb := hpack' M hM x hinj
    simpa only [pref_Iio] using hb
  rw [Finset.sum_add_distrib]
  have hHbound : (∑ i : Fin M, LatticeProb.h (pref x (i:ℕ)) (x i)) ≤ Real.sqrt (2*(d:ℝ)*C₁) * P := by
    have h1 : (∑ i : Fin M, LatticeProb.h (pref x (i:ℕ)) (x i))^2
        ≤ (M:ℝ) * ∑ i : Fin M, (LatticeProb.h (pref x (i:ℕ)) (x i))^2 := by
      have hc := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin M)))
        (f := fun i => LatticeProb.h (pref x (i:ℕ)) (x i))
      simpa using hc
    have h2 : (∑ i : Fin M, (LatticeProb.h (pref x (i:ℕ)) (x i))^2) ≤ 2*(d:ℝ)*T (pref x M) := by
      calc (∑ i : Fin M, (LatticeProb.h (pref x (i:ℕ)) (x i))^2)
          ≤ ∑ i : Fin M, 2*(d:ℝ)*(T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) :=
            Finset.sum_le_sum (fun i _ => hhsq i)
        _ = 2*(d:ℝ) * ∑ i : Fin M, (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
            rw [Finset.mul_sum]
        _ = 2*(d:ℝ)*T (pref x M) := by rw [htel]
    have h3 : (∑ i : Fin M, LatticeProb.h (pref x (i:ℕ)) (x i))^2 ≤ (2*(d:ℝ)*C₁) * (P*P) := by
      have h4 : (M:ℝ) * ∑ i : Fin M, (LatticeProb.h (pref x (i:ℕ)) (x i))^2
          ≤ (M:ℝ) * (2*(d:ℝ)*(C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hMR.le
        exact h2.trans (by nlinarith [hTM])
      rw [hPP]
      refine h1.trans (h4.trans ?_)
      ring_nf
      exact le_refl _
    have h5 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_sq_eq_abs] at h5
    have h6 : Real.sqrt ((2*(d:ℝ)*C₁)*(P*P)) = Real.sqrt (2*(d:ℝ)*C₁) * P := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self hPpos.le]
    rw [h6] at h5
    exact le_trans (le_abs_self _) h5
  have hUbound : (∑ i : Fin M, u (insert (x i) (pref x (i:ℕ))) (x i))
      ≤ Real.sqrt (C₁*C₂) * P := by
    have h1 : (∑ i : Fin M, u (insert (x i) (pref x (i:ℕ))) (x i))
        ≤ ∑ i : Fin M, Real.sqrt (Reff (pref x (i:ℕ)) (x i))
            * Real.sqrt (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) :=
      Finset.sum_le_sum (fun i _ => huabs i)
    have h2 := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin M))
      (f := fun i : Fin M => Reff (pref x (i:ℕ)) (x i))
      (g := fun i : Fin M => T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) hRnn hdTnn
    have h3 : Real.sqrt (∑ i : Fin M, Reff (pref x (i:ℕ)) (x i))
        * Real.sqrt (∑ i : Fin M, (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))))
        ≤ Real.sqrt (C₂ * (M:ℝ)) * Real.sqrt (C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ))) := by
      refine mul_le_mul (Real.sqrt_le_sqrt hRsum) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [htel]
      exact Real.sqrt_le_sqrt hTM
    have h4 : Real.sqrt (C₂ * (M:ℝ)) * Real.sqrt (C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ)))
        = Real.sqrt (C₁*C₂) * P := by
      rw [← Real.sqrt_mul (by positivity)]
      have h5 : C₂ * (M:ℝ) * (C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ))) = (C₁*C₂) * (P*P) := by
        rw [hPP]; ring
      rw [h5, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hPpos.le]
    linarith [h1, h2, h3, h4 ▸ h3]
  have : Real.sqrt (2*(d:ℝ)*C₁) * P + Real.sqrt (C₁*C₂) * P
      = (Real.sqrt (2*(d:ℝ)*C₁) + Real.sqrt (C₁*C₂)) * P := by ring
  linarith [hHbound, hUbound]

/-- The insertion inequality.  For `d ≥ 2` there is a constant `C > 0`, depending only on
`d`, such that for every injective enumeration `x : Fin M → Site d` of `M ≥ 1` sites,
with `A_i` the set of the sites before `x i`,
`∑ i, (h A_i (x i) + u (insert (x i) A_i) (x i)) ≤ C * M ^ (1 + 1/d)`. -/
theorem insertion_inequality (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, (LatticeProb.h ((Finset.Iio i).image x) (x i)
            + u (insert (x i) ((Finset.Iio i).image x)) (x i))
        ≤ C * (M : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
  insertion_inequality_of hd (exit_time_bounds (by omega)) (resistance_packing hd)

end LatticeProb
