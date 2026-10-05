/-
# Li--Shao normal comparison: the mixed-derivative orthant integral in an arbitrary pair of
coordinates (route item 4)

Continuing `LatticeProb/Prob/NormalComparisonOrthantMixed.lean`: there
`integral_Iic_mixed_deriv₂` integrates the mixed derivative `∂₁ ∂₀ p = pxy` over the orthant
`Set.Iic b ⊆ (Fin (m+2) → ℝ)`, but only in the coordinates `0` and `1`.  The Gaussian density of
the next packets is differentiated through `Function.update x i s` in an *arbitrary* ordered
pair `i ≠ j` of coordinates.  This file moves `(i, j)` to `(0, 1)` by a coordinate permutation
`σ` with `σ 0 = i`, `σ 1 = j` (`exists_perm_zero_one`) and transports every hypothesis.

## Route

* Put `T y := fun l => y (σ.symm l)` and `p' := p ∘ T`, `px' := px ∘ T`, `pxy' := pxy ∘ T`,
  `b' := fun k => b (σ k)`.  By `integral_Iic_perm` and `integrableOn_Iic_perm`, the orthant
  integral of `pxy` over `Iic b` is that of `pxy'` over `Iic b'`, and integrability transports.
* **Bridge.**  `T (Function.update z a v) = Function.update (T z) (σ a) v`
  (`perm_comp_update`, from `Function.update_comp_equiv`).  Combined with
  `Fin.cons x₀ (Fin.cons s x'') = update (Fin.cons x₀ (Fin.cons 0 x'')) 1 s` and
  `Fin.cons x (Fin.cons c x'') = update (Fin.cons 0 (Fin.cons c x'')) 0 x`, the slices of
  `p', px', pxy'` along `Fin.cons` are the slices of `p, px, pxy` along
  `Function.update _ (σ 1) s`, resp. `Function.update _ (σ 0) s`; the side condition
  `y (σ 1) = b (σ 1)` holds because the second coordinate of the base point is `b' 1`.
* `integral_Iic_mixed_deriv₂ b' p' px' pxy'` then gives the value
  `p' (Fin.cons (b' 0) (Fin.cons (b' 1) x'')) = p (pairCorner σ b x'')` on the right, and the
  final statement `exists_perm_integral_Iic_mixed_deriv` chooses `σ` for a given pair `i ≠ j`.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonOrthantMixed
import LatticeProb.Prob.NormalComparisonOrthantPerm

open MeasureTheory

namespace LatticeProb

/-! ### The corner point and its coordinates -/

/-- The point of `Fin (m+2) → ℝ` whose coordinates `σ 0`, `σ 1` equal `b (σ 0)`, `b (σ 1)` and
whose remaining coordinates `σ (k+2)` are `x'' k`. -/
def pairCorner {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ) (x'' : Fin m → ℝ) :
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

/-! ### The bridge between `Fin.cons` slices and `Function.update` slices -/

/-- Permuting the coordinates commutes with `Function.update`:
`(update z a v) ∘ σ⁻¹ = update (z ∘ σ⁻¹) (σ a) v`. -/
private theorem perm_comp_update {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : Fin n → ℝ) (a : Fin n)
    (v : ℝ) :
    (fun l => (Function.update z a v) (σ.symm l))
      = Function.update (fun l => z (σ.symm l)) (σ a) v :=
  Function.update_comp_equiv z σ.symm a v

/-- Varying the second `Fin.cons` coordinate is an `update` in coordinate `1`. -/
private theorem cons_cons_eq_update_one {m : ℕ} (x₀ s : ℝ) (x'' : Fin m → ℝ) :
    (Fin.cons x₀ (Fin.cons s x'') : Fin (m + 2) → ℝ)
      = Function.update (Fin.cons x₀ (Fin.cons (0 : ℝ) x'') : Fin (m + 2) → ℝ) 1 s := by
  have h1 : (Fin.cons s x'' : Fin (m + 1) → ℝ)
      = Function.update (Fin.cons (0 : ℝ) x'' : Fin (m + 1) → ℝ) 0 s :=
    (Fin.update_cons_zero _ _ _).symm
  rw [h1, Fin.cons_update, Fin.succ_zero_eq_one']

/-- Varying the first `Fin.cons` coordinate is an `update` in coordinate `0`. -/
private theorem cons_cons_eq_update_zero {m : ℕ} (x₀ c : ℝ) (x'' : Fin m → ℝ) :
    (Fin.cons x₀ (Fin.cons c x'') : Fin (m + 2) → ℝ)
      = Function.update (Fin.cons (0 : ℝ) (Fin.cons c x'') : Fin (m + 2) → ℝ) 0 x₀ :=
  (Fin.update_cons_zero _ _ _).symm

/-- The permuted `Fin.cons` point with varying second coordinate is an `update` in the
coordinate `σ 1` of the permuted base point. -/
private theorem perm_cons_cons_update_one {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (x₀ s : ℝ)
    (x'' : Fin m → ℝ) :
    (fun l => (Fin.cons x₀ (Fin.cons s x'') : Fin (m + 2) → ℝ) (σ.symm l))
      = Function.update
          (fun l => (Fin.cons x₀ (Fin.cons (0 : ℝ) x'') : Fin (m + 2) → ℝ) (σ.symm l)) (σ 1) s := by
  rw [cons_cons_eq_update_one x₀ s x'', perm_comp_update]

/-- The permuted `Fin.cons` point with varying first coordinate is an `update` in the
coordinate `σ 0` of the permuted base point. -/
private theorem perm_cons_cons_update_zero {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (x₀ c : ℝ)
    (x'' : Fin m → ℝ) :
    (fun l => (Fin.cons x₀ (Fin.cons c x'') : Fin (m + 2) → ℝ) (σ.symm l))
      = Function.update
          (fun l => (Fin.cons (0 : ℝ) (Fin.cons c x'') : Fin (m + 2) → ℝ) (σ.symm l)) (σ 0) x₀ := by
  rw [cons_cons_eq_update_zero x₀ c x'', perm_comp_update]

/-- The coordinate `σ 1` of the permuted base point `(0, c, x'')` is `c`. -/
private theorem perm_cons_cons_apply_one {m : ℕ} (σ : Equiv.Perm (Fin (m + 2))) (x₀ c : ℝ)
    (x'' : Fin m → ℝ) :
    (fun l => (Fin.cons x₀ (Fin.cons c x'') : Fin (m + 2) → ℝ) (σ.symm l)) (σ 1) = c := by
  simp

/-! ### The mixed-derivative orthant integral in a general pair of coordinates -/

/-- **General-coordinate mixed derivative of an orthant integral.**  With `i := σ 0` and
`j := σ 1`: `px = ∂_i p` and `pxy = ∂_j px`, so `pxy = ∂_j ∂_i p`.  Integrating over the orthant
`{x ≤ b} ⊆ (Fin (m+2) → ℝ)` leaves `p` at the corner `pairCorner σ b x''` (coordinates `i`, `j`
frozen at `b i`, `b j`), integrated over the orthant of the remaining `m` coordinates
`σ (k+2)`.  The hypotheses are the differentiability, integrability and decay side conditions of
a smooth rapidly decaying density, along the coordinate lines `Function.update y (σ 1) s` and
`Function.update y (σ 0) s`; those for `p` and `px` are required only on the hyperplane
`y (σ 1) = b (σ 1)`.

The proof permutes the coordinates with `integral_Iic_perm` / `integrableOn_Iic_perm` and
applies `integral_Iic_mixed_deriv₂` to `p ∘ T`, `px ∘ T`, `pxy ∘ T`, where
`T y = fun l => y (σ.symm l)`. -/
theorem integral_Iic_mixed_deriv_pair {m : ℕ} (σ : Equiv.Perm (Fin (m + 2)))
    (b : Fin (m + 2) → ℝ) (p px pxy : (Fin (m + 2) → ℝ) → ℝ)
    (hint : IntegrableOn pxy (Set.Iic b) volume)
    (hdy : ∀ y : Fin (m + 2) → ℝ, ∀ t ∈ Set.Iic (b (σ 1)),
      HasDerivAt (fun s => px (Function.update y (σ 1) s)) (pxy (Function.update y (σ 1) t)) t)
    (hdy_int : ∀ y : Fin (m + 2) → ℝ,
      IntegrableOn (fun s => pxy (Function.update y (σ 1) s)) (Set.Iic (b (σ 1))))
    (hdy_lim : ∀ y : Fin (m + 2) → ℝ,
      Filter.Tendsto (fun s => px (Function.update y (σ 1) s)) Filter.atBot (nhds 0))
    (hdx : ∀ y : Fin (m + 2) → ℝ, y (σ 1) = b (σ 1) → ∀ t ∈ Set.Iic (b (σ 0)),
      HasDerivAt (fun s => p (Function.update y (σ 0) s)) (px (Function.update y (σ 0) t)) t)
    (hdx_int : ∀ y : Fin (m + 2) → ℝ, y (σ 1) = b (σ 1) →
      IntegrableOn (fun s => px (Function.update y (σ 0) s)) (Set.Iic (b (σ 0))))
    (hlim : ∀ y : Fin (m + 2) → ℝ, y (σ 1) = b (σ 1) →
      Filter.Tendsto (fun s => p (Function.update y (σ 0) s)) Filter.atBot (nhds 0)) :
    ∫ x in Set.Iic b, pxy x
      = ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)), p (pairCorner σ b x'') := by
  have hI := (integrableOn_Iic_perm σ b pxy).mp hint
  rw [integral_Iic_perm σ b pxy]
  refine integral_Iic_mixed_deriv₂ (fun k => b (σ k)) (fun y => p (fun l => y (σ.symm l)))
    (fun y => px (fun l => y (σ.symm l))) (fun y => pxy (fun l => y (σ.symm l))) hI
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro x₀ x'' y hy
    have h := hdy (fun l => (Fin.cons x₀ (Fin.cons (0 : ℝ) x'') : Fin (m + 2) → ℝ) (σ.symm l))
      y hy
    simp only [← perm_cons_cons_update_one] at h
    exact h
  · intro x₀ x''
    have h := hdy_int
      (fun l => (Fin.cons x₀ (Fin.cons (0 : ℝ) x'') : Fin (m + 2) → ℝ) (σ.symm l))
    simp only [← perm_cons_cons_update_one] at h
    exact h
  · intro x₀ x''
    have h := hdy_lim
      (fun l => (Fin.cons x₀ (Fin.cons (0 : ℝ) x'') : Fin (m + 2) → ℝ) (σ.symm l))
    simp only [← perm_cons_cons_update_one] at h
    exact h
  · intro x'' x hx
    have h := hdx
      (fun l => (Fin.cons (0 : ℝ) (Fin.cons (b (σ 1)) x'') : Fin (m + 2) → ℝ) (σ.symm l))
      (perm_cons_cons_apply_one σ 0 (b (σ 1)) x'') x hx
    simp only [← perm_cons_cons_update_zero] at h
    exact h
  · intro x''
    have h := hdx_int
      (fun l => (Fin.cons (0 : ℝ) (Fin.cons (b (σ 1)) x'') : Fin (m + 2) → ℝ) (σ.symm l))
      (perm_cons_cons_apply_one σ 0 (b (σ 1)) x'')
    simp only [← perm_cons_cons_update_zero] at h
    exact h
  · intro x''
    have h := hlim
      (fun l => (Fin.cons (0 : ℝ) (Fin.cons (b (σ 1)) x'') : Fin (m + 2) → ℝ) (σ.symm l))
      (perm_cons_cons_apply_one σ 0 (b (σ 1)) x'')
    simp only [← perm_cons_cons_update_zero] at h
    exact h

/-- **The mixed-derivative orthant integral for a given ordered pair `i ≠ j`.**  Some
permutation `σ` with `σ 0 = i` and `σ 1 = j` (`exists_perm_zero_one`) realises the identity of
`integral_Iic_mixed_deriv_pair`, here written with `j` and `i` in place of `σ 1` and `σ 0`:
`pxy = ∂_j ∂_i p` integrates over `{x ≤ b}` to the integral of `p` at the corner
`pairCorner σ b x''` over the orthant of the remaining coordinates. -/
theorem exists_perm_integral_Iic_mixed_deriv {m : ℕ} (i j : Fin (m + 2)) (hij : i ≠ j)
    (b : Fin (m + 2) → ℝ) (p px pxy : (Fin (m + 2) → ℝ) → ℝ)
    (hint : IntegrableOn pxy (Set.Iic b) volume)
    (hdy : ∀ y : Fin (m + 2) → ℝ, ∀ t ∈ Set.Iic (b j),
      HasDerivAt (fun s => px (Function.update y j s)) (pxy (Function.update y j t)) t)
    (hdy_int : ∀ y : Fin (m + 2) → ℝ,
      IntegrableOn (fun s => pxy (Function.update y j s)) (Set.Iic (b j)))
    (hdy_lim : ∀ y : Fin (m + 2) → ℝ,
      Filter.Tendsto (fun s => px (Function.update y j s)) Filter.atBot (nhds 0))
    (hdx : ∀ y : Fin (m + 2) → ℝ, y j = b j → ∀ t ∈ Set.Iic (b i),
      HasDerivAt (fun s => p (Function.update y i s)) (px (Function.update y i t)) t)
    (hdx_int : ∀ y : Fin (m + 2) → ℝ, y j = b j →
      IntegrableOn (fun s => px (Function.update y i s)) (Set.Iic (b i)))
    (hlim : ∀ y : Fin (m + 2) → ℝ, y j = b j →
      Filter.Tendsto (fun s => p (Function.update y i s)) Filter.atBot (nhds 0)) :
    ∃ σ : Equiv.Perm (Fin (m + 2)), σ 0 = i ∧ σ 1 = j ∧
      ∫ x in Set.Iic b, pxy x
        = ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)), p (pairCorner σ b x'') := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_zero_one i j hij
  subst h0 h1
  exact ⟨σ, rfl, rfl, integral_Iic_mixed_deriv_pair σ b p px pxy hint hdy hdy_int hdy_lim hdx
    hdx_int hlim⟩

end LatticeProb
