import Mathlib

/-!
# Regular classes of sets (Raic's (A1)-(A8)) and the class of rounded orthants

Packet P1 of the staged formalisation of Raic's Theorem 1.3 (A multivariate Berry-Esseen theorem
with explicit constants, arXiv:1802.06475), orthant case.  Pure real analysis on
`E = EuclideanSpace ℝ (Fin m)`; no probability and no Gaussian measure is used.

* `MvbeRegularClass m κ`: a class of sets with functions `ρ_A` satisfying (A1)-(A8); `mvbeLayer`
  is `A^{t|ρ}`; `mvbeGammaStarOf`, `mvbeGammaStar` are the generalised perimeter `γ*(A | ρ)`
  for an arbitrary measure `γ` (valued in `[0, ∞]`).
* `mvbeRho h`: the corner distance `‖(x - h)_+‖` (if some `x j > h j`) or `max_j (x j - h j)`
  (if `x ≤ h`); continuous, `LipschitzWith 1`, convex, coordinatewise nondecreasing
  (`mvbeCoordMono`).  The key tool is the dual representation `ρ_h(x) = max {⟨u, x - h⟩ : u ≥ 0,
  ‖u‖ = 1}` (`mvbeRho_ge_dual`, `mvbe_exists_rho_dual`).
* `mvbeOrthant h s = {ρ_h ≤ s}` (rounded orthant) and `mvbeSignedDist`, Raic's signed distance
  `δ_A`; `mvbeSignedDist_orthant` shows `δ_{O_{h,s}} = ρ_h - s = ρ_{h,s}` for `s ≥ 0`.
* `mvbeRoundedRegularClass m : MvbeRegularClass m 1`: the class `{O_{h,s} : h, s ≥ 0}` with
  `ρ_A = δ_A` satisfies (A1)-(A8) with `κ = 1`.
* `mvbeUnitGradAE_volume`: `ρ_h` is differentiable with `∑_j (∂_j ρ_h)² = 1` Lebesgue-a.e.
  (more generally for every measure absolutely continuous w.r.t. Lebesgue measure).

The ambient dimension is `m` with `[NeZero m]` (the maximum over `Fin m` needs `m ≥ 1`).
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal

namespace LatticeProb

section RegularClass

variable {m : ℕ}

/-- The layer `A^{t|ρ} = {x | ρ_A(x) ≤ t}` of a set `A` for a family `ρ` of functions
(`ρ A = ρ_A`). -/
def mvbeLayer (ρ : Set (EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m) → ℝ)
    (A : Set (EuclideanSpace ℝ (Fin m))) (t : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ρ A x ≤ t}

/-- **Regular classes of sets** in the sense of Raic, *A multivariate Berry-Esseen theorem with
explicit constants* (Bernoulli 25(4A), 2019, arXiv:1802.06475), p. 4.

A class `cls` of sets in `E = ℝ^m`, with a generalised signed distance `ρ_A = rho A : E → ℝ`
for each `A`, satisfies (A1)-(A8) with constant `κ`.  The paper's statements, verbatim:

* (A1) A is closed under translations and uniform scalings by factors greater than one.
* (A2) For each A ∈ A and t ∈ ℝ, `A^{t|ρ} ∈ A ∪ {∅, ℝ^d}`.
* (A3) For each A ∈ A and ε > 0, either `A^{-ε|ρ} = ∅` or `{x; ρ_{A^{-ε|ρ}}(x) < ε} ⊆ A`.
* (A4) For each A ∈ A, `ρ_A(x) ≤ 0` for all `x ∈ A` and `ρ_A(x) ≥ 0` for all `x ∉ A`.
* (A5) For each A ∈ A and each `y ∈ ℝ^d`, `ρ_{A+y}(x + y) = ρ_A(x)` for all `x ∈ ℝ^d`.
* (A6) For each A ∈ A and each `q ≥ 1`, `|ρ_{qA}(qx)| ≤ q |ρ_A(x)|` for all `x ∈ ℝ^d`.
* (A7) For each A ∈ A, `ρ_A` is non-expansive on `{x; ρ_A(x) ≥ 0}`, i.e.,
  `|ρ_A(x) - ρ_A(y)| ≤ |x - y|` for all `x, y` with `ρ_A(x) ≥ 0` and `ρ_A(y) ≥ 0`.
* (A8) For each A ∈ A, `ρ_A` is differentiable on `{x; ρ_A(x) > 0}`.  Moreover, there exists
  `κ ≥ 0`, such that `|∇ρ_A(x) - ∇ρ_A(y)| ≤ κ |x - y| / min{ρ_A(x), ρ_A(y)}` for all `x, y`
  with `ρ_A(x) > 0` and `ρ_A(y) > 0`.

Here `A^{t|ρ} := {x; ρ_A(x) ≤ t}` is `mvbeLayer rho A t`.

Formalisation choices.  `rho : Set E → E → ℝ` is a total function on sets (its values off `cls`
are junk and never used, except in (A3) when `A^{-ε|ρ} = univ`, which the paper also leaves
undefined).  `A + y` and `qA` are the images under `x ↦ x + y` and `x ↦ q • x`.  `∇` is Mathlib's
`gradient`.  The optional assumption (A1') of the paper is not part of the structure.  The
requirement `κ ≥ 0` of (A8) is the field `kappa_nonneg`.  Borel measurability of the members of
the class and of the functions `ρ_A` is added as in the feasibility report (Raic works with
"measurable" sets and functions). -/
structure MvbeRegularClass (m : ℕ) (κ : ℝ) where
  /-- the class `A` of sets -/
  cls : Set (Set (EuclideanSpace ℝ (Fin m)))
  /-- the generalised signed distances `A ↦ ρ_A` -/
  rho : Set (EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m) → ℝ
  kappa_nonneg : 0 ≤ κ
  measurableSet_mem : ∀ A ∈ cls, MeasurableSet A
  measurable_rho : ∀ A ∈ cls, Measurable (rho A)
  a1_translate : ∀ A ∈ cls, ∀ y : EuclideanSpace ℝ (Fin m), (fun x => x + y) '' A ∈ cls
  a1_scale : ∀ A ∈ cls, ∀ q : ℝ, 1 < q → (fun x => q • x) '' A ∈ cls
  a2 : ∀ A ∈ cls, ∀ t : ℝ, mvbeLayer rho A t ∈ cls ∪ {∅, Set.univ}
  a3 : ∀ A ∈ cls, ∀ ε : ℝ, 0 < ε →
    mvbeLayer rho A (-ε) = ∅ ∨ {x | rho (mvbeLayer rho A (-ε)) x < ε} ⊆ A
  a4_nonpos : ∀ A ∈ cls, ∀ x ∈ A, rho A x ≤ 0
  a4_nonneg : ∀ A ∈ cls, ∀ x ∉ A, 0 ≤ rho A x
  a5 : ∀ A ∈ cls, ∀ y x : EuclideanSpace ℝ (Fin m), rho ((fun z => z + y) '' A) (x + y) = rho A x
  a6 : ∀ A ∈ cls, ∀ q : ℝ, 1 ≤ q → ∀ x : EuclideanSpace ℝ (Fin m),
    |rho ((fun z => q • z) '' A) (q • x)| ≤ q * |rho A x|
  a7 : ∀ A ∈ cls, ∀ x y : EuclideanSpace ℝ (Fin m), 0 ≤ rho A x → 0 ≤ rho A y →
    |rho A x - rho A y| ≤ ‖x - y‖
  a8_differentiableAt : ∀ A ∈ cls, ∀ x : EuclideanSpace ℝ (Fin m), 0 < rho A x →
    DifferentiableAt ℝ (rho A) x
  a8_gradient_sub_le : ∀ A ∈ cls, ∀ x y : EuclideanSpace ℝ (Fin m), 0 < rho A x → 0 < rho A y →
    ‖gradient (rho A) x - gradient (rho A) y‖ ≤ κ * ‖x - y‖ / min (rho A x) (rho A y)

/-- Raic's generalised Gaussian perimeter of a single set, for an arbitrary measure `γ`:
`γ*(A | ρ) = sup_{ε > 0} max{γ(A^{ε|ρ} \ A), γ(A \ A^{-ε|ρ})} / ε`, valued in `[0, ∞]`. -/
noncomputable def mvbeGammaStarOf (γ : Measure (EuclideanSpace ℝ (Fin m)))
    (ρ : Set (EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m) → ℝ)
    (A : Set (EuclideanSpace ℝ (Fin m))) : ℝ≥0∞ :=
  ⨆ (ε : ℝ) (_ : 0 < ε),
    max (γ (mvbeLayer ρ A ε \ A)) (γ (A \ mvbeLayer ρ A (-ε))) / ENNReal.ofReal ε

/-- Raic's generalised Gaussian perimeter of a class: `γ*(A | ρ) = sup_{A ∈ A} γ*(A | ρ)`, for an
arbitrary measure `γ`, valued in `[0, ∞]`. -/
noncomputable def mvbeGammaStar (γ : Measure (EuclideanSpace ℝ (Fin m)))
    (cls : Set (Set (EuclideanSpace ℝ (Fin m))))
    (ρ : Set (EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m) → ℝ) : ℝ≥0∞ :=
  ⨆ A ∈ cls, mvbeGammaStarOf γ ρ A

/-- `γ*(A | ρ)` for a regular class. -/
noncomputable def MvbeRegularClass.gammaStar {κ : ℝ} (C : MvbeRegularClass m κ)
    (γ : Measure (EuclideanSpace ℝ (Fin m))) : ℝ≥0∞ :=
  mvbeGammaStar γ C.cls C.rho

theorem mvbe_max_div_le_gammaStar (γ : Measure (EuclideanSpace ℝ (Fin m)))
    (cls : Set (Set (EuclideanSpace ℝ (Fin m))))
    (ρ : Set (EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m) → ℝ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ cls) {ε : ℝ} (hε : 0 < ε) :
    max (γ (mvbeLayer ρ A ε \ A)) (γ (A \ mvbeLayer ρ A (-ε))) / ENNReal.ofReal ε
      ≤ mvbeGammaStar γ cls ρ :=
  le_iSup₂_of_le A hA (le_iSup₂_of_le ε hε le_rfl)

/-- The outer layer estimate `γ(A^{ε|ρ} \ A) ≤ ε γ*(A | ρ)`. -/
theorem mvbe_layer_diff_le (γ : Measure (EuclideanSpace ℝ (Fin m)))
    (cls : Set (Set (EuclideanSpace ℝ (Fin m))))
    (ρ : Set (EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m) → ℝ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ cls) {ε : ℝ} (hε : 0 < ε) :
    γ (mvbeLayer ρ A ε \ A) ≤ ENNReal.ofReal ε * mvbeGammaStar γ cls ρ := by
  have h := mvbe_max_div_le_gammaStar γ cls ρ hA hε
  rw [ENNReal.div_le_iff' (by simpa using hε) ENNReal.ofReal_ne_top] at h
  exact le_trans (le_max_left _ _) h

/-- The inner layer estimate `γ(A \ A^{-ε|ρ}) ≤ ε γ*(A | ρ)`. -/
theorem mvbe_diff_layer_le (γ : Measure (EuclideanSpace ℝ (Fin m)))
    (cls : Set (Set (EuclideanSpace ℝ (Fin m))))
    (ρ : Set (EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin m) → ℝ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ cls) {ε : ℝ} (hε : 0 < ε) :
    γ (A \ mvbeLayer ρ A (-ε)) ≤ ENNReal.ofReal ε * mvbeGammaStar γ cls ρ := by
  have h := mvbe_max_div_le_gammaStar γ cls ρ hA hε
  rw [ENNReal.div_le_iff' (by simpa using hε) ENNReal.ofReal_ne_top] at h
  exact le_trans (le_max_right _ _) h

end RegularClass

section Rho

variable {m : ℕ}

/-- The positive part vector `(x - h)_+`, coordinatewise `max (x j - h j) 0`, in `ℝ^m`. -/
noncomputable def mvbePos (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j => max (x j - h j) 0)

/-- The maximal coordinate `max_j (x j - h j)` (the index set `Fin m` is nonempty). -/
noncomputable def mvbeMaxCoord [NeZero m] (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => x j - h j)

open scoped Classical in
/-- The corner distance function of the orthant `{x ≤ h}`. -/
noncomputable def mvbeRho [NeZero m] (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  if ∃ j, h j < x j then ‖mvbePos h x‖ else mvbeMaxCoord h x

theorem mvbePos_apply (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    mvbePos h x j = max (x j - h j) 0 := by
  simp [mvbePos]

theorem mvbePos_norm_eq (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ‖mvbePos h x‖ = √(∑ j, (max (x j - h j) 0) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mvbePos_apply, Real.norm_eq_abs, sq_abs]

theorem mvbe_norm_eq_sqrt (x : EuclideanSpace ℝ (Fin m)) : ‖x‖ = √(∑ j, (x j) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

/-- Unit vectors with nonnegative coordinates. -/
def mvbeNonnegUnit (u : Fin m → ℝ) : Prop := (∀ j, 0 ≤ u j) ∧ ∑ j, u j ^ 2 = 1

theorem mvbeNonnegUnit.le_one {u : Fin m → ℝ} (hu : mvbeNonnegUnit u) (j : Fin m) :
    u j ≤ 1 := by
  have h1 : u j ^ 2 ≤ ∑ i, u i ^ 2 :=
    Finset.single_le_sum (f := fun i => u i ^ 2) (fun i _ => sq_nonneg (u i)) (Finset.mem_univ j)
  rw [hu.2] at h1
  nlinarith [hu.1 j]

theorem mvbeNonnegUnit.one_le_sum {u : Fin m → ℝ} (hu : mvbeNonnegUnit u) :
    1 ≤ ∑ j, u j := by
  calc (1 : ℝ) = ∑ j, u j ^ 2 := hu.2.symm
    _ ≤ ∑ j, u j := Finset.sum_le_sum fun j _ => by
        have := hu.1 j
        have := hu.le_one j
        nlinarith

theorem mvbeNonnegUnit_single [DecidableEq (Fin m)] (j : Fin m) :
    mvbeNonnegUnit (fun i : Fin m => if i = j then (1 : ℝ) else 0) := by
  refine ⟨fun i => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp

variable [NeZero m]

theorem mvbeRho_of_exists {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∃ j, h j < x j) : mvbeRho h x = √(∑ j, (max (x j - h j) 0) ^ 2) := by
  rw [mvbeRho, if_pos hx, mvbePos_norm_eq]

theorem mvbeRho_of_not_exists {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : ¬ ∃ j, h j < x j) : mvbeRho h x = mvbeMaxCoord h x := by
  rw [mvbeRho, if_neg hx]

theorem mvbe_le_maxCoord (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    x j - h j ≤ mvbeMaxCoord h x :=
  Finset.le_sup' (fun j => x j - h j) (Finset.mem_univ j)

theorem mvbeMaxCoord_le {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hr : ∀ j, x j - h j ≤ r) : mvbeMaxCoord h x ≤ r :=
  Finset.sup'_le _ _ fun j _ => hr j

theorem mvbe_exists_maxCoord_eq (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ∃ j, mvbeMaxCoord h x = x j - h j := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin m))
    (fun j => x j - h j)
  exact ⟨j, hj⟩

/-- Weak duality: `ρ_h(x) ≥ ⟨u, x - h⟩` for every nonnegative unit vector `u`. -/
theorem mvbeRho_ge_dual {u : Fin m → ℝ} (hu : mvbeNonnegUnit u) (h : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ∑ j, u j * (x j - h j) ≤ mvbeRho h x := by
  by_cases hx : ∃ j, h j < x j
  · rw [mvbeRho_of_exists hx]
    calc ∑ j, u j * (x j - h j) ≤ ∑ j, u j * max (x j - h j) 0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hu.1 j)
      _ ≤ √(∑ j, u j ^ 2) * √(∑ j, (max (x j - h j) 0) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = √(∑ j, (max (x j - h j) 0) ^ 2) := by rw [hu.2, Real.sqrt_one, one_mul]
  · rw [mvbeRho_of_not_exists hx]
    have hM : mvbeMaxCoord h x ≤ 0 := mvbeMaxCoord_le fun j => by
      have := not_exists.1 hx j
      linarith
    calc ∑ j, u j * (x j - h j) ≤ ∑ j, u j * mvbeMaxCoord h x :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (mvbe_le_maxCoord h x j) (hu.1 j)
      _ = (∑ j, u j) * mvbeMaxCoord h x := by rw [Finset.sum_mul]
      _ ≤ 1 * mvbeMaxCoord h x := by nlinarith [hu.one_le_sum]
      _ = mvbeMaxCoord h x := one_mul _

/-- Strong duality: the maximum in `mvbeRho_ge_dual` is attained. -/
theorem mvbe_exists_rho_dual (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ∃ u : Fin m → ℝ, mvbeNonnegUnit u ∧ ∑ j, u j * (x j - h j) = mvbeRho h x := by
  classical
  by_cases hx : ∃ j, h j < x j
  · set P : ℝ := √(∑ j, (max (x j - h j) 0) ^ 2) with hP
    have hS : 0 < ∑ j, (max (x j - h j) 0) ^ 2 := by
      obtain ⟨j, hj⟩ := hx
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => (max (x i - h i) 0) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j))
      have : 0 < max (x j - h j) 0 := lt_max_of_lt_left (by linarith)
      positivity
    have hPpos : 0 < P := Real.sqrt_pos.2 hS
    have hP2 : P ^ 2 = ∑ j, (max (x j - h j) 0) ^ 2 := Real.sq_sqrt hS.le
    refine ⟨fun j => max (x j - h j) 0 / P, ⟨fun j => by positivity, ?_⟩, ?_⟩
    · simp only [div_pow]
      rw [← Finset.sum_div, ← hP2]
      exact div_self (by positivity)
    · rw [mvbeRho_of_exists hx]
      have : ∀ j, max (x j - h j) 0 / P * (x j - h j) = (max (x j - h j) 0) ^ 2 / P := by
        intro j
        rcases le_total (x j - h j) 0 with hj | hj
        · rw [max_eq_right hj]; ring
        · rw [max_eq_left hj]; ring
      simp only [this]
      rw [← Finset.sum_div, ← hP2]
      field_simp
      exact (Real.sqrt_sq hPpos.le).symm
  · obtain ⟨j0, hj0⟩ := mvbe_exists_maxCoord_eq h x
    refine ⟨fun i : Fin m => if i = j0 then (1 : ℝ) else 0, mvbeNonnegUnit_single j0, ?_⟩
    rw [mvbeRho_of_not_exists hx, hj0]
    simp

theorem mvbeRho_ge_coord (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    x j - h j ≤ mvbeRho h x := by
  classical
  have := mvbeRho_ge_dual (mvbeNonnegUnit_single j) h x
  simpa using this

theorem mvbeRho_sub_le (h : Fin m → ℝ) (x y : EuclideanSpace ℝ (Fin m)) :
    mvbeRho h x - mvbeRho h y ≤ ‖x - y‖ := by
  obtain ⟨u, hu, hx⟩ := mvbe_exists_rho_dual h x
  have hy := mvbeRho_ge_dual hu h y
  have hcs : ∑ j, u j * (x j - y j) ≤ ‖x - y‖ := by
    calc _ ≤ √(∑ j, u j ^ 2) * √(∑ j, (x j - y j) ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = ‖x - y‖ := by
        rw [hu.2, Real.sqrt_one, one_mul, mvbe_norm_eq_sqrt]
        simp
  have : ∑ j, u j * (x j - h j) = ∑ j, u j * (y j - h j) + ∑ j, u j * (x j - y j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith

theorem mvbeRho_lipschitz (h : Fin m → ℝ) : LipschitzWith 1 (mvbeRho h) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, abs_sub_le_iff]
  exact ⟨mvbeRho_sub_le h x y, by rw [← norm_neg, neg_sub]; exact mvbeRho_sub_le h y x⟩

theorem mvbeRho_continuous (h : Fin m → ℝ) : Continuous (mvbeRho h) :=
  (mvbeRho_lipschitz h).continuous

theorem mvbeRho_convexOn (h : Fin m → ℝ) : ConvexOn ℝ Set.univ (mvbeRho h) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨u, hu, hz⟩ := mvbe_exists_rho_dual h (a • x + b • y)
  have hx := mvbeRho_ge_dual hu h x
  have hy := mvbeRho_ge_dual hu h y
  have hsum : ∑ j, u j * ((a • x + b • y) j - h j)
      = a * ∑ j, u j * (x j - h j) + b * ∑ j, u j * (y j - h j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hh : h j = a * h j + b * h j := by rw [← add_mul, hab, one_mul]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    conv_lhs => rw [hh]
    ring
  rw [smul_eq_mul, smul_eq_mul, ← hz, hsum]
  nlinarith

/-- Coordinatewise monotonicity of a function on `ℝ^m`: nondecreasing along each coordinate
direction. -/
def mvbeCoordMono (ρ : EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  ∀ (j : Fin m) (x : EuclideanSpace ℝ (Fin m)) (s t : ℝ), s ≤ t →
    ρ (x + s • EuclideanSpace.single j 1) ≤ ρ (x + t • EuclideanSpace.single j 1)

theorem mvbeRho_coordMono (h : Fin m → ℝ) : mvbeCoordMono (mvbeRho h) := by
  intro j x s t hst
  obtain ⟨u, hu, hs⟩ := mvbe_exists_rho_dual h (x + s • EuclideanSpace.single j 1)
  have ht := mvbeRho_ge_dual hu h (x + t • EuclideanSpace.single j 1)
  have key : ∀ c : ℝ, ∑ i, u i * ((x + c • EuclideanSpace.single j (1 : ℝ) :
        EuclideanSpace ℝ (Fin m)) i - h i) = ∑ i, u i * (x i - h i) + c * u j := by
    intro c
    simp [mul_add, Finset.sum_add_distrib, mul_sub]
    ring
  rw [key] at hs ht
  nlinarith [hu.1 j]

theorem mvbeRho_eq_of_sub_eq {h h' : Fin m → ℝ} {x x' : EuclideanSpace ℝ (Fin m)}
    (hz : ∀ j, x' j - h' j = x j - h j) : mvbeRho h' x' = mvbeRho h x := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu, he⟩ := mvbe_exists_rho_dual h' x'
    rw [← he]
    simpa [hz] using mvbeRho_ge_dual hu h x
  · obtain ⟨u, hu, he⟩ := mvbe_exists_rho_dual h x
    rw [← he]
    simpa [hz] using mvbeRho_ge_dual hu h' x'

theorem mvbeRho_translate (h : Fin m → ℝ) (x y : EuclideanSpace ℝ (Fin m)) :
    mvbeRho (fun j => h j + y j) (x + y) = mvbeRho h x :=
  mvbeRho_eq_of_sub_eq fun j => by simp

theorem mvbeRho_smul {q : ℝ} (hq : 0 < q) (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    mvbeRho (fun j => q * h j) (q • x) = q * mvbeRho h x := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu, he⟩ := mvbe_exists_rho_dual (fun j => q * h j) (q • x)
    rw [← he]
    have := mvbeRho_ge_dual hu h x
    calc ∑ j, u j * ((q • x) j - q * h j) = q * ∑ j, u j * (x j - h j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by simp only [PiLp.smul_apply, smul_eq_mul]; ring
      _ ≤ q * mvbeRho h x := mul_le_mul_of_nonneg_left this hq.le
  · obtain ⟨u, hu, he⟩ := mvbe_exists_rho_dual h x
    have := mvbeRho_ge_dual hu (fun j => q * h j) (q • x)
    have e : ∑ j, u j * ((q • x) j - q * h j) = q * ∑ j, u j * (x j - h j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, he] at this
    exact this

theorem mvbeRho_pos_iff (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    0 < mvbeRho h x ↔ ∃ j, h j < x j := by
  constructor
  · intro hx
    by_contra hne
    rw [mvbeRho_of_not_exists hne] at hx
    have : mvbeMaxCoord h x ≤ 0 := mvbeMaxCoord_le fun j => by
      have := not_exists.1 hne j
      linarith
    linarith
  · rintro ⟨j, hj⟩
    have := mvbeRho_ge_coord h x j
    linarith

theorem mvbeRho_le_iff_of_nonpos {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hr : r ≤ 0) : mvbeRho h x ≤ r ↔ ∀ j, x j ≤ h j + r := by
  constructor
  · intro hx j
    have := mvbeRho_ge_coord h x j
    linarith
  · intro hx
    have hne : ¬ ∃ j, h j < x j := by
      rintro ⟨j, hj⟩
      have := hx j
      linarith
    rw [mvbeRho_of_not_exists hne]
    exact mvbeMaxCoord_le fun j => by linarith [hx j]

theorem mvbeRho_self (h : Fin m → ℝ) : mvbeRho h (WithLp.toLp 2 h) = 0 := by
  refine le_antisymm ?_ ?_
  · rw [mvbeRho_le_iff_of_nonpos le_rfl]
    intro j; simp
  · obtain ⟨u, hu, he⟩ := mvbe_exists_rho_dual h (WithLp.toLp 2 h)
    have := mvbeRho_ge_dual hu h (WithLp.toLp 2 h)
    simpa using this

/-! ### Rounded orthants and their signed distance function -/

/-- The rounded orthant `O_{h,s} = {x | ρ_h(x) ≤ s}`.  For `s ≥ 0` it is the closed
`s`-neighbourhood of the orthant `{x ≤ h}`; for `s ≤ 0` it is the shifted orthant
`{x ≤ h + s}`. -/
def mvbeOrthant (h : Fin m → ℝ) (s : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | mvbeRho h x ≤ s}

/-- The function `ρ_{h,s} = ρ_h - s`. -/
noncomputable def mvbeRhoRound (h : Fin m → ℝ) (s : ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  mvbeRho h x - s

open scoped Classical in
/-- Raic's signed distance function `δ_A`: `-dist(x, Aᶜ)` on `A`, `dist(x, A)` off `A`. -/
noncomputable def mvbeSignedDist (A : Set (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  if x ∈ A then -Metric.infDist x Aᶜ else Metric.infDist x A

theorem mvbe_mem_orthant {h : Fin m → ℝ} {s : ℝ} {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ mvbeOrthant h s ↔ mvbeRho h x ≤ s := Iff.rfl

omit [NeZero m] in
theorem mvbe_norm_toLp {u : Fin m → ℝ} (hu : mvbeNonnegUnit u) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m))‖ = 1 := by
  rw [mvbe_norm_eq_sqrt]
  simp [hu.2]

theorem mvbe_infDist_compl_orthant {h : Fin m → ℝ} {s : ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : mvbeRho h x ≤ s) :
    Metric.infDist x (mvbeOrthant h s)ᶜ = s - mvbeRho h x := by
  obtain ⟨u, hu, he⟩ := mvbe_exists_rho_dual h x
  set v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 u with hv
  have hvn : ‖v‖ = 1 := mvbe_norm_toLp hu
  have hb : ∀ t : ℝ, s - mvbeRho h x < t →
      x + t • v ∈ (mvbeOrthant h s)ᶜ ∧ dist x (x + t • v) = t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    refine ⟨?_, ?_⟩
    · intro hmem
      have h1 := mvbeRho_ge_dual hu h (x + t • v)
      have h2 : ∑ j, u j * ((x + t • v) j - h j) = ∑ j, u j * (x j - h j) + t := by
        have : ∑ j, u j * ((x + t • v) j - h j)
            = ∑ j, u j * (x j - h j) + t * ∑ j, u j ^ 2 := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [hv]
          ring
        rw [this, hu.2, mul_one]
      have h3 : mvbeRho h (x + t • v) ≤ s := hmem
      linarith
    · rw [dist_eq_norm, show x - (x + t • v) = -(t • v) by abel, norm_neg, norm_smul, hvn,
        Real.norm_eq_abs, abs_of_pos ht0, mul_one]
  have hne : (mvbeOrthant h s)ᶜ.Nonempty :=
    ⟨_, (hb (s - mvbeRho h x + 1) (by linarith)).1⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨hm, hd⟩ := hb (s - mvbeRho h x + ε) (by linarith)
    calc Metric.infDist x (mvbeOrthant h s)ᶜ
        ≤ dist x (x + (s - mvbeRho h x + ε) • v) := Metric.infDist_le_dist_of_mem hm
      _ = s - mvbeRho h x + ε := hd
  · refine (Metric.le_infDist hne).2 fun b hb' => ?_
    have h1 : s < mvbeRho h b := by
      simpa [mvbeOrthant] using hb'
    have h2 := mvbeRho_sub_le h b x
    rw [dist_comm, dist_eq_norm]
    linarith

theorem mvbe_infDist_orthant {h : Fin m → ℝ} {s : ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hs : 0 ≤ s) (hx : s < mvbeRho h x) :
    Metric.infDist x (mvbeOrthant h s) = mvbeRho h x - s := by
  have hex : ∃ j, h j < x j := (mvbeRho_pos_iff h x).1 (by linarith)
  set P : ℝ := mvbeRho h x with hP
  have hPpos : 0 < P := by linarith
  have hPsq : P = √(∑ j, (max (x j - h j) 0) ^ 2) := mvbeRho_of_exists hex
  have hP2 : P ^ 2 = ∑ j, (max (x j - h j) 0) ^ 2 := by
    rw [hPsq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hmem0 : (WithLp.toLp 2 h : EuclideanSpace ℝ (Fin m)) ∈ mvbeOrthant h s := by
    rw [mvbe_mem_orthant, mvbeRho_self]; exact hs
  refine le_antisymm ?_ ?_
  · -- the nearest point
    set v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => max (x j - h j) 0 / P) with hv
    have hvn : ‖v‖ = 1 := by
      rw [mvbe_norm_eq_sqrt]
      simp only [hv, PiLp.toLp_apply, div_pow]
      rw [← Finset.sum_div, ← hP2, div_self (by positivity), Real.sqrt_one]
    set a : EuclideanSpace ℝ (Fin m) := x - (P - s) • v with ha
    have hpos : ∀ j, max (a j - h j) 0 = (s / P) * max (x j - h j) 0 := by
      intro j
      have haj : a j - h j = (x j - h j) - (P - s) * (max (x j - h j) 0 / P) := by
        simp [ha, hv]
        ring
      rcases le_total (x j - h j) 0 with hj | hj
      · rw [haj, max_eq_right hj]
        simp only [zero_div, mul_zero, sub_zero, mul_zero]
        exact max_eq_right hj
      · rw [haj, max_eq_left hj]
        have : (x j - h j) - (P - s) * ((x j - h j) / P) = (s / P) * (x j - h j) := by
          field_simp
          ring
        rw [this]
        exact max_eq_left (by positivity)
    have haA : a ∈ mvbeOrthant h s := by
      rw [mvbe_mem_orthant]
      by_cases hex' : ∃ j, h j < a j
      · rw [mvbeRho_of_exists hex']
        simp only [hpos, mul_pow]
        rw [← Finset.mul_sum, ← hP2, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
          Real.sqrt_sq hPpos.le]
        rw [div_mul_cancel₀ _ hPpos.ne']
      · rw [mvbeRho_of_not_exists hex']
        refine le_trans (mvbeMaxCoord_le fun j => ?_) hs
        have := not_exists.1 hex' j
        linarith
    have hda : dist x a = P - s := by
      rw [dist_eq_norm, ha, sub_sub_cancel, norm_smul, hvn, mul_one, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    calc Metric.infDist x (mvbeOrthant h s) ≤ dist x a := Metric.infDist_le_dist_of_mem haA
      _ = P - s := hda
  · refine (Metric.le_infDist ⟨_, hmem0⟩).2 fun a ha => ?_
    have h1 := mvbeRho_sub_le h x a
    have h2 : mvbeRho h a ≤ s := ha
    rw [dist_eq_norm]
    linarith

theorem mvbeSignedDist_orthant {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin m)) : mvbeSignedDist (mvbeOrthant h s) x = mvbeRho h x - s := by
  unfold mvbeSignedDist
  by_cases hx : x ∈ mvbeOrthant h s
  · rw [if_pos hx, mvbe_infDist_compl_orthant hx]; ring
  · rw [if_neg hx]
    exact mvbe_infDist_orthant hs (not_le.1 hx)

/-- For `x ≤ h` (no coordinate above `h`) and `s ≥ 0`:
`dist(x, O_{h,s}ᶜ) = s + min_j (h_j - x_j) = s - max_j (x_j - h_j)`. -/
theorem mvbe_infDist_compl_orthant_of_le {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s)
    {x : EuclideanSpace ℝ (Fin m)} (hx : ∀ j, x j ≤ h j) :
    Metric.infDist x (mvbeOrthant h s)ᶜ = s - mvbeMaxCoord h x := by
  have hne : ¬ ∃ j, h j < x j := by
    rintro ⟨j, hj⟩
    exact absurd (hx j) (not_le.2 hj)
  have hM : mvbeMaxCoord h x ≤ 0 := mvbeMaxCoord_le fun j => by linarith [hx j]
  rw [mvbe_infDist_compl_orthant (by rw [mvbeRho_of_not_exists hne]; linarith),
    mvbeRho_of_not_exists hne]

/-! ### The gradient of `ρ_h` where some coordinate exceeds `h` -/

omit [NeZero m] in

theorem mvbe_hasDerivAt_sq_max (t : ℝ) :
    HasDerivAt (fun r : ℝ => (max r 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
    have h2 : (fun r : ℝ => (max r 0) ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with r hr
      simp [max_eq_right (le_of_lt (show r < 0 from hr))]
    rw [max_eq_right ht.le, mul_zero]
    exact this.congr_of_eventuallyEq h2
  · subst ht
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have h1 : (fun r : ℝ => (max (0 + r) 0) ^ 2 - (max 0 0) ^ 2 - r • (2 * max 0 0))
        =O[𝓝 0] fun r : ℝ => r ^ 2 := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun r => ?_)
      simp only [zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, sub_zero, mul_zero, smul_zero, Real.norm_eq_abs, one_mul]
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      rcases le_total r 0 with hr | hr
      · rw [max_eq_right hr]; simp [sq_nonneg]
      · rw [max_eq_left hr]
    exact h1.trans_isLittleO (isLittleO_pow_id (by norm_num))
  · have : HasDerivAt (fun r : ℝ => r ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : (fun r : ℝ => r ^ 2) =ᶠ[𝓝 t] fun r : ℝ => (max r 0) ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with r hr
      simp [max_eq_left (le_of_lt (show 0 < r from hr))]
    rw [max_eq_left ht.le]
    exact this.congr_of_eventuallyEq h2.symm

/-- The gradient `(x - h)_+ / ρ_h(x)` of `ρ_h` on `{ρ_h > 0}`. -/
noncomputable def mvbeGrad (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j => max (x j - h j) 0 / mvbeRho h x)

theorem mvbe_hasGradientAt_rho {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∃ j, h j < x j) : HasGradientAt (mvbeRho h) (mvbeGrad h x) x := by
  classical
  have hj : ∀ j, HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => (max (y j - h j) 0) ^ 2)
      ((2 * max (x j - h j) 0) • (EuclideanSpace.proj j : StrongDual ℝ _)) x := by
    intro j
    have h1 : HasDerivAt (fun r : ℝ => (max (r - h j) 0) ^ 2) (2 * max (x j - h j) 0) (x j) :=
      HasDerivAt.comp_sub_const (f := fun r : ℝ => (max r 0) ^ 2) (x j) (h j)
        (mvbe_hasDerivAt_sq_max (x j - h j))
    exact h1.comp_hasFDerivAt x (EuclideanSpace.proj j : StrongDual ℝ _).hasFDerivAt
  have hΦ := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
  have hSpos : 0 < ∑ j, (max (x j - h j) 0) ^ 2 := by
    obtain ⟨j, hj'⟩ := hx
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => (max (x i - h i) 0) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    have : 0 < max (x j - h j) 0 := lt_max_of_lt_left (by linarith)
    positivity
  have hsq := hΦ.sqrt hSpos.ne'
  have hev : (mvbeRho h) =ᶠ[𝓝 x]
      fun y => √(∑ j, (max (y j - h j) 0) ^ 2) := by
    obtain ⟨j, hj'⟩ := hx
    have hop : IsOpen {y : EuclideanSpace ℝ (Fin m) | h j < y j} :=
      isOpen_lt continuous_const ((EuclideanSpace.proj j : StrongDual ℝ _).continuous)
    filter_upwards [hop.mem_nhds hj'] with y hy
    exact mvbeRho_of_exists ⟨j, hy⟩
  have hρ := hsq.congr_of_eventuallyEq hev
  have hP : mvbeRho h x = √(∑ j, (max (x j - h j) 0) ^ 2) := mvbeRho_of_exists hx
  have hgrad : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m)) (mvbeGrad h x)
      = (1 / (2 * √(∑ i, (max (x i - h i) 0) ^ 2))) •
        ∑ i, (2 * max (x i - h i) 0) • (EuclideanSpace.proj i : StrongDual ℝ _) := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [InnerProductSpace.toDual_apply_apply]
    have hPpos : 0 < √(∑ j, (max (x j - h j) 0) ^ 2) := Real.sqrt_pos.2 hSpos
    simp only [mvbeGrad, PiLp.inner_apply, hP, smul_apply, sum_apply, EuclideanSpace.coe_proj,
      smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hasGradientAt_iff_hasFDerivAt, hgrad]
  exact hρ

theorem mvbeGrad_apply (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    mvbeGrad h x j = max (x j - h j) 0 / mvbeRho h x := by
  simp [mvbeGrad]

theorem mvbeRho_sq_of_exists {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∃ j, h j < x j) : mvbeRho h x ^ 2 = ∑ j, (max (x j - h j) 0) ^ 2 := by
  rw [mvbeRho_of_exists hx]
  exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- The Raic-(A8) estimate for the gradient `(x - h)_+ / ρ_h`:
`ρ_h(x) ρ_h(y) |∇ρ(x) - ∇ρ(y)|² ≤ |x - y|²`. -/
theorem mvbeGrad_sub_sq_le {h : Fin m → ℝ} {x y : EuclideanSpace ℝ (Fin m)}
    (hx : ∃ j, h j < x j) (hy : ∃ j, h j < y j) :
    mvbeRho h x * mvbeRho h y * ‖mvbeGrad h x - mvbeGrad h y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  set a := mvbeRho h x with ha
  set b := mvbeRho h y with hb
  have hapos : 0 < a := (mvbeRho_pos_iff h x).2 hx
  have hbpos : 0 < b := (mvbeRho_pos_iff h y).2 hy
  set p : Fin m → ℝ := fun j => max (x j - h j) 0 with hp
  set q : Fin m → ℝ := fun j => max (y j - h j) 0 with hq
  have hpa : ∑ j, p j ^ 2 = a ^ 2 := (mvbeRho_sq_of_exists hx).symm
  have hqb : ∑ j, q j ^ 2 = b ^ 2 := (mvbeRho_sq_of_exists hy).symm
  have hnorm : ‖mvbeGrad h x - mvbeGrad h y‖ ^ 2 = ∑ j, (p j / a - q j / b) ^ 2 := by
    rw [mvbe_norm_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mvbeGrad_apply, hp, hq, ha, hb]
  have key : a * b * ∑ j, (p j / a - q j / b) ^ 2 = 2 * a * b - 2 * ∑ j, p j * q j := by
    have : ∀ j, a * b * (p j / a - q j / b) ^ 2
        = (b / a) * p j ^ 2 + (a / b) * q j ^ 2 - 2 * (p j * q j) := by
      intro j
      field_simp
      ring
    rw [Finset.mul_sum]
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hpa, hqb]
    field_simp
    ring
  have h2 : ∑ j, (p j - q j) ^ 2 = a ^ 2 + b ^ 2 - 2 * ∑ j, p j * q j := by
    have : ∀ j, (p j - q j) ^ 2 = p j ^ 2 + q j ^ 2 - 2 * (p j * q j) := fun j => by ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hpa, hqb]
  have h3 : ∑ j, (p j - q j) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [mvbe_norm_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    refine Finset.sum_le_sum fun j _ => ?_
    have := abs_max_sub_max_le_abs (x j - h j) (y j - h j) 0
    have h4 : |x j - h j - (y j - h j)| = |(x - y) j| := by simp
    rw [h4] at this
    exact sq_le_sq.2 (by simpa [hp, hq] using this)
  rw [hnorm]
  nlinarith [sq_nonneg (a - b)]

theorem mvbeGrad_sub_norm_le {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) {x y : EuclideanSpace ℝ (Fin m)}
    (hx : s < mvbeRho h x) (hy : s < mvbeRho h y) :
    ‖mvbeGrad h x - mvbeGrad h y‖
      ≤ 1 * ‖x - y‖ / min (mvbeRho h x - s) (mvbeRho h y - s) := by
  have hex : ∃ j, h j < x j := (mvbeRho_pos_iff h x).1 (by linarith)
  have hey : ∃ j, h j < y j := (mvbeRho_pos_iff h y).1 (by linarith)
  have hk := mvbeGrad_sub_sq_le hex hey
  set μ := min (mvbeRho h x - s) (mvbeRho h y - s) with hμ
  have hμpos : 0 < μ := lt_min (by linarith) (by linarith)
  have hμa : μ ≤ mvbeRho h x := (min_le_left _ _).trans (by linarith)
  have hμb : μ ≤ mvbeRho h y := (min_le_right _ _).trans (by linarith)
  have hμab : μ * μ ≤ mvbeRho h x * mvbeRho h y :=
    mul_le_mul hμa hμb hμpos.le (by linarith)
  rw [one_mul, le_div_iff₀ hμpos]
  have hsq : (‖mvbeGrad h x - mvbeGrad h y‖ * μ) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    calc (‖mvbeGrad h x - mvbeGrad h y‖ * μ) ^ 2
        = (μ * μ) * ‖mvbeGrad h x - mvbeGrad h y‖ ^ 2 := by ring
      _ ≤ (mvbeRho h x * mvbeRho h y) * ‖mvbeGrad h x - mvbeGrad h y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hμab (sq_nonneg _)
      _ ≤ ‖x - y‖ ^ 2 := hk
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hμpos.le) (norm_nonneg _)).1 hsq

/-! ### The class of rounded orthants is a regular class with `κ = 1` -/

theorem mvbeSignedDist_orthant_eq {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    mvbeSignedDist (mvbeOrthant h s) = fun x => mvbeRho h x - s :=
  funext (mvbeSignedDist_orthant hs)

/-- The class `{O_{h,s} : h ∈ ℝ^m, s ≥ 0}` of rounded orthants. -/
def mvbeRoundedClass (m : ℕ) [NeZero m] : Set (Set (EuclideanSpace ℝ (Fin m))) :=
  {A | ∃ (h : Fin m → ℝ) (s : ℝ), 0 ≤ s ∧ A = mvbeOrthant h s}

theorem mvbeOrthant_mem_roundedClass {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    mvbeOrthant h s ∈ mvbeRoundedClass m :=
  ⟨h, s, hs, rfl⟩

theorem mvbeOrthant_isClosed (h : Fin m → ℝ) (s : ℝ) : IsClosed (mvbeOrthant h s) :=
  isClosed_le (mvbeRho_continuous h) continuous_const

/-- For `r ≤ 0` the rounded orthant `O_{h,r}` is the shifted orthant `{x ≤ h + r}`. -/
theorem mvbeOrthant_of_nonpos {h : Fin m → ℝ} {r : ℝ} (hr : r ≤ 0) :
    mvbeOrthant h r = mvbeOrthant (fun j => h j + r) 0 := by
  ext x
  rw [mvbe_mem_orthant, mvbe_mem_orthant, mvbeRho_le_iff_of_nonpos hr,
    mvbeRho_le_iff_of_nonpos le_rfl]
  simp

/-- Shifting a corner by `d ≤ 0` raises `ρ` by at least `-d`. -/
theorem mvbeRho_shift_ge {d : ℝ} (hd : d ≤ 0) (h : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    mvbeRho h x - d ≤ mvbeRho (fun j => h j + d) x := by
  obtain ⟨u, hu, he⟩ := mvbe_exists_rho_dual h x
  have := mvbeRho_ge_dual hu (fun j => h j + d) x
  have e : ∑ j, u j * (x j - (h j + d)) = ∑ j, u j * (x j - h j) - d * ∑ j, u j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, he] at this
  nlinarith [hu.one_le_sum]

theorem mvbeOrthant_image_add (h : Fin m → ℝ) (s : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    (fun x => x + y) '' mvbeOrthant h s = mvbeOrthant (fun j => h j + y j) s := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mvbe_mem_orthant, mvbeRho_translate]
    exact hx
  · intro hz
    refine ⟨z - y, ?_, sub_add_cancel z y⟩
    rw [mvbe_mem_orthant]
    have := mvbeRho_translate h (z - y) y
    rw [sub_add_cancel] at this
    rw [← this]
    exact hz

theorem mvbeOrthant_image_smul {q : ℝ} (hq : 0 < q) (h : Fin m → ℝ) (s : ℝ) :
    (fun x => q • x) '' mvbeOrthant h s = mvbeOrthant (fun j => q * h j) (q * s) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mvbe_mem_orthant, mvbeRho_smul hq]
    exact mul_le_mul_of_nonneg_left hx hq.le
  · intro hz
    refine ⟨q⁻¹ • z, ?_, by
      show q • q⁻¹ • z = z
      rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul]⟩
    rw [mvbe_mem_orthant]
    have h1 := mvbeRho_smul hq h (q⁻¹ • z)
    rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul] at h1
    have h2 : mvbeRho (fun j => q * h j) z ≤ q * s := hz
    rw [h1] at h2
    exact le_of_mul_le_mul_left h2 hq

theorem mvbeLayer_orthant {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    mvbeLayer mvbeSignedDist (mvbeOrthant h s) t = mvbeOrthant h (s + t) := by
  ext x
  simp only [mvbeLayer, Set.mem_setOf_eq, mvbe_mem_orthant, mvbeSignedDist_orthant hs]
  constructor <;> intro hx <;> linarith

theorem mvbeRounded_a2 {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    mvbeLayer mvbeSignedDist (mvbeOrthant h s) t ∈ mvbeRoundedClass m ∪ {∅, Set.univ} := by
  rw [mvbeLayer_orthant hs]
  left
  by_cases hst : 0 ≤ s + t
  · exact mvbeOrthant_mem_roundedClass hst
  · rw [mvbeOrthant_of_nonpos (not_le.1 hst).le]
    exact mvbeOrthant_mem_roundedClass le_rfl

theorem mvbeRounded_a3 {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) {ε : ℝ} (_hε : 0 < ε) :
    mvbeLayer mvbeSignedDist (mvbeOrthant h s) (-ε) = ∅ ∨
      {x | mvbeSignedDist (mvbeLayer mvbeSignedDist (mvbeOrthant h s) (-ε)) x < ε}
        ⊆ mvbeOrthant h s := by
  right
  rw [mvbeLayer_orthant hs]
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  rw [mvbe_mem_orthant]
  by_cases hsε : 0 ≤ s + -ε
  · rw [mvbeSignedDist_orthant hsε] at hx
    linarith
  · have hneg : s + -ε ≤ 0 := (not_le.1 hsε).le
    rw [mvbeOrthant_of_nonpos hneg, mvbeSignedDist_orthant le_rfl] at hx
    have := mvbeRho_shift_ge hneg h x
    linarith

theorem mvbeRounded_a5 {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) (y x : EuclideanSpace ℝ (Fin m)) :
    mvbeSignedDist ((fun z => z + y) '' mvbeOrthant h s) (x + y)
      = mvbeSignedDist (mvbeOrthant h s) x := by
  rw [mvbeOrthant_image_add, mvbeSignedDist_orthant hs, mvbeSignedDist_orthant hs,
    mvbeRho_translate]

theorem mvbeRounded_a6 {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) {q : ℝ} (hq : 1 ≤ q)
    (x : EuclideanSpace ℝ (Fin m)) :
    |mvbeSignedDist ((fun z => q • z) '' mvbeOrthant h s) (q • x)|
      ≤ q * |mvbeSignedDist (mvbeOrthant h s) x| := by
  have hq0 : 0 < q := by linarith
  rw [mvbeOrthant_image_smul hq0, mvbeSignedDist_orthant (mul_nonneg hq0.le hs),
    mvbeSignedDist_orthant hs, mvbeRho_smul hq0, ← mul_sub, abs_mul, abs_of_pos hq0]

theorem mvbeRounded_a7 {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) (x y : EuclideanSpace ℝ (Fin m)) :
    |mvbeSignedDist (mvbeOrthant h s) x - mvbeSignedDist (mvbeOrthant h s) y| ≤ ‖x - y‖ := by
  rw [mvbeSignedDist_orthant hs, mvbeSignedDist_orthant hs, sub_sub_sub_cancel_right,
    abs_sub_le_iff]
  exact ⟨mvbeRho_sub_le h x y, by rw [← norm_neg, neg_sub]; exact mvbeRho_sub_le h y x⟩

theorem mvbe_hasGradientAt_rho_sub {h : Fin m → ℝ} {s : ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∃ j, h j < x j) :
    HasGradientAt (fun y => mvbeRho h y - s) (mvbeGrad h x) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  exact (mvbe_hasGradientAt_rho hx).sub_const s

/-- **The class of rounded orthants `{O_{h,s} : h, s ≥ 0}`, with `ρ_A = δ_A` the signed distance
function, satisfies Raic's (A1)-(A8) with `κ = 1`.**  On `O_{h,s}` the function `ρ_A` is
`ρ_{h,s} = ρ_h - s` (`mvbeSignedDist_orthant`). -/
noncomputable def mvbeRoundedRegularClass (m : ℕ) [NeZero m] : MvbeRegularClass m 1 where
  cls := mvbeRoundedClass m
  rho := mvbeSignedDist
  kappa_nonneg := zero_le_one
  measurableSet_mem := by
    rintro A ⟨h, s, hs, rfl⟩
    exact (mvbeOrthant_isClosed h s).measurableSet
  measurable_rho := by
    rintro A ⟨h, s, hs, rfl⟩
    rw [mvbeSignedDist_orthant_eq hs]
    exact ((mvbeRho_continuous h).sub continuous_const).measurable
  a1_translate := by
    rintro A ⟨h, s, hs, rfl⟩ y
    rw [mvbeOrthant_image_add]
    exact mvbeOrthant_mem_roundedClass hs
  a1_scale := by
    rintro A ⟨h, s, hs, rfl⟩ q hq
    have hq0 : 0 < q := by linarith
    rw [mvbeOrthant_image_smul hq0]
    exact mvbeOrthant_mem_roundedClass (mul_nonneg hq0.le hs)
  a2 := by
    rintro A ⟨h, s, hs, rfl⟩ t
    exact mvbeRounded_a2 hs t
  a3 := by
    rintro A ⟨h, s, hs, rfl⟩ ε hε
    exact mvbeRounded_a3 hs hε
  a4_nonpos := by
    rintro A ⟨h, s, hs, rfl⟩ x hx
    rw [mvbeSignedDist_orthant hs]
    exact sub_nonpos.2 hx
  a4_nonneg := by
    rintro A ⟨h, s, hs, rfl⟩ x hx
    rw [mvbeSignedDist_orthant hs]
    exact sub_nonneg.2 (not_le.1 hx).le
  a5 := by
    rintro A ⟨h, s, hs, rfl⟩ y x
    exact mvbeRounded_a5 hs y x
  a6 := by
    rintro A ⟨h, s, hs, rfl⟩ q hq x
    exact mvbeRounded_a6 hs hq x
  a7 := by
    rintro A ⟨h, s, hs, rfl⟩ x y _ _
    exact mvbeRounded_a7 hs x y
  a8_differentiableAt := by
    rintro A ⟨h, s, hs, rfl⟩ x hx
    rw [mvbeSignedDist_orthant hs] at hx
    have hex : ∃ j, h j < x j := (mvbeRho_pos_iff h x).1 (by linarith)
    rw [mvbeSignedDist_orthant_eq hs]
    exact (mvbe_hasGradientAt_rho_sub (s := s) hex).differentiableAt
  a8_gradient_sub_le := by
    rintro A ⟨h, s, hs, rfl⟩ x y hx hy
    rw [mvbeSignedDist_orthant hs] at hx hy
    have hex : ∃ j, h j < x j := (mvbeRho_pos_iff h x).1 (by linarith)
    have hey : ∃ j, h j < y j := (mvbeRho_pos_iff h y).1 (by linarith)
    have hgx : gradient (mvbeSignedDist (mvbeOrthant h s)) x = mvbeGrad h x := by
      rw [mvbeSignedDist_orthant_eq hs]
      exact (mvbe_hasGradientAt_rho_sub (s := s) hex).gradient
    have hgy : gradient (mvbeSignedDist (mvbeOrthant h s)) y = mvbeGrad h y := by
      rw [mvbeSignedDist_orthant_eq hs]
      exact (mvbe_hasGradientAt_rho_sub (s := s) hey).gradient
    rw [hgx, hgy, mvbeSignedDist_orthant hs x, mvbeSignedDist_orthant hs y]
    exact mvbeGrad_sub_norm_le hs (by linarith) (by linarith)

/-- The members of the regular class `mvbeRoundedRegularClass` carry `ρ_{h,s} = ρ_h - s`. -/
theorem mvbeRoundedRegularClass_rho {h : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin m)) :
    (mvbeRoundedRegularClass m).rho (mvbeOrthant h s) x = mvbeRhoRound h s x :=
  mvbeSignedDist_orthant hs x

/-! ### The gradient of `ρ_h` has unit length almost everywhere -/

/-- Almost everywhere, `ρ` is differentiable with a gradient of Euclidean norm one:
`∑_j (∂_j ρ)² = 1` for `μ`-a.e. `x`. -/
def mvbeUnitGradAE (ρ : EuclideanSpace ℝ (Fin m) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∀ᵐ x ∂μ, DifferentiableAt ℝ ρ x ∧
    ∑ j, (fderiv ℝ ρ x (EuclideanSpace.single j 1)) ^ 2 = 1

/-- Near a point with a strictly dominant coordinate `j0 ≤ 0`, `ρ_h(y) = y j0 - h j0`. -/
theorem mvbeRho_eq_coord_of_dominant {h : Fin m → ℝ} {y : EuclideanSpace ℝ (Fin m)} {j0 : Fin m}
    (hU : ∀ k, k ≠ j0 → y k - h k < 0 ∧ y k - h k < y j0 - h j0) :
    mvbeRho h y = y j0 - h j0 := by
  classical
  by_cases hex : ∃ j, h j < y j
  · obtain ⟨j, hj⟩ := hex
    have hjj : j = j0 := by
      by_contra hne
      have := (hU j hne).1
      linarith
    subst hjj
    have hpos : 0 < y j - h j := by linarith
    have hsum : ∑ k, (max (y k - h k) 0) ^ 2 = (y j - h j) ^ 2 := by
      rw [Finset.sum_eq_single j]
      · rw [max_eq_left hpos.le]
      · intro k _ hk
        rw [max_eq_right (hU k hk).1.le]
        norm_num
      · intro hj'; exact absurd (Finset.mem_univ j) hj'
    rw [mvbeRho_of_exists ⟨j, hj⟩, hsum, Real.sqrt_sq hpos.le]
  · rw [mvbeRho_of_not_exists hex]
    refine le_antisymm (mvbeMaxCoord_le fun k => ?_) (mvbe_le_maxCoord h y j0)
    by_cases hk : k = j0
    · rw [hk]
    · exact (hU k hk).2.le

theorem mvbeUnitGrad_of_exists {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∃ j, h j < x j) :
    DifferentiableAt ℝ (mvbeRho h) x ∧
      ∑ j, (fderiv ℝ (mvbeRho h) x (EuclideanSpace.single j 1)) ^ 2 = 1 := by
  classical
  have hg := mvbe_hasGradientAt_rho hx
  refine ⟨hg.differentiableAt, ?_⟩
  have hP : 0 < mvbeRho h x := (mvbeRho_pos_iff h x).2 hx
  have hP2 := mvbeRho_sq_of_exists hx
  have e : ∀ j, fderiv ℝ (mvbeRho h) x (EuclideanSpace.single j 1)
      = max (x j - h j) 0 / mvbeRho h x := by
    intro j
    rw [hg.fderiv_apply, EuclideanSpace.inner_single_right]
    simp [mvbeGrad_apply]
  simp_rw [e, div_pow]
  rw [← Finset.sum_div, ← hP2]
  exact div_self (by positivity)

theorem mvbeUnitGrad_of_distinct {h : Fin m → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∀ i j, i ≠ j → x i - h i ≠ x j - h j) :
    DifferentiableAt ℝ (mvbeRho h) x ∧
      ∑ j, (fderiv ℝ (mvbeRho h) x (EuclideanSpace.single j 1)) ^ 2 = 1 := by
  classical
  by_cases hex : ∃ j, h j < x j
  · exact mvbeUnitGrad_of_exists hex
  · obtain ⟨j0, hj0⟩ := mvbe_exists_maxCoord_eq h x
    have hnon : ∀ k, x k - h k ≤ 0 := fun k => by
      have := not_exists.1 hex k
      linarith
    have hlt : ∀ k, k ≠ j0 → x k - h k < x j0 - h j0 := by
      intro k hk
      have h1 : x k - h k ≤ x j0 - h j0 := hj0 ▸ mvbe_le_maxCoord h x k
      exact lt_of_le_of_ne h1 (hx k j0 hk)
    have hcont : ∀ k, Continuous fun y : EuclideanSpace ℝ (Fin m) => y k :=
      fun k => (EuclideanSpace.proj k : StrongDual ℝ (EuclideanSpace ℝ (Fin m))).continuous
    have hev : ∀ᶠ y in nhds x, ∀ k, k ≠ j0 → y k - h k < 0 ∧ y k - h k < y j0 - h j0 := by
      refine Filter.eventually_all.2 fun k => ?_
      by_cases hk : k = j0
      · exact Filter.Eventually.of_forall fun y hk' => absurd hk hk'
      · have hk0 : x k - h k < 0 := lt_of_lt_of_le (hlt k hk) (hnon j0)
        have c1 : Continuous fun y : EuclideanSpace ℝ (Fin m) => y k - h k :=
          (hcont k).sub continuous_const
        have c2 : Continuous fun y : EuclideanSpace ℝ (Fin m) => y j0 - h j0 :=
          (hcont j0).sub continuous_const
        have e1 : ∀ᶠ y in nhds x, y k - h k < 0 :=
          c1.continuousAt.eventually_lt continuousAt_const hk0
        have e2 : ∀ᶠ y in nhds x, y k - h k < y j0 - h j0 :=
          c1.continuousAt.eventually_lt c2.continuousAt (hlt k hk)
        filter_upwards [e1, e2] with y h1 h2 _ using ⟨h1, h2⟩
    have hloc : (fun y : EuclideanSpace ℝ (Fin m) => y j0 - h j0) =ᶠ[nhds x] mvbeRho h := by
      filter_upwards [hev] with y hy using (mvbeRho_eq_coord_of_dominant hy).symm
    have hd : HasFDerivAt (mvbeRho h)
        (EuclideanSpace.proj j0 : StrongDual ℝ (EuclideanSpace ℝ (Fin m))) x := by
      have := ((EuclideanSpace.proj j0 : StrongDual ℝ (EuclideanSpace ℝ (Fin m))).hasFDerivAt
        (x := x)).sub_const (h j0)
      exact this.congr_of_eventuallyEq hloc.symm
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.fderiv]
    simp [Finset.sum_ite_eq]

omit [NeZero m] in
/-- A hyperplane `{x | x i - x j = c}` (`i ≠ j`) is Lebesgue-null. -/
theorem mvbe_volume_hyperplane_null {i j : Fin m} (hij : i ≠ j) (c : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin m))) {x | x i - x j = c} = 0 := by
  classical
  set f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin m))).toLinearMap
      - (EuclideanSpace.proj j : StrongDual ℝ (EuclideanSpace ℝ (Fin m))).toLinearMap with hf
  have hK : LinearMap.ker f ≠ ⊤ := by
    intro htop
    have hmem : (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin m))
        ∈ LinearMap.ker f := by
      rw [htop]; trivial
    rw [LinearMap.mem_ker] at hmem
    simp [hf, hij.symm] at hmem
  set p : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i c with hp
  have hset : {x : EuclideanSpace ℝ (Fin m) | x i - x j = c}
      = (fun x => x + (-p)) ⁻¹' (LinearMap.ker f : Set (EuclideanSpace ℝ (Fin m))) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, hf,
      LinearMap.sub_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.coe_proj, PiLp.add_apply,
      PiLp.neg_apply, hp]
    simp [hij.symm]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ hK

omit [NeZero m] in
/-- The tie set: `{x | ∃ i ≠ j, x i - h i = x j - h j}` is Lebesgue-null. -/
theorem mvbe_volume_ties_null (h : Fin m → ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin m)))
      {x | ∃ i j, i ≠ j ∧ x i - h i = x j - h j} = 0 := by
  have : {x : EuclideanSpace ℝ (Fin m) | ∃ i j, i ≠ j ∧ x i - h i = x j - h j}
      = ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {x | x i - x j = h i - h j} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, j, hij, hx⟩
      exact ⟨i, j, hij, by linarith⟩
    · rintro ⟨i, j, hij, hx⟩
      exact ⟨i, j, hij, by linarith⟩
  rw [this]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  exact mvbe_volume_hyperplane_null hij _

/-- **`ρ_h` is a.e. differentiable with a unit-length gradient, with respect to any measure that
is absolutely continuous with respect to Lebesgue measure.** -/
theorem mvbeUnitGradAE_of_ac (h : Fin m → ℝ) {μ : Measure (EuclideanSpace ℝ (Fin m))}
    (hμ : μ ≪ volume) : mvbeUnitGradAE (mvbeRho h) μ := by
  have hnull : μ {x | ∃ i j, i ≠ j ∧ x i - h i = x j - h j} = 0 :=
    hμ (mvbe_volume_ties_null h)
  rw [mvbeUnitGradAE, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  by_contra hcon
  apply hx
  refine mvbeUnitGrad_of_distinct fun i j hij hxe => hcon ⟨i, j, hij, hxe⟩

/-- **`ρ_h` has a unit-length gradient Lebesgue-almost everywhere.** -/
theorem mvbeUnitGradAE_volume (h : Fin m → ℝ) :
    mvbeUnitGradAE (mvbeRho h) (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
  mvbeUnitGradAE_of_ac h Measure.AbsolutelyContinuous.rfl

end Rho

end LatticeProb
