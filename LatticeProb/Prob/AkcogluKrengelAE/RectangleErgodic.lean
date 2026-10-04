/-
# The rectangle multiparameter ergodic theorem: the boundary-slab reduction

This file states the **rectangle** multiparameter pointwise ergodic reduction on `ℤ^d` that the
shared library is missing.  The library proves the *anchored-cube* theorem
`LatticeProb.exists_ae_tendsto_gridAvg_univ_with_integral`
(`LatticeProb/Prob/AkcogluKrengelAE/BoundedErgodic.lean:561`): for a measure-preserving additive
action `σ` of `ℤ^d` on a probability space and a bounded measurable `h`, the full cube average
over `[0,N)^d` converges a.e. to a limit `G` with `∫G = ∫h`.

The external `VRW.External.PointwiseErgodicCubes` (`ext-multiparameter-ergodic`, `vrjp.tex:836`)
needs instead the **rectangle** average: for every `a ≤ b : Fin d → ℝ`,
`N^{-d} Σ_{x ∈ ∏ᵢ [⌈Naᵢ⌉, ⌈Nbᵢ⌉)} v x → (∏ᵢ (bᵢ − aᵢ)) · ∫ v` a.e.  The naive difference
`[0,Nb) = [0,Na) ⊔ N[a,b)` is invalid, because the two cube averages have different
normalizations and their limits differ by `(∏bᵢ − ∏aᵢ)∫`, not `∏(bᵢ − aᵢ)∫`.

## What is proved here

The exact **boundary-slab decomposition** of the rectangle indicator into `2^d` anchored boxes:

  `1_{∏ᵢ [⌈Naᵢ⌉, ⌈Nbᵢ⌉)} = ∑_{S ⊆ {1,…,d}} (−1)^{|S|} 1_{∏ᵢ [0, ⌈N c_{S,i}⌉)}`,
  where `c_{S,i} = aᵢ` for `i ∈ S` and `c_{S,i} = bᵢ` otherwise.

This is the algebraic content: the `2^d` corners `{0, a, b}` give the alternating sum, and the
normalized limit is `∑_S (−1)^{|S|} ∏ᵢ c_{S,i} = ∏ᵢ (bᵢ − aᵢ)`, which is exactly the frozen
statement's normalization `∏(bᵢ − aᵢ) ∫v`.  The decomposition is proved, together with the
normalization, as `indicator_rectBox_eq_sum_anchoredBox`, `signed_sum_corner_eq_prod_sub` and
`sum_rectBox_eq_signed_sum_anchoredBox`, for `0 ≤ a ≤ b`.

From the decomposition the reduction is immediate and is proved here:

* `RectangleErgodic_of_AnchoredBox`: the a.e. rectangle theorem (for `0 ≤ a ≤ b`) follows from
the a.e. anchored **box** theorem (each of the `2^d` boxes) — a finite intersection of conull
sets, plus the normalization `∏(bᵢ − aᵢ)`.

## The exact remaining gaps

Two steps are still missing; neither is hidden in a `sorry`.

1. **The anchored-box theorem from the anchored-cube theorem.**  `AnchoredBoxErgodic` is *not*
the anchored-cube theorem: the cube theorem handles only `[0,N)^d`, whereas the decomposition
produces boxes `∏ᵢ [0, ⌈N cᵢ⌉)` with **coordinate-dependent** side lengths `⌈N cᵢ⌉`.  The missing
step is the boundary-slab tiling that derives the box theorem from the cube theorem: choose a
cube side `s = s(N) → ∞` with `s = o(N)`, partition `∏ᵢ [0, mᵢ)` into `∏ᵢ ⌊mᵢ/s⌋` cubes of side
`s` plus a remainder of relative volume `O(s / minᵢ mᵢ) → 0`, and average the shifted cube
limits (which are invariant under the action).

2. **Arbitrary `a` (possibly negative) from `0 ≤ a`.**  The frozen statement allows every
`a ≤ b : Fin d → ℝ`.  For `a ≱ 0`, pick an integer shift `z ≥ ⌈−a⌉`; the identity
`∑_{x ∈ rectBox a b N} f (τ x ω) = ∑_{y ∈ rectBox (a+z) (b+z) N} f (τ y (τ (−(Nz)) ω))`
reduces the average to the `0 ≤ a` theorem applied at `τ (−(Nz)) ω`.  Because `N` ranges over a
countable set, the a.e. statement survives the countable intersection of the conull good sets.
This shift bookkeeping is not formalized here; the present file reduces the frozen rectangle
statement to the `0 ≤ a` case and to item 1.
-/
import LatticeProb.Prob.AkcogluKrengelAE.BoundedErgodic

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The anchored box `∏ᵢ [0, ⌈N cᵢ⌉) ⊂ ℤ^d`.  It is empty in a coordinate with `⌈N cᵢ⌉ ≤ 0`. -/
noncomputable def anchoredBox {d : ℕ} (c : Fin d → ℝ) (N : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => Finset.Ico (0 : ℤ) ⌈(N : ℝ) * c i⌉

/-- The rectangle `∏ᵢ [⌈N aᵢ⌉, ⌈N bᵢ⌉) ⊂ ℤ^d`. -/
noncomputable def rectBox {d : ℕ} (a b : Fin d → ℝ) (N : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => Finset.Ico ⌈(N : ℝ) * a i⌉ ⌈(N : ℝ) * b i⌉

/-- Membership in the anchored box. -/
theorem mem_anchoredBox {d : ℕ} {c : Fin d → ℝ} {N : ℕ} {x : Site d} :
    x ∈ anchoredBox c N ↔ ∀ i, x i ∈ Finset.Ico (0 : ℤ) ⌈(N : ℝ) * c i⌉ :=
  Fintype.mem_piFinset

/-- Membership in the rectangle. -/
theorem mem_rectBox {d : ℕ} {a b : Fin d → ℝ} {N : ℕ} {x : Site d} :
    x ∈ rectBox a b N ↔ ∀ i, x i ∈ Finset.Ico ⌈(N : ℝ) * a i⌉ ⌈(N : ℝ) * b i⌉ :=
  Fintype.mem_piFinset

/-- The corner box of the alternating sum: coordinate `i` uses side `aᵢ` when `i ∈ S` and side
`bᵢ` otherwise. -/
def corner {d : ℕ} (a b : Fin d → ℝ) (S : Finset (Fin d)) : Fin d → ℝ :=
  fun i => if i ∈ S then a i else b i

/-- The `ℤ`-indicator of `Ico 0 m` is monotone in `m`, and the difference of two such
indicators is the indicator of the interval `Ico n m` when `0 ≤ n ≤ m`. -/
theorem ite_Ico_sub_ite_Ico {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) (x : ℤ) :
    (if x ∈ Finset.Ico (0 : ℤ) m then (1 : ℝ) else 0) -
        (if x ∈ Finset.Ico (0 : ℤ) n then (1 : ℝ) else 0) =
      (if x ∈ Finset.Ico n m then (1 : ℝ) else 0) := by
  by_cases h1 : x ∈ Finset.Ico (0 : ℤ) m
  · by_cases h2 : x ∈ Finset.Ico (0 : ℤ) n
    · have h3 : x ∉ Finset.Ico n m := by
        intro h; simp only [Finset.mem_Ico] at h h2; omega
      simp [h1, h2, h3]
    · have h3 : x ∈ Finset.Ico n m := by
        simp only [Finset.mem_Ico] at h1 h2 ⊢
        omega
      simp [h1, h2, h3]
  · have h2 : x ∉ Finset.Ico (0 : ℤ) n := fun h => h1 (by
      simp only [Finset.mem_Ico] at h ⊢; omega)
    have h3 : x ∉ Finset.Ico n m := by
      intro h; exact h1 (by simp only [Finset.mem_Ico] at h ⊢; omega)
    simp [h1, h2, h3]

/-- The product of the `Ico 0 m` indicators over the coordinates is the indicator of the
anchored box. -/
theorem prod_ite_Ico_eq_indicator_anchoredBox {d : ℕ} (c : Fin d → ℝ) (N : ℕ) (x : Site d) :
    (∏ i, (if x i ∈ Finset.Ico (0 : ℤ) ⌈(N : ℝ) * c i⌉ then (1 : ℝ) else 0)) =
      (if x ∈ anchoredBox c N then (1 : ℝ) else 0) := by
  classical
  rw [Fintype.prod_boole]
  by_cases h : ∀ i, x i ∈ Finset.Ico (0 : ℤ) ⌈(N : ℝ) * c i⌉
  · rw [if_pos h, if_pos (by simpa only [mem_anchoredBox] using h)]
  · rw [if_neg h, if_neg (by simpa only [mem_anchoredBox] using h)]

/-- **The rectangle is the alternating sum of its `2^d` anchored corner boxes.**  For
`0 ≤ a ≤ b` and every site `x`,
`1_{∏ᵢ [⌈Naᵢ⌉, ⌈Nbᵢ⌉)} = ∑_{S} (−1)^{|S|} 1_{∏ᵢ [0, ⌈N c_{S,i}⌉)}`, `c_{S,i} = aᵢ` on `S`
and `bᵢ` off `S`.  This is the boundary-slab decomposition behind the rectangle theorem. -/
theorem indicator_rectBox_eq_sum_anchoredBox {d : ℕ} (a b : Fin d → ℝ) (N : ℕ) (x : Site d)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    (if x ∈ rectBox a b N then (1 : ℝ) else 0) =
      ∑ S : Finset (Fin d), (-1) ^ S.card *
        (if x ∈ anchoredBox (corner a b S) N then (1 : ℝ) else 0) := by
  classical
  let F : Fin d → ℝ := fun i => if x i ∈ Finset.Ico (0 : ℤ) ⌈(N : ℝ) * b i⌉ then 1 else 0
  let G : Fin d → ℝ := fun i => if x i ∈ Finset.Ico (0 : ℤ) ⌈(N : ℝ) * a i⌉ then 1 else 0
  have hrect : (if x ∈ rectBox a b N then (1 : ℝ) else 0) = ∏ i, (F i - G i) := by
    have h1 : (if x ∈ rectBox a b N then (1 : ℝ) else 0) =
        ∏ i, (if x i ∈ Finset.Ico ⌈(N : ℝ) * a i⌉ ⌈(N : ℝ) * b i⌉ then (1 : ℝ) else 0) := by
      rw [Fintype.prod_boole]
      by_cases h : ∀ i, x i ∈ Finset.Ico ⌈(N : ℝ) * a i⌉ ⌈(N : ℝ) * b i⌉
      · rw [if_pos h, if_pos (by simpa only [mem_rectBox] using h)]
      · rw [if_neg h, if_neg (by simpa only [mem_rectBox] using h)]
    rw [h1]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (ite_Ico_sub_ite_Ico (Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg N) (ha i)))
      (Int.ceil_mono (mul_le_mul_of_nonneg_left (hab i) (Nat.cast_nonneg N))) (x i)).symm
  rw [hrect, Finset.prod_sub F G Finset.univ, Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have hfactor : (∏ i, (if i ∈ S then G i else F i)) =
      (∏ i ∈ Finset.univ \ S, F i) * ∏ i ∈ S, G i := by
    have hfilter1 : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
    have hfilter2 : Finset.univ.filter (fun i => ¬ i ∈ S) = Finset.univ \ S := by
      ext i; simp [Finset.mem_sdiff]
    rw [Finset.prod_ite, hfilter1, hfilter2, mul_comm]
  have hprod : (∏ i ∈ Finset.univ \ S, F i) * ∏ i ∈ S, G i =
      (if x ∈ anchoredBox (corner a b S) N then (1 : ℝ) else 0) := by
    have hcongr : (∏ i, (if i ∈ S then G i else F i)) =
        ∏ i, (if x i ∈ Finset.Ico (0 : ℤ) ⌈(N : ℝ) * (corner a b S) i⌉ then
          (1 : ℝ) else 0) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ S <;> simp [F, G, corner, hi]
    rw [← hfactor, hcongr, prod_ite_Ico_eq_indicator_anchoredBox]
  rw [mul_assoc, hprod]

/-- The signed sum of the `2^d` corner products is the product of the coordinate differences:
`∑_{S} (−1)^{|S|} ∏ᵢ c_{S,i} = ∏ᵢ (bᵢ − aᵢ)`.  This is the normalization that makes the frozen
rectangle limit `∏(bᵢ − aᵢ) ∫v` come out of the `2^d` anchored-box limits. -/
theorem signed_sum_corner_eq_prod_sub {d : ℕ} (a b : Fin d → ℝ) :
    ∑ S : Finset (Fin d), (-1) ^ S.card * (∏ i, corner a b S i) =
      ∏ i, (b i - a i) := by
  classical
  rw [Finset.prod_sub (fun i => b i) (fun i => a i) Finset.univ, Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have hprod : (∏ i, corner a b S i) = (∏ i ∈ Finset.univ \ S, b i) * ∏ i ∈ S, a i := by
    rw [mul_comm]
    rw [show (∏ i ∈ S, a i) = ∏ i ∈ Finset.univ.filter (fun i => i ∈ S), a i by
      congr 1; ext i; simp]
    rw [show (∏ i ∈ Finset.univ \ S, b i) = ∏ i ∈ Finset.univ.filter (fun i => ¬ i ∈ S), b i by
      congr 1; ext i; simp [Finset.mem_sdiff]]
    rw [← Finset.prod_ite (s := Finset.univ) (p := fun i => i ∈ S) (fun i => a i) (fun i => b i)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ S <;> simp [corner, hi]
  rw [hprod, mul_assoc]

/-- Summing the boundary-slab decomposition over the common ambient box gives the rectangle
sum as the signed sum of the `2^d` anchored box sums. -/
theorem sum_rectBox_eq_signed_sum_anchoredBox {d : ℕ} (f : Site d → ℝ) (a b : Fin d → ℝ) (N : ℕ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    ∑ x ∈ rectBox a b N, f x =
      ∑ S : Finset (Fin d), (-1) ^ S.card * ∑ x ∈ anchoredBox (corner a b S) N, f x := by
  classical
  have hU : rectBox a b N ⊆ anchoredBox b N := by
    intro x hx
    rw [mem_rectBox] at hx; rw [mem_anchoredBox]
    intro i
    have hi := hx i
    simp only [Finset.mem_Ico] at hi ⊢
    exact ⟨le_trans (Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg N) (ha i))) hi.1, hi.2⟩
  have hsub : ∀ S : Finset (Fin d), anchoredBox (corner a b S) N ⊆ anchoredBox b N := by
    intro S x hx
    rw [mem_anchoredBox] at hx ⊢
    intro i
    have hi := hx i
    simp only [Finset.mem_Ico] at hi ⊢
    refine ⟨hi.1, lt_of_lt_of_le hi.2 ?_⟩
    apply Int.ceil_mono
    by_cases hS : i ∈ S
    · have hc : corner a b S i = a i := by simp [corner, hS]
      rw [hc]
      exact mul_le_mul_of_nonneg_left (hab i) (Nat.cast_nonneg N)
    · have hc : corner a b S i = b i := by simp [corner, hS]
      rw [hc]
  have hstep1 : (∑ x ∈ anchoredBox b N, (if x ∈ rectBox a b N then f x else 0)) =
      ∑ x ∈ rectBox a b N, f x := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hU h, h⟩⟩
  have hstep2 : (∑ x ∈ anchoredBox b N, (if x ∈ rectBox a b N then f x else 0)) =
      ∑ x ∈ anchoredBox b N,
        ∑ S : Finset (Fin d), (-1) ^ S.card *
          (if x ∈ anchoredBox (corner a b S) N then f x else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hid := indicator_rectBox_eq_sum_anchoredBox a b N x ha hab
    rw [show (if x ∈ rectBox a b N then f x else 0) =
        (if x ∈ rectBox a b N then (1 : ℝ) else 0) * f x by
      by_cases h : x ∈ rectBox a b N <;> simp [h],
      hid, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases h : x ∈ anchoredBox (corner a b S) N <;> simp [h]
  have hinner : ∀ S : Finset (Fin d),
      (∑ x ∈ anchoredBox b N,
          (-1) ^ S.card * (if x ∈ anchoredBox (corner a b S) N then f x else 0)) =
        (-1) ^ S.card * ∑ x ∈ anchoredBox (corner a b S) N, f x := by
    intro S
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub S h, h⟩⟩
  calc
    ∑ x ∈ rectBox a b N, f x
        = ∑ x ∈ anchoredBox b N, (if x ∈ rectBox a b N then f x else 0) := hstep1.symm
    _ = ∑ x ∈ anchoredBox b N,
          ∑ S : Finset (Fin d), (-1) ^ S.card *
            (if x ∈ anchoredBox (corner a b S) N then f x else 0) := hstep2
    _ = ∑ S : Finset (Fin d),
          ∑ x ∈ anchoredBox b N,
            (-1) ^ S.card * (if x ∈ anchoredBox (corner a b S) N then f x else 0) :=
          Finset.sum_comm
    _ = ∑ S : Finset (Fin d), (-1) ^ S.card * ∑ x ∈ anchoredBox (corner a b S) N, f x :=
          Finset.sum_congr rfl (fun S _ => hinner S)

/-- The anchored-**box** almost-everywhere ergodic theorem: for a measure-preserving additive
`ℤ^d` action on an ergodic probability space, the average over `∏ᵢ [0, ⌈N cᵢ⌉)` converges a.e.
to `(∏ᵢ cᵢ) ∫h`.  This is the step the library does not yet have: the anchored-cube theorem
handles only `cᵢ` all equal (the cube `[0,N)^d`). -/
def AnchoredBoxErgodic (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    (∀ A : Set Ω, MeasurableSet A → (∀ z, τ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
    ∀ c : Fin d → ℝ, (∀ i, 0 ≤ c i) →
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ anchoredBox c N, h (τ x ω)) atTop (𝓝 ((∏ i, c i) * ∫ ω, h ω ∂μ))

/-- The rectangle almost-everywhere ergodic theorem for `0 ≤ a ≤ b`, the action form of
`VRW.External.PointwiseErgodicCubes` after unfolding the shift action. -/
def RectangleErgodic (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    (∀ A : Set Ω, MeasurableSet A → (∀ z, τ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
    ∀ a b : Fin d → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ b i) →
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ rectBox a b N, h (τ x ω)) atTop (𝓝 ((∏ i, (b i - a i)) * ∫ ω, h ω ∂μ))

/-- **The rectangle reduction.**  The a.e. rectangle theorem follows from the a.e. anchored-box
theorem: for a.e. `ω` all `2^d` signed anchored-box averages converge, and the boundary-slab
decomposition `sum_rectBox_eq_signed_sum_anchoredBox` plus the normalization
`signed_sum_corner_eq_prod_sub` identify the limit. -/
theorem RectangleErgodic_of_AnchoredBox {d : ℕ} (H : AnchoredBoxErgodic d) :
    RectangleErgodic d := by
  intro Ω instΩ ν instν τ hτ hadd herg h hh hbdd a b ha hab
  have hb0 : ∀ i, 0 ≤ b i := fun i => le_trans (ha i) (hab i)
  have hbox : ∀ S : Finset (Fin d), ∀ᵐ ω ∂ν,
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ anchoredBox (corner a b S) N, h (τ x ω)) atTop
        (𝓝 ((∏ i, corner a b S i) * ∫ ω, h ω ∂ν)) := by
    intro S
    refine H ν τ hτ hadd herg h hh hbdd (corner a b S) (fun i => ?_)
    by_cases hi : i ∈ S <;> simp [corner, hi, ha i, hb0 i]
  have hall : ∀ᵐ ω ∂ν, ∀ S : Finset (Fin d),
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ anchoredBox (corner a b S) N, h (τ x ω)) atTop
        (𝓝 ((∏ i, corner a b S i) * ∫ ω, h ω ∂ν)) := by
    rw [Filter.eventually_all]
    exact hbox
  filter_upwards [hall] with ω hω
  have hfun : ∀ N : ℕ, (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ rectBox a b N, h (τ x ω) =
      ∑ S : Finset (Fin d), (-1) ^ S.card *
        ((N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox (corner a b S) N, h (τ x ω)) := by
    intro N
    rw [sum_rectBox_eq_signed_sum_anchoredBox (fun x => h (τ x ω)) a b N ha hab,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  have hlim : Tendsto (fun N : ℕ => ∑ S : Finset (Fin d), (-1) ^ S.card *
        ((N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox (corner a b S) N, h (τ x ω)))
      atTop (𝓝 ((∏ i, (b i - a i)) * ∫ ω, h ω ∂ν)) := by
    have h2 : Tendsto (fun N : ℕ => ∑ S : Finset (Fin d), (-1) ^ S.card *
          ((N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox (corner a b S) N, h (τ x ω)))
        atTop (𝓝 (∑ S : Finset (Fin d), (-1) ^ S.card *
          ((∏ i, corner a b S i) * ∫ ω, h ω ∂ν))) :=
      tendsto_finsetSum Finset.univ (fun S _ => (hω S).const_mul ((-1) ^ S.card))
    have hlim2 : (∑ S : Finset (Fin d), (-1) ^ S.card *
          ((∏ i, corner a b S i) * ∫ ω, h ω ∂ν)) =
        (∏ i, (b i - a i)) * ∫ ω, h ω ∂ν := by
      rw [show (∑ S : Finset (Fin d), (-1) ^ S.card *
            ((∏ i, corner a b S i) * ∫ ω, h ω ∂ν)) =
          (∑ S : Finset (Fin d), (-1) ^ S.card * (∏ i, corner a b S i)) *
            ∫ ω, h ω ∂ν by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun S _ => by ring)]
      rw [signed_sum_corner_eq_prod_sub]
    rwa [hlim2] at h2
  simp_rw [hfun]
  exact hlim

end LatticeProb
