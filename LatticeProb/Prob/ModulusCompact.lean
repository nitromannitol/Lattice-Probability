/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftConditionedModulus

/-!
# A compact set of continuous paths defined by a sequence of moduli of continuity

For `η : ℕ → ℕ → ℝ≥0` with all values positive, let `modulusSet η` be the set of functions
`f : ℝ≥0 → ℝ` with `f 0 = 0` which, for every horizon `j` and level `m`, have modulus `1 / (m + 1)`
at scale `η j m` on `[0, j]` (`LatticeProb.HasModulus`).

* `LatticeProb.isClosed_modulusSet`: `modulusSet η` is closed in the product topology.
* `LatticeProb.abs_le_of_mem_modulusSet`: the chain bound `|f x| ≤ n` for `x ≤ n η j 0`, `x ≤ j`.
* `LatticeProb.equicontinuous_modulusSet`: `modulusSet η` is equicontinuous.
* `LatticeProb.isCompact_modulusSet`: the set of continuous paths in `modulusSet η` is compact in
  `C(ℝ≥0, ℝ)` (Arzelà–Ascoli).
-/

open Filter Topology Set
open scoped NNReal

noncomputable section

namespace LatticeProb

/-- The functions vanishing at `0` with modulus `1 / (m + 1)` at scale `η j m` on `[0, j]`, for
all `j, m`. -/
def modulusSet (η : ℕ → ℕ → ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  {f | f 0 = 0 ∧ ∀ j m : ℕ, HasModulus f j (η j m) (1 / ((m : ℝ) + 1))}

/-- `modulusSet η` is closed in the topology of pointwise convergence. -/
theorem isClosed_modulusSet (η : ℕ → ℕ → ℝ≥0) : IsClosed (modulusSet η) := by
  have h0 : IsClosed {f : ℝ≥0 → ℝ | f 0 = 0} := isClosed_eq (continuous_apply 0) continuous_const
  have h1 : ∀ j m : ℕ,
      IsClosed {f : ℝ≥0 → ℝ | HasModulus f j (η j m) (1 / ((m : ℝ) + 1))} := by
    intro j m
    have : {f : ℝ≥0 → ℝ | HasModulus f j (η j m) (1 / ((m : ℝ) + 1))} =
        ⋂ s : ℝ≥0, ⋂ t : ℝ≥0, ⋂ (_ : s ≤ j), ⋂ (_ : t ≤ j), ⋂ (_ : |(s : ℝ) - t| ≤ η j m),
          {f | |f s - f t| ≤ 1 / ((m : ℝ) + 1)} := by
      ext f
      simp only [HasModulus, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [this]
    refine isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_le (by fun_prop) continuous_const
  have : modulusSet η = {f : ℝ≥0 → ℝ | f 0 = 0} ∩
      ⋂ j : ℕ, ⋂ m : ℕ, {f : ℝ≥0 → ℝ | HasModulus f j (η j m) (1 / ((m : ℝ) + 1))} := by
    ext f
    simp only [modulusSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact h0.inter (isClosed_iInter fun j => isClosed_iInter fun m => h1 j m)

/-- **Chain bound.**  On `[0, j]`, a function in `modulusSet η` is at most `n` in absolute value
at the points `x ≤ n η j 0`. -/
theorem abs_le_of_mem_modulusSet {η : ℕ → ℕ → ℝ≥0} {f : ℝ≥0 → ℝ} (hf : f ∈ modulusSet η)
    (j n : ℕ) : ∀ x : ℝ≥0, x ≤ j → x ≤ n * η j 0 → |f x| ≤ n := by
  obtain ⟨h0, hmod⟩ := hf
  induction n with
  | zero =>
    intro x _ hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp [h0]
  | succ n ih =>
    intro x hxj hx
    set e := η j 0 with he
    have hx' : x - e ≤ n * e := by
      rw [tsub_le_iff_right]
      calc x ≤ ((n + 1 : ℕ) : ℝ≥0) * e := hx
        _ = n * e + e := by push_cast; ring
    have h1 := ih (x - e) (le_trans tsub_le_self hxj) hx'
    have hd : |(x : ℝ) - ((x - e : ℝ≥0) : ℝ)| ≤ e := by
      by_cases hex : e ≤ x
      · rw [NNReal.coe_sub hex]
        simp
      · push Not at hex
        rw [tsub_eq_zero_of_le hex.le]
        simp only [NNReal.coe_zero, sub_zero]
        rw [abs_of_nonneg (NNReal.coe_nonneg x)]
        exact_mod_cast hex.le
    have h2 := hmod j 0 x (x - e) hxj (le_trans tsub_le_self hxj) hd
    have h3 : |f x| ≤ |f (x - e)| + |f x - f (x - e)| := by
      calc |f x| = |f (x - e) + (f x - f (x - e))| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    simp only [Nat.cast_zero, zero_add, div_one] at h2
    push_cast
    linarith

/-- Pointwise bound: every `x` has a bound `N` valid for all functions of `modulusSet η`. -/
theorem exists_bound_modulusSet {η : ℕ → ℕ → ℝ≥0} (hη : ∀ j m, 0 < η j m) (x : ℝ≥0) :
    ∃ N : ℝ, ∀ f ∈ modulusSet η, |f x| ≤ N := by
  obtain ⟨n, hn⟩ := exists_nat_ge (x / η ⌈x⌉₊ 0)
  refine ⟨n, fun f hf => abs_le_of_mem_modulusSet hf ⌈x⌉₊ n x (Nat.le_ceil x) ?_⟩
  rwa [div_le_iff₀ (hη _ _)] at hn

/-- `modulusSet η` is equicontinuous, when all the scales are positive. -/
theorem equicontinuous_modulusSet {η : ℕ → ℕ → ℝ≥0} (hη : ∀ j m, 0 < η j m) :
    Equicontinuous ((↑) : modulusSet η → ℝ≥0 → ℝ) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  set j : ℕ := ⌈x⌉₊ + 1 with hj
  refine ⟨min (η j m : ℝ) 1, lt_min (by exact_mod_cast hη j m) one_pos, fun y hy f => ?_⟩
  have hy1 : dist y x < η j m := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : dist y x < 1 := lt_of_lt_of_le hy (min_le_right _ _)
  rw [NNReal.dist_eq] at hy1 hy2
  have hxj : x ≤ j := by
    have := Nat.le_ceil x
    have h' : (⌈x⌉₊ : ℝ≥0) ≤ j := by rw [hj]; push_cast; exact le_self_add
    exact this.trans h'
  have hyj : y ≤ j := by
    have h1 : (y : ℝ) < x + 1 := by linarith [le_abs_self ((y : ℝ) - x)]
    have h2 : (x : ℝ) ≤ ⌈x⌉₊ := by exact_mod_cast Nat.le_ceil x
    have h3 : (y : ℝ) ≤ j := by rw [hj]; push_cast; linarith
    exact_mod_cast h3
  have := f.2.2 j m x y hxj hyj (by rw [abs_sub_comm]; exact hy1.le)
  rw [Real.dist_eq]
  calc |f.1 x - f.1 y| ≤ 1 / ((m : ℝ) + 1) := this
    _ < ε := hm

/-- **Compactness.**  With all scales positive, the continuous paths in `modulusSet η` form a
compact subset of `C(ℝ≥0, ℝ)` (compact-open topology). -/
theorem isCompact_modulusSet {η : ℕ → ℕ → ℝ≥0} (hη : ∀ j m, 0 < η j m) :
    IsCompact {f : C(ℝ≥0, ℝ) | (f : ℝ≥0 → ℝ) ∈ modulusSet η} := by
  have hequi := equicontinuous_modulusSet hη
  have himage : ContinuousMap.toFun '' {f : C(ℝ≥0, ℝ) | (f : ℝ≥0 → ℝ) ∈ modulusSet η} =
      modulusSet η := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro hg
      exact ⟨⟨g, hequi.continuous ⟨g, hg⟩⟩, hg, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [himage]
    choose N hN using exists_bound_modulusSet hη
    have hpi : IsCompact (Set.pi Set.univ fun x : ℝ≥0 => Set.Icc (-N x) (N x)) :=
      isCompact_univ_pi fun x => isCompact_Icc
    refine hpi.of_isClosed_subset (isClosed_modulusSet η) fun f hf x _ => ?_
    exact abs_le.1 (hN x f hf)
  · exact hequi.comp
      (fun f : {f : C(ℝ≥0, ℝ) | (f : ℝ≥0 → ℝ) ∈ modulusSet η} =>
        (⟨(f.1 : ℝ≥0 → ℝ), f.2⟩ : modulusSet η))

end LatticeProb
