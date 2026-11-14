import Mathlib

/-!
# First mesh interval below a level

A function that starts above a level and later dips strictly below it has a
first mesh interval containing such a dip.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The first mesh interval containing a strict dip has no earlier strict dip. -/
theorem exists_first_mesh_dip {X : ℝ → ℝ} {a c ε : ℝ} (hε : 0 < ε)
    (ha : c ≤ X a) (hdip : ∃ t ≥ a, X t < c) :
    ∃ n : ℕ, ∃ t ∈ Icc (a + (n : ℝ) * ε) (a + ((n : ℝ) + 1) * ε),
      X t < c ∧ ∀ u ∈ Icc a (a + (n : ℝ) * ε), c ≤ X u := by
  classical
  obtain ⟨t, hta, ht⟩ := hdip
  obtain ⟨N, hN⟩ := exists_nat_gt ((t - a) / ε)
  have htN : t ≤ a + ((N : ℝ) + 1) * ε := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hex : ∃ n : ℕ, ∃ u ∈ Icc a (a + ((n : ℝ) + 1) * ε), X u < c :=
    ⟨N, t, ⟨hta, htN⟩, ht⟩
  let n := Nat.find hex
  obtain ⟨v, hv, hvlt⟩ := Nat.find_spec hex
  have hbefore : ∀ u ∈ Icc a (a + (n : ℝ) * ε), c ≤ X u := by
    intro u hu
    by_cases hn : n = 0
    · have : u = a := by simpa [hn] using hu
      simpa [this] using ha
    · obtain ⟨m, hnm⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hmn : m < n := by rw [hnm]; exact Nat.lt_succ_self m
      have hmin := Nat.find_min hex hmn
      have hnot : ¬ X u < c := by
        intro hlt
        apply hmin
        refine ⟨u, ?_, hlt⟩
        simpa [hnm, Nat.cast_succ] using hu
      exact le_of_not_gt hnot
  have hvleft : a + (n : ℝ) * ε ≤ v := by
    by_contra h
    have hvbefore : v ∈ Icc a (a + (n : ℝ) * ε) := ⟨hv.1, le_of_not_ge h⟩
    exact (not_lt_of_ge (hbefore v hvbefore)) hvlt
  exact ⟨n, v, ⟨hvleft, hv.2⟩, hvlt, hbefore⟩

end LatticeProb
