/-
`ℕ∞`-valued arrival/hitting-time boilerplate, moved from
`Exploding-Sandpiles`'s `Exploding/Support/Wave.lean` and
`Exploding/Support/Gen.lean`.  Every hitting time in that formalization
(`crossingTime`, `chemDist`, `lastArrival`, `clusterArrival`, `arrival`) is an
`sInf` over `{t : ℕ∞ | ∃ n : ℕ, t = n ∧ P n}` so that the absence of a witness
reads as `⊤` rather than the junk natural number `0`; these are the two facts
that identify such an infimum (attained at a witness natural, or `⊤` when
there is none) and the arithmetic for combining a finite such time with a
natural constant.  Paper-independent: none of the five statements below
mentions a graph, a lattice, or a sandpile.
-/
import Mathlib

namespace LatticeProb

/-- An `ℕ∞`-infimum over `{t | ∃ n, t = n ∧ P n}` is attained at a witness
natural, when one exists. -/
theorem sInf_coe_attained {P : ℕ → Prop} (h : ∃ n : ℕ, P n) :
    ∃ n : ℕ, P n ∧ sInf {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = (n : ℕ∞) := by
  classical
  refine ⟨sInf {n | P n}, Nat.sInf_mem h, le_antisymm ?_ ?_⟩
  · exact sInf_le ⟨sInf {n | P n}, rfl, Nat.sInf_mem h⟩
  · refine le_sInf ?_
    rintro t ⟨m, rfl, hm⟩
    exact_mod_cast Nat.sInf_le hm

/-- An `ℕ∞`-infimum over `{t | ∃ n, t = n ∧ P n}` is `⊤` when no natural
satisfies `P`. -/
theorem sInf_coe_top {P : ℕ → Prop} (h : ¬ ∃ n : ℕ, P n) :
    sInf {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = ⊤ := by
  have hempty : {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    rintro m rfl hm
    exact h ⟨m, hm⟩
  rw [hempty, sInf_empty]

/-- A finite `ℕ∞`-valued time plus a natural constant is finite. -/
theorem add_nat_ne_top {a : ℕ∞} (ha : a ≠ ⊤) (C : ℕ) : a + (C : ℕ∞) ≠ ⊤ := by
  intro h
  rw [ENat.add_eq_top] at h
  exact h.elim ha (by simp)

/-- The `toNat` of a sum of a finite `ℕ∞` and a natural is the sum of the
`toNat`s. -/
theorem toNat_add_nat {a : ℕ∞} (ha : a ≠ ⊤) (C : ℕ) :
    (a + (C : ℕ∞)).toNat = a.toNat + C := by
  cases a with
  | top => exact absurd rfl ha
  | coe n => simp [ENat.toNat_add]

/-- If `a ≤ b + C` in `ℕ∞` with `b` finite, then `a.toNat ≤ b.toNat + C`. -/
theorem toNat_le_add {a b : ℕ∞} {C : ℕ} (h : a ≤ b + (C : ℕ∞)) (hb : b ≠ ⊤) :
    a.toNat ≤ b.toNat + C := by
  have hfin : b + (C : ℕ∞) ≠ ⊤ := add_nat_ne_top hb C
  have h1 : a.toNat ≤ (b + (C : ℕ∞)).toNat := ENat.toNat_le_toNat h hfin
  rwa [toNat_add_nat hb C] at h1

end LatticeProb
