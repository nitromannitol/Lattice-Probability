/-
The same-parity gradient of the lattice walk, reduced to its generators.

`eq:rw-tv-gradient` compares the kernel at two sites of the same parity, that
is at sites whose difference `u` has even `ℓ¹` norm.  Every such `u` is a sum of
`|u|_1/2` vectors of `ℓ¹` norm exactly two, and the total-variation distance is
sub-additive along that decomposition because the kernel is translation
invariant.  So the whole clause reduces to the two generators `±e_i ± e_j` and
`±2e_i`, and the number of them is `|u|_1/2`, which is the linear factor the
paper's bound carries.

What is here is that reduction.  The kernel has finite support, so every
difference is summable; the sum is invariant under translating the site, so the
triangle inequality is sub-additive in the shift; and any nonzero vector loses
exactly one unit of `ℓ¹` norm when the right unit vector is subtracted, so an
induction peels two units at a time.  The generator is then the SUM OF TWO UNIT
VECTORS, which is `±e_i ± e_j` when the two are in different coordinates,
`±2e_i` when they agree, and `0` when they cancel; stating the hypothesis that
way avoids a parity argument, since a bound for every such sum is exactly what
the two- and one-dimensional gradient files supply.

The bound on ONE generator is taken as a hypothesis here.  In the plane it is
`LatticeProb.exists_tsum_srwHeat_two_grad_le`; in general `d` it is the piece
still owed, and it is what the block splitting of the kernel for a pair of
coordinates against the rest is for.
-/
import Mathlib
import LatticeProb.Walk.SRWDiag

noncomputable section

namespace LatticeProb

variable {d : ℕ}

/-! ### Summability and translation invariance -/

/-- The difference of the kernel and its translate is summable, the kernel
having finite support. -/
theorem summable_abs_srwHeat_shift (n : ℕ) (g : Site d) :
    Summable fun w : Site d => |srwHeat d n w - srwHeat d n (w + g)| := by
  classical
  refine summable_of_ne_finset_zero
    (s := boxFinset (0 : Site d) n ∪ (boxFinset (0 : Site d) n).image (fun y => y - g))
    fun x hx => ?_
  have hx1 : srwHeat d n x = 0 := by
    refine srwHeat_eq_zero_of_notMem_box fun hmem => hx ?_
    exact Finset.mem_union_left _ hmem
  have hx2 : srwHeat d n (x + g) = 0 := by
    refine srwHeat_eq_zero_of_notMem_box fun hmem => hx ?_
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x + g, hmem, by simp⟩)
  simp [hx1, hx2]

/-- The total-variation distance between the kernel and its translate by `g`
does not see where the sum is centred. -/
theorem tsum_abs_srwHeat_shift_translate (n : ℕ) (g v : Site d) :
    ∑' w : Site d, |srwHeat d n (w + v) - srwHeat d n (w + v + g)|
      = ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + g)| :=
  (Equiv.addRight v).tsum_eq (fun w => |srwHeat d n w - srwHeat d n (w + g)|)

/-! ### Peeling one unit step off a lattice vector -/

theorem graphNorm_single (i : Fin d) (a : ℤ) : graphNorm (Pi.single i a : Site d) = a.natAbs := by
  classical
  simp only [graphNorm, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem exists_unit_peel {u : Site d} (hu : u ≠ 0) :
    ∃ g : Site d, graphNorm g = 1 ∧ graphNorm (u - g) + 1 = graphNorm u := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin d, u i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (funext fun i => hc i)
  set s : ℤ := if 0 < u i then 1 else -1 with hs
  set g : Site d := Pi.single i s with hg
  have hsabs : s.natAbs = 1 := by
    rw [hs]; split <;> simp
  refine ⟨g, by rw [hg, graphNorm_single, hsabs], ?_⟩
  have hsplit : ∀ f : Fin d → ℕ, ∑ k ∈ (Finset.univ : Finset (Fin d)).erase i, f k + f i
      = ∑ k : Fin d, f k := fun f => Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have he : ∀ k ∈ (Finset.univ : Finset (Fin d)).erase i,
      ((u - g) k).natAbs = (u k).natAbs := by
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp [hg, Pi.sub_apply, hki]
  have hi' : ((u - g) i).natAbs + 1 = (u i).natAbs := by
    have hval : (u - g) i = u i - s := by simp [hg, Pi.sub_apply]
    rw [hval, hs]
    rcases lt_trichotomy (u i) 0 with h | h | h
    · rw [if_neg (not_lt.mpr h.le)]
      omega
    · exact absurd h hi
    · rw [if_pos h]
      omega
  calc graphNorm (u - g) + 1
      = (∑ k ∈ (Finset.univ : Finset (Fin d)).erase i, ((u - g) k).natAbs
          + ((u - g) i).natAbs) + 1 := by rw [graphNorm, hsplit]
    _ = ∑ k ∈ (Finset.univ : Finset (Fin d)).erase i, (u k).natAbs + (u i).natAbs := by
        rw [Finset.sum_congr rfl he]; omega
    _ = graphNorm u := by rw [graphNorm, hsplit]

theorem tsum_abs_srwHeat_shift_add_le (n : ℕ) (g v : Site d) :
    ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + (g + v))|
      ≤ (∑' w : Site d, |srwHeat d n w - srwHeat d n (w + g)|)
        + ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + v)| := by
  have hH : Summable fun w : Site d => |srwHeat d n (w + g) - srwHeat d n (w + g + v)| := by
    have h := ((Equiv.addRight g).summable_iff
      (f := fun w : Site d => |srwHeat d n w - srwHeat d n (w + v)|)).mpr
        (summable_abs_srwHeat_shift n v)
    simpa [Function.comp_def] using h
  have hpt : ∀ w : Site d, |srwHeat d n w - srwHeat d n (w + (g + v))|
      ≤ |srwHeat d n w - srwHeat d n (w + g)|
        + |srwHeat d n (w + g) - srwHeat d n (w + g + v)| := by
    intro w
    rw [← add_assoc]
    exact abs_sub_le _ _ _
  calc ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + (g + v))|
      ≤ ∑' w : Site d, (|srwHeat d n w - srwHeat d n (w + g)|
          + |srwHeat d n (w + g) - srwHeat d n (w + g + v)|) :=
        Summable.tsum_le_tsum hpt (summable_abs_srwHeat_shift n (g + v))
          ((summable_abs_srwHeat_shift n g).add hH)
    _ = (∑' w : Site d, |srwHeat d n w - srwHeat d n (w + g)|)
          + ∑' w : Site d, |srwHeat d n (w + g) - srwHeat d n (w + g + v)| :=
        Summable.tsum_add (summable_abs_srwHeat_shift n g) hH
    _ = (∑' w : Site d, |srwHeat d n w - srwHeat d n (w + g)|)
          + ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + v)| := by
        rw [tsum_abs_srwHeat_shift_translate n v g]

theorem tsum_abs_srwHeat_even_shift_le {n : ℕ} {K : ℝ}
    (hK : ∀ g₁ g₂ : Site d, graphNorm g₁ = 1 → graphNorm g₂ = 1 →
      ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + (g₁ + g₂))| ≤ K) :
    ∀ (r : ℕ) (u : Site d), graphNorm u = 2 * r →
      ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + u)| ≤ (r : ℝ) * K := by
  intro r
  induction r with
  | zero =>
      intro u hu
      have hu0 : u = 0 := graphNorm_eq_zero_iff.mp (by omega)
      simp [hu0]
  | succ r ih =>
      intro u hu
      have hune : u ≠ 0 := by
        intro hc
        rw [hc, graphNorm_zero] at hu
        omega
      obtain ⟨g₁, hg₁, hg₁n⟩ := exists_unit_peel hune
      have hvne : u - g₁ ≠ 0 := by
        intro hc
        rw [hc, graphNorm_zero] at hg₁n
        omega
      obtain ⟨g₂, hg₂, hg₂n⟩ := exists_unit_peel hvne
      have hvn : graphNorm (u - g₁ - g₂) = 2 * r := by omega
      have hdec : u = (g₁ + g₂) + (u - g₁ - g₂) := by abel
      have hIH := ih (u - g₁ - g₂) hvn
      have hgen := hK g₁ g₂ hg₁ hg₂
      have hsub := tsum_abs_srwHeat_shift_add_le n (g₁ + g₂) (u - g₁ - g₂)
      rw [hdec]
      have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [hsub, hgen, hIH]

/-- **The same-parity gradient, reduced to the generators.**  If the
total-variation distance between the kernel and its translate is at most `K` for
every shift that is a sum of two unit vectors, then it is at most `|u|_1/2 · K`
for every shift `u` of even `ℓ¹` norm.  This is the reduction of clause 2 of
`eq:rw-tv-gradient` to its generators `±e_i ± e_j` and `±2e_i`; the linear factor
`|u|_1` of the paper's bound is the number of generators. -/
theorem tsum_abs_srwHeat_shift_le_of_even {n : ℕ} {K : ℝ}
    (hK : ∀ g₁ g₂ : Site d, graphNorm g₁ = 1 → graphNorm g₂ = 1 →
      ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + (g₁ + g₂))| ≤ K)
    (u : Site d) (hu : Even (graphNorm u)) :
    ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + u)| ≤ (graphNorm u : ℝ) / 2 * K := by
  obtain ⟨r, hr⟩ := hu
  have hr' : graphNorm u = 2 * r := by omega
  have h := tsum_abs_srwHeat_even_shift_le hK r u hr'
  have hcast : (graphNorm u : ℝ) / 2 = (r : ℝ) := by
    rw [hr']; push_cast; ring
  rw [hcast]
  exact h

/-- The `ℓ¹` norm of a vector supported at two distinct coordinates is the sum of
the two absolute values. -/
theorem graphNorm_single_add_single {i j : Fin d} (hij : i ≠ j) (a b : ℤ) :
    graphNorm ((Pi.single i a : Site d) + Pi.single j b) = a.natAbs + b.natAbs := by
  classical
  simp only [graphNorm, Pi.add_apply, Pi.single_apply]
  have key : ∑ k ∈ ({i, j} : Finset (Fin d)),
      ((if k = i then a else 0) + (if k = j then b else 0)).natAbs
      = ∑ k : Fin d, ((if k = i then a else 0) + (if k = j then b else 0)).natAbs := by
    refine Finset.sum_subset (fun k _ => Finset.mem_univ k) ?_
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    push Not at hk
    simp [hk.1, hk.2]
  rw [← key, Finset.sum_insert (show (i : Fin d) ∉ ({j} : Finset (Fin d)) from by simp [hij])]
  simp [hij, hij.symm]

/-- A vector of `ℓ¹` norm one is a signed unit vector.  With
`LatticeProb.graphNorm_single_add_single` this identifies the generators
`g₁ + g₂` of the reduction: `±e_i ± e_j`, `±2e_i`, and `0`. -/
theorem eq_single_of_graphNorm_eq_one {u : Site d} (hu : graphNorm u = 1) :
    ∃ (i : Fin d) (s : ℤ), s.natAbs = 1 ∧ u = Pi.single i s := by
  classical
  rw [graphNorm] at hu
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ k : Fin d, (u k).natAbs ≠ 0 from by rw [hu]; simp)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hu
  have hui : (u i).natAbs = 1 := by omega
  have hzero : ∑ k ∈ Finset.univ.erase i, (u k).natAbs = 0 := by omega
  refine ⟨i, u i, hui, ?_⟩
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · have hk' : (u k).natAbs = 0 := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le _)] at hzero
      exact hzero k (by simp [hk])
    simp [hk, Int.natAbs_eq_zero.mp hk']


end LatticeProb
