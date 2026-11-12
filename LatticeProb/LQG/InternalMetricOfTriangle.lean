import Mathlib
import LatticeProb.LQG.LengthMetricDerived

/-!
# Concatenation and reversal of paths for a function with the triangle inequality only

Let `E : ℂ → ℂ → ℝ` satisfy the triangle inequality in the form
`ofReal (E x z) ≤ ofReal (E x y) + ofReal (E y z)`; no symmetry, positivity, or
`E x x = 0` is assumed.  The `E`-length of a curve is the supremum of the sums
`∑ ofReal (E (p t_{i+1}) (p t_i))` over partitions.

* `curveLength_le_add_of_ofReal_triangle`: subadditivity of the length across a split point;
* `pathLength_trans_le_of_ofReal_triangle`: the length of a concatenation is at most the sum;
* `internalMetric_triangle_of_ofReal_triangle`: the triangle inequality of the internal metric;
* `pathLength_symm_le_of_ofReal_symm`, `internalMetric_symm_of_ofReal_symm`: symmetry, when
  `ofReal (E x y) = ofReal (E y x)`.
-/

open Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.LQG

variable {E : ℂ → ℂ → ℝ}

private theorem curveLength_mono_aux {f : ℝ → ℂ} {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    curveLength E f a b ≤ curveLength E f a' b' := by
  unfold curveLength
  refine iSup_le fun q => ?_
  exact le_iSup_of_le (⟨q.1, q.2.1, q.2.2.1, fun i => ⟨ha.trans (q.2.2.2 i).1,
    (q.2.2.2 i).2.trans hb⟩⟩ : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a' b' }) le_rfl

/-- A single step `s ≤ t` in `[a, b]` is a partition: its term is at most the length. -/
theorem ofReal_le_curveLength {f : ℝ → ℂ} {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) : ENNReal.ofReal (E (f t) (f s)) ≤ curveLength E f a b := by
  have hmono : Monotone (fun i : ℕ => if i = 0 then s else t) := by
    refine monotone_nat_of_le_succ fun n => ?_
    by_cases hn : n = 0
    · subst hn; simpa using hst
    · simp [hn]
  have hmem : ∀ i : ℕ, (fun i : ℕ => if i = 0 then s else t) i ∈ Icc a b := by
    intro i
    by_cases hi : i = 0 <;> simp [hi, hs, ht]
  unfold curveLength
  exact le_iSup_of_le (⟨1, ⟨fun i => if i = 0 then s else t, hmono, hmem⟩⟩ :
    ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b }) (by simp)

/-- Prepending a step `s ≤ s'` to a partition of `[s', t]`. -/
theorem ofReal_add_curveLength_le {f : ℝ → ℂ} {s s' t : ℝ} (h1 : s ≤ s') (h2 : s' ≤ t) :
    ENNReal.ofReal (E (f s') (f s)) + curveLength E f s' t ≤ curveLength E f s t := by
  unfold curveLength
  have hne : Nonempty (ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc s' t }) :=
    ⟨0, fun _ => s', monotone_const, fun _ => ⟨le_rfl, h2⟩⟩
  rw [ENNReal.add_iSup]
  refine iSup_le fun q => ?_
  obtain ⟨N, w, hw, hwm⟩ := q
  let x : ℕ → ℝ := fun i => Nat.casesOn i s (fun j => Nat.casesOn j s' w)
  have hx : Monotone x := by
    refine monotone_nat_of_le_succ fun n => ?_
    rcases n with _ | _ | n
    · exact h1
    · exact (hwm 0).1
    · exact hw (Nat.le_succ n)
  have hxm : ∀ i, x i ∈ Icc s t := by
    intro i
    rcases i with _ | _ | i
    · exact ⟨le_rfl, h1.trans h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1.trans (hwm i).1, (hwm i).2⟩
  refine le_trans ?_ (le_iSup_of_le (⟨N + 2, ⟨x, hx, hxm⟩⟩ :
    ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc s t }) le_rfl)
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have e : ∀ i : ℕ, ENNReal.ofReal (E (f (x (i + 1 + 1 + 1))) (f (x (i + 1 + 1)))) =
      ENNReal.ofReal (E (f (w (i + 1))) (f (w i))) := fun i => rfl
  simp only [e]
  have e0 : ENNReal.ofReal (E (f (x (0 + 1))) (f (x 0))) = ENNReal.ofReal (E (f s') (f s)) := rfl
  rw [e0]
  rw [add_comm (ENNReal.ofReal (E (f s') (f s)))]
  exact add_le_add (le_self_add) le_rfl

/-- **Subadditivity of length.** If `E` satisfies the triangle inequality, the length of a curve on
`[a, b]` is at most the sum of its lengths on `[a, m]` and `[m, b]` (for any `m`; if `m ∉ [a, b]`
one of the two lengths is the length on an interval containing `[a, b]` or the supremum over
the empty set of partitions). -/
theorem curveLength_le_add_of_ofReal_triangle
    (htri : ∀ x y z, ENNReal.ofReal (E x z) ≤ ENNReal.ofReal (E x y) + ENNReal.ofReal (E y z))
    (f : ℝ → ℂ) (a m b : ℝ) :
    curveLength E f a b ≤ curveLength E f a m + curveLength E f m b := by
  have key : ∀ (N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc a b) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (E (f (u (i + 1))) (f (u i))) ≤
        if u 0 ≤ m then curveLength E f (u 0) m + curveLength E f m b
        else curveLength E f (u 0) b := by
    intro N
    induction N with
    | zero => intro u _ _; simp
    | succ N ih =>
      intro u hu hum
      rw [Finset.sum_range_succ']
      have hih := ih (fun i => u (i + 1)) (fun i j hij => hu (Nat.succ_le_succ hij))
        (fun i => hum (i + 1))
      simp only [zero_add] at hih
      have h01 : u 0 ≤ u 1 := hu (Nat.zero_le 1)
      have hu1b : u 1 ≤ b := (hum 1).2
      by_cases h1 : u 1 ≤ m
      · have h0 : u 0 ≤ m := h01.trans h1
        simp only [h1, ↓reduceIte] at hih
        simp only [h0, ↓reduceIte]
        calc _ ≤ (curveLength E f (u 1) m + curveLength E f m b) +
              ENNReal.ofReal (E (f (u 1)) (f (u 0))) := by
              simp only [zero_add]; exact add_le_add_left hih _ |>.trans_eq' rfl
          _ = (ENNReal.ofReal (E (f (u 1)) (f (u 0))) + curveLength E f (u 1) m) +
              curveLength E f m b := by ring
          _ ≤ curveLength E f (u 0) m + curveLength E f m b :=
              add_le_add_left (ofReal_add_curveLength_le h01 h1) _ |>.trans_eq' rfl
      · have hm1 : m ≤ u 1 := (not_le.1 h1).le
        simp only [h1, ↓reduceIte] at hih
        by_cases h0 : u 0 ≤ m
        · simp only [h0, ↓reduceIte]
          have t := htri (f (u 1)) (f m) (f (u 0))
          have hR := ofReal_add_curveLength_le (E := E) (f := f) hm1 hu1b
          have hL : ENNReal.ofReal (E (f m) (f (u 0))) ≤ curveLength E f (u 0) m :=
            ofReal_le_curveLength ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
          calc _ ≤ curveLength E f (u 1) b + (ENNReal.ofReal (E (f (u 1)) (f m)) +
                ENNReal.ofReal (E (f m) (f (u 0)))) := by
                simp only [zero_add]; exact add_le_add hih t
            _ = (ENNReal.ofReal (E (f (u 1)) (f m)) + curveLength E f (u 1) b) +
                ENNReal.ofReal (E (f m) (f (u 0))) := by ring
            _ ≤ curveLength E f m b + curveLength E f (u 0) m := add_le_add hR hL
            _ = _ := add_comm _ _
        · simp only [h0, ↓reduceIte]
          have h0m : m ≤ u 0 := (not_le.1 h0).le
          calc _ ≤ curveLength E f (u 1) b + ENNReal.ofReal (E (f (u 1)) (f (u 0))) := by
                simp only [zero_add]; exact add_le_add_left hih _ |>.trans_eq' rfl
            _ = ENNReal.ofReal (E (f (u 1)) (f (u 0))) + curveLength E f (u 1) b := add_comm _ _
            _ ≤ curveLength E f (u 0) b := ofReal_add_curveLength_le h01 hu1b
  refine iSup_le fun q => ?_
  obtain ⟨N, u, hu, hum⟩ := q
  have hk := key N u hu hum
  have hau : a ≤ u 0 := (hum 0).1
  refine hk.trans ?_
  split_ifs with h0
  · exact add_le_add (curveLength_mono_aux hau le_rfl) le_rfl
  · exact (curveLength_mono_aux (not_le.1 h0).le le_rfl).trans le_add_self

private theorem curveLength_comp_le {g : ℝ → ℂ} {φ : ℝ → ℝ} (hφ : Monotone φ) {a b a' b' : ℝ}
    (hmaps : ∀ t ∈ Icc a b, φ t ∈ Icc a' b') :
    curveLength E (fun t => g (φ t)) a b ≤ curveLength E g a' b' := by
  unfold curveLength
  refine iSup_le fun q => ?_
  obtain ⟨N, u, hu, hum⟩ := q
  exact le_iSup_of_le (⟨N, ⟨fun i => φ (u i), hφ.comp hu, fun i => hmaps _ (hum i)⟩⟩ :
    ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a' b' }) le_rfl

/-- The length of a concatenation of paths is at most the sum of the lengths, for a function `E`
satisfying only the triangle inequality `ofReal (E x z) ≤ ofReal (E x y) + ofReal (E y z)`. -/
theorem pathLength_trans_le_of_ofReal_triangle
    (htri : ∀ x y z, ENNReal.ofReal (E x z) ≤ ENNReal.ofReal (E x y) + ENNReal.ofReal (E y z))
    {x y z : ℂ} (p : Path x y) (q : Path y z) :
    pathLength E (p.trans q) ≤ pathLength E p + pathLength E q := by
  have hsplit := curveLength_le_add_of_ofReal_triangle htri (p.trans q).extend 0 (1 / 2) 1
  refine hsplit.trans (add_le_add ?_ ?_)
  · rw [curveLength_eq_of_eqOn (q := fun t => p.extend (2 * t))
      (fun t ht => Path.extend_trans_of_le_half p q ht.2)]
    exact curveLength_comp_le (g := p.extend) (φ := fun t => 2 * t)
      (fun s t hst => by linarith) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  · rw [curveLength_eq_of_eqOn (q := fun t => q.extend (2 * t - 1))
      (fun t ht => Path.extend_trans_of_half_le p q ht.1)]
    exact curveLength_comp_le (g := q.extend) (φ := fun t => 2 * t - 1)
      (fun s t hst => by linarith) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- The internal metric satisfies the triangle inequality, also when infinite, when `E` satisfies
the triangle inequality `ofReal (E x z) ≤ ofReal (E x y) + ofReal (E y z)`. -/
theorem internalMetric_triangle_of_ofReal_triangle
    (htri : ∀ x y z, ENNReal.ofReal (E x z) ≤ ENNReal.ofReal (E x y) + ENNReal.ofReal (E y z))
    (U : Set ℂ) (x y z : ℂ) :
    internalMetric E U x z ≤ internalMetric E U x y + internalMetric E U y z := by
  simp only [internalMetric, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf₂ fun q hq => le_iInf₂ fun p hp => ?_
  have hpq : ∀ t, (p.trans q) t ∈ U := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  exact (iInf_le_of_le (p.trans q) (iInf_le _ hpq)).trans
    (pathLength_trans_le_of_ofReal_triangle htri p q)

/-- Reversing a path does not increase its length when `ofReal (E x y) = ofReal (E y x)`. -/
theorem pathLength_symm_le_of_ofReal_symm
    (hsymm : ∀ x y, ENNReal.ofReal (E x y) = ENNReal.ofReal (E y x)) {x y : ℂ} (p : Path x y) :
    pathLength E p.symm ≤ pathLength E p := by
  refine curveLength_le_of_partition_bound fun N u hu hum => ?_
  let v : ℕ → ℝ := fun j => 1 - u (N - j)
  have hv : Monotone v := fun i j hij => by
    have := hu (Nat.sub_le_sub_left hij N)
    simp only [v]; linarith
  have hvm : ∀ j, v j ∈ Icc (0 : ℝ) 1 := fun j =>
    ⟨by have := (hum (N - j)).2; simp only [v]; linarith,
     by have := (hum (N - j)).1; simp only [v]; linarith⟩
  have h1 : ∑ j ∈ Finset.range N, ENNReal.ofReal (E (p.extend (v (j + 1))) (p.extend (v j))) ≤
      pathLength E p := by
    unfold pathLength curveLength
    exact le_iSup_of_le (⟨N, ⟨v, hv, hvm⟩⟩ :
      ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1 }) le_rfl
  have hrefl := Finset.sum_range_reflect
    (fun i => ENNReal.ofReal (E (p.extend (1 - u i)) (p.extend (1 - u (i + 1))))) N
  calc ∑ i ∈ Finset.range N, ENNReal.ofReal (E (p.symm.extend (u (i + 1))) (p.symm.extend (u i)))
      = ∑ i ∈ Finset.range N,
          ENNReal.ofReal (E (p.extend (1 - u (i + 1))) (p.extend (1 - u i))) := by
        simp only [Path.extend_symm_apply]
    _ = ∑ i ∈ Finset.range N,
          ENNReal.ofReal (E (p.extend (1 - u i)) (p.extend (1 - u (i + 1)))) :=
        Finset.sum_congr rfl fun i _ => hsymm _ _
    _ = ∑ j ∈ Finset.range N, ENNReal.ofReal (E (p.extend (v (j + 1))) (p.extend (v j))) := by
        rw [← hrefl]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjN := Finset.mem_range.1 hj
        have e1 : N - (j + 1) = N - 1 - j := by omega
        have e2 : N - j = N - 1 - j + 1 := by omega
        simp only [v, e1, e2]
    _ ≤ pathLength E p := h1

/-- The internal metric is symmetric when `ofReal (E x y) = ofReal (E y x)`. -/
theorem internalMetric_symm_of_ofReal_symm
    (hsymm : ∀ x y, ENNReal.ofReal (E x y) = ENNReal.ofReal (E y x))
    (U : Set ℂ) (x y : ℂ) : internalMetric E U x y = internalMetric E U y x := by
  have hle (a b : ℂ) : internalMetric E U a b ≤ internalMetric E U b a := by
    unfold internalMetric
    refine le_iInf₂ fun p hp => ?_
    have hp' : ∀ t, p.symm t ∈ U := by
      intro t
      simp only [Path.symm_apply, Function.comp_apply]
      exact hp _
    exact (iInf_le_of_le p.symm (iInf_le _ hp')).trans (pathLength_symm_le_of_ofReal_symm hsymm p)
  exact le_antisymm (hle x y) (hle y x)

end LatticeProb.LQG
