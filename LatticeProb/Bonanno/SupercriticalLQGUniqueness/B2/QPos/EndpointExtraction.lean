/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.EndpointExtraction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointCost

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 


theorem annular_indices_of_nearest_neighbor
    (f : ℕ → ℤ) (N : ℕ) (r R : ℤ)
    (hrR : r + 1 < R) (hstart : f 0 ≤ r) (hend : R ≤ f N)
    (hstep : ∀ i < N, f (i + 1) ≤ f i + 1) :
    ∃ s t : ℕ, 0 < s ∧ s ≤ t ∧ t ≤ N ∧
      f s = r + 1 ∧ f t = R ∧
      (∀ i, s ≤ i → i ≤ t → r + 1 ≤ f i ∧ f i ≤ R) := by
  classical
  let ht : ∃ i : ℕ, R ≤ f i := ⟨N, hend⟩
  let t := Nat.find ht
  have htN : t ≤ N := Nat.find_min' ht hend
  have htprop : R ≤ f t := Nat.find_spec ht
  have ht0 : 0 < t := by
    by_contra h
    have h0 : t = 0 := Nat.eq_zero_of_not_pos h
    rw [h0] at htprop
    omega
  have hprev : f (t - 1) < R := by
    apply lt_of_not_ge
    intro h
    exact Nat.find_min ht (Nat.sub_lt ht0 (by omega)) h
  have htval : f t = R := by
    have hsucc : t - 1 + 1 = t := by omega
    have hs := hstep (t - 1) (by omega)
    rw [hsucc] at hs
    omega
  let u := Nat.findGreatest (fun i => f i ≤ r) t
  have hu : f u ≤ r := by
    dsimp [u]
    exact Nat.findGreatest_spec (P := fun i => f i ≤ r)
      (m := 0) (Nat.zero_le t) hstart
  have hut : u ≤ t := Nat.findGreatest_le t
  have hu_lt : u < t := by
    by_contra h
    have heq : u = t := by omega
    rw [heq, htval] at hu
    omega
  have hnext : r < f (u + 1) := by
    by_contra h
    have hh : f (u + 1) ≤ r := by omega
    have hmax := Nat.le_findGreatest (P := fun i => f i ≤ r) (n := t)
      (m := u + 1) (by omega) hh
    omega
  have hnext_eq : f (u + 1) = r + 1 := by
    have hs := hstep u (by omega)
    omega
  refine ⟨u + 1, t, by omega, by omega, htN, hnext_eq, htval, ?_⟩
  intro i hsi hit
  constructor
  · have hri : r < f i := by
      by_contra h
      have hh : f i ≤ r := by omega
      have hmax := Nat.le_findGreatest (P := fun j => f j ≤ r) (n := t)
        (m := i) hit hh
      omega
    omega
  · by_cases hit' : i = t
    · rw [hit', htval]
    · have hiR : f i < R := by
        apply lt_of_not_ge
        intro h
        exact Nat.find_min ht (by omega) h
      omega

 
def latticeSupRadius (z : ℤ × ℤ) : ℤ := max |z.1| |z.2|

theorem latticeSupRadius_step {z w : ℤ × ℤ}
    (h : latticeAdjacent z w) :
    latticeSupRadius w ≤ latticeSupRadius z + 1 := by
  rcases h with h | h | h | h
  · obtain ⟨hx, hy⟩ := h
    dsimp [latticeSupRadius]
    rw [hx, hy]
    have ha : |z.1 + 1| ≤ |z.1| + 1 := by
      simpa using (abs_add_le z.1 (1 : ℤ))
    omega
  · obtain ⟨hx, hy⟩ := h
    dsimp [latticeSupRadius]
    rw [hx, hy]
    have ha : |z.1 - 1| ≤ |z.1| + 1 := by
      simpa [sub_eq_add_neg] using (abs_add_le z.1 (-1 : ℤ))
    omega
  · obtain ⟨hx, hy⟩ := h
    dsimp [latticeSupRadius]
    rw [hx, hy]
    have ha : |z.2 + 1| ≤ |z.2| + 1 := by
      simpa using (abs_add_le z.2 (1 : ℤ))
    omega
  · obtain ⟨hx, hy⟩ := h
    dsimp [latticeSupRadius]
    rw [hx, hy]
    have ha : |z.2 - 1| ≤ |z.2| + 1 := by
      simpa [sub_eq_add_neg] using (abs_add_le z.2 (-1 : ℤ))
    omega

 

theorem lattice_annular_indices
    (p : ℕ → ℤ × ℤ) (N : ℕ) (r R : ℤ)
    (hrR : r + 1 < R) (hstart : latticeSupRadius (p 0) ≤ r)
    (hend : R ≤ latticeSupRadius (p N))
    (hpath : ∀ i < N, latticeAdjacent (p i) (p (i + 1))) :
    ∃ s t : ℕ, 0 < s ∧ s ≤ t ∧ t ≤ N ∧
      latticeSupRadius (p s) = r + 1 ∧ latticeSupRadius (p t) = R ∧
      (∀ i, s ≤ i → i ≤ t →
        r + 1 ≤ latticeSupRadius (p i) ∧ latticeSupRadius (p i) ≤ R) := by
  exact annular_indices_of_nearest_neighbor
    (fun i => latticeSupRadius (p i)) N r R hrR hstart hend
    (fun i hi => latticeSupRadius_step (hpath i hi))

end SupercriticalLQGUniqueness.B2.QPos
