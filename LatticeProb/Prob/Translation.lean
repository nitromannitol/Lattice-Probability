/-
The ergodic zero-one law on the lattice: an event of an i.i.d. field on `ℤ^d`
that is invariant under a single nonzero translation has probability `0` or `1`.

The general statement is `LatticeProb.ergodic_coordShift_infinitePi`, which needs
the reindexing to be injective, to preserve the one-site laws, and to push every
finite set off itself after enough iterations.  Translation by a nonzero vector
does all three: it is injective, the one-site law does not depend on the site,
and a finite set is contained in a box, which `n` translations leave once `n`
exceeds twice the radius of the box.
-/
import LatticeProb.IID
import LatticeProb.Prob.ZeroOne

noncomputable section

namespace LatticeProb

open MeasureTheory

variable {d : ℕ}

/-- Translating `n` times translates by `n • v`. -/
theorem iterate_add_right (v : Site d) (n : ℕ) (x : Site d) :
    (fun y : Site d => y + v)^[n] x = x + n • v := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, ih, succ_nsmul]; abel

/-- A nonzero translation pushes any finite set of sites off itself. -/
theorem exists_add_nsmul_notMem {v : Site d} (hv : v ≠ 0) (s : Finset (Site d)) :
    ∃ n : ℕ, ∀ x ∈ s, x + n • v ∉ s := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin d, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  set M : ℕ := s.sup fun x => (x i).natAbs with hM
  refine ⟨2 * M + 1, fun x hx hmem => ?_⟩
  set N : ℤ := 2 * (M : ℤ) + 1 with hN
  have hxM : |x i| ≤ (M : ℤ) := by
    have h := Finset.le_sup (f := fun x : Site d => (x i).natAbs) hx
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  have hcoord : (x + (2 * M + 1 : ℕ) • v) i = x i + N * v i := by
    show x i + ((2 * M + 1 : ℕ) : ℤ) * v i = x i + N * v i
    rw [hN]; push_cast; ring
  have hyM : |x i + N * v i| ≤ (M : ℤ) := by
    have h := Finset.le_sup (f := fun x : Site d => (x i).natAbs) hmem
    rw [← hcoord, Int.abs_eq_natAbs]
    exact_mod_cast h
  have hv1 : 1 ≤ |v i| := Int.one_le_abs hi
  have hNpos : (0 : ℤ) ≤ N := by rw [hN]; positivity
  have hbig : N ≤ N * |v i| := by nlinarith
  have habs : N * |v i| = |N * v i| := by
    rw [abs_mul, abs_of_nonneg hNpos]
  have htri : |N * v i| ≤ |x i + N * v i| + |x i| := by
    have h := abs_add_le (x i + N * v i) (-(x i))
    simpa using h
  rw [hN] at hbig
  linarith

/-- The zero-one law for translations.  An event of the i.i.d. field on `ℤ^d`
with one-site law `μ` that is invariant under translation by a single nonzero
vector has probability `0` or `1`. -/
theorem measure_zero_or_one_of_translationInvariant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {v : Site d} (hv : v ≠ 0)
    {A : Set (Site d → X)} (hA : MeasurableSet A)
    (hinv : coordShift (fun x : Site d => x + v) ⁻¹' A = A) :
    iidLaw d μ A = 0 ∨ iidLaw d μ A = 1 := by
  have herg : Ergodic (coordShift (X := X) fun x : Site d => x + v)
      (Measure.infinitePi fun _ : Site d => μ) := by
    refine ergodic_coordShift_infinitePi (fun _ : Site d => μ)
      (fun a b hab => by simpa using hab) (fun _ => rfl) fun s => ?_
    obtain ⟨n, hn⟩ := exists_add_nsmul_notMem hv s
    exact ⟨n, fun x hx => by rw [iterate_add_right]; exact hn x hx⟩
  rcases herg.ae_empty_or_univ hA hinv with h | h
  · left
    show (Measure.infinitePi fun _ : Site d => μ) A = 0
    rw [measure_congr h, measure_empty]
  · right
    show (Measure.infinitePi fun _ : Site d => μ) A = 1
    rw [measure_congr h]
    exact measure_univ

/-- An event invariant under every translation has probability `0` or `1`, as
soon as there is a nonzero vector to translate by. -/
theorem measure_zero_or_one_of_allTranslationInvariant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {v : Site d} (hv : v ≠ 0)
    {A : Set (Site d → X)} (hA : MeasurableSet A)
    (hinv : ∀ w : Site d, coordShift (fun x : Site d => x + w) ⁻¹' A = A) :
    iidLaw d μ A = 0 ∨ iidLaw d μ A = 1 :=
  measure_zero_or_one_of_translationInvariant μ hv hA (hinv v)

end LatticeProb

end
