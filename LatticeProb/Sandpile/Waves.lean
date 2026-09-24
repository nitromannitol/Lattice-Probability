/-
The `n`-wave (Fey-Levine-Peres wave decomposition) of the classical integer
sandpile, moved from `Exploding-Sandpiles`'s `Exploding/Support/Toppling.lean`
and the paper-independent lemmas of `Exploding/Support/Wave.lean` (that file's
own remaining content is the penultimate-wave/penultimate-cluster machinery
specific to `paper/exploding.tex`'s explosion criterion, which is not moved
here).

`wave η n z` is the `n`-wave `u_t^{(n,z)}` of `(3.1)`: `u_0 = nδ_z` and, away
from `z`, `u_{t+1}(x) = ⌊(∑_{y∼x}u_t(y) + η(x))/2d⌋`, with no `u_t(x)+1` cap.
It is the single-wave building block of the Diaconis-Fulton wave
decomposition of the parallel toppling odometer `LatticeProb.Sandpile.podo`.
-/
import LatticeProb.Sandpile.Toppling

namespace LatticeProb.Sandpile

open LatticeProb

variable {d : ℕ}

/-! ### Neighbours -/

/-- `x + eᵢ` is a neighbour of `x`. -/
theorem adj_add_unit (x : Site d) (i : Fin d) : (lattice d).Adj (x + unit i) x :=
  ⟨i, Or.inr rfl⟩

/-- `x - eᵢ` is a neighbour of `x`. -/
theorem adj_sub_unit (x : Site d) (i : Fin d) : (lattice d).Adj (x - unit i) x :=
  ⟨i, Or.inl (by abel)⟩

/-- A nonnegative function has a nonnegative neighbour sum. -/
theorem nbrSumZ_nonneg (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d) :
    0 ≤ nbrSumZ u x :=
  Finset.sum_nonneg fun _ _ => add_nonneg (hu _) (hu _)

/-- Comparing neighbour sums needs the comparison only at the neighbours. -/
theorem nbrSumZ_mono_adj (u v : Site d → ℤ) (x : Site d)
    (h : ∀ y, (lattice d).Adj y x → u y ≤ v y) : nbrSumZ u x ≤ nbrSumZ v x := by
  simp only [nbrSumZ]
  refine Finset.sum_le_sum ?_
  intro i _
  exact add_le_add (h _ (adj_add_unit x i)) (h _ (adj_sub_unit x i))

/-- A positive neighbour sum of a nonnegative function is carried by a
neighbour. -/
theorem exists_adj_pos_of_nbrSumZ_pos (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d)
    (h : 0 < nbrSumZ u x) : ∃ y, (lattice d).Adj y x ∧ 0 < u y := by
  by_contra hcon
  have hcon' : ∀ y, (lattice d).Adj y x → u y ≤ 0 := fun y hy =>
    not_lt.mp fun hpos => hcon ⟨y, hy, hpos⟩
  have hz : ∀ i : Fin d, u (x + unit i) + u (x - unit i) = 0 := by
    intro i
    have h1 : u (x + unit i) = 0 := le_antisymm (hcon' _ (adj_add_unit x i)) (hu _)
    have h2 : u (x - unit i) = 0 := le_antisymm (hcon' _ (adj_sub_unit x i)) (hu _)
    rw [h1, h2]; ring
  have hs : nbrSumZ u x = 0 := by
    simp only [nbrSumZ]
    exact Finset.sum_eq_zero fun i _ => hz i
  rw [hs] at h
  exact lt_irrefl 0 h

/-! ### The `n`-wave -/

open scoped Classical in
/-- The `n`-wave `u_t^{(n,z)}` for the background `η` starting at `z`, of
`(3.1)`: `u_0 = nδ_z` and, away from `z`,
`u_{t+1}(x) = ⌊(∑_{y∼x}u_t(y) + η(x))/2d⌋`, with no `u_t(x)+1` cap. -/
noncomputable def wave (η : Site d → ℤ) (n : ℕ) (z : Site d) : ℕ → Site d → ℤ
  | 0 => fun x => if x = z then (n : ℤ) else 0
  | t + 1 => fun x =>
      if x = z then (n : ℤ)
      else (nbrSumZ (wave η n z t) x + η x) / (2 * d)

theorem wave_zero (η : Site d → ℤ) (n : ℕ) (z : Site d) (x : Site d) :
    wave η n z 0 x = if x = z then (n : ℤ) else 0 := rfl

theorem wave_succ (η : Site d → ℤ) (n : ℕ) (z x : Site d) (t : ℕ) :
    wave η n z (t + 1) x =
      if x = z then (n : ℤ)
      else (nbrSumZ (wave η n z t) x + η x) / (2 * d) := rfl

@[simp] theorem wave_at_centre (η : Site d → ℤ) (n : ℕ) (z : Site d) (t : ℕ) :
    wave η n z t z = (n : ℤ) := by
  cases t with
  | zero => simp [wave_zero]
  | succ t => simp [wave_succ]

theorem wave_of_ne (η : Site d → ℤ) (n : ℕ) (z x : Site d) (t : ℕ) (h : x ≠ z) :
    wave η n z (t + 1) x = (nbrSumZ (wave η n z t) x + η x) / (2 * d) := by
  simp [wave_succ, h]

/-- The `n`-wave is monotone in `n`. -/
theorem wave_mono_n (η : Site d → ℤ) (hd : (0 : ℤ) < 2 * (d : ℤ)) (z : Site d) {n m : ℕ}
    (hnm : n ≤ m) (t : ℕ) (x : Site d) : wave η n z t x ≤ wave η m z t x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x = z <;> simp [wave_zero, h, Nat.cast_le.mpr hnm]
  | succ t ih =>
    by_cases h : x = z
    · simp [h]; exact_mod_cast hnm
    · simp only [wave_succ, if_neg h]
      refine Int.ediv_le_ediv hd ?_
      have h1 := nbrSumZ_mono (fun y => ih y) x
      linarith

/-- On a nonnegative background the `n`-wave is nonnegative. -/
theorem wave_nonneg (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (n : ℕ) (z : Site d)
    (t : ℕ) (x : Site d) : 0 ≤ wave η n z t x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x = z <;> simp [wave_zero, h]
  | succ t ih =>
    by_cases h : x = z
    · simp [h]
    · rw [wave_of_ne _ _ _ _ _ h]
      apply Int.ediv_nonneg _ (by positivity)
      have : 0 ≤ nbrSumZ (wave η n z t) x := by
        refine Finset.sum_nonneg ?_
        intro i _
        exact add_nonneg (ih _) (ih _)
      linarith [hη x]

/-- On a nonnegative background the `n`-wave is nondecreasing in time. -/
theorem wave_mono_t (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (hd : (0 : ℤ) < 2 * (d : ℤ))
    (n : ℕ) (z : Site d) (t : ℕ) (x : Site d) :
    wave η n z t x ≤ wave η n z (t + 1) x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x = z
    · simp [h]
    · rw [wave_zero]
      simp only [if_neg h]
      exact wave_nonneg η hη n z 1 x
  | succ t ih =>
    by_cases h : x = z
    · simp [h]
    · rw [wave_of_ne _ _ _ _ _ h, wave_of_ne _ _ _ _ _ h]
      exact Int.ediv_le_ediv hd (by linarith [nbrSumZ_mono (fun y => ih y) x])

/-- On a nonnegative background the `n`-wave is nondecreasing along any stretch
of time. -/
theorem wave_mono_time (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (hd : (0 : ℤ) < 2 * (d : ℤ))
    (n : ℕ) (z : Site d) {s t : ℕ} (hst : s ≤ t) (x : Site d) :
    wave η n z s x ≤ wave η n z t x := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact le_trans ih (wave_mono_t η hη hd n z t x)

/-- A site at which the wave equation holds is stable there. -/
theorem lap_le_of_fixed (η : Site d → ℤ) (hd : (0 : ℤ) < 2 * (d : ℤ)) (u : Site d → ℤ)
    (x : Site d) (h : u x = (nbrSumZ u x + η x) / (2 * (d : ℤ))) :
    lap u x + η x ≤ 2 * (d : ℤ) - 1 := by
  have key := Int.lt_ediv_add_one_mul_self (nbrSumZ u x + η x) hd
  rw [← h] at key
  simp only [lap]
  nlinarith [key]

/-- The `n`-wave is *stabilizable* if it is eventually constant. -/
def WaveStabilizable (η : Site d → ℤ) (n : ℕ) (z : Site d) : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T

/-- `M̂_η(z) = min{n ≥ 1 : the n-wave for η starting at z is not
stabilizable}`, the index of the last-wave. -/
noncomputable def waveThreshold (η : Site d → ℤ) (z : Site d) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}

end LatticeProb.Sandpile
