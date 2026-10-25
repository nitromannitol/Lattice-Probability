module

public import LatticeProb.Sandpile.Toppling

@[expose] public section

/-!
# Generic facts about the parallel toppling process

For the parallel toppling odometer `podo` and sandpile `pconf` of `Toppling`, this file records
the facts that need no wave or radius input:

* `dirac_nonneg`: the unit mass is nonnegative;
* `podo_succ_eq_min_floor` and `podo_succ_le_floor`: wherever the sandpile is nonnegative, one
  step of the odometer is the minimum of "one more toppling" and the floor of
  `(∑_{y∼x} v_t(y) + s₀(x)) / 2d`, and in particular it is at most that floor;
* `podo_mono`: the odometer is nondecreasing across any time gap, by `monotone_nat_of_le_succ`;
* `podo_eq_zero`: a zero initial pile has zero odometer at every time.

Nonnegativity of the sandpile is `pconf_nonneg` in `Nonnegative`.
-/

namespace LatticeProb.Sandpile

open LatticeProb

variable {d : ℕ}

/-- The unit mass is nonnegative. -/
theorem dirac_nonneg (z x : Site d) : 0 ≤ dirac z x := by
  unfold dirac
  split_ifs <;> norm_num

/-- Wherever the sandpile is nonnegative, the parallel odometer's one-step update is the minimum
of "one more toppling" and the floor of `(∑_{y∼x} v_t(y) + s₀(x)) / 2d`. -/
theorem podo_succ_eq_min_floor (s0 : Site d → ℤ) (hdz : (0 : ℤ) < 2 * (d : ℤ))
    (t : ℕ) (x : Site d) (hp : 0 ≤ pconf s0 t x) :
    podo s0 (t + 1) x =
      min (podo s0 t x + 1) ((nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ))) := by
  have hpc : pconf s0 t x = nbrSumZ (podo s0 t) x + s0 x - 2 * (d : ℤ) * podo s0 t x := by
    simp only [pconf, lap]
    ring
  have hiff : podo s0 t x + 1 ≤ (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)) ↔
      2 * (d : ℤ) ≤ pconf s0 t x := by
    rw [Int.le_ediv_iff_mul_le hdz, hpc]
    constructor <;> intro h <;> linarith
  have hfl : podo s0 t x ≤ (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)) := by
    rw [Int.le_ediv_iff_mul_le hdz]
    rw [hpc] at hp
    linarith
  rw [podo_succ]
  split_ifs with hc
  · rw [min_eq_left (hiff.2 hc)]
  · have hneg : ¬ (podo s0 t x + 1 ≤ (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ))) :=
      fun h => hc (hiff.1 h)
    have hlt : (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)) < podo s0 t x + 1 :=
      not_le.mp hneg
    have hle : (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)) ≤ podo s0 t x :=
      Int.lt_add_one_iff.mp hlt
    have hmin : min (podo s0 t x + 1) ((nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)))
        = (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)) := min_eq_right (by linarith)
    rw [hmin, add_zero]
    exact le_antisymm hfl hle

/-- The floor bound: the next odometer value is at most `(∑_{y∼x} v_t(y) + s₀(x)) / 2d`. -/
theorem podo_succ_le_floor (s0 : Site d → ℤ) (hdz : (0 : ℤ) < 2 * (d : ℤ))
    (t : ℕ) (x : Site d) (hp : 0 ≤ pconf s0 t x) :
    podo s0 (t + 1) x ≤ (nbrSumZ (podo s0 t) x + s0 x) / (2 * (d : ℤ)) := by
  rw [podo_succ_eq_min_floor s0 hdz t x hp]
  exact min_le_right _ _

/-- The parallel toppling odometer is nondecreasing in time across any gap. -/
theorem podo_mono (s0 : Site d → ℤ) {s t : ℕ} (hst : s ≤ t) (x : Site d) :
    podo s0 s x ≤ podo s0 t x :=
  monotone_nat_of_le_succ (fun t => podo_mono_step s0 t x) hst

/-- A zero initial pile has zero odometer at every time: no site ever holds `2d` chips,
since the Laplacian of the zero odometer vanishes. -/
theorem podo_eq_zero (s0 : Site d → ℤ) (hd : 0 < d) (hs : ∀ x, s0 x = 0) :
    ∀ t : ℕ, ∀ x : Site d, podo s0 t x = 0 := by
  have hdz : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    linarith
  intro t
  induction t with
  | zero => intro x; rfl
  | succ t ih =>
    intro x
    have hlap : lap (podo s0 t) x = 0 := by simp [lap, nbrSumZ, ih]
    have hpc0 : pconf s0 t x = 0 := by simp [pconf, hlap, hs]
    rw [podo_succ, ih x, hpc0, if_neg (not_le.mpr hdz), add_zero]

end LatticeProb.Sandpile
