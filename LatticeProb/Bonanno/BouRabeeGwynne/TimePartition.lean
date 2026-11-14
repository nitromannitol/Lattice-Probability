/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TimePartition at commit fdb5cad; proof syntax is adjusted for the local toolchain. -/
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Finite ordered time partitions and their actual affine matching map. -/

open scoped unitInterval

namespace BouRabeeGwynne

private lemma exists_adjacent_interval {α : Type*} [LinearOrder α] (n : ℕ)
    (a : Fin (n + 2) → α) (x : α) (hfirst : a 0 ≤ x)
    (hlast : x ≤ a (Fin.last (n + 1))) :
    ∃ i : Fin (n + 1), a i.castSucc ≤ x ∧ x ≤ a i.succ := by
  induction n with
  | zero => exact ⟨0, hfirst, hlast⟩
  | succ n ih =>
    by_cases hx : x ≤ a (1 : Fin (n + 3))
    · exact ⟨0, hfirst, hx⟩
    · obtain ⟨i, hi⟩ := ih (fun j => a j.succ) (le_of_lt (lt_of_not_ge hx)) hlast
      exact ⟨i.succ, hi⟩

/-- `n+1` nondegenerate consecutive subintervals of the normalized time interval. -/
structure TimePartition (n : ℕ) where
  knots : Fin (n + 2) → unitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = 0
  last : knots (Fin.last (n + 1)) = 1

namespace TimePartition

variable {n : ℕ} (P Q : TimePartition n)

def left (i : Fin (n + 1)) : unitInterval := P.knots i.castSucc

def right (i : Fin (n + 1)) : unitInterval := P.knots i.succ

lemma left_lt_right (i : Fin (n + 1)) : P.left i < P.right i :=
  P.strictMono_knots i.castSucc_lt_succ

lemma gap_pos (i : Fin (n + 1)) : 0 < (P.right i : ℝ) - (P.left i : ℝ) :=
  sub_pos.mpr (P.left_lt_right i)

lemma right_le_left {i j : Fin (n + 1)} (hij : i < j) : P.right i ≤ P.left j :=
  P.strictMono_knots.monotone (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt hij)

lemma exists_interval (x : unitInterval) :
    ∃ i : Fin (n + 1), P.left i ≤ x ∧ x ≤ P.right i := by
  apply exists_adjacent_interval n P.knots x
  · rw [P.first]
    exact bot_le
  · rw [P.last]
    exact le_top

noncomputable def interval (x : unitInterval) : Fin (n + 1) :=
  Classical.choose (P.exists_interval x)

lemma interval_spec (x : unitInterval) :
    P.left (P.interval x) ≤ x ∧ x ≤ P.right (P.interval x) :=
  Classical.choose_spec (P.exists_interval x)

/-- The affine map of the `i`th source interval onto the `i`th target interval. -/
noncomputable def affine (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  Q.left i + ((x - P.left i) / (P.right i - P.left i)) * (Q.right i - Q.left i)

@[simp] lemma affine_left (i : Fin (n + 1)) :
    P.affine Q i (P.left i) = Q.left i := by
  simp [affine]

@[simp] lemma affine_right (i : Fin (n + 1)) :
    P.affine Q i (P.right i) = Q.right i := by
  unfold affine
  rw [div_self (P.gap_pos i).ne']
  ring

lemma affine_strictMono (i : Fin (n + 1)) : StrictMono (P.affine Q i) := by
  intro x y hxy
  unfold affine
  exact add_lt_add_right
    (mul_lt_mul_of_pos_right
      (div_lt_div_of_pos_right (sub_lt_sub_right hxy _) (P.gap_pos i))
      (Q.gap_pos i)) _

lemma affine_mem_interval (i : Fin (n + 1)) {x : ℝ}
    (hx : (P.left i : ℝ) ≤ x ∧ x ≤ P.right i) :
    (Q.left i : ℝ) ≤ P.affine Q i x ∧ P.affine Q i x ≤ Q.right i := by
  constructor
  · simpa only [P.affine_left Q i] using (P.affine_strictMono Q i).monotone hx.1
  · simpa only [P.affine_right Q i] using (P.affine_strictMono Q i).monotone hx.2

lemma affine_inverse (i : Fin (n + 1)) (x : ℝ) :
    Q.affine P i (P.affine Q i x) = x := by
  unfold affine
  (field_simp [(P.gap_pos i).ne', (Q.gap_pos i).ne']; ring)

private lemma affine_eq_of_mem_intervals_le (i j : Fin (n + 1))
    (hij : i ≤ j) {x : unitInterval}
    (hi : P.left i ≤ x ∧ x ≤ P.right i)
    (hj : P.left j ≤ x ∧ x ≤ P.right j) :
    P.affine Q i x = P.affine Q j x := by
  by_cases heq : i = j
  · rw [heq]
  have hgap := P.right_le_left (lt_of_le_of_ne hij heq)
  have hxi : x = P.right i := le_antisymm hi.2 (hgap.trans hj.1)
  have hxj : x = P.left j := le_antisymm (hi.2.trans hgap) hj.1
  have hindex : i.succ = j.castSucc :=
    P.strictMono_knots.injective (hxi.symm.trans hxj)
  calc
    P.affine Q i x = Q.right i := by rw [hxi, P.affine_right Q]
    _ = Q.left j := congrArg (fun k => (Q.knots k : ℝ)) hindex
    _ = P.affine Q j x := by rw [hxj, P.affine_left Q]

lemma affine_eq_of_mem_intervals (i j : Fin (n + 1)) {x : unitInterval}
    (hi : P.left i ≤ x ∧ x ≤ P.right i)
    (hj : P.left j ≤ x ∧ x ≤ P.right j) :
    P.affine Q i x = P.affine Q j x := by
  rcases le_total i j with hij | hji
  · exact P.affine_eq_of_mem_intervals_le Q i j hij hi hj
  · exact (P.affine_eq_of_mem_intervals_le Q j i hji hj hi).symm

/-- Explicit piecewise affine matching. Either choice at a shared knot gives
exactly the same value, as proved by `affine_eq_of_mem_intervals`. -/
noncomputable def map (x : unitInterval) : unitInterval :=
  ⟨P.affine Q (P.interval x) x,
    let h := P.affine_mem_interval Q (P.interval x) (P.interval_spec x)
    ⟨(Q.left (P.interval x)).property.1.trans h.1,
      h.2.trans (Q.right (P.interval x)).property.2⟩⟩

lemma map_eq_affine (i : Fin (n + 1)) {x : unitInterval}
    (hx : P.left i ≤ x ∧ x ≤ P.right i) :
    (P.map Q x : ℝ) = P.affine Q i x :=
  P.affine_eq_of_mem_intervals Q (P.interval x) i (P.interval_spec x) hx

lemma map_mem_interval (i : Fin (n + 1)) {x : unitInterval}
    (hx : P.left i ≤ x ∧ x ≤ P.right i) :
    Q.left i ≤ P.map Q x ∧ P.map Q x ≤ Q.right i := by
  change (Q.left i : ℝ) ≤ (P.map Q x : ℝ) ∧ (P.map Q x : ℝ) ≤ Q.right i
  rw [P.map_eq_affine Q i hx]
  exact P.affine_mem_interval Q i hx

lemma map_inverse (x : unitInterval) : Q.map P (P.map Q x) = x := by
  apply Subtype.ext
  let i := P.interval x
  have hx := P.interval_spec x
  rw [Q.map_eq_affine P i (P.map_mem_interval Q i hx), P.map_eq_affine Q i hx]
  exact P.affine_inverse Q i x

lemma map_monotone : Monotone (P.map Q) := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  let i := P.interval x
  let j := P.interval y
  have hi := P.interval_spec x
  have hj := P.interval_spec y
  have hij : i ≤ j := by
    by_contra h
    have hgap := P.right_le_left (lt_of_not_ge h)
    exact (not_le_of_gt hxy) (hj.2.trans (hgap.trans hi.1))
  by_cases heq : i = j
  · change (P.map Q x : ℝ) ≤ (P.map Q y : ℝ)
    rw [P.map_eq_affine Q i hi, P.map_eq_affine Q j hj, ← heq]
    exact (P.affine_strictMono Q i).monotone hxy.le
  · exact (P.map_mem_interval Q i hi).2.trans
      ((Q.right_le_left (lt_of_le_of_ne hij heq)).trans (P.map_mem_interval Q j hj).1)

/-- The actual increasing homeomorphic time change matching the partitions.
Its inverse is the same explicit affine construction with the partitions swapped. -/
noncomputable def timeChange : unitInterval ≃o unitInterval :=
  Equiv.toOrderIso
    { toFun := P.map Q
      invFun := Q.map P
      left_inv := P.map_inverse Q
      right_inv := Q.map_inverse P }
    (P.map_monotone Q) (Q.map_monotone P)

@[simp] lemma timeChange_apply (x : unitInterval) :
    P.timeChange Q x = P.map Q x := rfl

lemma continuous_timeChange : Continuous (P.timeChange Q) :=
  (P.timeChange Q).toHomeomorph.continuous

lemma timeChange_eq_affine (i : Fin (n + 1)) {x : unitInterval}
    (hx : P.left i ≤ x ∧ x ≤ P.right i) :
    (P.timeChange Q x : ℝ) = P.affine Q i x := P.map_eq_affine Q i hx

@[simp] lemma timeChange_left (i : Fin (n + 1)) :
    P.timeChange Q (P.left i) = Q.left i := by
  apply Subtype.ext
  rw [P.timeChange_eq_affine Q i ⟨le_rfl, (P.left_lt_right i).le⟩, P.affine_left Q]

@[simp] lemma timeChange_right (i : Fin (n + 1)) :
    P.timeChange Q (P.right i) = Q.right i := by
  apply Subtype.ext
  rw [P.timeChange_eq_affine Q i ⟨(P.left_lt_right i).le, le_rfl⟩, P.affine_right Q]

lemma timeChange_mem_interval (i : Fin (n + 1)) {x : unitInterval}
    (hx : P.left i ≤ x ∧ x ≤ P.right i) :
    Q.left i ≤ P.timeChange Q x ∧ P.timeChange Q x ≤ Q.right i :=
  P.map_mem_interval Q i hx

end TimePartition
end BouRabeeGwynne
