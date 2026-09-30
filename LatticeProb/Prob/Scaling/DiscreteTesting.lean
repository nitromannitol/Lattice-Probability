/- Summation by parts for finitely supported lattice tests and discrete time.

Moved from Parking-Sharpness.
-/
import LatticeProb.Site
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.BigOperators.Intervals

open LatticeProb
noncomputable section
namespace LatticeProb.Scaling.DiscreteTesting

/-- Discrete integration by parts, including its two endpoint terms. -/
theorem sum_time_difference (f ψ : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (f (n + 1) - f n) * ψ (n + 1)) =
      f N * ψ N - f 0 * ψ 0 -
        ∑ n ∈ Finset.range N, f n * (ψ (n + 1) - ψ n) := by
  have h := Finset.sum_range_sub (fun n => f n * ψ n) N
  have heq : (∑ n ∈ Finset.range N, (f (n + 1) - f n) * ψ (n + 1)) +
      (∑ n ∈ Finset.range N, f n * (ψ (n + 1) - ψ n)) =
      ∑ n ∈ Finset.range N, (f (n + 1) * ψ (n + 1) - f n * ψ n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  linarith

/-- Sum the discrete time identity over space using finite-support tests. -/
theorem sum_tsum_time_difference {α : Type*} (f ψ : ℕ → α → ℝ)
    (hψ : ∀ n, Function.HasFiniteSupport (ψ n)) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑' x, ψ (n + 1) x * (f (n + 1) x - f n x)) +
      (∑ n ∈ Finset.range N, ∑' x, f n x * (ψ (n + 1) x - ψ n x)) =
      (∑' x, f N x * ψ N x) - ∑' x, f 0 x * ψ 0 x := by
  have hI : ∀ m n, Summable (fun x => f m x * ψ n x) := fun m n =>
    summable_of_hasFiniteSupport ((hψ n).mul_right (f m))
  have hA : ∀ n, Summable fun x => ψ (n + 1) x * (f (n + 1) x - f n x) :=
    fun n => summable_of_hasFiniteSupport ((hψ (n + 1)).mul_left _)
  have hB : ∀ n, Summable fun x => f n x * (ψ (n + 1) x - ψ n x) := by
    intro n
    simpa only [mul_sub] using (hI n (n + 1)).sub (hI n n)
  calc
    _ = ∑ n ∈ Finset.range N, ((∑' x, f (n + 1) x * ψ (n + 1) x) -
        ∑' x, f n x * ψ n x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [← (hA n).tsum_add (hB n), ← (hI (n + 1) (n + 1)).tsum_sub (hI n n)]
      apply tsum_congr
      intro x
      ring
    _ = _ := Finset.sum_range_sub (fun n => ∑' x, f n x * ψ n x) N

/-- The symmetric walk operator is self-adjoint against a finite-support test;
the field itself need not be summable. -/
theorem tsum_mul_walkOp {d : ℕ} (f ψ : Site d → ℝ)
    (hψ : Function.HasFiniteSupport ψ) :
    (∑' x : Site d, ψ x * walkOp f x) = ∑' x : Site d, walkOp ψ x * f x := by
  have hsum1 : ∀ i : Fin d, Summable fun x : Site d => ψ x * f (x + unit i) :=
    fun i => summable_of_hasFiniteSupport (hψ.mul_left _)
  have hsum2 : ∀ i : Fin d, Summable fun x : Site d => ψ x * f (x - unit i) :=
    fun i => summable_of_hasFiniteSupport (hψ.mul_left _)
  have hshift : ∀ i : Fin d,
      (∑' x : Site d, ψ x * f (x + unit i)) = ∑' x : Site d, ψ (x - unit i) * f x := by
    intro i
    rw [← (Equiv.addRight (unit i)).tsum_eq (fun x : Site d => ψ (x - unit i) * f x)]
    exact tsum_congr fun x => by simp
  have hshift' : ∀ i : Fin d,
      (∑' x : Site d, ψ x * f (x - unit i)) = ∑' x : Site d, ψ (x + unit i) * f x := by
    intro i
    rw [← (Equiv.subRight (unit i)).tsum_eq (fun x : Site d => ψ (x + unit i) * f x)]
    exact tsum_congr fun x => by simp
  have hsumA : ∀ i : Fin d, Summable fun x : Site d => ψ (x - unit i) * f x := by
    intro i
    rw [← (Equiv.addRight (unit i)).summable_iff]
    exact (hsum1 i).congr fun x => by simp
  have hsumB : ∀ i : Fin d, Summable fun x : Site d => ψ (x + unit i) * f x := by
    intro i
    rw [← (Equiv.subRight (unit i)).summable_iff]
    exact (hsum2 i).congr fun x => by simp
  have hpt : ∀ x : Site d, ψ x * walkOp f x =
      (∑ i : Fin d, (ψ x * f (x + unit i) + ψ x * f (x - unit i))) / (2 * d) := by
    intro x
    simp only [walkOp, nbrSum, ← mul_div_assoc, Finset.mul_sum, mul_add]
  rw [tsum_congr hpt, tsum_div_const]
  rw [Summable.tsum_finsetSum fun i _ => (hsum1 i).add (hsum2 i)]
  simp_rw [(hsum1 _).tsum_add (hsum2 _), hshift, hshift']
  simp_rw [← (hsumA _).tsum_add (hsumB _)]
  rw [← Summable.tsum_finsetSum fun i _ => (hsumA i).add (hsumB i), ← tsum_div_const]
  apply tsum_congr
  intro x
  simp only [walkOp, nbrSum, div_mul_eq_mul_div, Finset.sum_mul, add_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Finite-support testing makes the adjoint pairing summable. -/
theorem summable_walkOp_mul {d : ℕ} (f ψ : Site d → ℝ)
    (hψ : Function.HasFiniteSupport ψ) :
    Summable (fun x : Site d => walkOp ψ x * f x) := by
  have hplus : ∀ i : Fin d, Summable fun x : Site d => ψ (x + unit i) * f x :=
    fun i => summable_of_hasFiniteSupport
      ((hψ.fun_comp_of_injective (Equiv.addRight (unit i)).injective).mul_left f)
  have hminus : ∀ i : Fin d, Summable fun x : Site d => ψ (x - unit i) * f x :=
    fun i => summable_of_hasFiniteSupport
      ((hψ.fun_comp_of_injective (Equiv.subRight (unit i)).injective).mul_left f)
  have hsum := (summable_sum (s := Finset.univ)
    (fun i _ => (hplus i).add (hminus i))).div_const (2 * (d : ℝ))
  simpa only [walkOp, nbrSum, div_mul_eq_mul_div, Finset.sum_mul, add_mul] using hsum

end LatticeProb.Scaling.DiscreteTesting
