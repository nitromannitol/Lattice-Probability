/-
An abstract finite-range translation-invariant transition kernel on `Site d`, the recursion
it drives, and its truncated Green function.

`IsLatticeKernel r K` says that `K` is nonnegative, supported within sup-distance `r` of the
starting point, stochastic (each row sums to `1` over its support box), and invariant under
every translation of the lattice. `kOp`, `kIter`, `kGreen` and `kSol` are `(Kf)(x)`,
`K^j(0, ·)`, `g^K_n = ∑_{j<n} K^j(0, ·)` and the solution of the recursion `v_0 = 0`,
`v_{n+1} = (η + Kv_n)⁺`.

Any repository running a recursion driven by a general finite-range translation-invariant
kernel rather than a fixed kernel (such as the simple random walk kernel) can instantiate
these definitions at its own `K`, rather than redo the abstraction for its own special case.

Moved from Parking-Sharpness (`Parking.IsLatticeKernel` and its companions of
`Parking/Support/Kernel.lean`; `Parking.greenMax`, tied to the specific simple-random-walk
Green function, is not moved).
-/
import LatticeProb.ParticleHole
import LatticeProb.Walk.Shells

noncomputable section

namespace LatticeProb.Walk

/-- `K` is a finite-range translation-invariant stochastic kernel of range `r`. -/
def IsLatticeKernel {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) : Prop :=
  (∀ y x, 0 ≤ K y x) ∧
  (∀ y x, K y x ≠ 0 → supNorm (x - y) ≤ r) ∧
  (∀ y, ∑ x ∈ boxFinset y r, K y x = 1) ∧
  (∀ v y x, K (y + v) (x + v) = K y x)

/-- `(K f)(x) = ∑_y K(x, y) f(y)`. -/
def kOp {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) (f : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ y ∈ boxFinset x r, K x y * f y

/-- `K^j(0, x)`, the `j`-step transition kernel iterate started at the origin. -/
def kIter {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => ∑ y ∈ boxFinset x r, kIter r K j y * K y x

/-- The truncated Green function `g^K_n(z) = ∑_{j<n} K^j(0, z)`. -/
def kGreen {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) (n : ℕ) (z : Site d) : ℝ :=
  ∑ j ∈ Finset.range n, kIter r K j z

/-- The solution of `v_0 = 0`, `v_{n+1} = (η + K v_n)⁺`. -/
def kSol {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (η x + kOp r K (kSol r K η n) x)

/-- The `l²` norm of a function on the lattice. -/
def l2Norm {d : ℕ} (f : Site d → ℝ) : ℝ := Real.sqrt (∑' x : Site d, f x ^ 2)

/-- The sup norm of a function on the lattice. -/
def supAbs {d : ℕ} (f : Site d → ℝ) : ℝ := ⨆ x : Site d, |f x|

end LatticeProb.Walk
