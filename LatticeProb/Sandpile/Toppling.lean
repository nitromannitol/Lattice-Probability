/-
The classical (integer, Abelian) sandpile under parallel toppling on `ℤ^d`,
moved from `Exploding-Sandpiles`'s `Exploding/Support/Toppling.lean` and
`Exploding/Support/SubFodo*.lean`.  `LatticeProb.Graph` already has a
*divisible* sandpile (`LatticeProb.Graph.topple`/`config`/`odometer`, threshold
`1`, continuous mass, general locally finite graph); this is the different,
classical model, in which a site holds an integer number of chips and fires
when it holds at least as many chips as it has neighbours.

A *background* is a function `η : Site d → ℤ`; a *sandpile* is a function
`s : Site d → ℤ` counting chips.  A site *fires* when it holds at least `2d`
chips (`2d` being `(LatticeProb.lattice d).degree x` at every site): firing
removes `2d` chips from it and adds one chip to each neighbour.  Parallel
toppling fires every unstable site at once.

The objects here, with the display of `paper/exploding.tex` they transcribe:

* `nbrSumZ`, `lap`   the integer neighbour sum and the lattice Laplacian
  `Δu(x) = ∑_{y∼x}(u(y)-u(x))`;
* `podo`, `pconf`   the parallel toppling odometer `v_t` and sandpile `s_t`
  of `(1.1)`, for the initial sandpile `s_0`;
* `Stabilizable`, `Robust`, `Explosive`   the notions of the Overview;
* `explosionThreshold`   the threshold `M_η` of `(1.3)`;
* `fodo`, `fconf`   the `S`-frozen odometer `w_t` and sandpile `s_t'` of
  `(2.3)`.

Integer division `/` on `ℤ` rounds towards `-∞`, so it is the floor `⌊·⌋` of
the paper: `(-7 : ℤ) / 2 = -4`.

`nbrSumZ` and `lap` are exactly `Dynamic-Dimensional-Reduction`'s
`DimRed/Support/Basic.lean`'s `nbrSum`/`lap` (`Δ^{(d)}u(x) = -2du(x) +
nbrSum u(x)`, the same sum reassociated): two independent formalizations
introduced the same integer discrete Laplacian under the same names for
different papers.  `Random-Abelian-Sandpile`'s `RandomSandpile/Support/
Basic.lean` also has its own real-valued `Δ`/`Δi` and an integer
`laplacianInt` defined via `SimpleGraph.neighborFinset`; `lap` below is the
`Site d`/`lattice d` value of that same discrete Laplacian, stated in the
paper's own direction-sum form rather than through `neighborFinset`, since
that is the form the toppling recursion is proved in.

The name `LatticeProb.nbrSum` is already taken (the library's existing
real-valued neighbour sum, `LatticeProb/Site.lean`); the integer-valued sum
here is `nbrSumZ`, matching the source repo's own choice of name for exactly
this reason.
-/
import LatticeProb.Site

namespace LatticeProb.Sandpile

open LatticeProb

variable {d : ℕ}

/-- The unit mass at `z`. -/
def dirac (z : Site d) : Site d → ℤ := fun x => if x = z then 1 else 0

@[simp] theorem dirac_self (z : Site d) : dirac z z = 1 := by simp [dirac]

theorem dirac_of_ne {x z : Site d} (h : x ≠ z) : dirac z x = 0 := by simp [dirac, h]

/-- The sum of `u` over the `2d` neighbours of `x`, direction by direction, so
that `d = 0` is not special-cased. -/
def nbrSumZ (u : Site d → ℤ) (x : Site d) : ℤ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

theorem nbrSumZ_mono {u v : Site d → ℤ} (h : ∀ y, u y ≤ v y) (x : Site d) :
    nbrSumZ u x ≤ nbrSumZ v x :=
  Finset.sum_le_sum fun _ _ => add_le_add (h _) (h _)

theorem nbrSumZ_add_const (u : Site d → ℤ) (c : ℤ) (x : Site d) :
    nbrSumZ (fun y => c + u y) x = 2 * (d : ℤ) * c + nbrSumZ u x := by
  simp only [nbrSumZ]
  rw [show (fun i : Fin d => (c + u (x + unit i)) + (c + u (x - unit i)))
        = (fun i : Fin d => 2 * c + (u (x + unit i) + u (x - unit i))) from
      funext fun i => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp
  ring

theorem nbrSumZ_congr {u v : Site d → ℤ} (h : ∀ y, u y = v y) (x : Site d) :
    nbrSumZ u x = nbrSumZ v x := by
  simp only [nbrSumZ, h]

/-- The lattice Laplacian `Δu(x) = ∑_{y∼x}(u(y)-u(x))`. -/
def lap (u : Site d → ℤ) (x : Site d) : ℤ := nbrSumZ u x - 2 * d * u x

theorem lap_eq (u : Site d → ℤ) (x : Site d) :
    lap u x = nbrSumZ u x - 2 * d * u x := rfl

/-- The Laplacian is the sum of its coordinatewise second differences, moved
from `Dynamic-Dimensional-Reduction`'s `DimRed/Support/SecondDiff.lean:24
lap_eq_sum_second_diff`, proved there for the same object (`DimRed.lap`,
`DimRed.nbrSum`) under different names, with no dependence on that repo's
hypercube or simplex. -/
theorem lap_eq_sum_second_diff (u : Site d → ℤ) (x : Site d) :
    lap u x = ∑ i : Fin d, (-2 * u x + u (x + unit i) + u (x - unit i)) := by
  simp only [lap, nbrSumZ]
  calc
    (∑ i : Fin d, (u (x + unit i) + u (x - unit i))) - 2 * (d : ℤ) * u x =
        (∑ _i : Fin d, (-2 : ℤ) * u x) +
            ∑ i : Fin d, (u (x + unit i) + u (x - unit i)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    _ = ∑ i : Fin d, (-2 * u x + u (x + unit i) + u (x - unit i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The parallel toppling odometer `v_t` for the initial sandpile `s₀`:
`v_0 = 0` and `v_{t+1} = v_t + 1{s_t ≥ 2d}`, where `s_t = s₀ + Δv_t`. -/
def podo (s0 : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      podo s0 t x + (if 2 * d ≤ s0 x + lap (podo s0 t) x then 1 else 0)

/-- The parallel toppling sandpile `s_t = s₀ + Δv_t`. -/
def pconf (s0 : Site d → ℤ) (t : ℕ) (x : Site d) : ℤ := s0 x + lap (podo s0 t) x

@[simp] theorem podo_zero (s0 : Site d → ℤ) : podo s0 0 = fun _ => 0 := rfl

theorem podo_succ (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    podo s0 (t + 1) x = podo s0 t x + (if 2 * d ≤ pconf s0 t x then 1 else 0) := rfl

/-- The parallel toppling odometer is nondecreasing in time. -/
theorem podo_mono_step (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    podo s0 t x ≤ podo s0 (t + 1) x := by
  rw [podo_succ]
  exact le_add_of_nonneg_right (by positivity)

/-- `s₀` is *stabilizable*: the parallel toppling odometer is eventually
constant. -/
def Stabilizable (s0 : Site d → ℤ) : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T

/-- A background is *robust* if `η + n δ₀` is stabilizable for every `n ≥ 1`. -/
def Robust (η : Site d → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Stabilizable (fun x => η x + n * dirac (0 : Site d) x)

/-- A background is *explosive* if it is not robust. -/
def Explosive (η : Site d → ℤ) : Prop := ¬ Robust η

/-- The explosion threshold `M_η = min{n ≥ 1 : η + n δ₀ is not stabilizable}`
of `(1.3)`.  Carry `Explosive η` to know the set is nonempty. -/
noncomputable def explosionThreshold (η : Site d → ℤ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => η x + n * dirac (0 : Site d) x)}

open scoped Classical in
/-- The `S`-frozen parallel toppling odometer `w_t` of `(2.3)`: the odometer is
held at `w₀` on `S`, and `s_t' = s₀ + Δw_t`. -/
noncomputable def fodo (S : Set (Site d)) (s0 w0 : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => w0
  | t + 1 => fun x =>
      if x ∈ S then w0 x
      else fodo S s0 w0 t x + (if 2 * d ≤ s0 x + lap (fodo S s0 w0 t) x then 1 else 0)

/-- The `S`-frozen parallel toppling sandpile `s_t' = s₀ + Δw_t`. -/
noncomputable def fconf (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) (x : Site d) : ℤ :=
  s0 x + lap (fodo S s0 w0 t) x

@[simp] theorem fodo_zero (S : Set (Site d)) (s0 w0 : Site d → ℤ) : fodo S s0 w0 0 = w0 := rfl

open scoped Classical in
theorem fodo_succ (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    fodo S s0 w0 (t + 1) x =
      if x ∈ S then w0 x
      else fodo S s0 w0 t x + (if 2 * d ≤ fconf S s0 w0 t x then 1 else 0) := rfl

/-- On the frozen set the frozen odometer never moves. -/
theorem fodo_of_mem (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) {x : Site d} (hx : x ∈ S) :
    fodo S s0 w0 t x = w0 x := by
  cases t with
  | zero => rfl
  | succ t => rw [fodo_succ]; exact if_pos hx

/-- A frozen odometer started from a nonnegative initial condition stays
nonnegative. -/
theorem fodo_nonneg (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    (hw0nn : ∀ x, 0 ≤ w0 x) (t : ℕ) (x : Site d) :
    0 ≤ fodo S s0 w0 t x := by
  induction t generalizing x with
  | zero => exact hw0nn x
  | succ t ih =>
    rw [fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx]; exact hw0nn x
    · rw [if_neg hx]
      have := ih x
      split_ifs <;> linarith

/-- Off the frozen set the frozen odometer takes one parallel-toppling step. -/
theorem fodo_succ_of_notMem (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) {x : Site d}
    (hx : x ∉ S) :
    fodo S s0 w0 (t + 1) x =
      fodo S s0 w0 t x + (if 2 * d ≤ fconf S s0 w0 t x then 1 else 0) := by
  rw [fodo_succ, if_neg hx]

/-- A site off the frozen set with at least `2d` chips topples at the next
step. -/
theorem fodo_topple_of_ge (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) {x : Site d}
    (hx : x ∉ S) (h0 : fodo S s0 w0 t x = 0) (hge : 2 * d ≤ fconf S s0 w0 t x) :
    fodo S s0 w0 (t + 1) x = 1 := by
  classical
  rw [fodo_succ, if_neg hx, if_pos hge, h0]
  ring

end LatticeProb.Sandpile
