/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.IndexSet at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# The index set `Ξ` of the discrete-time walk reflected off `∞`
(Gwynne–Sung, arXiv:2506.18827, Section 3.2, equations (3.9)–(3.14), and (3.24))

## The design decision

The paper fixes a starting vertex `z`, sets `n_z := min{n : z ∈ VG_n}`, and for
`n ≥ m ≥ n_z` defines the times `J^{m,n}_k` of (3.9) from the level-`n` chain `Y^n` and the
vertex set `VG_m`.  It then declares `(n, j) ∼ (m, k)` when `m < n` and `j = J^{m,n}_k` (or
symmetrically), writes `Ξ` for the set of equivalence classes, orders `Ξ` by comparing the
time coordinates of representatives at a common level, and sets `Y_ξ := Y^n_j` for any
`(n, j) ∈ ξ` (3.13).  `Ξ` is a *random* countable linear order: it depends on the sample
path through the `J^{m,n}`, and its order type depends on the excursion lengths.

### The encoding chosen here

Levels are re-indexed so that `n = n_z + i` becomes `i : ℕ`; the data are an exhaustion
`Gs : ℕ → Set V` (`Gs i = VG_{n_z+i}`) and a family of paths `Y : ℕ → ℕ → V`
(`Y i = Y^{n_z+i}`).  Nothing in this file is probabilistic: everything is a deterministic
function of `(Gs, Y)`, and the a.s. properties of the coupling enter only as explicit
hypotheses (`Consistent`, monotonicity of `Gs`, recurrence of the level-`0` path).

* **Ambient index set.**  `Ξ₀ := Lex (ℕ →₀ ℕ)`, finitely supported sequences of naturals in
  lexicographic order (first differing coordinate decides).  This is a *fixed*, countable
  linear order with least element `0`.  It is the universal "address space" of the excursion
  tree: an address `a` is read as "level-`0` time `a 0`; then, inside the level-`1` excursion
  following it, offset `a 1`; then, inside the level-`2` excursion following *that*, offset
  `a 2`; …", with offset `0` meaning "the same class, seen one level finer".
* **The classes of (3.13).**  The class `[(n_z + n, j)]` is encoded as the address
  `addr Gs Y n j : ℕ →₀ ℕ`, defined by recursion on the level: `addr 0 j = single 0 j`, and
  `addr (n+1) j = addr n k + single (n+1) (j - J^{n,n+1}_k)` where `k` is the unique level-`n`
  time with `J^{n,n+1}_k ≤ j < J^{n,n+1}_{k+1}`.  Two pairs are equivalent in the paper's
  sense exactly when they have the same address (`addr_eq_of_paperRel`, `J_eq_of_addr_eq`):
  `addr (n + d) (J^{n,n+d} k) = addr n k`, and conversely `addr (n+d) j = addr n k` forces
  `j = J^{n,n+d} k`.  The inverse map is `tm Gs Y n a`, the level-`n` time of the address
  `a` (`tm_addr : tm n (addr n j) = j`).
* **The paper's `Ξ`** is the *realised* subset `{a // Realized Gs Y a}` of `Ξ₀`, where
  `Realized a := ∃ n j, addr n j = a` — literally "`a` is the class of some pair".  Its order
  is the restriction of the ambient order, and it agrees with the paper's: at every level
  `n`, `j ↦ addr n j` is strictly increasing into `Ξ₀` (`addr_strictMono`), so for two
  realised addresses with representatives at a common level `a ≤ b ↔ tm n a ≤ tm n b`
  (`le_iff_tm_le`).  This is the paper's "ξ ≤ ξ̃ iff `j ≤ j̃` at any common level".
* **`Y_ξ`** is `Yxi Gs Y a := Y (level a) (tm (level a) a)` where `level a` is the largest
  coordinate in the support of `a` (the smallest level at which the class has a
  representative).  Under `Consistent Gs Y` — the coupling identity (3.12),
  `Y (n+1) (J^{n,n+1} k) = Y n k` — this is independent of the level used
  (`Consistent.Yxi_eq`), and `Yxi (addr n j) = Y n j` is exactly (3.13)
  (`Consistent.Yxi_addr`).
* **(3.14)** is `Consistent.exists_addr_eq_of_mem`: if `Y_ξ ∈ VG_n` then `ξ` has a
  representative at level `n`.  **(3.24)**, the successor `ξ̂`, is `succAt n a := addr n
  (tm n a + 1)`; when `Y_ξ ∈ VG_n` its level-`(n+d)` time is `tm (n+d) a + 1` for every `d`
  (`Consistent.tm_succAt`), hence nothing realised lies strictly between `ξ` and `ξ̂`
  (`Consistent.not_lt_lt_succAt`).
* **Cofinality.**  The level-`0` elements `addr 0 k` are cofinal in `Ξ` (`lt_addr_zero_succ`),
  so "for arbitrarily large `ξ ∈ Ξ`" means "for arbitrarily large level-`0` times", and `Ξ`
  has no maximum (`exists_gt`).  The least element is `ξ₀ = 0 = addr n 0` for every `n`
  (`addr_zero_eq_zero`).

### Alternatives rejected

1. *The literal quotient* `Quot (Σ n, ℕ) (paper's relation)`, built per sample path.  This
   makes `Ξ` a type depending on `ω`; `Y`, the holding-time family `{T_ξ}`, and every sum
   `∑_{ξ ≤ η}` become dependently typed, and the product measure for the holding times would
   have to be built on a random index type.  The address encoding gives the same classes and
   the same order (proved, not assumed) inside a fixed countable type.
2. *Re-indexing by `ℕ`.*  Impossible: `Ξ` contains elements with no immediate predecessor
   (the returns from `∞`), so it is not order-isomorphic to `ℕ`; nor is it well-ordered (an
   element with no predecessor has an infinite descending chain below it), so no ordinal
   encoding is available either.  The order type is moreover random.
3. *Lexicographic `ℕ × ℕ`* (level, time) — that is the un-quotiented pair set, and its order
   is not the paper's (the paper's order interleaves levels).
4. *`Lex (ℕ → ℕ)`* (mathlib's `Pi.Lex` on a well-ordered index) — the same order, but
   uncountable, so countability of `Ξ` would need a separate argument that `Finsupp` provides
   for free.  *`Lex (List ℕ)`* with prefix-first order fails outright: the level at which an
   offset is taken must be encoded positionally, otherwise the classes of `(n+1, J^{n,n+1}_k
   + i)` and of a finer-level excursion offset collide.

### Interaction with `Kernel.traj` being `ℕ`-indexed

`Ξ` is never the index of a probability construction.  The construction of Section 3.2
decomposes as follows.
1. Each level-`n` chain `Y^n` is an `ℕ`-indexed Markov chain on `B₁G_n` — Ionescu–Tulcea
   (`Kernel.trajMeasure`) with *time* as the index (owned by `ApproximatingChain.lean`).
2. The coupling of Lemma 3.4 is a *second* Ionescu–Tulcea construction whose `ℕ`-index is the
   exhaustion level and whose state at stage `i` is the whole level-`i` path `ℕ → V`
   (a standard Borel space for countable discrete `V`): `μ₀ :=` law of `Y^{n_z}` from `z`,
   and the stage kernel `κ i : Kernel (ℕ → V) (ℕ → V)` is
   `condDistrib id (coarsenPath (Gs i)) (law of Y^{n_z+i+1} from z)`, the regular conditional
   law of the finer path given its coarsening; Lemma 3.3 (`(law Y^{n+1}).map coarsenPath =
   law Y^n`) is exactly the hypothesis that makes the joint law of consecutive levels equal
   `law Y^n ⊗ₘ κ`.  The resulting measure on `ℕ → (ℕ → V)` is the paper's `P_z`, and
   `Consistent Gs Y` holds `P_z`-a.s.  The conditional-independence clause of Lemma 3.4 is the
   Markov property of this level-indexed chain.
3. The process `Y : Ξ → VG` of (3.13) is then the *deterministic* function `Yxi Gs Y` of
   the sample `Y : ℕ → ℕ → V`, and the holding times of Section 3.3 are realised as
   `T_a := E_a / w (Yxi a)` for an i.i.d. `Exponential(1)` family `E : Ξ₀ → ℝ` indexed by the
   fixed countable type `Ξ₀` (`Measure.infinitePi`), independent of the paths — which is the
   paper's "conditionally independent, `T_ξ ~ Exponential(w(Y_ξ))`".
No Kolmogorov extension over finite subsets of `Ξ` is needed.

### The `w*` discrepancy (recorded, not resolved here)

The printed Theorem 1.6 assumes `w ≥ w*` everywhere; Lemma 3.5 assumes it off a finite set.
`Theorem16Statement.lean` uses the printed form.  Lemma 3.5 is not proved in this file (see
the module-level assessment in the report); its deterministic reductions are.

## Conventions

`V` is an arbitrary type; the graph structure is irrelevant to this file.  `Gs` is used
through `Monotone Gs` (the `G_n` increase) and, where needed, `⋃ n, Gs n = univ`.  No local
finiteness anywhere.
-/

namespace ReflectedWalk.IndexSet

variable {V : Type*}

/-! ### The coarsening times `J^{m,n}` of (3.9) for one step of the level -/

open Classical in
/-- The coarsening times of (3.9): given a set `S` (the paper's `VG_m`) and a path `p` (the
paper's `Y^n`), `coarsen S p k` is `J^{m,n}_k`.  From a time at which `p` is in `S`, the next
time is one step later; from a time at which `p` is outside `S`, the next time is the next
visit to `S`.  If `p` never returns to `S` (a null event for the chains of Section 3.1) the
next time is taken one step later, so that the map is always strictly increasing. -/
noncomputable def coarsen (S : Set V) (p : ℕ → V) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if p (coarsen S p k) ∈ S then coarsen S p k + 1
    else if h : ∃ j, coarsen S p k < j ∧ p j ∈ S then Nat.find h else coarsen S p k + 1

section coarsen

variable (S : Set V) (p : ℕ → V)

@[simp] lemma coarsen_zero : coarsen S p 0 = 0 := rfl

/-- (3.9), first case. -/
lemma coarsen_succ_of_mem {k : ℕ} (h : p (coarsen S p k) ∈ S) :
    coarsen S p (k + 1) = coarsen S p k + 1 := by
  rw [coarsen]; simp [h]

/-- The coarsening times are strictly increasing (each step advances by at least one). -/
lemma lt_coarsen_succ (k : ℕ) : coarsen S p k < coarsen S p (k + 1) := by
  classical
  rw [coarsen]
  split_ifs with h1 h2
  · exact Nat.lt_succ_self _
  · exact (Nat.find_spec h2).1
  · exact Nat.lt_succ_self _

lemma coarsen_strictMono : StrictMono (coarsen S p) :=
  strictMono_nat_of_lt_succ (lt_coarsen_succ S p)

lemma coarsen_mono : Monotone (coarsen S p) := (coarsen_strictMono S p).monotone

lemma self_le_coarsen (k : ℕ) : k ≤ coarsen S p k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (lt_coarsen_succ S p k))

/-- (3.9), second case: the next coarsening time is at most any later visit to `S`. -/
lemma coarsen_succ_le_of_mem {k j : ℕ} (hj : coarsen S p k < j) (hjS : p j ∈ S) :
    coarsen S p (k + 1) ≤ j := by
  classical
  rw [coarsen]
  split_ifs with h1 h2
  · exact hj
  · exact Nat.find_min' h2 ⟨hj, hjS⟩
  · exact absurd ⟨j, hj, hjS⟩ h2

/-- Strictly between two consecutive coarsening times the path is outside `S`. -/
lemma not_mem_of_lt_of_lt {k j : ℕ} (h1 : coarsen S p k < j) (h2 : j < coarsen S p (k + 1)) :
    p j ∉ S :=
  fun hjS => absurd (coarsen_succ_le_of_mem S p h1 hjS) (not_le.mpr h2)

/-- The level-`(m)` time whose excursion contains the level-`n` time `j`: the largest `k`
with `J^{m,n}_k ≤ j`. -/
noncomputable def coarsenPred (j : ℕ) : ℕ :=
  Nat.findGreatest (fun k => coarsen S p k ≤ j) j

lemma coarsen_coarsenPred_le (j : ℕ) : coarsen S p (coarsenPred S p j) ≤ j :=
  Nat.findGreatest_spec (P := fun k => coarsen S p k ≤ j) (Nat.zero_le j) (by simp)

lemma lt_coarsen_coarsenPred_succ (j : ℕ) : j < coarsen S p (coarsenPred S p j + 1) := by
  by_contra hc
  have h : coarsen S p (coarsenPred S p j + 1) ≤ j := not_lt.mp hc
  have hb : coarsenPred S p j + 1 ≤ j :=
    le_trans (self_le_coarsen S p _) h
  exact Nat.findGreatest_is_greatest (P := fun k => coarsen S p k ≤ j)
    (Nat.lt_succ_self _) hb h

/-- `coarsenPred` is characterised by the two-sided bound. -/
lemma coarsenPred_eq_of_le_of_lt {k j : ℕ} (h1 : coarsen S p k ≤ j)
    (h2 : j < coarsen S p (k + 1)) : coarsenPred S p j = k := by
  apply le_antisymm
  · by_contra hc
    have h : k < coarsenPred S p j := not_le.mp hc
    have : coarsen S p (k + 1) ≤ coarsen S p (coarsenPred S p j) :=
      coarsen_mono S p (Nat.succ_le_of_lt h)
    exact absurd (lt_of_lt_of_le h2 (this.trans (coarsen_coarsenPred_le S p j)))
      (lt_irrefl _)
  · exact Nat.le_findGreatest (le_trans (self_le_coarsen S p k) h1) h1

lemma coarsenPred_coarsen (k : ℕ) : coarsenPred S p (coarsen S p k) = k :=
  coarsenPred_eq_of_le_of_lt S p le_rfl (lt_coarsen_succ S p k)

/-- The deterministic core of (3.14): every visit of the path to `S` is a coarsening time. -/
lemma exists_coarsen_eq_of_mem {j : ℕ} (hjS : p j ∈ S) : ∃ k, coarsen S p k = j := by
  refine ⟨coarsenPred S p j, ?_⟩
  rcases (coarsen_coarsenPred_le S p j).lt_or_eq with h | h
  · exact absurd (coarsen_succ_le_of_mem S p h hjS)
      (not_le.mpr (lt_coarsen_coarsenPred_succ S p j))
  · exact h

end coarsen

/-! ### Levels, the composite times `J^{m,n}`, and addresses -/

section levels

variable (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)

/-- `J^{n_z+n, n_z+n+1}`: the coarsening of the level-`(n+1)` path with respect to `G_{n_z+n}`. -/
noncomputable def Jstep (n : ℕ) : ℕ → ℕ := coarsen (Gs n) (Y (n + 1))

/-- `J^{n_z+m, n_z+m+d}` as the composite of one-level coarsenings.  The paper defines
`J^{m,n}` directly by (3.9) from `Y^n`; under the coupling of Lemma 3.4 the two agree, and the
composite form makes the cocycle identity `J^{m,n} = J^{m',n} ∘ J^{m,m'}` (used on p. 20 to
finish the induction) hold by definition. -/
noncomputable def J (m : ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | d + 1 => Jstep Gs Y (m + d) ∘ J m d

@[simp] lemma J_zero (m : ℕ) : J Gs Y m 0 = id := rfl

lemma J_succ (m d : ℕ) (k : ℕ) : J Gs Y m (d + 1) k = Jstep Gs Y (m + d) (J Gs Y m d k) := rfl

lemma J_strictMono (m d : ℕ) : StrictMono (J Gs Y m d) := by
  induction d with
  | zero => exact strictMono_id
  | succ d ih => exact (coarsen_strictMono _ _).comp ih

/-- The cocycle identity `J^{m,m+d+e} = J^{m+d,m+d+e} ∘ J^{m,m+d}`. -/
lemma J_add (m d e : ℕ) (k : ℕ) : J Gs Y m (d + e) k = J Gs Y (m + d) e (J Gs Y m d k) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [← Nat.add_assoc, J_succ, ih, J_succ, Nat.add_assoc]

/-- The level-`n` time of an address: `tm 0 a = a 0`, and the level-`(n+1)` time is the
coarsening time of the level-`n` time, plus the offset `a (n+1)` inside that excursion. -/
noncomputable def tm : ℕ → (ℕ →₀ ℕ) → ℕ
  | 0, a => a 0
  | n + 1, a => Jstep Gs Y n (tm n a) + a (n + 1)

@[simp] lemma tm_zero (a : ℕ →₀ ℕ) : tm Gs Y 0 a = a 0 := rfl

lemma tm_succ (n : ℕ) (a : ℕ →₀ ℕ) :
    tm Gs Y (n + 1) a = Jstep Gs Y n (tm Gs Y n a) + a (n + 1) := rfl

/-- `tm n` only depends on the coordinates `≤ n`. -/
lemma tm_congr {n : ℕ} {a b : ℕ →₀ ℕ} (h : ∀ i ≤ n, a i = b i) : tm Gs Y n a = tm Gs Y n b := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    rw [tm_succ, tm_succ, ih (fun i hi => h i (Nat.le_succ_of_le hi)), h (n + 1) le_rfl]

/-- The level-`(m+d)` time of an address supported in `[0, m]` is obtained from its level-`m`
time by `J^{m,m+d}`. -/
lemma tm_add_of_eq_zero {m : ℕ} {a : ℕ →₀ ℕ} (ha : ∀ i, m < i → a i = 0) (d : ℕ) :
    tm Gs Y (m + d) a = J Gs Y m d (tm Gs Y m a) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, tm_succ, ih, J_succ, ha (m + d + 1) (by omega), Nat.add_zero]

/-- The address of the pair `(n_z + n, j)`: the class `[(n, j)]` of (3.13), encoded as a
finitely supported sequence.  See the module docstring. -/
noncomputable def addr : ℕ → ℕ → (ℕ →₀ ℕ)
  | 0, j => Finsupp.single 0 j
  | n + 1, j =>
    addr n (coarsenPred (Gs n) (Y (n + 1)) j) +
      Finsupp.single (n + 1) (j - Jstep Gs Y n (coarsenPred (Gs n) (Y (n + 1)) j))

@[simp] lemma addr_zero (j : ℕ) : addr Gs Y 0 j = Finsupp.single 0 j := rfl

lemma addr_succ (n j : ℕ) :
    addr Gs Y (n + 1) j =
      addr Gs Y n (coarsenPred (Gs n) (Y (n + 1)) j) +
        Finsupp.single (n + 1) (j - Jstep Gs Y n (coarsenPred (Gs n) (Y (n + 1)) j)) := rfl

/-- Addresses of level `n` are supported in `[0, n]`. -/
lemma addr_apply_of_lt {n i : ℕ} (h : n < i) (j : ℕ) : addr Gs Y n j i = 0 := by
  induction n generalizing i j with
  | zero =>
    rw [addr_zero, Finsupp.single_eq_of_ne (Nat.pos_of_ne_zero (by omega)).ne']
  | succ n ih =>
    rw [addr_succ, Finsupp.add_apply, ih (by omega), Finsupp.single_eq_of_ne (by omega),
      Nat.add_zero]

/-- `tm n` inverts `addr n`: the level-`n` time of the class of `(n, j)` is `j`. -/
lemma tm_addr (n j : ℕ) : tm Gs Y n (addr Gs Y n j) = j := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [tm_succ, addr_succ, Finsupp.add_apply, addr_apply_of_lt Gs Y (Nat.lt_succ_self n),
      Finsupp.single_eq_same, Nat.zero_add]
    rw [tm_congr Gs Y (b := addr Gs Y n (coarsenPred (Gs n) (Y (n + 1)) j))
      (fun i hi => by rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), Nat.add_zero])]
    rw [ih]
    exact Nat.add_sub_cancel' (coarsen_coarsenPred_le _ _ j)

lemma addr_injective (n : ℕ) : Function.Injective (addr Gs Y n) :=
  Function.LeftInverse.injective (tm_addr Gs Y n)

/-- A class seen one level finer: `[(n+1, J^{n,n+1}_j)] = [(n, j)]`. -/
lemma addr_succ_Jstep (n j : ℕ) : addr Gs Y (n + 1) (Jstep Gs Y n j) = addr Gs Y n j := by
  rw [addr_succ, Jstep, coarsenPred_coarsen, Nat.sub_self, Finsupp.single_zero, add_zero]

/-- `[(m + d, J^{m,m+d}_k)] = [(m, k)]`: the paper's generating relation identifies pairs with
the same address. -/
lemma addr_J (m d k : ℕ) : addr Gs Y (m + d) (J Gs Y m d k) = addr Gs Y m k := by
  induction d with
  | zero => rfl
  | succ d ih => rw [← Nat.add_assoc, J_succ, addr_succ_Jstep, ih]

/-- Conversely, equal addresses at levels `m + d` and `m` force the paper's relation. -/
lemma J_eq_of_addr_eq {m d j k : ℕ} (h : addr Gs Y (m + d) j = addr Gs Y m k) :
    j = J Gs Y m d k := by
  have h1 := tm_addr Gs Y (m + d) j
  rw [h, tm_add_of_eq_zero Gs Y (fun i hi => addr_apply_of_lt Gs Y hi k), tm_addr] at h1
  exact h1.symm

/-- The paper's relation on pairs `(level, time)` (p. 20): `(n, j) ∼ (m, k)` iff they are
equal, or `m < n` and `j = J^{m,n}_k`, or symmetrically.  Levels are relative to `n_z`. -/
def PaperRel (n j m k : ℕ) : Prop :=
  (n = m ∧ j = k) ∨ (m < n ∧ j = J Gs Y m (n - m) k) ∨ (n < m ∧ k = J Gs Y n (m - n) j)

/-- Related pairs have the same address: the address is a class invariant. -/
lemma addr_eq_of_paperRel {n j m k : ℕ} (h : PaperRel Gs Y n j m k) :
    addr Gs Y n j = addr Gs Y m k := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hmn, rfl⟩ | ⟨hnm, rfl⟩
  · rfl
  · have := addr_J Gs Y m (n - m) k
    rwa [Nat.add_sub_cancel' hmn.le] at this
  · have := addr_J Gs Y n (m - n) j
    rw [Nat.add_sub_cancel' hnm.le] at this
    exact this.symm

/-- Pairs with the same address are related: the fibres of `addr` are exactly the classes. -/
lemma paperRel_of_addr_eq {n j m k : ℕ} (h : addr Gs Y n j = addr Gs Y m k) :
    PaperRel Gs Y n j m k := by
  rcases lt_trichotomy n m with hnm | rfl | hmn
  · refine Or.inr (Or.inr ⟨hnm, ?_⟩)
    have h' : addr Gs Y (n + (m - n)) k = addr Gs Y n j := by
      rw [Nat.add_sub_cancel' hnm.le]; exact h.symm
    exact J_eq_of_addr_eq Gs Y h'
  · exact Or.inl ⟨rfl, addr_injective Gs Y n h⟩
  · refine Or.inr (Or.inl ⟨hmn, ?_⟩)
    have h' : addr Gs Y (m + (n - m)) j = addr Gs Y m k := by
      rw [Nat.add_sub_cancel' hmn.le]; exact h
    exact J_eq_of_addr_eq Gs Y h'

/-- The least class `ξ₀ = [(n, 0)]` is the zero address at every level (p. 23, proof of
Lemma 3.7: "the first element of `Ξ` … contains `(n, 0)` for each `n ≥ n_z`"). -/
lemma addr_zero_eq_zero (n : ℕ) : addr Gs Y n 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : coarsenPred (Gs n) (Y (n + 1)) 0 = 0 :=
      coarsenPred_eq_of_le_of_lt _ _ le_rfl (lt_coarsen_succ _ _ 0)
    rw [addr_succ, h0, ih, Jstep, coarsen_zero, Nat.sub_self, Finsupp.single_zero, add_zero]

/-! ### The ambient linear order `Ξ₀ = Lex (ℕ →₀ ℕ)` -/

/-- The ambient index set: finitely supported sequences of naturals, lexicographically ordered.
The paper's `Ξ` is the realised subset `Xi Gs Y` below. -/
abbrev Xi₀ : Type := Lex (ℕ →₀ ℕ)

instance : Countable Xi₀ := inferInstanceAs (Countable (ℕ →₀ ℕ))

/-- Unfolding the lexicographic order: the first coordinate where the two differ decides. -/
lemma toLex_lt_toLex_iff {a b : ℕ →₀ ℕ} :
    toLex a < toLex b ↔ ∃ i, (∀ j < i, a j = b j) ∧ a i < b i :=
  Iff.rfl

/-- Adding a coordinate beyond the common support does not affect a strict comparison. -/
lemma toLex_add_single_lt {n : ℕ} {a b : ℕ →₀ ℕ} (h : toLex a < toLex b)
    (hb : ∀ i, n < i → b i = 0) {m : ℕ} (hm : n < m) (x : ℕ) :
    toLex (a + Finsupp.single m x) < toLex b := by
  obtain ⟨i, hlt, hi⟩ := toLex_lt_toLex_iff.mp h
  have hin : i ≤ n := by
    by_contra hcon
    rw [hb i (not_le.mp hcon)] at hi
    exact absurd hi (Nat.not_lt_zero _)
  refine toLex_lt_toLex_iff.mpr ⟨i, fun j hj => ?_, ?_⟩
  · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), Nat.add_zero]
    exact hlt j hj
  · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), Nat.add_zero]
    exact hi

/-- Consecutive times at one level have increasing addresses. -/
lemma addr_lt_addr_succ (n j : ℕ) : toLex (addr Gs Y n j) < toLex (addr Gs Y n (j + 1)) := by
  induction n generalizing j with
  | zero =>
    refine toLex_lt_toLex_iff.mpr ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    simp
  | succ n ih =>
    set S := Gs n
    set p := Y (n + 1)
    set k := coarsenPred S p j with hk
    have hk1 : coarsen S p k ≤ j := coarsen_coarsenPred_le S p j
    have hk2 : j < coarsen S p (k + 1) := lt_coarsen_coarsenPred_succ S p j
    rcases (Nat.succ_le_of_lt hk2).lt_or_eq with hlt | heq
    · -- the successor time lies in the same excursion
      have hpred : coarsenPred S p (j + 1) = k :=
        coarsenPred_eq_of_le_of_lt S p (Nat.le_succ_of_le hk1) hlt
      rw [addr_succ, addr_succ, hpred]
      refine toLex_lt_toLex_iff.mpr ⟨n + 1, fun i hi => ?_, ?_⟩
      · rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega),
          Finsupp.single_eq_of_ne (by omega)]
      · rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_same,
          addr_apply_of_lt Gs Y (Nat.lt_succ_self n), Nat.zero_add, Nat.zero_add]
        change j - Jstep Gs Y n k < j + 1 - Jstep Gs Y n k
        exact Nat.sub_lt_sub_right hk1 (Nat.lt_succ_self j)
    · -- the successor time starts the next excursion
      have heq' : j + 1 = Jstep Gs Y n (k + 1) := heq
      rw [heq', addr_succ_Jstep, addr_succ]
      exact toLex_add_single_lt (ih k) (fun i hi => addr_apply_of_lt Gs Y hi _)
        (Nat.lt_succ_self n) _

/-- At each level, `j ↦ [(n, j)]` is an order embedding of `ℕ` into `Ξ₀`. -/
lemma addr_strictMono (n : ℕ) : StrictMono (fun j => toLex (addr Gs Y n j)) :=
  strictMono_nat_of_lt_succ (addr_lt_addr_succ Gs Y n)

lemma addr_le_addr_iff {n j j' : ℕ} :
    toLex (addr Gs Y n j) ≤ toLex (addr Gs Y n j') ↔ j ≤ j' :=
  (addr_strictMono Gs Y n).le_iff_le

lemma addr_lt_addr_iff {n j j' : ℕ} :
    toLex (addr Gs Y n j) < toLex (addr Gs Y n j') ↔ j < j' :=
  (addr_strictMono Gs Y n).lt_iff_lt

/-! ### The realised index set `Ξ` -/

/-- `a` is the class of some pair `(n, j)`: the defining property of membership in the
paper's `Ξ`. -/
def Realized (a : ℕ →₀ ℕ) : Prop := ∃ n j, addr Gs Y n j = a

/-- The paper's random index set `Ξ`, as the realised subset of `Ξ₀`, with the induced
linear order. -/
def Xi : Type := {a : Xi₀ // Realized Gs Y (ofLex a)}

noncomputable instance : LinearOrder (Xi Gs Y) := Subtype.instLinearOrder _

instance : Countable (Xi Gs Y) := Subtype.countable

lemma realized_addr (n j : ℕ) : Realized Gs Y (addr Gs Y n j) := ⟨n, j, rfl⟩

lemma realized_zero : Realized Gs Y 0 := ⟨0, 0, addr_zero_eq_zero Gs Y 0⟩

/-- A realised address has a representative at every level from some point on. -/
lemma Realized.exists_addr_eq {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) :
    ∃ m, ∀ n, m ≤ n → ∃ j, addr Gs Y n j = a := by
  obtain ⟨m, j, rfl⟩ := ha
  refine ⟨m, fun n hn => ⟨J Gs Y m (n - m) j, ?_⟩⟩
  have := addr_J Gs Y m (n - m) j
  rwa [Nat.add_sub_cancel' hn] at this

/-- Two realised addresses have representatives at a common level. -/
lemma Realized.exists_common_level {a b : ℕ →₀ ℕ} (ha : Realized Gs Y a) (hb : Realized Gs Y b) :
    ∃ n, (∃ j, addr Gs Y n j = a) ∧ ∃ j, addr Gs Y n j = b := by
  obtain ⟨ma, hma⟩ := ha.exists_addr_eq
  obtain ⟨mb, hmb⟩ := hb.exists_addr_eq
  exact ⟨max ma mb, hma _ (le_max_left _ _), hmb _ (le_max_right _ _)⟩

/-- The paper's description of the order (p. 20): for classes with representatives at a
common level `n`, `ξ ≤ ξ̃` iff the level-`n` times compare. -/
lemma le_iff_tm_le {n : ℕ} {a b : ℕ →₀ ℕ} (ha : ∃ j, addr Gs Y n j = a)
    (hb : ∃ j, addr Gs Y n j = b) :
    toLex a ≤ toLex b ↔ tm Gs Y n a ≤ tm Gs Y n b := by
  obtain ⟨j, rfl⟩ := ha
  obtain ⟨j', rfl⟩ := hb
  rw [tm_addr, tm_addr, addr_le_addr_iff]

lemma lt_iff_tm_lt {n : ℕ} {a b : ℕ →₀ ℕ} (ha : ∃ j, addr Gs Y n j = a)
    (hb : ∃ j, addr Gs Y n j = b) :
    toLex a < toLex b ↔ tm Gs Y n a < tm Gs Y n b := by
  obtain ⟨j, rfl⟩ := ha
  obtain ⟨j', rfl⟩ := hb
  rw [tm_addr, tm_addr, addr_lt_addr_iff]

/-- Every level-`n` time lies in the excursion of the level-`0` time `addr n j 0`:
`J^{0,n}(a 0) ≤ j < J^{0,n}(a 0 + 1)` for `a = addr n j`. -/
lemma J_addr_apply_zero_le (n j : ℕ) :
    J Gs Y 0 n (addr Gs Y n j 0) ≤ j ∧ j < J Gs Y 0 n (addr Gs Y n j 0 + 1) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    set k := coarsenPred (Gs n) (Y (n + 1)) j
    have h0 : addr Gs Y (n + 1) j 0 = addr Gs Y n k 0 := by
      rw [addr_succ, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), Nat.add_zero]
    obtain ⟨ih1, ih2⟩ := ih k
    rw [h0]
    constructor
    · calc J Gs Y 0 (n + 1) (addr Gs Y n k 0)
          = Jstep Gs Y n (J Gs Y 0 n (addr Gs Y n k 0)) := by rw [J_succ, Nat.zero_add]
        _ ≤ Jstep Gs Y n k := coarsen_mono _ _ ih1
        _ ≤ j := coarsen_coarsenPred_le _ _ j
    · calc j < Jstep Gs Y n (k + 1) := lt_coarsen_coarsenPred_succ _ _ j
        _ ≤ Jstep Gs Y n (J Gs Y 0 n (addr Gs Y n k 0 + 1)) := coarsen_mono _ _ ih2
        _ = J Gs Y 0 (n + 1) (addr Gs Y n k 0 + 1) := by rw [J_succ, Nat.zero_add]

/-- The level-`0` elements are cofinal in `Ξ`: every realised address lies strictly below the
level-`0` class of the next level-`0` time.  This is what "for arbitrarily large `ξ ∈ Ξ`"
means: it suffices to look at level-`0` times. -/
lemma lt_addr_zero_succ {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) :
    toLex a < toLex (addr Gs Y 0 (a 0 + 1)) := by
  obtain ⟨n, j, rfl⟩ := ha
  have h := (J_addr_apply_zero_le Gs Y n j).2
  have e : addr Gs Y 0 (addr Gs Y n j 0 + 1) = addr Gs Y n (J Gs Y 0 n (addr Gs Y n j 0 + 1)) := by
    have := addr_J Gs Y 0 n (addr Gs Y n j 0 + 1)
    rw [Nat.zero_add] at this
    exact this.symm
  rw [e, addr_lt_addr_iff]
  exact h

lemma addr_zero_le {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) :
    toLex (addr Gs Y 0 (a 0)) ≤ toLex a := by
  obtain ⟨n, j, rfl⟩ := ha
  have h := (J_addr_apply_zero_le Gs Y n j).1
  have e : addr Gs Y 0 (addr Gs Y n j 0) = addr Gs Y n (J Gs Y 0 n (addr Gs Y n j 0)) := by
    have := addr_J Gs Y 0 n (addr Gs Y n j 0)
    rw [Nat.zero_add] at this
    exact this.symm
  rw [e, addr_le_addr_iff]
  exact h

/-- `Ξ` has no largest element. -/
lemma exists_gt (ξ : Xi Gs Y) : ∃ η : Xi Gs Y, ξ < η :=
  ⟨⟨toLex (addr Gs Y 0 (ofLex ξ.1 0 + 1)), realized_addr Gs Y 0 _⟩, lt_addr_zero_succ Gs Y ξ.2⟩

/-- `ξ₀ = 0` is the least element of `Ξ`. -/
lemma zero_le_xi (a : ℕ →₀ ℕ) : toLex (0 : ℕ →₀ ℕ) ≤ toLex a := bot_le

end levels

/-! ### The process `Y_ξ` of (3.13), under the coupling identity (3.12) -/

section process

variable (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)

/-- The coupling identity (3.12) of Lemma 3.4 for consecutive levels:
`Y^{n+1}_{J^{n,n+1}_k} = Y^n_k`.  It holds `P_z`-a.s. under the coupling; here it is a
hypothesis on the sample. -/
def Consistent : Prop := ∀ n k, Y (n + 1) (Jstep Gs Y n k) = Y n k

/-- (3.12) for arbitrary levels `m ≤ m + d`. -/
lemma Consistent.Y_J (h : Consistent Gs Y) (m d k : ℕ) : Y (m + d) (J Gs Y m d k) = Y m k := by
  induction d with
  | zero => rfl
  | succ d ih => rw [← Nat.add_assoc, J_succ, h, ih]

/-- The level of an address: the largest coordinate of its support (`0` for the zero address).
This is the smallest level at which the class has a representative. -/
def level (a : ℕ →₀ ℕ) : ℕ := a.support.sup id

lemma apply_eq_zero_of_level_lt {a : ℕ →₀ ℕ} {i : ℕ} (h : level a < i) : a i = 0 := by
  by_contra hne
  have hi : i ∈ a.support := Finsupp.mem_support_iff.mpr hne
  exact absurd (Finset.le_sup (f := id) hi) (not_le.mpr h)

lemma level_addr_le (n j : ℕ) : level (addr Gs Y n j) ≤ n := by
  refine Finset.sup_le fun i hi => ?_
  by_contra hc
  exact absurd (addr_apply_of_lt Gs Y (not_le.mp hc) j) (Finsupp.mem_support_iff.mp hi)

/-- (3.13): `Y_ξ := Y^n_j` for `(n, j) ∈ ξ`, evaluated at the smallest level of `ξ`. -/
noncomputable def Yxi (a : ℕ →₀ ℕ) : V := Y (level a) (tm Gs Y (level a) a)

lemma Consistent.Y_tm_succ (h : Consistent Gs Y) {a : ℕ →₀ ℕ} {n : ℕ} (hn : level a ≤ n) :
    Y (n + 1) (tm Gs Y (n + 1) a) = Y n (tm Gs Y n a) := by
  have e : tm Gs Y (n + 1) a = Jstep Gs Y n (tm Gs Y n a) := by
    rw [tm_succ, apply_eq_zero_of_level_lt (Nat.lt_succ_of_le hn)]
    exact Nat.add_zero _
  rw [e]
  exact h n _

/-- (3.13) is well defined: `Y_ξ` may be read off at any level `≥ level ξ`. -/
lemma Consistent.Yxi_eq (h : Consistent Gs Y) {a : ℕ →₀ ℕ} {n : ℕ} (hn : level a ≤ n) :
    Yxi Gs Y a = Y n (tm Gs Y n a) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, h.Y_tm_succ Gs Y (Nat.le_add_right _ _), ih (Nat.le_add_right _ _)]

/-- (3.13) in the paper's form: `Y_{[(n,j)]} = Y^n_j`. -/
lemma Consistent.Yxi_addr (h : Consistent Gs Y) (n j : ℕ) : Yxi Gs Y (addr Gs Y n j) = Y n j := by
  rw [h.Yxi_eq Gs Y (level_addr_le Gs Y n j), tm_addr]

lemma Yxi_zero : Yxi Gs Y 0 = Y 0 0 := by
  simp [Yxi, level]

/-- (3.14): if `Y_ξ ∈ VG_n` then `ξ` has a representative `(n, j)` at level `n`.  Needs the
exhaustion to be increasing. -/
lemma Consistent.exists_addr_eq_of_mem (h : Consistent Gs Y) (hG : Monotone Gs)
    {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) {n : ℕ} (hn : Yxi Gs Y a ∈ Gs n) :
    ∃ j, addr Gs Y n j = a := by
  obtain ⟨m, j, rfl⟩ := ha
  rw [h.Yxi_addr] at hn
  rcases Nat.lt_or_ge n m with hnm | hmn
  swap
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨J Gs Y m d j, addr_J Gs Y m d j⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm.le
    -- descend one level at a time
    have key : ∀ d j, Y (n + d) j ∈ Gs n → ∃ j', addr Gs Y n j' = addr Gs Y (n + d) j := by
      intro d
      induction d with
      | zero => exact fun j _ => ⟨j, rfl⟩
      | succ d ih =>
        intro j hj
        show ∃ j', addr Gs Y n j' = addr Gs Y (n + d + 1) j
        obtain ⟨k, hk⟩ := exists_coarsen_eq_of_mem (Gs (n + d)) (Y (n + d + 1))
          (hG (Nat.le_add_right n d) hj)
        have hk' : Jstep Gs Y (n + d) k = j := hk
        rw [← hk', addr_succ_Jstep]
        apply ih
        rw [← h (n + d) k, hk']
        exact hj
    exact key d j hn

/-- (3.24): the successor of `ξ` read at level `n`, `ξ̂ = [(n, k+1)]` where `ξ = [(n, k)]`. -/
noncomputable def succAt (n : ℕ) (a : ℕ →₀ ℕ) : ℕ →₀ ℕ := addr Gs Y n (tm Gs Y n a + 1)

lemma realized_succAt (n : ℕ) (a : ℕ →₀ ℕ) : Realized Gs Y (succAt Gs Y n a) :=
  realized_addr Gs Y n _

/-- If `Y_ξ ∈ VG_n` then `J^{n,n+d}_{k+1} = J^{n,n+d}_k + 1` for every `d` (p. 23): the
successor at level `n` stays the successor at every finer level. -/
lemma Consistent.J_succ_of_mem (h : Consistent Gs Y) (hG : Monotone Gs) {n k : ℕ}
    (hk : Y n k ∈ Gs n) (d : ℕ) : J Gs Y n d (k + 1) = J Gs Y n d k + 1 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [J_succ, J_succ, ih, Jstep, coarsen_succ_of_mem]
    change Y (n + d + 1) (Jstep Gs Y (n + d) (J Gs Y n d k)) ∈ Gs (n + d)
    rw [h, h.Y_J]
    exact hG (Nat.le_add_right n d) hk

/-- The level-`(n+d)` time of `ξ̂` is one more than that of `ξ`, when `Y_ξ ∈ VG_n`. -/
lemma Consistent.tm_succAt (h : Consistent Gs Y) (hG : Monotone Gs) {n : ℕ} {a : ℕ →₀ ℕ}
    (ha : ∃ j, addr Gs Y n j = a) (hmem : Yxi Gs Y a ∈ Gs n) (d : ℕ) :
    tm Gs Y (n + d) (succAt Gs Y n a) = tm Gs Y (n + d) a + 1 := by
  obtain ⟨j, rfl⟩ := ha
  rw [h.Yxi_addr] at hmem
  rw [succAt, tm_addr, tm_add_of_eq_zero Gs Y (fun i hi => addr_apply_of_lt Gs Y hi _),
    tm_add_of_eq_zero Gs Y (fun i hi => addr_apply_of_lt Gs Y hi _), tm_addr, tm_addr,
    h.J_succ_of_mem Gs Y hG hmem]

/-- Nothing in `Ξ` lies strictly between `ξ` and its successor `ξ̂` (p. 23, "there does not
exist any `η ∈ Ξ` with `ξ < η < [(m, k+1)]`"). -/
lemma Consistent.not_lt_lt_succAt (h : Consistent Gs Y) (hG : Monotone Gs) {n : ℕ}
    {a : ℕ →₀ ℕ} (ha : ∃ j, addr Gs Y n j = a) (hmem : Yxi Gs Y a ∈ Gs n)
    {b : ℕ →₀ ℕ} (hb : Realized Gs Y b) :
    ¬ (toLex a < toLex b ∧ toLex b < toLex (succAt Gs Y n a)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨m, hm⟩ := hb.exists_addr_eq
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_max_left n m)
  have haN : ∃ j, addr Gs Y (max n m) j = a := by
    obtain ⟨j, rfl⟩ := ha
    exact ⟨J Gs Y n d j, by rw [hd]; exact addr_J Gs Y n d j⟩
  have hsN : ∃ j, addr Gs Y (max n m) j = succAt Gs Y n a :=
    ⟨J Gs Y n d _, by rw [hd]; exact addr_J Gs Y n d _⟩
  have hbN := hm (max n m) (le_max_right n m)
  rw [lt_iff_tm_lt Gs Y haN hbN, hd] at h1
  rw [lt_iff_tm_lt Gs Y hbN hsN, hd] at h2
  have := h.tm_succAt Gs Y hG ha hmem d
  omega

/-- Property (v) at the discrete level (p. 25): if the level-`0` chain visits `z` at
arbitrarily large times, then `Ξ` contains arbitrarily large `ξ` with `Y_ξ = z`. -/
lemma Consistent.exists_gt_Yxi_eq (h : Consistent Gs Y) {z : V}
    (hrec : ∀ k, ∃ k', k < k' ∧ Y 0 k' = z) (ξ : Xi Gs Y) :
    ∃ η : Xi Gs Y, ξ < η ∧ Yxi Gs Y (ofLex η.1) = z := by
  obtain ⟨k', hk', hz⟩ := hrec (ofLex ξ.1 0)
  refine ⟨⟨toLex (addr Gs Y 0 k'), realized_addr Gs Y 0 k'⟩, ?_, ?_⟩
  · show ξ.1 < toLex (addr Gs Y 0 k')
    calc ξ.1 < toLex (addr Gs Y 0 (ofLex ξ.1 0 + 1)) := lt_addr_zero_succ Gs Y ξ.2
      _ ≤ toLex (addr Gs Y 0 k') := (addr_le_addr_iff Gs Y).mpr (Nat.succ_le_of_lt hk')
  · show Yxi Gs Y (addr Gs Y 0 k') = z
    rw [h.Yxi_addr]
    exact hz

end process

/-! ### Section 3.3: holding times, the clock `τ_η` of (3.25), the successor (3.24), and (3.26)

Everything here is again a deterministic function of the sample: the paths `Y`, the
exhaustion `Gs`, the rate function `w`, and a family `E : (ℕ →₀ ℕ) → ℝ` of "unit"
holding times (i.i.d. `Exponential(1)` under the product law, independent of the paths).
The a.s. inputs of Lemma 3.5 are isolated as hypotheses of `holdingTimesSummable_of`. -/

section time

open scoped ENNReal NNReal

variable (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)

/-- A realised address has a representative at *every* level `n ≥ level a`, namely
`(n, tm n a)`. -/
lemma addr_tm_of_level_le {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) {n : ℕ} (hn : level a ≤ n) :
    addr Gs Y n (tm Gs Y n a) = a := by
  obtain ⟨m, j, rfl⟩ := ha
  rcases Nat.lt_or_ge n m with hnm | hmn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm.le
    have hz : ∀ i, n < i → addr Gs Y (n + d) j i = 0 :=
      fun i hi => apply_eq_zero_of_level_lt (lt_of_le_of_lt hn hi)
    have e := tm_add_of_eq_zero Gs Y hz d
    rw [tm_addr] at e
    have e2 : J Gs Y n d (tm Gs Y n (addr Gs Y (n + d) j)) = j := e.symm
    calc addr Gs Y n (tm Gs Y n (addr Gs Y (n + d) j))
        = addr Gs Y (n + d) (J Gs Y n d (tm Gs Y n (addr Gs Y (n + d) j))) :=
          (addr_J Gs Y n d _).symm
      _ = addr Gs Y (n + d) j := by rw [e2]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [tm_add_of_eq_zero Gs Y (fun i hi => addr_apply_of_lt Gs Y hi j) d, tm_addr, addr_J]

variable (w : V → ℝ) (E : (ℕ →₀ ℕ) → ℝ)

/-- The realised set `Ξ`, as a set of addresses. -/
def realizedSet : Set (ℕ →₀ ℕ) := {a | Realized Gs Y a}

/-- The holding time `T_ξ := E_ξ / w(Y_ξ)` of Section 3.3: for an i.i.d. `Exponential(1)` family
`E` independent of the paths, this is `Exponential(w(Y_ξ))` conditionally on the paths, as the
paper prescribes.  Valued in `[0, ∞]` so that the sums of (3.25) are unconditionally defined. -/
noncomputable def holding (a : ℕ →₀ ℕ) : ℝ≥0∞ := ENNReal.ofReal (E a / w (Yxi Gs Y a))

lemma holding_ne_top (a : ℕ →₀ ℕ) : holding Gs Y w E a ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `{ξ ∈ Ξ : ξ < η}`. -/
def below (η : ℕ →₀ ℕ) : Set (ℕ →₀ ℕ) := {a | Realized Gs Y a ∧ toLex a < toLex η}

/-- (3.25): `τ_η := ∑_{ξ ∈ Ξ, ξ < η} T_ξ`. -/
noncomputable def tau (η : ℕ →₀ ℕ) : ℝ≥0∞ :=
  ∑' a, (below Gs Y η).indicator (holding Gs Y w E) a

/-- `∑_{ξ ∈ Ξ} T_ξ`, the total time of the first clause of (3.16). -/
noncomputable def totalTime : ℝ≥0∞ :=
  ∑' a, (realizedSet Gs Y).indicator (holding Gs Y w E) a

lemma below_subset_below {η η' : ℕ →₀ ℕ} (h : toLex η ≤ toLex η') :
    below Gs Y η ⊆ below Gs Y η' :=
  fun _ ha => ⟨ha.1, lt_of_lt_of_le ha.2 h⟩

lemma tau_mono {η η' : ℕ →₀ ℕ} (h : toLex η ≤ toLex η') :
    tau Gs Y w E η ≤ tau Gs Y w E η' :=
  ENNReal.tsum_le_tsum fun a =>
    Set.indicator_le_indicator_of_subset (below_subset_below Gs Y h) (fun _ => zero_le) a

lemma tau_le_totalTime (η : ℕ →₀ ℕ) : tau Gs Y w E η ≤ totalTime Gs Y w E :=
  ENNReal.tsum_le_tsum fun a =>
    Set.indicator_le_indicator_of_subset (fun _ ha => ha.1) (fun _ => zero_le) a

/-- Lemma 3.5, Step 1, deterministic half: the second clause of (3.16) for every `η ∈ Ξ` follows
from its level-`0` instances, by cofinality of the level-`0` elements. -/
lemma tau_lt_top_of_level_zero (h : ∀ k, tau Gs Y w E (addr Gs Y 0 k) < ⊤) {η : ℕ →₀ ℕ}
    (hη : Realized Gs Y η) : tau Gs Y w E η < ⊤ :=
  lt_of_le_of_lt (tau_mono Gs Y w E (lt_addr_zero_succ Gs Y hη).le) (h _)

/-- Lemma 3.5, Step 0, deterministic half: the first clause of (3.16) follows from divergence
of the level-`0` holding times (which the paper derives from recurrence of `Y^{n_z}`). -/
lemma totalTime_eq_top (h : ∑' k, holding Gs Y w E (addr Gs Y 0 k) = ⊤) :
    totalTime Gs Y w E = ⊤ := by
  apply top_le_iff.mp
  calc (⊤ : ℝ≥0∞) = ∑' k, holding Gs Y w E (addr Gs Y 0 k) := h.symm
    _ ≤ totalTime Gs Y w E :=
      ENNReal.summable.tsum_le_tsum_of_inj (addr Gs Y 0) (addr_injective Gs Y 0)
        (fun _ _ => zero_le)
        (fun k => by
          rw [Set.indicator_of_mem
            (show addr Gs Y 0 k ∈ realizedSet Gs Y from realized_addr Gs Y 0 k)])
        ENNReal.summable

/-- The layers `G_0`, `G_{n+1} \ G_n` of the exhaustion (p. 22, "`G_n \ G_{n-1}`"); they
partition `VG` when `Gs` is increasing with union `VG`. -/
def layer : ℕ → Set V
  | 0 => Gs 0
  | n + 1 => Gs (n + 1) \ Gs n

lemma layer_subset (n : ℕ) : layer Gs n ⊆ Gs n := by
  cases n with
  | zero => exact fun _ hx => hx
  | succ n => exact fun _ hx => hx.1

lemma exists_mem_layer (hcov : ∀ x, ∃ n, x ∈ Gs n) (x : V) : ∃ n, x ∈ layer Gs n := by
  classical
  obtain ⟨n₀, hn₀, hmin⟩ : ∃ n, x ∈ Gs n ∧ ∀ m < n, x ∉ Gs m :=
    ⟨Nat.find (hcov x), Nat.find_spec (hcov x), fun m hm => Nat.find_min (hcov x) hm⟩
  cases n₀ with
  | zero => exact ⟨0, hn₀⟩
  | succ m => exact ⟨m + 1, hn₀, hmin m (Nat.lt_succ_self m)⟩

lemma layer_eq_of_mem (hG : Monotone Gs) {x : V} {n m : ℕ} (hn : x ∈ layer Gs n)
    (hm : x ∈ layer Gs m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exfalso
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact hm.2 (hG (Nat.lt_succ_iff.mp h) (layer_subset Gs n hn))
  · exact h
  · exfalso
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact hn.2 (hG (Nat.lt_succ_iff.mp h) (layer_subset Gs m hm))

/-- The time spent in layer `n` before `η`: `∑{T_ξ : ξ ∈ Ξ, ξ < η, Y_ξ ∈ G_n \ G_{n-1}}`.  For
`η = η₁` (the first return to `z`) this is the paper's `S_n` of (3.18). -/
noncomputable def layerTime (n : ℕ) (η : ℕ →₀ ℕ) : ℝ≥0∞ :=
  ∑' a, (below Gs Y η ∩ {a | Yxi Gs Y a ∈ layer Gs n}).indicator (holding Gs Y w E) a

/-- Lemma 3.5, Step 3, the bookkeeping: `τ_η` is the sum over layers of the layer times
(the displayed decomposition on p. 22). -/
lemma tau_eq_tsum_layerTime (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n) (η : ℕ →₀ ℕ) :
    tau Gs Y w E η = ∑' n, layerTime Gs Y w E n η := by
  unfold layerTime tau
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  obtain ⟨n₀, hn₀⟩ := exists_mem_layer Gs hcov (Yxi Gs Y a)
  rw [tsum_eq_single n₀]
  · by_cases ha : a ∈ below Gs Y η
    · have hmem : a ∈ below Gs Y η ∩ {a | Yxi Gs Y a ∈ layer Gs n₀} := ⟨ha, hn₀⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ha]
    · have hnot : a ∉ below Gs Y η ∩ {a | Yxi Gs Y a ∈ layer Gs n₀} := fun h => ha h.1
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem ha]
  · intro n hn
    apply Set.indicator_of_notMem
    rintro ⟨-, hmem⟩
    exact hn (layer_eq_of_mem Gs hG hmem hn₀)

/-- The part of `τ_{[(0,K)]}` spent in `G_{n_z}` is a finite sum of finite terms (p. 22, "the
first sum has only finitely many terms"): by (3.14) every such `ξ` is `[(0, j)]` with `j < K`. -/
lemma layerTime_zero_lt_top (h : Consistent Gs Y) (hG : Monotone Gs) (K : ℕ) :
    layerTime Gs Y w E 0 (addr Gs Y 0 K) < ⊤ := by
  unfold layerTime
  rw [tsum_eq_sum (s := (Finset.range K).image (addr Gs Y 0))]
  · exact ENNReal.sum_lt_top.mpr fun a _ =>
      lt_of_le_of_lt (Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le))
        (lt_top_iff_ne_top.mpr (holding_ne_top Gs Y w E a))
  · intro a ha
    apply Set.indicator_of_notMem
    rintro ⟨⟨hreal, hlt⟩, hmem⟩
    obtain ⟨j, rfl⟩ := h.exists_addr_eq_of_mem Gs Y hG hreal hmem
    apply ha
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr ((addr_lt_addr_iff Gs Y).mp hlt), rfl⟩

/-- Lemma 3.5, Step 3, reduced: `τ_{[(0,K)]} < ∞` iff the times spent in the higher layers
before `[(0,K)]` are summable — the paper's `∑_{n > n_z} S_n < ∞`, (3.22). -/
lemma tau_addr_zero_lt_top_iff (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (K : ℕ) :
    tau Gs Y w E (addr Gs Y 0 K) < ⊤ ↔
      ∑' n, layerTime Gs Y w E (n + 1) (addr Gs Y 0 K) < ⊤ := by
  rw [tau_eq_tsum_layerTime Gs Y w E hG hcov, tsum_eq_zero_add' ENNReal.summable,
    ENNReal.add_lt_top]
  exact and_iff_right (layerTime_zero_lt_top Gs Y w E h hG K)

/-- The conclusion (3.16) of Lemma 3.5, for one sample `(Y, E)`. -/
def HoldingTimesSummable : Prop :=
  totalTime Gs Y w E = ⊤ ∧ ∀ η, Realized Gs Y η → tau Gs Y w E η < ⊤

/-- Lemma 3.5 with its probabilistic inputs isolated.  (3.16) holds for a sample as soon as
(Step 0) the level-`0` holding times diverge and (Steps 2–3) for every level-`0` time `K` the
times spent in the layers `G_{n+1} \ G_n` before `[(0,K)]` are summable.  Under the coupling,
the first is a.s. by recurrence of `Y^{n_z}` (Remark 3.1) and the divergence of a countable
sum of i.i.d. exponentials; the second is the Borel–Cantelli step (3.20)–(3.22) once the rates
satisfy (3.21) for the finitely many `K ≤ n` at each stage `n` — which avoids the strong
Markov reduction to `η₁` of the paper's Step 1. -/
lemma holdingTimesSummable_of (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (h0 : ∑' k, holding Gs Y w E (addr Gs Y 0 k) = ⊤)
    (h3 : ∀ K, ∑' n, layerTime Gs Y w E (n + 1) (addr Gs Y 0 K) < ⊤) :
    HoldingTimesSummable Gs Y w E :=
  ⟨totalTime_eq_top Gs Y w E h0, fun _ hη => tau_lt_top_of_level_zero Gs Y w E
    (fun K => (tau_addr_zero_lt_top_iff Gs Y w E h hG hcov K).mpr (h3 K)) hη⟩

lemma exists_level_le_mem (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n) (a : ℕ →₀ ℕ) :
    ∃ m, level a ≤ m ∧ Yxi Gs Y a ∈ Gs m := by
  obtain ⟨n, hn⟩ := hcov (Yxi Gs Y a)
  exact ⟨max (level a) n, le_max_left _ _, hG (le_max_right _ _) hn⟩

open Classical in
/-- (3.24): the successor `ξ̂` of `ξ`, read at a level `m ≥ level ξ` with `Y_ξ ∈ VG_m` (the
paper's "let `m ≥ n_z` be chosen so that `Y_ξ ∈ G_m`"; the result does not depend on the
choice, being the immediate successor in `Ξ`); `ξ` itself if there is no such level. -/
noncomputable def succ (a : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  if h : ∃ m, level a ≤ m ∧ Yxi Gs Y a ∈ Gs m then succAt Gs Y (Classical.choose h) a else a

/-- `ξ̂ ∈ Ξ`, `ξ < ξ̂`, and nothing in `Ξ` lies strictly between them (p. 23). -/
lemma Consistent.succ_spec (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) :
    Realized Gs Y (succ Gs Y a) ∧ toLex a < toLex (succ Gs Y a) ∧
      ∀ b, Realized Gs Y b → ¬ (toLex a < toLex b ∧ toLex b < toLex (succ Gs Y a)) := by
  have hx := exists_level_le_mem Gs Y hG hcov a
  have hspec := Classical.choose_spec hx
  have hrep : ∃ j, addr Gs Y (Classical.choose hx) j = a :=
    ⟨_, addr_tm_of_level_le Gs Y ha hspec.1⟩
  unfold succ
  rw [dif_pos hx]
  refine ⟨realized_succAt Gs Y _ a, ?_, fun b hb => h.not_lt_lt_succAt Gs Y hG hrep hspec.2 hb⟩
  rw [succAt, lt_iff_tm_lt Gs Y hrep ⟨_, rfl⟩, tm_addr]
  exact Nat.lt_succ_self _

/-- `η < η'` in `Ξ` forces `η̂ ≤ η'`, hence `τ_{η̂} ≤ τ_{η'}`: the holding intervals of (3.26)
are ordered like their labels. -/
lemma Consistent.tau_succ_le (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {η η' : ℕ →₀ ℕ} (hη : Realized Gs Y η) (hη' : Realized Gs Y η')
    (hlt : toLex η < toLex η') : tau Gs Y w E (succ Gs Y η) ≤ tau Gs Y w E η' := by
  apply tau_mono
  by_contra hc
  exact (h.succ_spec Gs Y hG hcov hη).2.2 η' hη' ⟨hlt, not_le.mp hc⟩

/-- `t ∈ [τ_η, τ_{η̂})` for `η ∈ Ξ`. -/
def InInterval (η : ℕ →₀ ℕ) (t : ℝ≥0∞) : Prop :=
  Realized Gs Y η ∧ tau Gs Y w E η ≤ t ∧ t < tau Gs Y w E (succ Gs Y η)

/-- The intervals `[τ_η, τ_{η̂})`, `η ∈ Ξ`, are pairwise disjoint, so (3.26) is well defined. -/
lemma Consistent.inInterval_unique (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {η η' : ℕ →₀ ℕ} {t : ℝ≥0∞}
    (h1 : InInterval Gs Y w E η t) (h2 : InInterval Gs Y w E η' t) : η = η' := by
  rcases lt_trichotomy (toLex η) (toLex η') with hlt | heq | hlt
  · exact absurd (lt_of_le_of_lt
      (le_trans (h.tau_succ_le Gs Y w E hG hcov h1.1 h2.1 hlt) h2.2.1) h1.2.2) (lt_irrefl _)
  · exact toLex_inj.mp heq
  · exact absurd (lt_of_le_of_lt
      (le_trans (h.tau_succ_le Gs Y w E hG hcov h2.1 h1.1 hlt) h1.2.1) h2.2.2) (lt_irrefl _)

open Classical in
/-- (3.26): `X_t := Y_η` for `t ∈ [τ_η, τ_{η̂})`, and `X_t := ∞` (`none`) if `t` lies in no such
interval.  Time is `[0,∞) = ℝ≥0`, as in `Theorem16Statement`. -/
noncomputable def X (t : ℝ≥0) : Option V :=
  if h : ∃ η, InInterval Gs Y w E η t then some (Yxi Gs Y (Classical.choose h)) else none

lemma Consistent.X_eq_of_inInterval (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {η : ℕ →₀ ℕ} {t : ℝ≥0} (hη : InInterval Gs Y w E η t) :
    X Gs Y w E t = some (Yxi Gs Y η) := by
  unfold X
  rw [dif_pos ⟨η, hη⟩]
  have hu := h.inInterval_unique Gs Y w E hG hcov
    (Classical.choose_spec (⟨η, hη⟩ : ∃ η, InInterval Gs Y w E η t)) hη
  exact congrArg (fun a => some (Yxi Gs Y a)) hu

lemma X_eq_none_iff (t : ℝ≥0) : X Gs Y w E t = none ↔ ¬ ∃ η, InInterval Gs Y w E η t := by
  unfold X
  split_ifs with hx <;> simp [hx]

end time

/-! ### Measurability of the coarsening map

The coupling of Lemma 3.4 is built (see the module docstring) from the regular conditional
law of the level-`(n+1)` path given its coarsening `k ↦ Y^{n+1}_{J^{n,n+1}_k}`.  For that, the
coarsening must be a measurable map of path space `ℕ → V` (product σ-algebra).  This section
proves it, for any measurable `S`, by rewriting one step of (3.9) as a *total* `Nat.find` and
using `measurable_find` together with the countable-fibre lemma
`measurable_from_prod_countable_left`. -/

section measurability

open MeasureTheory

/-- The next visit to `S` after time `m` exists in the following total form: the first `j > m`
with `p j ∈ S`, or `m + 1` if `p` never visits `S` after `m`. -/
lemma exists_next (S : Set V) (p : ℕ → V) (m : ℕ) :
    ∃ j, m < j ∧ (p j ∈ S ∨ ∀ i, m < i → p i ∉ S) := by
  by_cases h : ∃ j, m < j ∧ p j ∈ S
  · obtain ⟨j, hj, hjS⟩ := h
    exact ⟨j, hj, Or.inl hjS⟩
  · exact ⟨m + 1, Nat.lt_succ_self m, Or.inr fun i hi hiS => h ⟨i, hi, hiS⟩⟩

open Classical in
/-- One step of (3.9) from time `m`, as a total function of the path. -/
noncomputable def step (S : Set V) (m : ℕ) (p : ℕ → V) : ℕ :=
  if p m ∈ S then m + 1 else Nat.find (exists_next S p m)

open Classical in
lemma find_next_of_exists {S : Set V} {p : ℕ → V} {m : ℕ} (h : ∃ j, m < j ∧ p j ∈ S) :
    Nat.find (exists_next S p m) = Nat.find h := by
  rw [Nat.find_eq_iff]
  refine ⟨⟨(Nat.find_spec h).1, Or.inl (Nat.find_spec h).2⟩, fun i hi => ?_⟩
  rintro ⟨hmi, hor⟩
  rcases hor with hiS | hnone
  · exact Nat.find_min h hi ⟨hmi, hiS⟩
  · obtain ⟨j, hj, hjS⟩ := h
    exact hnone j hj hjS

open Classical in
lemma find_next_of_not_exists {S : Set V} {p : ℕ → V} {m : ℕ} (h : ¬ ∃ j, m < j ∧ p j ∈ S) :
    Nat.find (exists_next S p m) = m + 1 := by
  rw [Nat.find_eq_iff]
  refine ⟨⟨Nat.lt_succ_self m, Or.inr fun i hi hiS => h ⟨i, hi, hiS⟩⟩, fun i hi => ?_⟩
  rintro ⟨hmi, -⟩
  omega

open Classical in
/-- (3.9) as an iteration of `step`. -/
lemma coarsen_succ_eq_step (S : Set V) (p : ℕ → V) (k : ℕ) :
    coarsen S p (k + 1) = step S (coarsen S p k) p := by
  rw [coarsen, step]
  by_cases h1 : p (coarsen S p k) ∈ S
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : ∃ j, coarsen S p k < j ∧ p j ∈ S
    · rw [dif_pos h2, find_next_of_exists h2]
    · rw [dif_neg h2, find_next_of_not_exists h2]

variable [MeasurableSpace V] {S : Set V}

lemma measurableSet_next (hS : MeasurableSet S) (m j : ℕ) :
    MeasurableSet {p : ℕ → V | m < j ∧ (p j ∈ S ∨ ∀ i, m < i → p i ∉ S)} := by
  have e : {p : ℕ → V | m < j ∧ (p j ∈ S ∨ ∀ i, m < i → p i ∉ S)} =
      {_p : ℕ → V | m < j} ∩ ((fun p : ℕ → V => p j) ⁻¹' S ∪
        ⋂ i, ⋂ (_ : m < i), ((fun p : ℕ → V => p i) ⁻¹' S)ᶜ) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage,
      Set.mem_iInter, Set.mem_compl_iff]
  rw [e]
  refine (MeasurableSet.const _).inter (((measurable_pi_apply j) hS).union ?_)
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    ((measurable_pi_apply i) hS).compl

open Classical in
lemma measurable_step (hS : MeasurableSet S) (m : ℕ) :
    Measurable fun p : ℕ → V => step S m p := by
  unfold step
  refine Measurable.ite ((measurable_pi_apply m) hS) measurable_const ?_
  exact measurable_find (fun p => exists_next S p m) (measurableSet_next hS m)

/-- The coarsening times `J_k` of (3.9) are measurable functions of the path. -/
lemma measurable_coarsen (hS : MeasurableSet S) (k : ℕ) :
    Measurable fun p : ℕ → V => coarsen S p k := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have h1 : Measurable fun q : (ℕ → V) × ℕ => step S q.2 q.1 :=
      measurable_from_prod_countable_left fun m => measurable_step hS m
    have h2 : Measurable fun p : ℕ → V => (p, coarsen S p k) := measurable_id.prodMk ih
    have e : (fun p : ℕ → V => coarsen S p (k + 1)) = fun p => step S (coarsen S p k) p :=
      funext fun p => coarsen_succ_eq_step S p k
    rw [e]
    exact h1.comp h2

/-- The coarsened path `k ↦ p (J_k)`: the paper's `{Y^n_{J^{m,n}_k}}_{k ≥ 0}`, which by
Lemma 3.3 has the law of `Y^m`. -/
noncomputable def coarsenPath (S : Set V) (p : ℕ → V) : ℕ → V := fun k => p (coarsen S p k)

/-- The coarsening is a measurable self-map of path space: this is what makes the regular
conditional law `condDistrib id (coarsenPath S) (law of Y^{n+1})` of the module docstring
available. -/
lemma measurable_coarsenPath (hS : MeasurableSet S) :
    Measurable (coarsenPath S : (ℕ → V) → ℕ → V) := by
  refine measurable_pi_iff.mpr fun k => ?_
  have h1 : Measurable fun q : (ℕ → V) × ℕ => q.1 q.2 :=
    measurable_from_prod_countable_left fun j => measurable_pi_apply j
  exact h1.comp (measurable_id.prodMk (measurable_coarsen hS k))

omit [MeasurableSpace V] in
/-- (3.12) restated: the sample is consistent iff each level is the coarsening of the next. -/
lemma consistent_iff (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) :
    Consistent Gs Y ↔ ∀ n, coarsenPath (Gs n) (Y (n + 1)) = Y n :=
  ⟨fun h n => funext fun k => h n k, fun h n k => congrFun (h n) k⟩

end measurability

end ReflectedWalk.IndexSet
