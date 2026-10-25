module

/- Fresh vertex/depth indices and finite products for independent cell reads.
The cursor advances at each departure, so repeated visits always read a new cell. -/
public import LatticeProb.Graph.CyclePopping.Basic
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-! Fresh vertex/depth indices and finite products for independent cell reads.
The cursor advances at each departure, so repeated visits always read a new cell. -/

set_option autoImplicit false

namespace LatticeProb.Prob.AdaptiveReads

open MeasureTheory ProbabilityTheory LatticeProb.Graph.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V : Type*}

/-- The cursor after departures `p 0, ..., p (n-1)`, starting at `k`. -/
def departureCursor (p : ℕ → V) (k : Cursor V) : ℕ → Cursor V
  | 0 => k
  | n + 1 => pop (departureCursor p k n) {p n}

/-- The actual depth and vertex queried at departure `n`. -/
def readIndex (p : ℕ → V) (k : Cursor V) (n : ℕ) : ℕ × V :=
  (departureCursor p k n (p n), p n)

/-- Departure cursors are coordinatewise increasing in time. -/
theorem departure_cursor_mono (p : ℕ → V) (k : Cursor V) {i j : ℕ} (hij : i ≤ j) :
    departureCursor p k i ≤ departureCursor p k j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact le_trans ih (le_pop _ _)

/-- An earlier read at a vertex lies strictly below its cursor at any later time. -/
theorem read_depth_lt (p : ℕ → V) (k : Cursor V) {i j : ℕ} (hij : i < j) :
    departureCursor p k i (p i) < departureCursor p k j (p i) := by
  have hm := departure_cursor_mono p k (Nat.succ_le_of_lt hij) (p i)
  have hs : departureCursor p k (i + 1) (p i) = departureCursor p k i (p i) + 1 :=
    pop_apply_of_mem _ _ (Finset.mem_singleton_self _)
  rw [hs] at hm
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hm

/-- Every vertex/depth read is fresh, including along paths with repeated vertices. -/
theorem read_index_injective (p : ℕ → V) (k : Cursor V) :
    Function.Injective (readIndex p k) := by
  intro i j he
  have hv : p i = p j := congrArg Prod.snd he
  have hd : departureCursor p k i (p i) = departureCursor p k j (p j) :=
    congrArg Prod.fst he
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [← hv] at hd
    exact False.elim ((read_depth_lt p k hij).ne hd)
  · exact hij
  · rw [hv] at hd
    exact False.elim ((read_depth_lt p k hij).ne hd.symm)

variable {Ω K : Type*} [MeasurableSpace Ω] {A : K → Type*}
variable [∀ q, MeasurableSpace (A q)] [∀ q, MeasurableSingletonClass (A q)]

/-- **Measure finite reads of injectivity.** A fixed finite transcript of distinct independent cells has the product of its
individual cell masses. Adaptivity is handled by proving an exact transcript-cylinder
identity and constructing the distinct read indices in each application. -/
theorem measure_finite_reads_of_injective (P : Measure Ω) (X : ∀ q, Ω → A q)
    (hind : iIndepFun X P) (n : ℕ) (q : Fin n → K) (hq : Function.Injective q)
    (a : ∀ i, A (q i)) :
    P {ω | ∀ i, X (q i) ω = a i} = ∏ i, P {ω | X (q i) ω = a i} := by
  have hi : iIndepFun (fun i : Fin n => X (q i)) P := hind.precomp hq
  have h := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => {a i}) (fun i _ => measurableSet_singleton (a i))
  have he : {ω | ∀ i, X (q i) ω = a i} =
      ⋂ i ∈ (Finset.univ : Finset (Fin n)), X (q i) ⁻¹' {a i} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_univ, forall_const]
  rw [he]
  exact h

end

end LatticeProb.Prob.AdaptiveReads
