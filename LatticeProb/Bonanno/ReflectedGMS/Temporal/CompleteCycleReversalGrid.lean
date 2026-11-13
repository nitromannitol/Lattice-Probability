/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CompleteCycleReversalGrid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedCycleReversal
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Complete-cycle reversal from grid reversal (regeneration milestone 2(b), abstract half)

`Temporal/TwoSidedCycleReversal.CompleteCycleReversal ν` asks `ν.map cycRev = ν` for a law `ν`
of complete cycles from `v` (holding at `v`, then an excursion, killed at the first complete
return); `cycRev` keeps the holding in front and reverses the excursion right-continuously
(through left limits).  This module proves it for the image `μ.map fc` of ANY law `μ` whose
paths are almost surely regular complete cycles (`GoodCyc`) and whose **grid words satisfy
the discrete block reversal** (`hgrid`): on every grid of mesh `1/(N+1)`, the probability of a
word `w₀ … wₙ` that holds at `v` on `[0,a)` and ends at `v` is unchanged when its excursion
block `[a, n)` is read backwards (`wordRev`).  For a reversible Markov family this is detailed
balance along the loop `v → w_a → ⋯ → w_{n-1} → v`
(`Temporal/CompleteCycleReversalProof` discharges it at the actual area walk).

No semigroup, no excursion theory and no non-explosion input: the proof is a **pure grid
limit**.

* **Discrete identity** (`measure_revSetT_eq`): the discrete cycle of a grid sequence (first
  exit index `a`, first return index `n`, `DCyc`) is unique, so the event "the discrete cycle
  satisfies a finite observable" splits over `(a, n)` into countable unions of grid words,
  and `hgrid` identifies the law of the word, restricted to the cycle words, with its image
  under the block reversal (`ext_of_singleton` on the countable word space).
* **Deterministic convergence** (`GoodCyc.eventually_mem_fwd`, `…_rev`): along every regular
  complete cycle, for all fine enough grids the discrete cycle indices are the ceilings
  `⌈h(N+1)⌉`, `⌈L(N+1)⌉` of the holding and return times, the forward read at index
  `⌈t(N+1)⌉ + 1` is the path strictly after `t` (right regularity), and the reversed read is
  the path strictly before `L + h − t` (the index shift `+ 1` makes it one-sided), i.e. the left
  limit (`HasLeftLimits`).  No time needs to avoid a jump time: all discrete indicators are
  eventually equal to their limits at every good path.
* The finite-dimensional sets `cylS F s` (finitely many prescribed labels, cycle length `< s`)
  form a π-system generating the σ-algebra of `Cyc v` (`generateFrom_cylSys`); both sides of
  the reversal identity are limits of the same discrete masses
  (`tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure`).

Main theorem: `completeCycleReversal_of_grid`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleReversalGrid

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TwoSidedCycleSplice

instance instMeasurableSingletonClassOptionNat : MeasurableSingletonClass (Option ℕ) :=
  ⟨fun _ => measurableSet_option _⟩

/-! ### 1. Grid meshes and ceiling indices -/

/-- The grid mesh `1 / (N + 1)`. -/
noncomputable def gδ (N : ℕ) : ℝ≥0 := ((N : ℝ≥0) + 1)⁻¹

theorem gδ_pos (N : ℕ) : 0 < gδ N := inv_pos.2 (by positivity)

/-- The ceiling index of a time on the grid of mesh `gδ N`. -/
noncomputable def ci (N : ℕ) (t : ℝ≥0) : ℕ := ⌈t * ((N : ℝ≥0) + 1)⌉₊

theorem lt_ci_iff {N k : ℕ} {t : ℝ≥0} : k < ci N t ↔ (k : ℝ≥0) * gδ N < t := by
  rw [ci, Nat.lt_ceil, gδ, mul_inv_lt_iff₀ (by positivity)]

theorem ci_le_iff {N k : ℕ} {t : ℝ≥0} : ci N t ≤ k ↔ t ≤ (k : ℝ≥0) * gδ N := by
  rw [ci, Nat.ceil_le, gδ, le_mul_inv_iff₀ (by positivity)]

theorem le_ci_mul (N : ℕ) (t : ℝ≥0) : t ≤ (ci N t : ℝ≥0) * gδ N := ci_le_iff.1 le_rfl

theorem ci_mul_lt (N : ℕ) (t : ℝ≥0) : (ci N t : ℝ≥0) * gδ N < t + gδ N := by
  have hpos : (0 : ℝ≥0) < (N : ℝ≥0) + 1 := by positivity
  have h := Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ t * ((N : ℝ≥0) + 1) by positivity)
  have h2 := mul_lt_mul_of_pos_right h (inv_pos.2 hpos)
  rw [add_mul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one, one_mul] at h2
  exact h2

theorem ci_mono (N : ℕ) : Monotone (ci N) := fun _ _ h =>
  Nat.ceil_mono (mul_le_mul_of_nonneg_right h (by positivity))

/-- The ceiling bounds, in `ℝ`. -/
theorem ci_real (N : ℕ) (t : ℝ≥0) :
    (t : ℝ) ≤ (ci N t : ℝ) * (gδ N : ℝ) ∧ (ci N t : ℝ) * (gδ N : ℝ) < t + gδ N := by
  constructor
  · exact_mod_cast le_ci_mul N t
  · exact_mod_cast ci_mul_lt N t

theorem one_le_ci {N : ℕ} {t : ℝ≥0} (ht : 0 < t) : 1 ≤ ci N t :=
  lt_ci_iff.2 (by rw [Nat.cast_zero, zero_mul]; exact ht)

theorem eventually_gδ_lt {ε : ℝ≥0} (hε : 0 < ε) : ∀ᶠ N in atTop, gδ N < ε := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ε⁻¹
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hpos : (0 : ℝ≥0) < (N : ℝ≥0) + 1 := by positivity
  rw [gδ, inv_lt_comm₀ hpos hε]
  calc ε⁻¹ < N₀ := hN₀
    _ ≤ N := by exact_mod_cast hN
    _ < (N : ℝ≥0) + 1 := lt_add_one _

theorem tendsto_gδ : Tendsto gδ atTop (𝓝 0) := by
  rw [tendsto_order]
  exact ⟨fun a ha => absurd ha (by simp), fun a ha => eventually_gδ_lt ha⟩

theorem eventually_add_mul_gδ_lt {t b : ℝ≥0} (h : t < b) (c : ℝ≥0) :
    ∀ᶠ N in atTop, t + c * gδ N < b := by
  have ht : Tendsto (fun N => t + c * gδ N) atTop (𝓝 (t + c * 0)) :=
    tendsto_const_nhds.add (tendsto_gδ.const_mul c)
  rw [mul_zero, add_zero] at ht
  exact ht.eventually (gt_mem_nhds h)

/-- The same bound, read in `ℝ`. -/
theorem eventually_add_mul_gδ_lt_real {t b : ℝ≥0} (h : t < b) (c : ℕ) :
    ∀ᶠ N in atTop, (t : ℝ) + (c : ℝ) * gδ N < b := by
  filter_upwards [eventually_add_mul_gδ_lt h (c : ℝ≥0)] with N hN
  exact_mod_cast hN

/-! ### 2. Grid sequences, words, the discrete cycle and its block reversal -/

/-- The grid sequence of a trajectory at mesh `gδ N`. -/
noncomputable def gridSeq (N : ℕ) (x : Trajectory ℕ) : ℕ → Option ℕ :=
  fun k => x ((k : ℝ≥0) * gδ N)

/-- The grid word of length `n + 1`. -/
noncomputable def gridWord (N n : ℕ) (x : Trajectory ℕ) : Fin (n + 1) → Option ℕ :=
  fun k => gridSeq N x k

theorem measurable_gridWord (N n : ℕ) : Measurable (gridWord N n) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- A word, extended by `none` beyond its length. -/
def wext {n : ℕ} (w : Fin (n + 1) → Option ℕ) : ℕ → Option ℕ :=
  fun k => if hk : k < n + 1 then w ⟨k, hk⟩ else none

theorem wext_gridWord {N n k : ℕ} (hk : k ≤ n) (x : Trajectory ℕ) :
    wext (gridWord N n x) k = gridSeq N x k := by
  simp only [wext, gridWord, dif_pos (Nat.lt_succ_of_le hk)]

/-- **The discrete complete cycle** of a sequence: at `v` on the indices `< a`, off `v` on
`[a, n)`, back at `v` at `n`. -/
structure DCyc (v a n : ℕ) (y : ℕ → Option ℕ) : Prop where
  one_le : 1 ≤ a
  lt : a < n
  hold : ∀ k, k < a → y k = some v
  exc : ∀ k, a ≤ k → k < n → y k ≠ some v
  ret : y n = some v

theorem DCyc.congr {v a n : ℕ} {y y' : ℕ → Option ℕ} (h : DCyc v a n y)
    (hyy : ∀ k, k ≤ n → y k = y' k) : DCyc v a n y' where
  one_le := h.one_le
  lt := h.lt
  hold k hk := (hyy k (by have := h.lt; omega)).symm.trans (h.hold k hk)
  exc k hk1 hk2 := by rw [← hyy k hk2.le]; exact h.exc k hk1 hk2
  ret := (hyy n le_rfl).symm.trans h.ret

/-- The discrete cycle of a sequence is unique. -/
theorem DCyc.unique {v a n a' n' : ℕ} {y : ℕ → Option ℕ} (h : DCyc v a n y)
    (h' : DCyc v a' n' y) : a = a' ∧ n = n' := by
  have ha : a = a' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact h.exc a le_rfl h.lt (h'.hold a hlt)
    · exact h'.exc a' le_rfl h'.lt (h.hold a' hlt)
  subst ha
  refine ⟨rfl, ?_⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.exc n h.lt.le hlt h.ret
  · exact h.exc n' h'.lt.le hlt h'.ret

/-- The block reversal of `[a, n)` on sequences. -/
def blockRev (a n : ℕ) (y : ℕ → Option ℕ) : ℕ → Option ℕ :=
  fun k => if a ≤ k ∧ k < n then y (n + a - 1 - k) else y k

theorem blockRev_blockRev (a n : ℕ) (y : ℕ → Option ℕ) : blockRev a n (blockRev a n y) = y := by
  funext k
  simp only [blockRev]
  split_ifs with h1 h2
  · congr 1
    omega
  · exfalso
    omega
  · rfl

theorem DCyc.blockRev {v a n : ℕ} {y : ℕ → Option ℕ} (h : DCyc v a n y) :
    DCyc v a n (blockRev a n y) where
  one_le := h.one_le
  lt := h.lt
  hold k hk := by
    simp only [ReflectedGMS.CycleReversalGrid.blockRev]
    rw [if_neg (by omega)]
    exact h.hold k hk
  exc k hk1 hk2 := by
    simp only [ReflectedGMS.CycleReversalGrid.blockRev]
    rw [if_pos ⟨hk1, hk2⟩]
    have := h.one_le
    exact h.exc _ (by omega) (by omega)
  ret := by
    simp only [ReflectedGMS.CycleReversalGrid.blockRev]
    rw [if_neg (by omega)]
    exact h.ret

theorem dcyc_blockRev_iff {v a n : ℕ} {y : ℕ → Option ℕ} :
    DCyc v a n (blockRev a n y) ↔ DCyc v a n y :=
  ⟨fun h => by simpa only [blockRev_blockRev] using h.blockRev, fun h => h.blockRev⟩

/-- The block reversal of `[a, n)` on words of length `n + 1`. -/
def wordRev {n : ℕ} (a : ℕ) (w : Fin (n + 1) → Option ℕ) : Fin (n + 1) → Option ℕ :=
  fun k => if hk : a ≤ (k : ℕ) ∧ (k : ℕ) < n then w ⟨n + a - 1 - k, by omega⟩ else w k

theorem wext_wordRev {n : ℕ} (a : ℕ) (w : Fin (n + 1) → Option ℕ) :
    wext (wordRev a w) = blockRev a n (wext w) := by
  funext k
  simp only [wext, wordRev, blockRev]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem wordRev_wordRev {n : ℕ} (a : ℕ) (w : Fin (n + 1) → Option ℕ) :
    wordRev a (wordRev a w) = w := by
  funext k
  simp only [wordRev]
  split_ifs with h1 h2
  · congr 1
    exact Fin.ext (show n + a - 1 - (n + a - 1 - (k : ℕ)) = k by omega)
  · exfalso
    exact h2 ⟨by omega, by omega⟩
  · rfl

theorem measurable_wordRev {n : ℕ} (a : ℕ) : Measurable (wordRev (n := n) a) := by
  refine measurable_pi_iff.2 fun k => ?_
  simp only [wordRev]
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

/-! ### 3. The discrete observables and the discrete reversal identity -/

/-- The discrete cycle killed at index `n`, read at the index `⌈t (N+1)⌉ + 1`. -/
noncomputable def dRead (N n : ℕ) (y : ℕ → Option ℕ) (t : ℝ≥0) : Option ℕ :=
  if ci N t + 1 < n then y (ci N t + 1) else none

/-- The discrete finite-dimensional observable: finitely many prescribed labels and a length
bound. -/
def Obs (N n : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) (y : ℕ → Option ℕ) : Prop :=
  (∀ p ∈ F, dRead N n y p.1 = some p.2) ∧ (n : ℝ≥0) * gδ N < s

theorem obs_congr {N n : ℕ} {F : Finset (ℝ≥0 × ℕ)} {s : ℝ≥0} {y y' : ℕ → Option ℕ}
    (hyy : ∀ k, k < n → y k = y' k) : Obs N n F s y ↔ Obs N n F s y' := by
  have hr : ∀ t, dRead N n y t = dRead N n y' t := by
    intro t
    unfold dRead
    split_ifs with h
    · exact hyy _ h
    · rfl
  simp only [Obs, hr]

/-- The words whose discrete cycle is `(a, n)` and satisfies the observable. -/
def fwdWords (v N a n : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) : Set (Fin (n + 1) → Option ℕ) :=
  {w | DCyc v a n (wext w) ∧ Obs N n F s (wext w)}

/-- The words whose discrete cycle is `(a, n)` and whose block reversal satisfies the
observable. -/
def revWords (v N a n : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) : Set (Fin (n + 1) → Option ℕ) :=
  {w | DCyc v a n (wext w) ∧ Obs N n F s (wext (wordRev a w))}

/-- The discrete forward event. -/
def fwdSetT (v N : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) : Set (Trajectory ℕ) :=
  ⋃ p : ℕ × ℕ, gridWord N p.2 ⁻¹' fwdWords v N p.1 p.2 F s

/-- The discrete reversed event. -/
def revSetT (v N : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) : Set (Trajectory ℕ) :=
  ⋃ p : ℕ × ℕ, gridWord N p.2 ⁻¹' revWords v N p.1 p.2 F s

theorem measurableSet_fwdSetT (v N : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) :
    MeasurableSet (fwdSetT v N F s) :=
  MeasurableSet.iUnion fun p => measurable_gridWord N p.2 (Set.to_countable _).measurableSet

theorem measurableSet_revSetT (v N : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) :
    MeasurableSet (revSetT v N F s) :=
  MeasurableSet.iUnion fun p => measurable_gridWord N p.2 (Set.to_countable _).measurableSet

theorem dcyc_gridSeq_of_wext {v N a n : ℕ} {x : Trajectory ℕ}
    (h : DCyc v a n (wext (gridWord N n x))) : DCyc v a n (gridSeq N x) :=
  h.congr fun k hk => wext_gridWord hk x

theorem pairwise_disjoint_pieces {α : Type*} (X : α → Trajectory ℕ) (v N : ℕ)
    (S : ∀ a n : ℕ, Set (Fin (n + 1) → Option ℕ))
    (hS : ∀ a n w, w ∈ S a n → DCyc v a n (wext w)) :
    Pairwise (Function.onFun Disjoint fun p : ℕ × ℕ => (gridWord N p.2 ∘ X) ⁻¹' S p.1 p.2) := by
  intro p q hpq
  refine Set.disjoint_left.2 fun z hp hq => hpq ?_
  have h1 := dcyc_gridSeq_of_wext (hS _ _ _ hp)
  have h2 := dcyc_gridSeq_of_wext (hS _ _ _ hq)
  obtain ⟨ha, hn⟩ := h1.unique h2
  exact Prod.ext ha hn

/-- **The block reversal preserves the law of the cycle words.** -/
theorem map_wordRev_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {X : α → Trajectory ℕ} (hX : Measurable X) {v N a n : ℕ}
    (hgrid : ∀ w : Fin (n + 1) → Option ℕ, DCyc v a n (wext w) →
      μ ((gridWord N n ∘ X) ⁻¹' {w}) = μ ((gridWord N n ∘ X) ⁻¹' {wordRev a w})) :
    ((μ.map (gridWord N n ∘ X)).restrict {w | DCyc v a n (wext w)}).map (wordRev a) =
      (μ.map (gridWord N n ∘ X)).restrict {w | DCyc v a n (wext w)} := by
  have hg : Measurable (gridWord N n ∘ X) := (measurable_gridWord N n).comp hX
  have hC : MeasurableSet {w : Fin (n + 1) → Option ℕ | DCyc v a n (wext w)} :=
    (Set.to_countable _).measurableSet
  have hmem : ∀ w : Fin (n + 1) → Option ℕ,
      DCyc v a n (wext (wordRev a w)) ↔ DCyc v a n (wext w) := fun w => by
    rw [wext_wordRev]
    exact dcyc_blockRev_iff
  refine Measure.ext_of_singleton fun w => ?_
  rw [Measure.map_apply (measurable_wordRev a) (measurableSet_singleton w),
    Measure.restrict_apply ((measurable_wordRev a) (measurableSet_singleton w)),
    Measure.restrict_apply (measurableSet_singleton w)]
  have hpre : wordRev a ⁻¹' {w} = {wordRev a w} := by
    ext w'
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · rintro rfl
      rw [wordRev_wordRev]
    · rintro rfl
      exact wordRev_wordRev a w
  rw [hpre]
  by_cases hw : DCyc v a n (wext w)
  · have hw' : DCyc v a n (wext (wordRev a w)) := (hmem w).2 hw
    rw [Set.inter_eq_left.2 (Set.singleton_subset_iff.2
        (show wordRev a w ∈ {w : Fin (n + 1) → Option ℕ | DCyc v a n (wext w)} from hw')),
      Set.inter_eq_left.2 (Set.singleton_subset_iff.2
        (show w ∈ {w : Fin (n + 1) → Option ℕ | DCyc v a n (wext w)} from hw)),
      Measure.map_apply hg (measurableSet_singleton _),
      Measure.map_apply hg (measurableSet_singleton _), hgrid w hw]
  · have hw' : ¬ DCyc v a n (wext (wordRev a w)) := fun h => hw ((hmem w).1 h)
    rw [Set.singleton_inter_eq_empty.2
        (show wordRev a w ∉ {w : Fin (n + 1) → Option ℕ | DCyc v a n (wext w)} from hw'),
      Set.singleton_inter_eq_empty.2
        (show w ∉ {w : Fin (n + 1) → Option ℕ | DCyc v a n (wext w)} from hw)]

/-- **The discrete reversal identity.** -/
theorem measure_revSetT_eq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {X : α → Trajectory ℕ} (hX : Measurable X) {v : ℕ}
    (hgrid : ∀ (N a n : ℕ) (w : Fin (n + 1) → Option ℕ), DCyc v a n (wext w) →
      μ ((gridWord N n ∘ X) ⁻¹' {w}) = μ ((gridWord N n ∘ X) ⁻¹' {wordRev a w}))
    (N : ℕ) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) :
    μ (X ⁻¹' revSetT v N F s) = μ (X ⁻¹' fwdSetT v N F s) := by
  have hr : X ⁻¹' revSetT v N F s =
      ⋃ p : ℕ × ℕ, (gridWord N p.2 ∘ X) ⁻¹' revWords v N p.1 p.2 F s := by
    rw [revSetT, Set.preimage_iUnion]
    rfl
  have hf : X ⁻¹' fwdSetT v N F s =
      ⋃ p : ℕ × ℕ, (gridWord N p.2 ∘ X) ⁻¹' fwdWords v N p.1 p.2 F s := by
    rw [fwdSetT, Set.preimage_iUnion]
    rfl
  have hdr : Pairwise (Function.onFun Disjoint
      fun p : ℕ × ℕ => (gridWord N p.2 ∘ X) ⁻¹' revWords v N p.1 p.2 F s) :=
    pairwise_disjoint_pieces X v N (fun a n => revWords v N a n F s) fun _ _ _ hw => hw.1
  have hdf : Pairwise (Function.onFun Disjoint
      fun p : ℕ × ℕ => (gridWord N p.2 ∘ X) ⁻¹' fwdWords v N p.1 p.2 F s) :=
    pairwise_disjoint_pieces X v N (fun a n => fwdWords v N a n F s) fun _ _ _ hw => hw.1
  rw [hr, hf,
    measure_iUnion hdr
      (fun p => ((measurable_gridWord N p.2).comp hX) (Set.to_countable _).measurableSet),
    measure_iUnion hdf
      (fun p => ((measurable_gridWord N p.2).comp hX) (Set.to_countable _).measurableSet)]
  refine tsum_congr fun p => ?_
  obtain ⟨a, n⟩ := p
  have hg : Measurable (gridWord N n ∘ X) := (measurable_gridWord N n).comp hX
  have hB : MeasurableSet {w : Fin (n + 1) → Option ℕ | Obs N n F s (wext w)} :=
    (Set.to_countable _).measurableSet
  have hC : MeasurableSet {w : Fin (n + 1) → Option ℕ | DCyc v a n (wext w)} :=
    (Set.to_countable _).measurableSet
  have hrev : revWords v N a n F s = wordRev a ⁻¹' {w | Obs N n F s (wext w)} ∩
      {w | DCyc v a n (wext w)} := by
    ext w
    simp only [revWords, mem_inter_iff, mem_preimage, mem_setOf_eq]
    exact and_comm
  have hfwd : fwdWords v N a n F s = {w | Obs N n F s (wext w)} ∩
      {w | DCyc v a n (wext w)} := by
    ext w
    simp only [fwdWords, mem_inter_iff, mem_setOf_eq]
    exact and_comm
  show μ ((gridWord N n ∘ X) ⁻¹' revWords v N a n F s) =
    μ ((gridWord N n ∘ X) ⁻¹' fwdWords v N a n F s)
  rw [hrev, hfwd, ← Measure.map_apply hg ((measurable_wordRev a hB).inter hC),
    ← Measure.map_apply hg (hB.inter hC),
    ← Measure.restrict_apply (measurable_wordRev a hB), ← Measure.restrict_apply hB,
    ← Measure.map_apply (measurable_wordRev a) hB,
    map_wordRev_restrict μ hX (fun w hw => hgrid N a n w hw)]

/-! ### 4. Regular complete cycles and the deterministic grid limit -/

/-- **A regular complete cycle of a path**: right-regular with left limits, holding at `v` on
`[0, h)`, off `v` on `[h, L)`, back at `v` at `L`. -/
structure GoodCyc (v : ℕ) (x : Trajectory ℕ) (h L : ℝ≥0) : Prop where
  regLL : IsRegLL x
  pos : 0 < h
  lt : h < L
  hold : ∀ t, t < h → x t = some v
  exc : ∀ t, h ≤ t → t < L → x t ≠ some v
  ret : x L = some v

variable {v : ℕ} {x : Trajectory ℕ} {h L : ℝ≥0}

theorem GoodCyc.isCycle (hx : GoodCyc v x h L) : IsCycle v (glue x L cem) L := by
  refine ⟨?_, isRegLL_glue hx.regLL isRegLL_cem _, fun t ht => ?_,
    ⟨h, hx.pos, hx.lt, fun t ht => ?_, fun t h1 h2 => ?_⟩⟩
  · rw [glue_of_lt (hx.pos.trans hx.lt)]
    exact hx.hold 0 hx.pos
  · rw [glue_of_le ht]
    rfl
  · rw [glue_of_lt (ht.trans hx.lt)]
    exact hx.hold t ht
  · rw [glue_of_lt h2]
    exact hx.exc t h1 h2

/-- The complete cycle of a good path, as a point of the cycle space. -/
noncomputable def GoodCyc.cyc (hx : GoodCyc v x h L) : Cyc v :=
  ⟨(glue x L cem, L), hx.isCycle⟩

theorem GoodCyc.holdTime_cyc (hx : GoodCyc v x h L) : holdTime hx.cyc = h :=
  holdTime_eq hx.cyc hx.lt
    (fun t ht => by
      show glue x L cem t = some v
      rw [glue_of_lt (ht.trans hx.lt)]
      exact hx.hold t ht)
    (fun t h1 h2 => by
      show glue x L cem t ≠ some v
      rw [glue_of_lt (show t < L from h2)]
      exact hx.exc t h1 (show t < L from h2))

/-- For fine grids the discrete cycle of a good path is `(⌈h(N+1)⌉, ⌈L(N+1)⌉)`. -/
theorem GoodCyc.eventually_dcyc (hx : GoodCyc v x h L) :
    ∀ᶠ N in atTop, DCyc v (ci N h) (ci N L) (gridSeq N x) := by
  obtain ⟨b, hLb, hb⟩ := rr_some hx.regLL.regular hx.ret
  filter_upwards [eventually_add_mul_gδ_lt hLb 1, eventually_add_mul_gδ_lt hx.lt 1] with N h1 h2
  rw [one_mul] at h1 h2
  refine ⟨one_le_ci hx.pos, ?_, fun k hk => hx.hold _ (lt_ci_iff.1 hk),
    fun k hk1 hk2 => hx.exc _ (ci_le_iff.1 hk1) (lt_ci_iff.1 hk2), ?_⟩
  · exact lt_ci_iff.2 ((ci_mul_lt N h).trans h2)
  · exact hb _ (le_ci_mul N L) ((ci_mul_lt N L).trans h1)

/-- The length bound of the discrete cycle converges. -/
theorem GoodCyc.eventually_len (hx : GoodCyc v x h L) (s : ℝ≥0) :
    ∀ᶠ N in atTop, ((ci N L : ℝ≥0) * gδ N < s ↔ L < s) := by
  by_cases hLs : L < s
  · filter_upwards [eventually_add_mul_gδ_lt hLs 1] with N hN
    rw [one_mul] at hN
    exact ⟨fun _ => hLs, fun _ => (ci_mul_lt N L).trans hN⟩
  · filter_upwards with N
    exact ⟨fun h' => absurd ((le_ci_mul N L).trans_lt h') hLs, fun h' => absurd h' hLs⟩

/-- **The forward read converges to the cycle** (right regularity; one-sided from the
right). -/
theorem GoodCyc.eventually_dRead (hx : GoodCyc v x h L) (t : ℝ≥0) (j : ℕ) :
    ∀ᶠ N in atTop, (dRead N (ci N L) (gridSeq N x) t = some j ↔ glue x L cem t = some j) := by
  by_cases htL : t < L
  · have hright : ∃ b, t < b ∧ ∀ s, t < s → s < b → (x s = some j ↔ x t = some j) := by
      cases hxt : x t with
      | some w =>
        obtain ⟨b, htb, hb⟩ := rr_some hx.regLL.regular hxt
        exact ⟨b, htb, fun s h1 h2 => by rw [hb s h1.le h2]⟩
      | none =>
        obtain ⟨b, htb, hb⟩ := rr_none hx.regLL.regular hxt j
        refine ⟨b, htb, fun s h1 h2 => ?_⟩
        simp only [reduceCtorEq, iff_false]
        exact hb s h1 h2
    obtain ⟨b, htb, hb⟩ := hright
    filter_upwards [eventually_add_mul_gδ_lt_real htb 2, eventually_add_mul_gδ_lt_real htL 2]
      with N hNb hNL
    simp only [Nat.cast_ofNat] at hNb hNL
    obtain ⟨hc1, hc2⟩ := ci_real N t
    have hg : (0 : ℝ) < gδ N := by exact_mod_cast gδ_pos N
    have hsplit : ((ci N t : ℝ) + 1) * (gδ N : ℝ) = (ci N t : ℝ) * gδ N + gδ N := by ring
    have hk : ci N t + 1 < ci N L :=
      lt_ci_iff.2 (NNReal.coe_lt_coe.1 (by push_cast; linarith))
    have hτ1 : t < ((ci N t + 1 : ℕ) : ℝ≥0) * gδ N :=
      NNReal.coe_lt_coe.1 (by push_cast; linarith)
    have hτ2 : ((ci N t + 1 : ℕ) : ℝ≥0) * gδ N < b :=
      NNReal.coe_lt_coe.1 (by push_cast; linarith)
    rw [glue_of_lt htL]
    simp only [dRead]
    rw [if_pos hk]
    exact hb _ hτ1 hτ2
  · filter_upwards with N
    have hLt : L ≤ t := not_lt.1 htL
    have hk : ¬ ci N t + 1 < ci N L := by
      have := ci_mono N hLt
      omega
    unfold dRead
    rw [if_neg hk, glue_of_le hLt]
    rfl

/-- The reversed cycle path of a good path, evaluated. -/
theorem GoodCyc.cycRevPath_of_mid (hx : GoodCyc v x h L) {t : ℝ≥0} (hht : h ≤ t) (htL : t < L) :
    cycRevPath (glue x L cem) v h L t = leftLim x (L - (t - h)) := by
  have h1 : t - h < L - h := (tsub_lt_tsub_iff_right hht).2 htL
  rw [cycRevPath, glue_of_le hht, glue_of_lt h1,
    revPiece_of_lt (lt_of_lt_of_le h1 tsub_le_self)]
  have hT : 0 < L - (t - h) := tsub_pos_of_lt (lt_of_lt_of_le h1 tsub_le_self)
  refine leftLim_congr hT fun s hs => ?_
  exact glue_of_lt (lt_of_lt_of_le hs.2 tsub_le_self)

/-- **The reversed read converges to the reversed cycle** (left limits; the index shift makes
the read one-sided from the left). -/
theorem GoodCyc.eventually_dRead_rev (hx : GoodCyc v x h L) (t : ℝ≥0) (j : ℕ) :
    ∀ᶠ N in atTop, (dRead N (ci N L) (blockRev (ci N h) (ci N L) (gridSeq N x)) t = some j ↔
      cycRevPath (glue x L cem) v h L t = some j) := by
  rcases lt_or_ge t h with hth | hht
  · -- inside the holding: both sides read `v`
    filter_upwards [eventually_add_mul_gδ_lt_real hth 2] with N hN
    simp only [Nat.cast_ofNat] at hN
    obtain ⟨hc1, hc2⟩ := ci_real N t
    have hg : (0 : ℝ) < gδ N := by exact_mod_cast gδ_pos N
    have hsplit : ((ci N t : ℝ) + 1) * (gδ N : ℝ) = (ci N t : ℝ) * gδ N + gδ N := by ring
    have hka : ci N t + 1 < ci N h :=
      lt_ci_iff.2 (NNReal.coe_lt_coe.1 (by push_cast; linarith))
    have hkn : ci N t + 1 < ci N L := hka.trans_le (ci_mono N hx.lt.le)
    have hτ : ((ci N t + 1 : ℕ) : ℝ≥0) * gδ N < h := lt_ci_iff.1 hka
    simp only [dRead, blockRev]
    rw [if_pos hkn, if_neg (by omega), cycRevPath, glue_of_lt hth]
    show x (((ci N t + 1 : ℕ) : ℝ≥0) * gδ N) = some j ↔ some v = some j
    rw [hx.hold _ hτ]
  · rcases lt_or_ge t L with htL | hLt
    · -- inside the excursion: the left limit at `L + h − t`
      have hthL : t - h ≤ L := tsub_le_self.trans htL.le
      have hTreal : ((L - (t - h) : ℝ≥0) : ℝ) = L - t + h := by
        rw [NNReal.coe_sub hthL, NNReal.coe_sub hht]
        ring
      have hT : 0 < L - (t - h) := tsub_pos_of_lt (lt_of_le_of_lt tsub_le_self htL)
      obtain ⟨b, hbT, hor⟩ := hx.regLL.leftLimits j (L - (t - h)) hT
      filter_upwards [eventually_add_mul_gδ_lt_real hbT 3, eventually_add_mul_gδ_lt_real htL 2]
        with N hNb hNL
      simp only [Nat.cast_ofNat] at hNb hNL
      rw [hTreal] at hNb
      obtain ⟨hc1, hc2⟩ := ci_real N t
      obtain ⟨hn1, hn2⟩ := ci_real N L
      obtain ⟨ha1, ha2⟩ := ci_real N h
      have hg : (0 : ℝ) < gδ N := by exact_mod_cast gδ_pos N
      have hsplit : ((ci N t : ℝ) + 1) * (gδ N : ℝ) = (ci N t : ℝ) * gδ N + gδ N := by ring
      have hkn : ci N t + 1 < ci N L :=
        lt_ci_iff.2 (NNReal.coe_lt_coe.1 (by push_cast; linarith))
      have hak : ci N h ≤ ci N t := ci_mono N hht
      have ha1' : 1 ≤ ci N h := one_le_ci hx.pos
      obtain ⟨j', hj'⟩ : ∃ j', j' = ci N L + ci N h - 1 - (ci N t + 1) := ⟨_, rfl⟩
      have hj : j' + ci N t + 2 = ci N L + ci N h := by omega
      have hjr : (j' : ℝ) + ci N t + 2 = ci N L + ci N h := by exact_mod_cast hj
      have hjg : (j' : ℝ) * gδ N = (ci N L : ℝ) * gδ N + (ci N h : ℝ) * gδ N -
          (ci N t : ℝ) * gδ N - 2 * gδ N := by
        rw [show (j' : ℝ) = ci N L + ci N h - ci N t - 2 by linarith]
        ring
      have hτ1 : b < (j' : ℝ≥0) * gδ N :=
        NNReal.coe_lt_coe.1 (by push_cast; linarith)
      have hτ2 : (j' : ℝ≥0) * gδ N < L - (t - h) :=
        NNReal.coe_lt_coe.1 (by rw [hTreal]; push_cast; linarith)
      simp only [dRead, blockRev]
      rw [if_pos hkn, if_pos (show ci N h ≤ ci N t + 1 ∧ ci N t + 1 < ci N L from
        ⟨by omega, hkn⟩), ← hj', hx.cycRevPath_of_mid hht htL]
      show x ((j' : ℝ≥0) * gδ N) = some j ↔ leftLim x (L - (t - h)) = some j
      rcases hor with hin | hout
      · rw [hin _ ⟨hτ1, hτ2⟩, leftLim_eq_some_iff.2 ⟨b, hbT, hin⟩]
      · exact ⟨fun h' => absurd h' (hout _ ⟨hτ1, hτ2⟩),
          fun h' => absurd h' (leftLim_ne_some_of hbT hout)⟩
    · -- after the return: both sides are `∞`
      filter_upwards with N
      have hk : ¬ ci N t + 1 < ci N L := by
        have := ci_mono N hLt
        omega
      simp only [dRead]
      rw [if_neg hk, cycRevPath, glue_of_le (hx.lt.le.trans hLt),
        glue_of_le (tsub_le_tsub_right hLt h)]
      rfl

/-! ### 5. The finite-dimensional π-system of the cycle space -/

/-- Finitely many prescribed labels and a length bound. -/
def cylS (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) : Set (Cyc v) :=
  {c | (∀ p ∈ F, c.1.1 p.1 = some p.2) ∧ c.1.2 < s}

/-- The finite-dimensional π-system. -/
def cylSys (v : ℕ) : Set (Set (Cyc v)) := {S | ∃ F s, S = cylS F s}

theorem isPiSystem_cylSys : IsPiSystem (cylSys v) := by
  rintro _ ⟨F₁, s₁, rfl⟩ _ ⟨F₂, s₂, rfl⟩ -
  refine ⟨F₁ ∪ F₂, min s₁ s₂, ?_⟩
  ext c
  simp only [cylS, mem_inter_iff, mem_setOf_eq, Finset.mem_union, lt_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun p hp => hp.elim (h1 p) (h3 p), h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨⟨fun p hp => h1 p (Or.inl hp), h2⟩, fun p hp => h1 p (Or.inr hp), h4⟩

theorem measurableSet_cylS (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) :
    MeasurableSet (cylS (v := v) F s) := by
  have hx : Measurable fun c : Cyc v => c.1.1 := measurable_fst.comp measurable_subtype_coe
  have hL : Measurable fun c : Cyc v => c.1.2 := measurable_snd.comp measurable_subtype_coe
  have h1 : MeasurableSet {c : Cyc v | ∀ p ∈ F, c.1.1 p.1 = some p.2} := by
    have : {c : Cyc v | ∀ p ∈ F, c.1.1 p.1 = some p.2} =
        ⋂ p ∈ F, {c : Cyc v | c.1.1 p.1 = some p.2} := by
      ext c
      simp
    rw [this]
    refine Finset.measurableSet_biInter F fun p _ => ?_
    have hm := ((measurable_pi_apply p.1).comp hx) (measurableSet_singleton (some p.2))
    exact hm
  have h2 : MeasurableSet {c : Cyc v | c.1.2 < s} := measurableSet_lt hL measurable_const
  exact h1.inter h2

theorem measurableSet_gen_eval (t : ℝ≥0) (S : Set (Option ℕ)) :
    MeasurableSet[MeasurableSpace.generateFrom (cylSys v)] {c : Cyc v | c.1.1 t ∈ S} := by
  have hsome : ∀ j : ℕ, MeasurableSet[MeasurableSpace.generateFrom (cylSys v)]
      {c : Cyc v | c.1.1 t = some j} := by
    intro j
    have : {c : Cyc v | c.1.1 t = some j} = ⋃ m : ℕ, cylS {(t, j)} (m : ℝ≥0) := by
      ext c
      simp only [mem_setOf_eq, mem_iUnion, cylS, Finset.mem_singleton, forall_eq]
      constructor
      · intro h'
        obtain ⟨m, hm⟩ := exists_nat_gt c.1.2
        exact ⟨m, h', hm⟩
      · rintro ⟨m, h', -⟩
        exact h'
    rw [this]
    exact MeasurableSet.iUnion fun m => MeasurableSpace.measurableSet_generateFrom ⟨_, _, rfl⟩
  have hnone : MeasurableSet[MeasurableSpace.generateFrom (cylSys v)]
      {c : Cyc v | c.1.1 t = none} := by
    have : {c : Cyc v | c.1.1 t = none} = (⋃ j : ℕ, {c : Cyc v | c.1.1 t = some j})ᶜ := by
      ext c
      simp only [mem_setOf_eq, mem_compl_iff, mem_iUnion, not_exists]
      cases c.1.1 t <;> simp
    rw [this]
    exact (MeasurableSet.iUnion hsome).compl
  have : {c : Cyc v | c.1.1 t ∈ S} = ⋃ o ∈ S, {c : Cyc v | c.1.1 t = o} := by
    ext c
    simp
  rw [this]
  refine MeasurableSet.biUnion (Set.to_countable S) fun o _ => ?_
  cases o with
  | none => exact hnone
  | some j => exact hsome j

/-- **The finite-dimensional sets generate the σ-algebra of the cycle space.** -/
theorem generateFrom_cylSys (v : ℕ) :
    MeasurableSpace.generateFrom (cylSys v) = (inferInstance : MeasurableSpace (Cyc v)) := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨F, s, rfl⟩
    exact measurableSet_cylS F s
  · have hx : Measurable[MeasurableSpace.generateFrom (cylSys v)] fun c : Cyc v => c.1.1 := by
      rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup, iSup_le_iff]
      intro t
      rw [MeasurableSpace.comap_comp]
      intro s hs
      obtain ⟨S, -, rfl⟩ := hs
      exact measurableSet_gen_eval t S
    have hL : Measurable[MeasurableSpace.generateFrom (cylSys v)] fun c : Cyc v => c.1.2 :=
      measurable_of_Iio fun s =>
        MeasurableSpace.measurableSet_generateFrom ⟨∅, s, by ext c; simp [cylS]⟩
    exact measurable_iff_comap_le.1 (hx.prodMk hL)

/-! ### 6. Convergence of the discrete events at a good path -/

theorem GoodCyc.eventually_mem_fwd (hx : GoodCyc v x h L) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) :
    ∀ᶠ N in atTop, (x ∈ fwdSetT v N F s ↔ hx.cyc ∈ cylS F s) := by
  have hF : ∀ᶠ N in atTop, ∀ p ∈ F,
      (dRead N (ci N L) (gridSeq N x) p.1 = some p.2 ↔ glue x L cem p.1 = some p.2) :=
    (eventually_all_finset F).2 fun p _ => hx.eventually_dRead p.1 p.2
  filter_upwards [hx.eventually_dcyc, hF, hx.eventually_len s] with N hd hFN hlen
  have hobs : Obs N (ci N L) F s (wext (gridWord N (ci N L) x)) ↔ hx.cyc ∈ cylS F s := by
    rw [obs_congr (y' := gridSeq N x) fun k hk => wext_gridWord hk.le x]
    show _ ↔ (∀ p ∈ F, glue x L cem p.1 = some p.2) ∧ L < s
    rw [Obs, ← hlen]
    exact and_congr_left' (forall₂_congr fun p hp => hFN p hp)
  constructor
  · intro hmem
    obtain ⟨⟨a, n⟩, hw⟩ := mem_iUnion.1 hmem
    obtain ⟨hd', hob⟩ := hw
    obtain ⟨rfl, rfl⟩ := (dcyc_gridSeq_of_wext hd').unique hd
    exact hobs.1 hob
  · intro hc
    exact mem_iUnion.2 ⟨(ci N h, ci N L),
      ⟨hd.congr fun k hk => (wext_gridWord hk x).symm, hobs.2 hc⟩⟩

theorem GoodCyc.eventually_mem_rev (hx : GoodCyc v x h L) (F : Finset (ℝ≥0 × ℕ)) (s : ℝ≥0) :
    ∀ᶠ N in atTop, (x ∈ revSetT v N F s ↔ cycRev hx.cyc ∈ cylS F s) := by
  have hF : ∀ᶠ N in atTop, ∀ p ∈ F,
      (dRead N (ci N L) (blockRev (ci N h) (ci N L) (gridSeq N x)) p.1 = some p.2 ↔
        cycRevPath (glue x L cem) v h L p.1 = some p.2) :=
    (eventually_all_finset F).2 fun p _ => hx.eventually_dRead_rev p.1 p.2
  filter_upwards [hx.eventually_dcyc, hF, hx.eventually_len s] with N hd hFN hlen
  have hobs : Obs N (ci N L) F s (wext (wordRev (ci N h) (gridWord N (ci N L) x))) ↔
      cycRev hx.cyc ∈ cylS F s := by
    rw [wext_wordRev, obs_congr (y' := blockRev (ci N h) (ci N L) (gridSeq N x)) fun k hk => by
      simp only [blockRev]
      split_ifs with hb
      · exact wext_gridWord (by omega) x
      · exact wext_gridWord hk.le x]
    show _ ↔ (∀ p ∈ F, cycRevPath (glue x L cem) v (holdTime hx.cyc) L p.1 = some p.2) ∧ L < s
    rw [hx.holdTime_cyc, Obs, ← hlen]
    exact and_congr_left' (forall₂_congr fun p hp => hFN p hp)
  constructor
  · intro hmem
    obtain ⟨⟨a, n⟩, hw⟩ := mem_iUnion.1 hmem
    obtain ⟨hd', hob⟩ := hw
    obtain ⟨rfl, rfl⟩ := (dcyc_gridSeq_of_wext hd').unique hd
    exact hobs.1 hob
  · intro hc
    exact mem_iUnion.2 ⟨(ci N h, ci N L),
      ⟨hd.congr fun k hk => (wext_gridWord hk x).symm, hobs.2 hc⟩⟩

/-! ### 7. The main theorem -/

/-- **Complete-cycle reversal from grid block reversal.**  If `μ`-almost every path `X a` is a
regular complete cycle from `v` whose cycle is `fc a`, and the grid words of `X` satisfy the
discrete block reversal on every grid `1/(N+1)`, then the cycle law `μ.map fc` is invariant
under `cycRev`. -/
theorem completeCycleReversal_of_grid {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {X : α → Trajectory ℕ} (hX : Measurable X)
    {fc : α → Cyc v} (hfc : Measurable fc)
    (hgood : ∀ᵐ a ∂μ, ∃ (h L : ℝ≥0) (hx : GoodCyc v (X a) h L), fc a = hx.cyc)
    (hgrid : ∀ (N a n : ℕ) (w : Fin (n + 1) → Option ℕ), DCyc v a n (wext w) →
      μ ((gridWord N n ∘ X) ⁻¹' {w}) = μ ((gridWord N n ∘ X) ⁻¹' {wordRev a w})) :
    CompleteCycleReversal (μ.map fc) := by
  unfold CompleteCycleReversal
  refine ext_of_generate_finite (cylSys v) (generateFrom_cylSys v).symm isPiSystem_cylSys ?_ ?_
  · rintro _ ⟨F, s, rfl⟩
    have hS := measurableSet_cylS (v := v) F s
    rw [Measure.map_apply measurable_cycRev hS, Measure.map_apply hfc (measurable_cycRev hS),
      Measure.map_apply hfc hS]
    have h1 : Tendsto (fun N => μ (X ⁻¹' fwdSetT v N F s)) atTop (𝓝 (μ (fc ⁻¹' cylS F s))) := by
      refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop (hfc hS)
        (fun N => hX (measurableSet_fwdSetT v N F s)) ?_
      filter_upwards [hgood] with a ha
      obtain ⟨h, L, hx, hfa⟩ := ha
      filter_upwards [hx.eventually_mem_fwd F s] with N hN
      rw [mem_preimage, mem_preimage, hfa]
      exact hN
    have h2 : Tendsto (fun N => μ (X ⁻¹' revSetT v N F s)) atTop
        (𝓝 (μ (fc ⁻¹' (cycRev ⁻¹' cylS F s)))) := by
      refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (hfc (measurable_cycRev hS)) (fun N => hX (measurableSet_revSetT v N F s)) ?_
      filter_upwards [hgood] with a ha
      obtain ⟨h, L, hx, hfa⟩ := ha
      filter_upwards [hx.eventually_mem_rev F s] with N hN
      rw [mem_preimage, mem_preimage, mem_preimage, hfa]
      exact hN
    have heq : (fun N => μ (X ⁻¹' revSetT v N F s)) = fun N => μ (X ⁻¹' fwdSetT v N F s) :=
      funext fun N => measure_revSetT_eq μ hX hgrid N F s
    rw [heq] at h2
    exact tendsto_nhds_unique h2 h1
  · rw [Measure.map_apply measurable_cycRev MeasurableSet.univ, preimage_univ]

end ReflectedGMS.CycleReversalGrid
