import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Chain

/-!
# The simple random walk of a cell configuration as a nearest-neighbour Markov chain

For a cell configuration `H` in the sense of Gwynne-Miller-Sheffield (the invariance principle for
random planar maps embedded by cells, Definition 1.15) with countably many cells, the law
`IsSRWLaw K₀ Q` of the simple random walk on the cells (transitions `c(K,K')/π(K)`) is only given
by its finite-dimensional distributions.  Here it is realised as the trajectory law of an explicit
Markov kernel, so that the general Markov chain theory applies to it.

* `kernel`: one step from `K` goes to `K'` with probability `c(K,K')/π(K)`; a cell without
  neighbours (`π(K) = 0`) is absorbing.  It is a Markov kernel (`π(K) = ∑ c(K,·)`).
* `summable_c`: the conductances out of a cell are summable, since by local finiteness only
  finitely many cells meet a compact cell.
* `isSRWLaw_chainLaw`: the chain started at a cell with `π(K₀) > 0` has the law `IsSRWLaw K₀`.
* `pi_pos_of_isSRWLaw`, `eq_chainLaw_of_isSRWLaw`: every law `Q` with `IsSRWLaw K₀ Q` starts at a
  non-isolated cell and equals the chain law.
* `isNNChain_kernel`: the chain is a nearest-neighbour chain on the adjacency graph of the cells.
* `abs_hit_sub_le_of_isSRWLaw`: the hitting-distribution separation estimate (the walk version of
  Lemma 3.12 of the invariance principle): for two starts `x, y`, the hitting laws of a set `I`
  differ in total variation by at most the probability that the walk from `x` does not separate
  `y` from `I` by its trace before hitting `I`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig)

/-! ### Conductance totals -/

section Totals

variable (hH : H.IsCellConfiguration)
include hH

/-- Only finitely many cells have positive conductance to a given cell: they meet it, and by local
finiteness only finitely many cells meet a compact set. -/
theorem finite_c_ne_zero (K : H.cells) : {K' : H.cells | H.c K K' ≠ 0}.Finite := by
  choose U hU hfin using hH.locallyFinite
  obtain ⟨t, -, hcov⟩ :=
    (K.1 : Cell).isCompact.elim_nhds_subcover U
      (fun z _ => hU z)
  refine ((t.finite_toSet.biUnion fun z _ => hfin z).preimage
    Subtype.val_injective.injOn).subset ?_
  intro K' hK'
  have hpos : 0 < H.c K K' := lt_of_le_of_ne (hH.c_nonneg _ _) (Ne.symm hK')
  obtain ⟨p, hpK, hpK'⟩ := hH.adj_inter K K' hpos
  obtain ⟨z, hz, hpU⟩ := mem_iUnion₂.1 (hcov hpK)
  exact mem_iUnion₂.2 ⟨z, hz, K'.2, p, hpK', hpU⟩

theorem summable_c (K : H.cells) : Summable fun K' : H.cells => H.c K K' :=
  summable_of_hasFiniteSupport (finite_c_ne_zero H hH K)

theorem pi_nonneg (K : H.cells) : 0 ≤ H.pi K :=
  tsum_nonneg fun _ => hH.c_nonneg _ _

theorem c_le_pi (K K' : H.cells) : H.c K K' ≤ H.pi K :=
  (summable_c H hH K).le_tsum K' fun _ _ => hH.c_nonneg _ _

theorem transition_nonneg (K K' : H.cells) : 0 ≤ H.transition K K' :=
  div_nonneg (hH.c_nonneg _ _) (pi_nonneg H hH K)

/-- A positive transition probability `K → K'` makes `K'` non-isolated. -/
theorem pi_pos_of_transition_pos {K K' : H.cells} (h : 0 < H.transition K K') :
    0 < H.pi K' := by
  have hc : 0 < H.c K K' := by
    rcases div_pos_iff.1 h with h' | h'
    · exact h'.1
    · exact absurd h'.2 (not_lt.2 (pi_nonneg H hH K))
  rw [hH.c_symm] at hc
  exact hc.trans_le (c_le_pi H hH K' K)

end Totals

/-! ### The kernel -/

section Kernel

variable [Countable H.cells]

/-- One step of the simple random walk on the cells from `K`: the cell `K'` with probability
`c(K,K')/π(K)`; a cell with `π(K) = 0` is absorbing. -/
def stepMeasure (K : H.cells) : Measure H.cells :=
  if 0 < H.pi K then
    Measure.sum fun K' : H.cells => ENNReal.ofReal (H.transition K K') • Measure.dirac K'
  else Measure.dirac K

/-- The transition kernel of the simple random walk on the cells. -/
def kernel : Kernel H.cells H.cells where
  toFun := stepMeasure H
  measurable' := measurable_of_countable _

theorem kernel_apply (K : H.cells) : kernel H K = stepMeasure H K := rfl

theorem kernel_singleton {K : H.cells} (h : 0 < H.pi K) (K' : H.cells) :
    kernel H K {K'} = ENNReal.ofReal (H.transition K K') := by
  rw [kernel_apply, stepMeasure, ite_eq_left h, Measure.sum_apply _ (measurableSet_singleton _),
    tsum_eq_single K' fun b hb => by
      simp [Measure.dirac_apply' _ (measurableSet_singleton _), hb]]
  simp [Measure.dirac_apply' _ (measurableSet_singleton _)]

variable (hH : H.IsCellConfiguration)
include hH

theorem isMarkovKernel_kernel : IsMarkovKernel (kernel H) := by
  refine ⟨fun K => ⟨?_⟩⟩
  rw [kernel_apply, stepMeasure]
  split_ifs with h
  · rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (transition_nonneg H hH K)
      ((summable_c H hH K).div_const _)]
    simp only [CellConfig.transition]
    rw [tsum_div_const]
    change ENNReal.ofReal (H.pi K / H.pi K) = 1
    rw [div_self h.ne', ENNReal.ofReal_one]
  · exact measure_univ

/-- The trajectory law of the simple random walk on the cells started at `K₀`. -/
def walkLaw (K₀ : H.cells) : Measure (ℕ → H.cells) :=
  @chainLaw _ _ (kernel H) (isMarkovKernel_kernel H hH) K₀

/-! ### Identification with `IsSRWLaw` -/

/-- The products of one-step probabilities of the kernel and of `IsSRWLaw` agree along every path
started at a non-isolated cell. -/
theorem prod_kernel_eq (s : ℕ → H.cells) (h0 : 0 < H.pi (s 0)) (n : ℕ) :
    ∏ i ∈ Finset.range n, kernel H (s i) {s (i + 1)} =
      ∏ i ∈ Finset.range n, ENNReal.ofReal (H.transition (s i) (s (i + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    by_cases hz : ∏ i ∈ Finset.range n, ENNReal.ofReal (H.transition (s i) (s (i + 1))) = 0
    · rw [hz, zero_mul, zero_mul]
    · have hpi : 0 < H.pi (s n) := by
        rcases n with _ | m
        · exact h0
        · rw [Finset.prod_range_succ] at hz
          have hm : ENNReal.ofReal (H.transition (s m) (s (m + 1))) ≠ 0 := right_ne_zero_of_mul hz
          exact pi_pos_of_transition_pos H hH (ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hm))
      rw [kernel_singleton H hpi]

theorem isSRWLaw_walkLaw {K₀ : H.cells} (h0 : 0 < H.pi K₀) :
    H.IsSRWLaw K₀ (walkLaw H hH K₀) := by
  have := isMarkovKernel_kernel H hH
  refine ⟨by unfold walkLaw; infer_instance, fun n x => ?_⟩
  set s : ℕ → H.cells := fun i => if h : i < n + 1 then x ⟨i, h⟩ else x 0 with hs_def
  have hsx : ∀ i : Fin (n + 1), s i = x i := fun i => by
    simp only [s]
    rw [dite_eq_left i.2]
  have hset : {ω : ℕ → H.cells | ∀ i : Fin (n + 1), ω i = x i} =
      {ω | ∀ i ≤ n, ω i = s i} := by
    ext ω
    constructor
    · intro h i hi
      have := h ⟨i, Nat.lt_succ_of_le hi⟩
      rw [this, ← hsx]
    · intro h i
      rw [h i (Nat.le_of_lt_succ i.2), hsx]
  rw [hset, walkLaw, chainLaw_cylinder]
  have hs0 : s 0 = x 0 := hsx 0
  by_cases hx : x 0 = K₀
  · rw [ite_eq_left (hs0.trans hx), ite_eq_left hx, one_mul, one_mul,
      prod_kernel_eq H hH s (by rw [hs0, hx]; exact h0) n]
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : s i = x i.castSucc := hsx i.castSucc
    have h2 : s (i + 1) = x i.succ := hsx i.succ
    rw [h1, h2]
  · rw [ite_eq_right (by rw [hs0]; exact hx), ite_eq_right hx, zero_mul, zero_mul]

/-- A law with `IsSRWLaw K₀` forces `π(K₀) > 0`: from an isolated cell no first step has positive
probability, while the start has probability one. -/
theorem pi_pos_of_isSRWLaw {K₀ : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q) :
    0 < H.pi K₀ := by
  by_contra hneg
  have hpi0 : H.pi K₀ = 0 := le_antisymm (not_lt.1 hneg) (pi_nonneg H hH K₀)
  have hstep : ∀ K' : H.cells, Q {ω | ∀ i : Fin 2, ω i = ![K₀, K'] i} = 0 := by
    intro K'
    rw [hQ.2 1 ![K₀, K']]
    simp [CellConfig.transition, hpi0]
  have hstart : Q {ω | ∀ i : Fin 1, ω i = (fun _ => K₀) i} = 1 := by
    rw [hQ.2 0 (fun _ => K₀)]
    simp
  have hsub : {ω : ℕ → H.cells | ∀ i : Fin 1, ω i = (fun _ => K₀) i} ⊆
      ⋃ K' : H.cells, {ω | ∀ i : Fin 2, ω i = ![K₀, K'] i} := by
    intro ω hω
    refine mem_iUnion.2 ⟨ω 1, ?_⟩
    intro i
    fin_cases i
    · simpa using hω 0
    · simp
  have := measure_mono_null hsub (measure_iUnion_null hstep)
  rw [hstart] at this
  exact one_ne_zero this

/-- **The law of the simple random walk on the cells is the chain law of `kernel`.** -/
theorem eq_walkLaw_of_isSRWLaw {K₀ : H.cells} {Q : Measure (ℕ → H.cells)}
    (hQ : H.IsSRWLaw K₀ Q) : Q = walkLaw H hH K₀ :=
  CellConfig.IsSRWLaw.unique (H := H) hQ (isSRWLaw_walkLaw H hH (pi_pos_of_isSRWLaw H hH hQ))

/-! ### Nearest-neighbour structure and the separation estimate -/

theorem isNNChain_kernel : IsNNChain (kernel H) id id H.graph where
  π_start _ := rfl
  kernel_eq _ := rfl
  step_null K := by
    have hmeas : MeasurableSet {t : H.cells | id t = id K ∨ H.graph.Adj (id K) (id t)}ᶜ :=
      MeasurableSet.of_discrete
    rw [kernel_apply, stepMeasure]
    split_ifs with h
    · rw [Measure.sum_apply _ hmeas]
      refine ENNReal.tsum_eq_zero.2 fun K' => ?_
      rw [Measure.smul_apply, Measure.dirac_apply' _ hmeas, smul_eq_mul]
      by_cases hm : K' ∈ {t : H.cells | id t = id K ∨ H.graph.Adj (id K) (id t)}ᶜ
      · have ht : H.transition K K' ≤ 0 := by
          by_contra hpos
          have hc : 0 < H.c K K' := by
            rcases div_pos_iff.1 (not_le.1 hpos) with h' | h'
            · exact h'.1
            · exact absurd h'.2 (not_lt.2 (pi_nonneg H hH K))
          have hc' : 0 < H.c K' K := by rwa [hH.c_symm]
          refine hm (Or.inr ⟨fun hKK => ?_, hc, hc'⟩)
          exact hH.adj_ne _ _ hc (congrArg Subtype.val hKK)
        rw [ENNReal.ofReal_of_nonpos ht, zero_mul]
      · rw [indicator_of_notMem hm, mul_zero]
    · rw [Measure.dirac_apply' _ hmeas, indicator_of_notMem (by simp)]

/-- **Hitting-distribution separation for the simple random walk on the cells** (the walk version
of Lemma 3.12 of the invariance principle).  For walk laws `Qx, Qy` from `x, y` that hit `I` almost
surely, the probabilities of first hitting `I` inside `W` differ by at most the probability that
the trace of the walk from `x` before hitting `I` fails to separate `y` from `I`. -/
theorem abs_hit_sub_le_of_isSRWLaw (I W : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1) :
    |(Qx (hitEvent I W)).toReal - (Qy (hitEvent I W)).toReal| ≤
      1 - (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) {y} I}).toReal := by
  have := isMarkovKernel_kernel H hH
  rw [eq_walkLaw_of_isSRWLaw H hH hQx] at hx ⊢
  rw [eq_walkLaw_of_isSRWLaw H hH hQy] at hy ⊢
  exact abs_hitLaw_sub_le (isNNChain_kernel H hH) I W hx hy

end Kernel

end LatticeProb.CellConfigSRW

end
