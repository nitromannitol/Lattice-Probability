/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Coupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.ApproximatingChain

/-!
# The coupling of the approximating chains (Gwynne–Sung, Section 3.2, Lemma 3.4)

Section 3.2 of arXiv:2506.18827 fixes a starting vertex `z`, sets `n_z := min{n : z ∈ VG_n}`
(3.11), and couples the chains `{Yⁿ}_{n ≥ n_z}` of Section 3.1, all started at `z`, so that

  `Yⁿ_{J^{m,n}_k} = Y^m_k`  for all `n ≥ m ≥ n_z` and `k`   (3.12)

(**Lemma 3.4**).  The coupled family is then used to define the discrete-time random walk
reflected off of `∞`, `Y : Ξ → VG`, by `Y_ξ := Yⁿ_j` for `(n, j) ∈ ξ` (3.13).

## Construction

Following the design recorded in the module docstring of `IndexSet.lean`, the coupling is a
*second* Ionescu–Tulcea construction (`Kernel.trajMeasure`) whose `ℕ`-index is the exhaustion
**level** and whose state at stage `i` is the whole level-`i` path `ℕ → V`:

* levels are re-indexed from a base level `n₀` (the paper's `n_z`): `Gs i := VG_{n₀+i}` and
  `ν i := law of Y^{n₀+i} started at z` (`LevelCoupling` is generic in `Gs`, `ν`);
* the stage kernel `stageKernel Gs ν i : Kernel (ℕ → V) (ℕ → V)` is
  `condDistrib id (coarsenPath (Gs i)) (ν (i+1))`, the regular conditional law of the finer
  path `Y^{i+1}` given its coarsening `k ↦ Y^{i+1}_{J^{i,i+1}_k}` — this is exactly the
  paper's "conditional on `{Yⁿ}_{n ≤ N-1}`, sample `Y^N` from its conditional law given
  `{Y^N_{J^{N-1,N}_k}}_k`" (proof of Lemma 3.4);
* Lemma 3.3 (`Exhaustion.chainLaw_map_coarsenPath`), `(ν (i+1)).map (coarsenPath (Gs i)) = ν i`,
  is the compatibility that makes the marginal of the coupling at level `i` equal to `ν i`
  (`coupling_map_apply`) and the joint law of two consecutive levels equal to the law of
  `(coarsenPath Y^{i+1}, Y^{i+1})` (`coupling_map_pair_eq`), whence (3.12) holds almost surely
  (`coupling_ae_coarsenPath`, `coupling_ae_consistent`).

The resulting probability measure `Exhaustion.coupling hG n₀ z` on `ℕ → (ℕ → V)`
(level ↦ path) is the paper's `P_z` (with the paper's level `n` at index `n - n₀`).

## The discrete-time walk (3.13) and the a.s. transfers

`IndexSet.lean` encodes the paper's `Ξ` inside the fixed countable linear order
`Ξ₀ = Lex (ℕ →₀ ℕ)` and defines `Y_ξ` as the deterministic function `Yxi Gs Y` of the sample;
here `LevelCoupling.walk Gs ω : Ξ₀ → V` is that function, it is measurable
(`measurable_walk`), and `Exhaustion.walkLaw hG n₀ z` is its law under `P_z`.  Since
`IndexSet.Consistent Gs ω` holds `P_z`-a.s., every theorem of `IndexSet.lean` with a
`Consistent` hypothesis becomes an a.s. statement about the coupled process; the transfers
provided are (3.12) at all levels (`coupling_ae_Y_J`), (3.13) (`coupling_ae_Yxi_addr`,
`coupling_ae_Yxi_eq`), (3.14) (`coupling_ae_exists_addr_eq_of_mem`), the successor lemmas
for (3.24) (`coupling_ae_J_succ_of_mem`, `coupling_ae_tm_succAt`,
`coupling_ae_not_lt_lt_succAt`) and the cofinality statement `coupling_ae_exists_gt_Yxi_eq`.
Any further transfer is `(E.coupling_ae_consistent hG n₀ z).mono`.

## The Markov clause of Lemma 3.4

The construction is a level-indexed Markov chain: the regular conditional law of the
level-`(i+1)` path given the levels `≤ i` is the stage kernel read off the level-`i` path
(`condDistrib_coupling`, from mathlib's `Kernel.condDistrib_trajMeasure`).  The paper's
finer clause — that the *prefixes* `{Yⁿ_j}_{j ≤ J^{m,n}_k}`, `n ≥ m+1`, are conditionally
independent of `Y^m` given `{Y^m_j}_{j ≤ k}` — additionally needs the excursion decomposition
of `Y^{m+1}` along the stopping times `J^{m,m+1}_k` (a joint strong Markov property); it is
not derived here.

## Conventions

`V` is countable with measurable singletons, never locally finite as a graph; `B₁Gₙ` may be
infinite.  Nothing is assumed about `z` beyond `z : V`; the paper's `z ∈ VG_{n_z}` enters only
through `coupling_ae_mem_ball1`, and `Exhaustion.nz` is (3.11).
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal

namespace ReflectedWalk

namespace LevelCoupling

variable {V : Type*}

/-! ### The discrete-time walk `Y : Ξ → VG` of (3.13) as a measurable function of the sample -/

section Walk

variable (Gs : ℕ → Set V)

/-- **The discrete-time random walk reflected off of `∞`** (3.13), as a function of the
sample: `Y_ξ := Yⁿ_j` for `(n, j) ∈ ξ`, evaluated on the ambient index set `Ξ₀`.  The paper's
process is its restriction to the realised subset `IndexSet.Xi Gs ω`; under the coupling it is
well defined a.s. (`coupling_ae_Yxi_addr`). -/
noncomputable def walk (ω : ℕ → ℕ → V) : IndexSet.Xi₀ → V :=
  fun a => IndexSet.Yxi Gs ω (ofLex a)

/-- (3.13) unfolded: `walk Gs ω a = Yxi Gs ω a`. -/
lemma walk_apply (ω : ℕ → ℕ → V) (a : IndexSet.Xi₀) :
    walk Gs ω a = IndexSet.Yxi Gs ω (ofLex a) := rfl

variable [MeasurableSpace V]

/-- The level-`n` time `tm Gs ω n a` of an address is a measurable function of the sample. -/
lemma measurable_tm (hGs : ∀ i, MeasurableSet (Gs i)) (n : ℕ) (a : ℕ →₀ ℕ) :
    Measurable fun ω : ℕ → ℕ → V => IndexSet.tm Gs ω n a := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have h1 : Measurable fun q : (ℕ → ℕ → V) × ℕ =>
        IndexSet.coarsen (Gs n) (q.1 (n + 1)) q.2 :=
      measurable_from_prod_countable_left fun k =>
        (IndexSet.measurable_coarsen (hGs n) k).comp (measurable_pi_apply (n + 1))
    have h2 : Measurable fun ω : ℕ → ℕ → V => (ω, IndexSet.tm Gs ω n a) :=
      measurable_id.prodMk ih
    show Measurable fun ω : ℕ → ℕ → V =>
      IndexSet.coarsen (Gs n) (ω (n + 1)) (IndexSet.tm Gs ω n a) + a (n + 1)
    exact (measurable_from_nat (f := fun k : ℕ => k + a (n + 1))).comp (h1.comp h2)

/-- `Y_ξ` of (3.13) is a measurable function of the sample, for every address `ξ`. -/
lemma measurable_Yxi (hGs : ∀ i, MeasurableSet (Gs i)) (a : ℕ →₀ ℕ) :
    Measurable fun ω : ℕ → ℕ → V => IndexSet.Yxi Gs ω a := by
  have h1 : Measurable fun q : (ℕ → ℕ → V) × ℕ => q.1 (IndexSet.level a) q.2 :=
    measurable_from_prod_countable_left fun j =>
      (measurable_pi_apply j).comp (measurable_pi_apply (IndexSet.level a))
  exact h1.comp (measurable_id.prodMk (measurable_tm Gs hGs (IndexSet.level a) a))

/-- `ω ↦ (Y_ξ)_{ξ ∈ Ξ₀}` is measurable for the product σ-algebra on `Ξ₀ → V`. -/
lemma measurable_walk (hGs : ∀ i, MeasurableSet (Gs i)) : Measurable (walk Gs) :=
  measurable_pi_iff.mpr fun a => measurable_Yxi Gs hGs (ofLex a)

end Walk

/-! ### The level-indexed Ionescu–Tulcea construction, generic in the family of laws -/

section Construction

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nonempty V]
  (Gs : ℕ → Set V) (ν : ℕ → Measure (ℕ → V)) [∀ i, IsProbabilityMeasure (ν i)]

/-- The stage kernel of the coupling (proof of Lemma 3.4): the regular conditional law of the
level-`(i+1)` path given its coarsening `k ↦ Y^{i+1}_{J^{i,i+1}_k}` along `Gs i`, i.e. the paper's
"conditional law of `Y^N` given `{Y^N_{J^{N-1,N}_k}}_{k ≥ 0}`". -/
noncomputable def stageKernel (i : ℕ) : Kernel (ℕ → V) (ℕ → V) :=
  condDistrib id (IndexSet.coarsenPath (Gs i)) (ν (i + 1))

/-- The stage kernel is a Markov kernel (a regular conditional law). -/
instance stageKernel_isMarkovKernel (i : ℕ) : IsMarkovKernel (stageKernel Gs ν i) := by
  unfold stageKernel
  infer_instance

/-- The stage kernel read off the last coordinate of a finite history of levels `0, …, i`:
the Ionescu–Tulcea input of the coupling. -/
noncomputable def levelKernel (i : ℕ) : Kernel (Finset.Iic i → (ℕ → V)) (ℕ → V) :=
  (stageKernel Gs ν i).comap (MarkovChain.lastCoord i) (MarkovChain.measurable_lastCoord i)

/-- The history-indexed stage kernel is a Markov kernel, as Ionescu–Tulcea requires. -/
instance levelKernel_isMarkovKernel (i : ℕ) : IsMarkovKernel (levelKernel Gs ν i) := by
  unfold levelKernel
  infer_instance

/-- The history-indexed stage kernel only reads the last level of the history. -/
lemma levelKernel_apply (i : ℕ) (h : Finset.Iic i → (ℕ → V)) :
    levelKernel Gs ν i h = stageKernel Gs ν i (MarkovChain.lastCoord i h) := rfl

/-- **The coupling of Lemma 3.4**, generic form: the Ionescu–Tulcea measure on
`ℕ → (ℕ → V)` (level ↦ path) started from the level-`0` law `ν 0` and iterating the stage
kernels.  With `Gs i = VG_{n_z+i}` and `ν i` the law of `Y^{n_z+i}` from `z`, this is the
paper's `P_z`. -/
noncomputable def coupling : Measure (ℕ → ℕ → V) :=
  Kernel.trajMeasure (X := fun _ => ℕ → V) (ν 0) (levelKernel Gs ν)

/-- The coupling is a probability measure (Lemma 3.4: "there is a coupling"). -/
instance coupling_isProbabilityMeasure : IsProbabilityMeasure (coupling Gs ν) := by
  unfold coupling
  infer_instance

/-- The level-`0` marginal of the coupling is `ν 0`. -/
lemma coupling_map_zero : (coupling Gs ν).map (fun ω => ω 0) = ν 0 := by
  have heq : (fun ω : ℕ → ℕ → V => ω 0) = MarkovChain.lastCoord 0 ∘ frestrictLe 0 := rfl
  rw [heq, ← Measure.map_map (MarkovChain.measurable_lastCoord 0) (measurable_frestrictLe 0),
    coupling, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_map (MarkovChain.measurable_lastCoord 0) (MeasurableEquiv.measurable _)]
  exact Measure.map_id

/-- The Markov property of the level-indexed chain at level `i`, joint form: the law of
(levels `≤ i`, level `i+1`) is the prefix law composed with the level kernel. -/
lemma coupling_history_next (i : ℕ) :
    (coupling Gs ν).map (frestrictLe i) ⊗ₘ levelKernel Gs ν i =
      (coupling Gs ν).map (fun ω => (frestrictLe i ω, ω (i + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- The joint law of two consecutive levels is the level-`i` marginal composed with the stage
kernel. -/
lemma coupling_map_pair (i : ℕ) :
    (coupling Gs ν).map (fun ω => (ω i, ω (i + 1))) =
      (coupling Gs ν).map (fun ω => ω i) ⊗ₘ stageKernel Gs ν i := by
  have h2 : (fun ω : ℕ → ℕ → V => (ω i, ω (i + 1))) =
      Prod.map (MarkovChain.lastCoord i) id ∘ (fun ω => (frestrictLe i ω, ω (i + 1))) := rfl
  have hmeas : Measurable (fun ω : ℕ → ℕ → V => (frestrictLe i ω, ω (i + 1))) :=
    (measurable_frestrictLe i).prodMk (measurable_pi_apply (i + 1))
  have hfl : ((coupling Gs ν).map (frestrictLe i)).map (MarkovChain.lastCoord i) =
      (coupling Gs ν).map (fun ω => ω i) :=
    Measure.map_map (MarkovChain.measurable_lastCoord i) (measurable_frestrictLe i)
  rw [h2, ← Measure.map_map ((MarkovChain.measurable_lastCoord i).prodMap measurable_id) hmeas,
    ← coupling_history_next Gs ν i,
    MarkovChain.compProd_map_prod_of_kernel_map ((coupling Gs ν).map (frestrictLe i))
      (levelKernel Gs ν i) (stageKernel Gs ν i) (MarkovChain.lastCoord i) id
      (MarkovChain.measurable_lastCoord i) measurable_id (fun _ => Measure.map_id), hfl]

/-- Lemma 3.3 makes the stage kernel push `ν i` to `ν (i+1)`: since `ν i` is the law of the
coarsening of `Y^{i+1}`, composing with the conditional law of `Y^{i+1}` given its coarsening
recovers the law of `Y^{i+1}`. -/
lemma stageKernel_comp (hGs : ∀ i, MeasurableSet (Gs i))
    (hν : ∀ i, (ν (i + 1)).map (IndexSet.coarsenPath (Gs i)) = ν i) (i : ℕ) :
    stageKernel Gs ν i ∘ₘ ν i = ν (i + 1) := by
  rw [stageKernel, ← hν i, condDistrib_comp_map
    (IndexSet.measurable_coarsenPath (hGs i)).aemeasurable aemeasurable_id, Measure.map_id]

/-- **Marginals of the coupling** (Lemma 3.4, "a coupling of `{Yⁿ}`"): the level-`i` marginal
of the coupling is `ν i`. -/
theorem coupling_map_apply (hGs : ∀ i, MeasurableSet (Gs i))
    (hν : ∀ i, (ν (i + 1)).map (IndexSet.coarsenPath (Gs i)) = ν i) (i : ℕ) :
    (coupling Gs ν).map (fun ω => ω i) = ν i := by
  induction i with
  | zero => exact coupling_map_zero Gs ν
  | succ i ih =>
    have h := congrArg Measure.snd (coupling_map_pair Gs ν i)
    rw [Measure.snd_compProd, ih, stageKernel_comp Gs ν hGs hν i] at h
    rw [← h, Measure.snd]
    exact (Measure.map_map measurable_snd
      ((measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1)))).symm

/-- The joint law of two consecutive levels is the law of `(coarsenPath (Gs i) Y^{i+1}, Y^{i+1})`
under `ν (i+1)`: the paper's "we first set `Y^N_{J^{N-1,N}_k} = Y^{N-1}_k`". -/
theorem coupling_map_pair_eq (hGs : ∀ i, MeasurableSet (Gs i))
    (hν : ∀ i, (ν (i + 1)).map (IndexSet.coarsenPath (Gs i)) = ν i) (i : ℕ) :
    (coupling Gs ν).map (fun ω => (ω i, ω (i + 1))) =
      (ν (i + 1)).map (fun p => (IndexSet.coarsenPath (Gs i) p, p)) := by
  rw [coupling_map_pair, coupling_map_apply Gs ν hGs hν i, stageKernel, ← hν i]
  exact compProd_map_condDistrib (IndexSet.measurable_coarsenPath (hGs i)).aemeasurable
    aemeasurable_id

/-- **(3.12) for consecutive levels, almost surely**: `coarsenPath (Gs i) (ω (i+1)) = ω i`. -/
theorem coupling_ae_coarsenPath (hGs : ∀ i, MeasurableSet (Gs i))
    (hν : ∀ i, (ν (i + 1)).map (IndexSet.coarsenPath (Gs i)) = ν i) (i : ℕ) :
    ∀ᵐ ω ∂coupling Gs ν, IndexSet.coarsenPath (Gs i) (ω (i + 1)) = ω i := by
  have hpair : Measurable (fun ω : ℕ → ℕ → V => (ω i, ω (i + 1))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1))
  have hs : MeasurableSet {x : (ℕ → V) × (ℕ → V) | IndexSet.coarsenPath (Gs i) x.2 = x.1} :=
    measurableSet_eq_fun ((IndexSet.measurable_coarsenPath (hGs i)).comp measurable_snd)
      measurable_fst
  have hg : Measurable (fun p : ℕ → V => (IndexSet.coarsenPath (Gs i) p, p)) :=
    (IndexSet.measurable_coarsenPath (hGs i)).prodMk measurable_id
  have h : ∀ᵐ x ∂(coupling Gs ν).map (fun ω => (ω i, ω (i + 1))),
      IndexSet.coarsenPath (Gs i) x.2 = x.1 := by
    rw [coupling_map_pair_eq Gs ν hGs hν i]
    exact (ae_map_iff hg.aemeasurable hs).mpr (Eventually.of_forall fun _ => rfl)
  exact ae_of_ae_map hpair.aemeasurable h

/-- **Lemma 3.4, (3.12)**: under the coupling, the sample is almost surely consistent in the
sense of `IndexSet.Consistent`, i.e. `Y^{i+1}_{J^{i,i+1}_k} = Y^i_k` for all `i, k`. -/
theorem coupling_ae_consistent (hGs : ∀ i, MeasurableSet (Gs i))
    (hν : ∀ i, (ν (i + 1)).map (IndexSet.coarsenPath (Gs i)) = ν i) :
    ∀ᵐ ω ∂coupling Gs ν, IndexSet.Consistent Gs ω := by
  have h : ∀ᵐ ω ∂coupling Gs ν, ∀ i, IndexSet.coarsenPath (Gs i) (ω (i + 1)) = ω i :=
    ae_all_iff.mpr fun i => coupling_ae_coarsenPath Gs ν hGs hν i
  filter_upwards [h] with ω hω
  exact (IndexSet.consistent_iff Gs ω).mpr hω

/-- An almost-sure property of the level-`i` chain is an almost-sure property of the
level-`i` coordinate of the coupling. -/
theorem coupling_ae_of_ae (hGs : ∀ i, MeasurableSet (Gs i))
    (hν : ∀ i, (ν (i + 1)).map (IndexSet.coarsenPath (Gs i)) = ν i) (i : ℕ)
    {q : (ℕ → V) → Prop} (h : ∀ᵐ p ∂ν i, q p) : ∀ᵐ ω ∂coupling Gs ν, q (ω i) := by
  rw [← coupling_map_apply Gs ν hGs hν i] at h
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

/-- **The Markov property of the level-indexed chain** (the Markov clause of Lemma 3.4 in the
form the construction provides): a regular conditional law of the level-`(i+1)` path given the
levels `≤ i` is the stage kernel evaluated at the level-`i` path. -/
theorem condDistrib_coupling (i : ℕ) :
    condDistrib (fun ω => ω (i + 1)) (frestrictLe i) (coupling Gs ν)
      =ᵐ[(coupling Gs ν).map (frestrictLe i)] levelKernel Gs ν i :=
  Kernel.condDistrib_trajMeasure

/-- The level-indexed Markov property in kernel form (from mathlib's
`Kernel.traj_comp_partialTraj`): the coupling is the law of the levels `≤ i` composed with the
Ionescu–Tulcea continuation kernel from level `i`, whose stage kernels read only the last
level. -/
theorem coupling_eq_traj_comp_prefix (i : ℕ) :
    coupling Gs ν =
      Kernel.traj (X := fun _ => ℕ → V) (levelKernel Gs ν) i ∘ₘ
        (coupling Gs ν).map (frestrictLe i) := by
  simp only [coupling, Kernel.trajMeasure]
  rw [Measure.map_comp _ _ (measurable_frestrictLe i), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Kernel.traj_comp_partialTraj (Nat.zero_le i)]

end Construction

end LevelCoupling

/-! ### The coupling `P_z` of Lemma 3.4 for the chains `Yⁿ` of an exhaustion -/

namespace ConductanceGraph.Exhaustion

variable {V : Type*} {G : ConductanceGraph V} (E : G.Exhaustion)

/-- The vertex sets `VG_{n₀+i}` of the exhaustion re-indexed from the base level `n₀` (the
paper's `n_z`), as the `Gs` of `IndexSet.lean`. -/
def levelSets (n₀ : ℕ) : ℕ → Set V := fun i => ↑(E.Gsub (n₀ + i))

/-- `Gs i = VG_{n₀+i}`, unfolded. -/
lemma levelSets_apply (n₀ i : ℕ) : E.levelSets n₀ i = ↑(E.Gsub (n₀ + i)) := rfl

/-- The re-indexed exhaustion is increasing. -/
lemma levelSets_mono (n₀ : ℕ) : Monotone (E.levelSets n₀) := fun _ _ hij =>
  Finset.coe_subset.mpr (E.mono (Nat.add_le_add_left hij n₀))

/-- Each `VG_{n₀+i}` is measurable (every subset of a countable discrete space is). -/
lemma measurableSet_levelSets [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (n₀ i : ℕ) : MeasurableSet (E.levelSets n₀ i) :=
  MeasurableSet.of_discrete

/-- The re-indexed exhaustion still covers `V`. -/
lemma exists_mem_levelSets (n₀ : ℕ) (x : V) : ∃ i, x ∈ E.levelSets n₀ i := by
  obtain ⟨n, hn⟩ := E.exists_mem x
  exact ⟨n, Finset.mem_coe.mpr (E.mono (Nat.le_add_left n n₀) hn)⟩

open Classical in
/-- `n_z := min{n : z ∈ VG_n}` of (3.11). -/
noncomputable def nz (z : V) : ℕ := Nat.find (E.exists_mem z)

open Classical in
/-- `z ∈ VG_{n_z}` (3.11). -/
lemma mem_Gsub_nz (z : V) : z ∈ E.Gsub (E.nz z) := Nat.find_spec (E.exists_mem z)

open Classical in
/-- `n_z` is the least level containing `z` (3.11). -/
lemma nz_le {z : V} {n : ℕ} (h : z ∈ E.Gsub n) : E.nz z ≤ n := Nat.find_min' (E.exists_mem z) h

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
  (hG : G.toSimpleGraph.Connected)

/-- The laws of the chains `Y^{n₀+i}` started at `z` (Section 3.1), indexed by the level offset. -/
noncomputable def levelLaw (n₀ : ℕ) (z : V) : ℕ → Measure (ℕ → V) :=
  fun i => E.chainLaw hG (n₀ + i) z

/-- Each `P_z`-law of `Y^{n₀+i}` is a probability measure. -/
instance levelLaw_isProbabilityMeasure (n₀ : ℕ) (z : V) (i : ℕ) :
    IsProbabilityMeasure (E.levelLaw hG n₀ z i) := by
  unfold levelLaw
  infer_instance

/-- Lemma 3.3 in the re-indexed form consumed by the coupling. -/
lemma levelLaw_map_coarsenPath (n₀ : ℕ) (z : V) (i : ℕ) :
    (E.levelLaw hG n₀ z (i + 1)).map (IndexSet.coarsenPath (E.levelSets n₀ i)) =
      E.levelLaw hG n₀ z i :=
  E.chainLaw_map_coarsenPath hG (n₀ + i) z

/-- **The coupling `P_z` of Lemma 3.4**: the joint law of `{Y^{n₀+i}}_{i ≥ 0}`, all started at
`z`, as a probability measure on `ℕ → (ℕ → V)` (level offset ↦ path).  Its level-`i` marginal is
the law of `Y^{n₀+i}` (`coupling_map_apply`) and (3.12) holds a.s. (`coupling_ae_consistent`).
The paper takes `n₀ = n_z` (`Exhaustion.nz`). -/
noncomputable def coupling (n₀ : ℕ) (z : V) : Measure (ℕ → ℕ → V) :=
  LevelCoupling.coupling (E.levelSets n₀) (E.levelLaw hG n₀ z)

/-- `P_z` is a probability measure. -/
instance coupling_isProbabilityMeasure (n₀ : ℕ) (z : V) :
    IsProbabilityMeasure (E.coupling hG n₀ z) := by
  unfold coupling
  infer_instance

/-- Under `P_z`, the level-`i` path has the law of `Y^{n₀+i}` started at `z`
(Lemma 3.4: "a coupling of `{Yⁿ}_{n ≥ n_z}`, each started from `Yⁿ_0 = z`"). -/
theorem coupling_map_apply (n₀ : ℕ) (z : V) (i : ℕ) :
    (E.coupling hG n₀ z).map (fun ω => ω i) = E.chainLaw hG (n₀ + i) z :=
  LevelCoupling.coupling_map_apply _ _ (E.measurableSet_levelSets n₀)
    (E.levelLaw_map_coarsenPath hG n₀ z) i

/-- **Lemma 3.4, (3.12)**: `P_z`-a.s. the sample is consistent, `Y^{n+1}_{J^{n,n+1}_k} = Yⁿ_k`
for all levels `n` and times `k`. -/
theorem coupling_ae_consistent (n₀ : ℕ) (z : V) :
    ∀ᵐ ω ∂E.coupling hG n₀ z, IndexSet.Consistent (E.levelSets n₀) ω :=
  LevelCoupling.coupling_ae_consistent _ _ (E.measurableSet_levelSets n₀)
    (E.levelLaw_map_coarsenPath hG n₀ z)

/-- The joint law of two consecutive levels under `P_z` is the law of
`(coarsenPath VG_{n₀+i} Y^{n₀+i+1}, Y^{n₀+i+1})`. -/
theorem coupling_map_pair_eq (n₀ : ℕ) (z : V) (i : ℕ) :
    (E.coupling hG n₀ z).map (fun ω => (ω i, ω (i + 1))) =
      (E.chainLaw hG (n₀ + i + 1) z).map
        (fun p => (IndexSet.coarsenPath (E.levelSets n₀ i) p, p)) :=
  LevelCoupling.coupling_map_pair_eq _ _ (E.measurableSet_levelSets n₀)
    (E.levelLaw_map_coarsenPath hG n₀ z) i

/-- Transfer of almost-sure properties of `Y^{n₀+i}` to the coupling. -/
theorem coupling_ae_of_ae (n₀ : ℕ) (z : V) (i : ℕ) {q : (ℕ → V) → Prop}
    (h : ∀ᵐ p ∂E.chainLaw hG (n₀ + i) z, q p) : ∀ᵐ ω ∂E.coupling hG n₀ z, q (ω i) :=
  LevelCoupling.coupling_ae_of_ae _ _ (E.measurableSet_levelSets n₀)
    (E.levelLaw_map_coarsenPath hG n₀ z) i h

/-- Every level starts at `z` (Lemma 3.4: "each started from `Yⁿ_0 = z`"). -/
theorem coupling_ae_start (n₀ : ℕ) (z : V) :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ i, ω i 0 = z :=
  ae_all_iff.mpr fun i => E.coupling_ae_of_ae hG n₀ z i (E.chainLaw_ae_start hG (n₀ + i) z)

/-- If `z ∈ VG_{n₀}` (e.g. `n₀ = n_z`), every level-`i` path stays in `B₁G_{n₀+i}`. -/
theorem coupling_ae_mem_ball1 (n₀ : ℕ) {z : V} (hz : z ∈ E.Gsub n₀) :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ i j, ω i j ∈ E.ball1 (n₀ + i) :=
  ae_all_iff.mpr fun i => E.coupling_ae_of_ae hG n₀ z i
    (E.chainLaw_ae_mem_ball1 hG (n₀ + i)
      (G.subset_ball1 _ (Finset.mem_coe.mpr (E.mono (Nat.le_add_right n₀ i) hz))))

/-- The Markov property of the level-indexed chain under `P_z`: a regular conditional law of
`Y^{n₀+i+1}` given `Y^{n₀}, …, Y^{n₀+i}` is the conditional law of `Y^{n₀+i+1}` given its
coarsening, evaluated at `Y^{n₀+i}`. -/
theorem condDistrib_coupling (n₀ : ℕ) (z : V) (i : ℕ) :
    condDistrib (fun ω => ω (i + 1)) (frestrictLe i) (E.coupling hG n₀ z)
      =ᵐ[(E.coupling hG n₀ z).map (frestrictLe i)]
        LevelCoupling.levelKernel (E.levelSets n₀) (E.levelLaw hG n₀ z) i :=
  LevelCoupling.condDistrib_coupling _ _ i

/-! #### The discrete-time random walk reflected off of `∞` under `P_z` -/

/-- **The law of the discrete-time random walk reflected off of `∞`** (3.13): the pushforward
of `P_z` under `ω ↦ (Y_ξ)_{ξ ∈ Ξ₀}`, a probability measure on `Ξ₀ → V`. -/
noncomputable def walkLaw (n₀ : ℕ) (z : V) : Measure (IndexSet.Xi₀ → V) :=
  (E.coupling hG n₀ z).map (LevelCoupling.walk (E.levelSets n₀))

/-- The law of the walk is a probability measure. -/
instance walkLaw_isProbabilityMeasure (n₀ : ℕ) (z : V) :
    IsProbabilityMeasure (E.walkLaw hG n₀ z) := by
  unfold walkLaw
  infer_instance

/-- The law of the walk evaluated on a measurable set of trajectories `Ξ₀ → V`. -/
lemma walkLaw_apply (n₀ : ℕ) (z : V) {s : Set (IndexSet.Xi₀ → V)} (hs : MeasurableSet s) :
    E.walkLaw hG n₀ z s = E.coupling hG n₀ z (LevelCoupling.walk (E.levelSets n₀) ⁻¹' s) :=
  Measure.map_apply (LevelCoupling.measurable_walk _ (E.measurableSet_levelSets n₀)) hs

/-- Almost-sure properties of the walk transfer from the coupling. -/
lemma walkLaw_ae_of_ae (n₀ : ℕ) (z : V) {q : (IndexSet.Xi₀ → V) → Prop}
    (hq : MeasurableSet {y | q y})
    (h : ∀ᵐ ω ∂E.coupling hG n₀ z, q (LevelCoupling.walk (E.levelSets n₀) ω)) :
    ∀ᵐ y ∂E.walkLaw hG n₀ z, q y :=
  (ae_map_iff (LevelCoupling.measurable_walk _ (E.measurableSet_levelSets n₀)).aemeasurable
    hq).mpr h

/-! #### The paper's `P_z`: base level `n_z` -/

/-- **The paper's `P_z`** (p. 20): the coupling of `{Yⁿ}_{n ≥ n_z}` started at `z`, i.e. the
coupling with base level `n_z` of (3.11).  Every `coupling_*` statement applies to it verbatim
with `n₀ := E.nz z`. -/
noncomputable abbrev Pz (z : V) : Measure (ℕ → ℕ → V) := E.coupling hG (E.nz z) z

/-- Under `P_z`, every level-`i` path stays in `B₁G_{n_z+i}`. -/
theorem Pz_ae_mem_ball1 (z : V) : ∀ᵐ ω ∂E.Pz hG z, ∀ i j, ω i j ∈ E.ball1 (E.nz z + i) :=
  E.coupling_ae_mem_ball1 hG (E.nz z) (E.mem_Gsub_nz z)

/-! #### Almost-sure forms of the deterministic theorems of `IndexSet.lean` -/

section Transfer

variable (n₀ : ℕ) (z : V)

/-- (3.12) at all pairs of levels, a.s.: `Y^{m+d}_{J^{m,m+d}_k} = Y^m_k`. -/
theorem coupling_ae_Y_J :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ m d k,
      ω (m + d) (IndexSet.J (E.levelSets n₀) ω m d k) = ω m k :=
  (E.coupling_ae_consistent hG n₀ z).mono fun _ hω m d k => hω.Y_J _ _ m d k

/-- (3.13) a.s.: `Y_{[(n,j)]} = Yⁿ_j`. -/
theorem coupling_ae_Yxi_addr :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ n j,
      IndexSet.Yxi (E.levelSets n₀) ω (IndexSet.addr (E.levelSets n₀) ω n j) = ω n j :=
  (E.coupling_ae_consistent hG n₀ z).mono fun _ hω n j => hω.Yxi_addr _ _ n j

/-- (3.13) a.s., in terms of `walk`: the walk at the address of `(n, j)` is `Yⁿ_j`. -/
theorem coupling_ae_walk_addr :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ n j,
      LevelCoupling.walk (E.levelSets n₀) ω (toLex (IndexSet.addr (E.levelSets n₀) ω n j)) =
        ω n j :=
  E.coupling_ae_Yxi_addr hG n₀ z

/-- (3.13) is well defined a.s.: `Y_ξ` may be read at any level `n ≥ level ξ`. -/
theorem coupling_ae_Yxi_eq :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ (a : ℕ →₀ ℕ) (n : ℕ), IndexSet.level a ≤ n →
      IndexSet.Yxi (E.levelSets n₀) ω a = ω n (IndexSet.tm (E.levelSets n₀) ω n a) :=
  (E.coupling_ae_consistent hG n₀ z).mono fun _ hω _ _ hn => hω.Yxi_eq _ _ hn

/-- (3.14) a.s.: if `Y_ξ ∈ VG_{n₀+n}` then `ξ` has a representative `(n, j)` at level `n`. -/
theorem coupling_ae_exists_addr_eq_of_mem :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ a : ℕ →₀ ℕ, IndexSet.Realized (E.levelSets n₀) ω a →
      ∀ n, IndexSet.Yxi (E.levelSets n₀) ω a ∈ E.levelSets n₀ n →
        ∃ j, IndexSet.addr (E.levelSets n₀) ω n j = a :=
  (E.coupling_ae_consistent hG n₀ z).mono fun _ hω _ ha _ hn =>
    hω.exists_addr_eq_of_mem _ _ (E.levelSets_mono n₀) ha hn

/-- The successor at a level where the walk is inside `VG_{n₀+n}` stays the successor at all
finer levels (p. 23), a.s. -/
theorem coupling_ae_J_succ_of_mem :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ n k, ω n k ∈ E.levelSets n₀ n → ∀ d,
      IndexSet.J (E.levelSets n₀) ω n d (k + 1) = IndexSet.J (E.levelSets n₀) ω n d k + 1 :=
  (E.coupling_ae_consistent hG n₀ z).mono fun _ hω _ _ hk d =>
    hω.J_succ_of_mem _ _ (E.levelSets_mono n₀) hk d

/-- (3.24) a.s.: the level-`(n+d)` time of `ξ̂ = succAt n ξ` is one more than that of `ξ`,
when `Y_ξ ∈ VG_{n₀+n}` and `ξ` has a representative at level `n`. -/
theorem coupling_ae_tm_succAt :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ (n : ℕ) (a : ℕ →₀ ℕ),
      (∃ j, IndexSet.addr (E.levelSets n₀) ω n j = a) →
      IndexSet.Yxi (E.levelSets n₀) ω a ∈ E.levelSets n₀ n → ∀ d,
        IndexSet.tm (E.levelSets n₀) ω (n + d) (IndexSet.succAt (E.levelSets n₀) ω n a) =
          IndexSet.tm (E.levelSets n₀) ω (n + d) a + 1 :=
  (E.coupling_ae_consistent hG n₀ z).mono fun _ hω _ _ ha hmem d =>
    hω.tm_succAt _ _ (E.levelSets_mono n₀) ha hmem d

/-- Nothing in `Ξ` lies strictly between `ξ` and its successor `ξ̂` (p. 23), a.s. -/
theorem coupling_ae_not_lt_lt_succAt :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ (n : ℕ) (a : ℕ →₀ ℕ),
      (∃ j, IndexSet.addr (E.levelSets n₀) ω n j = a) →
      IndexSet.Yxi (E.levelSets n₀) ω a ∈ E.levelSets n₀ n →
      ∀ b : ℕ →₀ ℕ, IndexSet.Realized (E.levelSets n₀) ω b →
        ¬ (toLex a < toLex b ∧ toLex b < toLex (IndexSet.succAt (E.levelSets n₀) ω n a)) :=
  (E.coupling_ae_consistent hG n₀ z).mono fun _ hω _ _ ha hmem _ hb =>
    hω.not_lt_lt_succAt _ _ (E.levelSets_mono n₀) ha hmem hb

/-- Property (v) at the discrete level (p. 25), a.s.: if the level-`0` chain a.s. visits `z` at
arbitrarily large times, then a.s. `Ξ` contains arbitrarily large `ξ` with `Y_ξ = z`. -/
theorem coupling_ae_exists_gt_Yxi_eq
    (hrec : ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ k, ∃ k', k < k' ∧ ω 0 k' = z) :
    ∀ᵐ ω ∂E.coupling hG n₀ z, ∀ ξ : IndexSet.Xi (E.levelSets n₀) ω,
      ∃ η : IndexSet.Xi (E.levelSets n₀) ω,
        ξ < η ∧ IndexSet.Yxi (E.levelSets n₀) ω (ofLex η.1) = z := by
  filter_upwards [E.coupling_ae_consistent hG n₀ z, hrec] with ω hω hr
  exact fun ξ => hω.exists_gt_Yxi_eq _ _ hr ξ

end Transfer

/-- The level-`n₀` chain is recovered from the walk along the level-`0` addresses
`[(n₀, k)] = single 0 k`: pushing the law of the walk forward by `y ↦ (k ↦ y [(n₀, k)])` gives
the law of `Y^{n₀}` started at `z`. -/
theorem walkLaw_map_levelZero (n₀ : ℕ) (z : V) :
    (E.walkLaw hG n₀ z).map (fun y k => y (toLex (Finsupp.single 0 k))) =
      E.chainLaw hG n₀ z := by
  have hmeas : Measurable fun y : IndexSet.Xi₀ → V => fun k => y (toLex (Finsupp.single 0 k)) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  rw [walkLaw, Measure.map_map hmeas
    (LevelCoupling.measurable_walk _ (E.measurableSet_levelSets n₀))]
  have hae : (fun y : IndexSet.Xi₀ → V => fun k => y (toLex (Finsupp.single 0 k))) ∘
      LevelCoupling.walk (E.levelSets n₀) =ᵐ[E.coupling hG n₀ z] fun ω => ω 0 := by
    filter_upwards [E.coupling_ae_Yxi_addr hG n₀ z] with ω hω
    funext k
    exact hω 0 k
  rw [Measure.map_congr hae]
  exact E.coupling_map_apply hG n₀ z 0

end ConductanceGraph.Exhaustion

end ReflectedWalk
