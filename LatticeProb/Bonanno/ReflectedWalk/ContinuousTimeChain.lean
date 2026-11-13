/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.ContinuousTimeChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Existence
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The continuous-time approximating chain `Xⁿ` of (3.15) and its law
(Gwynne–Sung, arXiv:2506.18827, Section 3.3 and Step 1 of the uniqueness proof in Section 3.4)

`PathProperties.lean` already builds the process `Xⁿ` of (3.15) out of one sample
`(Y, E)` of the coupling of Lemma 3.4 and of the unit holding times: `PathProperties.Xn`
is `Xⁿ_t = Yⁿ_k` for the unique `k` with
`t ∈ [∑_{i<k} T_{[(n,i)]}, ∑_{i≤k} T_{[(n,i)]})`.  This file **identifies the law of
`Xⁿ`**, in the form used in Step 1 of Section 3.4 (p. 26): the embedded sequence
`(Yⁿ_j)_{j ≥ 0}` is the discrete chain of (3.2)–(3.3) started at `z`, and conditionally on
it the holding times `(Tⁿ_j)_{j ≥ 0}` are independent with `Tⁿ_j ~ Exponential(w(Yⁿ_j))`.

## The law delivered

Everything happens on `Existence.Sample V = (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)` with the paper's
`P_z = Exhaustion.jointLaw hG n₀ z = (coupling of Lemma 3.4) ⊗ (i.i.d. Exponential(1))`.
For the level offset `i` (absolute level `n = n₀ + i`) the pair

  `embeddedPair E w n₀ i ω = ((Yⁿ_j)_j, (Tⁿ_j)_j)`,  `Tⁿ_j = E_{[(n,j)]} / w(Yⁿ_j)`

is a random element of `(ℕ → V) × (ℕ → ℝ)`, and `map_embeddedPair` says

  `(E.jointLaw hG n₀ z).map (embeddedPair E w n₀ i) = E.chainLaw hG (n₀+i) z ⊗ₘ holdingKernel w`

where `holdingKernel w y = Measure.infinitePi fun j => Exponential(w (y j))`
(`holdingKernel_apply`).  **The first marginal is exactly `E.chainLaw hG (n₀+i) z`**
(`fst_map_embeddedPair`), the law of `Yⁿ` from `ApproximatingChain.lean`: this is the
meeting point with the general-process side of the uniqueness argument.

## What else is here

* **The time change** (section `TimeChange`): `Xⁿ_t = Yⁿ_k` for the unique `k` with
  `t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)` (`Xn_eq_of_mem_Ico`, `mem_Ico_unique`), the existence
  of such a `k` when `∑_j Tⁿ_j = ∞` (`exists_inLevelInterval`, `Xn_ne_none`), and the
  relation to `IndexSet`'s clock (3.25) and the intervals `[τ_η, τ_η̂)` of (3.26): the `j`-th
  holding interval of `Xⁿ` is the interval of `η = [(n,j)]` translated by the remainder `Rⁿ`
  of (3.29) (`inLevelInterval_iff_inInterval`).
* **`Xⁿ` as a functional of `(Yⁿ, Tⁿ)`** (section `JumpPath`): the time change `jumpPath` is a
  fixed measurable map, with `Xⁿ = jumpPath (Yⁿ, Tⁿ)` (`Xn_eq_jumpPath`), so the law of the
  *whole path* of `Xⁿ` is the pushforward of `E.chainLaw hG n z ⊗ₘ holdingKernel w`
  (`map_trajectoryN`).  Any process whose embedded chain and holding times have that joint
  law therefore has the same law as `Xⁿ` — the conclusion of Step 1 of Section 3.4 (p. 26)
  for the process `X̃ⁿ` extracted from an arbitrary process satisfying (i)–(vi).
* **The transition function** (section `Family`): `Xⁿ` as a `ProcessFamily` (`chainFamily`)
  with `P_z(Xⁿ_t = y)` computed from the same joint law (`chainFamily_transition`,
  `measure_processN_eq`) — the input to `Theorem16.identDistrib_of_transition`.  The
  left-hand side of `chainFamily_transition` is `ProcessFamily.transition` unfolded, so this
  file does not have to import `ReflectedWalk.TransitionUniqueness`.

## Hypotheses carried, and who discharges them

* `∀ x, 0 < w x` — the rate function of Theorem 1.6.
* `Monotone Gs`, `∀ x, ∃ n, x ∈ Gs n`, `Consistent` — the exhaustion and the coupling of
  Lemma 3.4 (`Coupling.lean`), a.s. under `jointLaw` (`jointLaw_ae_consistent`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

universe u

namespace ReflectedWalk

/-! ### Reindexing and rescaling an i.i.d. family -/

/-- **Reindexing an i.i.d. family along an injection.**  If `σ : ℕ → ι` is injective, the
coordinates `(x_{σ j})_{j ∈ ℕ}` of an i.i.d. `ι`-indexed family are again i.i.d. with the same
one-dimensional law.  Used with `σ = addr Gs Y n`, the (path-dependent, injective) enumeration
of the level-`n` classes `[(n, j)] ∈ Ξ`, to see the level-`n` unit holding times as an i.i.d.
sequence indexed by the jump number. -/
lemma infinitePi_map_comp_injective {ι : Type*} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {σ : ℕ → ι} (hσ : Function.Injective σ) :
    (Measure.infinitePi fun _ : ι => μ).map (fun x : ι → α => fun j : ℕ => x (σ j)) =
      Measure.infinitePi fun _ : ℕ => μ := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  obtain ⟨t', ht'σ, hmt'⟩ :
      ∃ t' : ι → Set α, (∀ j, t' (σ j) = t j) ∧ ∀ i, MeasurableSet (t' i) := by
    refine ⟨fun i => if h : ∃ j, σ j = i then t h.choose else Set.univ, fun j => ?_, fun i => ?_⟩
    · have h : ∃ j', σ j' = σ j := ⟨j, rfl⟩
      dsimp only
      rw [dite_eq_left h]
      exact congrArg t (hσ h.choose_spec)
    · dsimp only
      split_ifs with h
      · exact ht _
      · exact MeasurableSet.univ
  have hmσ : Measurable (fun x : ι → α => fun j : ℕ => x (σ j)) :=
    Measurable.of_eval fun j => measurable_pi_apply (σ j)
  have hpre : (fun x : ι → α => fun j : ℕ => x (σ j)) ⁻¹' (Set.pi ↑s t)
      = Set.pi ↑(s.image σ) t' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro hx i ⟨j, hj, rfl⟩
      rw [ht'σ]
      exact hx j hj
    · intro hx j hj
      rw [← ht'σ j]
      exact hx (σ j) ⟨j, hj, rfl⟩
  rw [Measure.map_apply hmσ (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre,
    Measure.infinitePi_pi _ fun i _ => hmt' i,
    Finset.prod_image fun a _ b _ h => hσ h]
  exact Finset.prod_congr rfl fun j _ => by rw [ht'σ]

/-! ### The i.i.d. `Exponential(1)` sequence indexed by the jump number -/

/-- The law of the level-`n` **unit** holding times, read along the jumps: an i.i.d.
`Exponential(1)` sequence indexed by `j ∈ ℕ` (Section 3.3). -/
noncomputable def expSeq : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => ProbabilityTheory.expMeasure 1

instance expSeq_isProbabilityMeasure : IsProbabilityMeasure expSeq := by
  unfold expSeq; infer_instance

/-- **Rescaling.**  Dividing the `j`-th coordinate of the i.i.d. `Exponential(1)` sequence by
`v j > 0` gives independent `Exponential(v j)` coordinates: the holding times
`T_j = E_j / w(Y_j)` of Section 3.3. -/
lemma expSeq_map_div (v : ℕ → ℝ) (hv : ∀ j, 0 < v j) :
    expSeq.map (fun e : ℕ → ℝ => fun j => e j / v j) =
      Measure.infinitePi fun j => ProbabilityTheory.expMeasure (v j) := by
  calc expSeq.map (fun e : ℕ → ℝ => fun j => e j / v j)
      = (Measure.infinitePi fun _ : ℕ => ProbabilityTheory.expMeasure 1).map
          (fun x : ℕ → ℝ => fun i : ℕ => (fun (j : ℕ) (y : ℝ) => y / v j) i (x i)) := rfl
    _ = Measure.infinitePi fun j =>
          (ProbabilityTheory.expMeasure 1).map (fun y : ℝ => y / v j) :=
        Measure.infinitePi_map_pi _ fun j => measurable_id.div_const (v j)
    _ = Measure.infinitePi fun j => ProbabilityTheory.expMeasure (v j) :=
        congrArg Measure.infinitePi (funext fun j => Existence.expMeasure_one_map_div (hv j))

/-- The unit holding times of the classes `[(n, j)]`, `j ∈ ℕ`, are an i.i.d. `Exponential(1)`
sequence: `j ↦ [(n,j)]` is injective (`IndexSet.addr_injective`), so this is
`infinitePi_map_comp_injective` for the i.i.d. family `expFamily` of `RateFunction.lean`. -/
lemma expFamily_map_comp_addr {V : Type u} (Gs : ℕ → Set V) (y : ℕ → ℕ → V) (n : ℕ) :
    expFamily.map (fun e : (ℕ →₀ ℕ) → ℝ => fun j => e (IndexSet.addr Gs y n j)) = expSeq := by
  rw [expFamily, expSeq]
  exact infinitePi_map_comp_injective _ (IndexSet.addr_injective Gs y n)

/-! ### The conditional law of the holding times given the embedded chain -/

section Kernel

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- `(y, e) ↦ (e_j / w(y_j))_j` is measurable. -/
lemma measurable_divSeq (w : V → ℝ) :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => fun j => p.2 j / w (p.1 j) :=
  Measurable.of_eval fun j =>
    ((measurable_pi_apply j).comp measurable_snd).div
      ((measurable_of_countable w).comp ((measurable_pi_apply j).comp measurable_fst))

/-- **The conditional law of the holding times of (3.15) given the embedded chain**:
conditionally on `(Yⁿ_j)_j = y`, the holding times `(Tⁿ_j)_j` are independent with
`Tⁿ_j ~ Exponential(w(y_j))` (`holdingKernel_apply`).  Built as a pushforward of the i.i.d.
`Exponential(1)` sequence so that measurability in `y` is automatic. -/
noncomputable def holdingKernel (w : V → ℝ) : Kernel (ℕ → V) (ℕ → ℝ) :=
  Kernel.map ((Kernel.id : Kernel (ℕ → V) (ℕ → V)) ×ₖ Kernel.const (ℕ → V) expSeq)
    (fun p : (ℕ → V) × (ℕ → ℝ) => fun j => p.2 j / w (p.1 j))

instance holdingKernel_isMarkovKernel (w : V → ℝ) : IsMarkovKernel (holdingKernel w) :=
  Kernel.IsMarkovKernel.map _ (measurable_divSeq w)

/-- **Section 3.3, the holding times**: given the embedded chain `y`, the holding times are
independent with `T_j ~ Exponential(w (y j))`. -/
lemma holdingKernel_apply {w : V → ℝ} (hw : ∀ x, 0 < w x) (y : ℕ → V) :
    holdingKernel w y = Measure.infinitePi fun j => ProbabilityTheory.expMeasure (w (y j)) := by
  rw [holdingKernel, Kernel.map_apply _ (measurable_divSeq w), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_divSeq w) measurable_prodMk_left]
  exact expSeq_map_div (fun j => w (y j)) fun j => hw _

/-- The `Exponential(1)` family, reindexed along the classes `[(n,j)]` and rescaled by
`w(Yⁿ_j)`, has the law `holdingKernel w (Yⁿ)`. -/
lemma expFamily_map_holding {w : V → ℝ} (hw : ∀ x, 0 < w x) (Gs : ℕ → Set V)
    (y : ℕ → ℕ → V) (n : ℕ) :
    expFamily.map
        (fun e : (ℕ →₀ ℕ) → ℝ => fun j => e (IndexSet.addr Gs y n j) / w (y n j)) =
      holdingKernel w (y n) := by
  have hf : Measurable (fun e : (ℕ →₀ ℕ) → ℝ => fun j => e (IndexSet.addr Gs y n j)) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  have hg : Measurable (fun e : ℕ → ℝ => fun j => e j / w (y n j)) :=
    Measurable.of_eval fun j => (measurable_pi_apply j).div_const _
  rw [holdingKernel_apply hw, ← expSeq_map_div (fun j => w (y n j)) (fun j => hw _),
    ← expFamily_map_comp_addr Gs y n, Measure.map_map hg hf]
  rfl

end Kernel

namespace ContinuousTimeChain

open IndexSet PathProperties Existence

/-! ### The embedded chain and its holding times, on the sample space of Section 3.3 -/

section Law

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  {G : ConductanceGraph V} (E : G.Exhaustion) (w : V → ℝ)

/-- **The embedded discrete chain `Yⁿ` of (3.15)**, read off a sample of the coupling of
Lemma 3.4 at level offset `i` above the base level (absolute level `n = n₀ + i`). -/
def embedded (i : ℕ) (ω : Sample V) : ℕ → V := ω.1 i

/-- **The holding times of (3.15)**: `Tⁿ_j = T_{[(n,j)]} = E_{[(n,j)]} / w(Yⁿ_j)`, the paper's
`T_ξ` for `ξ = [(n,j)]`, as a real-valued sequence indexed by the jump number. -/
noncomputable def holdingSeq (n₀ i : ℕ) (ω : Sample V) : ℕ → ℝ :=
  fun j => ω.2 (addr (E.levelSets n₀) ω.1 i j) / w (ω.1 i j)

/-- **The data determining `Xⁿ`**: the embedded sequence together with its holding times,
`((Yⁿ_j)_j, (Tⁿ_j)_j)` of (3.15). -/
noncomputable def embeddedPair (n₀ i : ℕ) (ω : Sample V) : (ℕ → V) × (ℕ → ℝ) :=
  (embedded i ω, holdingSeq E w n₀ i ω)

/-- `ω ↦ E_{[(n,j)]}`, the unit holding time of the `j`-th level-`n` class, is measurable:
the class itself is one of countably many values, each on a measurable event
(`PathProperties.measurableSet_addr`). -/
lemma measurable_evalAddr (n₀ i j : ℕ) :
    Measurable fun ω : Sample V => ω.2 (addr (E.levelSets n₀) ω.1 i j) := by
  let _ : MeasurableSpace (ℕ →₀ ℕ) := ⊤
  have _ : MeasurableSingletonClass (ℕ →₀ ℕ) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have h1 : Measurable fun q : Sample V × (ℕ →₀ ℕ) => q.1.2 q.2 :=
    measurable_from_prod_countable_left fun a =>
      (measurable_pi_apply a).comp measurable_snd
  have h2 : Measurable fun ω : Sample V => addr (E.levelSets n₀) ω.1 i j :=
    measurable_to_countable' fun a =>
      PathProperties.measurableSet_addr (E.levelSets n₀) measurable_fst i j a
  exact h1.comp (measurable_id.prodMk h2)

/-- The holding times of (3.15) are random variables. -/
lemma measurable_holdingSeq (n₀ i : ℕ) : Measurable (holdingSeq E w n₀ i) :=
  Measurable.of_eval fun j =>
    (measurable_evalAddr E n₀ i j).div
      ((measurable_of_countable w).comp (Existence.measurable_Y i j))

/-- The pair `((Yⁿ_j)_j, (Tⁿ_j)_j)` is a random element of `(ℕ → V) × (ℕ → ℝ)`. -/
lemma measurable_embeddedPair (n₀ i : ℕ) : Measurable (embeddedPair E w n₀ i) :=
  (measurable_pi_apply i).comp measurable_fst |>.prodMk (measurable_holdingSeq E w n₀ i)

variable [Nontrivial V] (hG : G.toSimpleGraph.Connected)

/-- **The law of the embedded chain of `Xⁿ` is `E.chainLaw hG n z`** — the law of `Yⁿ` of
(3.2)–(3.3) started at `z`, from `ApproximatingChain.lean`.  This is Lemma 3.4's statement
that the level-`n` marginal of the coupling is the law of `Yⁿ`. -/
theorem map_embedded (n₀ : ℕ) (z : V) (i : ℕ) :
    (E.jointLaw hG n₀ z).map (embedded i) = E.chainLaw hG (n₀ + i) z := by
  have h : (embedded i : Sample V → ℕ → V) = (fun y : ℕ → ℕ → V => y i) ∘ Prod.fst := rfl
  rw [h, ← Measure.map_map (measurable_pi_apply i) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul, E.coupling_map_apply hG n₀ z i]

/-- **The law of `(Yⁿ, Tⁿ)` of (3.15).**  Under the paper's `P_z` of Section 3.3, the
embedded sequence `(Yⁿ_j)_j` is the discrete chain of (3.2)–(3.3) started at `z`, and
conditionally on it the holding times `(Tⁿ_j)_j` are independent with
`Tⁿ_j ~ Exponential(w(Yⁿ_j))` (`holdingKernel_apply`).

This is the statement of Section 3.3 that `Xⁿ` "is a continuous time version of `Yⁿ` which
spends an `exponential(w(x))` amount of time at each state `x`", and it is the form in which
Step 1 of Section 3.4 (p. 26) identifies the law of the process built from an arbitrary
process satisfying (i)–(vi). -/
theorem map_embeddedPair (hw : ∀ x, 0 < w x) (n₀ : ℕ) (z : V) (i : ℕ) :
    (E.jointLaw hG n₀ z).map (embeddedPair E w n₀ i) =
      E.chainLaw hG (n₀ + i) z ⊗ₘ holdingKernel w := by
  classical
  have hmeas := measurable_embeddedPair E w n₀ i
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply hmeas (hA.prod hB)]
  have hprod : E.jointLaw hG n₀ z = (E.coupling hG n₀ z).prod expFamily := rfl
  rw [hprod, Measure.prod_apply (hmeas (hA.prod hB))]
  have hslice : ∀ y : ℕ → ℕ → V,
      expFamily (Prod.mk y ⁻¹' (embeddedPair E w n₀ i ⁻¹' (A ×ˢ B))) =
        ((fun y : ℕ → ℕ → V => y i) ⁻¹' A).indicator
          (fun y : ℕ → ℕ → V => holdingKernel w (y i) B) y := by
    intro y
    by_cases hy : y i ∈ A
    · have hy' : y ∈ (fun y : ℕ → ℕ → V => y i) ⁻¹' A := hy
      rw [Set.indicator_of_mem hy']
      have hset : Prod.mk y ⁻¹' (embeddedPair E w n₀ i ⁻¹' (A ×ˢ B)) =
          (fun e : (ℕ →₀ ℕ) → ℝ =>
            fun j => e (addr (E.levelSets n₀) y i j) / w (y i j)) ⁻¹' B := by
        ext e
        simp only [Set.mem_preimage, embeddedPair, embedded, Set.mem_prod, hy, true_and]
        rfl
      rw [hset, ← Measure.map_apply
        (Measurable.of_eval fun j => (measurable_pi_apply _).div_const _) hB,
        expFamily_map_holding hw (E.levelSets n₀) y i]
    · have hy' : y ∉ (fun y : ℕ → ℕ → V => y i) ⁻¹' A := hy
      rw [Set.indicator_of_notMem hy']
      have hset : Prod.mk y ⁻¹' (embeddedPair E w n₀ i ⁻¹' (A ×ˢ B)) = ∅ := by
        ext e
        simp only [Set.mem_preimage, embeddedPair, embedded, Set.mem_prod, hy, false_and,
          Set.mem_empty_iff_false]
      rw [hset, measure_empty]
  simp_rw [hslice]
  rw [lintegral_indicator (measurable_pi_apply i hA),
    Measure.compProd_apply_prod hA hB, ← E.coupling_map_apply hG n₀ z i,
    setLIntegral_map hA (Kernel.measurable_coe _ hB) (measurable_pi_apply i)]

/-- **The first marginal is `E.chainLaw hG n z`** — the meeting point of the two sides of the
uniqueness comparison of Section 3.4. -/
theorem fst_map_embeddedPair (hw : ∀ x, 0 < w x) (n₀ : ℕ) (z : V) (i : ℕ) :
    ((E.jointLaw hG n₀ z).map (embeddedPair E w n₀ i)).map Prod.fst =
      E.chainLaw hG (n₀ + i) z := by
  rw [map_embeddedPair E w hG hw n₀ z i]
  exact Measure.fst_compProd _ _

/-- **The law of `(Yⁿ, Tⁿ)` under the paper's `P_z`** of Section 3.3 (base level `n_z`), the
probability space on which the existence half of Theorem 1.6 is built
(`Existence.sampleLaw`). -/
theorem sampleLaw_map_embeddedPair (hw : ∀ x, 0 < w x) (z : V) (i : ℕ) :
    (sampleLaw E hG z).map (embeddedPair E w (E.nz z) i) =
      E.chainLaw hG (E.nz z + i) z ⊗ₘ holdingKernel w :=
  map_embeddedPair E w hG hw (E.nz z) z i

/-- The embedded chain of `Xⁿ` under the paper's `P_z` has the law `E.chainLaw hG n z` of
`Yⁿ`, started at `z`. -/
theorem sampleLaw_map_embedded (z : V) (i : ℕ) :
    (sampleLaw E hG z).map (embedded i) = E.chainLaw hG (E.nz z + i) z :=
  map_embedded E hG (E.nz z) z i

end Law

/-! ### The time change of (3.15)

`Xⁿ_t = Yⁿ_k` for the unique `k` with `t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)`, and the relation
of this bookkeeping to the clock (3.25) of the full process `X`, which is (3.29). -/

section TimeChange

variable {V : Type u} (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (E : (ℕ →₀ ℕ) → ℝ)

/-- The holding times of (3.15) as a real sequence: `Tⁿ_j = T_{[(n,j)]} = E_{[(n,j)]}/w(Yⁿ_j)`,
matching `holdingSeq` on the sample space. -/
noncomputable def levelHolding (n j : ℕ) : ℝ := E (addr Gs Y n j) / w (Y n j)

/-- `T_{[(n,j)]}` is `Tⁿ_j` (the two differ only by (3.13), `Y_ξ = Yⁿ_j`). -/
lemma holding_addr_eq (h : Consistent Gs Y) (n j : ℕ) :
    holding Gs Y w E (addr Gs Y n j) = ENNReal.ofReal (levelHolding Gs Y w E n j) := by
  rw [holding, h.Yxi_addr, levelHolding]

/-- **The left endpoint of the `k`-th holding interval of (3.15)** is the partial sum
`∑_{j<k} Tⁿ_j`. -/
lemma levelTau_eq_sum (h : Consistent Gs Y) (n k : ℕ) :
    levelTau Gs Y w E n k =
      ∑ j ∈ Finset.range k, ENNReal.ofReal (levelHolding Gs Y w E n j) :=
  Finset.sum_congr rfl fun j _ => holding_addr_eq Gs Y w E h n j

/-- **(3.15), the time change.**  `Xⁿ_t = Yⁿ_k` whenever
`t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)`. -/
theorem Xn_eq_of_mem_Ico (h : Consistent Gs Y) {n k : ℕ} {t : ℝ≥0}
    (h1 : ∑ j ∈ Finset.range k, ENNReal.ofReal (levelHolding Gs Y w E n j) ≤ t)
    (h2 : (t : ℝ≥0∞) < ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (levelHolding Gs Y w E n j)) :
    Xn Gs Y w E n t = some (Y n k) :=
  Xn_eq_of_inLevelInterval Gs Y w E
    ⟨by rw [levelTau_eq_sum Gs Y w E h]; exact h1, by rw [levelTau_eq_sum Gs Y w E h]; exact h2⟩

/-- **The index `k` of the time change is unique**: the holding intervals of (3.15) are
pairwise disjoint. -/
theorem mem_Ico_unique {n k k' : ℕ} {t : ℝ≥0∞}
    (h1 : levelTau Gs Y w E n k ≤ t ∧ t < levelTau Gs Y w E n (k + 1))
    (h2 : levelTau Gs Y w E n k' ≤ t ∧ t < levelTau Gs Y w E n (k' + 1)) : k = k' :=
  inLevelInterval_unique Gs Y w E h1 h2

/-- **The time change covers `[0, ∞)`** as soon as the level-`n` holding times diverge,
`∑_j Tⁿ_j = ∞` — which holds a.s. because `Yⁿ` returns to its starting point infinitely often
(Remark 3.1, Step 0 of Lemma 3.5; the level-`0` case is
`Exhaustion.jointLaw_ae_tsum_holding_addr_zero_eq_top` in `RateFunction.lean`). -/
theorem exists_inLevelInterval {n : ℕ}
    (h_tsum_holding_addr_eq_top : ∑' j, holding Gs Y w E (addr Gs Y n j) = ⊤) (t : ℝ≥0) :
    ∃ k, InLevelInterval Gs Y w E n k t := by
  classical
  have hsup : (⨆ k, levelTau Gs Y w E n k) = ⊤ := by
    rw [← h_tsum_holding_addr_eq_top, ENNReal.tsum_eq_iSup_nat]
    rfl
  have hex : ∃ k, (t : ℝ≥0∞) < levelTau Gs Y w E n k := by
    refine lt_iSup_iff.mp ?_
    rw [hsup]
    exact ENNReal.coe_lt_top
  have hmspec : (t : ℝ≥0∞) < levelTau Gs Y w E n (Nat.find hex) := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0] at hmspec
      have hz : levelTau Gs Y w E n 0 = 0 := by simp [levelTau]
      rw [hz] at hmspec
      exact absurd hmspec (not_lt.mpr zero_le)
    · exact hpos
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  refine ⟨Nat.find hex - 1, not_lt.mp (Nat.find_min hex (by omega)), ?_⟩
  rw [hsucc]
  exact hmspec

/-- **`Xⁿ` is defined at every time**, given the divergence `∑_j Tⁿ_j = ∞`. -/
theorem Xn_ne_none {n : ℕ} (h_tsum_holding_addr_eq_top : ∑' j, holding Gs Y w E (addr Gs Y n j) = ⊤) (t : ℝ≥0) :
    Xn Gs Y w E n t ≠ none :=
  fun hc => ((Xn_eq_none_iff Gs Y w E n t).mp hc) (exists_inLevelInterval Gs Y w E h_tsum_holding_addr_eq_top t)

/-- The remainder `Rⁿ` of (3.29) is finite as soon as the clock (3.25) is, which is (3.16). -/
lemma remainder_ne_top {n j : ℕ} (hτ : tau Gs Y w E (addr Gs Y n j) ≠ ⊤) :
    remainder Gs Y w E n (addr Gs Y n j) ≠ ⊤ := by
  refine ne_top_of_le_ne_top hτ ?_
  rw [tau_eq_levelTau_add]
  exact le_add_self

/-- **(3.29), as an identity of holding intervals.**  The `j`-th holding interval of `Xⁿ`
(3.15) is the interval `[τ_η, τ_η̂)` of (3.26) for `η = [(n,j)]`, translated by the remainder
`Rⁿ`: `t` lies in the former iff `t + Rⁿ` lies in the latter.  Together with
`PathProperties.Xn_eq_X` this is the whole content of `X_t = Xⁿ_{t - Rⁿ}` on `[τ_η, τ_η̂)`. -/
theorem inLevelInterval_iff_inInterval (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {n j : ℕ}
    (h_remainder_ne_top : remainder Gs Y w E n (addr Gs Y n j) ≠ ⊤) (t : ℝ≥0∞) :
    InLevelInterval Gs Y w E n j t ↔
      InInterval Gs Y w E (addr Gs Y n j) (t + remainder Gs Y w E n (addr Gs Y n j)) := by
  unfold InLevelInterval InInterval
  rw [tau_eq_levelTau_add, tau_succ_eq_levelTau_add Gs Y w E h hG hcov,
    ENNReal.add_le_add_iff_right h_remainder_ne_top,
    ENNReal.add_lt_add_iff_right h_remainder_ne_top,
    and_iff_right (realized_addr Gs Y n j)]

end TimeChange

/-! ### `Xⁿ` as a functional of `(Yⁿ, Tⁿ)`, and the law of its whole path

(3.15) reads `Xⁿ` off the embedded chain and its holding times by a fixed, measurable time
change `jumpPath`.  Combined with `map_embeddedPair` this identifies the law of the *path* of
`Xⁿ`: it is the pushforward of `E.chainLaw hG n z ⊗ₘ holdingKernel w` under `jumpPath`.  This
is the sense in which the process `X̃ⁿ` extracted from an arbitrary process satisfying
(i)–(vi) in Step 1 of Section 3.4 (p. 26) "has the same law as the process `Xⁿ` defined in
(3.15)": it suffices to match the joint law of the embedded chain and the holding times. -/

section JumpPath

variable {V : Type u}

/-- The clock of (3.15) read off a sequence of holding times: `∑_{j<k} T_j`. -/
noncomputable def jumpClock (T : ℕ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range k, ENNReal.ofReal (T j)

lemma jumpClock_mono (T : ℕ → ℝ) : Monotone (jumpClock T) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [jumpClock, jumpClock, Finset.sum_range_succ]
  exact le_self_add

/-- `t` lies in the `k`-th holding interval `[∑_{j<k} T_j, ∑_{j≤k} T_j)` of (3.15). -/
def InJump (T : ℕ → ℝ) (k : ℕ) (t : ℝ≥0∞) : Prop :=
  jumpClock T k ≤ t ∧ t < jumpClock T (k + 1)

/-- The holding intervals of (3.15) are pairwise disjoint, so the time change is well defined. -/
lemma inJump_unique {T : ℕ → ℝ} {k k' : ℕ} {t : ℝ≥0∞} (h1 : InJump T k t) (h2 : InJump T k' t) :
    k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (lt_of_lt_of_le h1.2 (le_trans (jumpClock_mono T hlt) h2.1)) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le h2.2 (le_trans (jumpClock_mono T hlt) h1.1)) (lt_irrefl _)

open Classical in
/-- **(3.15) as a functional of the embedded chain and its holding times**: for a path
`y : ℕ → V` and holding times `T : ℕ → ℝ`, `jumpPath (y, T) t = y k` for the unique `k` with
`t ∈ [∑_{j<k} T_j, ∑_{j≤k} T_j)`, and `∞` (`none`) if `t` lies in no such interval. -/
noncomputable def jumpPath (p : (ℕ → V) × (ℕ → ℝ)) (t : ℝ≥0) : Option V :=
  if h : ∃ k, InJump p.2 k (t : ℝ≥0∞) then some (p.1 (Classical.choose h)) else none

lemma jumpPath_eq_of_inJump {p : (ℕ → V) × (ℕ → ℝ)} {k : ℕ} {t : ℝ≥0}
    (hk : InJump p.2 k (t : ℝ≥0∞)) : jumpPath p t = some (p.1 k) := by
  unfold jumpPath
  rw [dite_eq_left ⟨k, hk⟩]
  exact congrArg (fun k => some (p.1 k)) (inJump_unique
    (Classical.choose_spec (⟨k, hk⟩ : ∃ k, InJump p.2 k (t : ℝ≥0∞))) hk)

lemma jumpPath_eq_none_iff (p : (ℕ → V) × (ℕ → ℝ)) (t : ℝ≥0) :
    jumpPath p t = none ↔ ¬ ∃ k, InJump p.2 k (t : ℝ≥0∞) := by
  unfold jumpPath
  split_ifs with hx <;> simp [hx]

lemma jumpPath_eq_some_iff (p : (ℕ → V) × (ℕ → ℝ)) (t : ℝ≥0) (x : V) :
    jumpPath p t = some x ↔ ∃ k, InJump p.2 k (t : ℝ≥0∞) ∧ p.1 k = x := by
  constructor
  · intro ht
    obtain ⟨k, hk⟩ : ∃ k, InJump p.2 k (t : ℝ≥0∞) := by
      by_contra hn
      rw [(jumpPath_eq_none_iff p t).mpr hn] at ht
      exact absurd ht (by simp)
    rw [jumpPath_eq_of_inJump hk] at ht
    exact ⟨k, hk, Option.some_injective V ht⟩
  · rintro ⟨k, hk, rfl⟩
    exact jumpPath_eq_of_inJump hk

/-- **`Xⁿ` is the time change of `(Yⁿ, Tⁿ)`**: (3.15) depends on the sample only through the
embedded chain `Yⁿ` and its holding times `Tⁿ`. -/
theorem Xn_eq_jumpPath (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (Eh : (ℕ →₀ ℕ) → ℝ)
    (h : Consistent Gs Y) (n : ℕ) (t : ℝ≥0) :
    Xn Gs Y w Eh n t = jumpPath (Y n, levelHolding Gs Y w Eh n) t := by
  have hclock : ∀ k, jumpClock (levelHolding Gs Y w Eh n) k = levelTau Gs Y w Eh n k :=
    fun k => (levelTau_eq_sum Gs Y w Eh h n k).symm
  by_cases hx : ∃ k, InLevelInterval Gs Y w Eh n k (t : ℝ≥0∞)
  · obtain ⟨k, hk⟩ := hx
    rw [Xn_eq_of_inLevelInterval Gs Y w Eh hk,
      jumpPath_eq_of_inJump (p := (Y n, levelHolding Gs Y w Eh n)) (k := k)
        ⟨by rw [show ((Y n, levelHolding Gs Y w Eh n) : (ℕ → V) × (ℕ → ℝ)).2 =
              levelHolding Gs Y w Eh n from rfl, hclock]; exact hk.1,
         by rw [show ((Y n, levelHolding Gs Y w Eh n) : (ℕ → V) × (ℕ → ℝ)).2 =
              levelHolding Gs Y w Eh n from rfl, hclock]; exact hk.2⟩]
  · rw [(Xn_eq_none_iff Gs Y w Eh n t).mpr hx,
      (jumpPath_eq_none_iff (Y n, levelHolding Gs Y w Eh n) t).mpr]
    rintro ⟨k, hk1, hk2⟩
    exact hx ⟨k, by rw [← hclock]; exact hk1, by rw [← hclock]; exact hk2⟩

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

omit [Countable V] [MeasurableSingletonClass V] in
lemma measurable_jumpClock (k : ℕ) :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => jumpClock p.2 k :=
  Finset.measurable_sum _ fun j _ =>
    ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).comp measurable_snd)

/-- The time change of (3.15) is measurable, so it transports laws. -/
lemma measurable_jumpPath (t : ℝ≥0) :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => jumpPath p t := by
  have hsome : ∀ x : V,
      MeasurableSet ((fun p : (ℕ → V) × (ℕ → ℝ) => jumpPath p t) ⁻¹' {some x}) := by
    intro x
    have e : (fun p : (ℕ → V) × (ℕ → ℝ) => jumpPath p t) ⁻¹' {some x} =
        ⋃ k, (({p : (ℕ → V) × (ℕ → ℝ) | jumpClock p.2 k ≤ (t : ℝ≥0∞)} ∩
          {p | (t : ℝ≥0∞) < jumpClock p.2 (k + 1)}) ∩ {p | p.1 k = x}) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_ofPred_eq, jumpPath_eq_some_iff, InJump, and_assoc]
    rw [e]
    refine MeasurableSet.iUnion fun k => MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
    · exact measurable_jumpClock k measurableSet_Iic
    · exact measurable_jumpClock (k + 1) measurableSet_Ioi
    · have hk : Measurable fun p : (ℕ → V) × (ℕ → ℝ) => p.1 k :=
        (measurable_pi_apply k).comp measurable_fst
      exact hk (measurableSet_singleton x)
  refine measurable_to_countable' fun o => ?_
  cases o with
  | none =>
    rw [PathProperties.preimage_none_eq_compl_iUnion]
    exact (MeasurableSet.iUnion hsome).compl
  | some x => exact hsome x

/-- The path `t ↦ Xⁿ_t` as a random element of the path space `Trajectory V`. -/
lemma measurable_jumpTrajectory :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => (fun t => jumpPath p t : Trajectory V) :=
  Measurable.of_eval fun t => measurable_jumpPath t

end JumpPath

/-! ### The law of the path of `Xⁿ`, and its transition function -/

section Trajectory

open Existence

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  {G : ConductanceGraph V} (E : G.Exhaustion) (w : V → ℝ)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- On the sample space of Section 3.3, `Xⁿ` is the time change of `embeddedPair`. -/
lemma processN_eq_jumpPath (n₀ i : ℕ) {ω : Sample V}
    (hc : Consistent (E.levelSets n₀) ω.1) (t : ℝ≥0) :
    PathProperties.processN (E.levelSets n₀) w Prod.fst Prod.snd i t ω =
      jumpPath (embeddedPair E w n₀ i ω) t :=
  Xn_eq_jumpPath (E.levelSets n₀) ω.1 w ω.2 hc i t

variable [Nontrivial V] (hG : G.toSimpleGraph.Connected)

/-- **The law of the whole path of `Xⁿ` of (3.15)**: the pushforward, under the time change,
of the joint law `E.chainLaw hG n z ⊗ₘ holdingKernel w` of the embedded chain and its holding
times.  Any process whose embedded chain and holding times have that joint law therefore has
the same law as `Xⁿ` — this is the last sentence of Step 1 of Section 3.4 (p. 26). -/
theorem map_trajectoryN (hw : ∀ x, 0 < w x) (n₀ : ℕ) (z : V) (i : ℕ) :
    (E.jointLaw hG n₀ z).map
        (fun ω => (fun t => PathProperties.processN (E.levelSets n₀) w Prod.fst Prod.snd i t ω :
          Trajectory V)) =
      (E.chainLaw hG (n₀ + i) z ⊗ₘ holdingKernel w).map
        (fun p => (fun t => jumpPath p t : Trajectory V)) := by
  have hae : (fun ω : Sample V =>
      (fun t => PathProperties.processN (E.levelSets n₀) w Prod.fst Prod.snd i t ω :
        Trajectory V)) =ᵐ[E.jointLaw hG n₀ z]
      fun ω : Sample V => (fun t => jumpPath (embeddedPair E w n₀ i ω) t : Trajectory V) := by
    filter_upwards [E.jointLaw_ae_consistent hG n₀ z] with ω hc
    exact funext fun t => processN_eq_jumpPath E w n₀ i hc t
  rw [Measure.map_congr hae, ← map_embeddedPair E w hG hw n₀ z i,
    Measure.map_map measurable_jumpTrajectory (measurable_embeddedPair E w n₀ i)]
  rfl

/-- **The transition function of `Xⁿ`**: `P_z(Xⁿ_t = y)` is computed from the joint law of the
embedded chain and its holding times.  This is `ProcessFamily.transition` of `chainFamily`
(`chainFamily_transition`). -/
theorem measure_processN_eq (hw : ∀ x, 0 < w x) (n₀ : ℕ) (z : V) (i : ℕ) (t : ℝ≥0) (y : V) :
    E.jointLaw hG n₀ z
        {ω | PathProperties.processN (E.levelSets n₀) w Prod.fst Prod.snd i t ω = some y} =
      (E.chainLaw hG (n₀ + i) z ⊗ₘ holdingKernel w) {p | jumpPath p t = some y} := by
  have hsy : MeasurableSet {p : (ℕ → V) × (ℕ → ℝ) | jumpPath p t = some y} :=
    measurable_jumpPath t (measurableSet_singleton (some y))
  calc E.jointLaw hG n₀ z
        {ω | PathProperties.processN (E.levelSets n₀) w Prod.fst Prod.snd i t ω = some y}
      = E.jointLaw hG n₀ z {ω | jumpPath (embeddedPair E w n₀ i ω) t = some y} := by
        refine measure_congr ?_
        filter_upwards [E.jointLaw_ae_consistent hG n₀ z] with ω hc
        simp only [processN_eq_jumpPath E w n₀ i hc t]
    _ = E.jointLaw hG n₀ z
          (embeddedPair E w n₀ i ⁻¹' {p : (ℕ → V) × (ℕ → ℝ) | jumpPath p t = some y}) := rfl
    _ = ((E.jointLaw hG n₀ z).map (embeddedPair E w n₀ i))
          {p : (ℕ → V) × (ℕ → ℝ) | jumpPath p t = some y} :=
        (Measure.map_apply (measurable_embeddedPair E w n₀ i) hsy).symm
    _ = (E.chainLaw hG (n₀ + i) z ⊗ₘ holdingKernel w)
          {p : (ℕ → V) × (ℕ → ℝ) | jumpPath p t = some y} := by
        rw [map_embeddedPair E w hG hw n₀ z i]

end Trajectory

/-! ### `Xⁿ` as a process family, and its transition function -/

section Family

open Existence

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  {G : ConductanceGraph V} (E : G.Exhaustion) (w : V → ℝ)

/-- `Xⁿ` of (3.15) is a random variable on the sample space of Section 3.3 (the fibres are
measurable by `PathProperties.measurableSet_prod_Xn`, read at a fixed time). -/
lemma measurable_Xn_sample (Gs : ℕ → Set V) (n : ℕ) (t : ℝ≥0) :
    Measurable fun ω : Sample V => Xn Gs ω.1 w ω.2 n t := by
  refine measurable_to_countable' fun o => ?_
  have e : (fun ω : Sample V => Xn Gs ω.1 w ω.2 n t) ⁻¹' {o} =
      (fun ω : Sample V => (ω, (t : ℝ))) ⁻¹'
        {q : Sample V × ℝ |
          Xn Gs (Prod.fst q.1) w (Prod.snd q.1) n (Real.toNNReal q.2) = o} := by
    ext ω
    simp [Real.toNNReal_coe]
  rw [e]
  exact (measurable_id.prodMk measurable_const)
    (PathProperties.measurableSet_prod_Xn Gs w measurable_fst measurable_snd n o)

/-- `Xⁿ` with the base level `n_{Y⁰₀}` read off the starting vertex, as in
`Existence.process`, is a random variable. -/
lemma measurable_chainX (i : ℕ) (t : ℝ≥0) :
    Measurable fun ω : Sample V =>
      PathProperties.processN (E.levelSets (E.nz (ω.1 0 0))) w Prod.fst Prod.snd i t ω := by
  have h : (fun ω : Sample V =>
      PathProperties.processN (E.levelSets (E.nz (ω.1 0 0))) w Prod.fst Prod.snd i t ω) =
      fun ω : Sample V => (fun q : Sample V × V =>
        PathProperties.processN (E.levelSets (E.nz q.2)) w Prod.fst Prod.snd i t q.1)
          (ω, ω.1 0 0) := rfl
  rw [h]
  have hF : Measurable fun q : Sample V × V =>
      PathProperties.processN (E.levelSets (E.nz q.2)) w Prod.fst Prod.snd i t q.1 := by
    refine measurable_from_prod_countable_left fun v => ?_
    exact measurable_Xn_sample w (E.levelSets (E.nz v)) i t
  exact hF.comp (measurable_id.prodMk (Existence.measurable_Y (V := V) 0 0))

variable [Nontrivial V] (hG : G.toSimpleGraph.Connected)

/-- **The process family of the continuous-time approximating chain `Xⁿ` of (3.15)**, at the
level `n = n_z + i` above the starting point, on the sample space of Section 3.3 with the
paper's `P_z`.  Same shape as `Existence.processFamily` for the limit process `X`, so the two
are comparable objects. -/
noncomputable def chainFamily (i : ℕ) : ProcessFamily V where
  Ω := Sample V
  X := fun t ω =>
    PathProperties.processN (E.levelSets (E.nz (ω.1 0 0))) w Prod.fst Prod.snd i t ω
  measurable_X := fun t => measurable_chainX E w i t
  P := sampleLaw E hG

/-- The law of the family started at `z`, unfolded. -/
lemma chainFamily_P (i : ℕ) (z : V) : (chainFamily E w hG i).P z = sampleLaw E hG z := rfl

/-- **The transition function of `Xⁿ`**: `pⁿ_t(z, y) = P_z(Xⁿ_t = y)` is the `jumpPath` time
change applied to the joint law `E.chainLaw hG (n_z+i) z ⊗ₘ holdingKernel w` of the embedded
chain and its holding times.

The left-hand side is literally `TransitionUniqueness`'s `ProcessFamily.transition`, which is
`𝓧.P z {ω | 𝓧.X t ω = some y}` by definition; it is spelled out here so that this file does
not import `ReflectedWalk.TransitionUniqueness`, and
`(chainFamily E w hG i).transition z t y = …` follows from this statement by `rfl` on the
left-hand side.  The whole `t`-family determines the finite-dimensional distributions of a
process satisfying (i)–(vi) (`Theorem16.identDistrib_of_transition`). -/
theorem chainFamily_transition (hw : ∀ x, 0 < w x) (i : ℕ) (z : V) (t : ℝ≥0) (y : V) :
    (chainFamily E w hG i).P z {ω | (chainFamily E w hG i).X t ω = some y} =
      (E.chainLaw hG (E.nz z + i) z ⊗ₘ holdingKernel w)
        {p : (ℕ → V) × (ℕ → ℝ) | jumpPath p t = some y} := by
  rw [← measure_processN_eq E w hG hw (E.nz z) z i t y]
  refine measure_congr ?_
  filter_upwards [Existence.sampleLaw_ae_start E hG z] with ω h0
  show ((chainFamily E w hG i).X t ω = some y) =
    (PathProperties.processN (E.levelSets (E.nz z)) w Prod.fst Prod.snd i t ω = some y)
  rw [show (chainFamily E w hG i).X t ω =
    PathProperties.processN (E.levelSets (E.nz (ω.1 0 0))) w Prod.fst Prod.snd i t ω from rfl,
    h0 0]

end Family

end ContinuousTimeChain

end ReflectedWalk
