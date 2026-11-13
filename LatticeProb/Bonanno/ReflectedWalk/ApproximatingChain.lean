/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.ApproximatingChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.FiniteApproximation
import LatticeProb.Bonanno.ReflectedWalk.IndexSet
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Kernel.Irreducible
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The approximating chains `Yⁿ` (Gwynne–Sung, Section 3.1)

Section 3.1 of arXiv:2506.18827 fixes a finite connected subgraph `Gₙ` of `G` and defines a
discrete-time Markov chain `Yⁿ` on the radius-one neighbourhood

  `B₁Gₙ = {x : x ∈ VGₙ or x ∼ y for some y ∈ VGₙ}`   (3.1)

with transition probabilities

  `pₙ(x,y) = c(x,y)/π(x)` for `x ∈ VGₙ`,   (3.2)
  `pₙ(x,y) = hm^x_{VGₙ}(y)` for `x ∈ B₁Gₙ ∖ Gₙ`.   (3.3)

This file builds (3.1)–(3.3) as a genuine `ProbabilityTheory.Kernel` on `V` (`stepKernel`),
proves it is a Markov kernel, constructs the law of the chain started at `z` by the
Ionescu–Tulcea theorem (`MarkovChain.chainLaw`, `Exhaustion.chainLaw`), proves **Lemma 3.2**
(the hitting distribution of a finite `A ⊆ VGₙ` is the energy-minimizing harmonic measure,
`energyMin_eq_integral_hitVertex`), formalizes **Remark 3.1** — the induced chain `Ỹⁿ` on the
finite set `VGₙ` with transition probabilities (3.4) (`inducedKernel`) and its irreducibility
(`inducedKernel_isIrreducible`, in the sense of mathlib's `Kernel.IsIrreducible`) — and proves
**Lemma 3.3**, the consistency of the chains under the coarsening (3.9) of `IndexSet.lean`
(`chainLaw_map_coarsenPath`), via a strong Markov property at the hitting time
(`chainLaw_map_walkShift_hitIndex`).  The almost-sure finiteness of hitting times of finite
sets (`hitTime_ae_ne_top`), which Lemmas 3.2 and 3.3 need, is proved directly by a maximum
principle; the general recurrence theory of Remark 3.1 lives elsewhere.

## Design

* `B₁Gₙ` may be infinite, since `G` is not locally finite; no finiteness of `B₁Gₙ` is ever
  assumed.  The kernel `stepKernel` is defined on **all** of `V` by the same two formulas
  (from any `x ∉ VGₙ` the chain jumps into `VGₙ` by harmonic measure); its restriction to
  the invariant set `B₁Gₙ` (`stepKernel_ball1_compl`, `chainLaw_ae_mem_ball1`) is the paper's
  chain, and every statement proved for all starting points `x ∈ V` in particular covers
  `x ∈ B₁Gₙ`.
* The chain law is `Kernel.trajMeasure (dirac z) (histKernel κ)` where `histKernel κ n` is the
  one-step kernel `κ` read off the last coordinate of the history — the five-line idiom of
  `BouRabeeGwynne/StoppedWalk.lean`.  The generic material in `MarkovChain` (finite-history
  bookkeeping, the restart identity `chainLaw_map_walkShift`, the first-step decomposition
  `integral_walkShift_one`) is adapted from the sibling project's `TrajectoryCoupling.lean`,
  `WalkMemoryless.lean`, `WalkJointRestart.lean` and `StoppedWalk.lean`, generalized from
  `[Fintype V]` to an arbitrary measurable state space (the state space of the paper is
  countable, and `[Countable V] [MeasurableSingletonClass V]` is assumed only where a set of
  vertices has to be measurable).
* Finiteness of hitting times and Lemma 3.2 are both proved by the paper's own argument: a
  first-step analysis (the Markov property, (3.7)/(3.8)) followed by a maximum principle on
  the finite set `VGₙ` (`eq_zero_of_mean_value`), which is exactly how the paper uses the
  induced chain of Remark 3.1.  Hitting times are mathlib's `hittingAfter` and are stopping
  times for the canonical filtration `Filtration.piLE`.
-/

open MeasureTheory ProbabilityTheory Set Preorder Filter
open scoped ENNReal Topology

namespace ReflectedWalk

namespace MarkovChain

/-! ### Finite histories (adapted from `BouRabeeGwynne.TrajectoryCoupling` / `WalkMemoryless`) -/

section Histories

variable {S : Type*}

/-- Append one state to a finite history (BouRabeeGwynne `TrajectoryCoupling.append`). -/
def append (n : ℕ) (p : (Finset.Iic n → S) × S) : Finset.Iic (n + 1) → S :=
  fun i => if hi : i.val ≤ n then p.1 ⟨i.val, Finset.mem_Iic.mpr hi⟩ else p.2

lemma append_restrict (n : ℕ) (ω : ℕ → S) :
    append n (frestrictLe n ω, ω (n + 1)) = frestrictLe (n + 1) ω := by
  funext i
  by_cases hi : i.val ≤ n
  · simp [append, hi, frestrictLe_apply]
  · have heq : i.val = n + 1 := by have := Finset.mem_Iic.mp i.property; omega
    simp [append, frestrictLe_apply, heq]

/-- The suffix of a finite history starting at time `a` (BouRabeeGwynne `shiftPrefix`). -/
def shiftPrefix (a k : ℕ) (h : Finset.Iic (a + k) → S) : Finset.Iic k → S :=
  fun i => h ⟨a + i.val, Finset.mem_Iic.mpr
    (Nat.add_le_add_left (Finset.mem_Iic.mp i.property) a)⟩

lemma shiftPrefix_zero (a : ℕ) (h : Finset.Iic a → S) :
    shiftPrefix a 0 h = fun _ => h ⟨a, Finset.mem_Iic.mpr le_rfl⟩ := by
  funext i
  have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
  simp [shiftPrefix, hi]

lemma shiftPrefix_append (a k : ℕ) :
    shiftPrefix (S := S) a (k + 1) ∘ append (a + k) =
      append k ∘ Prod.map (shiftPrefix a k) id := by
  funext p i
  by_cases hi : i.val ≤ k
  · have hai : a + i.val ≤ a + k := Nat.add_le_add_left hi a
    simp [shiftPrefix, append, hi, hai]
  · have hai : ¬ a + i.val ≤ a + k := by omega
    simp [shiftPrefix, append, hi, hai]

/-- The path shifted by `n` steps, `(θ_n ω)_k = ω_{n+k}` (BouRabeeGwynne `walkShift`). -/
def walkShift (n : ℕ) (ω : ℕ → S) : ℕ → S := fun k => ω (n + k)

@[simp] lemma walkShift_apply (n k : ℕ) (ω : ℕ → S) : walkShift n ω k = ω (n + k) := rfl

/-- The last coordinate of a finite history of length `n`. -/
abbrev lastCoord (n : ℕ) (h : Finset.Iic n → S) : S := h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

variable [MeasurableSpace S]

lemma measurable_append (n : ℕ) : Measurable (append (S := S) n) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.val ≤ n
  · simp only [append, hi, ↓reduceDIte]
    exact (measurable_fst : Measurable
      (Prod.fst : (Finset.Iic n → S) × S → (Finset.Iic n → S))).eval
  · simpa only [append, hi, ↓reduceDIte] using
      (measurable_snd : Measurable (Prod.snd : (Finset.Iic n → S) × S → S))

lemma measurable_shiftPrefix (a k : ℕ) : Measurable (shiftPrefix (S := S) a k) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

lemma measurable_walkShift (n : ℕ) : Measurable (walkShift (S := S) n) :=
  Measurable.of_eval fun k => measurable_pi_apply (n + k)

lemma measurable_lastCoord (n : ℕ) : Measurable (lastCoord (S := S) n) := measurable_pi_apply _

/-- Equality of all finite-prefix pushforwards determines a finite measure on sequence space
(BouRabeeGwynne `TrajectoryCoupling.measure_eq_of_prefix_eq`, cylinder uniqueness). -/
lemma measure_eq_of_prefix_eq (ρ σ : Measure (ℕ → S)) [IsFiniteMeasure ρ]
    (hprefix : ∀ n, ρ.map (frestrictLe n) = σ.map (frestrictLe n)) : ρ = σ := by
  have hall (I : Finset ℕ) : ρ.map I.restrict = σ.map I.restrict := by
    let q : (Finset.Iic (I.sup id) → S) → (I → S) :=
      fun h i => h ⟨i.val, I.subset_Iic_sup_id i.property⟩
    have hq : Measurable q := Measurable.of_eval fun _ => measurable_pi_apply _
    have heq : q ∘ frestrictLe (π := fun _ : ℕ => S) (I.sup id) =
        I.restrict (π := fun _ : ℕ => S) := rfl
    calc
      ρ.map I.restrict = (ρ.map (frestrictLe (I.sup id))).map q := by
        rw [Measure.map_map hq (measurable_frestrictLe _), heq]
      _ = (σ.map (frestrictLe (I.sup id))).map q := congrArg (fun m => m.map q) (hprefix _)
      _ = σ.map I.restrict := by rw [Measure.map_map hq (measurable_frestrictLe _), heq]
  apply MeasureTheory.ext_of_generate_finite (measurableCylinders (fun _ : ℕ => S))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro s hs
    obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders _).mp hs
    rw [cylinder, ← Measure.map_apply (by fun_prop) ht,
      ← Measure.map_apply (by fun_prop) ht, hall]
  · have hu := congrArg (fun m : Measure (Finset.Iic 0 → S) => m univ) (hprefix 0)
    simpa only [Measure.map_apply (measurable_frestrictLe 0) MeasurableSet.univ,
      preimage_univ] using hu

end Histories

section ProductMap

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

/-- Pushforward of a `compProd` along a product map intertwining the kernels
(BouRabeeGwynne `compProd_map_prod_of_kernel_map`). -/
lemma compProd_map_prod_of_kernel_map (μ : Measure A) [SFinite μ]
    (κ : Kernel A B) [IsSFiniteKernel κ] (η : Kernel C D) [IsSFiniteKernel η]
    (f : A → C) (g : B → D) (hf : Measurable f) (hg : Measurable g)
    (hmap : ∀ a, (κ a).map g = η (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f g) = μ.map f ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap hg) hs,
    Measure.compProd_apply ((hf.prodMap hg) hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro a
  rw [← hmap a, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

end ProductMap

/-! ### Prefix laws of Ionescu–Tulcea trajectories
(adapted from `BouRabeeGwynne.TrajectoryCoupling` and `WalkMemoryless`) -/

section Prefixes

variable {S : Type*} [MeasurableSpace S]
  (κ : (n : ℕ) → Kernel (Finset.Iic n → S) S) [∀ n, IsMarkovKernel (κ n)]

/-- The prefix of length `n + 1` of a trajectory law is obtained from the prefix of length `n`
by one more transition (BouRabeeGwynne `TrajectoryCoupling.prefix_succ`). -/
lemma prefix_succ (μ : Measure S) [IsProbabilityMeasure μ] (n : ℕ) :
    (Kernel.trajMeasure (X := fun _ => S) μ κ).map (frestrictLe (n + 1)) =
      ((Kernel.trajMeasure (X := fun _ => S) μ κ).map (frestrictLe n) ⊗ₘ κ n).map (append n) := by
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.map_map (measurable_append n) (by fun_prop)]
  congr 1
  funext ω
  exact (append_restrict n ω).symm

/-- The continuation kernel started from a history `h` has `h` as its prefix
(BouRabeeGwynne `TrajectoryCoupling.prefix_at_start_traj`). -/
lemma prefix_at_start_traj (a : ℕ) (h : Finset.Iic a → S) :
    (Kernel.traj (X := fun _ => S) κ a h).map (frestrictLe a) = Measure.dirac h := by
  have hp := congrArg (fun k : Kernel (Finset.Iic a → S) (Finset.Iic a → S) => k h)
    (Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := κ) a a)
  simpa only [Kernel.map_apply _ (measurable_frestrictLe a),
    Kernel.partialTraj_self, Kernel.id_apply] using hp

/-- One more transition of the continuation kernel
(BouRabeeGwynne `TrajectoryCoupling.prefix_succ_traj`). -/
lemma prefix_succ_traj (a b : ℕ) (hab : a ≤ b) (h : Finset.Iic a → S) :
    (Kernel.traj (X := fun _ => S) κ a h).map (frestrictLe (b + 1)) =
      ((Kernel.traj (X := fun _ => S) κ a h).map (frestrictLe b) ⊗ₘ κ b).map
        (append b) := by
  have hp := congrArg (fun k : Kernel (Finset.Iic a → S) (Finset.Iic b → S) => k h)
    (Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := κ) a b)
  simp only [Kernel.map_apply _ (measurable_frestrictLe b)] at hp
  have hs := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => S) (κ := κ) (x₀ := h) hab
  rw [← hp] at hs
  rw [hs, Measure.map_map (measurable_append b) (by fun_prop)]
  congr 1
  funext ω
  exact (append_restrict b ω).symm

end Prefixes

/-! ### The chain generated by a one-step Markov kernel -/

section Chain

variable {S : Type*} [MeasurableSpace S] (κ : Kernel S S) [IsMarkovKernel κ]

/-- The history-dependent kernel of a time-homogeneous chain: the next state is drawn from
`κ` at the last coordinate of the history (BouRabeeGwynne `historyKernel`). -/
noncomputable def histKernel (n : ℕ) : Kernel (Finset.Iic n → S) S :=
  κ.comap (lastCoord n) (measurable_lastCoord n)

instance histKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (histKernel κ n) := by
  unfold histKernel
  infer_instance

omit [IsMarkovKernel κ] in
lemma histKernel_apply (n : ℕ) (h : Finset.Iic n → S) : histKernel κ n h = κ (lastCoord n h) :=
  rfl

/-- The law `P_z` of the chain with one-step kernel `κ` started at `z`, from Ionescu–Tulcea
(BouRabeeGwynne `trajectoryLaw`). -/
noncomputable def chainLaw (z : S) : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) (Measure.dirac z) (histKernel κ)

instance chainLaw_isProbabilityMeasure (z : S) : IsProbabilityMeasure (chainLaw κ z) := by
  unfold chainLaw
  infer_instance

/-- The initial history is the starting point (BouRabeeGwynne `trajectoryLaw_initialHistory`). -/
lemma chainLaw_initialHistory (z : S) :
    (chainLaw κ z).map (frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 => z) := by
  rw [chainLaw, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (by fun_prop)]
  rfl

lemma chainLaw_marginal_zero (z : S) :
    (chainLaw κ z).map (fun ω => ω 0) = Measure.dirac z := by
  have heq : (fun ω : ℕ → S => ω 0) = lastCoord 0 ∘ frestrictLe 0 := rfl
  rw [heq, ← Measure.map_map (measurable_lastCoord 0) (measurable_frestrictLe 0),
    chainLaw_initialHistory, Measure.map_dirac' (measurable_lastCoord 0)]

/-- `Y_0 = z` almost surely under `P_z`. -/
lemma chainLaw_ae_start [MeasurableSingletonClass S] (z : S) :
    ∀ᵐ ω ∂chainLaw κ z, ω 0 = z := by
  have h : ∀ᵐ y ∂(chainLaw κ z).map (fun ω => ω 0), y = z := by
    rw [chainLaw_marginal_zero]
    exact (ae_dirac_iff (measurableSet_singleton z)).mpr rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h

/-- The Markov property at a deterministic time, joint form: the law of (history up to `n`,
state at `n + 1`) is the prefix law composed with `κ` (BouRabeeGwynne
`trajectoryLaw_history_next`). -/
lemma chainLaw_history_next (z : S) (n : ℕ) :
    (chainLaw κ z).map (frestrictLe n) ⊗ₘ histKernel κ n =
      (chainLaw κ z).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- One-step marginals evolve by `κ` (BouRabeeGwynne `trajectoryLaw_marginal_succ`). -/
lemma chainLaw_marginal_succ (z : S) (n : ℕ) :
    (chainLaw κ z).map (fun ω => ω (n + 1)) = κ ∘ₘ (chainLaw κ z).map (fun ω => ω n) := by
  symm
  calc
    κ ∘ₘ (chainLaw κ z).map (fun ω => ω n) =
        κ ∘ₘ ((chainLaw κ z).map (frestrictLe n)).map (lastCoord n) := by
      rw [Measure.map_map (measurable_lastCoord n) (measurable_frestrictLe n)]
      rfl
    _ = histKernel κ n ∘ₘ (chainLaw κ z).map (frestrictLe n) := by
      rw [← Measure.deterministic_comp_eq_map (measurable_lastCoord n), Measure.comp_assoc,
        Kernel.comp_deterministic_eq_comap]
      rfl
    _ = (((chainLaw κ z).map (frestrictLe n)) ⊗ₘ histKernel κ n).snd :=
      (Measure.snd_compProd _ _).symm
    _ = (chainLaw κ z).map (fun ω => ω (n + 1)) := by
      rw [chainLaw_history_next, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
      rfl

/-- The law of `Y_1` under `P_z` is `κ z`. -/
lemma chainLaw_marginal_one (z : S) : (chainLaw κ z).map (fun ω => ω 1) = κ z := by
  rw [chainLaw_marginal_succ, chainLaw_marginal_zero]
  exact Measure.dirac_bind κ.measurable z

/-- The chain law as a Markov kernel in the starting point (BouRabeeGwynne `walkPathKernel`,
without the finiteness assumption: measurability comes from `Kernel.comap`). -/
noncomputable def pathKernel : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) (histKernel κ) 0).comap (fun z _ => z)
    (Measurable.of_eval fun _ => measurable_id)

instance pathKernel_isMarkovKernel : IsMarkovKernel (pathKernel κ) := by
  unfold pathKernel
  infer_instance

lemma pathKernel_apply (z : S) : pathKernel κ z = chainLaw κ z := by
  rw [pathKernel, Kernel.comap_apply, chainLaw, Kernel.trajMeasure,
    Measure.map_dirac' (MeasurableEquiv.measurable _), Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- A fresh chain started from the last vertex of a history (BouRabeeGwynne `restartKernel`). -/
noncomputable def restartKernel (a : ℕ) : Kernel (Finset.Iic a → S) (ℕ → S) :=
  (pathKernel κ).comap (lastCoord a) (measurable_lastCoord a)

/-- Each finite future prefix under the continuation kernel has the law of a fresh chain
started at the last vertex of the history (BouRabeeGwynne `continuation_shiftPrefix_law`). -/
lemma continuation_shiftPrefix_law (a : ℕ) (h : Finset.Iic a → S) (k : ℕ) :
    ((Kernel.traj (X := fun _ => S) (histKernel κ) a h).map
      (frestrictLe (a + k))).map (shiftPrefix a k) =
      (chainLaw κ (lastCoord a h)).map (frestrictLe k) := by
  induction k with
  | zero =>
    change ((Kernel.traj (X := fun _ => S) (histKernel κ) a h).map
      (frestrictLe a)).map (shiftPrefix a 0) = _
    rw [prefix_at_start_traj (histKernel κ) a h,
      Measure.map_dirac' (measurable_shiftPrefix a 0),
      chainLaw_initialHistory, shiftPrefix_zero]
  | succ k ih =>
    change ((Kernel.traj (X := fun _ => S) (histKernel κ) a h).map
      (frestrictLe (a + k + 1))).map (shiftPrefix a (k + 1)) = _
    have htarget := prefix_succ (histKernel κ) (Measure.dirac (lastCoord a h)) k
    change (chainLaw κ (lastCoord a h)).map (frestrictLe (k + 1)) = _ at htarget
    have hmap (p : Finset.Iic (a + k) → S) :
        (histKernel κ (a + k) p).map id = histKernel κ k (shiftPrefix a k p) := by
      rw [Measure.map_id]
      rfl
    rw [prefix_succ_traj (histKernel κ) a (a + k) (Nat.le_add_right _ _) h, htarget,
      Measure.map_map (measurable_shiftPrefix a (k + 1)) (measurable_append (a + k)),
      shiftPrefix_append,
      ← Measure.map_map (measurable_append k)
        ((measurable_shiftPrefix a k).prodMap measurable_id),
      compProd_map_prod_of_kernel_map _ _ _ _ _ (measurable_shiftPrefix a k) measurable_id hmap,
      ih]
    rfl

/-- Whole-path restart at a deterministic time under the continuation kernel
(BouRabeeGwynne `continuation_walkShift_law`). -/
theorem continuation_walkShift_law (a : ℕ) (h : Finset.Iic a → S) :
    (Kernel.traj (X := fun _ => S) (histKernel κ) a h).map (walkShift a) =
      chainLaw κ (lastCoord a h) := by
  apply measure_eq_of_prefix_eq
  intro k
  rw [Measure.map_map (measurable_frestrictLe k) (measurable_walkShift a)]
  have heq : frestrictLe (π := fun _ : ℕ => S) k ∘ walkShift a =
      shiftPrefix a k ∘ frestrictLe (π := fun _ : ℕ => S) (a + k) := rfl
  rw [heq, ← Measure.map_map (measurable_shiftPrefix a k) (measurable_frestrictLe (a + k))]
  exact continuation_shiftPrefix_law κ a h k

lemma traj_map_walkShift (a : ℕ) :
    (Kernel.traj (X := fun _ => S) (histKernel κ) a).map (walkShift a) = restartKernel κ a := by
  ext h : 1
  rw [Kernel.map_apply _ (measurable_walkShift a), continuation_walkShift_law, restartKernel,
    Kernel.comap_apply, pathKernel_apply]

/-- The restart identity: `P_z` is the prefix law up to time `a` composed with the
continuation kernel (from mathlib's `Kernel.traj_comp_partialTraj`). -/
lemma chainLaw_eq_traj_comp_prefix (z : S) (a : ℕ) :
    chainLaw κ z =
      Kernel.traj (X := fun _ => S) (histKernel κ) a ∘ₘ (chainLaw κ z).map (frestrictLe a) := by
  simp only [chainLaw, Kernel.trajMeasure]
  rw [Measure.map_comp _ _ (measurable_frestrictLe a), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Kernel.traj_comp_partialTraj (Nat.zero_le a)]

/-- **Markov property at a deterministic time**, path form: under `P_z` the shifted path
`θ_a Y` has the law of a fresh chain started from `Y_a`. -/
theorem chainLaw_map_walkShift (z : S) (a : ℕ) :
    (chainLaw κ z).map (walkShift a) = pathKernel κ ∘ₘ (chainLaw κ z).map (fun ω => ω a) := by
  conv_lhs => rw [chainLaw_eq_traj_comp_prefix κ z a]
  rw [Measure.map_comp _ _ (measurable_walkShift a), traj_map_walkShift, restartKernel,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, Measure.map_map (measurable_lastCoord a)
      (measurable_frestrictLe a)]
  rfl

end Chain

/-! ### Integrals of bounded functions along the chain -/

section Integrals

/-- A bounded a.e.-strongly measurable function is integrable against a finite measure. -/
lemma integrable_of_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  (integrable_const C).mono' hf (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- The integral against a composed measure `η ∘ₘ μ` is the iterated integral
(`Kernel.integral_comp` transported through `Measure.comp_eq_comp_const_apply`). -/
lemma integral_comp_measure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (η : Kernel α β) [IsSFiniteKernel η] {f : β → ℝ}
    (hf : Integrable f (η ∘ₘ μ)) :
    ∫ b, f b ∂(η ∘ₘ μ) = ∫ a, ∫ b, f b ∂η a ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

variable {S : Type*} [MeasurableSpace S] (κ : Kernel S S) [IsMarkovKernel κ]

/-- **Markov property at a deterministic time**, integral form: for bounded measurable `F`,
`E_z[F(θ_a Y)] = E_z[E_{Y_a}[F(Y)]]`. -/
theorem integral_walkShift (z : S) (a : ℕ) {F : (ℕ → S) → ℝ} (hF : Measurable F) (C : ℝ)
    (hC : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F (walkShift a ω) ∂chainLaw κ z =
      ∫ y, (∫ ω, F ω ∂chainLaw κ y) ∂(chainLaw κ z).map (fun ω => ω a) := by
  have : IsProbabilityMeasure ((chainLaw κ z).map (fun ω => ω a)) :=
    ⟨by rw [Measure.map_apply (measurable_pi_apply a) MeasurableSet.univ]; simp⟩
  rw [← integral_map (measurable_walkShift a).aemeasurable hF.aestronglyMeasurable,
    chainLaw_map_walkShift,
    integral_comp_measure _ _ (integrable_of_bounded _ hF.aestronglyMeasurable C hC)]
  simp_rw [pathKernel_apply]

/-- **First-step decomposition** (the Markov property at time `1`): for bounded measurable `F`,
`E_z[F(θ_1 Y)] = ∫ E_y[F(Y)] κ(z, dy)`.  This is the mechanism behind (3.7) and (3.8). -/
theorem integral_walkShift_one (z : S) {F : (ℕ → S) → ℝ} (hF : Measurable F) (C : ℝ)
    (hC : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F (walkShift 1 ω) ∂chainLaw κ z = ∫ y, (∫ ω, F ω ∂chainLaw κ y) ∂κ z := by
  rw [integral_walkShift κ z 1 hF C hC, chainLaw_marginal_one]

/-- Invariance: if `κ` never leaves `B` from inside `B`, then the chain started in `B` stays in
`B` at all times, almost surely. -/
lemma chainLaw_ae_forall_mem {B : Set S} (hB : MeasurableSet B) (hinv : ∀ y ∈ B, κ y Bᶜ = 0)
    {z : S} (hz : z ∈ B) : ∀ᵐ ω ∂chainLaw κ z, ∀ j, ω j ∈ B := by
  rw [ae_all_iff]
  intro j
  induction j with
  | zero =>
    have h : ∀ᵐ y ∂(chainLaw κ z).map (fun ω => ω 0), y ∈ B := by
      rw [chainLaw_marginal_zero]
      exact (ae_dirac_iff hB).mpr hz
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h
  | succ j ih =>
    have hae : ∀ᵐ y ∂(chainLaw κ z).map (fun ω => ω j), κ y Bᶜ = 0 := by
      have h : ∀ᵐ y ∂(chainLaw κ z).map (fun ω => ω j), y ∈ B :=
        (ae_map_iff (measurable_pi_apply j).aemeasurable
          (show MeasurableSet {y : S | y ∈ B} from hB)).mpr ih
      filter_upwards [h] with y hy using hinv y hy
    have hmap : (chainLaw κ z).map (fun ω => ω (j + 1)) Bᶜ = 0 := by
      rw [chainLaw_marginal_succ, Measure.bind_apply hB.compl κ.aemeasurable,
        lintegral_congr_ae hae, lintegral_zero]
    rw [Measure.map_apply (measurable_pi_apply (j + 1)) hB.compl] at hmap
    rw [ae_iff]
    exact hmap

end Integrals

/-! ### Hitting times of the coordinate process -/

section HittingTime

variable {V : Type*}

/-- `τ_A := min {j ≥ 0 : Y_j ∈ A}` (Lemma 3.2), with value `⊤` if `A` is never hit;
mathlib's `hittingAfter` applied to the coordinate process. -/
noncomputable def hitTime (A : Set V) : (ℕ → V) → WithTop ℕ :=
  hittingAfter (fun j (ω : ℕ → V) => ω j) A 0

/-- The index of the hitting time, with junk value `0` when `A` is never hit. -/
noncomputable def hitIndex (A : Set V) (ω : ℕ → V) : ℕ := (hitTime A ω).untopD 0

/-- `Y_{τ_A}`, the vertex of `A` first hit (junk value `Y_0` when `A` is never hit). -/
noncomputable def hitVertex (A : Set V) (ω : ℕ → V) : V := ω (hitIndex A ω)

/-- `Y` has avoided `A` up to and including time `j`, i.e. `τ_A > j`. -/
def survives (A : Set V) (j : ℕ) (ω : ℕ → V) : Prop := ∀ i ≤ j, ω i ∉ A

variable {A : Set V} {ω : ℕ → V}

lemma hitTime_eq_top_iff : hitTime A ω = ⊤ ↔ ∀ j, ω j ∉ A := by
  simp [hitTime, hittingAfter_eq_top_iff]

lemma hitTime_le_iff {n : ℕ} : hitTime A ω ≤ WithTop.some n ↔ ∃ j ≤ n, ω j ∈ A := by
  rw [hitTime, hittingAfter_le_iff]
  simp

lemma notMem_of_lt_hitTime {j : ℕ} (h : WithTop.some j < hitTime A ω) : ω j ∉ A :=
  notMem_of_lt_hittingAfter h (Nat.zero_le j)

/-- `τ_A = n` iff `Y_n ∈ A` and `Y_j ∉ A` for `j < n`. -/
lemma hitTime_eq_coe_iff {n : ℕ} :
    hitTime A ω = WithTop.some n ↔ ω n ∈ A ∧ ∀ j < n, ω j ∉ A := by
  constructor
  · intro h
    refine ⟨?_, fun j hj => notMem_of_lt_hitTime (by rw [h]; exact WithTop.coe_lt_coe.mpr hj)⟩
    obtain ⟨j, hjn, hj⟩ := hitTime_le_iff.mp h.le
    rcases hjn.lt_or_eq with hlt | rfl
    · exact absurd hj (notMem_of_lt_hitTime (by rw [h]; exact WithTop.coe_lt_coe.mpr hlt))
    · exact hj
  · rintro ⟨hn, hlt⟩
    refine le_antisymm (hittingAfter_le_of_mem (Nat.zero_le n) hn)
      (le_of_not_gt fun hlt' => ?_)
    obtain ⟨j, hj, hjA⟩ := hittingAfter_lt_iff.mp hlt'
    exact hlt j hj.2 hjA

lemma hitTime_eq_zero_of_mem (h : ω 0 ∈ A) : hitTime A ω = WithTop.some 0 :=
  hitTime_eq_coe_iff.mpr ⟨h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

lemma hitIndex_eq_of_eq {n : ℕ} (h : hitTime A ω = WithTop.some n) : hitIndex A ω = n := by
  rw [hitIndex, h, WithTop.untopD_coe]

/-- The first vertex hit lies in `A` whenever `A` is hit. -/
lemma hitVertex_mem (h : hitTime A ω ≠ ⊤) : hitVertex A ω ∈ A := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  rw [hitVertex, hitIndex_eq_of_eq hn.symm]
  exact (hitTime_eq_coe_iff.mp hn.symm).1

lemma hitVertex_of_mem_zero (h : ω 0 ∈ A) : hitVertex A ω = ω 0 := by
  rw [hitVertex, hitIndex_eq_of_eq (hitTime_eq_zero_of_mem h)]

/-- When the start is not in `A`: `τ_A = ⊤` iff `τ_A ∘ θ_1 = ⊤`. -/
lemma hitTime_eq_top_iff_walkShift (h0 : ω 0 ∉ A) :
    hitTime A ω = ⊤ ↔ hitTime A (walkShift 1 ω) = ⊤ := by
  simp only [hitTime_eq_top_iff, walkShift_apply]
  constructor
  · intro h j
    exact h (1 + j)
  · intro h j
    cases j with
    | zero => exact h0
    | succ k => rw [Nat.add_comm]; exact h k

/-- When the start is not in `A`: `τ_A = n + 1` iff `τ_A ∘ θ_1 = n`. -/
lemma hitTime_eq_succ_iff_walkShift (h0 : ω 0 ∉ A) {n : ℕ} :
    hitTime A ω = WithTop.some (n + 1) ↔ hitTime A (walkShift 1 ω) = WithTop.some n := by
  simp only [hitTime_eq_coe_iff, walkShift_apply]
  constructor
  · rintro ⟨hn, hlt⟩
    exact ⟨by rw [Nat.add_comm]; exact hn, fun j hj => hlt (1 + j) (by omega)⟩
  · rintro ⟨hn, hlt⟩
    refine ⟨by rw [Nat.add_comm]; exact hn, fun j hj => ?_⟩
    cases j with
    | zero => exact h0
    | succ k => rw [Nat.add_comm]; exact hlt k (by omega)

/-- When the start is not in `A` and `A` is hit, the first vertex hit is the first vertex hit
by the shifted path. -/
lemma hitVertex_walkShift (h0 : ω 0 ∉ A) (h : hitTime A ω ≠ ⊤) :
    hitVertex A ω = hitVertex A (walkShift 1 ω) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  have hn' := hn.symm
  cases n with
  | zero => exact absurd (hitTime_eq_coe_iff.mp hn').1 h0
  | succ m =>
    have hm : hitTime A (walkShift 1 ω) = WithTop.some m :=
      (hitTime_eq_succ_iff_walkShift h0).mp hn'
    rw [hitVertex, hitVertex, hitIndex_eq_of_eq hn', hitIndex_eq_of_eq hm, walkShift_apply,
      Nat.add_comm]

lemma survives_succ_iff {j : ℕ} :
    survives A (j + 1) ω ↔ ω 0 ∉ A ∧ survives A j (walkShift 1 ω) := by
  constructor
  · intro h
    exact ⟨h 0 (Nat.zero_le _), fun i hi => h (1 + i) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ k => rw [Nat.add_comm]; exact h k (by omega)

lemma survives_of_succ {j : ℕ} (h : survives A (j + 1) ω) : survives A j ω :=
  fun i hi => h i (Nat.le_succ_of_le hi)

lemma hitTime_eq_top_iff_survives : hitTime A ω = ⊤ ↔ ∀ j, survives A j ω := by
  rw [hitTime_eq_top_iff]
  exact ⟨fun h j i _ => h i, fun h j => h j j le_rfl⟩

variable [MeasurableSpace V]

/-- The coordinate process is adapted to the canonical filtration `Filtration.piLE`
(BouRabeeGwynne `coordinateProcess_adapted`). -/
lemma coordinateProcess_adapted :
    Adapted (Filtration.piLE (X := fun _ : ℕ => V)) (fun n (ω : ℕ → V) => ω n) := by
  intro n
  exact (measurable_pi_apply (⟨n, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic n)).comp
    (comap_measurable (restrictLe (π := fun _ : ℕ => V) n))

variable [Countable V] [MeasurableSingletonClass V]

/-- The hitting time is a stopping time of the canonical filtration. -/
lemma hitTime_isStoppingTime (A : Set V) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) (hitTime A) :=
  coordinateProcess_adapted.isStoppingTime_hittingAfter MeasurableSet.of_discrete

lemma measurableSet_hitTime_top (A : Set V) :
    MeasurableSet {ω : ℕ → V | hitTime A ω = ⊤} := by
  have : {ω : ℕ → V | hitTime A ω = ⊤} = ⋂ j, (fun ω : ℕ → V => ω j) ⁻¹' Aᶜ := by
    ext ω
    simp [hitTime_eq_top_iff]
  rw [this]
  exact MeasurableSet.iInter fun j => measurable_pi_apply j MeasurableSet.of_discrete

lemma measurableSet_hitTime_coe (A : Set V) (n : ℕ) :
    MeasurableSet {ω : ℕ → V | hitTime A ω = WithTop.some n} := by
  have : {ω : ℕ → V | hitTime A ω = WithTop.some n} =
      (fun ω : ℕ → V => ω n) ⁻¹' A ∩
        ⋂ j, ⋂ (_ : j < n), (fun ω : ℕ → V => ω j) ⁻¹' Aᶜ := by
    ext ω
    show hitTime A ω = WithTop.some n ↔ _
    rw [hitTime_eq_coe_iff]
    simp
  rw [this]
  exact (measurable_pi_apply n MeasurableSet.of_discrete).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurable_pi_apply j MeasurableSet.of_discrete)

lemma measurable_hitTime (A : Set V) : Measurable (hitTime A) := by
  refine measurable_to_countable' fun x => ?_
  induction x using WithTop.recTopCoe with
  | top => exact measurableSet_hitTime_top A
  | coe n => exact measurableSet_hitTime_coe A n

lemma measurable_hitIndex (A : Set V) : Measurable (hitIndex A) :=
  (measurable_hitTime A).untopD 0

lemma measurable_hitVertex (A : Set V) : Measurable (hitVertex A) := by
  have hev : Measurable (fun p : (ℕ → V) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact hev.comp (measurable_id.prodMk (measurable_hitIndex A))

lemma measurableSet_survives (A : Set V) (j : ℕ) :
    MeasurableSet {ω : ℕ → V | survives A j ω} := by
  have : {ω : ℕ → V | survives A j ω} =
      ⋂ i, ⋂ (_ : i ≤ j), (fun ω : ℕ → V => ω i) ⁻¹' Aᶜ := by
    ext ω
    simp [survives]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurable_pi_apply i MeasurableSet.of_discrete

end HittingTime

/-! ### The coarsening (3.9) along a shift of the path -/

section Coarsening

open IndexSet

variable {V : Type*}

open Classical in
/-- One step of (3.9) commutes with shifting the path: `step` from time `j` of `θ_a p` is
`step` from time `a + j` of `p`, shifted back by `a`. -/
lemma step_walkShift (S : Set V) (p : ℕ → V) (a j : ℕ) :
    step S j (walkShift a p) + a = step S (a + j) p := by
  unfold step
  by_cases hj : p (a + j) ∈ S
  · have hj' : walkShift a p j ∈ S := hj
    rw [ite_eq_left hj', ite_eq_left hj]
    omega
  · have hj' : walkShift a p j ∉ S := hj
    rw [ite_eq_right hj', ite_eq_right hj]
    by_cases h' : ∃ i, j < i ∧ walkShift a p i ∈ S
    · have h : ∃ i', a + j < i' ∧ p i' ∈ S := by
        obtain ⟨i, hi, hiS⟩ := h'
        exact ⟨a + i, by omega, hiS⟩
      rw [find_next_of_exists h', find_next_of_exists h]
      symm
      rw [Nat.find_eq_iff]
      refine ⟨⟨by have := (Nat.find_spec h').1; omega, ?_⟩, fun n hn hPn => ?_⟩
      · have := (Nat.find_spec h').2
        rw [walkShift_apply, Nat.add_comm] at this
        exact this
      · obtain ⟨hn1, hn2⟩ := hPn
        have hlt : n - a < Nat.find h' := by omega
        refine Nat.find_min h' hlt ⟨by omega, ?_⟩
        show p (a + (n - a)) ∈ S
        rwa [Nat.add_sub_cancel' (by omega : a ≤ n)]
    · have h : ¬ ∃ i', a + j < i' ∧ p i' ∈ S := by
        rintro ⟨i', hi', hiS⟩
        refine h' ⟨i' - a, by omega, ?_⟩
        show p (a + (i' - a)) ∈ S
        rwa [Nat.add_sub_cancel' (by omega : a ≤ i')]
      rw [find_next_of_not_exists h', find_next_of_not_exists h]
      omega

/-- The coarsening times after the first one are the coarsening times of the path shifted by
`J₁`: `J_{k+1}(p) = J₁(p) + J_k(θ_{J₁(p)} p)`. -/
lemma coarsen_succ_eq_add (S : Set V) (p : ℕ → V) (k : ℕ) :
    coarsen S p (k + 1) = coarsen S p 1 + coarsen S (walkShift (coarsen S p 1) p) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [coarsen_succ_eq_step, ih, ← step_walkShift, ← coarsen_succ_eq_step, Nat.add_comm]

/-- The coarsened path after its first step is the coarsening of the path shifted by `J₁`. -/
lemma coarsenPath_succ (S : Set V) (p : ℕ → V) (k : ℕ) :
    coarsenPath S p (k + 1) = coarsenPath S (walkShift (coarsen S p 1) p) k := by
  show p (coarsen S p (k + 1)) = walkShift (coarsen S p 1) p (coarsen S (walkShift (coarsen S p 1) p) k)
  rw [coarsen_succ_eq_add S p k]
  rfl

/-- (3.9), first case at time `0`: `J₁ = 1` when the path starts in `S`. -/
lemma coarsen_one_of_mem (S : Set V) (p : ℕ → V) (h : p 0 ∈ S) : coarsen S p 1 = 1 := by
  have := coarsen_succ_of_mem S p (k := 0) (by simpa using h)
  simpa using this

open Classical in
/-- (3.9), second case at time `0`: `J₁ = τ_S` when the path starts outside `S` and hits `S`. -/
lemma coarsen_one_of_not_mem (S : Set V) (p : ℕ → V) (h0 : p 0 ∉ S) (hne : hitTime S p ≠ ⊤) :
    coarsen S p 1 = hitIndex S p := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  have hn' := hn.symm
  obtain ⟨hnS, hlt⟩ := hitTime_eq_coe_iff.mp hn'
  have hpos : 0 < n := Nat.pos_of_ne_zero fun h => h0 (h ▸ hnS)
  have h1 : coarsen S p 1 = step S 0 p := coarsen_succ_eq_step S p 0
  rw [hitIndex_eq_of_eq hn', h1, step, ite_eq_right h0]
  have hex : ∃ j, 0 < j ∧ p j ∈ S := ⟨n, hpos, hnS⟩
  rw [find_next_of_exists hex, Nat.find_eq_iff]
  exact ⟨⟨hpos, hnS⟩, fun m hm hP => hlt m hm hP.2⟩

end Coarsening

/-! ### Survival probabilities and the limiting survival probability -/

section Survival

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  (κ : Kernel V V) [IsMarkovKernel κ] (A : Set V)

/-- The survival probability `P_x(τ_A > j)`. -/
noncomputable def survProb (j : ℕ) (x : V) : ℝ := (chainLaw κ x {ω | survives A j ω}).toReal

lemma survProb_eq_integral (j : ℕ) (x : V) :
    survProb κ A j x = ∫ ω, {ω : ℕ → V | survives A j ω}.indicator 1 ω ∂chainLaw κ x := by
  rw [integral_indicator_one (measurableSet_survives A j), measureReal_def, survProb]

omit [Countable V] [MeasurableSingletonClass V] in
lemma survProb_nonneg (j : ℕ) (x : V) : 0 ≤ survProb κ A j x := ENNReal.toReal_nonneg

omit [Countable V] [MeasurableSingletonClass V] in
lemma survProb_le_one (j : ℕ) (x : V) : survProb κ A j x ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

omit [Countable V] in
lemma survProb_of_mem {x : V} (hx : x ∈ A) (j : ℕ) : survProb κ A j x = 0 := by
  have h : ∀ᵐ ω ∂chainLaw κ x, ¬ survives A j ω := by
    filter_upwards [chainLaw_ae_start κ x] with ω h0 hs
    exact hs 0 (Nat.zero_le _) (by rw [h0]; exact hx)
  have h' := ae_iff.mp h
  simp only [not_not] at h'
  rw [survProb, h', ENNReal.toReal_zero]

/-- The first-step recursion `P_x(τ_A > j + 1) = ∫ P_y(τ_A > j) κ(x, dy)` for `x ∉ A`. -/
lemma survProb_succ {x : V} (hx : x ∉ A) (j : ℕ) :
    survProb κ A (j + 1) x = ∫ y, survProb κ A j y ∂κ x := by
  simp_rw [survProb_eq_integral]
  have hF : Measurable ({ω : ℕ → V | survives A j ω}.indicator (1 : (ℕ → V) → ℝ)) :=
    measurable_one.indicator (measurableSet_survives A j)
  have hC : ∀ ω, |{ω : ℕ → V | survives A j ω}.indicator (1 : (ℕ → V) → ℝ) ω| ≤ 1 := by
    intro ω
    by_cases h : survives A j ω <;> simp [Set.indicator, h]
  rw [← integral_walkShift_one κ x hF 1 hC]
  refine integral_congr_ae ?_
  filter_upwards [chainLaw_ae_start κ x] with ω h0
  have h0A : ω 0 ∉ A := by rw [h0]; exact hx
  by_cases hs : survives A j (walkShift 1 ω)
  · have : survives A (j + 1) ω := survives_succ_iff.mpr ⟨h0A, hs⟩
    simp [Set.indicator, this, hs]
  · have : ¬ survives A (j + 1) ω := fun h => hs (survives_succ_iff.mp h).2
    simp [Set.indicator, this, hs]

omit [Countable V] [MeasurableSingletonClass V] in
lemma survProb_antitone (x : V) : Antitone (fun j => survProb κ A j x) :=
  antitone_nat_of_succ_le fun _ => ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun _ h => survives_of_succ h)

/-- `P_x(τ_A = ∞)` as the decreasing limit of the survival probabilities. -/
noncomputable def survLim (x : V) : ℝ := ⨅ j, survProb κ A j x

omit [Countable V] [MeasurableSingletonClass V] in
lemma bddBelow_survProb (x : V) : BddBelow (Set.range fun j => survProb κ A j x) :=
  ⟨0, by rintro _ ⟨j, rfl⟩; exact survProb_nonneg κ A j x⟩

omit [Countable V] [MeasurableSingletonClass V] in
lemma survProb_tendsto (x : V) :
    Tendsto (fun j => survProb κ A j x) atTop (𝓝 (survLim κ A x)) :=
  tendsto_atTop_ciInf (survProb_antitone κ A x) (bddBelow_survProb κ A x)

omit [Countable V] [MeasurableSingletonClass V] in
lemma survLim_nonneg (x : V) : 0 ≤ survLim κ A x :=
  le_ciInf fun j => survProb_nonneg κ A j x

omit [Countable V] [MeasurableSingletonClass V] in
lemma survLim_le_one (x : V) : survLim κ A x ≤ 1 :=
  (ciInf_le (bddBelow_survProb κ A x) 0).trans (survProb_le_one κ A 0 x)

omit [Countable V] in
lemma survLim_of_mem {x : V} (hx : x ∈ A) : survLim κ A x = 0 := by
  simp [survLim, survProb_of_mem κ A hx]

/-- The limiting survival probability satisfies the mean-value equation off `A`
(dominated convergence in the first-step recursion). -/
lemma survLim_mean {x : V} (hx : x ∉ A) : survLim κ A x = ∫ y, survLim κ A y ∂κ x := by
  have h1 : Tendsto (fun j => survProb κ A (j + 1) x) atTop (𝓝 (survLim κ A x)) :=
    (survProb_tendsto κ A x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun j => ∫ y, survProb κ A j y ∂κ x) atTop
      (𝓝 (∫ y, survLim κ A y ∂κ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun j => (measurable_of_countable _).aestronglyMeasurable) (integrable_const 1)
      (fun j => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => survProb_tendsto κ A y)
    rw [Real.norm_eq_abs, abs_of_nonneg (survProb_nonneg κ A j y)]
    exact survProb_le_one κ A j y
  have h3 : (fun j => survProb κ A (j + 1) x) = fun j => ∫ y, survProb κ A j y ∂κ x :=
    funext fun j => survProb_succ κ A hx j
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

end Survival

/-! ### The maximum principle on a finite set -/

section MaxPrinciple

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  (κ : Kernel V V) [IsMarkovKernel κ]

/-- Structural hypotheses on a one-step kernel `κ` relative to a finite vertex set `S` and a
graph `Γ`: the graph induced on `S` is connected, from outside `S` the kernel jumps into `S`,
and adjacent vertices of `S` communicate in one step.  Both the kernel (3.2)–(3.3) of `Yⁿ`
and the kernel (3.4) of `Ỹⁿ` satisfy this with `S = VGₙ` (Remark 3.1). -/
structure StepsOn (Γ : SimpleGraph V) (S : Finset V) : Prop where
  connected : (Γ.induce (↑S : Set V)).Connected
  supp : ∀ x ∉ S, κ x (↑S : Set V)ᶜ = 0
  adj_pos : ∀ x ∈ S, ∀ y ∈ S, Γ.Adj x y → 0 < κ x {y}

variable {κ} {Γ : SimpleGraph V} {S A : Finset V}

/-- Maximum principle, one-sided version: a bounded function with the mean-value property
off `A ⊆ S` which vanishes on `A` is `≤ 0` everywhere (the paper's argument at the end of the
proof of Lemma 3.2: `g` attains its maximum over the finite set `VGₙ` at a point of `A`). -/
lemma le_zero_of_mean_value (hst : StepsOn κ Γ S) (hAS : A ⊆ S) (hA : A.Nonempty)
    {g : V → ℝ} (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (hmean : ∀ x ∉ A, g x = ∫ y, g y ∂κ x) (hzero : ∀ a ∈ A, g a = 0) : ∀ x, g x ≤ 0 := by
  have hS : S.Nonempty := hA.mono hAS
  set M := S.sup' hS g with hM
  have hint : ∀ x, Integrable g (κ x) := fun x =>
    integrable_of_bounded _ (measurable_of_countable _).aestronglyMeasurable C hC
  -- `g ≤ M` everywhere, using the support property outside `S`
  have hle : ∀ y, g y ≤ M := by
    intro y
    by_cases hy : y ∈ S
    · exact Finset.le_sup' g hy
    · have hyA : y ∉ A := fun h => hy (hAS h)
      rw [hmean y hyA]
      have hae : ∀ᵐ w ∂κ y, g w ≤ M := by
        have h0 : ∀ᵐ w ∂κ y, w ∈ (↑S : Set V) := by
          rw [ae_iff]
          exact hst.supp y hy
        filter_upwards [h0] with w hw
        exact Finset.le_sup' g (Finset.mem_coe.mp hw)
      calc ∫ w, g w ∂κ y ≤ ∫ _, M ∂κ y := integral_mono_ae (hint y) (integrable_const M) hae
        _ = M := by simp
  -- the set where the maximum is attained is closed under adjacency inside `S ∖ A`
  have hstep : ∀ x ∈ S, x ∉ A → g x = M → ∀ y ∈ S, Γ.Adj x y → g y = M := by
    intro x hxS hxA hgx y hyS hxy
    have h1 : ∫ w, (M - g w) ∂κ x = 0 := by
      rw [integral_sub (integrable_const M) (hint x), ← hmean x hxA, hgx]
      simp
    have h2 : ∀ᵐ w ∂κ x, g w = M := by
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all _ fun w => sub_nonneg.mpr (hle w)) ((integrable_const M).sub (hint x))).mp h1]
        with w hw
      simp only [Pi.zero_apply] at hw
      linarith
    by_contra hne
    have hsub : ({y} : Set V) ⊆ {w | ¬ g w = M} := by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hne
    exact (hst.adj_pos x hxS y hyS hxy).ne' (measure_mono_null hsub (ae_iff.mp h2))
  -- walk from a maximizer to `A` inside `S`
  have hwalk : ∀ (u v : ↥(↑S : Set V)), (Γ.induce (↑S : Set V)).Walk u v →
      g u = M → g v = M ∨ M = 0 := by
    intro u v w
    induction w with
    | nil => exact fun h => Or.inl h
    | @cons u w v hadj p ih =>
      intro hu
      by_cases huA : u.1 ∈ A
      · exact Or.inr (by rw [← hu, hzero _ huA])
      · exact ih (hstep u.1 (Finset.mem_coe.mp u.2) huA hu w.1 (Finset.mem_coe.mp w.2)
          (SimpleGraph.induce_adj.mp hadj))
  obtain ⟨x₀, hx₀S, hx₀⟩ := Finset.exists_mem_eq_sup' hS g
  obtain ⟨a, ha⟩ := hA
  obtain ⟨w⟩ := hst.connected.preconnected ⟨x₀, Finset.mem_coe.mpr hx₀S⟩
    ⟨a, Finset.mem_coe.mpr (hAS ha)⟩
  have hM0 : M = 0 := by
    rcases hwalk _ _ w hx₀.symm with h | h
    · rw [← h]
      exact hzero a ha
    · exact h
  intro x
  rw [← hM0]
  exact hle x

/-- **Maximum principle.**  A bounded function with the mean-value property
`g(x) = ∫ g dκ(x,·)` off `A ⊆ S` which vanishes on `A` vanishes identically. -/
theorem eq_zero_of_mean_value (hst : StepsOn κ Γ S) (hAS : A ⊆ S) (hA : A.Nonempty)
    {g : V → ℝ} (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (hmean : ∀ x ∉ A, g x = ∫ y, g y ∂κ x) (hzero : ∀ a ∈ A, g a = 0) : ∀ x, g x = 0 := by
  intro x
  refine le_antisymm (le_zero_of_mean_value hst hAS hA C hC hmean hzero x) ?_
  have hneg := le_zero_of_mean_value hst hAS hA (g := -g) C (fun x => by simpa using hC x)
    (fun x hx => by
      simp only [Pi.neg_apply, integral_neg]
      exact congrArg Neg.neg (hmean x hx))
    (fun a ha => by simp [hzero a ha]) x
  simpa using hneg

/-! ### Recurrence -/

/-- The chain hits every non-empty `A ⊆ S` almost surely: `P_x(τ_A = ∞) = 0` by the maximum
principle applied to the limiting survival probability (Remark 3.1). -/
theorem survLim_eq_zero (hst : StepsOn κ Γ S) (hAS : A ⊆ S) (hA : A.Nonempty) (x : V) :
    survLim κ (↑A : Set V) x = 0 :=
  eq_zero_of_mean_value hst hAS hA 1
    (fun y => by
      rw [abs_of_nonneg (survLim_nonneg κ _ y)]
      exact survLim_le_one κ _ y)
    (fun y hy => survLim_mean κ (↑A : Set V) fun h => hy (Finset.mem_coe.mp h))
    (fun a ha => survLim_of_mem κ (↑A : Set V) (Finset.mem_coe.mpr ha)) x

/-- For a non-empty finite `A ⊆ S`, the hitting time `τ_A` is almost surely finite from every
starting point (the paper's "`τₙ < ∞` a.s. since `Yⁿ` is recurrent", Lemma 3.2; here proved
directly by the maximum principle applied to the limiting survival probability). -/
theorem hitTime_ae_ne_top (hst : StepsOn κ Γ S) (hAS : A ⊆ S) (hA : A.Nonempty) (x : V) :
    ∀ᵐ ω ∂chainLaw κ x, hitTime (↑A : Set V) ω ≠ ⊤ := by
  have hzero := survLim_eq_zero hst hAS hA x
  have hle : ∀ j, (chainLaw κ x {ω | hitTime (↑A : Set V) ω = ⊤}).toReal ≤
      survProb κ (↑A : Set V) j x := fun j =>
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun ω hω => (hitTime_eq_top_iff_survives.mp hω) j)
  have h0 : (chainLaw κ x {ω | hitTime (↑A : Set V) ω = ⊤}).toReal ≤ 0 :=
    (le_ciInf hle).trans_eq hzero
  have hmeas : chainLaw κ x {ω | hitTime (↑A : Set V) ω = ⊤} = 0 := by
    have h := le_antisymm h0 ENNReal.toReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  simpa using hmeas

/-! ### Irreducibility -/

omit [Countable V] [IsMarkovKernel κ] in
/-- One step followed by `n` steps: `κ^{n+1}(a, {c}) > 0` whenever `κ(a, {b}) > 0` and
`κ^n(b, {c}) > 0` (Chapman–Kolmogorov). -/
lemma pow_succ_singleton_pos {a b c : V} {n : ℕ} (hab : 0 < κ a {b})
    (hbc : 0 < (κ ^ n) b {c}) : 0 < (κ ^ (n + 1)) a {c} := by
  rw [Nat.add_comm, Kernel.pow_add_apply_eq_lintegral κ 1 n a (measurableSet_singleton c),
    pow_one]
  refine lt_of_lt_of_le ?_ (setLIntegral_le_lintegral {b} _)
  rw [lintegral_singleton]
  exact ENNReal.mul_pos hbc.ne' hab.ne'

omit [Countable V] [IsMarkovKernel κ] in
/-- Along a walk of the graph induced on `S` whose steps all have positive one-step
probability, the endpoint is reached with positive probability in as many steps. -/
lemma exists_pow_singleton_pos_of_walk {Γ : SimpleGraph V} {S : Finset V}
    (hadj : ∀ x ∈ S, ∀ y ∈ S, Γ.Adj x y → 0 < κ x {y}) :
    ∀ (u v : ↥(↑S : Set V)), (Γ.induce (↑S : Set V)).Walk u v →
      ∃ n, 0 < (κ ^ n) u.1 {v.1} := by
  intro u v w
  induction w with
  | nil =>
    refine ⟨0, ?_⟩
    rw [pow_zero]
    show 0 < Kernel.id _ {_}
    rw [Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _)]
    exact zero_lt_one
  | @cons u w v hadj' p ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, pow_succ_singleton_pos (hadj u.1 (Finset.mem_coe.mp u.2) w.1
      (Finset.mem_coe.mp w.2) (SimpleGraph.induce_adj.mp hadj')) hn⟩

/-- From every starting point, every vertex of `S` is reached with positive probability in
finitely many steps: from `a ∈ S` along a walk of the connected graph induced on `S`, from
`a ∉ S` after first jumping into `S`. -/
lemma exists_pow_singleton_pos (hst : StepsOn κ Γ S) (a : V) {y : V} (hy : y ∈ S) :
    ∃ n, 0 < (κ ^ n) a {y} := by
  by_cases ha : a ∈ S
  · obtain ⟨w⟩ := hst.connected.preconnected ⟨a, Finset.mem_coe.mpr ha⟩
      ⟨y, Finset.mem_coe.mpr hy⟩
    exact exists_pow_singleton_pos_of_walk hst.adj_pos _ _ w
  · have hS1 : κ a (↑S : Set V) = 1 := by
      have h := measure_add_measure_compl (μ := κ a) (MeasurableSet.of_discrete (s := (↑S : Set V)))
      rwa [hst.supp a ha, add_zero, measure_univ] at h
    obtain ⟨y', hy'S, hy'⟩ : ∃ y' ∈ S, κ a {y'} ≠ 0 := by
      by_contra h
      have h' : ∀ y' ∈ S, κ a {y'} = 0 := fun y' hy' => by_contra fun hne => h ⟨y', hy', hne⟩
      have hsum : ∑ y' ∈ S, κ a {y'} = 0 := Finset.sum_eq_zero h'
      rw [sum_measure_singleton, hS1] at hsum
      exact one_ne_zero hsum
    obtain ⟨w⟩ := hst.connected.preconnected ⟨y', Finset.mem_coe.mpr hy'S⟩
      ⟨y, Finset.mem_coe.mpr hy⟩
    obtain ⟨n, hn⟩ := exists_pow_singleton_pos_of_walk hst.adj_pos _ _ w
    exact ⟨n + 1, pow_succ_singleton_pos (pos_iff_ne_zero.mpr hy') hn⟩

/-- **Irreducibility**, in mathlib's sense: a kernel satisfying `StepsOn κ Γ S` is
`φ`-irreducible for `φ` the counting measure on the finite set `S`, i.e. every set charged by
`φ` (every set meeting `S`) is reached from every state with positive probability in finitely
many steps.  Applied to the kernel (3.4) this is the irreducibility of `Ỹⁿ` on the finite state
space `VGₙ` asserted in Remark 3.1. -/
theorem isIrreducible_of_stepsOn (hst : StepsOn κ Γ S) :
    Kernel.IsIrreducible (Measure.count.restrict (↑S : Set V)) κ where
  irreducible A hA hφA a := by
    have hne : (A ∩ (↑S : Set V)).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [Measure.restrict_apply hA, h, measure_empty] at hφA
      exact lt_irrefl _ hφA
    obtain ⟨y, hyA, hyS⟩ := hne
    obtain ⟨n, hn⟩ := exists_pow_singleton_pos hst a (Finset.mem_coe.mp hyS)
    exact ⟨n, lt_of_lt_of_le hn (measure_mono (Set.singleton_subset_iff.mpr hyA))⟩

end MaxPrinciple

/-! ### The strong Markov property at a hitting time, in shift form -/

section StrongMarkovHitting

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  (κ : Kernel V V) [IsMarkovKernel κ]

/-- A kernel whose rows are concentrated on the fibres of `f` commutes with restriction to
`f`-cylinder events: `(η ∘ₘ ν)|_{f⁻¹ s} = η ∘ₘ (ν|_s)`. -/
lemma comp_restrict_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (η : Kernel α β) {f : β → α} (hf : Measurable f)
    (hη : ∀ a, η a (f ⁻¹' {a})ᶜ = 0) {s : Set α} (hs : MeasurableSet s) :
    (η ∘ₘ ν).restrict (f ⁻¹' s) = η ∘ₘ ν.restrict s := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.bind_apply (ht.inter (hf hs)) η.aemeasurable,
    Measure.bind_apply ht η.aemeasurable, ← lintegral_indicator hs]
  refine lintegral_congr fun a => ?_
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha]
    refine measure_inter_conull (measure_mono_null ?_ (hη a))
    exact Set.compl_subset_compl.mpr (Set.preimage_mono (Set.singleton_subset_iff.mpr ha))
  · rw [Set.indicator_of_notMem ha]
    refine measure_mono_null ?_ (hη a)
    intro b hb hb'
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hb'
    exact ha (hb' ▸ hb.2)

omit [Countable V] in
/-- The continuation kernel started from the history `h` is concentrated on paths with
prefix `h`. -/
lemma traj_fiber_compl (j : ℕ) (h : Finset.Iic j → V) :
    Kernel.traj (X := fun _ => V) (histKernel κ) j h (frestrictLe j ⁻¹' {h})ᶜ = 0 := by
  rw [← Set.preimage_compl,
    ← Measure.map_apply (measurable_frestrictLe j) (measurableSet_singleton h).compl,
    prefix_at_start_traj, Measure.dirac_apply' _ (measurableSet_singleton h).compl]
  simp

omit [Countable V] in
/-- The Markov property at a deterministic time `j`, restricted to a cylinder event
`frestrictLe j ⁻¹' s` of the history up to time `j`. -/
lemma chainLaw_restrict_map_walkShift (z : V) (j : ℕ) {s : Set (Finset.Iic j → V)}
    (hs : MeasurableSet s) :
    ((chainLaw κ z).restrict (frestrictLe j ⁻¹' s)).map (walkShift j) =
      pathKernel κ ∘ₘ ((chainLaw κ z).restrict (frestrictLe j ⁻¹' s)).map (fun ω => ω j) := by
  have hres : (chainLaw κ z).restrict (frestrictLe j ⁻¹' s) =
      Kernel.traj (X := fun _ => V) (histKernel κ) j ∘ₘ
        ((chainLaw κ z).map (frestrictLe j)).restrict s := by
    conv_lhs => rw [chainLaw_eq_traj_comp_prefix κ z j]
    exact comp_restrict_preimage _ _ (measurable_frestrictLe j) (traj_fiber_compl κ j) hs
  conv_lhs => rw [hres]
  rw [Measure.map_comp _ _ (measurable_walkShift j), traj_map_walkShift, restartKernel,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, Measure.restrict_map (measurable_frestrictLe j) hs,
    Measure.map_map (measurable_lastCoord j) (measurable_frestrictLe j)]
  rfl

omit [Countable V] [MeasurableSingletonClass V] in
/-- The event `{τ = j}` of a stopping time is a cylinder event of the history up to time `j`
(BouRabeeGwynne `stopping_event_prefix`). -/
lemma stopping_event_prefix {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ) (n : ℕ) :
    ∃ s : Set (Finset.Iic n → V), MeasurableSet s ∧
      frestrictLe n ⁻¹' s = {ω | τ ω = WithTop.some n} := by
  have hm := hτ.measurableSet_eq n
  rw [Filtration.piLE_eq_comap_frestrictLe] at hm
  exact hm

/-- **Strong Markov property at the hitting time `τ_A`**, shift form: if `τ_A < ∞` a.s.
under `P_z`, then the path shifted by `τ_A` has the law of a fresh chain started from
`Y_{τ_A}`.  Proved by slicing along `{τ_A = j}` and applying the deterministic-time Markov
property on each slice (the architecture of BouRabeeGwynne `trajectoryLaw_observed_future`). -/
theorem chainLaw_map_walkShift_hitIndex (z : V) (A : Set V)
    (hfin : ∀ᵐ ω ∂chainLaw κ z, hitTime A ω ≠ ⊤) :
    (chainLaw κ z).map (fun ω => walkShift (hitIndex A ω) ω) =
      pathKernel κ ∘ₘ (chainLaw κ z).map (hitVertex A) := by
  let T : ℕ → Set (ℕ → V) := fun j => {ω | hitTime A ω = WithTop.some j}
  have hT : ∀ j, MeasurableSet (T j) := fun j => measurableSet_hitTime_coe A j
  have hdisj : Pairwise fun i j => Disjoint (T i) (T j) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
    exact WithTop.coe_injective (hi.symm.trans hj)
  have hcover : ∀ᵐ ω ∂chainLaw κ z, ω ∈ ⋃ j, T j := by
    filter_upwards [hfin] with ω hω
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hω
    exact Set.mem_iUnion.mpr ⟨j, hj.symm⟩
  have hμ : chainLaw κ z = Measure.sum fun j => (chainLaw κ z).restrict (T j) := by
    rw [← Measure.restrict_iUnion hdisj hT, Measure.restrict_eq_self_of_ae_mem hcover]
  have hF : Measurable (fun ω : ℕ → V => walkShift (hitIndex A ω) ω) := by
    have h1 : Measurable (fun q : (ℕ → V) × ℕ => walkShift q.2 q.1) :=
      measurable_from_prod_countable_left fun j => measurable_walkShift j
    exact h1.comp (measurable_id.prodMk (measurable_hitIndex A))
  have hslice : ∀ j, ((chainLaw κ z).restrict (T j)).map (fun ω => walkShift (hitIndex A ω) ω) =
      pathKernel κ ∘ₘ ((chainLaw κ z).restrict (T j)).map (hitVertex A) := by
    intro j
    have hae : ∀ᵐ ω ∂(chainLaw κ z).restrict (T j), hitIndex A ω = j := by
      filter_upwards [ae_restrict_mem (hT j)] with ω hω
      exact hitIndex_eq_of_eq hω
    have h1 : ((chainLaw κ z).restrict (T j)).map (fun ω => walkShift (hitIndex A ω) ω) =
        ((chainLaw κ z).restrict (T j)).map (walkShift j) := by
      apply Measure.map_congr
      filter_upwards [hae] with ω hω
      rw [hω]
    have h2 : ((chainLaw κ z).restrict (T j)).map (hitVertex A) =
        ((chainLaw κ z).restrict (T j)).map (fun ω => ω j) := by
      apply Measure.map_congr
      filter_upwards [hae] with ω hω
      show ω (hitIndex A ω) = ω j
      rw [hω]
    obtain ⟨s, hs, hseq⟩ := stopping_event_prefix (hitTime_isStoppingTime A) j
    have hTj : T j = frestrictLe j ⁻¹' s := hseq.symm
    rw [h1, h2, hTj]
    exact chainLaw_restrict_map_walkShift κ z j hs
  calc (chainLaw κ z).map (fun ω => walkShift (hitIndex A ω) ω)
      = (Measure.sum fun j => (chainLaw κ z).restrict (T j)).map
          (fun ω => walkShift (hitIndex A ω) ω) := by rw [← hμ]
    _ = Measure.sum fun j => ((chainLaw κ z).restrict (T j)).map
          (fun ω => walkShift (hitIndex A ω) ω) := Measure.map_sum hF.aemeasurable
    _ = Measure.sum fun j => pathKernel κ ∘ₘ ((chainLaw κ z).restrict (T j)).map (hitVertex A) := by
        congr 1
        funext j
        exact hslice j
    _ = pathKernel κ ∘ₘ Measure.sum fun j => ((chainLaw κ z).restrict (T j)).map (hitVertex A) :=
        (Measure.bind_sum _ _ (pathKernel κ).aemeasurable).symm
    _ = pathKernel κ ∘ₘ (Measure.sum fun j => (chainLaw κ z).restrict (T j)).map (hitVertex A) := by
        rw [Measure.map_sum (measurable_hitVertex A).aemeasurable]
    _ = pathKernel κ ∘ₘ (chainLaw κ z).map (hitVertex A) := by rw [← hμ]

end StrongMarkovHitting

/-! ### Prepending a state to a path -/

section ConsPath

variable {S : Type*}

/-- Prepend a state to a path: `consPath z q = (z, q 0, q 1, …)`. -/
def consPath (z : S) (q : ℕ → S) : ℕ → S
  | 0 => z
  | k + 1 => q k

@[simp] lemma consPath_zero (z : S) (q : ℕ → S) : consPath z q 0 = z := rfl

@[simp] lemma consPath_succ (z : S) (q : ℕ → S) (k : ℕ) : consPath z q (k + 1) = q k := rfl

lemma consPath_walkShift (p : ℕ → S) : consPath (p 0) (walkShift 1 p) = p := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show p (1 + k) = p (k + 1)
    rw [Nat.add_comm]

/-- Prepend a state to a finite history. -/
def consPrefix (z : S) (k : ℕ) (h : Finset.Iic k → S) : Finset.Iic (k + 1) → S :=
  fun i => if hi : i.val = 0 then z else
    h ⟨i.val - 1, Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp i.property; omega)⟩

lemma frestrictLe_succ_consPath (z : S) (k : ℕ) (q : ℕ → S) :
    frestrictLe (k + 1) (consPath z q) = consPrefix z k (frestrictLe k q) := by
  funext ⟨i, hi⟩
  cases i with
  | zero => simp [consPrefix, frestrictLe_apply]
  | succ m => simp [consPrefix, frestrictLe_apply]

variable [MeasurableSpace S]

lemma measurable_consPath (z : S) : Measurable (consPath z) := by
  refine Measurable.of_eval fun k => ?_
  cases k with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

lemma measurable_consPrefix (z : S) (k : ℕ) : Measurable (consPrefix z k) := by
  refine Measurable.of_eval fun i => ?_
  by_cases hi : i.val = 0
  · simp only [consPrefix, hi, ↓reduceDIte]
    exact measurable_const
  · simp only [consPrefix, hi, ↓reduceDIte]
    exact measurable_pi_apply _

variable (κ : Kernel S S) [IsMarkovKernel κ] [MeasurableSingletonClass S]

/-- The chain law as the law of `(z, θ_1 Y)`: `P_z = (pathKernel ∘ₘ κ z).map (consPath z)`. -/
lemma chainLaw_eq_map_consPath (z : S) :
    chainLaw κ z = (pathKernel κ ∘ₘ κ z).map (consPath z) := by
  have h1 : chainLaw κ z = (chainLaw κ z).map (consPath z ∘ walkShift 1) := by
    conv_lhs => rw [← Measure.map_id (μ := chainLaw κ z)]
    apply Measure.map_congr
    filter_upwards [chainLaw_ae_start κ z] with p hp
    show p = consPath z (walkShift 1 p)
    rw [← hp, consPath_walkShift]
  rw [h1, ← Measure.map_map (measurable_consPath z) (measurable_walkShift 1),
    chainLaw_map_walkShift, chainLaw_marginal_one]

end ConsPath

/-! ### Markov kernels from transition matrices -/

section KernelOfProb

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- A transition matrix on `V`: nonnegative rows, each summable with sum `1`. -/
structure IsTransProb (p : V → V → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ p x y
  summable : ∀ x, Summable (p x)
  tsum_eq_one : ∀ x, ∑' y, p x y = 1

namespace IsTransProb

variable {p : V → V → ℝ} (hp : IsTransProb p)

/-- The row `p(x, ·)` as a probability mass function on `V`. -/
noncomputable def pmf (x : V) : PMF V :=
  ⟨fun y => ENNReal.ofReal (p x y), by
    have h := ENNReal.ofReal_tsum_of_nonneg (hp.nonneg x) (hp.summable x)
    rw [hp.tsum_eq_one x, ENNReal.ofReal_one] at h
    rw [h]
    exact ENNReal.summable.hasSum⟩

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
lemma pmf_apply (x y : V) : hp.pmf x y = ENNReal.ofReal (p x y) := rfl

/-- The Markov kernel on `V` with transition matrix `p`. -/
noncomputable def kernel : Kernel V V where
  toFun x := (hp.pmf x).toMeasure
  measurable' := measurable_of_countable _

instance kernel_isMarkovKernel : IsMarkovKernel hp.kernel :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

lemma kernel_apply (x : V) : hp.kernel x = (hp.pmf x).toMeasure := rfl

lemma kernel_singleton (x y : V) : hp.kernel x {y} = ENNReal.ofReal (p x y) :=
  PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)

lemma kernel_apply_eq_zero {x : V} {s : Set V} (h : ∀ y ∈ s, p x y = 0) : hp.kernel x s = 0 := by
  rw [kernel_apply, PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete]
  refine Set.disjoint_left.mpr fun y hy hys => ?_
  rw [PMF.mem_support_iff, pmf_apply, h y hys, ENNReal.ofReal_zero] at hy
  exact hy rfl

lemma kernel_singleton_pos {x y : V} (h : 0 < p x y) : 0 < hp.kernel x {y} := by
  rw [kernel_singleton]
  exact ENNReal.ofReal_pos.mpr h

/-- Integrals against the kernel are `∑_y p(x,y) f(y)`. -/
lemma integral_kernel (x : V) {f : V → ℝ} (hf : Integrable f (hp.kernel x)) :
    ∫ y, f y ∂hp.kernel x = ∑' y, p x y * f y := by
  rw [kernel_apply, PMF.integral_eq_tsum _ _ hf]
  refine tsum_congr fun y => ?_
  rw [pmf_apply, ENNReal.toReal_ofReal (hp.nonneg x y), smul_eq_mul]

end IsTransProb

end KernelOfProb

end MarkovChain

namespace ConductanceGraph

open MarkovChain
open Classical

section Defs

variable {V : Type*} (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected)

/-! ### (3.1): the radius-one neighbourhood `B₁Gₙ` -/

/-- (3.1): `B₁Gₙ = {x ∈ VG : x ∈ VGₙ or x ∼ y for some y ∈ VGₙ}`, for the vertex set
`S = VGₙ`.  It may be infinite, since `G` need not be locally finite. -/
def ball1 (S : Finset V) : Set V := {x | x ∈ S ∨ ∃ y ∈ S, G.Adj x y}

lemma subset_ball1 (S : Finset V) : (↑S : Set V) ⊆ G.ball1 S :=
  fun _ hx => Or.inl (Finset.mem_coe.mp hx)

/-! ### (3.2)–(3.3): the transition probabilities of `Yⁿ` -/

/-- The transition probabilities of `Yⁿ` (with `S = VGₙ`), defined on all of `V`:
(3.2) `c(x,y)/π(x)` for `x ∈ VGₙ`, and (3.3) `hm^x_{VGₙ}(y)` (supported on `VGₙ`) for
`x ∉ VGₙ`.  On `B₁Gₙ` this is exactly the paper's `pₙ`; outside `B₁Gₙ` it is the same
harmonic-measure jump, which is harmless because `B₁Gₙ` is invariant
(`stepKernel_ball1_compl`). -/
noncomputable def transProb (S : Finset V) (x y : V) : ℝ :=
  if x ∈ S then G.c x y / G.pi x else if y ∈ S then G.harmonicMeasure hG S x y else 0

variable {S : Finset V}

lemma transProb_of_mem {x : V} (hx : x ∈ S) (y : V) :
    G.transProb hG S x y = G.c x y / G.pi x := ite_eq_left hx

lemma transProb_of_not_mem_of_mem {x y : V} (hx : x ∉ S) (hy : y ∈ S) :
    G.transProb hG S x y = G.harmonicMeasure hG S x y := by
  rw [transProb, ite_eq_right hx, ite_eq_left hy]

lemma transProb_of_not_mem_of_not_mem {x y : V} (hx : x ∉ S) (hy : y ∉ S) :
    G.transProb hG S x y = 0 := by
  rw [transProb, ite_eq_right hx, ite_eq_right hy]

lemma transProb_nonneg (hS : S.Nonempty) (x y : V) : 0 ≤ G.transProb hG S x y := by
  unfold transProb
  split_ifs
  · exact div_nonneg (G.c_nonneg x y) (G.pi_nonneg x)
  · exact G.harmonicMeasure_nonneg hG hS x y
  · exact le_rfl

lemma summable_transProb (S : Finset V) (x : V) : Summable (G.transProb hG S x) := by
  by_cases hx : x ∈ S
  · have h : G.transProb hG S x = fun y => G.c x y / G.pi x :=
      funext fun y => G.transProb_of_mem hG hx y
    rw [h]
    exact (G.summable_c x).div_const _
  · exact summable_of_ne_finset_zero (s := S) fun y hy =>
      G.transProb_of_not_mem_of_not_mem hG hx hy

/-- The rows of (3.2)–(3.3) are probability vectors: from `x ∈ VGₙ` by (1.1), from
`x ∉ VGₙ` by Lemma 2.4 (`sum_harmonicMeasure`). -/
lemma tsum_transProb [Nontrivial V] (hS : S.Nonempty) (x : V) :
    ∑' y, G.transProb hG S x y = 1 := by
  by_cases hx : x ∈ S
  · simp only [transProb, ite_eq_left hx]
    rw [tsum_div_const, show ∑' y, G.c x y = G.pi x from rfl,
      div_self (G.pi_pos_of_connected hG x).ne']
  · rw [tsum_eq_sum (s := S) fun y hy => G.transProb_of_not_mem_of_not_mem hG hx hy,
      ← G.sum_harmonicMeasure hG hS x]
    exact Finset.sum_congr rfl fun y hy => G.transProb_of_not_mem_of_mem hG hx hy

/-- `h_φ` is bounded (Lemma 2.3, the maximum principle). -/
lemma energyMin_bounded {A : Finset V} (hA : A.Nonempty) (φ : V → ℝ) :
    ∃ C, ∀ x, |G.energyMin hG A φ x| ≤ C :=
  ⟨max |A.inf' hA φ| |A.sup' hA φ|, fun x =>
    abs_le_max_abs_abs (G.min_le_energyMin hG hA φ x) (G.energyMin_le_max hG hA φ x)⟩

/-! ### (3.4): the transition probabilities of the induced chain `Ỹⁿ` (Remark 3.1) -/

/-- The summand of (3.4): `z ↦ (c(x,z)/π(x)) · hm^z_{VGₙ}(y)` for `z ∈ B₁Gₙ ∖ Gₙ` (and `0`
for `z ∈ VGₙ`; non-neighbours `z` of `x` contribute `0` since `c(x,z) = 0`). -/
noncomputable def jumpTerm (S : Finset V) (x y z : V) : ℝ :=
  if z ∈ S then 0 else G.c x z / G.pi x * G.harmonicMeasure hG S z y

lemma jumpTerm_nonneg (hS : S.Nonempty) (x y z : V) : 0 ≤ G.jumpTerm hG S x y z := by
  unfold jumpTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (div_nonneg (G.c_nonneg x z) (G.pi_nonneg x))
      (G.harmonicMeasure_nonneg hG hS z y)

lemma jumpTerm_le (hS : S.Nonempty) (x y z : V) :
    G.jumpTerm hG S x y z ≤ G.c x z / G.pi x := by
  unfold jumpTerm
  split_ifs
  · exact div_nonneg (G.c_nonneg x z) (G.pi_nonneg x)
  · exact mul_le_of_le_one_right (div_nonneg (G.c_nonneg x z) (G.pi_nonneg x))
      (G.harmonicMeasure_le_one hG hS z y)

lemma summable_jumpTerm (hS : S.Nonempty) (x y : V) : Summable (G.jumpTerm hG S x y) :=
  Summable.of_nonneg_of_le (G.jumpTerm_nonneg hG hS x y) (G.jumpTerm_le hG hS x y)
    ((G.summable_c x).div_const _)

/-- (3.4): the transition probabilities `p̃ₙ(x,y)` of the induced chain `Ỹⁿ` on `VGₙ`,
`p̃ₙ(x,y) = c(x,y)/π(x) + ∑_{z ∈ B₁Gₙ ∖ Gₙ, z ∼ x} (c(x,z)/π(x)) hm^z_{VGₙ}(y)` for
`x, y ∈ VGₙ`, extended by `0` for `y ∉ VGₙ` and by the harmonic-measure jump (3.3) for
`x ∉ VGₙ` (so that the kernel lives on all of `V` and is supported on `VGₙ`). -/
noncomputable def inducedTransProb (S : Finset V) (x y : V) : ℝ :=
  if x ∈ S then (if y ∈ S then G.c x y / G.pi x + ∑' z, G.jumpTerm hG S x y z else 0)
  else G.transProb hG S x y

lemma inducedTransProb_of_mem_of_mem {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    G.inducedTransProb hG S x y = G.c x y / G.pi x + ∑' z, G.jumpTerm hG S x y z := by
  rw [inducedTransProb, ite_eq_left hx, ite_eq_left hy]

lemma inducedTransProb_of_not_mem_right {x y : V} (hy : y ∉ S) :
    G.inducedTransProb hG S x y = 0 := by
  unfold inducedTransProb
  split_ifs with hx
  · rfl
  · exact G.transProb_of_not_mem_of_not_mem hG hx hy

lemma inducedTransProb_nonneg (hS : S.Nonempty) (x y : V) :
    0 ≤ G.inducedTransProb hG S x y := by
  unfold inducedTransProb
  split_ifs
  · exact add_nonneg (div_nonneg (G.c_nonneg x y) (G.pi_nonneg x))
      (tsum_nonneg (G.jumpTerm_nonneg hG hS x y))
  · exact le_rfl
  · exact G.transProb_nonneg hG hS x y

lemma summable_inducedTransProb (S : Finset V) (x : V) :
    Summable (G.inducedTransProb hG S x) :=
  summable_of_ne_finset_zero (s := S) fun _ hy => G.inducedTransProb_of_not_mem_right hG hy

/-- The rows of (3.4) are probability vectors on `VGₙ`: `∑_{y ∈ VGₙ} p̃ₙ(x,y) = 1`, since
`∑_{y ∈ VGₙ} hm^z_{VGₙ}(y) = 1` (Lemma 2.4) and `∑_z c(x,z)/π(x) = 1`. -/
lemma tsum_inducedTransProb [Nontrivial V] (hS : S.Nonempty) (x : V) :
    ∑' y, G.inducedTransProb hG S x y = 1 := by
  by_cases hx : x ∈ S
  · rw [tsum_eq_sum (s := S) fun _ hy => G.inducedTransProb_of_not_mem_right hG hy]
    have h1 : ∑ y ∈ S, G.inducedTransProb hG S x y =
        ∑ y ∈ S, G.c x y / G.pi x + ∑ y ∈ S, ∑' z, G.jumpTerm hG S x y z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y hy => G.inducedTransProb_of_mem_of_mem hG hx hy
    have h2 : ∀ z, ∑ y ∈ S, G.jumpTerm hG S x y z =
        if z ∈ S then 0 else G.c x z / G.pi x := by
      intro z
      by_cases hz : z ∈ S
      · simp [jumpTerm, hz]
      · simp only [jumpTerm, ite_eq_right hz, ← Finset.mul_sum, G.sum_harmonicMeasure hG hS z, mul_one]
    have h3 : ∑ y ∈ S, G.c x y / G.pi x = ∑' z, (if z ∈ S then G.c x z / G.pi x else 0) := by
      rw [tsum_eq_sum (s := S) fun z hz => ite_eq_right hz]
      exact Finset.sum_congr rfl fun z hz => (ite_eq_left hz).symm
    have hs3 : Summable fun z => if z ∈ S then G.c x z / G.pi x else 0 :=
      summable_of_ne_finset_zero (s := S) fun z hz => ite_eq_right hz
    have hs4 : Summable fun z => if z ∈ S then 0 else G.c x z / G.pi x := by
      refine Summable.of_nonneg_of_le (f := fun z => G.c x z / G.pi x) (fun z => ?_) (fun z => ?_)
        ((G.summable_c x).div_const (G.pi x))
      · by_cases hz : z ∈ S <;> simp [hz, div_nonneg (G.c_nonneg x z) (G.pi_nonneg x)]
      · by_cases hz : z ∈ S <;> simp [hz, div_nonneg (G.c_nonneg x z) (G.pi_nonneg x)]
    have h4 : ∀ z, (if z ∈ S then G.c x z / G.pi x else 0) +
        (if z ∈ S then 0 else G.c x z / G.pi x) = G.c x z / G.pi x := by
      intro z
      split_ifs <;> simp
    rw [h1, ← Summable.tsum_finsetSum fun y _ => G.summable_jumpTerm hG hS x y]
    simp_rw [h2]
    rw [h3, ← hs3.tsum_add hs4]
    simp_rw [h4]
    rw [tsum_div_const, show ∑' z, G.c x z = G.pi x from rfl,
      div_self (G.pi_pos_of_connected hG x).ne']
  · have h : G.inducedTransProb hG S x = G.transProb hG S x :=
      funext fun y => by rw [inducedTransProb, ite_eq_right hx]
    rw [h]
    exact G.tsum_transProb hG hS x

end Defs

section Kernel

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected) {S : Finset V}

/-! ### The transition kernel of `Yⁿ` -/

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
lemma isTransProb_transProb (hS : S.Nonempty) : IsTransProb (G.transProb hG S) :=
  ⟨G.transProb_nonneg hG hS, G.summable_transProb hG S, G.tsum_transProb hG hS⟩

/-- **The transition kernel of `Yⁿ`**, (3.2)–(3.3), as a Markov kernel on `V`
(with `S = VGₙ`); `Nontrivial V` records that `G` is infinite, so that `π > 0`. -/
noncomputable def stepKernel (hS : S.Nonempty) : Kernel V V :=
  (G.isTransProb_transProb hG hS).kernel

instance stepKernel_isMarkovKernel (hS : S.Nonempty) : IsMarkovKernel (G.stepKernel hG hS) := by
  unfold stepKernel
  infer_instance

lemma stepKernel_singleton (hS : S.Nonempty) (x y : V) :
    G.stepKernel hG hS x {y} = ENNReal.ofReal (G.transProb hG S x y) :=
  (G.isTransProb_transProb hG hS).kernel_singleton x y

/-- Integrals against the kernel of `Yⁿ` are `∑_y pₙ(x,y) f(y)`. -/
lemma integral_stepKernel (hS : S.Nonempty) (x : V) {f : V → ℝ}
    (hf : Integrable f (G.stepKernel hG hS x)) :
    ∫ y, f y ∂G.stepKernel hG hS x = ∑' y, G.transProb hG S x y * f y :=
  (G.isTransProb_transProb hG hS).integral_kernel x hf

/-- From `x ∉ VGₙ` the chain jumps into `VGₙ`: (3.3) is supported on `VGₙ`. -/
lemma stepKernel_compl_of_not_mem (hS : S.Nonempty) {x : V} (hx : x ∉ S) :
    G.stepKernel hG hS x (↑S : Set V)ᶜ = 0 :=
  (G.isTransProb_transProb hG hS).kernel_apply_eq_zero fun _ hy =>
    G.transProb_of_not_mem_of_not_mem hG hx hy

/-- From `x ∈ VGₙ`, every neighbour of `x` is reached in one step with positive probability. -/
lemma stepKernel_singleton_pos (hS : S.Nonempty) {x y : V} (hx : x ∈ S) (hxy : G.Adj x y) :
    0 < G.stepKernel hG hS x {y} :=
  (G.isTransProb_transProb hG hS).kernel_singleton_pos
    (by rw [G.transProb_of_mem hG hx]; exact div_pos hxy (G.pi_pos_of_adj hxy))

/-- (3.2)–(3.3) never leave `B₁Gₙ` (indeed the kernel maps every `x ∈ V` into `B₁Gₙ`):
`Yⁿ` is a Markov chain on `B₁Gₙ`. -/
lemma stepKernel_ball1_compl (hS : S.Nonempty) (x : V) :
    G.stepKernel hG hS x (G.ball1 S)ᶜ = 0 := by
  refine (G.isTransProb_transProb hG hS).kernel_apply_eq_zero fun y hy => ?_
  have hyS : y ∉ S := fun h => hy (Or.inl h)
  by_cases hxS : x ∈ S
  · rw [G.transProb_of_mem hG hxS]
    have hadj : ¬ G.Adj y x := fun h => hy (Or.inr ⟨x, hxS, h⟩)
    have hc : G.c x y = 0 := by
      rw [G.c_symm]
      exact le_antisymm (not_lt.mp hadj) (G.c_nonneg y x)
    rw [hc, zero_div]
  · exact G.transProb_of_not_mem_of_not_mem hG hxS hyS

/-- The chain `Yⁿ` started in `B₁Gₙ` stays in `B₁Gₙ` at all times, almost surely. -/
lemma chainLaw_ae_mem_ball1 (hS : S.Nonempty) {z : V} (hz : z ∈ G.ball1 S) :
    ∀ᵐ ω ∂chainLaw (G.stepKernel hG hS) z, ∀ j, ω j ∈ G.ball1 S :=
  chainLaw_ae_forall_mem _ MeasurableSet.of_discrete
    (fun y _ => G.stepKernel_ball1_compl hG hS y) hz

/-- The kernel of `Yⁿ` satisfies the hypotheses of the maximum principle on `VGₙ`. -/
lemma stepsOn (hS : S.Nonempty) (hconn : (G.toSimpleGraph.induce (↑S : Set V)).Connected) :
    StepsOn (G.stepKernel hG hS) G.toSimpleGraph S where
  connected := hconn
  supp := fun _ hx => G.stepKernel_compl_of_not_mem hG hS hx
  adj_pos := fun _ hx _ _ hxy => G.stepKernel_singleton_pos hG hS hx hxy

/-! ### Lemma 3.2 -/

/-- (3.7) for `h_φ`: at `x ∈ VGₙ ∖ A`, `h_φ(x) = ∑_y pₙ(x,y) h_φ(y)`, i.e. discrete harmonicity
of `h_φ` at `x` (Proposition 1.3, Definition 1.2 with footnote 2) divided by `π(x)`. -/
lemma integral_stepKernel_energyMin_of_mem (hS : S.Nonempty) {A : Finset V}
    (hA : A.Nonempty) (φ : V → ℝ) {x : V} (hxS : x ∈ S) (hxA : x ∉ A) :
    ∫ y, G.energyMin hG A φ y ∂G.stepKernel hG hS x = G.energyMin hG A φ x := by
  obtain ⟨C, hC⟩ := G.energyMin_bounded hG hA φ
  rw [G.integral_stepKernel hG hS x
    (integrable_of_bounded _ (measurable_of_countable _).aestronglyMeasurable C hC)]
  have hharm : G.IsHarmonicAt (G.energyMin hG A φ) x :=
    G.energyMin_isHarmonicOn hG hA φ x (by simpa using hxA)
  have habs : Summable fun y => G.c x y * |G.energyMin hG A φ y - G.energyMin hG A φ x| :=
    hharm.absSummable
  have hsum : ∑' y, G.c x y * (G.energyMin hG A φ y - G.energyMin hG A φ x) = 0 :=
    hharm.tsum_eq_zero
  have hs1 : Summable fun y => G.c x y * (G.energyMin hG A φ y - G.energyMin hG A φ x) :=
    Summable.of_norm (habs.congr fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (G.c_nonneg x y)])
  have hs2 : Summable fun y => G.c x y * G.energyMin hG A φ x :=
    (G.summable_c x).mul_right _
  have hkey : ∑' y, G.c x y * G.energyMin hG A φ y = G.pi x * G.energyMin hG A φ x := by
    have heq : (fun y => G.c x y * G.energyMin hG A φ y) =
        fun y => G.c x y * (G.energyMin hG A φ y - G.energyMin hG A φ x) +
          G.c x y * G.energyMin hG A φ x := by
      funext y
      ring
    rw [heq, hs1.tsum_add hs2, hsum, zero_add, tsum_mul_right]
    rfl
  have hπ : G.pi x ≠ 0 := (G.pi_pos_of_connected hG x).ne'
  calc ∑' y, G.transProb hG S x y * G.energyMin hG A φ y
      = (∑' y, G.c x y * G.energyMin hG A φ y) / G.pi x := by
        rw [← tsum_div_const]
        exact tsum_congr fun y => by rw [G.transProb_of_mem hG hxS]; ring
    _ = G.energyMin hG A φ x := by rw [hkey, mul_div_cancel_left₀ _ hπ]

/-- (3.8) for `h_φ`: at `x ∉ VGₙ`, `h_φ(x) = ∑_{y ∈ VGₙ} hm^x_{VGₙ}(y) h_φ(y)`: by Lemma 2.2
(consistency, `energyMin_restrict`) `h_φ` is the energy-minimizing extension of its own
restriction to `VGₙ`, and Lemma 2.4 (2.8) (`energyMin_eq_sum_harmonicMeasure`) applies. -/
lemma integral_stepKernel_energyMin_of_not_mem (hS : S.Nonempty) {A : Finset V}
    (hA : A.Nonempty) (hAS : A ⊆ S) (φ : V → ℝ) {x : V} (hx : x ∉ S) :
    ∫ y, G.energyMin hG A φ y ∂G.stepKernel hG hS x = G.energyMin hG A φ x := by
  obtain ⟨C, hC⟩ := G.energyMin_bounded hG hA φ
  rw [G.integral_stepKernel hG hS x
    (integrable_of_bounded _ (measurable_of_countable _).aestronglyMeasurable C hC),
    tsum_eq_sum (s := S) fun y hy => by
      rw [G.transProb_of_not_mem_of_not_mem hG hx hy, zero_mul]]
  have hsum : ∑ y ∈ S, G.transProb hG S x y * G.energyMin hG A φ y =
      ∑ y ∈ S, G.energyMin hG A φ y * G.harmonicMeasure hG S x y :=
    Finset.sum_congr rfl fun y hy => by rw [G.transProb_of_not_mem_of_mem hG hx hy, mul_comm]
  rw [hsum, ← G.energyMin_eq_sum_harmonicMeasure hG hS (G.energyMin hG A φ) x,
    G.energyMin_restrict hG hA hAS φ]

/-- **Lemma 3.2.**  Let `A ⊆ VGₙ` be a non-empty finite set, `φ : V → ℝ`, `h_φ` the
energy-minimizing extension of `φ|_A` (Proposition 1.3), and `τₙ = min {j ≥ 0 : Yⁿ_j ∈ A}`.
Then for every starting point `x` (in particular every `x ∈ VGₙ`),
`h_φ(x) = E_x[φ(Yⁿ_{τₙ})]`.

The proof is the paper's: `f^φ_n(x) := E_x[φ(Yⁿ_{τₙ})]` satisfies (3.7)–(3.8) by the Markov
property (`integral_walkShift_one`), `h_φ` satisfies them by Proposition 1.3, Lemma 2.2 and
Lemma 2.4, and the difference vanishes on `A`, so it vanishes everywhere by the maximum
principle on the finite set `VGₙ` (`eq_zero_of_mean_value`).  The expectation is well defined
because `τₙ < ∞` almost surely (`hitTime_ae_ne_top`, Remark 3.1). -/
theorem energyMin_eq_integral_hitVertex (hS : S.Nonempty)
    (hconn : (G.toSimpleGraph.induce (↑S : Set V)).Connected) {A : Finset V} (hA : A.Nonempty)
    (hAS : A ⊆ S) (φ : V → ℝ) (x : V) :
    G.energyMin hG A φ x =
      ∫ ω, φ (hitVertex (↑A : Set V) ω) ∂chainLaw (G.stepKernel hG hS) x := by
  have hst : StepsOn (G.stepKernel hG hS) G.toSimpleGraph S := G.stepsOn hG hS hconn
  -- the bounded truncation of `φ` to `A`
  set φ' : V → ℝ := fun v => if v ∈ A then φ v else 0 with hφ'
  have hφ'_bdd : ∀ v, |φ' v| ≤ ∑ a ∈ A, |φ a| := by
    intro v
    simp only [hφ']
    split_ifs with hv
    · exact Finset.single_le_sum (fun a _ => abs_nonneg (φ a)) hv
    · rw [abs_zero]
      exact Finset.sum_nonneg fun a _ => abs_nonneg (φ a)
  set Φ : (ℕ → V) → ℝ := fun ω => φ' (hitVertex (↑A : Set V) ω) with hΦ
  have hΦ_meas : Measurable Φ := (measurable_of_countable φ').comp (measurable_hitVertex _)
  have hΦ_bdd : ∀ ω, |Φ ω| ≤ ∑ a ∈ A, |φ a| := fun ω => hφ'_bdd _
  -- `f^φ_n` of (3.5)
  set f : V → ℝ := fun y => ∫ ω, Φ ω ∂chainLaw (G.stepKernel hG hS) y with hf
  have hf_bdd : ∀ y, |f y| ≤ ∑ a ∈ A, |φ a| := by
    intro y
    have h := norm_integral_le_of_norm_le_const (μ := chainLaw (G.stepKernel hG hS) y)
      (C := ∑ a ∈ A, |φ a|) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hΦ_bdd ω)
    rw [show (chainLaw (G.stepKernel hG hS) y).real Set.univ = 1 by simp [measureReal_def],
      mul_one, Real.norm_eq_abs] at h
    exact h
  -- `f = φ` on `A`
  have hfA : ∀ a ∈ A, f a = φ a := by
    intro a ha
    have hae : ∀ᵐ ω ∂chainLaw (G.stepKernel hG hS) a, Φ ω = φ a := by
      filter_upwards [chainLaw_ae_start (G.stepKernel hG hS) a] with ω h0
      have h0A : ω 0 ∈ (↑A : Set V) := by rw [h0]; exact Finset.mem_coe.mpr ha
      simp only [hΦ, hitVertex_of_mem_zero h0A, h0, hφ', ite_eq_left ha]
    show ∫ ω, Φ ω ∂chainLaw (G.stepKernel hG hS) a = φ a
    rw [integral_congr_ae hae]
    simp [integral_const, measureReal_def]
  -- (3.7)/(3.8) for `f`: the first-step analysis
  have hfmean : ∀ y ∉ A, f y = ∫ w, f w ∂G.stepKernel hG hS y := by
    intro y hy
    have hae : ∀ᵐ ω ∂chainLaw (G.stepKernel hG hS) y, Φ ω = Φ (walkShift 1 ω) := by
      filter_upwards [chainLaw_ae_start (G.stepKernel hG hS) y,
        hitTime_ae_ne_top hst hAS hA y] with ω h0 hne
      have h0A : ω 0 ∉ (↑A : Set V) := by
        rw [h0]
        exact fun h => hy (Finset.mem_coe.mp h)
      simp only [hΦ, hitVertex_walkShift h0A hne]
    show ∫ ω, Φ ω ∂chainLaw (G.stepKernel hG hS) y =
      ∫ w, (∫ ω, Φ ω ∂chainLaw (G.stepKernel hG hS) w) ∂G.stepKernel hG hS y
    rw [integral_congr_ae hae, integral_walkShift_one _ y hΦ_meas _ hΦ_bdd]
  -- (3.7)/(3.8) for `h_φ`
  obtain ⟨C₁, hC₁⟩ := G.energyMin_bounded hG hA φ
  have hhmean : ∀ y ∉ A,
      G.energyMin hG A φ y = ∫ w, G.energyMin hG A φ w ∂G.stepKernel hG hS y := by
    intro y hy
    by_cases hyS : y ∈ S
    · exact (G.integral_stepKernel_energyMin_of_mem hG hS hA φ hyS hy).symm
    · exact (G.integral_stepKernel_energyMin_of_not_mem hG hS hA hAS φ hyS).symm
  -- the maximum principle for `g = h_φ - f`
  have hg := eq_zero_of_mean_value hst hAS hA (g := fun v => G.energyMin hG A φ v - f v)
    (C₁ + ∑ a ∈ A, |φ a|)
    (fun v => (abs_sub _ _).trans (add_le_add (hC₁ v) (hf_bdd v)))
    (fun v hv => by
      show G.energyMin hG A φ v - f v =
        ∫ w, (G.energyMin hG A φ w - f w) ∂G.stepKernel hG hS v
      rw [integral_sub
        (integrable_of_bounded _ (measurable_of_countable _).aestronglyMeasurable C₁ hC₁)
        (integrable_of_bounded _ (measurable_of_countable _).aestronglyMeasurable _ hf_bdd),
        ← hhmean v hv, ← hfmean v hv])
    (fun a ha => by
      show G.energyMin hG A φ a - f a = 0
      rw [hfA a ha, G.energyMin_eqOn hG hA φ (Finset.mem_coe.mpr ha), sub_self])
  have hx : G.energyMin hG A φ x = f x := sub_eq_zero.mp (hg x)
  rw [hx]
  refine integral_congr_ae ?_
  filter_upwards [hitTime_ae_ne_top hst hAS hA x] with ω hne
  simp only [hΦ, hφ', ite_eq_left (Finset.mem_coe.mp (hitVertex_mem hne))]

/-! ### Remark 3.1: the induced chain on `VGₙ` -/

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
lemma isTransProb_inducedTransProb (hS : S.Nonempty) : IsTransProb (G.inducedTransProb hG S) :=
  ⟨G.inducedTransProb_nonneg hG hS, G.summable_inducedTransProb hG S,
    G.tsum_inducedTransProb hG hS⟩

/-- **Remark 3.1**: the transition kernel (3.4) of the induced chain `Ỹⁿ` on the finite set
`VGₙ`, as a Markov kernel on `V` supported on `VGₙ`. -/
noncomputable def inducedKernel (hS : S.Nonempty) : Kernel V V :=
  (G.isTransProb_inducedTransProb hG hS).kernel

instance inducedKernel_isMarkovKernel (hS : S.Nonempty) :
    IsMarkovKernel (G.inducedKernel hG hS) := by
  unfold inducedKernel
  infer_instance

lemma inducedKernel_singleton (hS : S.Nonempty) (x y : V) :
    G.inducedKernel hG hS x {y} = ENNReal.ofReal (G.inducedTransProb hG S x y) :=
  (G.isTransProb_inducedTransProb hG hS).kernel_singleton x y

/-- `Ỹⁿ` lives on `VGₙ`: from every `x`, the kernel (3.4) is supported on `VGₙ`. -/
lemma inducedKernel_compl (hS : S.Nonempty) (x : V) :
    G.inducedKernel hG hS x (↑S : Set V)ᶜ = 0 :=
  (G.isTransProb_inducedTransProb hG hS).kernel_apply_eq_zero fun _ hy =>
    G.inducedTransProb_of_not_mem_right hG hy

/-- Adjacent vertices of `VGₙ` communicate in one step of `Ỹⁿ`: `p̃ₙ(x,y) ≥ c(x,y)/π(x) > 0`. -/
lemma inducedKernel_singleton_pos (hS : S.Nonempty) {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : G.Adj x y) : 0 < G.inducedKernel hG hS x {y} :=
  (G.isTransProb_inducedTransProb hG hS).kernel_singleton_pos (by
    rw [G.inducedTransProb_of_mem_of_mem hG hx hy]
    exact add_pos_of_pos_of_nonneg (div_pos hxy (G.pi_pos_of_adj hxy))
      (tsum_nonneg (G.jumpTerm_nonneg hG hS x y)))

/-- The chain `Ỹⁿ` started in `VGₙ` stays in `VGₙ` at all times, almost surely. -/
lemma inducedChainLaw_ae_mem (hS : S.Nonempty) {z : V} (hz : z ∈ S) :
    ∀ᵐ ω ∂chainLaw (G.inducedKernel hG hS) z, ∀ j, ω j ∈ S := by
  have h := chainLaw_ae_forall_mem (G.inducedKernel hG hS) (B := (↑S : Set V))
    MeasurableSet.of_discrete (fun y _ => G.inducedKernel_compl hG hS y) (Finset.mem_coe.mpr hz)
  filter_upwards [h] with ω hω j
  exact Finset.mem_coe.mp (hω j)

/-- The kernel (3.4) of `Ỹⁿ` satisfies the hypotheses of the maximum principle on `VGₙ`:
`Ỹⁿ` is an irreducible chain on the finite state space `VGₙ` (Remark 3.1). -/
lemma inducedStepsOn (hS : S.Nonempty)
    (hconn : (G.toSimpleGraph.induce (↑S : Set V)).Connected) :
    StepsOn (G.inducedKernel hG hS) G.toSimpleGraph S where
  connected := hconn
  supp := fun x _ => G.inducedKernel_compl hG hS x
  adj_pos := fun _ hx _ hy hxy => G.inducedKernel_singleton_pos hG hS hx hy hxy

/-- **Remark 3.1**: the induced chain `Ỹⁿ` with kernel (3.4) is an irreducible Markov chain on
the finite state space `VGₙ`, in the sense of `Kernel.IsIrreducible` with respect to the
counting measure on `VGₙ`. -/
theorem inducedKernel_isIrreducible (hS : S.Nonempty)
    (hconn : (G.toSimpleGraph.induce (↑S : Set V)).Connected) :
    Kernel.IsIrreducible (Measure.count.restrict (↑S : Set V)) (G.inducedKernel hG hS) :=
  isIrreducible_of_stepsOn (G.inducedStepsOn hG hS hconn)

/-- The kernel (3.2)–(3.3) of `Yⁿ` is likewise irreducible with respect to the counting measure
on `VGₙ`. -/
theorem stepKernel_isIrreducible (hS : S.Nonempty)
    (hconn : (G.toSimpleGraph.induce (↑S : Set V)).Connected) :
    Kernel.IsIrreducible (Measure.count.restrict (↑S : Set V)) (G.stepKernel hG hS) :=
  isIrreducible_of_stepsOn (G.stepsOn hG hS hconn)

/-! ### Lemma 3.3: consistency of the chains under coarsening -/

/-- For `z ∈ S ⊆ T` the one-step laws of `Y^S` and `Y^T` from `z` agree: both are (3.2). -/
lemma stepKernel_apply_of_mem {T : Finset V} (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T)
    {z : V} (hz : z ∈ S) : G.stepKernel hG hT z = G.stepKernel hG hS z :=
  Measure.ext_of_singleton fun y => by
    rw [stepKernel_singleton, stepKernel_singleton, G.transProb_of_mem hG (hST hz),
      G.transProb_of_mem hG hz]

/-- The law of `Y^T_{τ_S}` from `z ∉ S` is the harmonic-measure row `p_S(z, ·)` of (3.3):
Lemma 3.2 applied to the indicator functions `1_y`, `y ∈ S`. -/
lemma map_hitVertex_eq_stepKernel {T : Finset V} (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S ⊆ T) (hconnT : (G.toSimpleGraph.induce (↑T : Set V)).Connected) {z : V}
    (hz : z ∉ S) :
    (chainLaw (G.stepKernel hG hT) z).map (hitVertex (↑S : Set V)) = G.stepKernel hG hS z := by
  have hfin := hitTime_ae_ne_top (G.stepsOn hG hT hconnT) hST hS z
  refine Measure.ext_of_singleton fun y => ?_
  rw [Measure.map_apply (measurable_hitVertex _) (measurableSet_singleton y), stepKernel_singleton]
  have hset : hitVertex (↑S : Set V) ⁻¹' {y} = {ω | hitVertex (↑S : Set V) ω = y} := rfl
  rw [hset]
  by_cases hy : y ∈ S
  · rw [G.transProb_of_not_mem_of_mem hG hz hy]
    have h32 := G.energyMin_eq_integral_hitVertex hG hT hconnT hS hST (G.indic y) z
    have hind : (fun ω => G.indic y (hitVertex (↑S : Set V) ω)) =
        {ω : ℕ → V | hitVertex (↑S : Set V) ω = y}.indicator 1 := by
      funext ω
      by_cases h : hitVertex (↑S : Set V) ω = y <;> simp [indic, Set.indicator, h]
    have hs' : MeasurableSet {ω : ℕ → V | hitVertex (↑S : Set V) ω = y} :=
      measurable_hitVertex (↑S : Set V) (measurableSet_singleton y)
    rw [hind, integral_indicator_one hs', measureReal_def] at h32
    rw [harmonicMeasure, h32, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [G.transProb_of_not_mem_of_not_mem hG hz hy, ENNReal.ofReal_zero]
    have h : ∀ᵐ ω ∂chainLaw (G.stepKernel hG hT) z, ¬ hitVertex (↑S : Set V) ω = y := by
      filter_upwards [hfin] with ω hω h
      exact hy (Finset.mem_coe.mp (h ▸ hitVertex_mem hω))
    have h' := ae_iff.mp h
    simpa using h'

/-- **Lemma 3.3** (one level).  Let `S ⊆ T` be non-empty finite vertex sets with `T` inducing a
connected subgraph, and let `Y^S`, `Y^T` be the chains of Section 3.1 with kernels
`stepKernel hS`, `stepKernel hT`.  The coarsening (3.9) of `Y^T` along `S` — the path
`k ↦ Y^T_{J_k}` with `J_0 = 0`, `J_{k+1} = J_k + 1` if `Y^T_{J_k} ∈ S` and otherwise the next
visit to `S` — has the law of `Y^S`, from every starting point `z`.

The proof is a first-step analysis: pathwise the coarsened path is `z` followed by the
coarsening of the path shifted by `J₁`; under `P_z` the shifted path has the law of a fresh
`Y^T` started from `Y^T_{J₁}` (the Markov property at time `1` if `z ∈ S`, the strong Markov
property at the hitting time `τ_S` otherwise), and `Y^T_{J₁}` has law `p_S(z, ·)` — by (3.2) if
`z ∈ S` and by Lemma 3.2 (`map_hitVertex_eq_stepKernel`) if `z ∉ S`.  Since `Y^S` satisfies the
same recursion, all finite-dimensional marginals agree by induction, and cylinder uniqueness
finishes the proof. -/
theorem chainLaw_map_coarsenPath {T : Finset V} (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S ⊆ T) (hconnT : (G.toSimpleGraph.induce (↑T : Set V)).Connected) (z : V) :
    (chainLaw (G.stepKernel hG hT) z).map (IndexSet.coarsenPath (↑S : Set V)) =
      chainLaw (G.stepKernel hG hS) z := by
  have hmeasC : Measurable (IndexSet.coarsenPath (↑S : Set V) : (ℕ → V) → ℕ → V) :=
    IndexSet.measurable_coarsenPath MeasurableSet.of_discrete
  have hmeasJ : Measurable (fun p : ℕ → V => walkShift (IndexSet.coarsen (↑S : Set V) p 1) p) := by
    have h1 : Measurable (fun q : (ℕ → V) × ℕ => walkShift q.2 q.1) :=
      measurable_from_prod_countable_left fun j => measurable_walkShift j
    exact h1.comp (measurable_id.prodMk (IndexSet.measurable_coarsen MeasurableSet.of_discrete 1))
  -- the recursion for the coarsened law
  have hrec : ∀ y, (chainLaw (G.stepKernel hG hT) y).map (IndexSet.coarsenPath (↑S : Set V)) =
      ((pathKernel (G.stepKernel hG hT) ∘ₘ G.stepKernel hG hS y).map
        (IndexSet.coarsenPath (↑S : Set V))).map (consPath y) := by
    intro y
    have hpath : ∀ p : ℕ → V, IndexSet.coarsenPath (↑S : Set V) p =
        consPath (p 0) (IndexSet.coarsenPath (↑S : Set V)
          (walkShift (IndexSet.coarsen (↑S : Set V) p 1) p)) := fun p => funext fun k => by
      cases k with
      | zero => rfl
      | succ k => exact coarsenPath_succ _ p k
    have hshift : (chainLaw (G.stepKernel hG hT) y).map
        (fun p => walkShift (IndexSet.coarsen (↑S : Set V) p 1) p) =
        pathKernel (G.stepKernel hG hT) ∘ₘ G.stepKernel hG hS y := by
      by_cases hy : y ∈ S
      · have h : (chainLaw (G.stepKernel hG hT) y).map
            (fun p => walkShift (IndexSet.coarsen (↑S : Set V) p 1) p) =
            (chainLaw (G.stepKernel hG hT) y).map (walkShift 1) := by
          apply Measure.map_congr
          filter_upwards [chainLaw_ae_start (G.stepKernel hG hT) y] with p hp
          rw [coarsen_one_of_mem _ p (by rw [hp]; exact Finset.mem_coe.mpr hy)]
        rw [h, chainLaw_map_walkShift, chainLaw_marginal_one,
          G.stepKernel_apply_of_mem hG hS hT hST hy]
      · have hfin := hitTime_ae_ne_top (G.stepsOn hG hT hconnT) hST hS y
        have h : (chainLaw (G.stepKernel hG hT) y).map
            (fun p => walkShift (IndexSet.coarsen (↑S : Set V) p 1) p) =
            (chainLaw (G.stepKernel hG hT) y).map
              (fun p => walkShift (hitIndex (↑S : Set V) p) p) := by
          apply Measure.map_congr
          filter_upwards [chainLaw_ae_start (G.stepKernel hG hT) y, hfin] with p hp hne
          rw [coarsen_one_of_not_mem _ p (by rw [hp]; exact fun h => hy (Finset.mem_coe.mp h)) hne]
        rw [h, chainLaw_map_walkShift_hitIndex _ y _ hfin,
          G.map_hitVertex_eq_stepKernel hG hS hT hST hconnT hy]
    calc (chainLaw (G.stepKernel hG hT) y).map (IndexSet.coarsenPath (↑S : Set V))
        = (chainLaw (G.stepKernel hG hT) y).map (fun p => consPath y
            (IndexSet.coarsenPath (↑S : Set V) (walkShift (IndexSet.coarsen (↑S : Set V) p 1) p))) := by
          apply Measure.map_congr
          filter_upwards [chainLaw_ae_start (G.stepKernel hG hT) y] with p hp
          rw [hpath p, hp]
      _ = (((chainLaw (G.stepKernel hG hT) y).map
            (fun p => walkShift (IndexSet.coarsen (↑S : Set V) p 1) p)).map
              (IndexSet.coarsenPath (↑S : Set V))).map (consPath y) := by
          rw [Measure.map_map hmeasC hmeasJ, Measure.map_map (measurable_consPath y) (hmeasC.comp hmeasJ)]
          rfl
      _ = _ := by rw [hshift]
  -- all finite-dimensional marginals agree
  have hpre : ∀ k, ∀ y, ((chainLaw (G.stepKernel hG hT) y).map
      (IndexSet.coarsenPath (↑S : Set V))).map (frestrictLe k) =
      (chainLaw (G.stepKernel hG hS) y).map (frestrictLe k) := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [chainLaw_initialHistory, Measure.map_map (measurable_frestrictLe 0) hmeasC]
      have h : (chainLaw (G.stepKernel hG hT) y).map
          (frestrictLe 0 ∘ IndexSet.coarsenPath (↑S : Set V)) =
          (chainLaw (G.stepKernel hG hT) y).map (fun _ => fun _ : Finset.Iic 0 => y) := by
        apply Measure.map_congr
        filter_upwards [chainLaw_ae_start (G.stepKernel hG hT) y] with p hp
        funext i
        show p (IndexSet.coarsen (↑S : Set V) p i.val) = y
        have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
        rw [hi, IndexSet.coarsen_zero, hp]
      rw [h, Measure.map_const]
      simp
    | succ k ih =>
      intro y
      have hk' : ((pathKernel (G.stepKernel hG hT)).map (IndexSet.coarsenPath (↑S : Set V))).map
          (frestrictLe k) = (pathKernel (G.stepKernel hG hS)).map (frestrictLe k) := by
        refine Kernel.ext fun w => ?_
        rw [Kernel.map_apply _ (measurable_frestrictLe k), Kernel.map_apply _ hmeasC,
          pathKernel_apply, ih w, Kernel.map_apply _ (measurable_frestrictLe k), pathKernel_apply]
      have hcomp : frestrictLe (π := fun _ : ℕ => V) (k + 1) ∘ consPath y =
          consPrefix y k ∘ frestrictLe (π := fun _ : ℕ => V) k :=
        funext fun q => frestrictLe_succ_consPath y k q
      rw [hrec y, chainLaw_eq_map_consPath (G.stepKernel hG hS) y,
        Measure.map_map (measurable_frestrictLe (k + 1)) (measurable_consPath y),
        Measure.map_map (measurable_frestrictLe (k + 1)) (measurable_consPath y), hcomp,
        ← Measure.map_map (measurable_consPrefix y k) (measurable_frestrictLe k),
        ← Measure.map_map (measurable_consPrefix y k) (measurable_frestrictLe k)]
      congr 1
      rw [Measure.map_comp _ _ hmeasC, Measure.map_comp _ _ (measurable_frestrictLe k),
        Measure.map_comp _ _ (measurable_frestrictLe k), hk']
  exact measure_eq_of_prefix_eq _ _ fun k => hpre k z

end Kernel

/-! ### The chains `Yⁿ` and `Ỹⁿ` along an exhaustion `{Gₙ}` -/

namespace Exhaustion

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V} (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)

/-- `B₁Gₙ` of (3.1). -/
def ball1 (n : ℕ) : Set V := G.ball1 (E.Gsub n)

/-- The transition probabilities (3.2)–(3.3) of `Yⁿ`. -/
noncomputable def transProb (n : ℕ) : V → V → ℝ := G.transProb hG (E.Gsub n)

/-- The transition kernel of `Yⁿ` (Section 3.1). -/
noncomputable def stepKernel (n : ℕ) : Kernel V V := G.stepKernel hG (E.nonempty n)

instance stepKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (E.stepKernel hG n) := by
  unfold stepKernel
  infer_instance

lemma stepKernel_singleton (n : ℕ) (x y : V) :
    E.stepKernel hG n x {y} = ENNReal.ofReal (E.transProb hG n x y) :=
  G.stepKernel_singleton hG (E.nonempty n) x y

/-- The law `P_z` of `Yⁿ` started at `Yⁿ_0 = z` (Section 3.1), by Ionescu–Tulcea; a measure
on the path space `ℕ → V`. -/
noncomputable def chainLaw (n : ℕ) (z : V) : Measure (ℕ → V) :=
  MarkovChain.chainLaw (E.stepKernel hG n) z

instance chainLaw_isProbabilityMeasure (n : ℕ) (z : V) :
    IsProbabilityMeasure (E.chainLaw hG n z) := by
  unfold Exhaustion.chainLaw
  infer_instance

lemma chainLaw_ae_start (n : ℕ) (z : V) : ∀ᵐ ω ∂E.chainLaw hG n z, ω 0 = z :=
  MarkovChain.chainLaw_ae_start _ z

/-- `Yⁿ` is a Markov chain on `B₁Gₙ`: started in `B₁Gₙ` it never leaves it. -/
theorem chainLaw_ae_mem_ball1 (n : ℕ) {z : V} (hz : z ∈ E.ball1 n) :
    ∀ᵐ ω ∂E.chainLaw hG n z, ∀ j, ω j ∈ E.ball1 n :=
  G.chainLaw_ae_mem_ball1 hG (E.nonempty n) hz

lemma stepsOn (n : ℕ) : StepsOn (E.stepKernel hG n) G.toSimpleGraph (E.Gsub n) :=
  G.stepsOn hG (E.nonempty n) (E.connected n)

/-- **Lemma 3.2** for the chain `Yⁿ` of the exhaustion: for a non-empty finite `A ⊆ VGₙ`,
`φ : V → ℝ` and every `x`, `h_φ(x) = E_x[φ(Yⁿ_{τₙ})]`. -/
theorem energyMin_eq_integral_hitVertex (n : ℕ) {A : Finset V} (hA : A.Nonempty)
    (hAS : A ⊆ E.Gsub n) (φ : V → ℝ) (x : V) :
    G.energyMin hG A φ x = ∫ ω, φ (hitVertex (↑A : Set V) ω) ∂E.chainLaw hG n x :=
  G.energyMin_eq_integral_hitVertex hG (E.nonempty n) (E.connected n) hA hAS φ x

/-- A non-empty finite `A ⊆ VGₙ` is hit by `Yⁿ` in finite time almost surely, from every
starting point (the "`τₙ < ∞` a.s." of Lemma 3.2). -/
theorem hitTime_ae_ne_top (n : ℕ) {A : Finset V} (hA : A.Nonempty) (hAS : A ⊆ E.Gsub n)
    (x : V) : ∀ᵐ ω ∂E.chainLaw hG n x, hitTime (↑A : Set V) ω ≠ ⊤ :=
  MarkovChain.hitTime_ae_ne_top (E.stepsOn hG n) hAS hA x

/-- The kernel of `Yⁿ` is irreducible with respect to the counting measure on `VGₙ`. -/
theorem stepKernel_isIrreducible (n : ℕ) :
    Kernel.IsIrreducible (Measure.count.restrict (↑(E.Gsub n) : Set V)) (E.stepKernel hG n) :=
  G.stepKernel_isIrreducible hG (E.nonempty n) (E.connected n)

/-- The transition probabilities (3.4) of the induced chain `Ỹⁿ`. -/
noncomputable def inducedTransProb (n : ℕ) : V → V → ℝ := G.inducedTransProb hG (E.Gsub n)

/-- The transition kernel (3.4) of the induced chain `Ỹⁿ` on `VGₙ` (Remark 3.1). -/
noncomputable def inducedKernel (n : ℕ) : Kernel V V := G.inducedKernel hG (E.nonempty n)

instance inducedKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (E.inducedKernel hG n) := by
  unfold inducedKernel
  infer_instance

lemma inducedKernel_singleton (n : ℕ) (x y : V) :
    E.inducedKernel hG n x {y} = ENNReal.ofReal (E.inducedTransProb hG n x y) :=
  G.inducedKernel_singleton hG (E.nonempty n) x y

/-- The law of `Ỹⁿ` started at `z`. -/
noncomputable def inducedLaw (n : ℕ) (z : V) : Measure (ℕ → V) :=
  MarkovChain.chainLaw (E.inducedKernel hG n) z

instance inducedLaw_isProbabilityMeasure (n : ℕ) (z : V) :
    IsProbabilityMeasure (E.inducedLaw hG n z) := by
  unfold inducedLaw
  infer_instance

/-- `Ỹⁿ` is a chain on the finite state space `VGₙ`. -/
theorem inducedLaw_ae_mem (n : ℕ) {z : V} (hz : z ∈ E.Gsub n) :
    ∀ᵐ ω ∂E.inducedLaw hG n z, ∀ j, ω j ∈ E.Gsub n :=
  G.inducedChainLaw_ae_mem hG (E.nonempty n) hz

lemma inducedStepsOn (n : ℕ) : StepsOn (E.inducedKernel hG n) G.toSimpleGraph (E.Gsub n) :=
  G.inducedStepsOn hG (E.nonempty n) (E.connected n)

/-- **Remark 3.1**: `Ỹⁿ` is an irreducible Markov chain on the finite state space `VGₙ`
(`Kernel.IsIrreducible` with respect to the counting measure on `VGₙ`). -/
theorem inducedKernel_isIrreducible (n : ℕ) :
    Kernel.IsIrreducible (Measure.count.restrict (↑(E.Gsub n) : Set V))
      (E.inducedKernel hG n) :=
  G.inducedKernel_isIrreducible hG (E.nonempty n) (E.connected n)

/-- **Lemma 3.3.**  The coarsening (3.9) of `Y^{n+1}` along `VGₙ` has the law of `Yⁿ`:
`(P^{n+1}_z).map (coarsenPath VGₙ) = Pⁿ_z` for every starting point `z`.  This is the
consistency condition that couples the chains `{Yⁿ}` (Lemma 3.4 / `IndexSet.Consistent`). -/
theorem chainLaw_map_coarsenPath (n : ℕ) (z : V) :
    (E.chainLaw hG (n + 1) z).map (IndexSet.coarsenPath (↑(E.Gsub n) : Set V)) =
      E.chainLaw hG n z :=
  G.chainLaw_map_coarsenPath hG (E.nonempty n) (E.nonempty (n + 1))
    (E.subset_of_le (Nat.le_succ n)) (E.connected (n + 1)) z

end Exhaustion

end ConductanceGraph

end ReflectedWalk
