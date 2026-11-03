/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Markov.Chain at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HistKernel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HistKernelIsMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.ChainLaw

/-!
# Time-homogeneous Markov chains on path space: law, finite-dimensional distributions and the
Markov property at deterministic times

A Markov kernel `κ : Kernel S S` and a starting point `z : S` determine, by the Ionescu–Tulcea
theorem (`ProbabilityTheory.Kernel.trajMeasure`), the law `chainLaw κ z` of the chain on the
path space `ℕ → S`. This file proves:

* `chainLaw κ z` is a probability measure and `ω 0 = z` almost surely (`chainLaw_ae_start`);
* the finite-dimensional distributions (`chainLaw_cylinder`, and the decidability-free cases
  `chainLaw_cylinder_of_eq`, `chainLaw_cylinder_of_ne`):
  `P_z(ω i = s i, i ≤ n) = 1[s 0 = z] ∏_{i<n} κ (s i) {s (i+1)}`;
* the **Markov property at a deterministic time `n`**: for `F` determined by the coordinates
  `≤ n` and measurable `B`, `P_z(F ∩ {θ_n ω ∈ B}) = ∫⁻_F P_{ω n}(B) dP_z`
  (`chainLaw_inter_walkShift_preimage`, `chainLaw_inter_walkShift_preimage_of_piLE`), with the
  `lintegral` version `setLIntegral_walkShift` and the kernel version
  `chainLaw_restrict_map_walkShift`; one step from a fixed state:
  `P_z(ω n = u, ω (n+1) = v) = P_z(ω n = u) κ u {v}` (`chainLaw_eval_eq_eval_succ_eq`);
* the first-step decomposition of the whole path (`chainLaw_eq_map_consPath`,
  `chainLaw_apply_eq_lintegral_consPath`): `P_z(E) = ∫ κ(z,dy) P_y(z · ω ∈ E)`.

The chain is built with the history-dependent kernels `histKernel κ n`, which read `κ` off the
last coordinate of a finite history. The definitions `histKernel`, `chainLaw` and the instance `histKernel_isMarkovKernel` are
the declarations in `MatedCRTHarmonic/Frozen/{HistKernel,HistKernelIsMarkov,ChainLaw}.lean`;
this file proves their API.

## Attribution

The finite-history bookkeeping, `chainLaw` and its restart identity are ported (namespaces and
names adapted, no logic changes except where stated) from the repository's
`ReflectedWalk.MarkovChain` block, especially sections `Histories`, `ProductMap`, `Prefixes`,
`Chain`, `StrongMarkovHitting` (first three lemmas) and `ConsPath`; that file in turn adapts
BouRabeeGwynne's `TrajectoryCoupling.lean`, `WalkMemoryless.lean` and `StoppedWalk.lean`.

-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace MatedCRTHarmonic.Markov

/-! ### Finite histories -/

section Histories

variable {S : Type*}

/-- Append one state to a finite history. -/
def histAppend (n : ℕ) (p : (Finset.Iic n → S) × S) : Finset.Iic (n + 1) → S :=
  fun i => if hi : i.val ≤ n then p.1 ⟨i.val, Finset.mem_Iic.mpr hi⟩ else p.2

lemma histAppend_restrict (n : ℕ) (ω : ℕ → S) :
    histAppend n (frestrictLe n ω, ω (n + 1)) = frestrictLe (n + 1) ω := by
  funext i
  by_cases hi : i.val ≤ n
  · simp [histAppend, hi, frestrictLe_apply]
  · have heq : i.val = n + 1 := by have := Finset.mem_Iic.mp i.property; omega
    simp [histAppend, frestrictLe_apply, heq]

/-- The suffix of a finite history starting at time `a`. -/
def shiftPrefix (a k : ℕ) (h : Finset.Iic (a + k) → S) : Finset.Iic k → S :=
  fun i => h ⟨a + i.val, Finset.mem_Iic.mpr
    (Nat.add_le_add_left (Finset.mem_Iic.mp i.property) a)⟩

lemma shiftPrefix_zero (a : ℕ) (h : Finset.Iic a → S) :
    shiftPrefix a 0 h = fun _ => h ⟨a, Finset.mem_Iic.mpr le_rfl⟩ := by
  funext i
  have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
  simp [shiftPrefix, hi]

lemma shiftPrefix_histAppend (a k : ℕ) :
    shiftPrefix (S := S) a (k + 1) ∘ histAppend (a + k) =
      histAppend k ∘ Prod.map (shiftPrefix a k) id := by
  funext p i
  by_cases hi : i.val ≤ k
  · have hai : a + i.val ≤ a + k := Nat.add_le_add_left hi a
    simp [shiftPrefix, histAppend, hi, hai]
  · have hai : ¬ a + i.val ≤ a + k := by omega
    simp [shiftPrefix, histAppend, hi, hai]

/-- The path shifted by `n` steps, `(θ_n ω)_k = ω_{n+k}`. -/
def walkShift (n : ℕ) (ω : ℕ → S) : ℕ → S := fun k => ω (n + k)

@[simp] lemma walkShift_apply (n k : ℕ) (ω : ℕ → S) : walkShift n ω k = ω (n + k) := rfl

@[simp] lemma walkShift_zero (ω : ℕ → S) : walkShift 0 ω = ω := by
  funext k
  simp [walkShift]

lemma walkShift_walkShift (m n : ℕ) (ω : ℕ → S) :
    walkShift m (walkShift n ω) = walkShift (n + m) ω := by
  funext k
  simp [walkShift, Nat.add_assoc]

/-- The last coordinate of a finite history of length `n`. -/
abbrev lastCoord (n : ℕ) (h : Finset.Iic n → S) : S := h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

variable [MeasurableSpace S]

lemma measurable_histAppend (n : ℕ) : Measurable (histAppend (S := S) n) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.val ≤ n
  · simp only [histAppend, hi, ↓reduceDIte]
    exact (measurable_fst : Measurable
      (Prod.fst : (Finset.Iic n → S) × S → (Finset.Iic n → S))).eval
  · simpa only [histAppend, hi, ↓reduceDIte] using
      (measurable_snd : Measurable (Prod.snd : (Finset.Iic n → S) × S → S))

lemma measurable_shiftPrefix (a k : ℕ) : Measurable (shiftPrefix (S := S) a k) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

lemma measurable_walkShift (n : ℕ) : Measurable (walkShift (S := S) n) :=
  Measurable.of_eval fun k => measurable_pi_apply (n + k)

lemma measurable_lastCoord (n : ℕ) : Measurable (lastCoord (S := S) n) := measurable_pi_apply _

/-- Equality of all finite-prefix pushforwards determines a finite measure on sequence space
(cylinder uniqueness). -/
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

/-- Pushforward of a `compProd` along a product map intertwining the kernels. -/
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

/-! ### Prefix laws of Ionescu–Tulcea trajectories -/

section Prefixes

variable {S : Type*} [MeasurableSpace S]
  (κ : (n : ℕ) → Kernel (Finset.Iic n → S) S) [∀ n, IsMarkovKernel (κ n)]

/-- The prefix of length `n + 1` of a trajectory law is obtained from the prefix of length `n`
by one more transition. -/
lemma prefix_succ (μ : Measure S) [IsProbabilityMeasure μ] (n : ℕ) :
    (Kernel.trajMeasure (X := fun _ => S) μ κ).map (frestrictLe (n + 1)) =
      ((Kernel.trajMeasure (X := fun _ => S) μ κ).map (frestrictLe n) ⊗ₘ κ n).map
        (histAppend n) := by
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.map_map (measurable_histAppend n) (by fun_prop)]
  congr 1
  funext ω
  exact (histAppend_restrict n ω).symm

/-- The continuation kernel started from a history `h` has `h` as its prefix. -/
lemma prefix_at_start_traj (a : ℕ) (h : Finset.Iic a → S) :
    (Kernel.traj (X := fun _ => S) κ a h).map (frestrictLe a) = Measure.dirac h := by
  have hp := congrArg (fun k : Kernel (Finset.Iic a → S) (Finset.Iic a → S) => k h)
    (Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := κ) a a)
  simpa only [Kernel.map_apply _ (measurable_frestrictLe a),
    Kernel.partialTraj_self, Kernel.id_apply] using hp

/-- One more transition of the continuation kernel. -/
lemma prefix_succ_traj (a b : ℕ) (hab : a ≤ b) (h : Finset.Iic a → S) :
    (Kernel.traj (X := fun _ => S) κ a h).map (frestrictLe (b + 1)) =
      ((Kernel.traj (X := fun _ => S) κ a h).map (frestrictLe b) ⊗ₘ κ b).map
        (histAppend b) := by
  have hp := congrArg (fun k : Kernel (Finset.Iic a → S) (Finset.Iic b → S) => k h)
    (Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := κ) a b)
  simp only [Kernel.map_apply _ (measurable_frestrictLe b)] at hp
  have hs := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => S) (κ := κ) (x₀ := h) hab
  rw [← hp] at hs
  rw [hs, Measure.map_map (measurable_histAppend b) (by fun_prop)]
  congr 1
  funext ω
  exact (histAppend_restrict b ω).symm

end Prefixes

/-! ### The chain generated by a one-step Markov kernel -/

section Chain

variable {S : Type*} [MeasurableSpace S]

/-! The history-dependent kernel `histKernel κ n` (the next state is drawn from `κ` at the last
coordinate of the history), its `IsMarkovKernel` instance `histKernel_isMarkovKernel`, and the
chain law `chainLaw κ z = Kernel.trajMeasure (dirac z) (histKernel κ)` (Ionescu–Tulcea) are the
frozen definitions `MatedCRTHarmonic/Frozen/{HistKernel,HistKernelIsMarkov,ChainLaw}.lean`
-/

variable (κ : Kernel S S) [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
lemma histKernel_apply (n : ℕ) (h : Finset.Iic n → S) : histKernel κ n h = κ (lastCoord n h) :=
  rfl

instance chainLaw_isProbabilityMeasure (z : S) : IsProbabilityMeasure (chainLaw κ z) := by
  unfold chainLaw
  infer_instance

/-- The initial history is the starting point. -/
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

/-- `ω 0 = z` almost surely under `P_z`. -/
lemma chainLaw_ae_start [MeasurableSingletonClass S] (z : S) :
    ∀ᵐ ω ∂chainLaw κ z, ω 0 = z := by
  have h : ∀ᵐ y ∂(chainLaw κ z).map (fun ω => ω 0), y = z := by
    rw [chainLaw_marginal_zero]
    exact (ae_dirac_iff (measurableSet_singleton z)).mpr rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h

/-- The Markov property at a deterministic time, joint form: the law of (history up to `n`,
state at `n + 1`) is the prefix law composed with `κ`. -/
lemma chainLaw_history_next (z : S) (n : ℕ) :
    (chainLaw κ z).map (frestrictLe n) ⊗ₘ histKernel κ n =
      (chainLaw κ z).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- One-step marginals evolve by `κ`. -/
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

/-- The law of `ω 1` under `P_z` is `κ z`. -/
lemma chainLaw_marginal_one (z : S) : (chainLaw κ z).map (fun ω => ω 1) = κ z := by
  rw [chainLaw_marginal_succ, chainLaw_marginal_zero]
  exact Measure.dirac_bind κ.measurable z

/-- The chain law as a Markov kernel in the starting point. -/
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

/-- `z ↦ P_z(B)` is measurable. -/
lemma measurable_chainLaw_apply {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    Measurable fun z => chainLaw κ z B := by
  simp_rw [← pathKernel_apply]
  exact Kernel.measurable_coe _ hB

/-- `z ↦ E_z[f]` is measurable for measurable `f ≥ 0`. -/
lemma measurable_lintegral_chainLaw {f : (ℕ → S) → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun z => ∫⁻ ω, f ω ∂chainLaw κ z := by
  simp_rw [← pathKernel_apply]
  exact hf.lintegral_kernel

/-- A fresh chain started from the last vertex of a history. -/
noncomputable def restartKernel (a : ℕ) : Kernel (Finset.Iic a → S) (ℕ → S) :=
  (pathKernel κ).comap (lastCoord a) (measurable_lastCoord a)

/-- Each finite future prefix under the continuation kernel has the law of a fresh chain
started at the last vertex of the history. -/
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
      Measure.map_map (measurable_shiftPrefix a (k + 1)) (measurable_histAppend (a + k)),
      shiftPrefix_histAppend,
      ← Measure.map_map (measurable_histAppend k)
        ((measurable_shiftPrefix a k).prodMap measurable_id),
      compProd_map_prod_of_kernel_map _ _ _ _ _ (measurable_shiftPrefix a k) measurable_id hmap,
      ih]
    rfl

/-- Whole-path restart at a deterministic time under the continuation kernel. -/
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
continuation kernel (from Mathlib's `Kernel.traj_comp_partialTraj`). -/
lemma chainLaw_eq_traj_comp_prefix (z : S) (a : ℕ) :
    chainLaw κ z =
      Kernel.traj (X := fun _ => S) (histKernel κ) a ∘ₘ (chainLaw κ z).map (frestrictLe a) := by
  simp only [chainLaw, Kernel.trajMeasure]
  rw [Measure.map_comp _ _ (measurable_frestrictLe a), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Kernel.traj_comp_partialTraj (Nat.zero_le a)]

/-- **Markov property at a deterministic time**, path form: under `P_z` the shifted path
`θ_a ω` has the law of a fresh chain started from `ω a`. -/
theorem chainLaw_map_walkShift (z : S) (a : ℕ) :
    (chainLaw κ z).map (walkShift a) = pathKernel κ ∘ₘ (chainLaw κ z).map (fun ω => ω a) := by
  conv_lhs => rw [chainLaw_eq_traj_comp_prefix κ z a]
  rw [Measure.map_comp _ _ (measurable_walkShift a), traj_map_walkShift, restartKernel,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, Measure.map_map (measurable_lastCoord a)
      (measurable_frestrictLe a)]
  rfl

end Chain

/-! ### Finite-dimensional distributions -/

section Cylinder

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
  (κ : Kernel S S) [IsMarkovKernel κ]

lemma measurableSet_forall_le_eq (s : ℕ → S) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | ∀ i ≤ n, ω i = s i} := by
  have : {ω : ℕ → S | ∀ i ≤ n, ω i = s i} =
      ⋂ i, ⋂ (_ : i ≤ n), (fun ω : ℕ → S => ω i) ⁻¹' {s i} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurable_pi_apply i (measurableSet_singleton _)

open scoped Classical in
/-- **Finite-dimensional distributions** of the chain:
`P_z(ω i = s i for all i ≤ n) = 1[s 0 = z] · ∏_{i<n} κ (s i) {s (i+1)}`. -/
theorem chainLaw_cylinder (z : S) (s : ℕ → S) (n : ℕ) :
    chainLaw κ z {ω | ∀ i ≤ n, ω i = s i} =
      (if s 0 = z then 1 else 0) * ∏ i ∈ Finset.range n, κ (s i) {s (i + 1)} := by
  induction n with
  | zero =>
    have hset : {ω : ℕ → S | ∀ i ≤ 0, ω i = s i} = (fun ω : ℕ → S => ω 0) ⁻¹' {s 0} := by
      ext ω
      simp
    rw [hset, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      chainLaw_marginal_zero, Measure.dirac_apply' _ (measurableSet_singleton _),
      Finset.prod_range_zero, mul_one]
    by_cases h : s 0 = z
    · simp [h]
    · have : z ∉ ({s 0} : Set S) := fun hz => h (Set.mem_singleton_iff.mp hz).symm
      simp [h, this]
  | succ n ih =>
    -- the event is a rectangle in (history up to `n`, state at `n + 1`)
    let C : Set (Finset.Iic n → S) := {h | ∀ i, h i = s i}
    have hC : MeasurableSet C := by
      have : C = ⋂ i, (fun h : Finset.Iic n → S => h i) ⁻¹' {s i} := by
        ext h
        simp [C]
      rw [this]
      exact MeasurableSet.iInter fun i => measurable_pi_apply i (measurableSet_singleton _)
    have hset : {ω : ℕ → S | ∀ i ≤ n + 1, ω i = s i} =
        (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))) ⁻¹' (C ×ˢ {s (n + 1)}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, C,
        frestrictLe_apply]
      constructor
      · intro h
        exact ⟨fun i => h i (Nat.le_succ_of_le (Finset.mem_Iic.mp i.2)), h (n + 1) le_rfl⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_or_ge i (n + 1) with hlt | hge
        · exact h1 ⟨i, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hlt)⟩
        · have : i = n + 1 := le_antisymm hi hge
          subst this
          exact h2
    have hprefix : (chainLaw κ z).map (frestrictLe n) C =
        chainLaw κ z {ω | ∀ i ≤ n, ω i = s i} := by
      rw [Measure.map_apply (measurable_frestrictLe n) hC]
      congr 1
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, C, frestrictLe_apply]
      exact ⟨fun h i hi => h ⟨i, Finset.mem_Iic.mpr hi⟩, fun h i => h i (Finset.mem_Iic.mp i.2)⟩
    have hconst : ∀ h ∈ C, histKernel κ n h {s (n + 1)} = κ (s n) {s (n + 1)} := by
      intro h hh
      rw [histKernel_apply, lastCoord, hh]
    rw [hset, ← Measure.map_apply (by fun_prop) (hC.prod (measurableSet_singleton _)),
      ← chainLaw_history_next, Measure.compProd_apply_prod hC (measurableSet_singleton _),
      setLIntegral_congr_fun hC hconst, setLIntegral_const, hprefix, ih,
      Finset.prod_range_succ]
    ring

/-- Finite-dimensional distributions for a history starting at `z`:
`P_z(ω i = s i for all i ≤ n) = ∏_{i<n} κ (s i) {s (i+1)}`. -/
theorem chainLaw_cylinder_of_eq (z : S) (s : ℕ → S) (n : ℕ) (h : s 0 = z) :
    chainLaw κ z {ω | ∀ i ≤ n, ω i = s i} = ∏ i ∈ Finset.range n, κ (s i) {s (i + 1)} := by
  classical
  rw [chainLaw_cylinder]
  simp [h]

/-- The law of the first `n + 1` coordinates is concentrated on histories starting at `z`. -/
lemma chainLaw_cylinder_of_ne (z : S) (s : ℕ → S) (n : ℕ) (h : s 0 ≠ z) :
    chainLaw κ z {ω | ∀ i ≤ n, ω i = s i} = 0 := by
  classical
  rw [chainLaw_cylinder]
  simp [h]

end Cylinder

/-! ### The Markov property at a deterministic time, restricted to past events -/

section MarkovRestrict

variable {S : Type*} [MeasurableSpace S] (κ : Kernel S S) [IsMarkovKernel κ]

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

/-- The continuation kernel started from the history `h` is concentrated on paths with
prefix `h`. -/
lemma traj_fiber_compl [MeasurableSingletonClass S] (j : ℕ) (h : Finset.Iic j → S) :
    Kernel.traj (X := fun _ => S) (histKernel κ) j h (frestrictLe j ⁻¹' {h})ᶜ = 0 := by
  rw [← Set.preimage_compl,
    ← Measure.map_apply (measurable_frestrictLe j) (measurableSet_singleton h).compl,
    prefix_at_start_traj, Measure.dirac_apply' _ (measurableSet_singleton h).compl]
  simp

/-- The Markov property at a deterministic time `j`, restricted to a cylinder event
`frestrictLe j ⁻¹' s` of the history up to time `j`, kernel form. -/
lemma chainLaw_restrict_map_walkShift [MeasurableSingletonClass S] (z : S) (j : ℕ)
    {s : Set (Finset.Iic j → S)} (hs : MeasurableSet s) :
    ((chainLaw κ z).restrict (frestrictLe j ⁻¹' s)).map (walkShift j) =
      pathKernel κ ∘ₘ ((chainLaw κ z).restrict (frestrictLe j ⁻¹' s)).map (fun ω => ω j) := by
  have hres : (chainLaw κ z).restrict (frestrictLe j ⁻¹' s) =
      Kernel.traj (X := fun _ => S) (histKernel κ) j ∘ₘ
        ((chainLaw κ z).map (frestrictLe j)).restrict s := by
    conv_lhs => rw [chainLaw_eq_traj_comp_prefix κ z j]
    exact comp_restrict_preimage _ _ (measurable_frestrictLe j) (traj_fiber_compl κ j) hs
  conv_lhs => rw [hres]
  rw [Measure.map_comp _ _ (measurable_walkShift j), traj_map_walkShift, restartKernel,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, Measure.restrict_map (measurable_frestrictLe j) hs,
    Measure.map_map (measurable_lastCoord j) (measurable_frestrictLe j)]
  rfl

/-- **Markov property at a deterministic time**, `lintegral` form: for an event
`F = frestrictLe n ⁻¹' s` of the coordinates `≤ n` and measurable `f ≥ 0`,
`∫⁻_F f(θ_n ω) dP_z = ∫⁻_F E_{ω n}[f] dP_z`. -/
theorem setLIntegral_walkShift [MeasurableSingletonClass S] (z : S) (n : ℕ)
    {s : Set (Finset.Iic n → S)} (hs : MeasurableSet s) {f : (ℕ → S) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ ω in frestrictLe n ⁻¹' s, f (walkShift n ω) ∂chainLaw κ z =
      ∫⁻ ω in frestrictLe n ⁻¹' s, (∫⁻ ω', f ω' ∂chainLaw κ (ω n)) ∂chainLaw κ z := by
  rw [← lintegral_map hf (measurable_walkShift n), chainLaw_restrict_map_walkShift κ z n hs,
    Measure.lintegral_bind (pathKernel κ).aemeasurable hf.aemeasurable,
    lintegral_map (hf.lintegral_kernel (κ := pathKernel κ)) (measurable_pi_apply n)]
  simp_rw [pathKernel_apply]

/-- **Markov property at a deterministic time**, set form: for an event
`F = frestrictLe n ⁻¹' s` of the coordinates `≤ n` and measurable `B`,
`P_z(F ∩ {θ_n ω ∈ B}) = ∫⁻_F P_{ω n}(B) dP_z`. -/
theorem chainLaw_inter_walkShift_preimage [MeasurableSingletonClass S] (z : S) (n : ℕ)
    {s : Set (Finset.Iic n → S)} (hs : MeasurableSet s) {B : Set (ℕ → S)}
    (hB : MeasurableSet B) :
    chainLaw κ z (frestrictLe n ⁻¹' s ∩ walkShift n ⁻¹' B) =
      ∫⁻ ω in frestrictLe n ⁻¹' s, chainLaw κ (ω n) B ∂chainLaw κ z := by
  have h := setLIntegral_walkShift κ z n hs (measurable_one.indicator hB)
  simp only [lintegral_indicator_one hB] at h
  rw [← h, ← lintegral_indicator_one ((measurable_frestrictLe n hs).inter
    (measurable_walkShift n hB)), ← lintegral_indicator (measurable_frestrictLe n hs)]
  refine lintegral_congr fun ω => ?_
  by_cases h1 : ω ∈ frestrictLe n ⁻¹' s <;> by_cases h2 : walkShift n ω ∈ B <;>
    simp [Set.indicator, h1, h2]

/-- An event of `Filtration.piLE n` (determined by the coordinates `≤ n`) is a cylinder over
the history up to time `n`. -/
lemma exists_frestrictLe_preimage_of_piLE {n : ℕ} {F : Set (ℕ → S)}
    (hF : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] F) :
    ∃ s : Set (Finset.Iic n → S), MeasurableSet s ∧ frestrictLe n ⁻¹' s = F := by
  rw [Filtration.piLE_eq_comap_frestrictLe] at hF
  exact hF

/-- **Markov property at a deterministic time** for an event `F` of the canonical filtration
`Filtration.piLE n`: `P_z(F ∩ {θ_n ω ∈ B}) = ∫⁻_F P_{ω n}(B) dP_z`. -/
theorem chainLaw_inter_walkShift_preimage_of_piLE [MeasurableSingletonClass S] (z : S) (n : ℕ)
    {F : Set (ℕ → S)} (hF : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] F)
    {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    chainLaw κ z (F ∩ walkShift n ⁻¹' B) = ∫⁻ ω in F, chainLaw κ (ω n) B ∂chainLaw κ z := by
  obtain ⟨s, hs, rfl⟩ := exists_frestrictLe_preimage_of_piLE hF
  exact chainLaw_inter_walkShift_preimage κ z n hs hB

/-- `lintegral` form of the Markov property for an event of `Filtration.piLE n`. -/
theorem setLIntegral_walkShift_of_piLE [MeasurableSingletonClass S] (z : S) (n : ℕ)
    {F : Set (ℕ → S)} (hF : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] F)
    {f : (ℕ → S) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in F, f (walkShift n ω) ∂chainLaw κ z =
      ∫⁻ ω in F, (∫⁻ ω', f ω' ∂chainLaw κ (ω n)) ∂chainLaw κ z := by
  obtain ⟨s, hs, rfl⟩ := exists_frestrictLe_preimage_of_piLE hF
  exact setLIntegral_walkShift κ z n hs hf

/-- One step from a fixed state: `P_z(ω n = u, ω (n+1) = v) = P_z(ω n = u) · κ u {v}`. -/
theorem chainLaw_eval_eq_eval_succ_eq [MeasurableSingletonClass S] (z : S) (n : ℕ) (u v : S) :
    chainLaw κ z {ω | ω n = u ∧ ω (n + 1) = v} = chainLaw κ z {ω | ω n = u} * κ u {v} := by
  have hF : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] {ω : ℕ → S | ω n = u} := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    refine ⟨{h | h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = u},
      (measurableSet_singleton u).preimage (measurable_pi_apply _), ?_⟩
    ext ω
    simp [frestrictLe_apply]
  have hB : MeasurableSet {ω : ℕ → S | ω 1 = v} :=
    (measurableSet_singleton v).preimage (measurable_pi_apply 1)
  have hF' : MeasurableSet {ω : ℕ → S | ω n = u} :=
    (measurableSet_singleton u).preimage (measurable_pi_apply n)
  have hset : {ω : ℕ → S | ω n = u ∧ ω (n + 1) = v} =
      {ω | ω n = u} ∩ walkShift n ⁻¹' {ω | ω 1 = v} := by
    ext ω
    simp
  have hone : ∀ y, chainLaw κ y {ω | ω 1 = v} = κ y {v} := fun y => by
    rw [← chainLaw_marginal_one κ y, Measure.map_apply (measurable_pi_apply 1)
      (measurableSet_singleton v)]
    rfl
  rw [hset, chainLaw_inter_walkShift_preimage_of_piLE κ z n hF hB, mul_comm,
    ← setLIntegral_const]
  refine setLIntegral_congr_fun hF' fun ω hω => ?_
  rw [hone]
  rw [Set.mem_ofPred_eq] at hω
  rw [hω]

end MarkovRestrict

/-! ### Prepending a state: the first-step decomposition of the path -/

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

@[simp] lemma walkShift_one_consPath (z : S) (q : ℕ → S) : walkShift 1 (consPath z q) = q := by
  funext k
  rw [walkShift_apply, Nat.add_comm]
  rfl

variable [MeasurableSpace S]

lemma measurable_consPath (z : S) : Measurable (consPath z) := by
  refine Measurable.of_eval fun k => ?_
  cases k with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

variable (κ : Kernel S S) [IsMarkovKernel κ] [MeasurableSingletonClass S]

/-- The chain law as the law of `(z, θ_1 ω)`: `P_z = (pathKernel ∘ₘ κ z).map (consPath z)`. -/
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

/-- **First-step decomposition of the path law**: for measurable `E`,
`P_z(E) = ∫ κ(z, dy) P_y(consPath z ω ∈ E)`. -/
theorem chainLaw_apply_eq_lintegral_consPath (z : S) {E : Set (ℕ → S)} (hE : MeasurableSet E) :
    chainLaw κ z E = ∫⁻ y, chainLaw κ y (consPath z ⁻¹' E) ∂κ z := by
  conv_lhs => rw [chainLaw_eq_map_consPath κ z]
  rw [Measure.map_apply (measurable_consPath z) hE,
    Measure.bind_apply (measurable_consPath z hE) (pathKernel κ).aemeasurable]
  simp_rw [pathKernel_apply]

/-- First-step decomposition on a countable state space:
`P_z(E) = ∑' y, κ z {y} · P_y(consPath z ω ∈ E)`. -/
theorem chainLaw_apply_eq_tsum_consPath [Countable S] (z : S) {E : Set (ℕ → S)}
    (hE : MeasurableSet E) :
    chainLaw κ z E = ∑' y, κ z {y} * chainLaw κ y (consPath z ⁻¹' E) := by
  rw [chainLaw_apply_eq_lintegral_consPath κ z hE, lintegral_countable']
  simp_rw [mul_comm]

/-- First-step decomposition, `lintegral` form: `E_z[f] = ∫ κ(z, dy) E_y[f(z · ω)]`. -/
theorem lintegral_chainLaw_eq_consPath (z : S) {f : (ℕ → S) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂chainLaw κ z = ∫⁻ y, ∫⁻ ω, f (consPath z ω) ∂chainLaw κ y ∂κ z := by
  conv_lhs => rw [chainLaw_eq_map_consPath κ z]
  rw [lintegral_map hf (measurable_consPath z),
    Measure.lintegral_bind (pathKernel κ).aemeasurable
      (f := fun ω => f (consPath z ω)) (hf.comp (measurable_consPath z)).aemeasurable]
  simp_rw [pathKernel_apply]

end ConsPath

end MatedCRTHarmonic.Markov
