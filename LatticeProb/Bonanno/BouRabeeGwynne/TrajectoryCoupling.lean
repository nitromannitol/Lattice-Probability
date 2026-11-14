/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TrajectoryCoupling at commit fdb5cad;
   local lint settings are adjusted. -/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! Pushforwards of actual Ionescu–Tulcea trajectory laws. The transition
intertwining is checked on the entire finite history, so the conclusion gives
joint path marginals, not merely the marginal at each individual time. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace BouRabeeGwynne

section ProductMap

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

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

namespace TrajectoryCoupling

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Apply the spatial map at every position of a finite history. -/
def prefixMap (f : X → Y) (n : ℕ) (h : Finset.Iic n → X) : Finset.Iic n → Y :=
  fun i => f (h i)

@[fun_prop] lemma measurable_prefixMap {f : X → Y} (hf : Measurable f) (n : ℕ) :
    Measurable (prefixMap f n) := by
  exact Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)

/-- Append one state to a genuine finite history. -/
def append (n : ℕ) (p : (Finset.Iic n → X) × X) : Finset.Iic (n + 1) → X :=
  fun i => if hi : i.val ≤ n then p.1 ⟨i.val, Finset.mem_Iic.mpr hi⟩ else p.2

@[fun_prop] lemma measurable_append (n : ℕ) : Measurable (append (X := X) n) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.val ≤ n
  · simp only [append, hi, ↓reduceDIte]
    exact (measurable_fst : Measurable
      (Prod.fst : (Finset.Iic n → X) × X → (Finset.Iic n → X))).eval
  · simpa only [append, hi, ↓reduceDIte] using
      (measurable_snd : Measurable (Prod.snd : (Finset.Iic n → X) × X → X))

lemma append_restrict (n : ℕ) (ω : ℕ → X) :
    append n (frestrictLe n ω, ω (n + 1)) = frestrictLe (n + 1) ω := by
  funext i
  by_cases hi : i.val ≤ n
  · simp [append, hi, frestrictLe_apply]
  · have heq : i.val = n + 1 := by have := Finset.mem_Iic.mp i.property; omega
    simp [append, hi, frestrictLe_apply, heq]

lemma prefixMap_append (f : X → Y) (n : ℕ) :
    prefixMap f (n + 1) ∘ append n =
      append n ∘ Prod.map (prefixMap f n) f := by
  funext p i
  by_cases hi : i.val ≤ n <;> simp [prefixMap, append, hi]

variable (μ : Measure X) [IsProbabilityMeasure μ]
  (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)]

lemma prefix_zero :
    (Kernel.trajMeasure (X := fun _ => X) μ κ).map (frestrictLe 0) = μ.map (fun x _ => x) := by
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  rfl

lemma prefix_succ (n : ℕ) :
    (Kernel.trajMeasure (X := fun _ => X) μ κ).map (frestrictLe (n + 1)) =
      ((Kernel.trajMeasure (X := fun _ => X) μ κ).map (frestrictLe n) ⊗ₘ κ n).map (append n) := by
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.map_map (measurable_append n) (by fun_prop)]
  congr 1
  funext ω
  exact (append_restrict n ω).symm

variable (ν : Measure Y) [IsProbabilityMeasure ν]
  (η : (n : ℕ) → Kernel (Finset.Iic n → Y) Y) [∀ n, IsMarkovKernel (η n)]
  (f : X → Y) (hf : Measurable f)
  (hinit : μ.map f = ν)
  (hstep : ∀ n h, (κ n h).map f = η n (prefixMap f n h))

include hf hinit hstep in
/-- The full joint finite-history marginal is preserved by an intertwining of
initial laws and history-dependent transition kernels. -/
lemma map_prefix_law (n : ℕ) :
    ((Kernel.trajMeasure (X := fun _ => X) μ κ).map (frestrictLe n)).map (prefixMap f n) =
      (Kernel.trajMeasure (X := fun _ => Y) ν η).map (frestrictLe n) := by
  induction n with
  | zero =>
    rw [prefix_zero, prefix_zero, Measure.map_map (measurable_prefixMap hf 0) (by fun_prop),
      ← hinit, Measure.map_map (by fun_prop) hf]
    rfl
  | succ n ih =>
    rw [prefix_succ, prefix_succ,
      Measure.map_map (measurable_prefixMap hf (n + 1)) (measurable_append n),
      prefixMap_append,
      ← Measure.map_map (measurable_append n) ((measurable_prefixMap hf n).prodMap hf),
      compProd_map_prod_of_kernel_map _ _ _ _ _ (measurable_prefixMap hf n) hf (hstep n), ih]

/-- Equality of all prefix pushforwards determines a finite measure on the
entire sequence space, by uniqueness on the measurable cylinder sets. -/
lemma measure_eq_of_prefix_eq (ρ σ : Measure (ℕ → Y)) [IsFiniteMeasure ρ]
    (hprefix : ∀ n, ρ.map (frestrictLe n) = σ.map (frestrictLe n)) : ρ = σ := by
  have hall (I : Finset ℕ) : ρ.map I.restrict = σ.map I.restrict := by
    let q : (Finset.Iic (I.sup id) → Y) → (I → Y) :=
      fun h i => h ⟨i.val, I.subset_Iic_sup_id i.property⟩
    have hq : Measurable q := Measurable.of_eval fun _ => measurable_pi_apply _
    have heq : q ∘ frestrictLe (π := fun _ : ℕ => Y) (I.sup id) =
        I.restrict (π := fun _ : ℕ => Y) := rfl
    calc
      ρ.map I.restrict = (ρ.map (frestrictLe (I.sup id))).map q := by
        rw [Measure.map_map hq (measurable_frestrictLe _), heq]
      _ = (σ.map (frestrictLe (I.sup id))).map q := congrArg (fun m => m.map q) (hprefix _)
      _ = σ.map I.restrict := by rw [Measure.map_map hq (measurable_frestrictLe _), heq]
  apply MeasureTheory.ext_of_generate_finite (measurableCylinders (fun _ : ℕ => Y))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro s hs
    obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders _).mp hs
    rw [cylinder, ← Measure.map_apply (by fun_prop) ht,
      ← Measure.map_apply (by fun_prop) ht, hall]
  · have hu := congrArg (fun m : Measure (Finset.Iic 0 → Y) => m univ) (hprefix 0)
    simpa only [Measure.map_apply (measurable_frestrictLe 0) MeasurableSet.univ,
      preimage_univ] using hu

include hf hinit hstep in
/-- Exact whole-trajectory pushforward. In particular every finite skeleton
has its actual joint path law as marginal of the coupled trajectory. -/
lemma map_trajectory_law :
    (Kernel.trajMeasure (X := fun _ => X) μ κ).map (fun ω n => f (ω n)) = Kernel.trajMeasure (X := fun _ => Y) ν η := by
  apply measure_eq_of_prefix_eq
  intro n
  have hpath : Measurable (fun ω : ℕ → X => fun k => f (ω k)) :=
    Measurable.of_eval fun k => hf.comp (measurable_pi_apply k)
  rw [Measure.map_map (measurable_frestrictLe n) hpath]
  have heq : frestrictLe n ∘ (fun (ω : ℕ → X) k => f (ω k)) =
      prefixMap f n ∘ frestrictLe n := rfl
  rw [heq, ← Measure.map_map (measurable_prefixMap hf n) (measurable_frestrictLe n)]
  exact map_prefix_law μ κ ν η f hf hinit hstep n

end TrajectoryCoupling
end BouRabeeGwynne
