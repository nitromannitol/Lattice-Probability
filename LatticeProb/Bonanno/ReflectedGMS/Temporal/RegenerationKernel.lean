/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.RegenerationKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationCoding
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedBallEnergyGeometry
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The two-sided rooted laws as a kernel in the environment (`p:lem:regeninvariant`, milestone 1)

`Temporal/TwoSidedRegenerationCoding` defines, environment by environment, the two-sided rooted
law `rootedLaw G e` on the environment-independent coding `TwoSidedCoding`.  The consumer
(`Limit/BracketLLNDisintegratedWeld`, via `Temporal/RegenerativeInvarianceReduction`) needs these
laws as a **kernel** `Kernel Code.Env TwoSidedCoding`, i.e. measurable in the environment — the
manuscript's "measurable trajectory coding" (tex:1345), and the open part of the kernel.  This
module reduces that measurability to ONE named input and builds the kernel from it.

## The reduction

* `measurable_of_measurable_vertexCylinder` — a family of probability laws on the trajectory
  space `Trajectory ℕ` is measurable in its parameter as soon as the masses of the vertex
  cylinders `{x | x tᵢ = some gᵢ, i ∈ I}` are (π-λ on the generating π-system
  `ReflectedWalk.Theorem16.vertexCylinders`).
* `measurable_walkMass` / `measurable_slotLaw_vertexCylinder` — the cylinder masses of the
  forward label law are measurable as soon as the **transition function** of the area walk is:
  `slotTransition G n t m e = P_e^{H_n}(X_t = H_m)`, gated by the admissible set `G` and vanishing
  off active slots.  This is the Chapman–Kolmogorov recursion
  `ReflectedWalk.Theorem16.fdd_insert_max` (property (iv) at the largest prescribed time), run
  along `Finset.induction_on_max`; it needs the Markov property at every environment of `G`, which
  is why the laws are gated by an admissible set (`isReflectedWalk_areaFamily`).

## The kernel

* `slotKernel G hG hwalk hmeas n : Kernel Env (Trajectory ℕ)` — the forward label law from slot
  `n`; `twoSidedSlotKernel` — its two-sided product (`Kernel.prod`); `rootedKernel` — at the root
  cell, through the measurable root label (`measurable_rootLabel`, from
  `Corrector/MarkedBallEnergyGeometry.measurable_rootAt_elim`).  All are Markov kernels, and
  `rootedKernel_apply` identifies the fibre law with `rootedLaw G e`.
* The inputs: `hG : MeasurableSet G`; `hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e` (the
  project's residual clock clause, at every environment of the gate); and the ONE open
  measurability input `hmeas : ∀ n t m, Measurable (slotTransition G n t m)`.
* `liftSubtype` — a Markov kernel concentrated on a subset of its target lifts to that subset as a
  subtype (`Measure.comap` along the inclusion, well defined because the subset has full outer
  measure); this is how the regularity subtypes carrying the random-time shifts and the flow
  are reached from the raw coding without re-proving measurability in the environment.

## Satisfiability (checked) and what is NOT proved

* The three inputs are jointly satisfiable: at `G = ∅` every transition vanishes
  (`slotTransition_empty`, `measurable_slotTransition_empty`) and the kernel is the cemetery
  point mass; the shape check `example` composes `νenv ⊗ₘ rootedKernel …`.
* `hwalk` is satisfiable non-trivially by any `G ⊆ {e | EnvironmentAreaClockAdmissible e}`;
  whether such a `G` of full `νenv`-measure can be chosen measurable is part of the residual.
* **The open residual, exactly:** `hmeas` — the area-clock transition function
  `e ↦ P_e^{H_n}(X_t = H_m)` of the canonical construction is a measurable function of the
  environment on a measurable admissible set `G` of full measure.  Its natural proof is through
  the finite-level approximating chains of Gwynne–Sung Steps 1–2
  (`ReflectedWalk.UniquenessLimit.ApproximatedBy`: the transition is the limit of the
  level-`n` chain transitions, each a function of finitely many conductances), with the
  exhaustion chosen canonically from the labels; the level coupling of the sample law is a
  `condDistrib` (`ReflectedWalk.Coupling.stageKernel`), so nothing measurable in the environment
  can be read off the construction itself.  Not attempted here.

Nothing here certifies `p:lem:regeninvariant`, `p:prop:timeergodic`, `p:lem:bracketlimit`,
`p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.RegenerationKernel

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding

/-! ### 1. A kernel from measurable cylinder masses -/

/-- **Measurability of a family of trajectory laws from its vertex-cylinder masses.**  The vertex
cylinders are a π-system generating the cylinder σ-algebra, and the masses of complements and
disjoint unions of probability laws are measurable functions of those of the pieces. -/
theorem measurable_of_measurable_vertexCylinder {ι : Type*} [MeasurableSpace ι]
    (L : ι → Measure (Trajectory ℕ)) [∀ i, IsProbabilityMeasure (L i)]
    (h : ∀ (I : Finset ℝ≥0) (g : ℝ≥0 → ℕ), Measurable fun i => L i (vertexCylinder I g)) :
    Measurable L := by
  refine Measure.measurable_of_measurable_coe L fun s hs => ?_
  refine MeasurableSpace.induction_on_inter (C := fun s _ => Measurable fun i => L i s)
    generateFrom_vertexCylinders isPiSystem_vertexCylinders ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]
    exact measurable_const
  · rintro t ⟨I, g, rfl⟩
    exact h I g
  · intro t htm hC
    have heq : (fun i => L i tᶜ) = fun i => 1 - L i t := by
      funext i
      rw [measure_compl htm (measure_ne_top _ _), measure_univ]
    rw [heq]
    exact measurable_const.sub hC
  · intro f hdisj hfm hC
    have heq : (fun i => L i (⋃ k, f k)) = fun i => ∑' k, L i (f k) := by
      funext i
      exact measure_iUnion hdisj hfm
    rw [heq]
    exact Measurable.tsum hC

/-! ### 2. Slots, the transition function and the finite-dimensional recursion -/

/-- The set of environments whose code slot `n` carries a cell is measurable. -/
theorem measurableSet_slotPresent (n : ℕ) : MeasurableSet {e : Env | (e.val.1 n).isSome} :=
  ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion))
    Spatial.measurableSet_slotIsSome

/-- The vertex of slot `m` in `e`, `none` for an absent slot. -/
noncomputable def optVertex (e : Env) (m : ℕ) : Option (Vertex e.val) := by
  classical
  exact if h : (e.val.1 m).isSome then some ⟨m, h⟩ else none

theorem optVertex_of_isSome {e : Env} {m : ℕ} (h : (e.val.1 m).isSome) :
    optVertex e m = some ⟨m, h⟩ := by
  unfold optVertex
  rw [dite_eq_left h]

theorem optVertex_of_not {e : Env} {m : ℕ} (h : ¬ (e.val.1 m).isSome) : optVertex e m = none := by
  unfold optVertex
  rw [dite_eq_right h]

theorem map_val_eq_some_iff {e : Env} {m : ℕ} (hm : (e.val.1 m).isSome)
    (x : Option (Vertex e.val)) : x.map Subtype.val = some m ↔ x = optVertex e m := by
  rw [optVertex_of_isSome hm]
  cases x with
  | none => simp
  | some v =>
    constructor
    · intro h
      have hv : v.val = m := by simpa using h
      exact congrArg some (Subtype.ext hv)
    · intro h
      have hv : v = ⟨m, hm⟩ := Option.some_injective _ h
      rw [hv]
      rfl

theorem map_val_ne_some_of_not {e : Env} {m : ℕ} (hm : ¬ (e.val.1 m).isSome)
    (x : Option (Vertex e.val)) : x.map Subtype.val ≠ some m := by
  cases x with
  | none => simp
  | some v =>
    intro h
    have hv : v.val = m := by simpa using h
    exact hm (hv ▸ v.property)

open Classical in
/-- The label cylinder pulled back to the vertex trajectories of `e`: the vertex cylinder with
the slots decoded when every prescribed slot is active, empty otherwise. -/
theorem labelTraj_preimage_vertexCylinder (e : Env) (I : Finset ℝ≥0) (g : ℝ≥0 → ℕ) :
    labelTraj ⁻¹' vertexCylinder I g =
      if ∀ i ∈ I, (e.val.1 (g i)).isSome then
        {x : Trajectory (Vertex e.val) | ∀ i ∈ I, x i = optVertex e (g i)}
      else ∅ := by
  split_ifs with hact
  · ext x
    show (∀ i ∈ I, labelTraj x i = some (g i)) ↔ ∀ i ∈ I, x i = optVertex e (g i)
    exact forall₂_congr fun i hi => map_val_eq_some_iff (hact i hi) (x i)
  · ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hx' : ∀ i ∈ I, labelTraj x i = some (g i) := hx
    obtain ⟨i, hi⟩ := not_forall.1 hact
    obtain ⟨hiI, hni⟩ := not_imp.1 hi
    exact map_val_ne_some_of_not hni (x i) (hx' i hiI)

/-- **The area-clock transition function in the label coding**, gated by `G` and vanishing off
active slots: `slotTransition G n t m e = P_e^{H_n}(X_t = H_m)`. -/
noncomputable def slotTransition (G : Set Env) (n : ℕ) (t : ℝ≥0) (m : ℕ) (e : Env) : ℝ≥0∞ := by
  classical
  exact if h : e ∈ G ∧ (e.val.1 n).isSome ∧ (e.val.1 m).isSome then
    (areaFamily e).transition ⟨n, h.2.1⟩ t ⟨m, h.2.2⟩
  else 0

theorem slotTransition_of_not {G : Set Env} {n : ℕ} {t : ℝ≥0} {m : ℕ} {e : Env}
    (h : ¬ (e ∈ G ∧ (e.val.1 n).isSome ∧ (e.val.1 m).isSome)) :
    slotTransition G n t m e = 0 := by
  unfold slotTransition
  rw [dite_eq_right h]

/-- The Chapman–Kolmogorov factor of `fdd_insert_max`, read in the label coding. -/
theorem elim_transition_eq {G : Set Env} {e : Env} (he : e ∈ G) (a : ℕ) (t : ℝ≥0) (b : ℕ) :
    (optVertex e a).elim 0
        (fun x => (optVertex e b).elim 0 fun y => (areaFamily e).transition x t y)
      = slotTransition G a t b e := by
  unfold slotTransition
  by_cases ha : (e.val.1 a).isSome
  · by_cases hb : (e.val.1 b).isSome
    · rw [optVertex_of_isSome ha, optVertex_of_isSome hb, dite_eq_left ⟨he, ha, hb⟩]
      rfl
    · rw [optVertex_of_isSome ha, optVertex_of_not hb, dite_eq_right (fun h => hb h.2.2)]
      rfl
  · rw [optVertex_of_not ha, dite_eq_right (fun h => ha h.2.1)]
    rfl

/-- The finite-dimensional mass of the area walk from slot `n` prescribing the slots `g` on the
finite time set `I`, gated by `G`. -/
noncomputable def walkMass (G : Set Env) (n : ℕ) (I : Finset ℝ≥0) (g : ℝ≥0 → ℕ) (e : Env) :
    ℝ≥0∞ := by
  classical
  exact if h : e ∈ G ∧ (e.val.1 n).isSome then
    (areaFamily e).P ⟨n, h.2⟩ {ω | ∀ i ∈ I, (areaFamily e).X i ω = optVertex e (g i)}
  else 0

theorem walkMass_of_not {G : Set Env} {n : ℕ} {e : Env} (h : ¬ (e ∈ G ∧ (e.val.1 n).isSome))
    (I : Finset ℝ≥0) (g : ℝ≥0 → ℕ) : walkMass G n I g e = 0 := by
  unfold walkMass
  rw [dite_eq_right h]

theorem walkMass_of_mem {G : Set Env} {n : ℕ} {e : Env} (he : e ∈ G) (hn : (e.val.1 n).isSome)
    (I : Finset ℝ≥0) (g : ℝ≥0 → ℕ) :
    walkMass G n I g e =
      (areaFamily e).P ⟨n, hn⟩ {ω | ∀ i ∈ I, (areaFamily e).X i ω = optVertex e (g i)} := by
  unfold walkMass
  rw [dite_eq_left ⟨he, hn⟩]

theorem walkMass_empty_of_mem {G : Set Env} {n : ℕ} {e : Env} (he : e ∈ G)
    (hn : (e.val.1 n).isSome) (g : ℝ≥0 → ℕ) : walkMass G n ∅ g e = 1 := by
  rw [walkMass_of_mem he hn]
  have hset : {ω : (areaFamily e).Ω |
      ∀ i ∈ (∅ : Finset ℝ≥0), (areaFamily e).X i ω = optVertex e (g i)} = Set.univ := by
    ext ω
    simp
  rw [hset, measure_univ]

/-- One prescribed time: the mass is the transition from the start. -/
theorem walkMass_singleton_of_mem {G : Set Env} {n : ℕ} {e : Env} (he : e ∈ G)
    (hn : (e.val.1 n).isSome)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) (energyMinimizer e)
      (areaFamily e))
    (a : ℝ≥0) (g : ℝ≥0 → ℕ) : walkMass G n {a} g e = slotTransition G n a (g a) e := by
  rw [walkMass_of_mem he hn, ← elim_transition_eq he n a (g a), optVertex_of_isSome hn]
  simp only [Option.elim_some]
  have hset : {ω : (areaFamily e).Ω |
      ∀ i ∈ ({a} : Finset ℝ≥0), (areaFamily e).X i ω = optVertex e (g i)}
      = {ω | (areaFamily e).X a ω = optVertex e (g a)} := by
    ext ω
    simp
  rw [hset]
  cases hga : optVertex e (g a) with
  | none =>
    simp only [Option.elim_none]
    exact measure_none_eq_zero (hwalk ⟨n, hn⟩).2.1 a
  | some y => rfl

/-- **The Chapman–Kolmogorov step** (`fdd_insert_max`) in the label coding. -/
theorem walkMass_insert_of_mem {G : Set Env} {n : ℕ} {e : Env} (he : e ∈ G)
    (hn : (e.val.1 n).isSome)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) (energyMinimizer e)
      (areaFamily e))
    {s : Finset ℝ≥0} (hs : s.Nonempty) {a : ℝ≥0} (ha : ∀ i ∈ s, i < a) (g : ℝ≥0 → ℕ) :
    walkMass G n (insert a s) g e =
      walkMass G n s g e * slotTransition G (g (s.max' hs)) (a - s.max' hs) (g a) e := by
  rw [walkMass_of_mem he hn, walkMass_of_mem he hn, ← elim_transition_eq he]
  exact fdd_insert_max (areaFamily e) (fun x => (hwalk x).2.1)
    (fun z => (hwalk z).2.2.2.2.2.1) ⟨n, hn⟩ hs ha (fun i => optVertex e (g i))

/-- **The finite-dimensional masses are measurable in the environment** once the transition
function is, by induction on the prescribed times (largest first). -/
theorem measurable_walkMass (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m))
    (n : ℕ) (g : ℝ≥0 → ℕ) (I : Finset ℝ≥0) : Measurable (walkMass G n I g) := by
  classical
  have hgate : MeasurableSet {e : Env | e ∈ G ∧ (e.val.1 n).isSome} :=
    hG.inter (measurableSet_slotPresent n)
  induction I using Finset.induction_on_max with
  | empty =>
    have heq : walkMass G n ∅ g
        = {e : Env | e ∈ G ∧ (e.val.1 n).isSome}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext e
      by_cases h : e ∈ G ∧ (e.val.1 n).isSome
      · rw [walkMass_empty_of_mem h.1 h.2,
          Set.indicator_of_mem (show e ∈ {e : Env | e ∈ G ∧ (e.val.1 n).isSome} from h)]
      · rw [walkMass_of_not h,
          Set.indicator_of_notMem (show e ∉ {e : Env | e ∈ G ∧ (e.val.1 n).isSome} from h)]
    rw [heq]
    exact measurable_const.indicator hgate
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · have heq : walkMass G n (insert a ∅) g = slotTransition G n a (g a) := by
        funext e
        rw [Finset.insert_empty]
        by_cases h : e ∈ G ∧ (e.val.1 n).isSome
        · exact walkMass_singleton_of_mem h.1 h.2 (isReflectedWalk_areaFamily e (hwalk e h.1)) a g
        · rw [walkMass_of_not h, slotTransition_of_not (fun h' => h ⟨h'.1, h'.2.1⟩)]
      rw [heq]
      exact hmeas n a (g a)
    · have heq : walkMass G n (insert a s) g = fun e =>
          walkMass G n s g e * slotTransition G (g (s.max' hs)) (a - s.max' hs) (g a) e := by
        funext e
        by_cases h : e ∈ G ∧ (e.val.1 n).isSome
        · exact walkMass_insert_of_mem h.1 h.2 (isReflectedWalk_areaFamily e (hwalk e h.1)) hs
            ha g
        · rw [walkMass_of_not h, walkMass_of_not h, zero_mul]
      rw [heq]
      exact ih.mul (hmeas _ _ _)

/-- **The vertex-cylinder masses of the forward label law are measurable in the environment**,
from the transition function. -/
theorem measurable_slotLaw_vertexCylinder (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m))
    (n : ℕ) (I : Finset ℝ≥0) (g : ℝ≥0 → ℕ) :
    Measurable fun e => slotLaw G n e (vertexCylinder I g) := by
  classical
  have hgate : MeasurableSet {e : Env | e ∈ G ∧ (e.val.1 n).isSome} :=
    hG.inter (measurableSet_slotPresent n)
  have hact : MeasurableSet {e : Env | ∀ i ∈ I, (e.val.1 (g i)).isSome} := by
    have hset : {e : Env | ∀ i ∈ I, (e.val.1 (g i)).isSome}
        = ⋂ i ∈ (I : Set ℝ≥0), {e : Env | (e.val.1 (g i)).isSome} := by
      ext e
      simp
    rw [hset]
    exact MeasurableSet.biInter I.countable_toSet fun i _ => measurableSet_slotPresent (g i)
  have heq : (fun e => slotLaw G n e (vertexCylinder I g)) =
      {e : Env | e ∈ G ∧ (e.val.1 n).isSome}.indicator
          ({e : Env | ∀ i ∈ I, (e.val.1 (g i)).isSome}.indicator (walkMass G n I g))
        + {e : Env | e ∈ G ∧ (e.val.1 n).isSome}ᶜ.indicator
          (fun _ => Measure.dirac cemetery (vertexCylinder I g)) := by
    funext e
    by_cases h : e ∈ G ∧ (e.val.1 n).isSome
    · have hmem : e ∈ {e : Env | e ∈ G ∧ (e.val.1 n).isSome} := h
      rw [Pi.add_apply, Set.indicator_of_mem hmem, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hmem),
        add_zero, slotLaw_apply_of_mem h.1 h.2 (measurableSet_vertexCylinder I g),
        labelTraj_preimage_vertexCylinder]
      by_cases hact' : ∀ i ∈ I, (e.val.1 (g i)).isSome
      · rw [if_pos hact', Set.indicator_of_mem (show e ∈ {e : Env | ∀ i ∈ I, (e.val.1 (g i)).isSome}
          from hact'), walkMass_of_mem h.1 h.2]
        rfl
      · rw [if_neg hact', Set.indicator_of_notMem
          (show e ∉ {e : Env | ∀ i ∈ I, (e.val.1 (g i)).isSome} from hact'),
          Set.preimage_empty, measure_empty]
    · have hmem : e ∉ {e : Env | e ∈ G ∧ (e.val.1 n).isSome} := h
      rw [Pi.add_apply, Set.indicator_of_notMem hmem, Set.indicator_of_mem (Set.mem_compl hmem),
        zero_add, slotLaw_of_not h]
  rw [heq]
  exact ((measurable_walkMass G hG hwalk hmeas n g I).indicator hact).indicator hgate |>.add
    (measurable_const.indicator hgate.compl)

/-! ### 3. The kernels -/

/-- **The forward label law is measurable in the environment**, from the transition function. -/
theorem measurable_slotLaw (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (n : ℕ) :
    Measurable (slotLaw G n) :=
  measurable_of_measurable_vertexCylinder (slotLaw G n)
    (measurable_slotLaw_vertexCylinder G hG hwalk hmeas n)

/-- **The forward label law from slot `n` as a kernel in the environment.** -/
noncomputable def slotKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (n : ℕ) :
    Kernel Env (Trajectory ℕ) :=
  ⟨slotLaw G n, measurable_slotLaw G hG hwalk hmeas n⟩

instance slotKernel_isMarkovKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (n : ℕ) :
    IsMarkovKernel (slotKernel G hG hwalk hmeas n) :=
  ⟨fun e => slotLaw_isProbabilityMeasure G n e⟩

/-- **The two-sided law from slot `n` as a kernel**: the product of two copies of the forward
kernel. -/
noncomputable def twoSidedSlotKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (n : ℕ) :
    Kernel Env TwoSidedCoding :=
  slotKernel G hG hwalk hmeas n ×ₖ slotKernel G hG hwalk hmeas n

theorem twoSidedSlotKernel_apply (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (n : ℕ)
    (e : Env) : twoSidedSlotKernel G hG hwalk hmeas n e = twoSidedSlotLaw G n e :=
  Kernel.prod_apply _ _ _

instance twoSidedSlotKernel_isMarkovKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (n : ℕ) :
    IsMarkovKernel (twoSidedSlotKernel G hG hwalk hmeas n) := by
  unfold twoSidedSlotKernel
  infer_instance

/-- The two-sided laws, uncurried over the start slot. -/
noncomputable def slotKernelUncurried (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) :
    Kernel (Env × ℕ) TwoSidedCoding :=
  ⟨fun p => twoSidedSlotLaw G p.2 p.1, by
    refine measurable_from_prod_countable_left fun n => ?_
    have heq : (fun e : Env => twoSidedSlotLaw G n e)
        = fun e => twoSidedSlotKernel G hG hwalk hmeas n e :=
      funext fun e => (twoSidedSlotKernel_apply G hG hwalk hmeas n e).symm
    rw [heq]
    exact (twoSidedSlotKernel G hG hwalk hmeas n).measurable⟩

/-- **The root label is measurable in the environment** (slot-sum technique of
`measurable_rootAt_elim`). -/
theorem measurable_rootLabel : Measurable rootLabel := by
  classical
  refine measurable_to_countable' fun n => ?_
  set F : Env → ℝ≥0∞ := fun e => (rootAt (decode e) 0).elim 0 fun r =>
    (if (e.val.1 r.val).isSome then ((r.val : ℝ≥0∞) + 1) else 0) with hFdef
  have hF : Measurable F := by
    refine MarkedBallEnergyGeometry.measurable_rootAt_elim (E := fun e : Env => e) measurable_id
      (f := fun e k => if (e.val.1 k).isSome then ((k : ℝ≥0∞) + 1) else 0)
      (fun k => Measurable.ite (measurableSet_slotPresent k) measurable_const measurable_const)
      (fun e k hk => ?_)
    simp [hk]
  have hset : rootLabel ⁻¹' {n} = {e | F e = (n : ℝ≥0∞) + 1} ∪ ({e | F e = 0} ∩ {_e | n = 0}) := by
    ext e
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq, hFdef]
    cases hroot : rootAt (decode e) 0 with
    | none =>
      rw [rootLabel_of_none hroot]
      simp only [Option.elim_none]
      constructor
      · intro h
        exact Or.inr ⟨by simp, h.symm⟩
      · rintro (h | ⟨-, h⟩)
        · exact absurd h.symm (ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self))
        · exact h.symm
    | some v =>
      rw [rootLabel_of_some hroot]
      simp only [Option.elim_some]
      rw [if_pos v.property]
      constructor
      · intro h
        exact Or.inl (by rw [h])
      · rintro (h | ⟨h, -⟩)
        · have h' : ((v.val : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) :=
            (ENNReal.add_left_inj ENNReal.one_ne_top).1 h
          exact_mod_cast h'
        · exact absurd h (ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self))
  rw [hset]
  refine (measurableSet_eq_fun hF measurable_const).union
    ((measurableSet_eq_fun hF measurable_const).inter ?_)
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

/-- **The rooted two-sided law as a kernel in the environment**: `ℙ_H^{H_0}` in the label coding,
the `κ` of the regeneration lane. -/
noncomputable def rootedKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) :
    Kernel Env TwoSidedCoding :=
  (slotKernelUncurried G hG hwalk hmeas).comap (fun e => (e, rootLabel e))
    (measurable_id.prodMk measurable_rootLabel)

theorem rootedKernel_apply (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (e : Env) :
    rootedKernel G hG hwalk hmeas e = rootedLaw G e := rfl

instance rootedKernel_isMarkovKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) :
    IsMarkovKernel (rootedKernel G hG hwalk hmeas) :=
  ⟨fun e => rootedLaw_isProbabilityMeasure G e⟩

/-! ### 4. Lifting a kernel to a subtype of full outer measure -/

section Lift

variable {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]

end Lift

/-! ### 5. Satisfiability of the inputs and the consumer's shape -/

/-- **Shape check against the consumer**: the annealed law `νenv ⊗ₘ κ` of
`Limit/BracketLLNDisintegratedWeld` and `Temporal/RegenerativeInvarianceReduction` forms with
`κ := rootedKernel …`, on `Ω = Code.Env × TwoSidedCoding`. -/
noncomputable example (νenv : Measure Env) [IsProbabilityMeasure νenv] (G : Set Env)
    (hG : MeasurableSet G) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) :
    Measure (Env × TwoSidedCoding) :=
  νenv ⊗ₘ rootedKernel G hG hwalk hmeas

end ReflectedGMS.RegenerationKernel
