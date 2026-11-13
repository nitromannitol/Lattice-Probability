/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CycleDecompositionLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CycleDecompositionPathwise
import Mathlib.Probability.Independence.InfinitePi

/-!
# `RootedCycleDecomposition` from forward regeneration (milestone 2(c), part 2)

Let `μ` be a law of regular forward paths (`RegLL`) from `v` with **one-step regeneration at the
first complete return** (`ForwardRegeneration`: a.s. the path starts at `v` and returns,
`μ.map nx = μ`, `IndepFun (firstCycle v) nx μ`), and let `ν = μ.map (firstCycle v)` be its cycle
law.  Assume in addition

* (R4) `HoldExcIndep ν`: under `ν` the holding time of a cycle is independent of its excursion
  (`withHold 1 c`, the cycle with unit holding);
* (R5) `StraddleAbsCont ν`: the sum of two independent holding times is absolutely continuous
  w.r.t. one holding time.

Then for the two-sided law `P = (μ ⊗ μ)` on `TwoSidedReg` (independent forward and backward halves,
both from `v`), **`RootedCycleDecomposition P ν`**, i.e. `P.map ρ ≪ mixedLaw ν`
(`rootedCycleDecomposition_of_regeneration`).  Both extra hypotheses hold for the actual walk
(exponential holding at `v`, independent of the jump chain — property (iii) + the strong Markov
property at the exit time; `Exp ∗ Exp = Γ(2) ≪ Exp`); they are the inputs of the actual-law step.

## Route
* `splice_decomp` (pathwise): `ρ p = splice (decomp v p)` a.s.;
* `map_cycSeq`: the forward cycles are i.i.d. `ν` (`iIndep_cycleSigma`, already proved);
* the core `assemble_absCont`: under `ν^ℕ ⊗ ν^ℕ`, split every cycle into its two independent
  **atoms** (holding, excursion; `atom`, `recomb`), regroup the atoms into the ℤ-indexed blocks
  used by `assemble` (`sig`, injective via a left inverse), and absorb the straddling holding by
  resampling one coordinate of an infinite product (`infinitePi_map_update`,
  `map_update_absCont`).  No infinite product is ever split into two infinite products.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleDecomposition

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.FirstCycleLaw
open ReflectedGMS.RegenerativeInvarianceFiberwise

/-! ### 1. Generic measure-theoretic lemmas -/

section Generic

theorem iIndepFun_fin_two {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Fin 2 → Ω → β} (hX : ∀ i, Measurable (X i))
    (h : IndepFun (X 0) (X 1) P) : iIndepFun X P := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hX, Measure.infinitePi_eq_pi]
  apply (MeasurableEquiv.piFinTwo fun _ : Fin 2 => β).map_measurableEquiv_injective
  rw [(measurePreserving_piFinTwo fun i => P.map (X i)).map_eq,
    Measure.map_map (MeasurableEquiv.measurable _) (measurable_pi_iff.2 hX)]
  exact (indepFun_iff_map_prod_eq_prod_map_map (hX 0).aemeasurable (hX 1).aemeasurable).1 h

theorem indepFun_comp_of_map {Ω γ β β' : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    [MeasurableSpace β] [MeasurableSpace β'] {Q : Measure Ω} [IsFiniteMeasure Q] {Z : Ω → γ}
    (hZ : Measurable Z) {f : γ → β} {g : γ → β'} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g (Q.map Z)) : IndepFun (f ∘ Z) (g ∘ Z) Q := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    Measure.map_map (hf.prodMk hg) hZ, Measure.map_map hf hZ, Measure.map_map hg hZ] at h
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.comp hZ).aemeasurable (hg.comp hZ).aemeasurable]
  exact h

theorem indepFun_fst_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IndepFun (Prod.fst : α × β → α) Prod.snd (μ.prod ν) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ,
    measure_univ, one_smul, one_smul]
  exact Measure.map_id

theorem map_iterate_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}
    (hf : Measurable f) (h : μ.map f = μ) (k : ℕ) : μ.map (f^[k]) = μ := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ', ← Measure.map_map hf (hf.iterate k), ih, h]

theorem infinitePi_congr {ι X : Type*} [MeasurableSpace X] {μ μ' : ι → Measure X}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (μ' i)] (h : ∀ i, μ i = μ' i) :
    Measure.infinitePi μ = Measure.infinitePi μ' := by
  obtain rfl : μ = μ' := funext h
  rfl

theorem measurable_update_swap {ι X : Type*} [MeasurableSpace X] [DecidableEq ι] (i₀ : ι) :
    Measurable fun p : X × (ι → X) => Function.update p.2 i₀ p.1 :=
  (measurable_update' (X := fun _ : ι => X) (a := i₀)).comp measurable_swap

/-- **Resampling one coordinate of an infinite product.**  Replacing coordinate `i₀` of an
`infinitePi M`-distributed family by an independent `M' i₀`-distributed value gives
`infinitePi M'`, for any `M'` agreeing with `M` off `i₀`. -/
theorem infinitePi_map_update {ι X : Type*} [MeasurableSpace X] [DecidableEq ι]
    (M M' : ι → Measure X) [∀ i, IsProbabilityMeasure (M i)] [∀ i, IsProbabilityMeasure (M' i)]
    (i₀ : ι) (hM : ∀ i, i ≠ i₀ → M' i = M i) :
    ((M' i₀).prod (Measure.infinitePi M)).map (fun p => Function.update p.2 i₀ p.1) =
      Measure.infinitePi M' := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (measurable_update_swap i₀)
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  by_cases hs : i₀ ∈ s
  · have hpre : (fun p : X × (ι → X) => Function.update p.2 i₀ p.1) ⁻¹' Set.pi (↑s) t =
        t i₀ ×ˢ Set.pi (↑(s.erase i₀)) t := by
      ext ⟨x, w⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨?_, fun i ⟨hi, his⟩ => ?_⟩
        · have h' := h i₀ hs
          rwa [Function.update_self] at h'
        · have h' := h i his
          rwa [Function.update_of_ne hi] at h'
      · rintro ⟨hx, hw⟩ i his
        by_cases hi : i = i₀
        · subst hi
          rwa [Function.update_self]
        · rw [Function.update_of_ne hi]
          exact hw i ⟨hi, his⟩
    rw [hpre, Measure.prod_prod, Measure.infinitePi_pi M (fun i _ => ht i),
      ← Finset.mul_prod_erase s _ hs]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hM i (Finset.ne_of_mem_erase hi)]
  · have hpre : (fun p : X × (ι → X) => Function.update p.2 i₀ p.1) ⁻¹' Set.pi (↑s) t =
        (Set.univ : Set X) ×ˢ Set.pi (↑s) t := by
      ext ⟨x, w⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ,
        true_and]
      refine forall_congr' fun i => forall_congr' fun his => ?_
      have hi : i ≠ i₀ := fun h => hs (h ▸ his)
      rw [Function.update_of_ne hi]
    rw [hpre, Measure.prod_prod, measure_univ, one_mul, Measure.infinitePi_pi M (fun i _ => ht i)]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hM i (fun h => hs (h ▸ hi))]

/-- **Absolute continuity under resampling a coordinate from a function of two coordinates.**
If `F` ignores coordinate `i₁` and the law of `ψ (t i₀, t i₁)` is `≪ M i₀`, replacing `t i₀` by
`ψ (t i₀, t i₁)` before applying `F` gives a law `≪` the law of `F`. -/
theorem map_update_absCont {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [DecidableEq ι] (M : ι → Measure X) [∀ i, IsProbabilityMeasure (M i)] {i₀ i₁ : ι}
    (hne : i₀ ≠ i₁) {F : (ι → X) → Y} (hF : Measurable F)
    (hFi : ∀ t d, F (Function.update t i₁ d) = F t) {ψ : X × X → X} (hψ : Measurable ψ)
    (hac : ((M i₀).prod (M i₁)).map ψ ≪ M i₀) :
    (Measure.infinitePi M).map (fun t => F (Function.update t i₀ (ψ (t i₀, t i₁)))) ≪
      (Measure.infinitePi M).map F := by
  have hU0 := measurable_update_swap (X := X) i₀
  have hU1 := measurable_update_swap (X := X) i₁
  have h0 := infinitePi_map_update M M i₀ fun _ _ => rfl
  have h1 := infinitePi_map_update M M i₁ fun _ _ => rfl
  -- the infinite product as an image of `M i₀ ⊗ (M i₁ ⊗ Π)`
  have hPi : Measure.infinitePi M = ((M i₀).prod ((M i₁).prod (Measure.infinitePi M))).map
      (fun q => Function.update (Function.update q.2.2 i₁ q.2.1) i₀ q.1) := by
    have hmp := Measure.map_prod_map (M i₀) ((M i₁).prod (Measure.infinitePi M)) measurable_id hU1
    rw [Measure.map_id] at hmp
    calc Measure.infinitePi M
        = ((M i₀).prod (Measure.infinitePi M)).map (fun p => Function.update p.2 i₀ p.1) := h0.symm
      _ = ((M i₀).prod (((M i₁).prod (Measure.infinitePi M)).map
            (fun p => Function.update p.2 i₁ p.1))).map (fun p => Function.update p.2 i₀ p.1) := by
          rw [h1]
      _ = _ := by
          rw [hmp, Measure.map_map hU0 (measurable_id.prodMap hU1)]
          rfl
  have hmW : Measurable fun q : X × X × (ι → X) =>
      Function.update (Function.update q.2.2 i₁ q.2.1) i₀ q.1 :=
    hU0.comp (measurable_fst.prodMk (hU1.comp measurable_snd))
  have hT : Measurable fun t : ι → X => F (Function.update t i₀ (ψ (t i₀, t i₁))) :=
    hF.comp ((measurable_update' (X := fun _ : ι => X) (a := i₀)).comp (measurable_id.prodMk
      (hψ.comp ((measurable_pi_apply i₀ : Measurable fun t : ι → X => t i₀).prodMk
        (measurable_pi_apply i₁ : Measurable fun t : ι → X => t i₁)))))
  have hG : Measurable fun r : (X × X) × (ι → X) => F (Function.update r.2 i₀ (ψ r.1)) :=
    hF.comp (hU0.comp ((hψ.comp measurable_fst).prodMk measurable_snd))
  have hpt : ∀ q : X × X × (ι → X),
      F (Function.update (Function.update (Function.update q.2.2 i₁ q.2.1) i₀ q.1) i₀
        (ψ ((Function.update (Function.update q.2.2 i₁ q.2.1) i₀ q.1) i₀,
          (Function.update (Function.update q.2.2 i₁ q.2.1) i₀ q.1) i₁))) =
        F (Function.update q.2.2 i₀ (ψ (q.1, q.2.1))) := by
    rintro ⟨x, d, t⟩
    simp only [Function.update_self, Function.update_of_ne hne.symm, Function.update_idem]
    rw [Function.update_comm hne.symm, hFi]
  have hlhs : (Measure.infinitePi M).map (fun t => F (Function.update t i₀ (ψ (t i₀, t i₁)))) =
      (((M i₀).prod (M i₁)).prod (Measure.infinitePi M)).map
        (fun r => F (Function.update r.2 i₀ (ψ r.1))) := by
    conv_lhs => rw [hPi]
    rw [Measure.map_map hT hmW, ← (measurePreserving_prodAssoc (M i₀) (M i₁)
      (Measure.infinitePi M)).map_eq, Measure.map_map (hT.comp hmW)
      (MeasurableEquiv.measurable _)]
    congr 1
    funext r
    exact hpt (r.1.1, r.1.2, r.2)
  have hR : ((((M i₀).prod (M i₁)).map ψ).prod (Measure.infinitePi M)).map
      (fun p => F (Function.update p.2 i₀ p.1)) =
      (((M i₀).prod (M i₁)).prod (Measure.infinitePi M)).map
        (fun r => F (Function.update r.2 i₀ (ψ r.1))) := by
    have hmp := Measure.map_prod_map ((M i₀).prod (M i₁)) (Measure.infinitePi M) hψ measurable_id
    rw [Measure.map_id] at hmp
    have hG' : Measurable fun p : X × (ι → X) => F (Function.update p.2 i₀ p.1) := hF.comp hU0
    rw [hmp, Measure.map_map hG' (hψ.prodMap measurable_id)]
    rfl
  have hrhs : (Measure.infinitePi M).map F =
      ((M i₀).prod (Measure.infinitePi M)).map (fun p => F (Function.update p.2 i₀ p.1)) := by
    conv_lhs => rw [← h0]
    rw [Measure.map_map hF hU0]
    rfl
  rw [hlhs, ← hR, hrhs]
  exact (hac.prod Measure.AbsolutelyContinuous.rfl).map (hF.comp hU0)

end Generic

/-! ### 2. Atoms of a cycle: its holding and its excursion -/

variable {v : ℕ}

/-- A cycle carrying only a holding time: hold `h` at `v`, then the default excursion. -/
noncomputable def holdCyc (v : ℕ) (h : ℝ≥0) : Cyc v := withHold h (defaultCycle v)

theorem measurable_holdCyc : Measurable (holdCyc v) :=
  measurable_withHold_of measurable_id measurable_const

theorem holdTime_holdCyc {h : ℝ≥0} (hh : 0 < h) : holdTime (holdCyc v h) = h :=
  holdTime_withHold hh _

/-- The two atoms of a cycle: `0` its holding (as `holdCyc`), `1` its excursion (unit holding). -/
noncomputable def atom (c : Cyc v) (j : Fin 2) : Cyc v :=
  if j = 0 then holdCyc v (holdTime c) else withHold 1 c

theorem atom_zero (c : Cyc v) : atom c 0 = holdCyc v (holdTime c) := if_pos rfl

theorem atom_one (c : Cyc v) : atom c 1 = withHold 1 c := if_neg (by decide)

theorem measurable_atom (j : Fin 2) : Measurable fun c : Cyc v => atom c j := by
  by_cases hj : j = 0
  · have e : (fun c : Cyc v => atom c j) = fun c => holdCyc v (holdTime c) :=
      funext fun c => if_pos hj
    rw [e]
    exact measurable_holdCyc.comp measurable_holdTime
  · have e : (fun c : Cyc v => atom c j) = fun c => withHold 1 c := funext fun c => if_neg hj
    rw [e]
    exact measurable_withHold_of measurable_const measurable_id

theorem measurable_atom_vec : Measurable fun c : Cyc v => fun j => atom c j :=
  measurable_pi_iff.2 measurable_atom

/-- Recombination of two atoms into a cycle. -/
noncomputable def recomb (t : Fin 2 → Cyc v) : Cyc v := withHold (holdTime (t 0)) (t 1)

theorem measurable_recomb : Measurable (recomb (v := v)) := by
  have h0 : Measurable fun t : Fin 2 → Cyc v => t 0 := measurable_pi_apply 0
  have h1 : Measurable fun t : Fin 2 → Cyc v => t 1 := measurable_pi_apply 1
  exact measurable_withHold_of (measurable_holdTime.comp h0) h1

theorem recomb_atom (c : Cyc v) : recomb (fun j => atom c j) = c := by
  obtain ⟨hH0, -, -, -⟩ := cyc_hold c
  show withHold (holdTime (atom c 0)) (atom c 1) = c
  rw [atom_zero, atom_one, holdTime_holdCyc hH0, withHold_withHold hH0 one_pos, withHold_holdTime]

/-- **(R4) Holding/excursion independence of a cycle law.** -/
def HoldExcIndep (ν : Measure (Cyc v)) : Prop := IndepFun (holdTime (v := v)) (withHold 1) ν

/-- **(R5) The sum of two independent holdings is absolutely continuous w.r.t. one holding.** -/
def StraddleAbsCont (ν : Measure (Cyc v)) : Prop :=
  ((ν.map (holdTime (v := v))).prod (ν.map holdTime)).map (fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2) ≪
    ν.map holdTime

theorem iIndepFun_atom {ν : Measure (Cyc v)} [IsProbabilityMeasure ν] (h4 : HoldExcIndep ν) :
    iIndepFun (fun j c => atom c j) ν := by
  refine iIndepFun_fin_two measurable_atom ?_
  have e0 : (fun c : Cyc v => atom c 0) = holdCyc v ∘ holdTime := funext atom_zero
  have e1 : (fun c : Cyc v => atom c 1) = id ∘ withHold 1 := funext atom_one
  show IndepFun (fun c : Cyc v => atom c 0) (fun c => atom c 1) ν
  rw [e0, e1]
  exact h4.comp measurable_holdCyc measurable_id

theorem map_atom_recomb {ν : Measure (Cyc v)} [IsProbabilityMeasure ν] (h4 : HoldExcIndep ν) :
    (Measure.infinitePi fun j : Fin 2 => ν.map fun c => atom c j).map recomb = ν := by
  rw [← (iIndepFun_atom h4).map_fun_eq_infinitePi_map measurable_atom,
    Measure.map_map measurable_recomb measurable_atom_vec]
  have e : recomb ∘ (fun c : Cyc v => fun j => atom c j) = id := funext recomb_atom
  rw [e, Measure.map_id]

/-! ### 3. The core: the assembled two-sided sequence is `≪` the mixed product -/

/-- The two sides of a pair of cycle sequences. -/
def side (s : Fin 2) (ω : (ℕ → Cyc v) × (ℕ → Cyc v)) : ℕ → Cyc v := if s = 0 then ω.1 else ω.2

theorem side_zero (ω : (ℕ → Cyc v) × (ℕ → Cyc v)) : side 0 ω = ω.1 := if_pos rfl

theorem side_one (ω : (ℕ → Cyc v) × (ℕ → Cyc v)) : side 1 ω = ω.2 := if_neg (by decide)

theorem measurable_side (s : Fin 2) : Measurable (side (v := v) s) := by
  by_cases hs : s = 0
  · have e : side (v := v) s = Prod.fst := funext fun ω => if_pos hs
    rw [e]
    exact measurable_fst
  · have e : side (v := v) s = Prod.snd := funext fun ω => if_neg hs
    rw [e]
    exact measurable_snd

/-- The atom family of a pair of cycle sequences. -/
noncomputable def atomFam (ω : (ℕ → Cyc v) × (ℕ → Cyc v)) (q : (Fin 2 × ℕ) × Fin 2) : Cyc v :=
  atom (side q.1.1 ω q.1.2) q.2

theorem measurable_atomFam (q : (Fin 2 × ℕ) × Fin 2) :
    Measurable fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => atomFam ω q :=
  (measurable_atom q.2).comp ((measurable_pi_apply q.1.2).comp (measurable_side q.1.1))

section Core

variable (ν : Measure (Cyc v)) [IsProbabilityMeasure ν]

/-- `ν^ℕ`. -/
noncomputable abbrev seqLaw : Measure (ℕ → Cyc v) := Measure.infinitePi fun _ : ℕ => ν

theorem map_side (s : Fin 2) :
    ((seqLaw ν).prod (seqLaw ν)).map (side s) = seqLaw ν := by
  by_cases hs : s = 0
  · have e : side (v := v) s = Prod.fst := funext fun ω => if_pos hs
    rw [e, Measure.map_fst_prod, measure_univ, one_smul]
  · have e : side (v := v) s = Prod.snd := funext fun ω => if_neg hs
    rw [e, Measure.map_snd_prod, measure_univ, one_smul]

theorem map_side_eval (s : Fin 2) (k : ℕ) :
    ((seqLaw ν).prod (seqLaw ν)).map (fun ω => side s ω k) = ν := by
  have e : (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => side s ω k) =
      (fun w : ℕ → Cyc v => w k) ∘ side s := rfl
  rw [e, ← Measure.map_map (measurable_pi_apply k) (measurable_side s), map_side,
    Measure.infinitePi_map_eval]

theorem iIndepFun_sides :
    iIndepFun (fun (p : Fin 2 × ℕ) (ω : (ℕ → Cyc v) × (ℕ → Cyc v)) => side p.1 ω p.2)
      ((seqLaw ν).prod (seqLaw ν)) := by
  refine iIndepFun_uncurry' (X := fun (s : Fin 2) (k : ℕ) ω => side s ω k)
    (fun s k => (measurable_pi_apply k).comp (measurable_side s)) ?_ fun s => ?_
  · refine iIndepFun_fin_two (fun s => measurable_pi_iff.2 fun k =>
      (measurable_pi_apply k).comp (measurable_side s)) ?_
    have e0 : (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => fun k => side 0 ω k) = Prod.fst :=
      funext fun ω => side_zero ω
    have e1 : (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => fun k => side 1 ω k) = Prod.snd :=
      funext fun ω => side_one ω
    show IndepFun (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => fun k => side 0 ω k)
      (fun ω => fun k => side 1 ω k) _
    rw [e0, e1]
    exact indepFun_fst_snd _ _
  · rw [iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun k ω => side s ω k) fun k =>
      (measurable_pi_apply k).comp (measurable_side s)]
    have e : (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => fun k => side s ω k) = side s := rfl
    rw [e, map_side]
    exact infinitePi_congr fun k => (map_side_eval ν s k).symm

theorem iIndepFun_atomFam (h4 : HoldExcIndep ν) :
    iIndepFun (fun (q : (Fin 2 × ℕ) × Fin 2) ω => atomFam ω q) ((seqLaw ν).prod (seqLaw ν)) := by
  refine iIndepFun_uncurry' (X := fun (p : Fin 2 × ℕ) (j : Fin 2) ω => atom (side p.1 ω p.2) j)
    (fun p j => measurable_atomFam (p, j)) ?_ fun p => ?_
  · exact (iIndepFun_sides ν).comp (fun _ c j => atom c j) fun _ => measurable_atom_vec
  · refine iIndepFun_fin_two (fun j => measurable_atomFam (p, j)) ?_
    have hZ : Measurable fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => side p.1 ω p.2 :=
      (measurable_pi_apply p.2).comp (measurable_side p.1)
    have h := (iIndepFun_atom h4).indepFun (show (0 : Fin 2) ≠ 1 by decide)
    rw [← map_side_eval ν p.1 p.2] at h
    exact indepFun_comp_of_map hZ (measurable_atom 0) (measurable_atom 1) h

/-! #### Regrouping the atoms into the blocks of `assemble` -/

/-- The cycle-and-side of block `j`, atom `m`. -/
def blockBase : ℤ → Fin 2 → Fin 2 × ℕ
  | Int.ofNat k, _ => (0, k + 1)
  | Int.negSucc 0, _ => (0, 0)
  | Int.negSucc (k + 1), m => (1, if m = 0 then k + 1 else k)

/-- The atom index of block `j`, atom `m` (`Sum.inl`), and of the straddling holding
(`Sum.inr`). -/
def sig : (ℤ × Fin 2) ⊕ Unit → (Fin 2 × ℕ) × Fin 2
  | Sum.inl p => (blockBase p.1 p.2, p.2)
  | Sum.inr _ => ((1, 0), 0)

/-- A left inverse of `sig`. -/
def sigInv (q : (Fin 2 × ℕ) × Fin 2) : (ℤ × Fin 2) ⊕ Unit :=
  if q.1.1 = 0 then
    (if q.1.2 = 0 then Sum.inl (Int.negSucc 0, q.2) else Sum.inl (Int.ofNat (q.1.2 - 1), q.2))
  else if q.2 = 0 then
    (if q.1.2 = 0 then Sum.inr () else Sum.inl (Int.negSucc q.1.2, 0))
  else Sum.inl (Int.negSucc (q.1.2 + 1), 1)

theorem sigInv_sig : Function.LeftInverse sigInv sig := by
  rintro (⟨j, m⟩ | ⟨⟩)
  · rcases j with k | (_ | k) <;> fin_cases m <;> first | rfl | simp [sig, blockBase, sigInv]
  · rfl

theorem sig_injective : Function.Injective sig := sigInv_sig.injective

/-- The straddle indices. -/
def iStr : (ℤ × Fin 2) ⊕ Unit := Sum.inl (Int.negSucc 0, 0)

def iExtra : (ℤ × Fin 2) ⊕ Unit := Sum.inr ()

/-- The reversal applied at the backward blocks. -/
noncomputable def gj (j : ℤ) (c : Cyc v) : Cyc v := if j ≤ -2 then cycRev c else c

theorem measurable_gj (j : ℤ) : Measurable (gj (v := v) j) := by
  unfold gj
  split_ifs
  · exact measurable_cycRev
  · exact measurable_id

/-- The grouping map (no straddle). -/
noncomputable def grp (t : (ℤ × Fin 2) ⊕ Unit → Cyc v) (j : ℤ) : Cyc v :=
  gj j (recomb fun m => t (Sum.inl (j, m)))

theorem measurable_grp : Measurable (grp (v := v)) := by
  refine measurable_pi_iff.2 fun j => (measurable_gj j).comp (measurable_recomb.comp ?_)
  exact measurable_pi_iff.2 fun m => (measurable_pi_apply (Sum.inl (j, m)) :
    Measurable fun t : (ℤ × Fin 2) ⊕ Unit → Cyc v => t (Sum.inl (j, m)))

/-- The straddled holding. -/
noncomputable def psiStr (p : Cyc v × Cyc v) : Cyc v := holdCyc v (holdTime p.1 + holdTime p.2)

theorem measurable_psiStr : Measurable (psiStr (v := v)) :=
  measurable_holdCyc.comp ((measurable_holdTime.comp measurable_fst).add
    (measurable_holdTime.comp measurable_snd))

/-- The atom family regrouped. -/
noncomputable def regroup (ω : (ℕ → Cyc v) × (ℕ → Cyc v)) (i : (ℤ × Fin 2) ⊕ Unit) : Cyc v :=
  atomFam ω (sig i)

theorem measurable_regroup : Measurable (regroup (v := v)) :=
  measurable_pi_iff.2 fun i => measurable_atomFam (sig i)

/-- **Pathwise: `assemble` is the grouping of the regrouped atoms, with the straddle.** -/
theorem assemble_eq_grp (ω : (ℕ → Cyc v) × (ℕ → Cyc v)) :
    assemble ω.1 ω.2 = grp (Function.update (regroup ω) iStr
      (psiStr (regroup ω iStr, regroup ω iExtra))) := by
  funext j
  rcases j with k | (_ | k)
  · have hfun : (fun m : Fin 2 => Function.update (regroup ω) iStr
        (psiStr (regroup ω iStr, regroup ω iExtra)) (Sum.inl (Int.ofNat k, m))) =
        fun m => regroup ω (Sum.inl (Int.ofNat k, m)) := by
      funext m
      have hne : (Sum.inl (Int.ofNat k, m) : (ℤ × Fin 2) ⊕ Unit) ≠ iStr := by
        intro h
        cases h
      exact Function.update_of_ne hne _ _
    show ω.1 (k + 1) = gj (Int.ofNat k) (recomb fun m => Function.update (regroup ω) iStr
      (psiStr (regroup ω iStr, regroup ω iExtra)) (Sum.inl (Int.ofNat k, m)))
    rw [hfun]
    have hg : gj (v := v) (Int.ofNat k) = id := by
      funext c
      unfold gj
      rw [if_neg (by rw [Int.ofNat_eq_coe]; omega)]
      rfl
    rw [hg]
    show ω.1 (k + 1) = recomb fun m => atom (side 0 ω (k + 1)) m
    rw [recomb_atom, side_zero]
  · have hg : gj (v := v) (Int.negSucc 0) = id := by
      funext c
      unfold gj
      rw [if_neg (by decide)]
      rfl
    obtain ⟨ha, -, -, -⟩ := cyc_hold (ω.1 0)
    obtain ⟨hb, -, -, -⟩ := cyc_hold (ω.2 0)
    have e0 : Function.update (regroup ω) iStr (psiStr (regroup ω iStr, regroup ω iExtra))
        (Sum.inl (Int.negSucc 0, 0)) = holdCyc v (holdTime (ω.1 0) + holdTime (ω.2 0)) := by
      show Function.update (regroup ω) iStr (psiStr (regroup ω iStr, regroup ω iExtra)) iStr = _
      rw [Function.update_self]
      show holdCyc v (holdTime (atom (side 0 ω 0) 0) + holdTime (atom (side 1 ω 0) 0)) = _
      rw [atom_zero, atom_zero, holdTime_holdCyc (cyc_hold _).1, holdTime_holdCyc (cyc_hold _).1,
        side_zero, side_one]
    have hne1 : (Sum.inl (Int.negSucc 0, 1) : (ℤ × Fin 2) ⊕ Unit) ≠ iStr := by
      intro h
      cases h
    have e1 : Function.update (regroup ω) iStr (psiStr (regroup ω iStr, regroup ω iExtra))
        (Sum.inl (Int.negSucc 0, 1)) = withHold 1 (ω.1 0) := by
      rw [Function.update_of_ne hne1]
      show atom (side 0 ω 0) 1 = _
      rw [atom_one, side_zero]
    show withHold (holdTime (ω.1 0) + holdTime (ω.2 0)) (ω.1 0) =
      gj (Int.negSucc 0) (withHold (holdTime (Function.update (regroup ω) iStr
        (psiStr (regroup ω iStr, regroup ω iExtra)) (Sum.inl (Int.negSucc 0, 0))))
      (Function.update (regroup ω) iStr (psiStr (regroup ω iStr, regroup ω iExtra))
        (Sum.inl (Int.negSucc 0, 1))))
    rw [hg, e0, e1, holdTime_holdCyc (add_pos ha hb), withHold_withHold (add_pos ha hb) one_pos]
    rfl
  · have hfun : (fun m : Fin 2 => Function.update (regroup ω) iStr
        (psiStr (regroup ω iStr, regroup ω iExtra)) (Sum.inl (Int.negSucc (k + 1), m))) =
        fun m => regroup ω (Sum.inl (Int.negSucc (k + 1), m)) := by
      funext m
      have hne : (Sum.inl (Int.negSucc (k + 1), m) : (ℤ × Fin 2) ⊕ Unit) ≠ iStr := by
        intro h
        cases h
      exact Function.update_of_ne hne _ _
    show cycRev (withHold (holdTime (ω.2 (k + 1))) (ω.2 k)) =
      gj (Int.negSucc (k + 1)) (recomb fun m => Function.update (regroup ω) iStr
        (psiStr (regroup ω iStr, regroup ω iExtra)) (Sum.inl (Int.negSucc (k + 1), m)))
    rw [hfun]
    have hg : gj (v := v) (Int.negSucc (k + 1)) = cycRev := by
      funext c
      unfold gj
      rw [if_pos (by rw [Int.negSucc_eq]; omega)]
    rw [hg]
    obtain ⟨hk, -, -, -⟩ := cyc_hold (ω.2 (k + 1))
    show _ = cycRev (withHold (holdTime (atom (side 1 ω (k + 1)) 0)) (atom (side 1 ω k) 1))
    rw [atom_zero, atom_one, side_one, holdTime_holdCyc hk, withHold_withHold hk one_pos]

/-- The law of the regrouped atoms. -/
theorem map_regroup (h4 : HoldExcIndep ν) :
    ((seqLaw ν).prod (seqLaw ν)).map regroup =
      Measure.infinitePi fun i : (ℤ × Fin 2) ⊕ Unit => ν.map fun c => atom c (sig i).2 := by
  have hI := (iIndepFun_atomFam ν h4).precomp sig_injective
  rw [show (regroup (v := v)) = fun ω i => atomFam ω (sig i) from rfl,
    hI.map_fun_eq_infinitePi_map fun i => measurable_atomFam (sig i)]
  refine infinitePi_congr fun i => ?_
  show ((seqLaw ν).prod (seqLaw ν)).map (fun ω => atomFam ω (sig i)) = _
  have e : (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => atomFam ω (sig i)) =
      (fun c => atom c (sig i).2) ∘ fun ω => side (sig i).1.1 ω (sig i).1.2 := rfl
  have hZ : Measurable fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => side (sig i).1.1 ω (sig i).1.2 :=
    (measurable_pi_apply _).comp (measurable_side _)
  rw [e, ← Measure.map_map (measurable_atom _) hZ, map_side_eval]

/-- The grouped law (no straddle) is the mixed product. -/
theorem map_grp (h4 : HoldExcIndep ν) :
    (Measure.infinitePi fun i : (ℤ × Fin 2) ⊕ Unit => ν.map fun c => atom c (sig i).2).map
        grp = Measure.infinitePi (fun k : ℤ => if k ≤ -2 then ν.map cycRev else ν) := by
  have hinl : Measurable fun (t : (ℤ × Fin 2) ⊕ Unit → Cyc v) (p : ℤ × Fin 2) => t (Sum.inl p) :=
    measurable_pi_iff.2 fun p => (measurable_pi_apply (Sum.inl p) :
      Measurable fun t : (ℤ × Fin 2) ⊕ Unit → Cyc v => t (Sum.inl p))
  have hcur : Measurable (MeasurableEquiv.curry ℤ (Fin 2) (Cyc v)) :=
    MeasurableEquiv.measurable _
  have hfin : Measurable fun (w : ℤ → Fin 2 → Cyc v) (j : ℤ) => gj j (recomb (w j)) :=
    measurable_pi_iff.2 fun j => (measurable_gj j).comp (measurable_recomb.comp
      (measurable_pi_apply j : Measurable fun w : ℤ → Fin 2 → Cyc v => w j))
  have e : (grp (v := v)) = (fun (w : ℤ → Fin 2 → Cyc v) (j : ℤ) => gj j (recomb (w j))) ∘
      (MeasurableEquiv.curry ℤ (Fin 2) (Cyc v)) ∘
        fun (t : (ℤ × Fin 2) ⊕ Unit → Cyc v) (p : ℤ × Fin 2) => t (Sum.inl p) := rfl
  rw [e, ← Measure.map_map hfin (hcur.comp hinl), ← Measure.map_map hcur hinl,
    Measure.map_infinitePi_infinitePi_of_inj Sum.inl_injective]
  show Measure.map (fun (w : ℤ → Fin 2 → Cyc v) (j : ℤ) => gj j (recomb (w j)))
    (Measure.map (MeasurableEquiv.curry ℤ (Fin 2) (Cyc v))
      (Measure.infinitePi fun p : ℤ × Fin 2 =>
        (fun (_ : ℤ) (m : Fin 2) => ν.map fun c => atom c m) p.1 p.2)) = _
  rw [show Measure.map (MeasurableEquiv.curry ℤ (Fin 2) (Cyc v))
      (Measure.infinitePi fun p : ℤ × Fin 2 =>
        (fun (_ : ℤ) (m : Fin 2) => ν.map fun c => atom c m) p.1 p.2) =
      Measure.infinitePi fun _ : ℤ => Measure.infinitePi fun m : Fin 2 => ν.map fun c => atom c m
      from Measure.infinitePi_map_curry (fun (_ : ℤ) (m : Fin 2) => ν.map fun c => atom c m),
    Measure.infinitePi_map_pi (f := fun j c => gj j (recomb c)) _
      fun j => (measurable_gj j).comp measurable_recomb]
  refine infinitePi_congr fun j => ?_
  show Measure.map (gj j ∘ recomb) (Measure.infinitePi fun m : Fin 2 => ν.map fun c => atom c m) = _
  rw [← Measure.map_map (measurable_gj j) measurable_recomb, map_atom_recomb h4]
  unfold gj
  split_ifs <;> first | rfl | exact Measure.map_id

/-- **The core: the assembled two-sided sequence of `ν^ℕ ⊗ ν^ℕ` is `≪` the mixed product.** -/
theorem assemble_absCont (h4 : HoldExcIndep ν) (h5 : StraddleAbsCont ν) :
    ((seqLaw ν).prod (seqLaw ν)).map (fun ω => assemble ω.1 ω.2) ≪
      Measure.infinitePi (fun k : ℤ => if k ≤ -2 then ν.map cycRev else ν) := by
  classical
  have hne : iStr ≠ iExtra := by
    intro h
    cases h
  have hmapT : Measurable fun t : (ℤ × Fin 2) ⊕ Unit → Cyc v =>
      grp (Function.update t iStr (psiStr (t iStr, t iExtra))) :=
    measurable_grp.comp ((measurable_update' (X := fun _ : (ℤ × Fin 2) ⊕ Unit => Cyc v)
      (a := iStr)).comp (measurable_id.prodMk (measurable_psiStr.comp
        ((measurable_pi_apply iStr : Measurable fun t : (ℤ × Fin 2) ⊕ Unit → Cyc v => t iStr).prodMk
          (measurable_pi_apply iExtra : Measurable fun t : (ℤ × Fin 2) ⊕ Unit → Cyc v =>
            t iExtra)))))
  have e : (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => assemble ω.1 ω.2) =
      (fun t => grp (Function.update t iStr (psiStr (t iStr, t iExtra)))) ∘ regroup :=
    funext assemble_eq_grp
  rw [e, ← Measure.map_map hmapT measurable_regroup, map_regroup ν h4, ← map_grp ν h4]
  refine map_update_absCont (fun i => ν.map fun c => atom c (sig i).2) hne measurable_grp
    (fun t d => ?_) measurable_psiStr ?_
  · funext j
    unfold grp
    have hfun : (fun m => Function.update t iExtra d (Sum.inl (j, m))) =
        fun m => t (Sum.inl (j, m)) := by
      funext m
      exact Function.update_of_ne (by intro h; cases h) _ _
    rw [hfun]
  · -- the straddled holding is `≪` one holding atom
    show ((ν.map fun c => atom c 0).prod (ν.map fun c => atom c 0)).map psiStr ≪
      ν.map fun c => atom c 0
    have hA : ν.map (fun c => atom c 0) = (ν.map holdTime).map (holdCyc v) := by
      rw [Measure.map_map measurable_holdCyc measurable_holdTime]
      exact congrArg (fun f => ν.map f) (funext atom_zero)
    rw [hA, Measure.map_prod_map _ _ measurable_holdCyc measurable_holdCyc,
      Measure.map_map measurable_psiStr (measurable_holdCyc.prodMap measurable_holdCyc)]
    have hα : ∀ᵐ h ∂ν.map (holdTime (v := v)), 0 < h :=
      (ae_map_iff measurable_holdTime.aemeasurable measurableSet_Ioi).2
        (Eventually.of_forall fun c => (cyc_hold c).1)
    have hpos : ∀ᵐ p ∂(ν.map (holdTime (v := v))).prod (ν.map holdTime), 0 < p.1 ∧ 0 < p.2 :=
      (Measure.quasiMeasurePreserving_fst.ae hα).and (Measure.quasiMeasurePreserving_snd.ae hα)
    have hcongr : ((ν.map (holdTime (v := v))).prod (ν.map holdTime)).map
        (psiStr ∘ Prod.map (holdCyc v) (holdCyc v)) =
        ((ν.map (holdTime (v := v))).prod (ν.map holdTime)).map
          (holdCyc v ∘ fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2) := by
      refine Measure.map_congr ?_
      filter_upwards [hpos] with p hp
      show holdCyc v (holdTime (holdCyc v p.1) + holdTime (holdCyc v p.2)) = holdCyc v (p.1 + p.2)
      rw [holdTime_holdCyc hp.1, holdTime_holdCyc hp.2]
    have hadd : Measurable fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2 := measurable_fst.add measurable_snd
    rw [hcongr, ← Measure.map_map measurable_holdCyc hadd]
    exact h5.map measurable_holdCyc

end Core

/-! ### 4. From forward regeneration to `RootedCycleDecomposition` -/

/-- **One-step regeneration of a forward law at the first complete return.** -/
structure ForwardRegeneration (v : ℕ) (μ : Measure RegLL) : Prop where
  good : ∀ᵐ x ∂μ, Good v x
  shift : μ.map nx = μ
  indep : IndepFun (firstCycle v) nx μ

/-- The two-sided regular pair of two regular forward paths. -/
def pairReg (q : RegLL × RegLL) : TwoSidedReg := ⟨(q.1.1, q.2.1), ⟨q.1.2, q.2.2⟩⟩

theorem measurable_pairReg : Measurable pairReg :=
  ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd)).subtype_mk

/-- **The forward cycles are i.i.d.** -/
theorem map_cycSeq (μ : Measure RegLL) [IsProbabilityMeasure μ] (hshift : μ.map nx = μ)
    (hind : IndepFun (firstCycle v) nx μ) :
    μ.map (cycSeq v) = Measure.infinitePi fun _ : ℕ => μ.map (firstCycle v) := by
  have hI : iIndepFun (fun k x => cycleCoord nx (firstCycle v) k x) μ :=
    iIndep_cycleSigma μ measurable_nx (measurable_firstCycle v) hshift hind
  have hm : ∀ k, Measurable fun x => cycleCoord nx (firstCycle v) k x := fun k =>
    (measurable_firstCycle v).comp (measurable_nx.iterate k)
  rw [show cycSeq v = fun x k => cycleCoord nx (firstCycle v) k x from rfl,
    hI.map_fun_eq_infinitePi_map hm]
  refine infinitePi_congr fun k => ?_
  have e : (fun x => cycleCoord nx (firstCycle v) k x) = firstCycle v ∘ nx^[k] := rfl
  rw [e, ← Measure.map_map (measurable_firstCycle v) (measurable_nx.iterate k),
    map_iterate_eq measurable_nx hshift k]

theorem ae_all_good {μ : Measure RegLL} (h : ForwardRegeneration v μ) :
    ∀ᵐ x ∂μ, ∀ k, Good v (nx^[k] x) := by
  refine ae_all_iff.2 fun k => ?_
  have hk := h.good
  rw [← map_iterate_eq measurable_nx h.shift k] at hk
  exact (ae_map_iff (measurable_nx.iterate k).aemeasurable (measurableSet_good v)).1 hk

theorem ae_unbounded {μ : Measure RegLL} [IsProbabilityMeasure μ] (h : ForwardRegeneration v μ) :
    ∀ᵐ x ∂μ, Unbounded fun k => (firstCycle v (nx^[k] x)).1.2 := by
  have hlen : Measurable fun c : Cyc v => ((c.1.2 : ℝ≥0) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (measurable_snd.comp measurable_subtype_coe)
  filter_upwards [ae_mem_longRun μ measurable_nx (measurable_firstCycle v) h.shift h.indep hlen
    fun x => ENNReal.coe_pos.2 (Cyc.len_pos _)] with x hx n
  obtain ⟨k, hk⟩ := hx (n + 1)
  refine ⟨k, ?_⟩
  have hsum : cycleSum nx (firstCycle v) (fun c : Cyc v => ((c.1.2 : ℝ≥0) : ℝ≥0∞)) k x =
      ((psum (fun k => (firstCycle v (nx^[k] x)).1.2) k : ℝ≥0) : ℝ≥0∞) := by
    rw [cycleSum, psum, ENNReal.coe_finset_sum]
    rfl
  rw [hsum] at hk
  have hk' : ((n + 1 : ℕ) : ℝ≥0) ≤ psum (fun k => (firstCycle v (nx^[k] x)).1.2) k := by
    rw [← ENNReal.coe_le_coe]
    simpa using hk
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hk'

/-- **`RootedCycleDecomposition` from forward regeneration, (R4) and (R5).** -/
theorem rootedCycleDecomposition_of_regeneration (μ : Measure RegLL) [IsProbabilityMeasure μ]
    (hreg : ForwardRegeneration v μ) (h4 : HoldExcIndep (μ.map (firstCycle v)))
    (h5 : StraddleAbsCont (μ.map (firstCycle v))) :
    RootedCycleDecomposition ((μ.prod μ).map pairReg) (μ.map (firstCycle v)) := by
  set ν := μ.map (firstCycle v) with hν
  have hgood := ae_all_good hreg
  have hunb := ae_unbounded hreg
  have hae : (rho ∘ pairReg) =ᵐ[μ.prod μ] (splice ∘ decomp v ∘ pairReg) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood,
      Measure.quasiMeasurePreserving_snd.ae hgood, Measure.quasiMeasurePreserving_fst.ae hunb,
      Measure.quasiMeasurePreserving_snd.ae hunb] with q g1 g2 g3 g4
    exact (splice_decomp (p := pairReg q) g1 g2 g3 g4).symm
  have hdec : decomp v ∘ pairReg =
      (fun ω : (ℕ → Cyc v) × (ℕ → Cyc v) => assemble ω.1 ω.2) ∘
        Prod.map (cycSeq v) (cycSeq v) := rfl
  unfold RootedCycleDecomposition mixedLaw
  rw [Measure.map_map measurable_rho measurable_pairReg, Measure.map_congr hae,
    ← Measure.map_map measurable_splice ((measurable_decomp v).comp measurable_pairReg), hdec,
    ← Measure.map_map measurable_assemble ((measurable_cycSeq v).prodMap (measurable_cycSeq v)),
    ← Measure.map_prod_map _ _ (measurable_cycSeq v) (measurable_cycSeq v),
    map_cycSeq μ hreg.shift hreg.indep]
  exact (assemble_absCont ν h4 h5).map measurable_splice

end ReflectedGMS.CycleDecomposition
