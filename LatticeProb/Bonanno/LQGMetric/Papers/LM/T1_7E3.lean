/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7E3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E2

/-!
# LM Lemma 5.4, kernel form: conditional independence of finitely many variables

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 5.4 (`lem-square-ind`, l. 992–997): "Under the conditional law
given `(h, θ)`, a.s. the internal metrics `{D(·,·;S ∩ U) : S ∈ 𝒮^ε_θ}` are conditionally
independent", proved (l. 995–996) from LM Lemma 2.4 (`lem-open-ind`, l. 548–560), whose proof
(l. 553–559) applies the two-set statement "`D(·,·;V)` and `D(·,·;U ∖ cl V)` are conditionally
independent given `h`" to `V` ranging over finite unions of the sets.

This file is the probabilistic part of that argument, turning the iterated two-set conditional
independence (event form `CondIndepEv`) into the kernel form used by Efron–Stein
(`t17e_es_pi`, T1_7E1): with `κ = condDistrib Z k μ` and `Y_i = φ_i ∘ Z`,

* `t17e_condExp_iInter` — `μ⟦⋂_{i∈T} Y_i⁻¹ t_i | k⟧ = ∏_{i∈T} μ⟦Y_i⁻¹ t_i | k⟧` a.s.;
* `t17e_box` — for each box: `κ(k ω)(Y ∈ ∏ t_i) = ∏_i κ(k ω)(Y_i ∈ t_i)` a.s.;
* `t17e_condDistrib_pi` — for `law(k)`-a.e. `g`: `(κ g).map Y = ⨂_i (κ g).map Y_i`.

The last step uses a countable π-system generating the (countably generated) target
(`t17eFinInter`, finite intersections of `countableGeneratingSet`). Own bookkeeping (standard
measure theory: π–λ uniqueness, `Measure.pi_eq_generateFrom`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric.LM

section CountablePi

variable {E : Type*}

/-- finite intersections of the sets of `S` (a π-system containing `univ`) -/
def t17eFinInter (S : Set (Set E)) : Set (Set E) := (fun t => ⋂₀ t) '' {t | t.Finite ∧ t ⊆ S}

lemma t17eFinInter_countable {S : Set (Set E)} (hS : S.Countable) : (t17eFinInter S).Countable :=
  (Set.countable_ofPred_finite_subset hS).image _

lemma t17eFinInter_isPiSystem (S : Set (Set E)) : IsPiSystem (t17eFinInter S) := by
  rintro _ ⟨t₁, ⟨h₁, h₁S⟩, rfl⟩ _ ⟨t₂, ⟨h₂, h₂S⟩, rfl⟩ _
  exact ⟨t₁ ∪ t₂, ⟨h₁.union h₂, union_subset h₁S h₂S⟩, sInter_union t₁ t₂⟩

lemma univ_mem_t17eFinInter (S : Set (Set E)) : univ ∈ t17eFinInter S :=
  ⟨∅, ⟨finite_empty, empty_subset _⟩, sInter_empty⟩

lemma subset_t17eFinInter (S : Set (Set E)) : S ⊆ t17eFinInter S := fun s hs =>
  ⟨{s}, ⟨finite_singleton s, singleton_subset_iff.2 hs⟩, sInter_singleton s⟩

lemma measurableSet_of_mem_t17eFinInter [MeasurableSpace E] {S : Set (Set E)} (hS : ∀ s ∈ S, MeasurableSet s)
    {s : Set E} (hs : s ∈ t17eFinInter S) : MeasurableSet s := by
  obtain ⟨t, ⟨ht, htS⟩, rfl⟩ := hs
  exact MeasurableSet.sInter ht.countable fun u hu => hS u (htS hu)

lemma generateFrom_t17eFinInter [mE : MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] :
    MeasurableSpace.generateFrom (t17eFinInter (MeasurableSpace.countableGeneratingSet E)) = mE := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun s hs =>
    measurableSet_of_mem_t17eFinInter (fun u hu =>
      MeasurableSpace.measurableSet_countableGeneratingSet hu) hs) ?_
  conv_lhs => rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α := E)]
  exact MeasurableSpace.generateFrom_mono (subset_t17eFinInter _)

end CountablePi

variable {Ω α β ι E : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] [mE : MeasurableSpace E]
  [Fintype ι] [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {k : Ω → α} {Z : Ω → β} {φ : ι → β → E}

/-- the iterated two-set conditional independence: `(Y_i)_{i ∈ T} ⟂ Y_j | k` for `j ∉ T` -/
def T17eSeqIndep (k : Ω → α) (Z : Ω → β) (φ : ι → β → E) (μ : Measure Ω) : Prop :=
  ∀ T : Finset ι, ∀ j ∉ T, CondIndepEv (MeasurableSpace.comap k mα)
    (⨆ i ∈ T, MeasurableSpace.comap (φ i ∘ Z) mE) (MeasurableSpace.comap (φ j ∘ Z) mE) μ

omit mβ [StandardBorelSpace β] [Nonempty β] [Fintype ι] in
/-- product formula for the conditional probabilities of an intersection -/
theorem t17e_condExp_iInter (hk : Measurable k) (hseq : T17eSeqIndep k Z φ μ) (t : ι → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (T : Finset ι) :
    μ⟦⋂ i ∈ T, (φ i ∘ Z) ⁻¹' t i | MeasurableSpace.comap k mα⟧ =ᵐ[μ]
      ∏ i ∈ T, μ⟦(φ i ∘ Z) ⁻¹' t i | MeasurableSpace.comap k mα⟧ := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ, indicator_univ,
      Finset.prod_empty]
    rw [condExp_const hk.comap_le]
    rfl
  | insert j T hj ih =>
    have ha : MeasurableSet[⨆ i ∈ T, MeasurableSpace.comap (φ i ∘ Z) mE]
        (⋂ i ∈ T, (φ i ∘ Z) ⁻¹' t i) :=
      MeasurableSet.biInter T.countable_toSet fun i hi =>
        (le_iSup₂ (f := fun i (_ : i ∈ T) => MeasurableSpace.comap (φ i ∘ Z) mE) i hi) _
          ⟨t i, ht i, rfl⟩
    have hb : MeasurableSet[MeasurableSpace.comap (φ j ∘ Z) mE] ((φ j ∘ Z) ⁻¹' t j) :=
      ⟨t j, ht j, rfl⟩
    have hci := hseq T j hj _ _ ha hb
    rw [Finset.set_biInter_insert, inter_comm, Finset.prod_insert hj]
    filter_upwards [hci, ih] with ω h1 h2
    rw [h1]
    simp only [Pi.mul_apply, Finset.prod_apply] at h2 ⊢
    rw [h2, mul_comm]

/-- **one box**: `κ(k ω)(Y ∈ ∏ t_i) = ∏_i κ(k ω)(Y_i ∈ t_i)` a.s. -/
theorem t17e_box (hk : Measurable k) (hZ : Measurable Z) (hφ : ∀ i, Measurable (φ i))
    (hseq : T17eSeqIndep k Z φ μ) (t : ι → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    ∀ᵐ ω ∂μ, condDistrib Z k μ (k ω) ((fun b i => φ i b) ⁻¹' univ.pi t) =
      ∏ i, condDistrib Z k μ (k ω) (φ i ⁻¹' t i) := by
  have hvm : Measurable fun b i => φ i b := Measurable.of_eval hφ
  have h0 := condDistrib_ae_eq_condExp (μ := μ) hk hZ (hvm (MeasurableSet.univ_pi ht))
  have hi : ∀ᵐ ω ∂μ, ∀ i, (condDistrib Z k μ (k ω)).real (φ i ⁻¹' t i) =
      (μ⟦Z ⁻¹' (φ i ⁻¹' t i) | MeasurableSpace.comap k mα⟧) ω :=
    ae_all_iff.2 fun i => condDistrib_ae_eq_condExp (μ := μ) hk hZ (hφ i (ht i))
  have hP := t17e_condExp_iInter hk hseq t ht Finset.univ
  have hpre : Z ⁻¹' ((fun b i => φ i b) ⁻¹' univ.pi t) = ⋂ i ∈ Finset.univ, (φ i ∘ Z) ⁻¹' t i := by
    ext; simp
  filter_upwards [h0, hi, hP] with ω h0 hi hP
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top fun i _ => measure_ne_top _ _)).1 ?_
  rw [ENNReal.toReal_prod]
  simp only [measureReal_def] at h0 hi
  rw [h0, hpre, hP, Finset.prod_apply]
  exact Finset.prod_congr rfl fun i _ => (hi i).symm

/-- **LM Lemma 5.4, kernel form**: for `law(k)`-a.e. `g`, under `κ g = condDistrib Z k μ g` the
variables `φ_i` are independent: `(κ g).map (φ_i)_i = ⨂_i (κ g).map φ_i`. -/
theorem t17e_condDistrib_pi [MeasurableSpace.CountablyGenerated E] (hk : Measurable k)
    (hZ : Measurable Z) (hφ : ∀ i, Measurable (φ i)) (hseq : T17eSeqIndep k Z φ μ) :
    ∀ᵐ g ∂μ.map k, (condDistrib Z k μ g).map (fun b i => φ i b) =
      Measure.pi fun i => (condDistrib Z k μ g).map (φ i) := by
  set κ := condDistrib Z k μ
  set C := t17eFinInter (MeasurableSpace.countableGeneratingSet E)
  have hCm : ∀ s ∈ C, MeasurableSet s := fun s hs => measurableSet_of_mem_t17eFinInter
    (fun u hu => MeasurableSpace.measurableSet_countableGeneratingSet hu) hs
  have hvm : Measurable fun b i => φ i b := Measurable.of_eval hφ
  set B : Set (ι → Set E) := {t | ∀ i, t i ∈ C}
  have hB : B.Countable := Set.countable_pi fun _ =>
    t17eFinInter_countable MeasurableSpace.countable_countableGeneratingSet
  set Q : Set α := ⋂ t ∈ B, {g | κ g ((fun b i => φ i b) ⁻¹' univ.pi t) = ∏ i, κ g (φ i ⁻¹' t i)}
  have hQ : MeasurableSet Q := MeasurableSet.biInter hB fun t ht =>
    measurableSet_eq_fun (κ.measurable_coe (hvm (MeasurableSet.univ_pi fun i => hCm _ (ht i))))
      (Finset.measurable_prod _ fun i _ => κ.measurable_coe (hφ i (hCm _ (ht i))))
  have hQω : ∀ᵐ ω ∂μ, k ω ∈ Q := by
    have : ∀ᵐ ω ∂μ, ∀ t ∈ B, κ (k ω) ((fun b i => φ i b) ⁻¹' univ.pi t) =
        ∏ i, κ (k ω) (φ i ⁻¹' t i) :=
      (ae_ball_iff hB).2 fun t ht => t17e_box hk hZ hφ hseq t fun i => hCm _ (ht i)
    filter_upwards [this] with ω hω
    simp only [Q, mem_iInter]
    exact hω
  filter_upwards [(ae_map_iff hk.aemeasurable hQ).2 hQω] with g hg
  refine (Measure.pi_eq_generateFrom (C := fun _ => C) (fun _ => generateFrom_t17eFinInter)
    (fun _ => t17eFinInter_isPiSystem _) (fun _ => ⟨fun _ => univ,
      fun _ => univ_mem_t17eFinInter _, fun _ => measure_lt_top _ _, iUnion_const _⟩)
    fun t ht => ?_).symm
  have hgt : κ g ((fun b i => φ i b) ⁻¹' univ.pi t) = ∏ i, κ g (φ i ⁻¹' t i) :=
    Set.mem_iInter₂.1 hg t ht
  rw [Measure.map_apply hvm (MeasurableSet.univ_pi fun i => hCm _ (ht i)), hgt]
  exact Finset.prod_congr rfl fun i _ => (Measure.map_apply (hφ i) (hCm _ (ht i))).symm

end LQGMetric.LM
