/-
Regular conditional probability measures and their invariant fibres.

The conditioning σ-algebra need not be countably generated. Kernel uniqueness
compares whole fibre measures on a common conull set. The fixed-event identity
alone has an exceptional set that may depend on the event.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- Conditional probabilities of measurable events are measurable in the conditioning σ-algebra. -/
theorem LatticeProb.measurable_conditionalMeasure {X : Type*} (m : MeasurableSpace X) [mX : MeasurableSpace X]
    [StandardBorelSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    {A : Set X} (hA : MeasurableSet A) :
    Measurable[m] (fun x => ProbabilityTheory.condExpKernel Q m x A) :=
  ProbabilityTheory.measurable_condExpKernel hA

/-- Every conditional measure is a probability measure, including at exceptional conditioning points. -/
theorem LatticeProb.isProbabilityMeasure_conditionalMeasure {X : Type*} (m : MeasurableSpace X) [mX : MeasurableSpace X]
    [StandardBorelSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    (x : X) :
    IsProbabilityMeasure (ProbabilityTheory.condExpKernel Q m x) := by infer_instance

/-- The regular conditional law disintegrates the original measure on every conditioning event. -/
theorem LatticeProb.setLIntegral_conditionalMeasure {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] [StandardBorelSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] (hm : m ≤ mX)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet[m] B) :
    (∫⁻ x in B, condExpKernel Q m x A ∂Q) = Q (A ∩ B) := by
  rw [← setLIntegral_trim hm (measurable_condExpKernel hA) hB,
    ← Measure.compProd_apply_prod hB hA, compProd_trim_condExpKernel hm,
    Measure.map_apply ((measurable_id'' hm).prodMk measurable_id) (hB.prod hA)]
  change Q (B ∩ A) = Q (A ∩ B)
  rw [Set.inter_comm]

/-- Integrating the conditional measures recovers the original measure. -/
theorem LatticeProb.lintegral_conditionalMeasure {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] [StandardBorelSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] (hm : m ≤ mX)
    {A : Set X} (hA : MeasurableSet A) :
    (∫⁻ x, condExpKernel Q m x A ∂Q) = Q A := by
  simpa only [Measure.restrict_univ, Set.inter_univ] using
    LatticeProb.setLIntegral_conditionalMeasure Q hm hA MeasurableSet.univ

/-- Every conull predicate remains conull in almost every conditional measure. -/
theorem LatticeProb.ae_ae_conditionalMeasure {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] [StandardBorelSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] (hm : m ≤ mX)
    {p : X → Prop} (hp : ∀ᵐ x ∂Q, p x) :
    ∀ᵐ x ∂Q, ∀ᵐ y ∂condExpKernel Q m x, p y := by
  apply ae_of_ae_trim hm
  apply Measure.ae_ae_of_ae_comp
  rwa [condExpKernel_comp_trim hm]

/-- Two probability kernels with the same joint measure agree as measures outside one null set. -/
theorem LatticeProb.ae_eq_kernel_of_compProd_eq {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (Q : Measure X) [IsFiniteMeasure Q] (K L : Kernel X Y)
    [IsMarkovKernel K] [IsMarkovKernel L] (h : Q ⊗ₘ K = Q ⊗ₘ L) :
    K =ᵐ[Q] L := by
  have hK := condKernel_compProd Q K
  have hL := condKernel_compProd Q L
  simp only [h] at hK
  exact hK.symm.trans hL

/-- For each conditioning event, its conditional probability is almost surely its indicator. -/
theorem LatticeProb.conditionalMeasure_event {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] [StandardBorelSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] (hm : m ≤ mX)
    {A : Set X} (hA : MeasurableSet[m] A) :
    (fun x => (condExpKernel Q m x).real A) =ᵐ[Q] A.indicator (fun _ => (1 : ℝ)) := by
  have h := condExpKernel_ae_eq_condExp (μ := Q) hm (hm A hA)
  rw [condExp_of_stronglyMeasurable hm (stronglyMeasurable_const.indicator hA)
    ((integrable_const (1 : ℝ)).indicator (hm A hA))] at h
  exact h

/-- Conditioning on invariant events gives a kernel that is pointwise unchanged by the transformation. -/
theorem LatticeProb.conditionalMeasure_comp {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (Q : Measure X) [IsProbabilityMeasure Q] (T : X → X) :
    (fun x => condExpKernel Q (MeasurableSpace.invariants T) (T x)) =
      (fun x => condExpKernel Q (MeasurableSpace.invariants T) x) := by
  funext x
  apply Measure.ext
  intro A hA
  exact congrFun (MeasurableSpace.comp_eq_of_measurable_invariants
    (measurable_condExpKernel (μ := Q) (m := MeasurableSpace.invariants T) hA)) x

/-- A measurable function of the conditioning information is constant almost surely within almost every fibre. -/
theorem LatticeProb.ae_ae_eq_of_measurable_conditionalMeasure {X Y : Type*}
    {m : MeasurableSpace X} [mX : MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableEq Y] (Q : Measure X) [IsProbabilityMeasure Q]
    (hm : m ≤ mX) {g : X → Y} (hg : Measurable[m] g) :
    ∀ᵐ x ∂Q, ∀ᵐ y ∂condExpKernel Q m x, g y = g x := by
  apply ae_of_ae_trim hm
  apply Measure.ae_ae_of_ae_compProd (μ := Q.trim hm) (κ := condExpKernel Q m)
    (p := fun z : X × X => g z.2 = g z.1)
  rw [compProd_trim_condExpKernel hm]
  letI : MeasurableSpace (X × X) := m.prod mX
  have hd : @Measurable X (X × X) mX (m.prod mX) (fun x => (id x, id x)) :=
    (measurable_id'' hm).prodMk measurable_id
  have hp : @MeasurableSet (X × X) (m.prod mX) {z | g z.2 = g z.1} :=
    measurableSet_eq_fun ((hg.mono hm le_rfl).comp measurable_snd) (hg.comp measurable_fst)
  exact (ae_map_iff (mβ := m.prod mX) hd.aemeasurable hp).2 (Filter.Eventually.of_forall fun _ => rfl)

/-- A preserving transformation fixing the conditioning events preserves the joint conditional law. -/
theorem LatticeProb.compProd_conditionalMeasure_map {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] [StandardBorelSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] (hm : m ≤ mX) {T : X → X}
    (hT : MeasurePreserving T Q Q) (hi : m ≤ MeasurableSpace.invariants T) :
    Q.trim hm ⊗ₘ (condExpKernel Q m).map T = Q.trim hm ⊗ₘ condExpKernel Q m  := by
  rw [Measure.compProd_map hT.measurable, compProd_trim_condExpKernel hm]
  have hd : @Measurable X (X × X) mX (m.prod mX) (fun x => (id x, id x)) :=
    (measurable_id'' hm).prodMk measurable_id
  rw [Measure.map_map (measurable_id.prodMap hT.measurable) hd]
  apply Measure.ext_prod
  intro B A hB hA
  rw [Measure.map_apply ((measurable_id.prodMap hT.measurable).comp hd) (hB.prod hA),
    Measure.map_apply hd (hB.prod hA)]
  change Q (B ∩ T ⁻¹' A) = Q (B ∩ A)
  calc
    Q (B ∩ T ⁻¹' A) = Q (T ⁻¹' (B ∩ A)) := by
      rw [Set.preimage_inter, (hi B hB).2]
    _ = Q (B ∩ A) := hT.measure_preimage ((hm B hB).inter hA).nullMeasurableSet

/-- Invariance of a joint kernel measure implies invariance of almost every fibre measure. -/
theorem LatticeProb.ae_measurePreserving_of_compProd_map_eq {D X : Type*}
    [MeasurableSpace D] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (Q : Measure D) [IsFiniteMeasure Q] (K : Kernel D X) [IsMarkovKernel K]
    {T : X → X} (hT : Measurable T) (h : Q ⊗ₘ K.map T = Q ⊗ₘ K) :
    ∀ᵐ x ∂Q, MeasurePreserving T (K x) (K x) := by
  letI : IsMarkovKernel (K.map T) := Kernel.IsMarkovKernel.map K hT
  have hleft := condKernel_compProd Q (K.map T)
  have hright := condKernel_compProd Q K
  simp only [h] at hleft
  have heq := hleft.symm.trans hright
  filter_upwards [heq] with x hx
  exact ⟨hT, (Kernel.map_apply K hT x).symm.trans hx⟩

/-- Almost every conditional measure is preserved by a transformation that fixes the conditioning events. -/
theorem LatticeProb.ae_measurePreserving_conditionalMeasure {X : Type*}
    {m : MeasurableSpace X} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] (hm : m ≤ mX) {T : X → X}
    (hT : MeasurePreserving T Q Q) (hi : m ≤ MeasurableSpace.invariants T) :
    ∀ᵐ x ∂Q, MeasurePreserving T (condExpKernel Q m x) (condExpKernel Q m x) := by
  letI : Nonempty X := nonempty_of_isProbabilityMeasure Q
  apply ae_of_ae_trim hm
  exact @LatticeProb.ae_measurePreserving_of_compProd_map_eq X X m mX _ _ (Q.trim hm) _
    (condExpKernel Q m) _ T hT.measurable
    (LatticeProb.compProd_conditionalMeasure_map Q hm hT hi)

/-- Regular conditional probability measures with the set-integral identity and preservation of conull predicates. -/
theorem LatticeProb.exists_conditionalMeasures {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] [StandardBorelSpace X] (Q : Measure X)
    [IsProbabilityMeasure Q] (hm : m ≤ mX) {p : X → Prop} (hp : ∀ᵐ x ∂Q, p x) :
    ∃ K : X → Measure X,
      (∀ x, IsProbabilityMeasure (K x)) ∧
      (∀ A : Set X, MeasurableSet A → Measurable[m] fun x => K x A) ∧
      (∀ A : Set X, MeasurableSet A → ∀ B : Set X, MeasurableSet[m] B →
        (∫⁻ x in B, K x A ∂Q) = Q (A ∩ B)) ∧
      (∀ᵐ x ∂Q, ∀ᵐ y ∂K x, p y) := by
  refine ⟨fun x => condExpKernel Q m x, ?_, ?_, ?_, ?_⟩
  · intro x
    infer_instance
  · intro A hA
    exact measurable_condExpKernel hA
  · intro A hA B hB
    exact LatticeProb.setLIntegral_conditionalMeasure Q hm hA hB
  · exact LatticeProb.ae_ae_conditionalMeasure Q hm hp

/-- Disintegration with a common conull set of invariant fibres for a countable family of transformations. -/
theorem LatticeProb.exists_invariant_conditionalMeasures {X I : Type*} [Countable I]
    {m : MeasurableSpace X} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] (hm : m ≤ mX)
    (T : I → X → X) (hT : ∀ i, MeasurePreserving (T i) Q Q)
    (hi : ∀ i, m ≤ MeasurableSpace.invariants (T i))
    {p : X → Prop} (hp : ∀ᵐ x ∂Q, p x) :
    ∃ K : X → Measure X,
      (∀ x, IsProbabilityMeasure (K x)) ∧
      (∀ A : Set X, MeasurableSet A → Measurable[m] fun x => K x A) ∧
      (∀ A : Set X, MeasurableSet A → ∀ B : Set X, MeasurableSet[m] B →
        (∫⁻ x in B, K x A ∂Q) = Q (A ∩ B)) ∧
      (∀ᵐ x ∂Q, (∀ᵐ y ∂K x, p y) ∧ ∀ i, MeasurePreserving (T i) (K x) (K x)) := by
  refine ⟨fun x => condExpKernel Q m x, ?_, ?_, ?_, ?_⟩
  · intro x
    infer_instance
  · intro A hA
    exact measurable_condExpKernel hA
  · intro A hA B hB
    exact LatticeProb.setLIntegral_conditionalMeasure Q hm hA hB
  · exact (LatticeProb.ae_ae_conditionalMeasure Q hm hp).and
      (ae_all_iff.mpr fun i => LatticeProb.ae_measurePreserving_conditionalMeasure Q hm (hT i) (hi i))
