/-
Ergodic decomposition on a standard Borel probability space.

Disintegrate over the invariant σ-algebra. The conditional measures preserve
the transformation by uniqueness of disintegration. Bounded Birkhoff limits
are conditional expectations, and hence are constant within almost every
conditional fibre. A countable generating π-system provides one conull set
on which this holds simultaneously. On each remaining fibre, every invariant
event is independent of that generating family and therefore has mass zero
or one.

No countable-generation assumption on the invariant σ-algebra is needed.
-/
import LatticeProb.Prob.ConditionalMeasure
import LatticeProb.Prob.Kingman
import LatticeProb.Prob.ZeroOne

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The upper Birkhoff limit of a bounded measurable observable is invariant-measurable. -/
theorem LatticeProb.measurable_bLimsup_invariants {X : Type*} [MeasurableSpace X]
    {T : X → X} {f : X → ℝ} (hT : Measurable T) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    Measurable[MeasurableSpace.invariants T] (LatticeProb.bLimsup T f) := by
  refine MeasurableSpace.measurable_invariants_dom.mpr
    ⟨LatticeProb.measurable_bLimsup hT hf, ?_⟩
  intro s _
  ext x
  simp only [Set.mem_preimage, Function.comp_apply, LatticeProb.bLimsup_comp hC hb]

/-- A uniform bound on an observable bounds its upper Birkhoff limit. -/
theorem LatticeProb.abs_bLimsup_le {X : Type*} [MeasurableSpace X]
    {T : X → X} {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C) (x : X) : |LatticeProb.bLimsup T f x| ≤ C := by
  have hu := LatticeProb.isBoundedUnder_le_of
    (fun n => (abs_le.mp (LatticeProb.abs_bAvg_le (T := T) hC hb n x)).2)
  have hl := LatticeProb.isBoundedUnder_ge_of
    (fun n => (abs_le.mp (LatticeProb.abs_bAvg_le (T := T) hC hb n x)).1)
  apply abs_le.mpr
  constructor
  · exact (le_liminf_of_le hu.isCoboundedUnder_ge
      (Filter.Eventually.of_forall fun n =>
        (abs_le.mp (LatticeProb.abs_bAvg_le hC hb n x)).1)).trans
      (LatticeProb.bLiminf_le_bLimsup hC hb x)
  · exact limsup_le_of_le hl.isCoboundedUnder_le
      (Filter.Eventually.of_forall fun n =>
        (abs_le.mp (LatticeProb.abs_bAvg_le hC hb n x)).2)

/-- Every nonempty Birkhoff average has the same integral as its observable. -/
theorem LatticeProb.integral_bAvg {X : Type*} [MeasurableSpace X]
    {Q : Measure X} {T : X → X} {f : X → ℝ}
    (hT : MeasurePreserving T Q Q) (hf : Integrable f Q) {n : ℕ} (hn : n ≠ 0) :
    (∫ x, LatticeProb.bAvg T f n x ∂Q) = ∫ x, f x ∂Q := by
  unfold LatticeProb.bAvg birkhoffSum
  rw [integral_div, integral_finsetSum _ (fun k _ => LatticeProb.integrable_comp_iterate hT hf k)]
  simp_rw [LatticeProb.integral_comp_iterate hT hf]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

/-- Dominated convergence preserves the mean of a bounded Birkhoff limit. -/
theorem LatticeProb.integral_bLimsup_of_bounded {X : Type*} [MeasurableSpace X]
    {Q : Measure X} [IsFiniteMeasure Q] {T : X → X} {f : X → ℝ}
    (hT : MeasurePreserving T Q Q) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C)
    (hmean : ∀ n : ℕ, (∫ x, LatticeProb.bAvg T f (n+1) x ∂Q) = ∫ x, f x ∂Q) :
    (∫ x, LatticeProb.bLimsup T f x ∂Q) = ∫ x, f x ∂Q := by
  have hfi : Integrable f Q := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hc : ∀ᵐ x ∂Q, Filter.Tendsto (fun n : ℕ => LatticeProb.bAvg T f (n+1) x)
      Filter.atTop (nhds (LatticeProb.bLimsup T f x)) := by
    filter_upwards [LatticeProb.ae_tendsto_bLimsup hT hf hfi] with x hx
    exact hx.comp (tendsto_add_atTop_nat 1)
  have hd : ∀ n : ℕ, ∀ᵐ x ∂Q, ‖LatticeProb.bAvg T f (n+1) x‖ ≤ C := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using LatticeProb.abs_bAvg_le hC hb (n+1) x
  have hl := tendsto_integral_of_dominated_convergence (fun _ : X => C)
    (fun n => (LatticeProb.measurable_bAvg hT.measurable hf (n+1)).aestronglyMeasurable)
    (integrable_const C) hd hc
  simp only [hmean] at hl
  exact (tendsto_nhds_unique tendsto_const_nhds hl).symm

/-- The bounded Birkhoff limit is the conditional expectation on invariant events. -/
theorem LatticeProb.bLimsup_ae_eq_condExp_of_bounded {X : Type*} [MeasurableSpace X]
    {Q : Measure X} [IsFiniteMeasure Q] {T : X → X} {f : X → ℝ}
    (hT : MeasurePreserving T Q Q) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    LatticeProb.bLimsup T f =ᵐ[Q] Q[f | MeasurableSpace.invariants T] := by
  have hfi : Integrable f Q := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hgi : Integrable (LatticeProb.bLimsup T f) Q := Integrable.of_bound
    (LatticeProb.measurable_bLimsup hT.measurable hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using LatticeProb.abs_bLimsup_le (T := T) hC hb x)
  refine ae_eq_condExp_of_forall_setIntegral_eq (MeasurableSpace.invariants_le T) hfi
    (fun _ _ _ => hgi.integrableOn) ?_
    (LatticeProb.measurable_bLimsup_invariants hT.measurable hf hC hb).aestronglyMeasurable
  intro B hB _
  have hTB := LatticeProb.measurePreserving_restrict hT hB.1 hB.2
  exact LatticeProb.integral_bLimsup_of_bounded hTB hf hC hb
    (fun n => LatticeProb.integral_bAvg hTB hfi.restrict (Nat.succ_ne_zero n))

/-- A constant Birkhoff limit determines the integral on every invariant event. -/
theorem LatticeProb.setIntegral_eq_mul_of_bAvg_tendsto {X : Type*} [MeasurableSpace X]
    {Q : Measure X} [IsFiniteMeasure Q] {T : X → X} {f : X → ℝ}
    (hT : MeasurePreserving T Q Q) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) {L : ℝ}
    (hlim : ∀ᵐ x ∂Q, Tendsto (fun n => LatticeProb.bAvg T f n x) atTop (nhds L))
    {B : Set X} (hB : MeasurableSet[MeasurableSpace.invariants T] B) :
    (∫ x in B, f x ∂Q) = Q.real B * L := by
  have hfi : Integrable f Q := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hTB := LatticeProb.measurePreserving_restrict hT hB.1 hB.2
  have hmean : ∀ n : ℕ, (∫ x in B, LatticeProb.bAvg T f (n+1) x ∂Q) = ∫ x in B, f x ∂Q :=
    fun n => LatticeProb.integral_bAvg hTB hfi.restrict (Nat.succ_ne_zero n)
  have hc : ∀ᵐ x ∂Q.restrict B, Tendsto (fun n : ℕ => LatticeProb.bAvg T f (n+1) x)
      atTop (nhds L) := by
    filter_upwards [ae_restrict_le hlim] with x hx
    exact hx.comp (tendsto_add_atTop_nat 1)
  have hd : ∀ n : ℕ, ∀ᵐ x ∂Q.restrict B, ‖LatticeProb.bAvg T f (n+1) x‖ ≤ C := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using LatticeProb.abs_bAvg_le hC hb (n+1) x
  have hl := tendsto_integral_of_dominated_convergence (fun _ : X => C)
    (fun n => (LatticeProb.measurable_bAvg hT.measurable hf (n+1)).aestronglyMeasurable)
    (integrable_const C) hd hc
  simp only [hmean] at hl
  have heq := tendsto_nhds_unique tendsto_const_nhds hl
  simpa only [setIntegral_const, smul_eq_mul] using heq

/-- A countably generated measurable space admits a countable generating π-system. -/
theorem LatticeProb.exists_countable_generating_piSystem {X : Type*}
    [mX : MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] :
    ∃ C : Set (Set X), C.Countable ∧ IsPiSystem C ∧
      mX = MeasurableSpace.generateFrom C := by
  let G : ℕ → Set X := MeasurableSpace.natGeneratingSequence X
  let F : Finset ℕ → Set X := fun s => ⋂ n ∈ s, G n
  refine ⟨Set.range F, Set.countable_range F, ?_, ?_⟩
  · rintro A ⟨s, rfl⟩ B ⟨t, rfl⟩ _
    refine ⟨s ∪ t, ?_⟩
    ext x
    simp only [F, Set.mem_iInter, Finset.mem_union, Set.mem_inter_iff]
    simp only [or_imp, forall_and]
  · apply le_antisymm
    · calc
        mX = MeasurableSpace.generateFrom (Set.range G) :=
          (MeasurableSpace.generateFrom_natGeneratingSequence X).symm
        _ ≤ MeasurableSpace.generateFrom (Set.range F) := by
          apply MeasurableSpace.generateFrom_mono
          rintro A ⟨n, rfl⟩
          exact ⟨{n}, by ext x; simp [F]⟩
    · apply MeasurableSpace.generateFrom_le
      rintro A ⟨s, rfl⟩
      exact MeasurableSet.biInter s.countable_toSet fun n _ =>
        MeasurableSpace.measurableSet_natGeneratingSequence n

/-- An event independent of a generating π-system has probability zero or one. -/
theorem LatticeProb.measure_zero_or_one_of_inter_eq_mul {X : Type*}
    [mX : MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    {C : Set (Set X)} (hgen : mX = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) {B : Set X} (hB : MeasurableSet B)
    (h : ∀ A ∈ C, Q (A ∩ B) = Q B * Q A) : Q B = 0 ∨ Q B = 1 := by
  have heq : Q.restrict B = Q B • Q := by
    refine ext_of_generate_finite C hgen hpi ?_ (by simp)
    intro A hA
    have hAm : MeasurableSet A := by
      rw [hgen]
      exact MeasurableSpace.measurableSet_generateFrom hA
    simpa only [Measure.restrict_apply hAm, Measure.smul_apply, smul_eq_mul] using h A hA
  have hh := congrArg (fun ν : Measure X => ν B) heq
  simp only [Measure.restrict_apply hB, Set.inter_self, Measure.smul_apply, smul_eq_mul] at hh
  by_cases h0 : Q B = 0
  · exact Or.inl h0
  · right
    apply (ENNReal.mul_right_inj h0 (measure_ne_top Q B)).mp
    simpa only [mul_one] using hh.symm

/-- Bounded Birkhoff averages converge to their conditional-fibre means within almost every fibre. -/
theorem LatticeProb.ae_ae_bAvg_conditionalMeasure {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    {T : X → X} {f : X → ℝ} (hT : MeasurePreserving T Q Q) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    ∀ᵐ x ∂Q, ∀ᵐ y ∂condExpKernel Q (MeasurableSpace.invariants T) x,
      Tendsto (fun n => LatticeProb.bAvg T f n y) atTop
        (nhds (∫ z, f z ∂condExpKernel Q (MeasurableSpace.invariants T) x)) := by
  have hfi : Integrable f Q := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hm := MeasurableSpace.invariants_le T
  have hmean := (LatticeProb.bLimsup_ae_eq_condExp_of_bounded hT hf hC hb).trans
    (condExp_ae_eq_integral_condExpKernel hm hfi)
  have hconv := LatticeProb.ae_ae_conditionalMeasure Q hm
    (LatticeProb.ae_tendsto_bLimsup hT hf hfi)
  have hconst := LatticeProb.ae_ae_eq_of_measurable_conditionalMeasure Q hm
    (LatticeProb.measurable_bLimsup_invariants hT.measurable hf hC hb)
  filter_upwards [hmean, hconv, hconst] with x hx hc he
  filter_upwards [hc, he] with y hy hxy
  simpa only [hxy, hx] using hy

/-- Convergence to the mean on a generating π-system implies ergodicity of invariant events. -/
theorem LatticeProb.preErgodic_of_bAvg_piSystem {X : Type*} [mX : MeasurableSpace X]
    (Q : Measure X) [IsProbabilityMeasure Q] {T : X → X}
    (hT : MeasurePreserving T Q Q) {C : Set (Set X)}
    (hgen : mX = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (hlim : ∀ A ∈ C, ∀ᵐ x ∂Q,
      Tendsto (fun n => LatticeProb.bAvg T (A.indicator (fun _ => (1 : ℝ))) n x)
        atTop (nhds (Q.real A))) : PreErgodic T Q := by
  apply LatticeProb.preErgodic_of_prob_eq_zero_or_one
  intro B hB hBinv
  apply LatticeProb.measure_zero_or_one_of_inter_eq_mul Q hgen hpi hB
  intro A hA
  have hAm : MeasurableSet A := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  have hfm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hAm
  have hfb : ∀ x : X, |A.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    classical
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hi := LatticeProb.setIntegral_eq_mul_of_bAvg_tendsto hT hfm zero_le_one hfb
    (hlim A hA) (show MeasurableSet[MeasurableSpace.invariants T] B from ⟨hB, hBinv⟩)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top Q (A ∩ B))
    (ENNReal.mul_ne_top (measure_ne_top Q B) (measure_ne_top Q A))).mp
  simpa only [integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply hAm, ENNReal.toReal_mul] using hi

/-- The conditional measures on the invariant σ-algebra are almost surely ergodic. -/
theorem LatticeProb.ae_ergodic_conditionalMeasure {X : Type*} [mX : MeasurableSpace X]
    [StandardBorelSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    {T : X → X} (hT : MeasurePreserving T Q Q) :
    ∀ᵐ x ∂Q, Ergodic T (condExpKernel Q (MeasurableSpace.invariants T) x) := by
  obtain ⟨C, hcount, hpi, hgen⟩ := LatticeProb.exists_countable_generating_piSystem (X := X)
  letI : Countable C := hcount.to_subtype
  have hc : ∀ A : C, ∀ᵐ x ∂Q,
      ∀ᵐ y ∂condExpKernel Q (MeasurableSpace.invariants T) x,
        Tendsto (fun n => LatticeProb.bAvg T (A.val.indicator (fun _ => (1 : ℝ))) n y)
          atTop (nhds ((condExpKernel Q (MeasurableSpace.invariants T) x).real A.val)) := by
    intro A
    have hAm : MeasurableSet A.val := by
      rw [hgen]
      exact MeasurableSpace.measurableSet_generateFrom A.property
    have hfb : ∀ y : X, |A.val.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
      classical
      intro y
      by_cases hy : y ∈ A.val <;> simp [hy]
    simpa only [integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_one] using
      LatticeProb.ae_ae_bAvg_conditionalMeasure Q hT (measurable_const.indicator hAm)
        zero_le_one hfb
  have hall := ae_all_iff.mpr hc
  filter_upwards [hall, LatticeProb.ae_measurePreserving_conditionalMeasure Q
    (MeasurableSpace.invariants_le T) hT le_rfl] with x hx hTx
  refine ⟨hTx, LatticeProb.preErgodic_of_bAvg_piSystem _ hTx hgen hpi ?_⟩
  intro A hA
  exact hx ⟨A, hA⟩

/-- Ergodic decomposition of a probability-preserving transformation on a standard Borel space, with preservation of any conull predicate. -/
theorem LatticeProb.ergodic_decomposition {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    {T : X → X} (hT : MeasurePreserving T Q Q) {p : X → Prop} (hp : ∀ᵐ x ∂Q, p x) :
    ∃ K : X → Measure X,
      (∀ x, IsProbabilityMeasure (K x)) ∧
      (∀ A : Set X, MeasurableSet A →
        Measurable[MeasurableSpace.invariants T] fun x => K x A) ∧
      (∀ A : Set X, MeasurableSet A → ∀ B : Set X,
        MeasurableSet[MeasurableSpace.invariants T] B →
          (∫⁻ x in B, K x A ∂Q) = Q (A ∩ B)) ∧
      (∀ᵐ x ∂Q, (∀ᵐ y ∂K x, p y) ∧ Ergodic T (K x)) := by
  refine ⟨fun x => condExpKernel Q (MeasurableSpace.invariants T) x, ?_, ?_, ?_, ?_⟩
  · intro x
    infer_instance
  · intro A hA
    exact measurable_condExpKernel hA
  · intro A hA B hB
    exact LatticeProb.setLIntegral_conditionalMeasure Q (MeasurableSpace.invariants_le T) hA hB
  · exact (LatticeProb.ae_ae_conditionalMeasure Q (MeasurableSpace.invariants_le T) hp).and
      (LatticeProb.ae_ergodic_conditionalMeasure Q hT)
