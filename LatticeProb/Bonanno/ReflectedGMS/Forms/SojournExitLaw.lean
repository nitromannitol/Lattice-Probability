/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SojournExitLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnConditional

/-!
# The joint law of a sojourn: start time, holding length and exit vertex

Let `τ` be a completed stopping time of the reflected walk and `ρ` the exit time from the
current vertex after `τ`.  On the event `{τ < ∞, X_τ = x}`, the checked one-step law
`TargetReturnConditional.measure_exitPair_completed` gives, for every stopped-past event `F`,

  `P_z(F ∩ {X_τ = x} ∩ {ρ − τ ∈ B, X_ρ = v}) = P_z(F ∩ {X_τ = x}) · Exp(w x)(B) · c(x,v)/π(x)`.

Taking `F = {τ ∈ C}` and using uniqueness of product measures, this file upgrades that to the
**joint law** of the triple `(τ, (ρ − τ, X_ρ))` under `P_z` restricted to `{X_τ = x}`: it is
the product of the law of `τ` with `Exp(w x) ⊗ (c(x,·)/π(x))`.  The corollary
`lintegral_exitTriple` is Tonelli for this product, which is what the sojourn-by-sojourn energy
accounting consumes: any nonnegative functional of `(τ, ρ − τ, X_ρ)` integrates by first
averaging the holding length and the exit vertex against their explicit laws, `τ` being
frozen.

Also recorded: on `{X_τ = x}` the sojourn almost surely ends at a finite time and at a vertex.
No jump measure, compensator or bracket is asserted.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.SojournExitLaw

open ReflectedWalk ReflectedWalk.Theorem16 TargetReturnConditional

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-! ## The exit kernel -/

/-- Every subset of the discrete state space `Option V` is measurable. -/
theorem measurableSet_option' (S : Set (Option V)) : MeasurableSet S :=
  MeasurableSpace.measurableSet_top

/-- The one-step exit law from `x`: `∑_v c(x,v)/π(x) · δ_{some v}` on `Option V`. -/
noncomputable def exitKernel (G : ConductanceGraph V) (x : V) : Measure (Option V) :=
  Measure.sum fun v : V => ENNReal.ofReal (G.c x v / G.pi x) • Measure.dirac (some v)

theorem exitKernel_apply (G : ConductanceGraph V) (x : V) (S : Set (Option V)) :
    exitKernel G x S = ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) * S.indicator 1 (some v) := by
  rw [exitKernel, Measure.sum_apply _ (measurableSet_option' S)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_option' S)]

theorem lintegral_exitKernel (G : ConductanceGraph V) (x : V) (f : Option V → ℝ≥0∞) :
    (∫⁻ q, f q ∂exitKernel G x) = ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) * f (some v) := by
  rw [exitKernel, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul, lintegral_dirac]

/-- The exit probabilities from `x` sum to one. -/
theorem tsum_ofReal_exit_eq_one (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (x : V) : ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) = 1 := by
  have h := G.tsum_transProb hG (Finset.singleton_nonempty x) x
  simp_rw [G.transProb_of_mem hG (Finset.mem_singleton_self x)] at h
  have hs : Summable (fun v => G.c x v / G.pi x) :=
    (G.summable_transProb hG {x} x).congr fun v =>
      G.transProb_of_mem hG (Finset.mem_singleton_self x) v
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun v => div_nonneg (G.c_nonneg x v) (G.pi_pos_of_connected hG x).le) hs, h,
    ENNReal.ofReal_one]

theorem exitKernel_univ (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected) (x : V) :
    exitKernel G x univ = 1 := by
  rw [exitKernel_apply]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  exact tsum_ofReal_exit_eq_one G hG x

theorem isFiniteMeasure_exitKernel (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (x : V) : IsFiniteMeasure (exitKernel G x) :=
  ⟨by rw [exitKernel_univ G hG x]; exact ENNReal.one_lt_top⟩

/-! ## The exit triple -/

/-- The joint observable `(τ, (ρ − τ, X_ρ))`, where `ρ` is the first exit from `x` after `τ`. -/
noncomputable def exitTriple {Ω : Type u} (X : ℝ≥0 → Ω → Option V) (x : V)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 × (WithTop ℝ≥0 × Option V) :=
  (τ ω, (hitAfter X {s : Option V | s ≠ some x} τ ω - τ ω,
    stoppedValue X (hitAfter X {s : Option V | s ≠ some x} τ) ω))

section Process

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected) (z x : V)
  {τ : PF.Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ (PF.P z))
  (hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ)

include h hτm

theorem aemeasurable_exitTime :
    AEMeasurable (hitAfter PF.X {s : Option V | s ≠ some x} τ) (PF.P z) :=
  aemeasurable_hitAfter PF.measurable_X (h z).2.2.1 (h z).2.2.2.1 (admissibleTarget_ne x) hτm

theorem aemeasurable_holding :
    AEMeasurable (fun ω => hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω) (PF.P z) :=
  measurable_sub_withTop.comp_aemeasurable ((aemeasurable_exitTime h z x hτm).prodMk hτm)

theorem aemeasurable_exitTriple : AEMeasurable (exitTriple PF.X x τ) (PF.P z) := by
  have hXρ : AEMeasurable (stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ))
      (PF.P z) :=
    aemeasurable_stoppedValue PF.measurable_X (h z).2.2.1 (h z).2.2.2.1
      (aemeasurable_exitTime h z x hτm)
  exact hτm.prodMk ((aemeasurable_holding h z x hτm).prodMk hXρ)

include hG hτ

/-- **The one-step exit law on a `τ`-cylinder.**  `measure_exitPair_completed` at
`F = {τ ∈ C}`, which is a stopped-past event since `τ` is `𝓕_τ`-measurable. -/
theorem measure_exit_rect {C B : Set (WithTop ℝ≥0)} (hC : MeasurableSet C)
    (hB : MeasurableSet B) (v : V) :
    PF.P z ({ω | τ ω ∈ C} ∩ stopEvent PF.X τ x ∩
        ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ B} ∩
          stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) =
      PF.P z ({ω | τ ω ∈ C} ∩ stopEvent PF.X τ x) *
        (((expMeasure (w x)).map toWithTop) B * ENNReal.ofReal (G.c x v / G.pi x)) :=
  measure_exitPair_completed h hG z hτm hτ
    ((AEStoppedTime.of_le hτ fun _ => le_rfl).preimage hτ hC)
    (Finset.singleton_nonempty x) (Finset.mem_singleton_self x) hB v

/-- **On `{τ < ∞, X_τ = x}` the sojourn almost surely ends at a finite time, at a vertex.** -/
theorem ae_exit_vertex_of_stopEvent :
    ∀ᵐ ω ∂PF.P z, ω ∈ stopEvent PF.X τ x →
      hitAfter PF.X {s : Option V | s ≠ some x} τ ω ≠ ⊤ ∧
        ∃ v : V, stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω = some v := by
  have hii : RightContinuous (PF.P z) PF.X := (h z).2.2.1
  have hR : RightContinuousAtInfty (PF.P z) PF.X := (h z).2.2.2.1
  have hρm := aemeasurable_exitTime h z x hτm
  have hEnull : NullMeasurableSet (stopEvent PF.X τ x) (PF.P z) :=
    nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm x
  have hEvnull : ∀ v, NullMeasurableSet (stopEvent PF.X τ x ∩
      stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v) (PF.P z) := fun v =>
    hEnull.inter (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hρm v)
  have hEv : ∀ v, PF.P z (stopEvent PF.X τ x ∩
      stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v) =
      PF.P z (stopEvent PF.X τ x) * ENNReal.ofReal (G.c x v / G.pi x) := by
    intro v
    have hm := measure_exit_rect h hG z x hτm hτ (C := univ) (B := univ)
      MeasurableSet.univ MeasurableSet.univ v
    have e1 : {ω : PF.Ω | τ ω ∈ (univ : Set (WithTop ℝ≥0))} ∩ stopEvent PF.X τ x =
        stopEvent PF.X τ x := by
      ext ω
      simp
    have e2 : {ω : PF.Ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈
        (univ : Set (WithTop ℝ≥0))} ∩
          stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v =
        stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v := by
      ext ω
      simp
    rw [e1, e2, map_toWithTop_expMeasure_univ h x, one_mul] at hm
    exact hm
  have hunion : PF.P z (⋃ v, stopEvent PF.X τ x ∩
      stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v) =
      PF.P z (stopEvent PF.X τ x) := by
    rw [measure_iUnion₀ (fun v v' hvv' => ((disjoint_stopEvent hvv').mono
      inter_subset_right inter_subset_right).aedisjoint) hEvnull]
    simp_rw [hEv]
    rw [ENNReal.tsum_mul_left, tsum_ofReal_exit_eq_one G hG x, mul_one]
  have hdiff : PF.P z (stopEvent PF.X τ x \ ⋃ v, stopEvent PF.X τ x ∩
      stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v) = 0 := by
    rw [measure_diff (iUnion_subset fun v => inter_subset_left)
      (NullMeasurableSet.iUnion hEvnull) (measure_ne_top _ _), hunion, tsub_self]
  have hae : ∀ᵐ ω ∂PF.P z, ω ∉ stopEvent PF.X τ x \ ⋃ v, stopEvent PF.X τ x ∩
      stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v := by
    rw [ae_iff]
    simpa only [not_not, setOf_mem_eq] using hdiff
  filter_upwards [hae] with ω hω hE
  have hmem : ω ∈ ⋃ v, stopEvent PF.X τ x ∩
      stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v := by
    by_contra hn
    exact hω ⟨hE, hn⟩
  obtain ⟨v, hv⟩ := mem_iUnion.1 hmem
  exact ⟨hv.2.1, v, hv.2.2⟩

/-- **The joint law of `(τ, (ρ − τ, X_ρ))` on `{τ < ∞, X_τ = x}` is a product**: the law of
`τ` times `Exp(w x) ⊗ (c(x,·)/π(x))`. -/
theorem map_exitTriple_eq :
    ((PF.P z).restrict (stopEvent PF.X τ x)).map (exitTriple PF.X x τ) =
      (((PF.P z).restrict (stopEvent PF.X τ x)).map τ).prod
        (((expMeasure (w x)).map toWithTop).prod (exitKernel G x)) := by
  have hii : RightContinuous (PF.P z) PF.X := (h z).2.2.1
  have hR : RightContinuousAtInfty (PF.P z) PF.X := (h z).2.2.2.1
  have hρm := aemeasurable_exitTime h z x hτm
  have hLm := aemeasurable_holding h z x hτm
  haveI : IsProbabilityMeasure ((expMeasure (w x)).map toWithTop) :=
    ⟨map_toWithTop_expMeasure_univ h x⟩
  haveI : IsFiniteMeasure (exitKernel G x) := isFiniteMeasure_exitKernel G hG x
  have hΦ : AEMeasurable (exitTriple PF.X x τ) ((PF.P z).restrict (stopEvent PF.X τ x)) :=
    (aemeasurable_exitTriple h z x hτm).restrict
  have hτμ : AEMeasurable τ ((PF.P z).restrict (stopEvent PF.X τ x)) := hτm.restrict
  have hEnull : NullMeasurableSet (stopEvent PF.X τ x) (PF.P z) :=
    nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm x
  have hae := ae_exit_vertex_of_stopEvent h hG z x hτm hτ
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [Measure.map_apply_of_aemeasurable hΦ (hs.prod ht),
    Measure.map_apply_of_aemeasurable hτμ hs,
    Measure.restrict_apply₀ (hΦ.nullMeasurable (hs.prod ht)),
    Measure.restrict_apply₀ (hτμ.nullMeasurable hs)]
  change PF.P z (exitTriple PF.X x τ ⁻¹' (s ×ˢ t) ∩ stopEvent PF.X τ x) =
    PF.P z ({ω | τ ω ∈ s} ∩ stopEvent PF.X τ x) * _
  -- the sections of `t` at the vertices
  let tv : V → Set (WithTop ℝ≥0) := fun v => (fun l => (l, some v)) ⁻¹' t
  have htv : ∀ v, MeasurableSet (tv v) := fun v => (measurable_id.prodMk measurable_const) ht
  have hnull : ∀ v, NullMeasurableSet ({ω | τ ω ∈ s} ∩ stopEvent PF.X τ x ∩
      ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ tv v} ∩
        stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) (PF.P z) := fun v =>
    ((hτm.nullMeasurable hs).inter hEnull).inter
      ((hLm.nullMeasurable (htv v)).inter
        (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hρm v))
  have hdisj : Pairwise (Function.onFun (AEDisjoint (PF.P z)) fun v : V =>
      {ω | τ ω ∈ s} ∩ stopEvent PF.X τ x ∩
        ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ tv v} ∩
          stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) :=
    fun v v' hvv' => ((disjoint_stopEvent hvv').mono
      (inter_subset_right.trans inter_subset_right)
      (inter_subset_right.trans inter_subset_right)).aedisjoint
  have hsplit : exitTriple PF.X x τ ⁻¹' (s ×ˢ t) ∩ stopEvent PF.X τ x =ᵐ[PF.P z]
      ⋃ v : V, ({ω | τ ω ∈ s} ∩ stopEvent PF.X τ x ∩
        ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ tv v} ∩
          stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hae] with ω hω
    constructor
    · rintro ⟨hΦω, hEω⟩
      obtain ⟨hρfin, v, hv⟩ := hω hEω
      rw [mem_preimage, exitTriple, mem_prod] at hΦω
      refine mem_iUnion.2 ⟨v, ⟨⟨hΦω.1, hEω⟩, ?_, hρfin, hv⟩⟩
      show (hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω, some v) ∈ t
      rw [← hv]
      exact hΦω.2
    · intro hmem
      obtain ⟨v, ⟨⟨hτs, hEω⟩, hl, -, hv⟩⟩ := mem_iUnion.1 hmem
      refine ⟨?_, hEω⟩
      rw [mem_preimage, exitTriple, mem_prod]
      refine ⟨hτs, ?_⟩
      show (hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω,
        stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω) ∈ t
      rw [hv]
      exact hl
  rw [measure_congr hsplit, measure_iUnion₀ hdisj hnull]
  simp_rw [measure_exit_rect h hG z x hτm hτ hs (htv _)]
  rw [ENNReal.tsum_mul_left]
  congr 1
  -- the product measure of the section
  rw [Measure.prod_apply ht]
  have hκ : ∀ l, exitKernel G x (Prod.mk l ⁻¹' t) =
      ∑' v : V, (tv v).indicator (fun _ => ENNReal.ofReal (G.c x v / G.pi x)) l := by
    intro l
    rw [exitKernel_apply]
    refine tsum_congr fun v => ?_
    by_cases hl : l ∈ tv v
    · have hl' : some v ∈ Prod.mk l ⁻¹' t := hl
      rw [indicator_of_mem hl', indicator_of_mem hl, Pi.one_apply, mul_one]
    · have hl' : some v ∉ Prod.mk l ⁻¹' t := hl
      rw [indicator_of_notMem hl', indicator_of_notMem hl, mul_zero]
  simp_rw [hκ]
  rw [lintegral_tsum fun v => (measurable_const.indicator (htv v)).aemeasurable]
  refine tsum_congr fun v => ?_
  rw [lintegral_indicator_const (htv v), mul_comm]

/-- **Tonelli for the exit triple.**  A nonnegative functional of `(τ, ρ − τ, X_ρ)` integrates
over `{τ < ∞, X_τ = x}` by first averaging the holding length against `Exp(w x)` and the exit
vertex against `c(x,·)/π(x)`, with the start time `τ` frozen. -/
theorem lintegral_exitTriple (g : WithTop ℝ≥0 × (WithTop ℝ≥0 × Option V) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ ω in stopEvent PF.X τ x, g (exitTriple PF.X x τ ω) ∂PF.P z) =
      ∫⁻ ω in stopEvent PF.X τ x, ∫⁻ l, ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) *
        g (τ ω, (l, some v)) ∂(expMeasure (w x)).map toWithTop ∂PF.P z := by
  haveI : IsProbabilityMeasure ((expMeasure (w x)).map toWithTop) :=
    ⟨map_toWithTop_expMeasure_univ h x⟩
  haveI : IsFiniteMeasure (exitKernel G x) := isFiniteMeasure_exitKernel G hG x
  have hΦ : AEMeasurable (exitTriple PF.X x τ) ((PF.P z).restrict (stopEvent PF.X τ x)) :=
    (aemeasurable_exitTriple h z x hτm).restrict
  have hτμ : AEMeasurable τ ((PF.P z).restrict (stopEvent PF.X τ x)) := hτm.restrict
  let F : WithTop ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ l, ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) *
    g (s, (l, some v)) ∂(expMeasure (w x)).map toWithTop
  have hinner : Measurable (fun p : WithTop ℝ≥0 × WithTop ℝ≥0 =>
      ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) * g (p.1, (p.2, some v))) :=
    Measurable.ennreal_tsum fun v => measurable_const.mul
      (hg.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
  have hF : Measurable F := hinner.lintegral_prod_right'
  calc (∫⁻ ω in stopEvent PF.X τ x, g (exitTriple PF.X x τ ω) ∂PF.P z) =
        ∫⁻ p, g p ∂((PF.P z).restrict (stopEvent PF.X τ x)).map (exitTriple PF.X x τ) :=
        (lintegral_map' hg.aemeasurable hΦ).symm
    _ = ∫⁻ p, g p ∂(((PF.P z).restrict (stopEvent PF.X τ x)).map τ).prod
          (((expMeasure (w x)).map toWithTop).prod (exitKernel G x)) := by
        rw [map_exitTriple_eq h hG z x hτm hτ]
    _ = ∫⁻ s, ∫⁻ q, g (s, q) ∂((expMeasure (w x)).map toWithTop).prod (exitKernel G x)
          ∂((PF.P z).restrict (stopEvent PF.X τ x)).map τ :=
        lintegral_prod _ hg.aemeasurable
    _ = ∫⁻ s, F s ∂((PF.P z).restrict (stopEvent PF.X τ x)).map τ := by
        refine lintegral_congr fun s => ?_
        have hgs : Measurable (fun q : WithTop ℝ≥0 × Option V => g (s, q)) :=
          hg.comp (measurable_const.prodMk measurable_id)
        refine (lintegral_prod (fun q => g (s, q)) hgs.aemeasurable).trans ?_
        refine lintegral_congr fun l => ?_
        exact lintegral_exitKernel G x _
    _ = ∫⁻ ω in stopEvent PF.X τ x, F (τ ω) ∂PF.P z := lintegral_map' hF.aemeasurable hτμ

end Process

end ReflectedGMS.SojournExitLaw
