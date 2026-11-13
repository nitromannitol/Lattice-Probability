/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Coupling at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Connect
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2FlipVertex

 








set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hB x)

theorem abs_integral_le_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun x => (by rw [Real.norm_eq_abs]; exact hB x : ‖f x‖ ≤ B))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

namespace WiredConductances

variable {W : Type*} [Fintype W] [DecidableEq W] (G : WiredConductances W)

 
def aMap (x φ : EuclideanSpace ℝ W) : EuclideanSpace ℝ W :=
  WithLp.toLp 2 fun v => Real.sqrt (2 * x v + φ v ^ 2)

theorem continuous_aMap : Continuous fun q : EuclideanSpace ℝ W × EuclideanSpace ℝ W =>
    aMap q.1 q.2 := by
  unfold aMap
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun v => ?_)
  exact Real.continuous_sqrt.comp ((continuous_const.mul
    ((PiLp.continuous_apply 2 _ v).comp continuous_fst)).add
      (((PiLp.continuous_apply 2 _ v).comp continuous_snd).pow 2))

theorem aMap_nonneg (x φ : EuclideanSpace ℝ W) (v : W) : 0 ≤ aMap x φ v := by
  unfold aMap; simp only [WithLp.ofLp_toLp]; exact Real.sqrt_nonneg _

theorem aMap_sq_ge (x φ : EuclideanSpace ℝ W) (v : W) :
    2 * x v + φ v ^ 2 ≤ (aMap x φ v) ^ 2 := by
  unfold aMap
  simp only [WithLp.ofLp_toLp]
  rcases le_or_gt 0 (2 * x v + φ v ^ 2) with h | h
  · rw [Real.sq_sqrt h]
  · nlinarith [sq_nonneg (Real.sqrt (2 * x v + φ v ^ 2))]

 
theorem integral_shiftLaw_absE (hK : G.precision.PosDef) {u : ℝ} (Φ : EuclideanSpace ℝ W → ℝ)
    (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ a, |Φ a| ≤ B) :
    ∫ z, Φ (absE z) ∂(G.shiftLaw u) =
      ∑' s, G.soupMassAt (u ^ 2 / 2) s *
        ∫ L, ∫ φ, Φ (aMap (WithLp.toLp 2 L) φ) ∂G.gff ∂(G.holdingLaw s) := by
  have ht : (0 : ℝ) ≤ u ^ 2 / 2 := by positivity
  have hPL := G.isProbabilityMeasure_localTimeLaw hK ht
  have hPLE := G.isProbabilityMeasure_localTimeLawE hK ht
  have hPH := G.isProbabilityMeasure_holdingLaw hK
  
  have h1 : ∫ z, Φ (absE z) ∂(G.shiftLaw u) = ∫ a, Φ a ∂((G.shiftLaw u).map absE) := by
    rw [integral_map continuous_absE.measurable.aemeasurable hΦ.aestronglyMeasurable]
  
  have h2 : (G.shiftLaw u).map absE = G.gff.map (fun φ => WithLp.toLp 2 fun v => |φ v + u|) := by
    unfold shiftLaw
    rw [Measure.map_map continuous_absE.measurable (by fun_prop)]
    congr 1
  
  have h3 := G.rayKnight_abs hK u
  rw [h1, h2, ← h3, integral_map (continuous_aMap.measurable.aemeasurable.congr
    (Filter.Eventually.of_forall fun q => by rfl)) hΦ.aestronglyMeasurable]
  
  have hmeas : Measurable fun q : EuclideanSpace ℝ W × EuclideanSpace ℝ W =>
      Φ (WithLp.toLp 2 fun v => Real.sqrt (2 * q.1 v + q.2 v ^ 2)) :=
    hΦ.comp continuous_aMap.measurable
  rw [integral_prod _ (integrable_of_abs_le hmeas (fun q => hB _))]
  
  have hinner : Measurable fun x : EuclideanSpace ℝ W => ∫ φ, Φ (aMap x φ) ∂G.gff :=
    (StronglyMeasurable.integral_prod_right' (f := fun q : EuclideanSpace ℝ W ×
      EuclideanSpace ℝ W => Φ (aMap q.1 q.2)) hmeas.stronglyMeasurable).measurable
  have hbinner : ∀ x : EuclideanSpace ℝ W, |∫ φ, Φ (aMap x φ) ∂G.gff| ≤ B :=
    fun x => abs_integral_le_of_abs_le (fun φ => hB _)
  change ∫ x, (∫ φ, Φ (aMap x φ) ∂G.gff) ∂(G.localTimeLawE (u ^ 2 / 2)) = _
  rw [localTimeLawE, integral_map (by fun_prop) hinner.aestronglyMeasurable]
  rw [G.integral_localTimeLaw hK ht (fun L => ∫ φ, Φ (aMap (WithLp.toLp 2 L) φ) ∂G.gff)
    (integrable_of_abs_le (hinner.comp (by fun_prop)) (fun L => hbinner _))]
  rfl

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E] (Γ : EdgeGraph W E)

theorem measurableSet_circEvent (Pc : Set (Finset W)) : MeasurableSet (circEvent Pc) := by
  have : circEvent Pc = ⋃ c ∈ Pc, ⋂ x ∈ c, {z : EuclideanSpace ℝ W | 0 ≤ z x} := by
    ext z; simp [circEvent]
  rw [this]
  refine MeasurableSet.biUnion (Set.to_countable Pc) fun c _ => ?_
  refine MeasurableSet.biInter (c.countable_toSet) fun x _ => ?_
  exact measurableSet_le measurable_const (PiLp.continuous_apply 2 _ x).measurable

open Classical in
 
def disSum (u : ℝ) (s : Soup (Excursion W)) (a : EuclideanSpace ℝ W) : ℝ :=
  ∑ e, (if VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) then Γ.disBound u a e else 0)

open Classical in
theorem disSum_nonneg (u : ℝ) (s : Soup (Excursion W)) (a : EuclideanSpace ℝ W) :
    0 ≤ Γ.disSum u s a :=
  Finset.sum_nonneg fun e _ => by split_ifs; exact Γ.disBound_nonneg u a e; exact le_rfl

open Classical in
theorem disSum_le_card (u : ℝ) (hu : 0 ≤ u) (s : Soup (Excursion W)) (a : EuclideanSpace ℝ W)
    (ha : ∀ x, 0 ≤ a x) : Γ.disSum u s a ≤ Fintype.card E := by
  unfold disSum
  calc ∑ e, (if VisOrB s (Γ.tail e) ∧ VisOrB s (Γ.head e) then Γ.disBound u a e else 0)
      ≤ ∑ _e : E, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        split_ifs
        · unfold disBound
          rw [Real.exp_le_one_iff]
          have h1 : 0 ≤ ahat u a (Γ.tail e) := by
            cases Γ.tail e with
            | none => exact hu
            | some x => exact ha x
          have h2 : 0 ≤ ahat u a (Γ.head e) := by
            cases Γ.head e with
            | none => exact hu
            | some x => exact ha x
          have := Γ.cond_pos e
          have : 0 ≤ Γ.cond e * ahat u a (Γ.tail e) * ahat u a (Γ.head e) := by positivity
          linarith
        · exact zero_le_one
    _ = Fintype.card E := by simp

open Classical in
theorem continuous_disSum (u : ℝ) (s : Soup (Excursion W)) : Continuous (Γ.disSum u s) := by
  unfold disSum
  refine continuous_finsetSum _ fun e _ => ?_
  split_ifs
  · unfold disBound
    refine Real.continuous_exp.comp ?_
    have hc : ∀ o : Option W, Continuous fun a : EuclideanSpace ℝ W => ahat u a o := by
      intro o
      cases o with
      | none => exact continuous_const
      | some x => exact PiLp.continuous_apply 2 _ x
    exact (continuous_const.mul (hc _)).mul (hc _)
  · exact continuous_const

 
def circSignAverage (C u : ℝ) (Pc : Set (Finset W)) (a : EuclideanSpace ℝ W) : ℝ :=
  ∑ σ : W → Bool, signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ *
    (circEvent Pc).indicator 1 (signApply σ a)

theorem measurable_circSignAverage (C u : ℝ) (Pc : Set (Finset W)) :
    Measurable (Γ.circSignAverage C u Pc) := by
  unfold circSignAverage signKernel
  refine Finset.measurable_sum _ fun σ _ => ?_
  have hρ : Continuous fun z : EuclideanSpace ℝ W => C * Γ.toWired.shiftDensity u z :=
    continuous_const.mul (Γ.toWired.continuous_shiftDensity u)
  refine Measurable.mul ?_ ?_
  · refine Measurable.div ?_ ?_
    · exact (hρ.comp (continuous_signApply σ)).measurable
    · exact Finset.measurable_sum _ fun σ' _ => (hρ.comp (continuous_signApply σ')).measurable
  · exact (measurable_one.indicator (measurableSet_circEvent Pc)).comp
      (continuous_signApply σ).measurable

theorem circSignAverage_bounds {C : ℝ} (hC : 0 < C) (u : ℝ) (Pc : Set (Finset W))
    (a : EuclideanSpace ℝ W) : |Γ.circSignAverage C u Pc a| ≤ 1 := by
  have hρ : ∀ z, 0 < C * Γ.toWired.shiftDensity u z :=
    fun z => mul_pos hC (Γ.toWired.shiftDensity_pos u z)
  unfold circSignAverage
  have h0 : 0 ≤ ∑ σ : W → Bool, signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ *
      (circEvent Pc).indicator 1 (signApply σ a) :=
    Finset.sum_nonneg fun σ _ => mul_nonneg (signKernel_nonneg hρ a σ)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  rw [abs_of_nonneg h0]
  calc ∑ σ : W → Bool, signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ *
        (circEvent Pc).indicator 1 (signApply σ a)
      ≤ ∑ σ : W → Bool, signKernel (fun z => C * Γ.toWired.shiftDensity u z) a σ * 1 := by
        apply Finset.sum_le_sum
        intro σ _
        refine mul_le_mul_of_nonneg_left ?_ (signKernel_nonneg hρ a σ)
        exact Set.indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans (by simp)
    _ = 1 := by simp only [mul_one]; exact sum_signKernel hρ a

theorem soupMassAt_pos_excursion (t : ℝ) (s : Soup (Excursion W))
    (hs : 0 < Γ.toWired.soupMassAt t s) : ∀ i, 0 < Γ.toWired.excursionWeight (s.2 i) := by
  intro i
  unfold WiredConductances.soupMassAt soupMass at hs
  by_contra hle
  push_neg at hle
  have h0 : Γ.toWired.excursionWeight (s.2 i) = 0 :=
    le_antisymm hle (Γ.toWired.excursionWeight_nonneg _)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0, mul_zero]), mul_zero] at hs
  exact lt_irrefl 0 hs

theorem measurable_toLp_prod : Measurable fun q : (W → ℝ) × EuclideanSpace ℝ W =>
    ((WithLp.toLp 2 q.1 : EuclideanSpace ℝ W), q.2) :=
  ((PiLp.continuous_toLp 2 _).measurable.comp measurable_fst).prodMk measurable_snd

 
theorem shiftLaw_circEvent_eq (hK : Γ.toWired.precision.PosDef) {C u : ℝ} (hC : 0 < C)
    (hlaw : Γ.toWired.shiftLaw u =
      volume.withDensity fun z => ENNReal.ofReal (C * Γ.toWired.shiftDensity u z))
    (Pc : Set (Finset W)) :
    (Γ.toWired.shiftLaw u).real (circEvent Pc) =
      ∑' s, Γ.toWired.soupMassAt (u ^ 2 / 2) s *
        ∫ L, ∫ φ, Γ.circSignAverage C u Pc (WiredConductances.aMap (WithLp.toLp 2 L) φ)
          ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) := by
  have hP := Γ.toWired.isProbabilityMeasure_shiftLaw hK u
  set ρ : EuclideanSpace ℝ W → ℝ := fun z => C * Γ.toWired.shiftDensity u z with hρdef
  have hρc : Continuous ρ := continuous_const.mul (Γ.toWired.continuous_shiftDensity u)
  have hρpos : ∀ z, 0 < ρ z := fun z => mul_pos hC (Γ.toWired.shiftDensity_pos u z)
  have hρint : Integrable ρ := by
    refine ⟨hρc.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have : ∫⁻ z, ‖ρ z‖ₑ = (volume.withDensity fun z => ENNReal.ofReal (ρ z)) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      congr 1
      funext z
      rw [Real.enorm_eq_ofReal (hρpos z).le]
    rw [this, ← hlaw, measure_univ]
    exact ENNReal.one_lt_top
  have h12 : (Γ.toWired.shiftLaw u).real (circEvent Pc) =
      ∫ z, Γ.circSignAverage C u Pc (absE z) ∂(Γ.toWired.shiftLaw u) := by
    rw [← integral_indicator_one (measurableSet_circEvent Pc), hlaw]
    have := integral_sign_decomp hρc hρpos hρint
      ((measurable_one.indicator (measurableSet_circEvent Pc))) (C := 1) (fun z => by
        by_cases hz : z ∈ circEvent Pc <;> simp [Set.indicator, hz])
    exact this
  rw [h12, Γ.toWired.integral_shiftLaw_absE hK (Γ.circSignAverage C u Pc)
    (Γ.measurable_circSignAverage C u Pc) (Γ.circSignAverage_bounds hC u Pc)]

open Classical in
 
theorem soup_term_lower (hK : Γ.toWired.precision.PosDef) {C u : ℝ} (hC : 0 < C) (hu : 0 ≤ u)
    (Pc : Set (Finset W)) (s : Soup (Excursion W)) :
    Γ.toWired.soupMassAt (u ^ 2 / 2) s * ((if SoupCirc Pc s then 1 else 0) -
        ∫ L, ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)
          ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s)) ≤
      Γ.toWired.soupMassAt (u ^ 2 / 2) s *
        ∫ L, ∫ φ, Γ.circSignAverage C u Pc (WiredConductances.aMap (WithLp.toLp 2 L) φ)
          ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) := by
  have ht : (0 : ℝ) ≤ u ^ 2 / 2 := by positivity
  rcases (Γ.toWired.soupMassAt_nonneg ht s).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  have hPH := Γ.toWired.isProbabilityMeasure_holdingLaw hK s
  have hgffP : IsProbabilityMeasure Γ.toWired.gff := by
    unfold WiredConductances.gff; infer_instance
  have hexc := Γ.soupMassAt_pos_excursion (u ^ 2 / 2) s hpos
  have hmeasA : Measurable fun q : (W → ℝ) × EuclideanSpace ℝ W =>
      Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 q.1) q.2) :=
    (Γ.continuous_disSum u s).measurable.comp
      (WiredConductances.continuous_aMap.measurable.comp measurable_toLp_prod)
  have hmeasΨ : Measurable fun q : (W → ℝ) × EuclideanSpace ℝ W =>
      Γ.circSignAverage C u Pc (WiredConductances.aMap (WithLp.toLp 2 q.1) q.2) :=
    (Γ.measurable_circSignAverage C u Pc).comp
      (WiredConductances.continuous_aMap.measurable.comp measurable_toLp_prod)
  have hDbd : ∀ L φ, |Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)| ≤
      Fintype.card E := fun L φ => by
    rw [abs_of_nonneg (Γ.disSum_nonneg u s _)]
    exact Γ.disSum_le_card u hu s _ (WiredConductances.aMap_nonneg _ _)
  have hpt : ∀ L φ, (if SoupCirc Pc s then (1 : ℝ) else 0) -
      Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ) ≤
      Γ.circSignAverage C u Pc (WiredConductances.aMap (WithLp.toLp 2 L) φ) := fun L φ =>
    Γ.signAverage_lower C hC hu Pc s hexc _ (WiredConductances.aMap_nonneg _ _)
  have hcaL : ∀ L : W → ℝ, Continuous fun φ : EuclideanSpace ℝ W =>
      WiredConductances.aMap (WithLp.toLp 2 L) φ := fun L =>
    WiredConductances.continuous_aMap.comp
      ((continuous_const : Continuous fun _ : EuclideanSpace ℝ W =>
        (WithLp.toLp 2 L : EuclideanSpace ℝ W)).prodMk continuous_id)
  have hintD : ∀ L, Integrable (fun φ => Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ))
      Γ.toWired.gff := fun L =>
    integrable_of_abs_le ((Γ.continuous_disSum u s).comp (hcaL L)).measurable (hDbd L)
  have hintΨ : ∀ L, Integrable (fun φ => Γ.circSignAverage C u Pc
      (WiredConductances.aMap (WithLp.toLp 2 L) φ)) Γ.toWired.gff := fun L =>
    integrable_of_abs_le ((Γ.measurable_circSignAverage C u Pc).comp (hcaL L).measurable)
      (fun φ => Γ.circSignAverage_bounds hC u Pc _)
  have hmeasInD : Measurable fun L : W → ℝ => ∫ φ, Γ.disSum u s
      (WiredConductances.aMap (WithLp.toLp 2 L) φ) ∂Γ.toWired.gff :=
    (StronglyMeasurable.integral_prod_right' (f := fun q : (W → ℝ) × EuclideanSpace ℝ W =>
      Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 q.1) q.2))
      hmeasA.stronglyMeasurable).measurable
  have hmeasInΨ : Measurable fun L : W → ℝ => ∫ φ, Γ.circSignAverage C u Pc
      (WiredConductances.aMap (WithLp.toLp 2 L) φ) ∂Γ.toWired.gff :=
    (StronglyMeasurable.integral_prod_right' (f := fun q : (W → ℝ) × EuclideanSpace ℝ W =>
      Γ.circSignAverage C u Pc (WiredConductances.aMap (WithLp.toLp 2 q.1) q.2))
      hmeasΨ.stronglyMeasurable).measurable
  have hinner : ∀ L, (if SoupCirc Pc s then (1 : ℝ) else 0) -
      ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ) ∂Γ.toWired.gff ≤
      ∫ φ, Γ.circSignAverage C u Pc (WiredConductances.aMap (WithLp.toLp 2 L) φ)
        ∂Γ.toWired.gff := by
    intro L
    have h := integral_mono ((integrable_const (if SoupCirc Pc s then (1 : ℝ) else 0)).sub
      (hintD L)) (hintΨ L) (fun φ => hpt L φ)
    simp only [Pi.sub_apply] at h
    rwa [integral_sub (integrable_const _) (hintD L), integral_const, probReal_univ,
      one_smul] at h
  have hintInD : Integrable (fun L : W → ℝ => ∫ φ, Γ.disSum u s
      (WiredConductances.aMap (WithLp.toLp 2 L) φ) ∂Γ.toWired.gff) (Γ.toWired.holdingLaw s) :=
    integrable_of_abs_le hmeasInD (fun L => abs_integral_le_of_abs_le (hDbd L))
  have hintInΨ : Integrable (fun L : W → ℝ => ∫ φ, Γ.circSignAverage C u Pc
      (WiredConductances.aMap (WithLp.toLp 2 L) φ) ∂Γ.toWired.gff) (Γ.toWired.holdingLaw s) :=
    integrable_of_abs_le hmeasInΨ (fun L => abs_integral_le_of_abs_le
      (fun φ => Γ.circSignAverage_bounds hC u Pc _))
  have houter := integral_mono ((integrable_const (if SoupCirc Pc s then (1 : ℝ) else 0)).sub
    hintInD) hintInΨ (fun L => hinner L)
  simp only [Pi.sub_apply] at houter
  rwa [integral_sub (integrable_const _) hintInD, integral_const, probReal_univ,
    one_smul] at houter

open Classical in
 

theorem shiftLaw_circEvent_lower (hK : Γ.toWired.precision.PosDef) {u : ℝ} (hu : 0 ≤ u)
    (Pc : Set (Finset W)) :
    (∑' s, Γ.toWired.soupMassAt (u ^ 2 / 2) s * (if SoupCirc Pc s then 1 else 0)) -
        ∑' s, Γ.toWired.soupMassAt (u ^ 2 / 2) s *
          ∫ L, ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)
            ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) ≤
      (Γ.toWired.shiftLaw u).real (circEvent Pc) := by
  have ht : (0 : ℝ) ≤ u ^ 2 / 2 := by positivity
  obtain ⟨C, hC, hlaw⟩ := Γ.toWired.shiftLaw_eq_withDensity hK u
  rw [Γ.shiftLaw_circEvent_eq hK hC hlaw Pc]
  have hmass := Γ.toWired.hasSum_soupMassAt hK ht
  have hPH := Γ.toWired.isProbabilityMeasure_holdingLaw hK
  have hgffP : IsProbabilityMeasure Γ.toWired.gff := by
    unfold WiredConductances.gff; infer_instance
  have hsumm : ∀ X : Soup (Excursion W) → ℝ, (∀ s, |X s| ≤ Fintype.card E + 1) →
      Summable fun s => Γ.toWired.soupMassAt (u ^ 2 / 2) s * X s := by
    intro X hX
    refine Summable.of_norm_bounded
      (g := fun s => Γ.toWired.soupMassAt (u ^ 2 / 2) s * (Fintype.card E + 1))
      (hmass.summable.mul_right _) fun s => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Γ.toWired.soupMassAt_nonneg ht s),
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hX s) (Γ.toWired.soupMassAt_nonneg ht s)
  have hcard : (0 : ℝ) ≤ Fintype.card E := Nat.cast_nonneg _
  have hInD : ∀ s, |∫ L, ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)
      ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s)| ≤ Fintype.card E + 1 := fun s =>
    le_trans (abs_integral_le_of_abs_le fun L => abs_integral_le_of_abs_le fun φ => by
      rw [abs_of_nonneg (Γ.disSum_nonneg u s _)]
      exact Γ.disSum_le_card u hu s _ (WiredConductances.aMap_nonneg _ _)) (by linarith)
  have hInΨ : ∀ s, |∫ L, ∫ φ, Γ.circSignAverage C u Pc (WiredConductances.aMap (WithLp.toLp 2 L) φ)
      ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s)| ≤ Fintype.card E + 1 := fun s =>
    le_trans (abs_integral_le_of_abs_le fun L => abs_integral_le_of_abs_le fun φ =>
      Γ.circSignAverage_bounds hC u Pc _) (by linarith)
  have hInC : ∀ s : Soup (Excursion W), |(if SoupCirc Pc s then (1 : ℝ) else 0)| ≤
      Fintype.card E + 1 := fun s => by
    split_ifs <;> simp <;> linarith
  rw [← (hsumm _ hInC).tsum_sub (hsumm _ hInD)]
  refine Summable.tsum_le_tsum (fun s => ?_) ((hsumm _ hInC).sub (hsumm _ hInD)) (hsumm _ hInΨ)
  rw [← mul_sub]
  exact Γ.soup_term_lower hK hC hu Pc s

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
