/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2FlipSum at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Coupling

 









set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos

theorem exp_neg_mul_le_add {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.exp (-2 * c * x * y) ≤ Real.exp (-2 * c * x ^ 2) + Real.exp (-2 * c * y ^ 2) := by
  rcases le_total x y with h | h
  · have : Real.exp (-2 * c * x * y) ≤ Real.exp (-2 * c * x ^ 2) := by
      rw [Real.exp_le_exp]; nlinarith [mul_le_mul_of_nonneg_left h hx]
    linarith [Real.exp_pos (-2 * c * y ^ 2)]
  · have : Real.exp (-2 * c * x * y) ≤ Real.exp (-2 * c * y ^ 2) := by
      rw [Real.exp_le_exp]; nlinarith [mul_le_mul_of_nonneg_left h hy]
    linarith [Real.exp_pos (-2 * c * x ^ 2)]

 
theorem ae_nonneg_expConvPow {r : ℝ} (hr : 0 < r) :
    ∀ k : ℕ, ∀ᵐ x ∂(expConvPow r k), 0 ≤ x
  | 0 => by
    have hS : MeasurableSet {x : ℝ | 0 ≤ x} := measurableSet_Ici
    simp only [expConvPow]
    rw [ae_dirac_iff hS]
  | k + 1 => by
    have hk := ae_nonneg_expConvPow hr k
    have := isProbabilityMeasure_expConvPow hr k
    have := isProbabilityMeasure_expMeasure hr
    have hS : MeasurableSet {x : ℝ | 0 ≤ x} := measurableSet_Ici
    simp only [expConvPow]
    rw [Measure.conv, ae_map_iff (by fun_prop) hS]
    rw [ae_iff] at hk ⊢
    have hexp := ae_nonneg_expMeasure (r := r)
    rw [ae_iff] at hexp
    have h1 : ((expConvPow r k).prod (expMeasure r)) ({x : ℝ | ¬ 0 ≤ x} ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hk, zero_mul]
    have h2 : ((expConvPow r k).prod (expMeasure r)) (Set.univ ×ˢ {x : ℝ | ¬ 0 ≤ x}) = 0 := by
      rw [Measure.prod_prod, hexp, mul_zero]
    refine measure_mono_null ?_ (measure_union_null h1 h2)
    intro q hq
    simp only [Set.mem_setOf_eq, not_le] at hq
    simp only [Set.mem_union, Set.mem_prod, Set.mem_setOf_eq, not_le, Set.mem_univ, and_true,
      true_and]
    by_contra hcon
    push_neg at hcon
    linarith [hcon.1, hcon.2]

namespace EdgeGraph

variable {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E] (Γ : EdgeGraph W E)
def vertexTerm (κ u : ℝ) (s : Soup (Excursion W)) (L : W → ℝ) (φ : EuclideanSpace ℝ W) :
    Option W → ℝ
  | none => Real.exp (-2 * κ * u ^ 2)
  | some p => if soupVisitCount s p = 0 then 0 else Real.exp (-2 * κ * (2 * L p + (φ p) ^ 2))

 
def vertexAvg (κ u t : ℝ) : Option W → ℝ
  | none => Real.exp (-2 * κ * u ^ 2)
  | some p => WiredConductances.flipBound (4 * κ * t) (4 * κ * Γ.toWired.green p p)

theorem vertexTerm_nonneg (κ u : ℝ) (s : Soup (Excursion W)) (L : W → ℝ)
    (φ : EuclideanSpace ℝ W) (o : Option W) : 0 ≤ vertexTerm κ u s L φ o := by
  cases o with
  | none => exact (Real.exp_pos _).le
  | some p =>
    simp only [vertexTerm]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le

theorem vertexTerm_le_one {κ u : ℝ} (hκ : 0 ≤ κ) (s : Soup (Excursion W)) (L : W → ℝ)
    (hL : ∀ p, 0 ≤ L p) (φ : EuclideanSpace ℝ W) (o : Option W) : vertexTerm κ u s L φ o ≤ 1 := by
  cases o with
  | none =>
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  | some p =>
    simp only [vertexTerm]
    split_ifs
    · exact zero_le_one
    · exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (φ p), hL p])

open Classical in
theorem disSum_le_vertexTerms {u : ℝ} (hu : 0 ≤ u) (s : Soup (Excursion W)) (L : W → ℝ)
    (φ : EuclideanSpace ℝ W) :
    Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ) ≤
      ∑ e, (vertexTerm (Γ.cond e) u s L φ (Γ.tail e) +
        vertexTerm (Γ.cond e) u s L φ (Γ.head e)) := by
  unfold disSum
  apply Finset.sum_le_sum
  intro e _
  have hc := (Γ.cond_pos e).le
  set a := WiredConductances.aMap (WithLp.toLp 2 L) φ
  have hah : ∀ o : Option W, 0 ≤ ahat u a o := fun o => by
    cases o with
    | none => exact hu
    | some x => exact WiredConductances.aMap_nonneg _ _ x
  have hvt : ∀ o : Option W, VisOrB s o → Real.exp (-2 * Γ.cond e * (ahat u a o) ^ 2) ≤
      vertexTerm (Γ.cond e) u s L φ o := by
    intro o ho
    cases o with
    | none => exact le_rfl
    | some p =>
      have hp : soupVisitCount s p ≠ 0 := ho
      show Real.exp _ ≤ (if soupVisitCount s p = 0 then 0 else
        Real.exp (-2 * Γ.cond e * (2 * L p + (φ p) ^ 2)))
      rw [if_neg hp, Real.exp_le_exp]
      have := WiredConductances.aMap_sq_ge (WithLp.toLp 2 L) φ p
      have hca : (ahat u a (some p)) = a p := rfl
      rw [hca]
      have : 2 * L p + (φ p) ^ 2 ≤ (a p) ^ 2 := this
      nlinarith
  split_ifs with hv
  · unfold disBound
    calc Real.exp (-2 * Γ.cond e * ahat u a (Γ.tail e) * ahat u a (Γ.head e))
        ≤ Real.exp (-2 * Γ.cond e * (ahat u a (Γ.tail e)) ^ 2) +
          Real.exp (-2 * Γ.cond e * (ahat u a (Γ.head e)) ^ 2) :=
          exp_neg_mul_le_add hc (hah _) (hah _)
      _ ≤ _ := add_le_add (hvt _ hv.1) (hvt _ hv.2)
  · exact add_nonneg (vertexTerm_nonneg _ _ _ _ _ _) (vertexTerm_nonneg _ _ _ _ _ _)

 
theorem hasSum_vertexTerm (hK : Γ.toWired.precision.PosDef) {u : ℝ} (κ : ℝ) (hκ : 0 < κ)
    (o : Option W) :
    HasSum (fun s => Γ.toWired.soupMassAt (u ^ 2 / 2) s *
        ∫ L, ∫ φ, vertexTerm κ u s L φ o ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s))
      (vertexAvg Γ κ u (u ^ 2 / 2) o) := by
  have ht : (0 : ℝ) ≤ u ^ 2 / 2 := by positivity
  have hPH := Γ.toWired.isProbabilityMeasure_holdingLaw hK
  have hgffP : IsProbabilityMeasure Γ.toWired.gff := by
    unfold WiredConductances.gff; infer_instance
  cases o with
  | none =>
    have hc : ∀ s : Soup (Excursion W), ∫ L, ∫ φ, vertexTerm κ u s L φ none ∂Γ.toWired.gff
        ∂(Γ.toWired.holdingLaw s) = Real.exp (-2 * κ * u ^ 2) := by
      intro s
      show ∫ L, ∫ φ, Real.exp (-2 * κ * u ^ 2) ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) = _
      rw [integral_const, integral_const, probReal_univ, probReal_univ, one_smul, one_smul]
    simp_rw [hc]
    have := (Γ.toWired.hasSum_soupMassAt hK ht).mul_right (Real.exp (-2 * κ * u ^ 2))
    rw [one_mul] at this
    exact this
  | some p =>
    simp only [vertexTerm, vertexAvg]
    exact Γ.toWired.hasSum_flip_vertex hK ht p hκ

 
theorem tsum_disSum_le (hK : Γ.toWired.precision.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    ∑' s, Γ.toWired.soupMassAt (u ^ 2 / 2) s *
        ∫ L, ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)
          ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) ≤
      ∑ e, (vertexAvg Γ (Γ.cond e) u (u ^ 2 / 2) (Γ.tail e) +
        vertexAvg Γ (Γ.cond e) u (u ^ 2 / 2) (Γ.head e)) := by
  have ht : (0 : ℝ) ≤ u ^ 2 / 2 := by positivity
  have hPH := Γ.toWired.isProbabilityMeasure_holdingLaw hK
  have hgffP : IsProbabilityMeasure Γ.toWired.gff := by
    unfold WiredConductances.gff; infer_instance
  have hmass := Γ.toWired.hasSum_soupMassAt hK ht
  
  have hLnn : ∀ s, ∀ᵐ L ∂(Γ.toWired.holdingLaw s), ∀ p, 0 ≤ L p := by
    intro s
    unfold WiredConductances.holdingLaw
    rw [ae_all_iff]
    intro p
    have hp := fun v => isProbabilityMeasure_expConvPow (Γ.toWired.totalRate_pos hK v)
      (soupVisitCount s v)
    have h := ae_nonneg_expConvPow (Γ.toWired.totalRate_pos hK p) (soupVisitCount s p)
    rw [ae_iff] at h ⊢
    exact Measure.pi_eval_preimage_null
      (fun v => expConvPow (Γ.toWired.totalRate v) (soupVisitCount s v)) (i := p)
      (s := {x : ℝ | ¬ 0 ≤ x}) h
  have hcvt : ∀ (κ : ℝ) (s : Soup (Excursion W)) (o : Option W),
      Continuous fun q : (W → ℝ) × EuclideanSpace ℝ W => vertexTerm κ u s q.1 q.2 o := by
    intro κ s o
    cases o with
    | none => exact continuous_const
    | some p =>
      simp only [vertexTerm]
      split_ifs
      · exact continuous_const
      · exact Real.continuous_exp.comp (continuous_const.mul ((continuous_const.mul
          ((continuous_apply p).comp continuous_fst)).add
            (((PiLp.continuous_apply 2 _ p).comp continuous_snd).pow 2)))
  have hcD : ∀ s : Soup (Excursion W), Continuous fun q : (W → ℝ) × EuclideanSpace ℝ W =>
      Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 q.1) q.2) := fun s =>
    (Γ.continuous_disSum u s).comp (WiredConductances.continuous_aMap.comp
      (((PiLp.continuous_toLp 2 _).comp continuous_fst).prodMk continuous_snd))
  
  have hper : ∀ s, ∫ L, ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)
      ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) ≤
      ∑ e, (∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s) +
        ∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s)) := by
    intro s
    have hint1 : ∀ (κ : ℝ) (o : Option W) (L : W → ℝ), (∀ p, 0 ≤ L p) → 0 ≤ κ →
        Integrable (fun φ => vertexTerm κ u s L φ o) Γ.toWired.gff := by
      intro κ o L hL hκ
      refine integrable_of_abs_le ((hcvt κ s o).comp
        ((continuous_const : Continuous fun _ : EuclideanSpace ℝ W => L).prodMk
          continuous_id)).measurable (B := 1) fun φ => ?_
      rw [abs_of_nonneg (vertexTerm_nonneg _ _ _ _ _ _)]
      exact vertexTerm_le_one hκ s L hL φ o
    have hmeas1 : ∀ (κ : ℝ) (o : Option W), Measurable fun L : W → ℝ =>
        ∫ φ, vertexTerm κ u s L φ o ∂Γ.toWired.gff := fun κ o =>
      (StronglyMeasurable.integral_prod_right' (f := fun q : (W → ℝ) × EuclideanSpace ℝ W =>
        vertexTerm κ u s q.1 q.2 o) (hcvt κ s o).measurable.stronglyMeasurable).measurable
    have hint2 : ∀ (κ : ℝ) (o : Option W), 0 ≤ κ →
        Integrable (fun L => ∫ φ, vertexTerm κ u s L φ o ∂Γ.toWired.gff)
          (Γ.toWired.holdingLaw s) := by
      intro κ o hκ
      refine Integrable.of_bound (hmeas1 κ o).aestronglyMeasurable 1 ?_
      filter_upwards [hLnn s] with L hL
      rw [Real.norm_eq_abs]
      refine abs_integral_le_of_abs_le fun φ => ?_
      rw [abs_of_nonneg (vertexTerm_nonneg _ _ _ _ _ _)]
      exact vertexTerm_le_one hκ s L hL φ o
    have hmeasD : Measurable fun L : W → ℝ => ∫ φ, Γ.disSum u s
        (WiredConductances.aMap (WithLp.toLp 2 L) φ) ∂Γ.toWired.gff :=
      (StronglyMeasurable.integral_prod_right' (f := fun q : (W → ℝ) × EuclideanSpace ℝ W =>
        Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 q.1) q.2))
        (hcD s).measurable.stronglyMeasurable).measurable
    have hDbd : ∀ L φ, |Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)| ≤
        Fintype.card E := fun L φ => by
      rw [abs_of_nonneg (Γ.disSum_nonneg u s _)]
      exact Γ.disSum_le_card u hu s _ (WiredConductances.aMap_nonneg _ _)
    have hintD : Integrable (fun L => ∫ φ, Γ.disSum u s
        (WiredConductances.aMap (WithLp.toLp 2 L) φ) ∂Γ.toWired.gff) (Γ.toWired.holdingLaw s) :=
      integrable_of_abs_le hmeasD (fun L => abs_integral_le_of_abs_le (hDbd L))
    have hsum_eq : ∑ e, (∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s) +
        ∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s)) =
        ∫ L, ∑ e, (∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff +
          ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff) ∂(Γ.toWired.holdingLaw s) := by
      rw [integral_finset_sum (Finset.univ : Finset E)
        (f := fun e L => ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff +
          ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff) (fun e _ =>
        (hint2 _ _ (Γ.cond_pos e).le).add (hint2 _ _ (Γ.cond_pos e).le))]
      apply Finset.sum_congr rfl
      intro e _
      rw [integral_add (hint2 _ _ (Γ.cond_pos e).le) (hint2 _ _ (Γ.cond_pos e).le)]
    rw [hsum_eq]
    refine integral_mono_ae hintD (integrable_finset_sum (Finset.univ : Finset E) fun e _ =>
      (hint2 _ _ (Γ.cond_pos e).le).add (hint2 _ _ (Γ.cond_pos e).le)) ?_
    filter_upwards [hLnn s] with L hL
    have hintDφ : Integrable (fun φ => Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ))
        Γ.toWired.gff :=
      integrable_of_abs_le ((hcD s).comp ((continuous_const : Continuous fun _ :
        EuclideanSpace ℝ W => L).prodMk continuous_id)).measurable (hDbd L)
    have hφ_eq : ∑ e, (∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff +
        ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff) =
        ∫ φ, ∑ e, (vertexTerm (Γ.cond e) u s L φ (Γ.tail e) +
          vertexTerm (Γ.cond e) u s L φ (Γ.head e)) ∂Γ.toWired.gff := by
      rw [integral_finset_sum (Finset.univ : Finset E)
        (f := fun e φ => vertexTerm (Γ.cond e) u s L φ (Γ.tail e) +
          vertexTerm (Γ.cond e) u s L φ (Γ.head e)) (fun e _ =>
        (hint1 _ _ L hL (Γ.cond_pos e).le).add (hint1 _ _ L hL (Γ.cond_pos e).le))]
      apply Finset.sum_congr rfl
      intro e _
      rw [integral_add (hint1 _ _ L hL (Γ.cond_pos e).le) (hint1 _ _ L hL (Γ.cond_pos e).le)]
    show _ ≤ ∑ e, (∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff +
        ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff)
    rw [hφ_eq]
    exact integral_mono hintDφ (integrable_finset_sum (Finset.univ : Finset E) fun e _ =>
      (hint1 _ _ L hL (Γ.cond_pos e).le).add (hint1 _ _ L hL (Γ.cond_pos e).le))
      (fun φ => Γ.disSum_le_vertexTerms hu s L φ)
  have hR : HasSum (fun s => Γ.toWired.soupMassAt (u ^ 2 / 2) s *
      ∑ e, (∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s) +
        ∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s)))
      (∑ e, (vertexAvg Γ (Γ.cond e) u (u ^ 2 / 2) (Γ.tail e) +
        vertexAvg Γ (Γ.cond e) u (u ^ 2 / 2) (Γ.head e))) := by
    have := hasSum_sum (s := (Finset.univ : Finset E)) fun e _ =>
      (Γ.hasSum_vertexTerm hK (u := u) (Γ.cond e) (Γ.cond_pos e) (Γ.tail e)).add
        (Γ.hasSum_vertexTerm hK (u := u) (Γ.cond e) (Γ.cond_pos e) (Γ.head e))
    convert this using 1
    funext s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hLnn' : ∀ s, 0 ≤ ∫ L, ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)
      ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) := fun s =>
    integral_nonneg fun L => integral_nonneg fun φ => Γ.disSum_nonneg u s _
  have hle : ∀ s, Γ.toWired.soupMassAt (u ^ 2 / 2) s *
      ∫ L, ∫ φ, Γ.disSum u s (WiredConductances.aMap (WithLp.toLp 2 L) φ)
        ∂Γ.toWired.gff ∂(Γ.toWired.holdingLaw s) ≤
      Γ.toWired.soupMassAt (u ^ 2 / 2) s *
      ∑ e, (∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.tail e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s) +
        ∫ L, ∫ φ, vertexTerm (Γ.cond e) u s L φ (Γ.head e) ∂Γ.toWired.gff
          ∂(Γ.toWired.holdingLaw s)) := fun s =>
    mul_le_mul_of_nonneg_left (hper s) (Γ.toWired.soupMassAt_nonneg ht s)
  rw [← hR.tsum_eq]
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le
    (fun s => mul_nonneg (Γ.toWired.soupMassAt_nonneg ht s) (hLnn' s)) hle hR.summable) hR.summable

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
