/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4Local at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Translate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Good

 



























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP
open LQGMetric (DistOn restrictTo)

 
def eventCarrier (z : ℂ) (r : ℝ) : Set ℂ := {w | r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 4 * r}

 
lemma lfpp_costs_eq_of_eqOn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {V : Set ℂ}
    (hV : IsOpen V) (heq : ∀ x ∈ V, φ x = φ' x) (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (hS : closedAnn z r (2 * r) ⊆ V) (hA : (annAround z r).toSet ⊆ V) :
    acrossIn (Median.lfppMetric ξ a φ) z r (2 * r) = acrossIn (Median.lfppMetric ξ a φ') z r (2 * r) ∧
    aroundDist (Median.lfppMetric ξ a φ) (annAround z r) =
      aroundDist (Median.lfppMetric ξ a φ') (annAround z r) := by
  have h1 : ∀ x ∈ V, |φ' x - φ x| ≤ 0 := fun x hx => by rw [heq x hx, sub_self, abs_zero]
  have h2 : ∀ x ∈ V, |φ x - φ' x| ≤ 0 := fun x hx => by rw [heq x hx, sub_self, abs_zero]
  have e : ENNReal.ofReal (Real.exp (|ξ| * 0)) = 1 := by simp
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · have := compactPathInf_lfppMetric_le ξ a hV h2 (E := sphere z r) (F := sphere z (2 * r)) hS
    rwa [e, one_mul] at this
  · have := compactPathInf_lfppMetric_le ξ a hV h1 (E := sphere z r) (F := sphere z (2 * r)) hS
    rwa [e, one_mul] at this
  · have := aroundDist_lfppMetric_le ξ a hV h2 hA
    rwa [e, one_mul] at this
  · have := aroundDist_lfppMetric_le ξ a hV h1 hA
    rwa [e, one_mul] at this

 
theorem plEventLoc_transfer {ξ : ℝ} {D : DistC → LSCMetric} {c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {q : ℝ} {z : ℂ} {ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1} {r : Set.Ioi (0 : ℝ)} {C : ℝ}
    {g₁ g₂ : DistC} {U : TopologicalSpace.Opens ℂ}
    (hI : (D g₁).internal U = (D g₂).internal U) (hres : restrictTo U g₁ = restrictTo U g₂)
    (hU : eventCarrier z r ⊆ U) (hρ : 2 * plRad q ε < r) :
    g₁ ∈ plEventLoc ξ D c m q z ε hε r C ↔ g₂ ∈ plEventLoc ξ D c m q z ε hε r C := by
  have hr : (0 : ℝ) < r := r.2
  have hρ0 : 0 < plRad q ε := plRad_pos q hε
  set ρ := plRad q ε
  have hS : closedAnn z r (2 * r) ⊆ U := fun w hw => hU ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hA : (annAround z r).toSet ⊆ U := fun w hw => by
    rw [annAround, annAt_toSet] at hw
    exact hU ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hsph : sphere z r ⊆ U := fun w hw => by
    rw [mem_sphere, dist_eq_norm] at hw
    exact hU ⟨by linarith, by linarith⟩
  have hacc := acrossIn_eq_of_internal_eq hS hI (z := z) (r₁ := r) (r₂ := 2 * r)
  have hround := Uniqueness.BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq
    (D g₁) (D g₂) U hI (annAround z r) hA
  have hca := Uniqueness.Objects.AnnulusTails.circleAvg_congr_restrict hres hr z hsph
  
  set η := (r / 2 - ρ) / 2
  have hηv : η = (r / 2 - ρ) / 2 := rfl
  have hη : 0 < η := by rw [hηv]; linarith
  set V : Set ℂ := {w | (r : ℝ) - η < ‖w - z‖ ∧ ‖w - z‖ < 3 * r + η}
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hball : ∀ x ∈ V, closedBall x ρ ⊆ U := fun x hx y hy => by
    rw [mem_closedBall, dist_eq_norm] at hy
    have t1 : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by
      calc ‖y - z‖ = ‖(y - x) + (x - z)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have t2 : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
      calc ‖x - z‖ = ‖(x - y) + (y - z)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have t3 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
    have hx1 : (r : ℝ) - η < ‖x - z‖ := hx.1
    have hx2 : ‖x - z‖ < 3 * r + η := hx.2
    exact hU ⟨by linarith, by linarith⟩
  have heq : ∀ x ∈ V, plMollifyC q ε hε g₁ x = plMollifyC q ε hε g₂ x := fun x hx =>
    plMollify_congr q ε hε U hres (hball x hx)
  have hSV : closedAnn z r (2 * r) ⊆ V := fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hAV : (annAround z r).toSet ⊆ V := fun w hw => by
    rw [annAround, annAt_toSet] at hw
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨hLa, hLr⟩ := lfpp_costs_eq_of_eqOn ξ (m ⟨ε, hε.1⟩) hVo heq z r hSV hAV
  simp only [plEventLoc, mem_ofPred_eq, normD, normL, plLocMetric]
  rw [hacc, hround, hca, hLa, hLr]

 
theorem ae_plEventLoc_addConst_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P) (hw : IsWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (C : ℝ) (k : Ω → ℝ) :
    ∀ᵐ ω ∂P, (addConst (h ω) (k ω) ∈ plEventLoc ξ D c m q z ε hε r C ↔
      h ω ∈ plEventLoc ξ D c m q z ε hε r C) := by
  filter_upwards [ae_addConst_eq_mul_of_pfe P h hh hD k,
    LQGMetric.CircleAvg.ae_circleAvg_addConst hw z r.2] with ω hsc hca
  set s : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * k ω))
  have hs0 : s ≠ 0 := by simpa [s] using Real.exp_pos _
  have hst : s ≠ ∞ := ENNReal.ofReal_ne_top
  have hD' : ∀ x y, D (addConst (h ω) (k ω)) (x, y) = s * D (h ω) (x, y) := fun x y => hsc (x, y)
  have hL' : ∀ x y, plLocMetric (ξ : ℝ) q m ε hε (addConst (h ω) (k ω)) (x, y) =
      s * plLocMetric (ξ : ℝ) q m ε hε (h ω) (x, y) := fun x y => by
    unfold plLocMetric
    rw [lfppMetric_affine (ξ : ℝ) (m ⟨ε, hε.1⟩) (m ⟨ε, hε.1⟩) (φ := plMollifyC q ε hε (h ω))
      (φ' := plMollifyC q ε hε (addConst (h ω) (k ω))) (b := 0) (c := 1) one_ne_zero (k ω)
      (fun u => by
        show plMollify q ε hε (addConst (h ω) (k ω)) u = plMollify q ε hε (h ω) (0 + 1 * u) + k ω
        rw [plMollify_addConst, zero_add, one_mul])]
    have hm := (m ⟨ε, hε.1⟩).2
    simp only [mem_Ioi] at hm
    rw [norm_one, mul_one, mul_div_cancel_left₀ _ hm.ne', zero_add, zero_add, one_mul, one_mul]
  have hnD : normD ξ c (addConst (h ω) (k ω)) z r =
      normD ξ c (h ω) z r * ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) := by
    unfold normD
    rw [hca, ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (c r).2.le) (Real.exp_pos _).le),
      mul_assoc, ← Real.exp_add]
    congr 3; ring
  have hnL : normL ξ m ⟨ε, hε.1⟩ (addConst (h ω) (k ω)) z r =
      normL ξ m ⟨ε, hε.1⟩ (h ω) z r * ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) := by
    unfold normL
    rw [hca, ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (lfppScaleFactor_pos m _ r).le)
      (Real.exp_pos _).le), mul_assoc, ← Real.exp_add]
    congr 3; ring
  have hcancel : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) * s = 1 := by
    rw [mul_comm]; exact exp_mul_cancel (ξ : ℝ) (k ω)
  have key : ∀ (n n' X : ℝ≥0∞), n' = n * ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) →
      n' * (s * X) = n * X := fun n n' X hn => by
    rw [hn, mul_assoc, ← mul_assoc _ s, hcancel, one_mul]
  simp only [plEventLoc, mem_ofPred_eq]
  rw [acrossIn_eq_mul_of_dist_scale _ _ s hs0 hst hD',
    Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale _ _ s hs0 hst hD',
    acrossIn_eq_mul_of_dist_scale _ _ s hs0 hst hL',
    Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale _ _ s hs0 hst hL',
    key _ _ _ hnD, key _ _ _ hnD, key _ _ _ hnL, key _ _ _ hnL]

 


theorem canonical_plEventLoc_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (C : ℝ)
    (U : TopologicalSpace.Opens ℂ) (hU : eventCarrier z r ⊆ U) (hρ : 2 * plRad q ε < r) :
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      plEventLoc ξ D c m q z ε hε r C =ᵐ[Uniqueness.TwoScale.S36.muH P h] restrictTo U ⁻¹' S := by
  have hprob := Uniqueness.TwoScale.S36.muH_isProb P h hh.1
  have hμ : IsGFFPlusCont (id : DistC → DistC) (Uniqueness.TwoScale.S36.muH P h) :=
    Uniqueness.BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1
  set E := plEventLoc ξ D c m q z ε hε r C with hEdef
  obtain ⟨FD, -, hlocD⟩ := hD.2.2.1 (Uniqueness.TwoScale.S36.muH P h) id hμ U
  obtain ⟨W, hWae, hWm, hWsub⟩ := hlocD.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ := fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ E → g₂ ∈ E := by
    intro g₁ hg₁ g₂ hg₂ he hE₁
    have hres : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U he
    have hI : (D g₁).internal U = (D g₂).internal U := by
      have h1 : (D (id g₁)).internal U = FD (restrictTo U (id g₁)) := hWsub g₁ hg₁
      have h2 : (D (id g₂)).internal U = FD (restrictTo U (id g₂)) := hWsub g₂ hg₂
      simp only [id] at h1 h2
      rw [h1, h2, hres]
    exact (plEventLoc_transfer hI hres hU hρ).mp hE₁
  have hB : NullMeasurableSet E ((Uniqueness.TwoScale.S36.muH P h).map id) :=
    (measurableSet_plEventLoc (ξ : ℝ) hD.1 c m q z ε hε r C).nullMeasurableSet
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := E) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl) hWm hB hWae hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  exact hFe

 



theorem plEventLoc_centered_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (C : ℝ)
    (U : TopologicalSpace.Opens ℂ) (hU : eventCarrier z r ⊆ U) (hρ : 2 * plRad q ε < r) (R : ℝ) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) R z)) U)
      {ω | h ω ∈ plEventLoc ξ D c m q z ε hε r C} := by
  set E := plEventLoc ξ D c m q z ε hε r C with hEdef
  let q' : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) R z))
  obtain ⟨S, hS, hLocal⟩ := canonical_plEventLoc_local P h hh hD m q z ε hε r C U hU hρ
  have hmeasH := (Uniqueness.BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable
  have hLocalProd : {y : Ω × ℝ | Uniqueness.BiLipschitz.OneScale.gaussianShift h y ∈ E}
      =ᵐ[P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian]
      {y : Ω × ℝ | restrictTo U (Uniqueness.BiLipschitz.OneScale.gaussianShift h y) ∈ S} :=
    ae_of_ae_map hmeasH.aemeasurable hLocal
  have hprodW : IsWholePlaneGFF (fun y : Ω × ℝ => h y.1)
      (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian) :=
    Uniqueness.BiLipschitz.OneScale.gff_prod_fst P Uniqueness.BiLipschitz.OneScale.standardGaussian
      h hh.1
  have hprod : IsGFFPlusCont (fun y : Ω × ℝ => h y.1)
      (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian) :=
    GM.Tight.isGFFPlusCont_of_wp hprodW
  have hInv := ae_plEventLoc_addConst_iff (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian)
    (fun y => h y.1) hprod hprodW hD m q z ε hε r C (fun y => y.2)
  have hAE : ∀ᵐ y ∂P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian,
      (h y.1 ∈ E ↔ Uniqueness.BiLipschitz.OneScale.localShift U (q' y.1)
        (circleAvg (h y.1) R z + y.2) ∈ S) := by
    filter_upwards [hInv, hLocalProd] with y hi hl
    have hShift : Uniqueness.BiLipschitz.OneScale.localShift U (q' y.1)
        (circleAvg (h y.1) R z + y.2) =
        restrictTo U (Uniqueness.BiLipschitz.OneScale.gaussianShift h y) := by
      calc Uniqueness.BiLipschitz.OneScale.localShift U (q' y.1) (circleAvg (h y.1) R z + y.2) =
            restrictTo U (addConst (addConst (h y.1) (-circleAvg (h y.1) R z))
              (circleAvg (h y.1) R z + y.2)) :=
          Uniqueness.BiLipschitz.OneScale.localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h y.1) y.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 2
          ring
        _ = restrictTo U (Uniqueness.BiLipschitz.OneScale.gaussianShift h y) := rfl
    rw [hShift]
    exact hi.symm.trans (Iff.of_eq hl)
  have hSmooth := Uniqueness.BiLipschitz.OneScale.gaussian_smoothing_event P U q'
    (fun ω => circleAvg (h ω) R z) {ω | h ω ∈ E} S hS hAE
  refine ⟨{ω | Uniqueness.BiLipschitz.OneScale.gaussianSmooth U S (q' ω) > 1 / 2}, ?_, ?_⟩
  · have hB : MeasurableSet {v : DistOn U |
        Uniqueness.BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (Uniqueness.BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω

end SupercriticalLQGUniqueness.B2.Polylog
