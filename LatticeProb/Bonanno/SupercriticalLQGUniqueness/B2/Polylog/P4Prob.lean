/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4Prob at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Scale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

 


























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 
def unitField (X : C(ℂ, ℝ)) (r c' : ℝ) : C(ℂ, ℝ) :=
  ⟨fun u => X ((r : ℂ) * u) + -c', (X.continuous.comp (continuous_const.mul continuous_id)).add
    continuous_const⟩

lemma normL_eq_scale (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r : Set.Ioi (0 : ℝ))
    (g : DistC) :
    normL ξ m ε g 0 r = ENNReal.ofReal ((m ε : ℝ) * Real.exp (ξ * -circleAvg g r 0) /
      ((m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
        (Set.mem_Ioi.mp r.2))⟩ : ℝ) * r)) := by
  unfold normL lfppScaleFactor
  congr 1
  have h1 : (0 : ℝ) < r := r.2
  have h2 : (0 : ℝ) < (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
    (Set.mem_Ioi.mp r.2))⟩ : ℝ) := (m _).2
  have h3 : (0 : ℝ) < (m ε : ℝ) := (m ε).2
  rw [show ξ * -circleAvg g r 0 = -(ξ * circleAvg g r 0) by ring]
  field_simp

 
lemma inv_le_of_le_exp_mul {Y : ℝ≥0∞} {M' C' K' : ℝ} (hM : 0 < M')
    (hC : Real.exp K' * M' ≤ C') (hY : ENNReal.ofReal M'⁻¹ ≤ ENNReal.ofReal (Real.exp K') * Y) :
    ENNReal.ofReal C'⁻¹ ≤ Y := by
  have hk0 : ENNReal.ofReal (Real.exp K') ≠ 0 := by simpa using Real.exp_pos K'
  have hkt : ENNReal.ofReal (Real.exp K') ≠ ∞ := ENNReal.ofReal_ne_top
  have hCpos : 0 < C' := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hM) hC
  have h1 : ENNReal.ofReal C'⁻¹ ≤ (ENNReal.ofReal (Real.exp K'))⁻¹ * ENNReal.ofReal M'⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hC
  refine h1.trans ?_
  rw [ENNReal.inv_mul_le_iff hk0 hkt]
  exact hY

 
theorem lem_compare_event_prob_of_heatAnnulusTight (hT : PLHeatAnnulusTight)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    {q : ℝ} (hq : 0 < q) {ε₁ : ℝ} (hε₁ : ε₁ < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ (z : ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε ≤ ε₁ →
      ∀ r : Set.Ioi (0 : ℝ), ε ≤ r → (r : ℝ) ≤ 1 →
        ENNReal.ofReal p ≤ P {ω | h ω ∈ plEventLoc ξ D c m q z ε hε r C} := by
  obtain ⟨μ, hμp, hμ⟩ := Uniqueness.Positivity.Witnesses.exists_canonical_normalized_law
  set θ : ℝ := (1 - p) / 5 with hθdef
  have hθ : 0 < θ := by simp only [θ]; linarith
  
  have hV := hD.2.2.2.2.2.2 μ id hμ (fun r g => circleAvg g r 0)
    (fun r => Uniqueness.Toolkit.AnnulusIteration.ae_isCircleAverage_circleAvg hμ.1 r 0)
  obtain ⟨M₃, hM₃, hM₃b⟩ := (hV (annAt 0 1 2 one_pos one_lt_two)).1.2 θ hθ
  obtain ⟨M₄, hM₄, hM₄b⟩ := (hV (annAt 0 2 3 two_pos (by norm_num))).2.2 θ hθ
  
  obtain ⟨K, hK, hKb⟩ := exists_measure_locErrSup_gt_le (P := μ) hμ.1 hq
    (U := ball (0 : ℂ) 4) isBounded_ball hε₁ (θ := ENNReal.ofReal θ) (by positivity)
  
  have hXex : ∀ δ : Set.Ioi (0 : ℝ), ∃ X : DistC → C(ℂ, ℝ), IsHeatSmoothing μ id δ X :=
    fun δ => by
      obtain ⟨X, -, hX⟩ := exists_heatVersion hμ δ δ.2
      exact ⟨X, hX⟩
  choose X0 hX0 using hXex
  obtain ⟨-, hP2a⟩ := hT ξ Q hQ m hm μ id hμ X0 hX0 (annAt 0 1 2 one_pos one_lt_two)
  obtain ⟨-, hP2b⟩ := hT ξ Q hQ m hm μ id hμ X0 hX0 (annAt 0 2 3 two_pos (by norm_num))
  obtain ⟨M₁, hM₁, hM₁b⟩ := hP2a θ hθ
  obtain ⟨M₂, hM₂, hM₂b⟩ := hP2b θ hθ
  set MD := max M₃ M₄
  set ML := max M₁ M₂
  set Kx := |(ξ : ℝ)| * K
  set C := max (max MD (Real.exp Kx * ML)) 1
  have hMD : 0 < MD := lt_max_of_lt_left hM₃
  have hML : 0 < ML := lt_max_of_lt_left hM₁
  have hKx : 0 ≤ Kx := mul_nonneg (abs_nonneg _) hK.le
  refine ⟨C, le_max_right _ _, ?_⟩
  intro Ω _ P _ h hh z ε hε hεε₁ r hεr hr1
  rw [prob_plEventLoc_eq_zero P h hh hD m q z ε hε r C]
  have hlaw : P.map h = μ := by
    have := map_eq_of_candidate_normalized hh hμ
    rwa [Measure.map_id] at this
  have hEm := measurableSet_plEventLoc (ξ : ℝ) hD.1 c m q 0 ε hε r C
  rw [show {ω | h ω ∈ plEventLoc ξ D c m q 0 ε hε r C} = h ⁻¹' plEventLoc ξ D c m q 0 ε hε r C
    from rfl, ← Measure.map_apply hh.1.measurable hEm, hlaw]
  
  have hr : (0 : ℝ) < r := r.2
  set εI : Set.Ioi (0 : ℝ) := ⟨ε, hε.1⟩
  set δ : Set.Ioi (0 : ℝ) := ⟨ε / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp εI.2)
    (Set.mem_Ioi.mp r.2))⟩
  have hδ1 : (δ : ℝ) ≤ 1 := by
    show ε / r ≤ 1; rw [div_le_one hr]; exact hεr
  set cr : DistC → ℝ := fun g => circleAvg (affineComp r 0 g) 1 0
  set Y : DistC → C(ℂ, ℝ) := fun g => unitField (X0 εI g) r (cr g)
  set E := plEventLoc ξ D c m q 0 ε hε r C
  set A12 := annAt 0 1 2 one_pos one_lt_two
  set A23 := annAt 0 2 3 two_pos (by norm_num)
  have hdil12 : A12.dilate r r.2 = annAt 0 r (2 * r) r.2 (by linarith) := by
    simp only [A12]; rw [annAt_dilate]; exact annAt_congr rfl (mul_one _) (mul_comm _ _) _ _ _ _
  have hdil23 : A23.dilate r r.2 = annAround 0 r := by
    simp only [A23, annAround]; rw [annAt_dilate]; exact annAt_congr rfl (mul_comm _ _) (mul_comm _ _) _ _ _ _
  
  set B₁ := {g : DistC | normD ξ c g 0 r * acrossDist (D g) (annAt 0 r (2 * r) r.2 (by linarith)) <
    ENNReal.ofReal MD⁻¹}
  set B₂ := {g : DistC | ENNReal.ofReal MD < normD ξ c g 0 r * aroundDist (D g) (annAround 0 r)}
  set B₃ := {g : DistC | ENNReal.ofReal K < locErrSup q (ball (0 : ℂ) 4) ε₁ g}
  set B₄ := {g : DistC | acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (Y g)) A12 <
    ENNReal.ofReal ML⁻¹}
  set B₅ := {g : DistC | ENNReal.ofReal ML < aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) (Y g)) A23}
  have hB₁ : μ B₁ ≤ ENNReal.ofReal θ := by
    refine (measure_mono fun g hg => ?_).trans (hM₃b r).2
    show _ < ENNReal.ofReal M₃⁻¹
    have : ENNReal.ofReal MD⁻¹ ≤ ENNReal.ofReal M₃⁻¹ :=
      ENNReal.ofReal_le_ofReal (inv_anti₀ hM₃ (le_max_left _ _))
    refine lt_of_lt_of_le ?_ this
    simp only [id]
    rw [hdil12]; exact hg
  have hB₂ : μ B₂ ≤ ENNReal.ofReal θ := by
    refine (measure_mono fun g hg => ?_).trans (hM₄b r).1
    show ENNReal.ofReal M₄ < _
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_max_right M₃ M₄)) ?_
    simp only [id]
    rw [hdil23]; exact hg
  have hB₃ : μ B₃ ≤ ENNReal.ofReal θ := hKb
  have hYv : ∀ᵐ g ∂μ, ∀ u, Y g u = heatMollify (δ : ℝ) (gScale r g) u := by
    filter_upwards [ae_heatMollify_gScale hμ εI r (X0 εI) (hX0 εI)] with g hg u
    exact (hg u).symm
  have hXv : ∀ᵐ g ∂μ, ∀ u, X0 δ g u = heatMollify (δ : ℝ) g u :=
    DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ δ (X0 δ) (hX0 δ)
  have hsc := isWholePlaneGFF_gScale hμ.1 hr
  have hmapsc : μ.map (gScale r) = μ := by
    have := map_gScale hμ hr; rw [Measure.map_id] at this; exact this
  have hB₄ : μ B₄ ≤ ENNReal.ofReal θ := by
    refine (measure_le_of_scaled_version hsc.measurable.aemeasurable hmapsc (δ : ℝ) Y (X0 δ) hYv
      hXv (fun φ => acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) φ) A12 <
        ENNReal.ofReal ML⁻¹)).trans ?_
    refine (measure_mono fun g hg => ?_).trans (hM₁b δ hδ1).1
    exact lt_of_lt_of_le hg (ENNReal.ofReal_le_ofReal (inv_anti₀ hM₁ (le_max_left _ _)))
  have hB₅ : μ B₅ ≤ ENNReal.ofReal θ := by
    refine (measure_le_of_scaled_version hsc.measurable.aemeasurable hmapsc (δ : ℝ) Y (X0 δ) hYv
      hXv (fun φ => ENNReal.ofReal ML <
        aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) φ) A23)).trans ?_
    refine (measure_mono fun g hg => ?_).trans (hM₂b δ hδ1).2
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_max_right _ _)) hg
  
  have hgood : Eᶜ ≤ᵐ[μ] B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ := by
    filter_upwards [CircleAvg.ae_circleAvg_affineComp hμ.1 hr 0,
      DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ εI (X0 εI) (hX0 εI)] with g hcr hXε hgE
    simp only [id] at hcr hXε
    by_contra hbad
    simp only [mem_union, not_or] at hbad
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hbad
    apply hgE
    simp only [B₁, B₂, B₃, B₄, B₅, mem_ofPred_eq, not_lt] at h1 h2 h3 h4 h5
    
    have hcmp : ∀ w ∈ ball (0 : ℂ) 4, |X0 εI g w - plMollify q ε hε g w| ≤ K := by
      intro w hw
      have hle := le_iSup₂ (f := fun p (_ : p ∈ Ioc (0 : ℝ) ε₁ ×ˢ closure (ball (0 : ℂ) 4)) =>
        locErr q g p) (ε, w) ⟨⟨hε.1, hεε₁⟩, subset_closure hw⟩
      have h3' : locErr q g (ε, w) ≤ ENNReal.ofReal K := hle.trans h3
      rw [locErr, plMollifyT_of_mem q g hε w] at h3'
      rw [hXε w]
      exact (ENNReal.ofReal_le_ofReal_iff hK.le).1 h3'
    have hV4 : IsOpen (ball (0 : ℂ) 4) := isOpen_ball
    have hS4 : closedAnn 0 r (2 * r) ⊆ ball (0 : ℂ) 4 := fun w hw => by
      rw [mem_ball, dist_zero_right]; have := hw.2; rw [sub_zero] at this; linarith
    have hA4 : (annAround 0 r).toSet ⊆ ball (0 : ℂ) 4 := fun w hw => by
      rw [annAround, annAt_toSet] at hw
      rw [mem_ball, dist_zero_right]; have := hw.2; rw [sub_zero] at this; linarith
    
    have hφ : ∀ u, Y g u = X0 εI g ((r : ℂ) * u) + -cr g := fun u => rfl
    have hscA := unitScale_across_eq (ξ : ℝ) (m εI) (m δ) r (-cr g) hφ
    have hscR := unitScale_around_eq (ξ : ℝ) (m εI) (m δ) r (-cr g) hφ
    have hκ : ENNReal.ofReal ((m εI : ℝ) * Real.exp ((ξ : ℝ) * -cr g) / ((m δ : ℝ) * r)) =
        normL ξ m εI g 0 r := by
      rw [normL_eq_scale]; simp only [cr]; rw [hcr]
    rw [hκ] at hscA hscR
    
    have hcA := compactPathInf_lfppMetric_le (ξ : ℝ) (m εI) (φ := plMollifyC q ε hε g)
      (φ' := X0 εI g) hV4 (K := K) (fun x hx => hcmp x hx) (E := sphere 0 r)
      (F := sphere 0 (2 * r)) hS4
    have hcR := aroundDist_lfppMetric_le (ξ : ℝ) (m εI) (φ := X0 εI g)
      (φ' := plMollifyC q ε hε g) hV4 (K := K)
      (fun x hx => by rw [abs_sub_comm]; exact hcmp x hx) hA4
    refine ⟨?_, ?_, ?_, ?_⟩
    · 
      calc ENNReal.ofReal C⁻¹ ≤ ENNReal.ofReal MD⁻¹ :=
            ENNReal.ofReal_le_ofReal (inv_anti₀ hMD (le_max_of_le_left (le_max_left _ _)))
        _ ≤ normD ξ c g 0 r * acrossDist (D g) (annAt 0 r (2 * r) r.2 (by linarith)) := h1
        _ ≤ normD ξ c g 0 r * acrossIn (D g) 0 r (2 * r) :=
            mul_le_mul_right (acrossDist_le_acrossIn _ _ _ _) _
    · 
      exact h2.trans (ENNReal.ofReal_le_ofReal (le_max_of_le_left (le_max_left _ _)))
    · 
      refine inv_le_of_le_exp_mul hML (le_max_of_le_left (le_max_right _ _)) ?_
      calc ENNReal.ofReal ML⁻¹ ≤ acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (Y g)) A12 := h4
        _ = normL ξ m εI g 0 r * acrossDist (Median.lfppMetric (ξ : ℝ) (m εI) (X0 εI g))
              (annAt 0 r (2 * r) r.2 (by linarith)) := hscA
        _ ≤ normL ξ m εI g 0 r * acrossIn (Median.lfppMetric (ξ : ℝ) (m εI) (X0 εI g)) 0 r
              (2 * r) := mul_le_mul_right (acrossDist_le_acrossIn _ _ _ _) _
        _ ≤ normL ξ m εI g 0 r * (ENNReal.ofReal (Real.exp Kx) *
              acrossIn (plLocMetric (ξ : ℝ) q m ε hε g) 0 r (2 * r)) :=
            mul_le_mul_right hcA _
        _ = ENNReal.ofReal (Real.exp Kx) * (normL ξ m εI g 0 r *
              acrossIn (plLocMetric (ξ : ℝ) q m ε hε g) 0 r (2 * r)) := by ring
    · 
      calc normL ξ m εI g 0 r * aroundDist (plLocMetric (ξ : ℝ) q m ε hε g) (annAround 0 r)
          ≤ normL ξ m εI g 0 r * (ENNReal.ofReal (Real.exp Kx) *
              aroundDist (Median.lfppMetric (ξ : ℝ) (m εI) (X0 εI g)) (annAround 0 r)) :=
            mul_le_mul_right hcR _
        _ = ENNReal.ofReal (Real.exp Kx) *
              aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) (Y g)) A23 := by rw [hscR]; ring
        _ ≤ ENNReal.ofReal (Real.exp Kx) * ENNReal.ofReal ML := mul_le_mul_right h5 _
        _ = ENNReal.ofReal (Real.exp Kx * ML) := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (le_max_of_le_left (le_max_right _ _))
  
  have hcompl : μ Eᶜ ≤ ENNReal.ofReal (1 - p) := by
    calc μ Eᶜ ≤ μ (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) := measure_mono_ae hgood
      _ ≤ μ B₁ + μ B₂ + μ B₃ + μ B₄ + μ B₅ := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal θ + ENNReal.ofReal θ + ENNReal.ofReal θ + ENNReal.ofReal θ +
            ENNReal.ofReal θ := by gcongr
      _ = ENNReal.ofReal (1 - p) := by
          rw [← ENNReal.ofReal_add hθ.le hθ.le, ← ENNReal.ofReal_add (by positivity) hθ.le,
            ← ENNReal.ofReal_add (by positivity) hθ.le, ← ENNReal.ofReal_add (by positivity) hθ.le]
          congr 1; simp only [θ]; ring
  have hsum := measure_add_measure_compl (μ := μ) hEm
  rw [measure_univ] at hsum
  by_contra hlt
  push Not at hlt
  have : μ E + μ Eᶜ < ENNReal.ofReal p + ENNReal.ofReal (1 - p) :=
    ENNReal.add_lt_add_of_lt_of_le (measure_ne_top μ _) hlt hcompl
  rw [hsum, ← ENNReal.ofReal_add hp0.le (by linarith), show p + (1 - p) = 1 by ring,
    ENNReal.ofReal_one] at this
  exact lt_irrefl _ this

end SupercriticalLQGUniqueness.B2.Polylog
