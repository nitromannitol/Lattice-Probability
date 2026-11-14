/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P5CompareIterate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P5Iterate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Prob
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Local
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Compact
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P2HeatAnnulusTight

 




















set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.Polylog

 
def plLatticePt (ε : ℝ) (j k : ℤ) : ℂ := ⟨ε / 100 * j, ε / 100 * k⟩

 

def compareIterateHolds (ξ : ℝ) (D : DistC → LSCMetric) (c m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (q : ℝ) (U : Set ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (Rt : Finset (Ioi (0 : ℝ)))
    (C : ℝ) (g : DistC) : Prop :=
  ∀ j k : ℤ, plLatticePt ε j k ∈ thickening 1 U →
    ∃ r ∈ Rt, g ∈ plEventLoc ξ D c m q (plLatticePt ε j k) ε hε r C

 
lemma exists_index_set {ζ : ℝ} {ε : Ioi (0 : ℝ)} {Rt : Finset (Ioi (0 : ℝ))}
    (hsub : Rt ⊆ plRadiusSet ζ ε) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (plRadiusCount ζ ε) ∧ Rt = S.image (plRadPt ζ ε) ∧
      S.card = Rt.card := by
  classical
  refine ⟨(Finset.range (plRadiusCount ζ ε)).filter fun i => plRadPt ζ ε i ∈ Rt,
    Finset.filter_subset _ _, ?_, ?_⟩
  · ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hr
      have := hsub hr
      rw [plRadiusSet_eq, Finset.mem_image] at this
      obtain ⟨i, hi, rfl⟩ := this
      exact ⟨i, ⟨Finset.mem_range.1 hi, hr⟩, rfl⟩
    · rintro ⟨i, ⟨-, hi⟩, rfl⟩
      exact hi
  · have hRt : Rt = ((Finset.range (plRadiusCount ζ ε)).filter
        fun i => plRadPt ζ ε i ∈ Rt).image (plRadPt ζ ε) := by
      ext r
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hr
        have := hsub hr
        rw [plRadiusSet_eq, Finset.mem_image] at this
        obtain ⟨i, hi, rfl⟩ := this
        exact ⟨i, ⟨Finset.mem_range.1 hi, hr⟩, rfl⟩
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩
        exact hi
    conv_rhs => rw [hRt]
    rw [Finset.card_image_of_injective _ (plRadPt_injective ζ ε)]

 
lemma geoRad_eq_five_plRadPt (ζ : ℝ) (ε : Ioi (0 : ℝ)) (i : ℕ) :
    geoRad (5 * (ε : ℝ) ^ (1 - ζ) * (10 : ℝ) ^ (-(2 : ℝ))) i = 5 * (plRadPt ζ ε i : ℝ) := by
  unfold geoRad plRadPt
  simp only
  rw [show -((i : ℝ) + 2) = -(2 : ℝ) + -(i : ℝ) by ring, Real.rpow_add (by norm_num)]
  ring

 


theorem compare_iterate_site_of_heatAnnulusTight (hT : PLHeatAnnulusTight)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    {q : ℝ} (hq : 0 < q) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (a : ℝ) (ha : 0 < a) :
    ∃ C₅ c₁ ε₂ : ℝ, 1 ≤ C₅ ∧ 0 < c₁ ∧ 0 < ε₂ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (u : ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₂ →
        ∀ Rt : Finset (Ioi (0 : ℝ)), Rt ⊆ plRadiusSet ζ ⟨ε, hε.1⟩ → Rt.Nonempty →
          P {ω | ∀ r ∈ Rt, h ω ∉ plEventLoc (ξ : ℝ) D c m q u ε hε r C₅} ≤
            ENNReal.ofReal (c₁ * Real.exp (-a * Rt.card)) := by
  obtain ⟨p, c₁, hp0, hp1, hc₁, hit⟩ := annulus_iteration_finset a ha
  obtain ⟨C₅, hC₅, hprob⟩ := lem_compare_event_prob_of_heatAnnulusTight hT ξ Q hQ hD m hm hq
    (ε₁ := 1 / 2) (by norm_num) hp0 hp1
  obtain ⟨ε₃, hε₃, hrad⟩ := exists_two_plRad_lt (q := q) (s := ζ / 2) (by positivity)
  refine ⟨C₅, c₁, min ε₃ (1 / 2), hC₅, hc₁, lt_min hε₃ (by norm_num), ?_⟩
  intro Ω _ P _ h hh u ε hε hεs Rt hsub hne
  classical
  set e : Ioi (0 : ℝ) := ⟨ε, hε.1⟩ with he
  obtain ⟨S, hSsub, hRtS, hcard⟩ := exists_index_set hsub
  have hSne : S.Nonempty := by
    rw [hRtS] at hne
    exact Finset.image_nonempty.1 hne
  let E : ℕ → Set Ω := fun i => {ω | h ω ∈ plEventLoc (ξ : ℝ) D c m q u ε hε (plRadPt ζ e i) C₅}
  set ρ₀ : ℝ := 5 * ε ^ (1 - ζ) * (10 : ℝ) ^ (-(2 : ℝ)) with hρ₀def
  have hρ₀ : 0 < ρ₀ := by
    have := Real.rpow_pos_of_pos hε.1 (1 - ζ)
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 10) (-(2 : ℝ))
    positivity
  have hεle : ε ≤ 1 / 2 := le_trans (le_of_lt (lt_of_lt_of_le hεs (min_le_right _ _))) le_rfl
  have hmemS : ∀ i ∈ S, plRadPt ζ e i ∈ plRadiusSet ζ e := by
    intro i hi
    rw [plRadiusSet_eq]
    exact Finset.mem_image_of_mem _ (hSsub hi)
  have hloc : ∀ i ∈ S, LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (geoRad ρ₀ i) u))
        (LQGMetric.Blueprint.annulus u (1 / 10 * geoRad ρ₀ i) (9 / 10 * geoRad ρ₀ i))) (E i) := by
    intro i hi
    have hg : geoRad ρ₀ i = 5 * (plRadPt ζ e i : ℝ) := by
      rw [hρ₀def]; exact geoRad_eq_five_plRadPt ζ e i
    have hU : eventCarrier u (plRadPt ζ e i) ⊆
        (LQGMetric.Blueprint.annulus u (1 / 10 * geoRad ρ₀ i) (9 / 10 * geoRad ρ₀ i) : Set ℂ) := by
      intro w hw
      rw [hg]
      have hr := (plRadPt ζ e i).2
      change (plRadPt ζ e i : ℝ) / 2 < ‖w - u‖ ∧ ‖w - u‖ < 4 * (plRadPt ζ e i : ℝ) at hw
      change 1 / 10 * (5 * (plRadPt ζ e i : ℝ)) < ‖w - u‖ ∧
        ‖w - u‖ < 9 / 10 * (5 * (plRadPt ζ e i : ℝ))
      have hr' : (0 : ℝ) < plRadPt ζ e i := hr
      constructor <;> linarith [hw.1, hw.2]
    have hiN : i < plRadiusCount ζ ε := Finset.mem_range.1 (hSsub hi)
    have hρ : 2 * plRad q ε < (plRadPt ζ e i : ℝ) :=
      lt_of_lt_of_le (hrad ε hε.1 (lt_of_lt_of_le hεs (min_le_left _ _)))
        (le_plRadPt hζ0 hε hiN)
    exact plEventLoc_centered_local P h hh hD m q u ε hε (plRadPt ζ e i) C₅ _ hU hρ _
  have hpr : ∀ i ∈ S, ENNReal.ofReal p ≤ P (E i) := by
    intro i hi
    have hb := mem_plRadiusSet_bounds hζ0 hζ1 hε (hmemS i hi)
    exact hprob P h hh u ε hε hεle (plRadPt ζ e i) hb.1.le hb.2.le
  have hmain := hit P h hh.1 u ρ₀ hρ₀ S hSne E hloc hpr
  rw [hcard] at hmain
  refine le_trans (measure_mono ?_) hmain
  intro ω hω i hi hωi
  exact hω (plRadPt ζ e i) (by rw [hRtS]; exact Finset.mem_image_of_mem _ hi) hωi


 

lemma exp_neg_card_le {ζ ε : ℝ} (hζ : 0 < ζ) (hε : ε ∈ Ioo (0 : ℝ) 1) {K : ℕ}
    (hK : (plRadiusCount ζ ε : ℝ) ≤ 100 * K) :
    Real.exp (-(600 * Real.log 10 / ζ) * K) ≤
      Real.exp (11 * (600 * Real.log 10 / ζ) / 100) * ε ^ 3 := by
  have hN := plRadiusCount_ge hζ.le hε
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have ha : 0 < 600 * Real.log 10 / ζ := by positivity
  have hx : 600 * Real.log 10 / ζ * (ζ / 2 * Real.logb 10 ε⁻¹) / 100 = -(3 * Real.log ε) := by
    rw [Real.logb, Real.log_inv]
    field_simp
    ring
  have hK' : (ζ / 2 * Real.logb 10 ε⁻¹ - 11) / 100 ≤ K := by linarith
  have hexp : -(600 * Real.log 10 / ζ) * K ≤ 11 * (600 * Real.log 10 / ζ) / 100 + 3 * Real.log ε := by
    have := mul_le_mul_of_nonneg_left hK' ha.le
    nlinarith
  calc Real.exp (-(600 * Real.log 10 / ζ) * K)
      ≤ Real.exp (11 * (600 * Real.log 10 / ζ) / 100 + 3 * Real.log ε) := Real.exp_le_exp.2 hexp
    _ = Real.exp (11 * (600 * Real.log 10 / ζ) / 100) * ε ^ 3 := by
        rw [Real.exp_add, show (3 : ℝ) * Real.log ε = ((3 : ℕ) : ℝ) * Real.log ε by norm_num,
          Real.exp_nat_mul, Real.exp_log hε.1]

 
lemma card_pos_of_count {ζ ε : ℝ} (hζ : 0 < ζ) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hεs : ε < (10 : ℝ) ^ (-(24 / ζ))) {K : ℕ} (hK : (plRadiusCount ζ ε : ℝ) ≤ 100 * K) :
    0 < K := by
  have hN := plRadiusCount_ge hζ.le hε
  have hlt : (10 : ℝ) ^ (24 / ζ) < ε⁻¹ := by
    rw [Real.rpow_neg (by norm_num)] at hεs
    exact (lt_inv_comm₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 10) (24 / ζ)) hε.1).2 hεs
  have hlog : 24 / ζ < Real.logb 10 ε⁻¹ :=
    (Real.lt_logb_iff_rpow_lt (by norm_num) (inv_pos.2 hε.1)).2 hlt
  have h12 : 12 < ζ / 2 * Real.logb 10 ε⁻¹ := by
    have := mul_lt_mul_of_pos_left hlog (by positivity : (0 : ℝ) < ζ / 2)
    have e : ζ / 2 * (24 / ζ) = 12 := by field_simp; norm_num
    linarith
  have : (0 : ℝ) < K := by linarith
  exact_mod_cast this

 
theorem lem_compare_iterate_of_heatAnnulusTight (hT : PLHeatAnnulusTight)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    {q : ℝ} (hq : 0 < q) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C₅ : ℝ, 1 ≤ C₅ ∧ ∀ U : Set ℂ, Bornology.IsBounded U →
      ∃ c₀ ε₀ : ℝ, 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
        ∀ Rt : Finset (Ioi (0 : ℝ)), Rt ⊆ plRadiusSet ζ ⟨ε, hε.1⟩ →
          (plRadiusCount ζ ε : ℝ) ≤ 100 * Rt.card →
          P {ω | ¬ compareIterateHolds (ξ : ℝ) D c m q U ε hε Rt C₅ (h ω)} ≤
            ENNReal.ofReal (c₀ * ε) := by
  set a : ℝ := 600 * Real.log 10 / ζ with hadef
  have ha : 0 < a := by have := Real.log_pos (by norm_num : (1 : ℝ) < 10); positivity
  obtain ⟨C₅, c₁, ε₂, hC₅, hc₁, hε₂, hsite⟩ :=
    compare_iterate_site_of_heatAnnulusTight hT ξ Q hQ hD m hm hq hζ0 hζ1 a ha
  refine ⟨C₅, hC₅, fun U hU => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hU.subset_closedBall (0 : ℂ)
  set R₁ : ℝ := max R₀ 0 + 1 with hR₁def
  have hR₁ : 1 ≤ R₁ := by simp only [hR₁def]; linarith [le_max_right R₀ 0]
  set c₀ : ℝ := c₁ * Real.exp (11 * a / 100) * (200 * R₁ + 3) ^ 2 with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  set ε₀ : ℝ := min ε₂ (min (1 / 2) ((10 : ℝ) ^ (-(24 / ζ)))) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε₂ (lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
  have hε₀1 : ε₀ < 1 := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _))
    (by norm_num)
  refine ⟨c₀, ε₀, hc₀, hε₀, hε₀1, ?_⟩
  intro Ω _ P _ h hh ε hε hεε₀ Rt hsub hcount
  classical
  have hε₂' : ε < ε₂ := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have hε24 : ε < (10 : ℝ) ^ (-(24 / ζ)) :=
    lt_of_lt_of_le hεε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hKpos : 0 < Rt.card := card_pos_of_count hζ0 hε hε24 hcount
  have hne : Rt.Nonempty := Finset.card_pos.1 hKpos
  set Mn : ℕ := ⌈100 * R₁ / ε⌉₊ with hMndef
  let box : Finset (ℤ × ℤ) := Finset.Icc (-(Mn : ℤ)) Mn ×ˢ Finset.Icc (-(Mn : ℤ)) Mn
  let F : ℤ × ℤ → Set Ω := fun p =>
    {ω | ∀ r ∈ Rt, h ω ∉ plEventLoc (ξ : ℝ) D c m q (plLatticePt ε p.1 p.2) ε hε r C₅}
  have hcoord : ∀ (j k : ℤ), plLatticePt ε j k ∈ thickening 1 U →
      (j, k) ∈ box := by
    intro j k hu
    obtain ⟨y, hyU, hdy⟩ := mem_thickening_iff.1 hu
    have hy : ‖y‖ ≤ max R₀ 0 :=
      le_trans (by simpa using mem_closedBall.1 (hR₀ hyU)) (le_max_left _ _)
    have hu' : ‖plLatticePt ε j k‖ < R₁ := by
      have := norm_le_norm_add_norm_sub' (plLatticePt ε j k) y
      rw [dist_eq_norm] at hdy
      rw [hR₁def]
      linarith
    have hMn : 100 * R₁ / ε ≤ Mn := Nat.le_ceil _
    have hbd : ∀ t : ℤ, |ε / 100 * t| < R₁ → -(Mn : ℤ) ≤ t ∧ t ≤ Mn := by
      intro t ht
      rw [abs_mul, abs_of_pos (by linarith [hε.1] : (0 : ℝ) < ε / 100)] at ht
      have h1 : |(t : ℝ)| < 100 * R₁ / ε := by
        rw [lt_div_iff₀ hε.1]
        nlinarith
      have h2 : |(t : ℝ)| < Mn := lt_of_lt_of_le h1 hMn
      rw [abs_lt] at h2
      constructor
      · have : (-(Mn : ℤ) : ℝ) < t := by push_cast; linarith
        exact_mod_cast this.le
      · have : (t : ℝ) < ((Mn : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast this.le
    have hre : |ε / 100 * j| < R₁ :=
      lt_of_le_of_lt (by simpa [plLatticePt] using Complex.abs_re_le_norm (plLatticePt ε j k)) hu'
    have him : |ε / 100 * k| < R₁ :=
      lt_of_le_of_lt (by simpa [plLatticePt] using Complex.abs_im_le_norm (plLatticePt ε j k)) hu'
    simp only [box, Finset.mem_product, Finset.mem_Icc]
    exact ⟨hbd j hre, hbd k him⟩
  have hsubset : {ω | ¬ compareIterateHolds (ξ : ℝ) D c m q U ε hε Rt C₅ (h ω)} ⊆
      ⋃ p ∈ box, F p := by
    intro ω hω
    simp only [compareIterateHolds, mem_ofPred_eq, not_forall, not_exists, not_and] at hω
    obtain ⟨j, k, hu, hno⟩ := hω
    exact mem_biUnion (hcoord j k hu) (fun r hr hmem => hno r hr hmem)
  have hsiteb : ∀ p ∈ box, P (F p) ≤ ENNReal.ofReal (c₁ * Real.exp (-a * Rt.card)) :=
    fun p _ => hsite P h hh _ ε hε hε₂' Rt hsub hne
  have hcardbox : box.card = (2 * Mn + 1) * (2 * Mn + 1) := by
    simp only [box, Finset.card_product, Int.card_Icc]
    congr 1 <;> omega
  have hexp := exp_neg_card_le hζ0 hε hcount
  rw [← hadef] at hexp
  have hMn1 : (Mn : ℝ) < 100 * R₁ / ε + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hε.1.le)
  have hεle1 : ε ≤ 1 := hε.2.le
  have h2M : (2 * (Mn : ℝ) + 1) ≤ (200 * R₁ + 3) / ε := by
    rw [le_div_iff₀ hε.1]
    have : (Mn : ℝ) * ε ≤ 100 * R₁ + ε := by
      have := mul_lt_mul_of_pos_right hMn1 hε.1
      rw [add_mul, div_mul_cancel₀ _ hε.1.ne', one_mul] at this
      linarith
    nlinarith
  calc P {ω | ¬ compareIterateHolds (ξ : ℝ) D c m q U ε hε Rt C₅ (h ω)}
      ≤ P (⋃ p ∈ box, F p) := measure_mono hsubset
    _ ≤ ∑ p ∈ box, P (F p) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ box, ENNReal.ofReal (c₁ * Real.exp (-a * Rt.card)) := Finset.sum_le_sum hsiteb
    _ = ENNReal.ofReal (box.card * (c₁ * Real.exp (-a * Rt.card))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (c₀ * ε) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hcardbox]
        push_cast
        have hB : c₁ * Real.exp (-a * Rt.card) ≤ c₁ * (Real.exp (11 * a / 100) * ε ^ 3) :=
          mul_le_mul_of_nonneg_left hexp hc₁.le
        have hsq : (2 * (Mn : ℝ) + 1) * (2 * (Mn : ℝ) + 1) ≤ ((200 * R₁ + 3) / ε) ^ 2 := by
          rw [sq]
          exact mul_le_mul h2M h2M (by positivity) (div_nonneg (by linarith) hε.1.le)
        calc (2 * (Mn : ℝ) + 1) * (2 * (Mn : ℝ) + 1) * (c₁ * Real.exp (-a * Rt.card))
            ≤ ((200 * R₁ + 3) / ε) ^ 2 * (c₁ * (Real.exp (11 * a / 100) * ε ^ 3)) :=
              mul_le_mul hsq hB (by positivity) (by positivity)
          _ = c₀ * ε := by
              rw [hc₀def, div_pow]
              field_simp

 

def PLCompareIterate : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ D : DistC → LSCMetric, ∀ c : Ioi (0 : ℝ) → Ioi (0 : ℝ), Iface.IsPfeWeakMetric ξ D c →
    ∀ m : Ioi (0 : ℝ) → Ioi (0 : ℝ), (∀ δ, IsLFPPNormalizer ξ δ (m δ)) →
    ∀ q : ℝ, 0 < q → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ C₅ : ℝ, 1 ≤ C₅ ∧ ∀ U : Set ℂ, Bornology.IsBounded U →
      ∃ c₀ ε₀ : ℝ, 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
        ∀ Rt : Finset (Ioi (0 : ℝ)), Rt ⊆ plRadiusSet ζ ⟨ε, hε.1⟩ →
          (plRadiusCount ζ ε : ℝ) ≤ 100 * Rt.card →
          P {ω | ¬ compareIterateHolds (ξ : ℝ) D c m q U ε hε Rt C₅ (h ω)} ≤
            ENNReal.ofReal (c₀ * ε)

 
theorem plCompareIterate_of_heatAnnulusTight (hT : PLHeatAnnulusTight) : PLCompareIterate :=
  fun ξ Q hQ _D _c hD m hm _q hq _ζ hζ0 hζ1 =>
    lem_compare_iterate_of_heatAnnulusTight hT ξ Q hQ hD m hm hq hζ0 hζ1

 
theorem plCompareIterate_of_inputs (hPerc : Iface.DG20PercEstimate')
    (hS4 : Iface.DG20Section4) : PLCompareIterate :=
  plCompareIterate_of_heatAnnulusTight (plHeatAnnulusTight_of_inputs hPerc hS4)

end SupercriticalLQGUniqueness.B2.Polylog
