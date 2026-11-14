/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P7GoodRatios at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Compact
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Scale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.InputsPLA
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

 




























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 

 
lemma exists_good_point {μ : Measure DistC} [IsProbabilityMeasure μ] {B : Set DistC}
    (hB : μ B < 1) {p : DistC → Prop} (hp : ∀ᵐ g ∂μ, p g) : ∃ g, g ∉ B ∧ p g := by
  by_contra hcon
  push Not at hcon
  have hsub : (univ : Set DistC) ⊆ B ∪ {g | ¬ p g} := fun g _ => by
    by_cases hg : g ∈ B
    · exact Or.inl hg
    · exact Or.inr (hcon g hg)
  have h0 : μ {g | ¬ p g} = 0 := ae_iff.1 hp
  have := (measure_mono (μ := μ) hsub).trans (measure_union_le (μ := μ) _ _)
  rw [measure_univ, h0, add_zero] at this
  exact absurd hB (not_lt.2 this)

 
lemma field_bound_of_locErrSup {q ε η : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hεη : ε ≤ η) {U : Set ℂ}
    {g : DistC} {Xg : C(ℂ, ℝ)} (hX : ∀ u, Xg u = heatMollify ε g u) {K : ℝ} (hK : 0 ≤ K)
    (h3 : locErrSup q U η g ≤ ENNReal.ofReal K) :
    ∀ x ∈ U, |plMollify q ε hε g x - Xg x| ≤ K := by
  intro w hw
  have hle := le_iSup₂ (f := fun p (_ : p ∈ Ioc (0 : ℝ) η ×ˢ closure U) => locErr q g p) (ε, w)
    ⟨⟨hε.1, hεη⟩, subset_closure hw⟩
  have h3' : locErr q g (ε, w) ≤ ENNReal.ofReal K := hle.trans h3
  rw [locErr, plMollifyT_of_mem q g hε w] at h3'
  rw [abs_sub_comm, hX w]
  exact (ENNReal.ofReal_le_ofReal_iff hK).1 h3'

 
lemma mul_le_of_le_inv_mul {a : ℝ} (ha : 0 < a) {x y : ℝ≥0∞}
    (h : y ≤ ENNReal.ofReal a⁻¹ * x) : ENNReal.ofReal a * y ≤ x := by
  calc ENNReal.ofReal a * y ≤ ENNReal.ofReal a * (ENNReal.ofReal a⁻¹ * x) := mul_le_mul_right h _
    _ = x := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one,
        one_mul]

 
def unitRad : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩

lemma annAt_dilate_one (a b : ℝ) (h₁ : 0 < a) (h₁₂ : a < b) :
    (annAt 0 a b h₁ h₁₂).dilate unitRad unitRad.2 = annAt 0 a b h₁ h₁₂ := by
  rw [annAt_dilate]; exact annAt_congr rfl (one_mul a) (one_mul b) _ _ _ _

lemma ratioBC_pos (m c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r : Set.Ioi (0 : ℝ)) :
    0 < ratioBC m c ε r := by
  unfold ratioBC lfppScaleFactor
  have h1 : (0 : ℝ) < r := r.2
  have h2 := (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2) (Set.mem_Ioi.mp r.2))⟩).2
  have h3 := (m ε).2
  have h4 := (c r).2
  simp only [Set.mem_Ioi] at h2 h3 h4
  positivity

 
lemma le_of_chain_dir {M₁ c₁ C I E M₃ : ℝ} (hM₁ : 0 < M₁) (hc₁ : 0 < c₁) (hI : 0 < I)
    (h : M₁⁻¹ * c₁ ≤ C * I⁻¹ * E * M₃) : I ≤ C * E * M₃ * M₁ / c₁ := by
  rw [le_div_iff₀ hc₁]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ I * M₁)
  calc I * c₁ = I * M₁ * (M₁⁻¹ * c₁) := by field_simp
    _ ≤ I * M₁ * (C * I⁻¹ * E * M₃) := h2
    _ = C * E * M₃ * M₁ := by field_simp

 
lemma lt_of_chain_rev {E M₄ C S T W : ℝ} (hE : 0 < E) (hM : 0 < M₄) (hT : 0 < T) (hC : 0 < C)
    (hW : 0 < W) (hS : S < T⁻¹) (h : E⁻¹ * M₄⁻¹ ≤ C * S * W) : T < C * E * M₄ * W := by
  have h2 : E⁻¹ * M₄⁻¹ < C * T⁻¹ * W :=
    h.trans_lt (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hS hC) hW)
  rw [show C * T⁻¹ * W = (C * W) / T by ring, lt_div_iff₀ hT] at h2
  calc T = E⁻¹ * M₄⁻¹ * T * (E * M₄) := by field_simp
    _ < C * W * (E * M₄) := mul_lt_mul_of_pos_right h2 (by positivity)
    _ = C * E * M₄ * W := by ring

lemma sum_net_const (x : ℝ) :
    ∑ _b : Bool, ∑ _i ∈ Finset.range 9, ENNReal.ofReal x = ENNReal.ofReal (18 * x) := by
  simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_bool,
    nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  push_cast
  ring

lemma isConnected_ball3 : IsConnected (ball (0 : ℂ) 3) :=
  (convex_ball (0 : ℂ) 3).isConnected (nonempty_ball.2 (by norm_num))

 
lemma exists_small_eps {p₀ c₀ ε₀ ζ : ℝ} (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hε₀ : 0 < ε₀)
    (hζ1 : ζ < 1) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ε < ε₀ ∧ ε ≤ 1 / 2 ∧ c₀ * ε ^ p₀ ≤ 1 / 10 ∧ ε ^ (1 - ζ) ≤ 1 / 16 := by
  obtain ⟨e₁, he₁, he₁b⟩ := exists_rpow_le hp₀ (t := 1 / (10 * c₀)) (by positivity)
  obtain ⟨e₂, he₂, he₂b⟩ := exists_rpow_le (p := 1 - ζ) (by linarith) (t := 1 / 16) (by norm_num)
  refine ⟨min (min ε₀ (1 / 2)) (min e₁ e₂), by positivity, fun ε hε hεε₁ => ?_⟩
  have h1 : ε < ε₀ := lt_of_lt_of_le hεε₁ ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ε ≤ 1 / 2 := hεε₁.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ε ≤ e₁ := hεε₁.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : ε ≤ e₂ := hεε₁.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨h1, h2, ?_, he₂b ε hε.le h4⟩
  have := he₁b ε hε.le h3
  calc c₀ * ε ^ p₀ ≤ c₀ * (1 / (10 * c₀)) := mul_le_mul_of_nonneg_left this hc₀.le
    _ = 1 / 10 := by field_simp

 

 
theorem good_ratios_plus_of_inputs (hP6 : PLCompareSubset) (hS4 : Iface.DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q) {D : DistC → LSCMetric}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {q : ℝ} (hq : 0 < q) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ T₀ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₁ → ∀ T : ℝ, T₀ ≤ T →
      0 < plRadiusCount ζ ε →
      4 * (((plRadiusSet ζ ⟨ε, hε.1⟩).filter fun r => T < ratioBC m c ⟨ε, hε.1⟩ r).card : ℝ) <
        plRadiusCount ζ ε := by
  obtain ⟨Csub, hCsub, hCU⟩ := hP6 ξ Q hQ D c hD m hm q hq ζ hζ0 hζ1
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, -, hcmpP⟩ :=
    hCU (ball 0 3) isOpen_ball isConnected_ball3 isBounded_ball
  obtain ⟨μ, hμp, hμ⟩ := Uniqueness.Positivity.Witnesses.exists_canonical_normalized_law
  
  have hV := hD.2.2.2.2.2.2 μ id hμ (fun r g => circleAvg g r 0)
    (fun r => Uniqueness.Toolkit.AnnulusIteration.ae_isCircleAverage_circleAvg hμ.1 r 0)
  set A := annAt 0 (5 / 4) (7 / 4) (by norm_num) (by norm_num)
  obtain ⟨M₁, hM₁, hM₁b⟩ := (hV A).1.2 (1 / 8) (by norm_num)
  
  obtain ⟨K, hK, hKb⟩ := exists_measure_locErrSup_gt_le (P := μ) hμ.1 hq
    (U := ball (0 : ℂ) 4) isBounded_ball (η := 1 / 2) (by norm_num)
    (θ := ENNReal.ofReal (1 / 100)) (by norm_num)
  
  have hXex : ∀ δ : Set.Ioi (0 : ℝ), ∃ X : DistC → C(ℂ, ℝ), IsHeatSmoothing μ id δ X :=
    fun δ => by
      obtain ⟨X, -, hX⟩ := exists_heatVersion hμ δ δ.2
      exact ⟨X, hX⟩
  choose X0 hX0 using hXex
  obtain ⟨-, hS4t⟩ := (hS4 ξ Q hQ m hm).1 μ id hμ X0 hX0 ⟨ball 0 3, isOpen_ball⟩ isConnected_ball3
    1 2 one_mem_ball3 two_mem_ball3 (by norm_num)
  obtain ⟨M₃, hM₃, hM₃b⟩ := hS4t (1 / 8) (by norm_num)
  set c₁ : ℝ := (c unitRad : ℝ)
  have hc₁ : 0 < c₁ := (c unitRad).2
  set E := Real.exp (|(ξ : ℝ)| * K)
  obtain ⟨ε₁, hε₁, hε₁b⟩ := exists_small_eps hp₀ hc₀ hε₀ hζ1
  refine ⟨Csub * E * M₃ * M₁ / c₁ + 1, ε₁, hε₁, ?_⟩
  intro ε hε hεε₁ T hT hN
  obtain ⟨hεε₀, hε2, hεp, hρ⟩ := hε₁b ε hε.1 hεε₁
  by_contra hcon
  push Not at hcon
  set εI : Set.Ioi (0 : ℝ) := ⟨ε, hε.1⟩
  set Rt := (plRadiusSet ζ εI).filter fun r => T < ratioBC m c εI r
  have hN' : (0 : ℝ) < plRadiusCount ζ ε := by exact_mod_cast hN
  have hne : Rt.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Rt.card := by linarith
    exact_mod_cast this
  have hcard : (plRadiusCount ζ ε : ℝ) ≤ 100 * Rt.card := by
    have : (0 : ℝ) ≤ Rt.card := Nat.cast_nonneg _
    linarith
  have hB₄ := hcmpP μ id hμ ε hε hεε₀ Rt hne (Finset.filter_subset _ _) hcard
  
  set B₁ := {g : DistC | ENNReal.ofReal ((c unitRad : ℝ)⁻¹ *
      Real.exp (-((ξ : ℝ) * circleAvg g (unitRad : ℝ) 0))) *
      acrossDist (D g) (A.dilate unitRad unitRad.2) < ENNReal.ofReal M₁⁻¹}
  set B₂ := {g : DistC | ENNReal.ofReal K < locErrSup q (ball (0 : ℂ) 4) (1 / 2) g}
  set B₃ := {g : DistC | ENNReal.ofReal M₃ < ENNReal.ofReal ((m εI : ℝ)⁻¹) *
      DDDF.crossLenIn (ξ : ℝ) (X0 εI g) (ball 0 3) {1} {2}}
  set B₄ := {g : DistC | ¬ compareSubsetHolds (ξ : ℝ) D c m q ζ (ball 0 3) ε hε Rt hne Csub g}
  have hμB₁ : μ B₁ ≤ ENNReal.ofReal (1 / 8) := (hM₁b unitRad).2
  have hμB₂ : μ B₂ ≤ ENNReal.ofReal (1 / 100) := hKb
  have hμB₃ : μ B₃ ≤ ENNReal.ofReal (1 / 8) := (hM₃b ⟨ε, hε⟩).1
  have hμB₄ : μ B₄ ≤ ENNReal.ofReal (1 / 10) :=
    hB₄.trans (ENNReal.ofReal_le_ofReal hεp)
  have hBlt : μ (B₁ ∪ B₂ ∪ B₃ ∪ B₄) < 1 := by
    calc μ (B₁ ∪ B₂ ∪ B₃ ∪ B₄) ≤ μ B₁ + μ B₂ + μ B₃ + μ B₄ := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 100) + ENNReal.ofReal (1 / 8) +
            ENNReal.ofReal (1 / 10) := by gcongr
      _ < 1 := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.ofReal_lt_one]
          norm_num
  have hae : ∀ᵐ g ∂μ, circleAvg g (unitRad : ℝ) 0 = 0 ∧ ∀ u, X0 εI g u = heatMollify ε g u := by
    filter_upwards [hμ.2, DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ εI (X0 εI) (hX0 εI)]
      with g h1 h2
    exact ⟨Uniqueness.Toolkit.AnnulusIteration.circleAvg_eq_of_isCircleAverage (id g) unitRad 0 0 h1,
      h2⟩
  obtain ⟨g, hg, hca, hXg⟩ := exists_good_point hBlt hae
  simp only [mem_union, not_or] at hg
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hg
  simp only [B₁, B₂, B₃, B₄, mem_ofPred_eq, not_lt, not_not] at h1 h2 h3 h4
  rw [hca, mul_zero, neg_zero, Real.exp_zero, mul_one, annAt_dilate_one] at h1
  have hVg : ENNReal.ofReal (M₁⁻¹ * c₁) ≤ acrossDist (D g) A := by
    rw [ENNReal.ofReal_mul (inv_pos.2 hM₁).le, mul_comm]
    exact mul_le_of_le_inv_mul hc₁ h1
  have hfield := field_bound_of_locErrSup hε hε2 hXg hK.le h2
  have hinf : T < Rt.inf' hne (ratioBC m c εI) :=
    (Finset.lt_inf'_iff hne).2 fun r hr => (Finset.mem_filter.1 hr).2
  have hT0 : 0 < Csub * E * M₃ * M₁ / c₁ + 1 := by
    have : 0 ≤ Csub * E * M₃ * M₁ / c₁ := by positivity
    linarith
  have hIpos : 0 < Rt.inf' hne (ratioBC m c εI) := by linarith
  have hch := min_ratio_chain hCsub (hρ.trans (by norm_num)) hIpos h4 hVg
    (fun x hx => hfield x hx) h3 hM₃.le
  have := le_of_chain_dir hM₁ hc₁ hIpos hch
  linarith

 

 
theorem good_ratios_minus_of_inputs (hP2 : PLHeatAnnulusTight) (hP6 : PLCompareSubset)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q) {D : DistC → LSCMetric}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {q : ℝ} (hq : 0 < q) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ T₀ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₁ → ∀ T : ℝ, T₀ ≤ T →
      0 < plRadiusCount ζ ε →
      4 * (((plRadiusSet ζ ⟨ε, hε.1⟩).filter fun r => ratioBC m c ⟨ε, hε.1⟩ r < T⁻¹).card : ℝ) <
        plRadiusCount ζ ε := by
  obtain ⟨Csub, hCsub, hCU⟩ := hP6 ξ Q hQ D c hD m hm q hq ζ hζ0 hζ1
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, -, hcmpP⟩ :=
    hCU (ball 0 3) isOpen_ball isConnected_ball3 isBounded_ball
  obtain ⟨μ, hμp, hμ⟩ := Uniqueness.Positivity.Witnesses.exists_canonical_normalized_law
  
  have hV := hD.2.2.2.2.2.2 μ id hμ (fun r g => circleAvg g r 0)
    (fun r => Uniqueness.Toolkit.AnnulusIteration.ae_isCircleAverage_circleAvg hμ.1 r 0)
  set A := annAt 0 1 2 one_pos one_lt_two
  obtain ⟨M₂, hM₂, hM₂b⟩ := (hV A).2.2 (1 / 8) (by norm_num)
  
  obtain ⟨K, hK, hKb⟩ := exists_measure_locErrSup_gt_le (P := μ) hμ.1 hq
    (U := ball (0 : ℂ) 4) isBounded_ball (η := 1 / 2) (by norm_num)
    (θ := ENNReal.ofReal (1 / 100)) (by norm_num)
  
  have hXex : ∀ δ : Set.Ioi (0 : ℝ), ∃ X : DistC → C(ℂ, ℝ), IsHeatSmoothing μ id δ X :=
    fun δ => by
      obtain ⟨X, -, hX⟩ := exists_heatVersion hμ δ δ.2
      exact ⟨X, hX⟩
  choose X0 hX0 using hXex
  have hnetT : ∀ b : Bool, ∀ i : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ δ : Set.Ioi (0 : ℝ), (δ : ℝ) ≤ 1 →
      μ {g | acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (X0 δ g))
        (annAt (netPt b i) (1 / 8) (1 / 4) (by norm_num) (by norm_num)) < ENNReal.ofReal M⁻¹} ≤
        ENNReal.ofReal (1 / 400) := fun b i => by
    obtain ⟨-, hP⟩ := hP2 ξ Q hQ m hm μ id hμ X0 hX0
      (annAt (netPt b i) (1 / 8) (1 / 4) (by norm_num) (by norm_num))
    obtain ⟨M, hM, hMb⟩ := hP (1 / 400) (by norm_num)
    exact ⟨M, hM, fun δ hδ => (hMb δ hδ).1⟩
  choose Mn hMn hMnb using hnetT
  set M₄ := ∑ b : Bool, ∑ i ∈ Finset.range 9, Mn b i
  have hM₄ge : ∀ b : Bool, ∀ i : ℕ, i < 9 → Mn b i ≤ M₄ := fun b i hi => by
    refine le_trans ?_ (Finset.single_le_sum (f := fun b => ∑ i ∈ Finset.range 9, Mn b i)
      (fun b _ => Finset.sum_nonneg fun i _ => (hMn b i).le) (Finset.mem_univ b))
    exact Finset.single_le_sum (f := fun i => Mn b i) (fun i _ => (hMn b i).le)
      (Finset.mem_range.2 hi)
  have hM₄ : 0 < M₄ := lt_of_lt_of_le (hMn true 0) (hM₄ge true 0 (by norm_num))
  set c₁ : ℝ := (c unitRad : ℝ)
  have hc₁ : 0 < c₁ := (c unitRad).2
  set E := Real.exp (|(ξ : ℝ)| * K)
  obtain ⟨ε₁, hε₁, hε₁b⟩ := exists_small_eps hp₀ hc₀ hε₀ hζ1
  refine ⟨Csub * E * M₄ * (M₂ * c₁ + 1) + 1, ε₁, hε₁, ?_⟩
  intro ε hε hεε₁ T hT hN
  obtain ⟨hεε₀, hε2, hεp, hρ⟩ := hε₁b ε hε.1 hεε₁
  by_contra hcon
  push Not at hcon
  set εI : Set.Ioi (0 : ℝ) := ⟨ε, hε.1⟩
  set Rt := (plRadiusSet ζ εI).filter fun r => ratioBC m c εI r < T⁻¹
  have hN' : (0 : ℝ) < plRadiusCount ζ ε := by exact_mod_cast hN
  have hne : Rt.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Rt.card := by linarith
    exact_mod_cast this
  have hcard : (plRadiusCount ζ ε : ℝ) ≤ 100 * Rt.card := by
    have : (0 : ℝ) ≤ Rt.card := Nat.cast_nonneg _
    linarith
  have hB₄ := hcmpP μ id hμ ε hε hεε₀ Rt hne (Finset.filter_subset _ _) hcard
  have hεI1 : (εI : ℝ) ≤ 1 := hε.2.le
  
  set B₁ := {g : DistC | ENNReal.ofReal M₂ < ENNReal.ofReal ((c unitRad : ℝ)⁻¹ *
      Real.exp (-((ξ : ℝ) * circleAvg g (unitRad : ℝ) 0))) *
      aroundDist (D g) (A.dilate unitRad unitRad.2)}
  set B₂ := {g : DistC | ENNReal.ofReal K < locErrSup q (ball (0 : ℂ) 4) (1 / 2) g}
  set S : Bool → ℕ → Set DistC := fun b i => {g | acrossDist (Median.lfppMetric (ξ : ℝ) (m εI)
      (X0 εI g)) (annAt (netPt b i) (1 / 8) (1 / 4) (by norm_num) (by norm_num)) <
      ENNReal.ofReal (Mn b i)⁻¹}
  set B₃ := ⋃ b ∈ (Finset.univ : Finset Bool), ⋃ i ∈ Finset.range 9, S b i
  set B₄ := {g : DistC | ¬ compareSubsetHolds (ξ : ℝ) D c m q ζ (ball 0 3) ε hε Rt hne Csub g}
  have hμB₁ : μ B₁ ≤ ENNReal.ofReal (1 / 8) := (hM₂b unitRad).1
  have hμB₂ : μ B₂ ≤ ENNReal.ofReal (1 / 100) := hKb
  have hμB₃ : μ B₃ ≤ ENNReal.ofReal (18 * (1 / 400)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    rw [← sum_net_const (1 / 400)]
    refine Finset.sum_le_sum fun b _ => (measure_biUnion_finset_le _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => hMnb b i εI hεI1
  have hμB₄ : μ B₄ ≤ ENNReal.ofReal (1 / 10) :=
    hB₄.trans (ENNReal.ofReal_le_ofReal hεp)
  have hBlt : μ (B₁ ∪ B₂ ∪ B₃ ∪ B₄) < 1 := by
    calc μ (B₁ ∪ B₂ ∪ B₃ ∪ B₄) ≤ μ B₁ + μ B₂ + μ B₃ + μ B₄ := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 100) + ENNReal.ofReal (18 * (1 / 400)) +
            ENNReal.ofReal (1 / 10) := by gcongr
      _ < 1 := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.ofReal_lt_one]
          norm_num
  have hae : ∀ᵐ g ∂μ, circleAvg g (unitRad : ℝ) 0 = 0 ∧ ∀ u, X0 εI g u = heatMollify ε g u := by
    filter_upwards [hμ.2, DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ εI (X0 εI) (hX0 εI)]
      with g h1 h2
    exact ⟨Uniqueness.Toolkit.AnnulusIteration.circleAvg_eq_of_isCircleAverage (id g) unitRad 0 0 h1,
      h2⟩
  obtain ⟨g, hg, hca, hXg⟩ := exists_good_point hBlt hae
  simp only [mem_union, not_or] at hg
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hg
  simp only [B₁, B₂, B₄, mem_ofPred_eq, not_lt, not_not] at h1 h2 h4
  rw [hca, mul_zero, neg_zero, Real.exp_zero, mul_one, annAt_dilate_one] at h1
  have hfield := field_bound_of_locErrSup hε hε2 hXg hK.le h2
  have hnet : ∀ b : Bool, ∀ i : ℕ, i < 9 → ENNReal.ofReal M₄⁻¹ ≤
      acrossDist (Median.lfppMetric (ξ : ℝ) (m εI) (X0 εI g))
        (annAt (netPt b i) (1 / 8) (1 / 4) (by norm_num) (by norm_num)) := by
    intro b i hi
    have hgS : g ∉ S b i := fun hm' => h3 (mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ b))
      (mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi)) hm'))
    simp only [S, mem_ofPred_eq, not_lt] at hgS
    exact (ENNReal.ofReal_le_ofReal (inv_anti₀ (hMn b i) (hM₄ge b i hi))).trans hgS
  have hsupS : Rt.sup' hne (ratioBC m c εI) < T⁻¹ :=
    (Finset.sup'_lt_iff hne).2 fun r hr => (Finset.mem_filter.1 hr).2
  have hsup0 : 0 ≤ Rt.sup' hne (ratioBC m c εI) := by
    obtain ⟨r, hr⟩ := hne
    exact (ratioBC_pos m c εI r).le.trans (Finset.le_sup' _ hr)
  have hT0 : 0 < Csub * E * M₄ * (M₂ * c₁ + 1) + 1 := by
    have : 0 ≤ Csub * E * M₄ * (M₂ * c₁ + 1) := by positivity
    linarith
  have hch := max_ratio_chain hCsub hM₂.le hc₁ hρ hsup0 h4 h1 (fun x hx => hfield x hx) hnet
  rw [Real.exp_neg] at hch
  have := lt_of_chain_rev (Real.exp_pos _) hM₄ (by linarith) hCsub (by positivity) hsupS hch
  linarith

 

 
theorem lem_good_ratios_selected_of_inputs (hP2 : PLHeatAnnulusTight) (hP6 : PLCompareSubset)
    (hS4 : Iface.DG20Section4) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ Cr : ℝ, 1 < Cr ∧ ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1),
      (plRadiusCount ζ ε : ℝ) ≤ 2 * (((plRadiusSet ζ ⟨ε, hε.1⟩).filter fun r =>
        Cr⁻¹ ≤ ratioBC m c ⟨ε, hε.1⟩ r ∧ ratioBC m c ⟨ε, hε.1⟩ r ≤ Cr).card : ℝ) := by
  obtain ⟨Tp, εp, hεp, hplus⟩ := good_ratios_plus_of_inputs hP6 hS4 ξ Q hQ hD m hm one_pos hζ0 hζ1
  obtain ⟨Tm, εm, hεm, hminus⟩ :=
    good_ratios_minus_of_inputs hP2 hP6 ξ Q hQ hD m hm one_pos hζ0 hζ1
  obtain ⟨B, hB, hBb⟩ := ratioBC_bounds_compact hS4 hQ hD hm hζ0 hζ1 (lt_min hεp hεm)
  refine ⟨max (max Tp Tm) B + 2, by linarith [le_max_right (max Tp Tm) B], fun ε hε => ?_⟩
  set Cr := max (max Tp Tm) B + 2
  set εI : Set.Ioi (0 : ℝ) := ⟨ε, hε.1⟩
  have hcardS : ((plRadiusSet ζ εI).card : ℝ) = plRadiusCount ζ ε := by
    rw [card_plRadiusSet]
  by_cases hsmall : ε < min εp εm
  · rcases Nat.eq_zero_or_pos (plRadiusCount ζ ε) with h0 | hpos
    · rw [h0, Nat.cast_zero]; positivity
    · have h1 := hplus ε hε (lt_of_lt_of_le hsmall (min_le_left _ _)) Cr
        (by linarith [le_max_left Tp Tm, le_max_left (max Tp Tm) B]) hpos
      have h2 := hminus ε hε (lt_of_lt_of_le hsmall (min_le_right _ _)) Cr
        (by linarith [le_max_right Tp Tm, le_max_left (max Tp Tm) B]) hpos
      rw [← hcardS] at h1 h2 ⊢
      exact two_mul_card_good_ge _ _ Cr h1 h2
  · push Not at hsmall
    have hall : ((plRadiusSet ζ εI).filter fun r =>
        Cr⁻¹ ≤ ratioBC m c εI r ∧ ratioBC m c εI r ≤ Cr) = plRadiusSet ζ εI := by
      refine Finset.filter_true_of_mem fun r hr => ?_
      obtain ⟨hb1, hb2⟩ := hBb ε hε hsmall r hr
      have hBC : B ≤ Cr := by linarith [le_max_right (max Tp Tm) B]
      exact ⟨(inv_anti₀ (by linarith) hBC).trans hb1, hb2.trans hBC⟩
    rw [hall, hcardS]
    have : (0 : ℝ) ≤ plRadiusCount ζ ε := Nat.cast_nonneg _
    linarith

end SupercriticalLQGUniqueness.B2.Polylog
