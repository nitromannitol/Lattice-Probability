/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P7Trunc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7GoodRatios

 



















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 

def compareHolds (L Dg : LSCMetric) (ρ : ℝ) (U : Set ℂ) (C₀ : ℝ) : Prop :=
  ∀ (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U),
    L.internalSetDist (thickening ρ U) {x | (x : ℂ) ∈ ball z ρ} {x | (x : ℂ) ∈ ball w ρ} ≤
      ENNReal.ofReal C₀ * Dg.internal U (⟨z, hz⟩, ⟨w, hw⟩) ∧
    Dg.internalSetDist (thickening ρ U) {x | (x : ℂ) ∈ ball z ρ} {x | (x : ℂ) ∈ ball w ρ} ≤
      ENNReal.ofReal C₀ * L.internal U (⟨z, hz⟩, ⟨w, hw⟩)

 
lemma exists_plRadiusCount_pos {ζ : ℝ} (hζ0 : 0 < ζ) :
    ∃ εN : ℝ, 0 < εN ∧ ∀ ε : ℝ, 0 < ε → ε < εN → 0 < plRadiusCount ζ ε := by
  refine ⟨(10 : ℝ) ^ (-(22 / ζ)), Real.rpow_pos_of_pos (by norm_num) _, fun ε hε hεN => ?_⟩
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have h1 : Real.log ε < -(22 / ζ) * Real.log 10 := by
    have := Real.log_lt_log hε hεN
    rwa [Real.log_rpow (by norm_num)] at this
  have h2 : 11 < ζ / 2 * Real.logb 10 ε⁻¹ := by
    rw [Real.logb, Real.log_inv]
    have h3 : 22 / ζ < -Real.log ε / Real.log 10 := by
      rw [lt_div_iff₀ hl10]; linarith
    have h4 : ζ / 2 * (22 / ζ) = 11 := by field_simp; norm_num
    nlinarith
  have h5 : 11 ≤ ⌊ζ / 2 * Real.logb 10 ε⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast h2.le)
  unfold plRadiusCount
  omega

 
theorem prop_lqg_lfpp_trunc_of_inputs (hP2 : PLHeatAnnulusTight) (hP6 : PLCompareSubset)
    (hS4 : Iface.DG20Section4) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) {q : ℝ} (hq : 0 < q) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
          P {ω | ¬ compareHolds (plLocMetric (ξ : ℝ) q m ε hε (h ω)) (D (h ω)) (ε ^ (1 - ζ)) U C₀}
            ≤ ENNReal.ofReal (c₀ * ε ^ p₀) := by
  obtain ⟨Cr, hCr, hgood⟩ := lem_good_ratios_selected_of_inputs hP2 hP6 hS4 ξ Q hQ hD m hm hζ0 hζ1
  obtain ⟨Csub, hCsub, hCU⟩ := hP6 ξ Q hQ D c hD m hm q hq ζ hζ0 hζ1
  obtain ⟨εN, hεN, hεNb⟩ := exists_plRadiusCount_pos hζ0
  have hCr0 : 0 < Cr := lt_trans one_pos hCr
  refine ⟨Csub * Cr, mul_pos hCsub hCr0, fun U hUo hUc hUb => ?_⟩
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, hε₀1, hcmp⟩ := hCU U hUo hUc hUb
  refine ⟨p₀, c₀, min ε₀ εN, hp₀, hc₀, lt_min hε₀ hεN, lt_of_le_of_lt (min_le_left _ _) hε₀1, ?_⟩
  intro Ω _ P _ h hh ε hε hεε
  set εI : Set.Ioi (0 : ℝ) := ⟨ε, hε.1⟩
  set Rt := (plRadiusSet ζ εI).filter fun r => Cr⁻¹ ≤ ratioBC m c εI r ∧ ratioBC m c εI r ≤ Cr
  have hN : (0 : ℝ) < plRadiusCount ζ ε := by
    exact_mod_cast hεNb ε hε.1 (lt_of_lt_of_le hεε (min_le_right _ _))
  have hg := hgood ε hε
  have hne : Rt.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Rt.card := by linarith
    exact_mod_cast this
  have hcard : (plRadiusCount ζ ε : ℝ) ≤ 100 * Rt.card := by
    have : (0 : ℝ) ≤ Rt.card := Nat.cast_nonneg _
    linarith
  have hsup : Rt.sup' hne (ratioBC m c εI) ≤ Cr :=
    Finset.sup'_le hne _ fun r hr => (Finset.mem_filter.1 hr).2.2
  have hinf : Cr⁻¹ ≤ Rt.inf' hne (ratioBC m c εI) :=
    Finset.le_inf' hne _ fun r hr => (Finset.mem_filter.1 hr).2.1
  have hinf' : (Rt.inf' hne (ratioBC m c εI))⁻¹ ≤ Cr := by
    have := inv_anti₀ (inv_pos.2 hCr0) hinf
    rwa [inv_inv] at this
  have hA : Csub * Rt.sup' hne (ratioBC m c εI) ≤ Csub * Cr :=
    mul_le_mul_of_nonneg_left hsup hCsub.le
  have hB : Csub * (Rt.inf' hne (ratioBC m c εI))⁻¹ ≤ Csub * Cr :=
    mul_le_mul_of_nonneg_left hinf' hCsub.le
  refine (measure_mono fun ω hω => ?_).trans
    (hcmp P h hh ε hε (lt_of_lt_of_le hεε (min_le_left _ _)) Rt hne (Finset.filter_subset _ _)
      hcard)
  show ¬ compareSubsetHolds (ξ : ℝ) D c m q ζ U ε hε Rt hne Csub (h ω)
  intro hc
  apply hω
  intro z w hz hw
  obtain ⟨h1, h2⟩ := hc z w hz hw
  exact ⟨h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hA) _),
    h2.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hB) _)⟩

 
lemma tendsto_ofReal_mul_rpow {c₀ p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal (c₀ * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => c₀ * ε ^ p) (𝓝 0) (𝓝 (c₀ * (0 : ℝ) ^ p)) :=
    (tendsto_const_nhds.mul ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto))
  rw [Real.zero_rpow hp.ne', mul_zero] at h
  have := ENNReal.tendsto_ofReal (h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  rwa [ENNReal.ofReal_zero] at this

 

theorem thm_lqg_lfpp_of_inputs (hP2 : PLHeatAnnulusTight) (hP6 : PLCompareSubset)
    (hS4 : Iface.DG20Section4) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ δ, IsHeatSmoothing P h δ (X δ)) →
          Tendsto (fun ε : ℝ => if hε : ε ∈ Ioo (0 : ℝ) 1 then
              P {ω | ¬ compareHolds (Median.lfppMetric (ξ : ℝ) (m ⟨ε, hε.1⟩) (X ⟨ε, hε.1⟩ ω))
                (D (h ω)) (ε ^ (1 - ζ)) U Cm}
            else 0) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C₀, hC₀, hT⟩ := prop_lqg_lfpp_trunc_of_inputs hP2 hP6 hS4 ξ Q hQ hD m hm one_pos hζ0 hζ1
  set E := Real.exp (|(ξ : ℝ)| * 1)
  refine ⟨C₀ * E, mul_pos hC₀ (Real.exp_pos _), fun U hUo hUc hUb => ?_⟩
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, hε₀1, hTb⟩ := hT U hUo hUc hUb
  intro Ω _ P _ h hh X hX
  set V₁ := thickening 1 U
  have hV₁ : Bornology.IsBounded V₁ := hUb.thickening
  have herr := heatSmoothing_localized_tendsto hh one_pos hV₁ one_pos X hX
  set G : ℝ → ℝ≥0∞ := fun ε => if hε : ε ∈ Ioo (0 : ℝ) 1 then
    P {ω | ∃ z ∈ closure V₁, 1 < |X ⟨ε, hε.1⟩ ω z - plMollify 1 ε hε (h ω) z|} else 0
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal (c₀ * ε ^ p₀) + G ε) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_ofReal_mul_rpow (c₀ := c₀) hp₀).add herr
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hεε
  have hε : ε ∈ Ioo (0 : ℝ) 1 := ⟨hεε.1, lt_trans hεε.2 hε₀1⟩
  simp only [G, hε, ↓reduceDIte]
  refine (measure_mono fun ω hω => ?_).trans ((measure_union_le _ _).trans
    (add_le_add_left (hTb P h hh ε hε hεε.2) _))
  
  by_contra hno
  simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and, not_lt] at hno
  obtain ⟨hc, herr'⟩ := hno
  apply hω
  set ρ := ε ^ (1 - ζ)
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one hε.1.le hε.2.le (by linarith)
  have hρV : thickening ρ U ⊆ V₁ := thickening_mono hρ1 U
  have hUV : U ⊆ V₁ := self_subset_thickening one_pos U
  have hK1 : ∀ x ∈ thickening ρ U, |X ⟨ε, hε.1⟩ ω x - plMollifyC 1 ε hε (h ω) x| ≤ 1 :=
    fun x hx => herr' x (subset_closure (hρV hx))
  have hK2 : ∀ x ∈ U, |plMollifyC 1 ε hε (h ω) x - X ⟨ε, hε.1⟩ ω x| ≤ 1 :=
    fun x hx => by rw [abs_sub_comm]; exact herr' x (subset_closure (hUV hx))
  intro z w hz hw
  obtain ⟨h1, h2⟩ := hc z w hz hw
  have hEm : ENNReal.ofReal (C₀ * E) = ENNReal.ofReal E * ENNReal.ofReal C₀ := by
    rw [mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]
  constructor
  · calc (Median.lfppMetric (ξ : ℝ) (m ⟨ε, hε.1⟩) (X ⟨ε, hε.1⟩ ω)).internalSetDist
          (thickening ρ U) {x | (x : ℂ) ∈ ball z ρ} {x | (x : ℂ) ∈ ball w ρ}
        ≤ ENNReal.ofReal E * (plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).internalSetDist
          (thickening ρ U) {x | (x : ℂ) ∈ ball z ρ} {x | (x : ℂ) ∈ ball w ρ} :=
          internalSetDist_lfppMetric_le (ξ : ℝ) (m ⟨ε, hε.1⟩) isOpen_thickening hK1 _ _
      _ ≤ ENNReal.ofReal E * (ENNReal.ofReal C₀ * (D (h ω)).internal U (⟨z, hz⟩, ⟨w, hw⟩)) :=
          mul_le_mul_right h1 _
      _ = ENNReal.ofReal (C₀ * E) * (D (h ω)).internal U (⟨z, hz⟩, ⟨w, hw⟩) := by
          rw [hEm, mul_assoc]
  · calc (D (h ω)).internalSetDist (thickening ρ U) {x | (x : ℂ) ∈ ball z ρ}
          {x | (x : ℂ) ∈ ball w ρ}
        ≤ ENNReal.ofReal C₀ * (plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).internal U (⟨z, hz⟩, ⟨w, hw⟩) :=
          h2
      _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal E * (Median.lfppMetric (ξ : ℝ) (m ⟨ε, hε.1⟩)
            (X ⟨ε, hε.1⟩ ω)).internal U (⟨z, hz⟩, ⟨w, hw⟩)) :=
          mul_le_mul_right (internal_lfppMetric_le (ξ : ℝ) (m ⟨ε, hε.1⟩) hUo hK2 _) _
      _ = ENNReal.ofReal (C₀ * E) * (Median.lfppMetric (ξ : ℝ) (m ⟨ε, hε.1⟩)
            (X ⟨ε, hε.1⟩ ω)).internal U (⟨z, hz⟩, ⟨w, hw⟩) := by
          rw [hEm]; ring

end SupercriticalLQGUniqueness.B2.Polylog
