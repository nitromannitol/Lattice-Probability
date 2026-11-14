/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P2HeatAnnulusTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P2HeatDet
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteLowerTail

 

















set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open LQGMetric (DistC lfppLen)
open LQGMetric.DDDF (crossLenIn)

namespace SupercriticalLQGUniqueness.B2.Polylog

 

theorem heat_across_lower_tail_of_perc (hPerc : Iface.DG20PercEstimate') (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ δ : Ioi (0 : ℝ), (δ : ℝ) ≤ 1 →
      P {ω | acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A <
        ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal η := by
  obtain ⟨T, ε₀, hT, hε₀, hsmall⟩ :=
    PfeAxioms.dg20_heat_across_small_lower_of_perc hPerc ξ m hm P h hh X hX A η hη
  set ε₁ : ℝ := min ε₀ (1 / 2) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε₀ (by norm_num)
  obtain ⟨R, κ, hκ, hdet⟩ := exists_across_lower_of_field_bound A
  obtain ⟨Mf, hMf, hfield⟩ :=
    heat_compact_field_tail_Icc P h hh X hX ε₁ R hε₁ (closedBall (0 : ℂ) R) subset_rfl η hη
  obtain ⟨c, C, hc, hC, hmb⟩ := heat_normalizer_bounds_Icc ξ m hm P h hh X hX ε₁ hε₁
  set L : ℝ := C⁻¹ * (Real.exp (-(|(ξ : ℝ)| * Mf)) * κ) with hLdef
  have hL : 0 < L := by positivity
  refine ⟨max T L⁻¹, lt_max_of_lt_left hT, ?_⟩
  intro δ hδ1
  have hMT : ENNReal.ofReal (max T L⁻¹)⁻¹ ≤ ENNReal.ofReal T⁻¹ :=
    ENNReal.ofReal_le_ofReal ((inv_le_inv₀ (lt_max_of_lt_left hT) hT).2 (le_max_left _ _))
  have hML : ENNReal.ofReal (max T L⁻¹)⁻¹ ≤ ENNReal.ofReal L := by
    apply ENNReal.ofReal_le_ofReal
    rw [inv_le_comm₀ (lt_max_of_lt_left hT) hL]
    exact le_max_right _ _
  rcases lt_or_ge (δ : ℝ) ε₁ with hlt | hge
  · 
    have hδ0 : (δ : ℝ) < ε₀ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hδ1' : (δ : ℝ) < 1 := by
      have : ε₁ ≤ 1 / 2 := min_le_right _ _
      linarith
    let e : Ioo (0 : ℝ) 1 := ⟨δ, δ.2, hδ1'⟩
    have hs := hsmall e hδ0
    refine le_trans (measure_mono ?_) hs
    intro ω hω
    change acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A < _ at hω
    change acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m δ) (X δ ω)) A <
      ENNReal.ofReal T⁻¹
    rw [← lfppMetric_eq_normalizedLFPPMetric]
    exact lt_of_lt_of_le hω hMT
  · 
    refine le_trans (measure_mono ?_) (hfield δ hge hδ1)
    intro ω hω
    by_contra hbad
    simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hbad
    have hlow := hdet (ξ : ℝ) (m δ) (X δ ω) Mf hbad
    have hmδ : C⁻¹ ≤ ((m δ : ℝ))⁻¹ := (inv_le_inv₀ hC (m δ).2).2 (hmb δ hge hδ1).2
    have hLle : ENNReal.ofReal L ≤
        ENNReal.ofReal (((m δ : ℝ))⁻¹ * (Real.exp (-(|(ξ : ℝ)| * Mf)) * κ)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hmδ (by positivity))
    exact absurd (lt_of_lt_of_le hω hML) (not_lt.2 (hLle.trans hlow))

 

theorem heat_around_upper_tail_of_section4 (hS4 : Iface.DG20Section4) (ξ : Ioi (0 : ℝ))
    (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ δ : Ioi (0 : ℝ), (δ : ℝ) ≤ 1 →
      P {ω | ENNReal.ofReal M <
        aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A} ≤ ENNReal.ofReal η := by
  
  have hpts : ∀ j : Fin 4, ∃ z w : ℂ, z ∈ Strong.cfgSet₁ A j ∧ w ∈ Strong.cfgSet₂ A j := by
    intro j
    obtain ⟨-, -, -, -, -, h₁, h₂, -, -, -, -⟩ := DG20Pt.around_polar_data A j
    obtain ⟨z, hz⟩ := h₁.nonempty
    obtain ⟨w, hw⟩ := h₂.nonempty
    exact ⟨z, w, hz, hw⟩
  choose z w hz hw using hpts
  
  have hbox : ∀ j : Fin 4, ∃ Mj : ℝ, 0 < Mj ∧ ∀ ε : Ioo (0 : ℝ) 1,
      P {ω | ENNReal.ofReal Mj < ENNReal.ofReal ((m ⟨ε, ε.property.1⟩ : ℝ))⁻¹ *
        crossLenIn (ξ : ℝ) (X ⟨ε, ε.property.1⟩ ω) (Strong.cfgOpens A j : Set ℂ)
          {z j} {w j}} ≤ ENNReal.ofReal (η / 4) := by
    intro j
    obtain ⟨-, -, -, -, -, -, -, hs₁, hs₂, hdisj, hU⟩ := DG20Pt.around_polar_data A j
    have hzw : z j ≠ w j := fun he => hdisj.ne_of_mem (hz j) (hw j) he
    have hT := (hS4 ξ Q hQ m hm).1 P h hh X hX (Strong.cfgOpens A j) hU (z j) (w j)
      (hs₁ (hz j)) (hs₂ (hw j)) hzw
    obtain ⟨Mj, hMj, hb⟩ := hT.2 (η / 4) (by positivity)
    exact ⟨Mj, hMj, fun ε => (hb ε).1⟩
  choose Mb hMb hbtail using hbox
  set T : ℝ := ∑ j : Fin 4, Mb j with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => (hMb j).le
  have hMbT : ∀ j, Mb j ≤ T := fun j =>
    Finset.single_le_sum (f := Mb) (fun i _ => (hMb i).le) (Finset.mem_univ j)
  
  obtain ⟨κ, hκ, hdet⟩ := exists_around_upper_of_field_bound A
  set R : ℝ := ‖A.center‖ + A.outerRadius with hRdef
  have hAR : A.toSet ⊆ closedBall (0 : ℂ) R := by
    intro x hx
    have hx' : dist x A.center < A.outerRadius := hx.1
    rw [mem_closedBall, dist_zero_right]
    have htri : ‖x‖ ≤ ‖x - A.center‖ + ‖A.center‖ := by
      simpa using norm_add_le (x - A.center) A.center
    rw [← dist_eq_norm] at htri
    linarith
  obtain ⟨Mf, hMf, hfield⟩ :=
    heat_compact_field_tail_Icc P h hh X hX 1 R one_pos A.toSet hAR η hη
  obtain ⟨c, C, hc, hC, hmb⟩ := heat_normalizer_bounds_Icc ξ m hm P h hh X hX 1 one_pos
  set U : ℝ := c⁻¹ * (Real.exp (|(ξ : ℝ)| * Mf) * κ) with hUdef
  have hU : 0 < U := by positivity
  refine ⟨max (4 * T + 1) U, lt_max_of_lt_left (by linarith), ?_⟩
  intro δ hδ1
  rcases hδ1.lt_or_eq with hlt | heq
  · 
    let e : Ioo (0 : ℝ) 1 := ⟨δ, δ.2, hlt⟩
    have hsub : {ω | ENNReal.ofReal (max (4 * T + 1) U) <
        aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A} ⊆
        ⋃ j : Fin 4, {ω | ENNReal.ofReal (Mb j) < ENNReal.ofReal ((m δ : ℝ))⁻¹ *
          crossLenIn (ξ : ℝ) (X δ ω) (Strong.cfgOpens A j : Set ℂ) {z j} {w j}} := by
      intro ω hω
      by_contra hnot
      simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hnot
      have hle := aroundDist_lfppMetric_le_of_four (ξ : ℝ) (m δ) (X δ ω) A z w hz hw T hT0
        (fun j => (hnot j).trans (ENNReal.ofReal_le_ofReal (hMbT j)))
      exact absurd (lt_of_lt_of_le hω hle)
        (not_lt.2 (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    calc _ ≤ P (⋃ j : Fin 4, {ω | ENNReal.ofReal (Mb j) < ENNReal.ofReal ((m δ : ℝ))⁻¹ *
          crossLenIn (ξ : ℝ) (X δ ω) (Strong.cfgOpens A j : Set ℂ) {z j} {w j}}) :=
          measure_mono hsub
      _ ≤ ∑ j : Fin 4, P {ω | ENNReal.ofReal (Mb j) < ENNReal.ofReal ((m δ : ℝ))⁻¹ *
          crossLenIn (ξ : ℝ) (X δ ω) (Strong.cfgOpens A j : Set ℂ) {z j} {w j}} :=
          measure_iUnion_fintype_le P _
      _ ≤ ∑ _j : Fin 4, ENNReal.ofReal (η / 4) :=
          Finset.sum_le_sum fun j _ => hbtail j e
      _ = ENNReal.ofReal η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_ofNat, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  · 
    have hδ1' : (1 : ℝ) ≤ δ := heq.ge
    refine le_trans (measure_mono ?_) (hfield δ hδ1' hδ1)
    intro ω hω
    by_contra hbad
    simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hbad
    have hup := hdet (ξ : ℝ) (m δ) (X δ ω) Mf hbad
    have hmδ : ((m δ : ℝ))⁻¹ ≤ c⁻¹ := (inv_le_inv₀ (m δ).2 hc).2 (hmb δ hδ1' hδ1).1
    have hle : ENNReal.ofReal (((m δ : ℝ))⁻¹ * (Real.exp (|(ξ : ℝ)| * Mf) * κ)) ≤
        ENNReal.ofReal (max (4 * T + 1) U) :=
      ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hmδ (by positivity)).trans
        (le_max_right _ _))
    exact absurd (lt_of_lt_of_le hω (hup.trans hle)) (lt_irrefl _)

 


theorem plHeatAnnulusTight_of_inputs (hPerc : Iface.DG20PercEstimate')
    (hS4 : Iface.DG20Section4) : PLHeatAnnulusTight := by
  intro ξ Q hQ m hm Ω _ P _ h hh X hX A
  refine ⟨fun δ _ => ⟨aemeasurable_acrossDist_lfppMetric_heat P h hh (ξ : ℝ) (m δ) δ (X δ)
    (hX δ) A, aemeasurable_aroundDist_lfppMetric_heat P h hh (ξ : ℝ) (m δ) δ (X δ) (hX δ) A⟩,
    ?_⟩
  intro η hη
  obtain ⟨Ma, hMa, hacr⟩ := heat_across_lower_tail_of_perc hPerc ξ m hm P h hh X hX A η hη
  obtain ⟨Mb, hMb, haro⟩ :=
    heat_around_upper_tail_of_section4 hS4 ξ Q hQ m hm P h hh X hX A η hη
  refine ⟨max Ma Mb, lt_max_of_lt_left hMa, fun δ hδ => ⟨?_, ?_⟩⟩
  · refine le_trans (measure_mono fun ω hω => ?_) (hacr δ hδ)
    exact lt_of_lt_of_le hω (ENNReal.ofReal_le_ofReal
      ((inv_le_inv₀ (lt_max_of_lt_left hMa) hMa).2 (le_max_left _ _)))
  · refine le_trans (measure_mono fun ω hω => ?_) (haro δ hδ)
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_max_right _ _)) hω

end SupercriticalLQGUniqueness.B2.Polylog
