/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteLowerTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteCoverGeom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusTranslatedSmallLower

 



set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem dg20_heat_across_small_lower_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (A : EuclideanAnnulus)
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | acrossDist
          (PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
            (m ⟨ε, ε.property.1⟩) (X ⟨ε, ε.property.1⟩ ω)) A <
            ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η := by
  obtain ⟨d, q, hd, hd2, hqFin, hqNe, hcover⟩ :=
    exists_across_finite_cover A
  letI : Fintype q := hqFin.fintype
  have hqUniv : (Finset.univ : Finset q).Nonempty := by
    obtain ⟨z, hz⟩ := hqNe
    exact ⟨⟨z, hz⟩, Finset.mem_univ _⟩
  let δ : ℝ := η / ((Fintype.card q : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hEach (z : q) :
      ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
        ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
          P {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn (ξ : ℝ) (X ⟨ε, ε.property.1⟩ ω)
              (closedBall z.1 d) (sphere z.1 (d / 16))
              (sphere z.1 (3 * d / 4)) < ENNReal.ofReal T⁻¹} ≤
            ENNReal.ofReal δ :=
    SupercriticalLQGUniqueness.B2.DG20Pt.dg20_heat_annulus_translated_small_lower_of_perc
      hPerc ξ m hm P h hh X hX z.1 d hd hd2 δ hδ
  choose Tz εz hTz hεz htail using hEach
  let Tmax : ℝ := (Finset.univ : Finset q).sup' hqUniv Tz
  let T : ℝ := Tmax + 1
  have hT : 0 < T := by
    obtain ⟨z, hz⟩ := hqNe
    have hle : Tz ⟨z, hz⟩ ≤ Tmax :=
      Finset.le_sup' Tz (Finset.mem_univ ⟨z, hz⟩)
    dsimp [T]
    linarith [hTz ⟨z, hz⟩]
  let ε₀ : ℝ := (Finset.univ : Finset q).inf' hqUniv εz
  have hε₀ : 0 < ε₀ :=
    (Finset.lt_inf'_iff hqUniv).2 (fun z _ => hεz z)
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro ε hε
  let e : Ioi (0 : ℝ) := ⟨ε, ε.property.1⟩
  let C : Ω → ℝ≥0∞ := fun ω =>
    acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m e) (X e ω)) A
  let B : q → Ω → ℝ≥0∞ := fun z ω =>
    ENNReal.ofReal (m e : ℝ)⁻¹ *
      crossLenIn (ξ : ℝ) (X e ω)
        (closedBall z.1 d) (sphere z.1 (d / 16))
        (sphere z.1 (3 * d / 4))
  have hTzT (z : q) : Tz z ≤ T := by
    have hz : Tz z ≤ Tmax :=
      Finset.le_sup' Tz (Finset.mem_univ z)
    dsimp [T]
    linarith
  have hInv (z : q) : ENNReal.ofReal T⁻¹ ≤ ENNReal.ofReal (Tz z)⁻¹ := by
    apply ENNReal.ofReal_le_ofReal
    exact (inv_le_inv₀ hT (hTz z)).2 (hTzT z)
  have hProb (z : q) :
      P {ω | B z ω < ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal δ := by
    have hεz' : (ε : ℝ) < εz z :=
      lt_of_lt_of_le hε (Finset.inf'_le εz (Finset.mem_univ z))
    calc
      P {ω | B z ω < ENNReal.ofReal T⁻¹} ≤
        P {ω | B z ω < ENNReal.ofReal (Tz z)⁻¹} := by
          apply measure_mono
          intro ω hω
          exact lt_of_lt_of_le hω (hInv z)
      _ ≤ ENNReal.ofReal δ := by
        simpa only [B, e] using htail z ε hεz'
  have hSub : {ω | C ω < ENNReal.ofReal T⁻¹} ⊆
      ⋃ z : q, {ω | B z ω < ENNReal.ofReal T⁻¹} := by
    intro ω hω
    obtain ⟨z, hz, hbound⟩ := exists_finite_cross_below_across A d hd q hcover
      (ξ : ℝ) (m e) (X e ω)
    let zq : q := ⟨z, hz⟩
    exact mem_iUnion.mpr ⟨zq, lt_of_le_of_lt hbound hω⟩
  calc
    P {ω | C ω < ENNReal.ofReal T⁻¹} ≤
      P (⋃ z : q, {ω | B z ω < ENNReal.ofReal T⁻¹}) := measure_mono hSub
    _ ≤ ∑ z : q, P {ω | B z ω < ENNReal.ofReal T⁻¹} := by
      simpa only using (measure_iUnion_fintype_le P
        (fun z : q => {ω | B z ω < ENNReal.ofReal T⁻¹}))
    _ ≤ ∑ _z : q, ENNReal.ofReal δ :=
      Finset.sum_le_sum (fun z _ => hProb z)
    _ ≤ ENNReal.ofReal η := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [δ]
      have hc : 0 ≤ (Fintype.card q : ℝ) := Nat.cast_nonneg _
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (by linarith : 0 < (Fintype.card q : ℝ) + 1)).2
        (by nlinarith)

end SupercriticalLQGUniqueness.B2.PfeAxioms
