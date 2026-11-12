/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18S2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18S1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18T3

/-!
# DG:1774–1775: `DGProp3_18SqRef` from `R18Unit` by scaling (task P2-DG105s, P-118c step 4)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, DG:1774–1777 (scale and
translation invariance of the law of the whole-plane GFF modulo additive constant). See S3P18S1
for the affine map `A y = 2r y + c₀` and the LFPP comparison `s18_dgLFPP_scale`.

* **`dgProp3_18SqRef_of_unit : R18Unit → DGProp3_18SqRef`**: on a space carrying a normalized
  whole-plane GFF `h` with circle-average version `H`, apply `R18Unit` to `h(A ·) − h_R(c₀)` at
  `ζ/4`; `H_R(c₀) ≤ (ζ/4ξ) log δ⁻¹` off probability `≤ 2δ`; the constant `R^{1−e}` is absorbed by
  `t18_absorb`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint

/-- **DG:1774–1775, scaling step**: P3.22 in `𝕊(1)` coordinates for every normalized whole-plane
GFF (`R18Unit`) gives it on every square `t18Sq c r` for one reference process. -/
theorem dgProp3_18SqRef_of_unit (hU : R18Unit) : DGProp3_18SqRef := by
  intro γ hγ hγ2 c r hr ζ hζ
  obtain ⟨Ω, _, P, hP, h, hh⟩ := GFFExist.exists_normalizedWPGFF
  obtain ⟨H, hHG, -, hHae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh
  refine ⟨Ω, inferInstance, P, H, hHG, ?_⟩
  set R : ℝ := 2 * r with hRdef
  have hR : 0 < R := by positivity
  set c₀ := s18c0 c r
  have hh' := DFGPS.L36.isNormalizedWPGFF_rescale hh hR c₀
  obtain ⟨H', hH'G, -, hH'ae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh'
  obtain ⟨p, C, δ₁, hp, hδ₁, hb⟩ := hU γ hγ hγ2 hh' (fun ρ hρ ω => hH'G.continuous ρ hρ ω)
    hH'ae (ζ / 4) (by linarith [hζ.1])
  obtain ⟨v, hv, htail⟩ := s18_circleAvg_tail hh hR c₀
  set ξ := xiGamma γ with hξ
  have hξ0 : 0 < ξ := xiGamma_pos hγ
  have hζ0 : 0 < ζ := hζ.1
  set κ := ζ / (4 * ξ) with hκ
  have hκ0 : 0 < κ := by positivity
  set a₁ : ℝ := 1 / (8 * (v + 1)) with ha₁
  have ha₁0 : 0 < a₁ := by positivity
  set δ₂ := Real.exp (-(1 / (a₁ * (2 * κ) ^ 2))) with hδ₂
  set e := dgLambda γ - ζ / 4 with he
  set Ac := max (R ^ (1 - e)) 1 with hAc
  have hAc1 : 1 ≤ Ac := le_max_right _ _
  set δ₀ := min (R * δ₁) (min 1 (min δ₂ (Ac⁻¹ ^ (2 / ζ)))) with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by positivity) (lt_min one_pos
    (lt_min (Real.exp_pos _) (by positivity)))
  refine ⟨min p 1, |C| * R⁻¹ ^ p + 2, δ₀, lt_min hp one_pos, hδ₀0, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδR : δ / R < δ₁ := by
    rw [div_lt_iff₀ hR, mul_comm]; exact hδlt.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 := hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδδ₂ : δ < δ₂ :=
    hδlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδA : δ ≤ Ac⁻¹ ^ (2 / ζ) :=
    hδlt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set ρ := δ / R with hρ
  have hρ0 : 0 < ρ := by positivity
  have hRρ : R * ρ = δ := by rw [hρ]; field_simp
  set L := Real.log δ⁻¹ with hL
  have hLge : 1 / (a₁ * (2 * κ) ^ 2) ≤ L := by
    rw [hL, Real.log_inv, le_neg]
    have := Real.log_lt_log hδ0 hδδ₂
    rw [hδ₂, Real.log_exp] at this
    linarith
  have hL0 : 0 ≤ L := le_trans (by positivity) hLge
  -- the events
  set E₁ := {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
    dgLFPP ξ (fun x => H' ρ x ω) p18Half z w ≤ ρ ^ e} with hE₁
  set X : Ω → ℝ := fun ω => H R c₀ ω
  set E₂ := {ω | κ * L < |X ω|} with hE₂
  have hE₂le : P E₂ ≤ ENNReal.ofReal (2 * δ) := by
    have h1 : P E₂ = P {ω | 2 * κ * L / 2 < |circleAvg (h ω) R c₀|} := by
      refine measure_congr ?_
      filter_upwards [hHae R hR c₀] with ω hω
      simp only [eq_iff_iff]
      show κ * L < |H R c₀ ω| ↔ 2 * κ * L / 2 < |circleAvg (h ω) R c₀|
      rw [hω, show 2 * κ * L / 2 = κ * L by ring]
    rw [h1]
    refine (htail (2 * κ * L) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : Real.exp (-L) = δ := by rw [hL, Real.log_inv, neg_neg, Real.exp_log hδ0]
    have h3 := DG.r18_tail_le ha₁0 (by positivity : (0 : ℝ) < 2 * κ) hLge
    rw [h2] at h3
    linarith
  set N := {ω | ¬ ∀ x, H' ρ x ω = H (R * ρ) ((R : ℂ) * x + c₀) ω - H R c₀ ω} with hN
  have hN0 : P N = 0 := by
    have := DFGPS.L36.ae_rescale_eq hh hHG hHae hR c₀ hH'G hH'ae hρ0
    rw [ae_iff] at this
    exact this
  -- the deterministic bound on the good event
  have hkey : 2 * r * Real.exp (ξ * (κ * L)) * ρ ^ e ≤ δ ^ (dgLambda γ - ζ) := by
    have e1 : Real.exp (ξ * (κ * L)) = δ ^ (-(ζ / 4)) := by
      rw [Real.rpow_def_of_pos hδ0, hL, Real.log_inv]
      congr 1; rw [hκ]; field_simp
    have e2 : 2 * r * Real.exp (ξ * (κ * L)) * ρ ^ e = R ^ (1 - e) * δ ^ (dgLambda γ - ζ / 2) := by
      rw [e1, hρ, Real.div_rpow hδ0.le hR.le, Real.rpow_sub hR 1 e, Real.rpow_one, ← hRdef]
      have : δ ^ (dgLambda γ - ζ / 2) = δ ^ (-(ζ / 4)) * δ ^ e := by
        rw [← Real.rpow_add hδ0]; congr 1; rw [he]; ring
      rw [this]
      have : R ^ e ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
      field_simp
    rw [e2]
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ0.le _)).trans
      (t18_absorb hAc1 hζ0 hδ0 hδA)
  have hsub : {ω | ¬ ∀ z ∈ t18Sq c r, ∀ w ∈ t18Sq c r,
      dgLFPP ξ (fun x => H δ x ω) (t18Sq c (2 * r)) z w ≤ δ ^ (dgLambda γ - ζ)} ⊆
      E₁ ∪ E₂ ∪ N := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h1' : ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP ξ (fun x => H' ρ x ω) p18Half z w ≤ ρ ^ e := by
      by_contra hn; exact h1 hn
    have h2' : |X ω| ≤ κ * L := not_lt.1 h2
    have h3' : ∀ x, H' ρ x ω = H (R * ρ) ((R : ℂ) * x + c₀) ω - H R c₀ ω := by
      by_contra hn; exact h3 hn
    apply hω
    intro z hz w hw
    obtain ⟨z', hz', rfl⟩ := s18_A_surj hr hz
    obtain ⟨w', hw', rfl⟩ := s18_A_surj hr hw
    have hφ : ∀ x, H δ (((2 * r : ℝ) : ℂ) * x + s18c0 c r) ω = H' ρ x ω + X ω := fun x => by
      rw [h3' x, hRρ]; simp only [X, R, c₀]; ring
    have hD0 : 0 ≤ dgLFPP ξ (fun x => H' ρ x ω) p18Half z' w' :=
      Real.iInf_nonneg fun q => lfppLength_nonneg ξ _ q.1
    calc _ ≤ 2 * r * Real.exp (ξ * X ω) * dgLFPP ξ (fun x => H' ρ x ω) p18Half z' w' :=
          s18_dgLFPP_scale ξ hr hφ hz' hw'
      _ ≤ 2 * r * Real.exp (ξ * (κ * L)) * ρ ^ e := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2') hξ0.le)) (by positivity))
            (h1' z' hz' w' hw') hD0 (by positivity)
      _ ≤ _ := hkey
  -- the bound
  have hE₁le : P E₁ ≤ ENNReal.ofReal (C * ρ ^ p) := hb ρ ⟨hρ0, hδR⟩
  have hρp : C * ρ ^ p ≤ |C| * R⁻¹ ^ p * δ ^ p := by
    rw [hρ, div_eq_mul_inv, Real.mul_rpow hδ0.le (inv_nonneg.2 hR.le)]
    have : 0 ≤ δ ^ p * R⁻¹ ^ p := by positivity
    nlinarith [le_abs_self C]
  have hpow1 : δ ^ p ≤ δ ^ min p 1 :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have hpow2 : δ ≤ δ ^ min p 1 := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right p 1)
    rwa [Real.rpow_one] at this
  calc P _ ≤ P (E₁ ∪ E₂ ∪ N) := measure_mono hsub
    _ ≤ P E₁ + P E₂ + P N := (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ENNReal.ofReal (|C| * R⁻¹ ^ p * δ ^ p) + ENNReal.ofReal (2 * δ) + 0 := by
        rw [hN0]
        gcongr
        exact hE₁le.trans (ENNReal.ofReal_le_ofReal hρp)
    _ ≤ ENNReal.ofReal ((|C| * R⁻¹ ^ p + 2) * δ ^ min p 1) := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ |C| * R⁻¹ ^ p := by positivity
        have := mul_le_mul_of_nonneg_left hpow1 h0
        nlinarith

end LQGMetric.DG
