/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S6.Prop61Step1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.GeodSelN
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.Prop61Det
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.GLowLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics

/-!
# GM Proposition 6.1, Step 1 (task P2-DEC74)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Prop 6.1, Step 1, l. 3588–3599 (display (6.1) `eqn-away-from-max-times`).

`gm_P6_1Step1`: `P6_1Step1` from GM Theorem 4.2 (`T4_2`, conclusion as corrected in D74) and
GM Proposition 4.3 (`P4_3`, with the a.s.-geodesic-selector hypothesis of D74), following GM:
apply Theorem 4.2 to the objects of Proposition 4.3 with `ρ⁻¹𝕣` in place of `𝕣`, `U = B_2(0)`,
`ℓ = ρβ̄`; the pair `(z, r)` given by Theorem 4.2 has `𝕫, 𝕨 ∉ B_{λ₄r}(z)`, so Proposition 4.3
gives the times `s < t` with `|P(s) − P(t)| ≥ b r ≥ b ε^{1+ν} ρ⁻¹ 𝕣`.
* The selector is `geodSelN` (D79 (4), `GeodSelN.lean`): measurable, invariant under additive
  constants, and for each pair `a ≠ b` a.s. the `D_h`-geodesic (MQ Theorem 1.2,
  `MQThm1_2Weak`); only the countably many grid pairs are used. (Before D79: a choice of geodesic,
  `geodChoice`, which is neither measurable nor invariant.)
* GM's single-GFF hypothesis `P[G̲_𝕣(c'', β)] ≥ β` is transferred to every whole-plane GFF by
  `prob_GLow_eq` (GM treat it as a number, l. 3572).
* Parameters (GM l. 3584): `ν = ν_*`, `μ = ν_*/2` (so T4.2 is used with `μ/2 = ν_*/4`, DV-B3),
  `c₁' = c_* + (C_* − c_*)/3`, `c₂' = c_* + 2(C_* − c_*)/3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM Prop 6.1, Step 1** (display (6.1), l. 3588–3599) from GM Theorem 4.2 and
Proposition 4.3 (statements as in D74, D79), with the selector `geodSelN` of D79 (4)
(`exists_geodSelN`: measurable, invariant under additive constants, a.s. the geodesic, by MQ
Theorem 1.2). -/
theorem gm_P6_1Step1 (hT : T4_2) (hP43 : P4_3) (hMQ : MQThm1_2Weak) : P6_1Step1 := by
  intro γ D D' c cs Cs hPS hRat hlt
  have hγ := hPS.1; have hγ2 := hPS.2.1; have hD := hPS.2.2.1
  obtain ⟨sel, hinv, hmeas, hselae⟩ := exists_geodSelN hMQ hγ hγ2 hD
  obtain ⟨νs, hνs, hT1⟩ := hT hγ hγ2 hD sel hinv
  have hν0 : 0 < νs := hνs.1
  obtain ⟨𝕡, h𝕡, hT2⟩ := hT1 (μ := νs / 2 / 2) (ν := νs) (by positivity) (by linarith) le_rfl
    ![1 / 4, 2, 3, 4, 5] (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨b, ρ, hb, hρ, c'', hc'', hP2⟩ := hP43 hPS hRat hlt sel
    (fun P _ h hh a b hab => hselae P h hh a b hab) hinv hmeas
    νs (νs / 2) νs (cs + (Cs - cs) / 3) (cs + 2 * (Cs - cs) / 3) (by positivity)
    (by linarith) le_rfl hνs.2 (by linarith) (by linarith) (by linarith) 𝕡 h𝕡
  refine ⟨c'', cs + 2 * (Cs - cs) / 3, b, ρ, νs, hc'', by linarith, hb, hρ, hν0, ?_⟩
  intro β hβ βb hβb q hq η hη
  obtain ⟨ε₀, Λ, hε₀, -, hP3⟩ := hP2 β hβ
  have hρ0 : 0 < ρ := hρ.1
  obtain ⟨ε₁, hε₁, hT3⟩ := hT2 q (ρ * βb) (Metric.ball (0 : ℂ) 2) hq
    ⟨mul_pos hρ0 hβb.1, by nlinarith [hρ.2, hβb.2, hβb.1]⟩ Metric.isOpen_ball
    Metric.isBounded_ball ε₀ Λ η hε₀.1 hη
  refine ⟨ε₁, hε₁, ?_⟩
  intro R hR Ω _ P _ h hh hG ε hε
  have hGall : ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (h' : Ω' → DistC), IsWholePlaneGFF h' P' →
      ENNReal.ofReal β ≤ P' (h' ⁻¹' GLow D D' R c'' β) := by
    intro Ω' _ P' _ h' hh'
    rw [prob_GLow_eq hPS R c'' β P' h' hh' P h hh]
    exact hG
  obtain ⟨Rad, E, Ef, hGeo, hcon⟩ := hP3 R hR hGall
  have hR' : 0 < ρ⁻¹ * R := by positivity
  have hbound := hT3 (ρ⁻¹ * R) Rad E Ef hR' hGeo P h hh ε hε
  set T4 := {ω | ∀ a b : ℂ, (∃ m : ℤ × ℤ, a = ((ε ^ q * (ρ⁻¹ * R) : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      (∃ m : ℤ × ℤ, b = ((ε ^ q * (ρ⁻¹ * R) : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      a ∈ (fun x => ((ρ⁻¹ * R : ℝ) : ℂ) * x) '' Metric.ball (0 : ℂ) 2 →
      b ∈ (fun x => ((ρ⁻¹ * R : ℝ) : ℂ) * x) '' Metric.ball (0 : ℂ) 2 →
      ρ * βb * (ρ⁻¹ * R) ≤ ‖a - b‖ →
      ∃ z : ℂ, ∃ r ∈ Rad, r ∈ Icc (ε ^ (1 + νs) * (ρ⁻¹ * R)) (ε * (ρ⁻¹ * R)) ∧
        (range (sel a b (h ω)) ∩ Metric.ball z ((![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 1 * r)).Nonempty ∧
        h ω ∈ Ef r z a b ∧ a ∉ Metric.ball z ((![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 3 * r) ∧
        b ∉ Metric.ball z ((![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 3 * r)} with hT4
  set gp : ℤ × ℤ → ℂ := fun m => ((ε ^ q * (ρ⁻¹ * R) : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)
    with hgp
  set G := {ω | ∀ m m' : ℤ × ℤ, gp m ≠ gp m' →
    IsGeod01 (D (h ω)) (gp m) (gp m') (sel (gp m) (gp m') (h ω))} with hG_def
  have hGnull : P Gᶜ = 0 := by
    refine ae_iff.1 (ae_all_iff.2 fun m => ae_all_iff.2 fun m' => ?_)
    by_cases hmm : gp m = gp m'
    · exact Eventually.of_forall fun _ h' => absurd hmm h'
    · exact (hselae P h hh _ _ hmm).mono fun _ hω _ => hω
  -- grid and window conversions
  have hgrid : ∀ a : ℂ, a ∈ gridPts (ε ^ q * ρ⁻¹ * R) →
      ∃ m : ℤ × ℤ, a = ((ε ^ q * (ρ⁻¹ * R) : ℝ) : ℂ) * (m.1 + m.2 * Complex.I) := by
    rintro a ⟨m, hm⟩
    exact ⟨m, by rw [hm, mul_assoc (ε ^ q)]⟩
  have hwin : ∀ a : ℂ, a ∈ Metric.ball (0 : ℂ) (2 * R) →
      a ∈ (fun x => ((ρ⁻¹ * R : ℝ) : ℂ) * x) '' Metric.ball (0 : ℂ) 2 := by
    intro a ha
    have hc : ((ρ⁻¹ * R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR'.ne'
    refine ⟨a / ((ρ⁻¹ * R : ℝ) : ℂ), ?_, by simp only; rw [mul_div_cancel₀ _ hc]⟩
    rw [Metric.mem_ball, dist_zero_right] at ha ⊢
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR'.le, div_lt_iff₀ hR']
    calc ‖a‖ < 2 * R := ha
      _ ≤ 2 * (ρ⁻¹ * R) := by
        have : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ0 |>.2 hρ.2.le
        nlinarith
  have hsub : (T4 ∩ G) ⊆ {ω | ∀ a a' : ℂ, a ∈ gridPts (ε ^ q * ρ⁻¹ * R) →
      a' ∈ gridPts (ε ^ q * ρ⁻¹ * R) →
      a ∈ Metric.ball (0 : ℂ) (2 * R) → a' ∈ Metric.ball (0 : ℂ) (2 * R) → βb * R ≤ ‖a - a'‖ →
      ∃ P' : C(unitInterval, ℂ), IsGeod01 (D (h ω)) a a' P' ∧ ∃ s t : unitInterval, s < t ∧
        b * ε ^ (1 + νs) * ρ⁻¹ * R ≤ ‖P' s - P' t‖ ∧
        (D' (h ω)).1 (P' s, P' t) ≤ (cs + 2 * (Cs - cs) / 3) * (D (h ω)).1 (P' s, P' t)} := by
    rintro ω ⟨hω4, hωG⟩ a a' ha ha' hab hab' hdist
    have hl : ρ * βb * (ρ⁻¹ * R) ≤ ‖a - a'‖ := by
      rw [show ρ * βb * (ρ⁻¹ * R) = βb * R by field_simp]; exact hdist
    obtain ⟨z, r, hrR, hrI, -, hEf, haz, ha'z⟩ :=
      hω4 a a' (hgrid a ha) (hgrid a' ha') (hwin a hab) (hwin a' hab') hl
    have h3 : (![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 3 = 4 := rfl
    rw [h3] at haz ha'z
    obtain ⟨s, t, hst, -, -, hbr, hrat⟩ := hcon z r hrR a a' haz ha'z (h ω) hEf
    have hne : a ≠ a' := by
      intro he
      rw [he, sub_self, norm_zero] at hdist
      nlinarith [hβb.1]
    have hg : IsGeod01 (D (h ω)) a a' (sel a a' (h ω)) := by
      obtain ⟨m, hm⟩ := hgrid a ha
      obtain ⟨m', hm'⟩ := hgrid a' ha'
      subst hm hm'
      exact hωG m m' hne
    refine ⟨sel a a' (h ω), hg, s, t, hst, ?_, hrat⟩
    calc b * ε ^ (1 + νs) * ρ⁻¹ * R = b * (ε ^ (1 + νs) * (ρ⁻¹ * R)) := by ring
      _ ≤ b * r := mul_le_mul_of_nonneg_left hrI.1 hb.1.le
      _ ≤ _ := hbr
  calc P _ ≤ P (T4ᶜ ∪ Gᶜ) := by
        apply measure_mono
        intro ω hω
        by_contra hc
        simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hc
        exact hω (hsub ⟨hc.1, hc.2⟩)
    _ ≤ P T4ᶜ + P Gᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal η := by rw [hGnull, add_zero]; exact hbound

end LQGMetric.GM
