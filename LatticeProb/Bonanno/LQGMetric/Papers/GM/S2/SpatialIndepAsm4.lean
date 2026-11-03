/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepAsm4 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm3

/-!
# GM Lemma 2.7, assembly: `P[𝔐_z > A] ≤ ε` uniformly (GM l. 984–988)

Source: GM arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, l. 984–988:
"we can find `A > 0` (depending only on `s`, `p`, `q`) such that `P[𝔐_z ≤ A] ≥ 1 − ε` for each
`z`". `prob_not_goodD_le` covers the complement of the good set by the three events of
`pointwise_bad`; `exists_good_const` chooses `A` so that each has probability `≤ ε`
(`prob_oscEv_le`, `exists_offset_bound`, `prob_zbPair_ge_le`), uniformly in `z` and the field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric InnerProductSpace

namespace LQGMetric.GM

open Blueprint

theorem prob_not_goodD_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h' hh hz G : Ω → DistC} {U : Opens ℂ}
    (hdec : ∀ ω, h' ω = hh ω + hz ω) (hhG : hh =ᵐ[P] G)
    (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictTo U (hh ω) φ = ∫ x, g x * φ x)
    {x : ℂ} {R ρ₂ δ A : ℝ} (hδ : 0 < δ) (hBU : ball x R ⊆ U) (hρδ : ρ₂ * R + δ < R)
    (hρ : 0 ≤ ρ₂ * R) (S : Set ℂ) :
    P {ω | ¬ goodD δ hδ.le S x (ρ₂ * R) A (addConst (G ω) (-circleAvg (h' ω) R x))} ≤
      P (oscEv G x R ρ₂ (A / 2)) + P {ω | A / 4 < |offsetFun hδ.le R x (h' ω)|} +
        P {ω | A * (∫ y, radProf δ y) / 4 ≤ |hz ω (radBump δ hδ.le x)|} := by
  have hBU' : ballO x R ≤ U := fun y hy => hBU hy
  refine (measure_mono_ae ?_).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl))
  filter_upwards [hhG, hharm] with ω hω hωh hbad
  obtain ⟨g, hg, hrep⟩ := hωh
  rw [hω] at hrep
  have hdec' : h' ω = G ω + hz ω := by rw [hdec, hω]
  rcases pointwise_bad hg hrep hdec' hδ hBU hρδ hρ hbad with ⟨u, hu, hlt⟩ | h | h
  · exact Or.inl (Or.inl ⟨g, hg.mono hBU, rep_mono hBU' hrep, u, hu, hlt⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- the choice of `A` (GM l. 984–988), uniform in the centre and the field -/
theorem exists_good_const {δ R ρ₂ ε : ℝ} (hδ : 0 < δ) (hδR : δ < R) (hρ₂ : ρ₂ < 1)
    (hR : 0 < R) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      (∀ z : ℂ, volume (closedBall z (ρ₂ * R + (1 - ρ₂) * R / 3)) *
        ENNReal.ofReal (√(radK ((1 - ρ₂) * R / 3) (ρ₂ * R + (1 - ρ₂) * R / 3))) /
        ENNReal.ofReal (A / 2 / oscC ((1 - ρ₂) * R / 3)) ≤ ENNReal.ofReal ε) ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P → ∀ z : ℂ,
          P {ω | A / 4 < |offsetFun hδ.le R z (h ω)|} ≤ ENNReal.ofReal ε) ∧
      zbVar hδ hδR / (A * (∫ y, radProf δ y) / 4) ^ 2 ≤ ε := by
  obtain ⟨A₀, hA₀, hoff⟩ := exists_offset_bound hδ hR hε
  set δ' := (1 - ρ₂) * R / 3 with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ']; have := mul_pos (sub_pos.2 hρ₂) hR; linarith
  set r₀ := ρ₂ * R + δ'
  set X : ENNReal := volume (closedBall (0 : ℂ) r₀) * ENNReal.ofReal (√(radK δ' r₀))
  have hX : X ≠ ⊤ := ENNReal.mul_ne_top measure_closedBall_lt_top.ne ENNReal.ofReal_ne_top
  have hI' := integral_radProf_pos hδ'0
  have hC : 0 < oscC δ' := by
    unfold oscC
    exact div_pos (div_pos (expNegInvGlue.pos_of_pos (by positivity)) hI') hI'
  have hI := integral_radProf_pos hδ
  set zv := zbVar hδ hδR
  set I := ∫ y, radProf δ y
  have hX0 : 0 ≤ X.toReal := ENNReal.toReal_nonneg
  set A := 4 * A₀ + 2 * oscC δ' * (X.toReal / ε) + 4 * (1 + |zv| / ε) / I + 1 with hAdef
  have hXε : 0 ≤ X.toReal / ε := div_nonneg hX0 hε.le
  have hzε : 0 ≤ 4 * (1 + |zv| / ε) / I := by positivity
  have hCX : 0 ≤ 2 * oscC δ' * (X.toReal / ε) := by positivity
  refine ⟨A, by linarith, fun z => ?_, @fun Ω _ P _ h hh z => ?_, ?_⟩
  · rw [Measure.addHaar_closedBall_center volume z r₀]
    refine ENNReal.div_le_of_le_mul ?_
    show X ≤ _
    rw [← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_toReal hX]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : X.toReal / ε ≤ A / 2 / oscC δ' := by
      rw [le_div_iff₀ hC]
      have : X.toReal / ε * oscC δ' = 2 * oscC δ' * (X.toReal / ε) / 2 := by ring
      rw [this]; linarith
    rw [div_le_iff₀ hε] at h1
    linarith
  · refine (measure_mono fun ω hω => ?_).trans (hoff P h hh z)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  · have ht : 1 + |zv| / ε ≤ A * I / 4 := by
      have h1 : 4 * (1 + |zv| / ε) / I ≤ A := by linarith
      rw [div_le_iff₀ hI] at h1
      linarith
    have ht1 : 1 ≤ A * I / 4 := by linarith [div_nonneg (abs_nonneg zv) hε.le]
    have ht2 : A * I / 4 ≤ (A * I / 4) ^ 2 := by nlinarith
    have hzv : |zv| ≤ ε * (A * I / 4) := by
      have := (div_le_iff₀' hε).1 (show |zv| / ε ≤ A * I / 4 by linarith)
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [le_abs_self zv]

end LQGMetric.GM
