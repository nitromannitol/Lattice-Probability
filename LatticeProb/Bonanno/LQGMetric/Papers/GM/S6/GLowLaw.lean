/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S6.GLowLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.GoodRadiiLaw

/-!
# Law invariance of `P[G̲_r(c', β)]` (task P2-M2O, input of GM Proposition 6.1)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
GM Prop 6.1 (l. 3570–3574) has the hypothesis `P[G̲_𝕣(c'', β)] ≥ β` for "the" whole-plane GFF `h`;
`GM.P4_3` states it for every whole-plane GFF. GM treat `P[G̲_𝕣]` as a deterministic number
(the GFF is defined modulo additive constant, and `G̲_𝕣` is invariant under adding constants by
Weyl scaling); `prob_GLow_eq` proves this, exactly as `prob_attainedLow_eq` (S5/GoodRadiiLaw)
does for `attainedLow`: `G̲_r` is universally measurable (projection of a Borel set) and
invariant under `h ↦ h + a` (`IsWeakLQGMetric.ae_dist_addConst`), so
`prob_eq_of_ae_addConst_iff_um` applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `G̲_r(c', β)` is universally measurable (projection of a Borel set) -/
theorem uMeasurableSet_GLow {D D' : DistC → ContMetric} (hD : Measurable D)
    (hD' : Measurable D') (r c' β : ℝ) : UMeasurableSet (GLow D D' r c' β) := by
  let T := DistC × (ℂ × ℂ)
  have m1 : Measurable fun p : T => (p.2.1, p.2.2) := measurable_snd
  have hS1 : MeasurableSet {p : T | p.2.1 ∈ ball (0 : ℂ) r} :=
    isOpen_ball.measurableSet.preimage measurable_snd.fst
  have hS2 : MeasurableSet {p : T | p.2.2 ∈ ball (0 : ℂ) r} :=
    isOpen_ball.measurableSet.preimage measurable_snd.snd
  have hS3 : MeasurableSet {p : T | β * r ≤ ‖p.2.1 - p.2.2‖} :=
    measurableSet_le measurable_const (measurable_snd.fst.sub measurable_snd.snd).norm
  have fD : ∀ E : DistC → ContMetric, Measurable E →
      Measurable fun p : T => (E p.1).1 (p.2.1, p.2.2) := fun E hE =>
    continuous_contMetric_apply.measurable.comp ((hE.comp measurable_fst).prodMk m1)
  have hR : MeasurableSet {p : T | (D' p.1).1 (p.2.1, p.2.2) ≤ c' * (D p.1).1 (p.2.1, p.2.2)} :=
    measurableSet_le (fD D' hD') ((fD D hD).const_mul c')
  have hS := hS1.inter (hS2.inter (hS3.inter hR))
  convert UMeasurableSet.setOf_exists hS using 1
  ext g
  simp only [GLow, mem_ofPred_eq, mem_inter_iff, Prod.exists]
  constructor
  · rintro ⟨u, hu, v, hv, h1, h2⟩
    exact ⟨u, v, hu, hv, h1, h2⟩
  · rintro ⟨u, v, hu, hv, h1, h2⟩
    exact ⟨u, hu, v, hv, h1, h2⟩

/-- `G̲_r` is invariant under scaling `D_g` and `D̃_g` by a common factor -/
theorem mem_GLow_of_scale {D D' : DistC → ContMetric} {r c' β : ℝ} {g₁ g₂ : DistC}
    {e : ℝ} (he : 0 < e) (h : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h' : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ GLow D D' r c' β ↔ g₁ ∈ GLow D D' r c' β := by
  have hr : ∀ u v, (D' g₂).1 (u, v) ≤ c' * (D g₂).1 (u, v) ↔
      (D' g₁).1 (u, v) ≤ c' * (D g₁).1 (u, v) := fun u v => by
    rw [h, h', show c' * (e * (D g₁).1 (u, v)) = e * (c' * (D g₁).1 (u, v)) by ring]
    exact mul_le_mul_iff_right₀ he
  simp only [GLow, mem_ofPred_eq, hr]

/-- **`P[G̲_r(c', β)]` does not depend on the whole-plane GFF** (GM treat it as a number,
l. 3572; GFF modulo additive constant + Weyl scaling) -/
theorem prob_GLow_eq {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}
    (hPS : PairSetting γ D D' c) (r c' β : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : IsWholePlaneGFF h' P') :
    P (h ⁻¹' GLow D D' r c' β) = P' (h' ⁻¹' GLow D D' r c' β) := by
  obtain ⟨-, -, hD, hD'⟩ := hPS
  have key : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P →
      ∀ᵐ ω ∂P, ∀ a : ℝ, addConst (h ω) a ∈ GLow D D' r c' β ↔ h ω ∈ GLow D D' r c' β := by
    intro Ω _ P _ h hh
    have hgp := Tight.isGFFPlusCont_of_wp hh
    filter_upwards [hD.ae_dist_addConst hgp, hD'.ae_dist_addConst hgp] with ω h1 h2 a
    exact mem_GLow_of_scale (Real.exp_pos _) (h1 a) (h2 a)
  exact prob_eq_of_ae_addConst_iff_um hh hh'
    (uMeasurableSet_GLow hD.measurable hD'.measurable r c' β) (key P h hh) (key P' h' hh')

end LQGMetric.GM
