/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepAsm5 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm4
import LatticeProb.Bonanno.LQGMetric.Blueprint.MQGeodesic

/-!
# GM Lemma 2.7, assembly: the Radon–Nikodym bounds on the good event (GM l. 989–998)

Source: GM arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, l. 989–998
("on `{𝔐_z ≤ A}`, by [MQ, Lemma 4.1] … the conditional law of `(h − h_{1+s}(z))|_{B_1(z)}` given
`h|_{ℂ∖U}` is mutually absolutely continuous w.r.t. the law of a zero-boundary GFF … with
Radon–Nikodym derivative having finite second moment") and MQ arXiv:1812.03913 Lemma 4.1 with
Remark 4.2 (l. 549–610). `MQSpec` is the conclusion of `Blueprint.MQLem4_1Gen` for fixed
`ρ₁, ρ₂, M` and `p = 2`; `rn_bounds_of_rep` applies it to a frozen harmonic part `T` (`= 𝔥 − a`
on `B(x,R)`, bounded by `M` on `B(x, ρ₂R)`) and turns the two moment bounds into the two
probability bounds of `rn_pair_bounds`, for the shifted event `{h̊|_{B_1} + T|_{B_1} ∈ S}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric InnerProductSpace

namespace LQGMetric.GM

open Blueprint

/-- the conclusion of `Blueprint.MQLem4_1Gen` for fixed `ρ₁, ρ₂, M` and `p = 2` -/
def MQSpec (ρ₁ ρ₂ M c : ℝ) : Prop :=
  ∀ (z : ℂ) (r : ℝ), 0 < r →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ht : Ω → DistC),
      Measurable ht → IsZeroBoundaryGFF (ballO z r) (fun ω => restrictTo (ballO z r) (ht ω)) P →
    ∀ (g : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd g (Metric.ball z r) → ∀ a : ℝ,
      (∀ w ∈ Metric.ball z (ρ₂ * r), |g w - a| ≤ M) →
    ∀ G : DistC, (∀ φ : TestOn (ballO z r),
        restrictTo (ballO z r) G φ = ∫ x, (g x - a) * φ x) →
      let μ₀ : Measure (DistOn (ballO z (ρ₁ * r))) :=
        P.map fun ω => restrictTo (ballO z (ρ₁ * r)) (ht ω)
      let μg : Measure (DistOn (ballO z (ρ₁ * r))) :=
        P.map fun ω => restrictTo (ballO z (ρ₁ * r)) (ht ω + G)
      μg ≪ μ₀ ∧ μ₀ ≪ μg ∧
        ∫⁻ x, (μg.rnDeriv μ₀ x) ^ (2 : ℝ) ∂μ₀ ≤ ENNReal.ofReal c ∧
        ∫⁻ x, (μ₀.rnDeriv μg x) ^ (2 : ℝ) ∂μg ≤ ENNReal.ofReal c

theorem exists_MQSpec (hMQ : MQLem4_1Gen) {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (h2 : ρ₁ < ρ₂) (h3 : ρ₂ < 1)
    {M : ℝ} (hM : 0 < M) : ∃ c : ℝ, 0 < c ∧ MQSpec ρ₁ ρ₂ M c :=
  hMQ ρ₁ ρ₂ h1 h2 h3 M hM 2

lemma measurable_addConst_pi {α : Type*} [MeasurableSpace α] {ι : Type*} {G : α → DistC}
    {c : ι → α → ℝ} (hG : Measurable G) (hc : ∀ i, Measurable (c i)) :
    Measurable fun ω i => addConst (G ω) (c i ω) := by
  refine measurable_pi_iff.2 fun i => measurable_distOn_iff.2 fun φ => ?_
  simp only [GFFInv.addConst_apply]
  exact ((measurable_distOn_apply φ).comp hG).add ((hc i).const_mul _)

lemma addConst_add_left (G hz : DistC) (c : ℝ) : addConst (G + hz) c = hz + addConst G c := by
  unfold addConst addFun
  abel

/-- **GM l. 996–998 via MQ Lemma 4.1 + Remark 4.2**: for a frozen harmonic part `T` satisfying the
hypotheses of MQ Lemma 4.1, the shifted probability `μ₀{b + T|_{B_1} ∈ S}` and `μ₀(S)` control
each other. -/
theorem rn_bounds_of_rep {ρ₁ ρ₂ M c : ℝ} (hc : MQSpec ρ₁ ρ₂ M c) {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hρ₁R : ρ₁ * R = 1) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ht hz : Ω → DistC} (htm : Measurable ht) (hthz : ∀ᵐ ω ∂P, ht ω = hz ω)
    (hzb : IsZeroBoundaryGFF (ballO x R) (fun ω => restrictTo (ballO x R) (hz ω)) P)
    {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball x R)) {a0 : ℝ}
    (hb : ∀ w ∈ ball x (ρ₂ * R), |g w - a0| ≤ M) {T : DistC}
    (hT : ∀ φ : TestOn (ballO x R), restrictTo (ballO x R) T φ = ∫ y, (g y - a0) * φ y)
    {S : Set (DistOn (ballO x 1))} (hS : MeasurableSet S) :
    (P.map fun ω => restrictTo (ballO x 1) (hz ω)) {b | b + restrictTo (ballO x 1) T ∈ S} ^ 2 ≤
        ENNReal.ofReal c * (P.map fun ω => restrictTo (ballO x 1) (hz ω)) S ∧
      (P.map fun ω => restrictTo (ballO x 1) (hz ω)) S ^ 2 ≤
        ENNReal.ofReal c *
          (P.map fun ω => restrictTo (ballO x 1) (hz ω)) {b | b + restrictTo (ballO x 1) T ∈ S} := by
  have hzb' : IsZeroBoundaryGFF (ballO x R) (fun ω => restrictTo (ballO x R) (ht ω)) P :=
    isZeroBoundaryGFF_of_ae_eq hzb (by filter_upwards [hthz] with ω hω; rw [hω])
      ((measurable_restrictTo _).comp htm)
  have H := hc x R hR P ht htm hzb' g hg a0 hb T hT
  dsimp only at H
  rw [hρ₁R] at H
  obtain ⟨h1, h2, h3, h4⟩ := H
  have hP := rn_pair_bounds h1 h2 h3 h4 hS
  have e0 : (P.map fun ω => restrictTo (ballO x 1) (ht ω)) =
      P.map fun ω => restrictTo (ballO x 1) (hz ω) :=
    Measure.map_congr (by filter_upwards [hthz] with ω hω; rw [hω])
  have hadd : Measurable fun b : DistOn (ballO x 1) => b + restrictTo (ballO x 1) T :=
    measurable_distOn_iff.2 fun φ => by
      show Measurable fun b : DistOn (ballO x 1) => b φ + restrictTo (ballO x 1) T φ
      exact (measurable_distOn_apply φ).add_const _
  have eg : (P.map fun ω => restrictTo (ballO x 1) (ht ω + T)) S =
      (P.map fun ω => restrictTo (ballO x 1) (hz ω)) {b | b + restrictTo (ballO x 1) T ∈ S} := by
    have : (fun ω => restrictTo (ballO x 1) (ht ω + T)) =
        (fun b => b + restrictTo (ballO x 1) T) ∘ fun ω => restrictTo (ballO x 1) (ht ω) := by
      funext ω; simp only [Function.comp, restrictTo_add_gm]
    have hm : Measurable fun ω => restrictTo (ballO x 1) (ht ω) :=
      (measurable_restrictTo _).comp htm
    rw [this, ← Measure.map_map hadd hm, e0,
      Measure.map_apply hadd hS]
    rfl
  rw [eg, e0] at hP
  exact hP

end LQGMetric.GM
