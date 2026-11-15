import LatticeProb.Prob.WilliamsContinuousGlueLaw
import LatticeProb.Prob.UpcrossGlueCocycle
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Main

/-! # Williams gluing as an equality of continuous-path laws -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

open QuantumZipper QuantumZipper.Williams

/-- Equal laws of almost-sure representatives give equal continuous-path laws. -/
theorem map_continuousPath_eq_of_ae_coe_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {F G : Ω → C(ℝ≥0, ℝ)} {f g : Ω → (ℝ≥0 → ℝ)}
    (hF : Measurable F) (hG : Measurable G)
    (hf : ∀ᵐ ω ∂P, (F ω : ℝ≥0 → ℝ) = f ω)
    (hg : ∀ᵐ ω ∂P, (G ω : ℝ≥0 → ℝ) = g ω)
    (h : P.map f = P.map g) : P.map F = P.map G := by
  apply eq_of_map_coeFn_eq
  rw [Measure.map_map measurable_coeFn_path hF,
    Measure.map_map measurable_coeFn_path hG]
  exact (Measure.map_congr hf).trans (h.trans (Measure.map_congr hg).symm)

/-- Williams' gluing law as an equality of laws on continuous paths. -/
theorem map_williams_glueC_eq_map_postLast
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {σ μ c : ℝ} (hσ : 0 < σ) (hμ : 0 < μ)
    (hind : IndepFun (pathOf b) (pathOf b') P) (hc : 0 < c)
    (hhit : ∀ ω, ∃ t, dpath σ (-μ) b ω t = -c)
    (hhit' : ∀ ω (d : ℝ), 0 < d → ∃ t, dpath σ (-μ) b' ω t = -d) :
    P.map (fun ω => glueC c ⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩
      (williamsPostLastPath hb' σ μ ω)) = P.map (williamsPostLastPath hb' σ μ) := by
  have hX : Measurable (fun ω =>
      (⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩ : C(ℝ≥0, ℝ))) :=
    ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 (fun t => measurable_dpath hb σ (-μ) t)
  have hZ := measurable_williamsPostLastPath hb' σ μ
  have hF := (measurable_glueC c).comp (hX.prodMk hZ)
  apply map_continuousPath_eq_of_ae_coe_eq hF hZ
    (ae_williams_glue_eq hb hb' hσ hμ hhit) (Eventually.of_forall fun _ => rfl)
  exact map_glued_eq_map_postLast hb hb' hσ hμ hind hc hhit hhit'

end LatticeProb
