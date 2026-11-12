/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.LGDMeasQ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeas
import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMass
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Exp

/-!
# a.e.-measurability of `D_δ` for the LQG measure on the open unit square (P2-LGDMEAS)

`aemeasurable_qAreaMeasureOn_ball'`: for `0 < γ < 2` and a zero-boundary GFF `X` on `𝕍 = (0,1)²`,
`ω ↦ μ_{X ω}(B(c,r))` is a.e.-measurable for **every** ball (`DG.aemeasurable_qAreaMeasureOn_ball`
needs `B̄(c,r) ⊆ 𝕍`). The measure does not charge `𝕍ᶜ` (`qAreaMeasureOn_openSquare_compl`), so
`μ(B(c,r)) = μ(B(c,r) ∩ 𝕍)`, and the mass of the bounded open set `B(c,r) ∩ 𝕍` is the monotone
limit of the integrals of QZ's cut-offs `LQGMeas.openBump` (`LQGMeas.measure_open_eq_iSup`), each
an a.s. limit of measurable pre-limit integrals (`Prop16Area.Meas.Psi`). This is the argument of
`DG.aemeasurable_qAreaMeasureOn_ball` with `openBump` in place of `ballCut` (own elementary glue,
following QZ's `LQGMeas.measurable_qAreaMeasure_open`).

Consequences: a.e.-measurability of `ω ↦ D_δ(u,v)`, `log D_δ(u,v)`, `min_{A×B} D_δ`, and of
`logMinLGD` (the integrand of DZZ Lemma 3.10, `S3L10Exp.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set QuantumZipper
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Measure ℂ → ℝ}

/-- **a.e.-measurability of ball masses, every ball** -/
theorem aemeasurable_qAreaMeasureOn_ball' (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (c : ℂ) (r : ℝ) :
    AEMeasurable (fun ω => qAreaMeasureOn γ (X ω) openSquare (Metric.ball c r)) P := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  set W : Set ℂ := Metric.ball c r ∩ openSquare with hW
  have hWo : IsOpen W := Metric.isOpen_ball.inter isOpen_openSquare'
  have hWb : Bornology.IsBounded W := Metric.isBounded_ball.subset inter_subset_left
  have hWc : Wᶜ.Nonempty := ⟨0, fun h => by
    have := h.2; simp [openSquare] at this⟩
  have hWU : W ⊆ openSquare := inter_subset_right
  let F : Ω → ℝ≥0∞ := fun ω =>
    ⨆ n, ENNReal.ofReal (Prop16Area.Meas.Psi γ X (fun _ z => LQGMeas.openBump W n z) ω)
  have hF : Measurable F := Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (Prop16Area.Meas.measurable_Psi γ hXm
      ((LQGMeas.continuous_openBump W n).measurable.comp measurable_snd))
  refine hF.aemeasurable.congr ?_
  filter_upwards [ae_isVagueLimitOn_qAreaMeasureOn_openSquare hX hγ hγ2] with ω hm
  set μ := qAreaMeasureOn γ (X ω) openSquare
  have hts : ∀ n, tsupport (LQGMeas.openBump W n) ⊆ openSquare := fun n =>
    (LQGMeas.tsupport_openBump_subset W n).trans hWU
  have ePsi : ∀ n, Prop16Area.Meas.Psi γ X (fun _ z => LQGMeas.openBump W n z) ω =
      ∫ z, LQGMeas.openBump W n z ∂μ := fun n =>
    (hm.2.2 _ (LQGMeas.continuous_openBump W n) (LQGMeas.hasCompactSupport_openBump hWb n)
      (hts n)).limUnder_eq
  have eL : ∀ n, ENNReal.ofReal (∫ z, LQGMeas.openBump W n z ∂μ) =
      ∫⁻ z, ENNReal.ofReal (LQGMeas.openBump W n z) ∂μ := fun n =>
    ofReal_integral_eq_lintegral_ofReal
      (GoodSample.integrable_of_tsupport hm.2.1 (LQGMeas.continuous_openBump W n)
        (LQGMeas.hasCompactSupport_openBump hWb n) (hts n))
      (ae_of_all _ (LQGMeas.openBump_nonneg W n))
  simp only [F, ePsi, eL]
  rw [← LQGMeas.measure_open_eq_iSup μ hWo hWc, hW,
    measure_inter_conull (qAreaMeasureOn_openSquare_compl γ (X ω))]

omit [IsProbabilityMeasure P] in
/-- `logMinLGD` (DZZ Lemma 3.10's integrand) is a.e.-measurable for a random measure with
a.e.-measurable ball masses -/
theorem aemeasurable_logMinLGD {μ : Ω → Measure ℂ}
    (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P) (δ : ℝ) (A B : Set ℂ) :
    AEMeasurable (fun ω => logMinLGD (μ ω) δ A B) P :=
  aemeasurable_log_lgdMinSet hμ δ A B

end DZZ
end LQGMetric
