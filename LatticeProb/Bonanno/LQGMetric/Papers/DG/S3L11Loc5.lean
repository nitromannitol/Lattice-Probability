/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Loc5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Loc4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of `μ_{ĥ^tr}` (P2-DGLOC, part 5): node 2(a) of handoff/P2-DG105l.md

DG, arXiv:1807.01072, DG:1268 and DG:1302–1305: for the rescaled noise `W' = W ∘ U_{s,c}`
(`s = 2^{-j}`, the white noise of the cell seen in the unit frame, D105 N5), the event
`E_S = {goodSq (muTr W') …}` is a.s. determined by the white noise `W` on
`(0, s²) × (s · B_{1/10}(U) + c)`, `U` the unit-frame square `sqOne s₀ b₀ x₀`.

* `supportedIn_wnScale`: `U_{δ,b}` maps kernels carried by `(0,1) × T` to kernels carried by
  `(0, δ²) × (δT + b)`;
* `wnSigma_comp_le`: `σ(W ∘ T |_S) ≤ σ(W |_{S'})` when `T` maps `S`-kernels to `S'`-kernels;
* **`dgLocTr`** (the named statement of node 2(a)) and its proof **`dgLocTr_proved`**.

Own elementary glue.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent SupTail QuantumZipper

/-- `U_{δ,b}` maps kernels carried by `(0,1) × T` to kernels carried by `(0,δ²) × (δT + b)` -/
lemma supportedIn_wnScale {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {T : Set ℂ} (hT : MeasurableSet T)
    {g : WNSpace} (hg : SupportedIn (Ioo 0 1 ×ˢ T) g) :
    SupportedIn (Ioo 0 (δ ^ 2) ×ˢ (affineC δ b '' T)) (wnScale hδ b g) := by
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hd2 : 0 < δ ^ 2 := by positivity
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ T) := measurableSet_Ioo.prod hT
  have hS' : MeasurableSet (Ioo 0 (δ ^ 2) ×ˢ (affineC δ b '' T)) := by
    refine measurableSet_Ioo.prod ?_
    rw [← coe_affineHomeoC hδ b]
    exact (affineHomeoC hδ b).measurableEmbedding.measurableSet_image.2 hT
  have h1 : ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), q ∉ Ioo 0 1 ×ˢ T → (g : ℝ × ℂ → ℝ) q = 0 :=
    (ae_restrict_iff' hS.compl).1 hg
  have h2 := (qmp_scMap hδ b).ae h1
  unfold SupportedIn
  refine (ae_restrict_iff' hS'.compl).2 ?_
  filter_upwards [coeFn_wnScale hδ b g, h2] with p hp h hp'
  rw [hp]
  simp only [scFun]
  rw [h ?_, mul_zero]
  intro hmem
  apply hp'
  obtain ⟨hm1, hm2⟩ := hmem
  simp only [scMap] at hm1 hm2
  refine ⟨?_, ⟨_, hm2, ?_⟩⟩
  · rw [inv_mul_eq_div] at hm1
    exact ⟨(div_pos_iff_of_pos_right hd2).1 hm1.1, (div_lt_one hd2).1 hm1.2⟩
  · simp only [affineC, Complex.real_smul, Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hδC, one_mul, sub_add_cancel]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- `σ(W ∘ T |_S) ≤ σ(W |_{S'})` when `T` maps kernels carried by `S` to kernels carried by `S'` -/
lemma wnSigma_comp_le (T : WNSpace → WNSpace) {S S' : Set (ℝ × ℂ)}
    (hT : ∀ g, SupportedIn S g → SupportedIn S' (T g)) :
    wnSigma (fun f ω => W (T f) ω) S ≤ wnSigma W S' := by
  let _ : MeasurableSpace Ω := wnSigma W S'
  have hm : Measurable fun ω (g : {g // SupportedIn S g}) => W (T g.1) ω :=
    measurable_pi_iff.2 fun g => measurable_wnSigma (W := W) (hT g.1 g.2)
  exact hm.comap_le

/-- **DG node 2(a) (D105/D116), the locality of the `μ_{ĥ^tr}` events** (DG:1268, 1302–1305): for
the rescaled noise `W' = W ∘ U_{s,c}`, `s = 2^{-j}`, and any unit-frame square
`U = sqOne s₀ b₀ x₀ ⊆ K`, the event `E_S = {goodSq (muTr W') ε s₀ b₀ M x₀}` is a.s. equal to an
event of the white noise `W` on `(0, s²) × (s · B_{1/10}(U) + c)` -/
def dgLocTr (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ : ℝ) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) (j : ℕ) (c : ℂ)
    (hW' : IsWhiteNoise P (fun f ω => W (wnScaleDy j c f) ω)) (s₀ : ℝ) (b₀ : ℂ) (x₀ : ℤ × ℤ) :
    Prop :=
  ∀ ε M : ℝ, ∃ A', MeasurableSet[wnSigma W (Ioo 0 (((2 : ℝ)⁻¹ ^ j) ^ 2) ×ˢ
      (affineC ((2 : ℝ)⁻¹ ^ j) c '' Metric.thickening (1 / 10) (sqOne s₀ b₀ x₀)))] A' ∧
    {ω | goodSq (muTr hW' γ hb hK ω) ε s₀ b₀ M x₀} =ᵐ[P] A'

/-- **proof of node 2(a)** -/
theorem dgLocTr_proved {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) (j : ℕ) (c : ℂ)
    (hW' : IsWhiteNoise P (fun f ω => W (wnScaleDy j c f) ω)) {s₀ : ℝ} {b₀ : ℂ} {x₀ : ℤ × ℤ}
    (hsq : sqOne s₀ b₀ x₀ ⊆ ferniqueBox y b) :
    dgLocTr P W γ hb hK j c hW' s₀ b₀ x₀ := by
  intro ε M
  obtain ⟨A', hA', hE⟩ := goodSq_muTr_loc hW' hγ hγ2 hb hK hsq ε M
  refine ⟨A', wnSigma_comp_le (W := W) (wnScaleDy j c) (fun g hg => ?_) A' hA', hE⟩
  exact supportedIn_wnScale _ c isOpen_thickening.measurableSet hg

end DG
end LQGMetric
