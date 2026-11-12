/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32Z1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3EtaB3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32YCross
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32

/-!
# DZZ Prop 3.2 at `μIn`: assembly, and the first steps of D102 P-4bW (P2-DZZETA2)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), Prop 3.2 (`prop-approximate-LGD`), proof l. 1088–1206.

* **`dzz_prop32U_dzzMuIn_of`**: DZZ Prop 3.2 (uniform form `DZZProp32U`) at the walled measure
  `μIn = dzzMuIn γ W`, from the two probabilistic inputs of D102 P-4bW (`L32EncPhiHPW`,
  `L32StartPhiHPC`, still open) and a clip depth `r`; the lower half is now proved
  (`l32BallCover_dzzMuIn_eta`), the crossing is `l32BallCrossingW_holds`.
* `dzzMuIn_ball_le_of_boxes`: DZZ l. 1133–1137 ("each such ball can be covered by at most 4 boxes
  in `𝓑'_i`. Thus, each one has LQG measure at most `δ²` … by the definition of `𝓔_{B'_i,open}`
  together with (eq-M-tilde-B-bound)"), deterministic part, for a ball inside `𝕍`.
* `measure_exists_etaChaos_ge_le`: the union bound of DZZ l. 1126–1130 (`P(𝓔^c_{B'_i,open}) ≤
  |𝓑'_i| · t^{1.9}`), from (Eq.LQG-tildeM) = `measure_etaChaos_ge_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

/-- **DZZ Prop 3.2 at `μIn`**, from the two open inputs of D102 P-4bW. -/
theorem dzz_prop32U_dzzMuIn_of {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) {r : ℝ → ℝ} (hr : IsClipDepth γ r)
    (h1 : L32EncPhiHPW P γ W (dzzMuIn γ W) r) (h2 : L32StartPhiHPC P γ W (dzzMuIn γ W) r) :
    DZZProp32U P γ W (dzzMuIn γ W) ξ ξd :=
  dzz_prop32U_of hW hγ hγ2 hξ hξd (l32BallCover_dzzMuIn_eta hW hγ hγ2)
    (l32UpperCross_ofW' hW hγ hγ2 hr h1 h2 hξ hξd)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ l. 1133–1137** (deterministic): if `M^W(B̃) ≤ K M̃(B̃)` for the boxes near `c_B`
((eq-M-tilde-B-bound)), a ball inside `𝕍` covered by the boxes of `T` (all near `c_B`, with
`M̃(B̃) ≤ θ`) has `μIn`-mass at most `|T| K θ`. -/
lemma dzzMuIn_ball_le_of_boxes {γ δh : ℝ} {ω : Ω} {c : ℂ} {s : ℝ} {K θ : ℝ≥0∞}
    (hup : ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - c‖ ≤ 3 * s) →
      wickQArea γ W ω b'.closedBox ≤ K * etaChaos W γ δh b'.closedBox ω)
    {x : ℂ} {ρ : ℝ} (hball : Metric.ball x ρ ⊆ dzzV) (T : Finset DyBox)
    (hT : Metric.ball x ρ ⊆ ⋃ b' ∈ T, b'.closedBox)
    (hnear : ∀ b' ∈ T, ∀ z ∈ b'.closedBox, ‖z - c‖ ≤ 3 * s)
    (hθ : ∀ b' ∈ T, etaChaos W γ δh b'.closedBox ω ≤ θ) :
    dzzMuIn γ W ω (Metric.ball x ρ) ≤ T.card * (K * θ) := by
  rw [dzzMuIn, dzzWall_ball_of_subset _ hball]
  calc wickQArea γ W ω (Metric.ball x ρ) ≤ wickQArea γ W ω (⋃ b' ∈ T, b'.closedBox) :=
        measure_mono hT
    _ ≤ ∑ b' ∈ T, wickQArea γ W ω b'.closedBox := measure_biUnion_finset_le _ _
    _ ≤ ∑ _b' ∈ T, K * θ := Finset.sum_le_sum fun b' hb' =>
        (hup b' (hnear b' hb')).trans (mul_le_mul_right (hθ b' hb') K)
    _ = T.card * (K * θ) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **DZZ l. 1126–1130**: `P(∃ B̃ ∈ T, M̃(B̃) ≥ θ) ≤ Σ_{B̃ ∈ T} Leb(B̃)/θ` ((Eq.LQG-tildeM) and a
union bound). -/
lemma measure_exists_etaChaos_ge_le (hW : IsWhiteNoise P W) (γ δh : ℝ) (T : Finset DyBox)
    {θ : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθ : θ ≠ ⊤) :
    P {ω | ∃ b' ∈ T, θ ≤ etaChaos W γ δh b'.closedBox ω} ≤
      ∑ b' ∈ T, volume b'.closedBox / θ := by
  have e : {ω | ∃ b' ∈ T, θ ≤ etaChaos W γ δh b'.closedBox ω} =
      ⋃ b' ∈ T, {ω | θ ≤ etaChaos W γ δh b'.closedBox ω} := by
    ext ω; simp
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
  exact measure_etaChaos_ge_le hW γ δh (isClosed_closedBox_eta b').measurableSet hθ0 hθ

/-- the clip depth of D102 P-4bW: `r δ = δ^{C_mc} 2^{-kL37}/8` -/
def rP32 (γ : ℝ) (δ : ℝ) : ℝ := δ ^ dzzCmc γ * (2⁻¹ : ℝ) ^ kL37 γ δ / 8

lemma isClipDepth_rP32 (γ : ℝ) : IsClipDepth γ (rP32 γ) := by
  intro δ ⟨hδ0, _⟩
  have h : 0 < δ ^ dzzCmc γ * (2⁻¹ : ℝ) ^ kL37 γ δ :=
    mul_pos (Real.rpow_pos_of_pos hδ0 _) (by positivity)
  unfold rP32
  constructor <;> linarith

end DZZ
end LQGMetric
