/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L37P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR4b
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR4c
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG

/-!
# DG Lemma 3.7 from DGo Prop. 3.3 and DG Lemma 3.4, given the white-noise ZB GFF (task P2-HEAT3)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.7 (`lem-circle-avg-approx`,
DG:1096–1102), proof DG:1103–1105: "By [DGo, Proposition 3.2] (applied with `𝒰 = 𝕊(1)`), there is
a coupling of `ĥ` and `h^{𝕊(1)}` such that `max_{z∈𝕊} |h^{𝕊(1)}_δ(z) − ĥ_δ(z)| ≤ (ζ/2) log δ⁻¹`
with superpolynomially high probability; combine with Lemma 3.4."

DGo's coupling (DGo (3.1), Lemma 3.1, DGo:491–515) is `h^𝒰_δ(v) = √π W(K^𝒰_{δ,v})`: the
zero-boundary GFF built from the same white noise. The analytic content is proved here and in
`Papers/DGo/HeatDirR*`; the realization of that field as a random *distribution* is the node

* `DGZBRealization`: on some white-noise space there is `hz : Ω → DistC` with
  `IsZBGFFExtDist sqOne hz P` whose circle averages are `√π W(dirCircKernel (−1) 3 δ x)` a.s.
  (`x ∈ 𝕊(1/2)`, `δ ∈ (0, 1/2)`) — DGo:495 / DG:1104 for `𝒰 = 𝕊(1) = (−1,2)²`;

and **`dgLem3_7_of_realization : DGZBRealization → Blueprint.DGLem3_7`**: `hc` is the continuous
version of `√π W(K_{δ,·})` on `𝕊(1/2)` (`dgo_hat_cont_version_K`), `max_{𝕊(1/2)} |hc_δ − ĥ_δ|` is
handled by DGo Prop. 3.3 (`dgo_prop33_sq`, `ε = 1/4`) and `|ĥ_δ(z) − ĥ_δ(w)|`, `|z − w| ≤ Cδ`,
by DG Lemma 3.4 (`dg_lemma34C`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DG
namespace L37P

open WhiteNoise SupTail DGo.HeatDir HeatSq

/-- the white-noise zero-boundary GFF on `𝕊(1) = (−1,2)²` as a random distribution, with DGo's
circle averages `√π W(K^{𝕊(1)}_{δ,x})` (DGo (3.1), Lemma 3.1) -/
def DGZBRealization : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hz : Ω → DistC),
    IsWhiteNoise P W ∧ Blueprint.IsZBGFFExtDist Blueprint.sqOne hz P ∧
    ∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∀ x ∈ Blueprint.sqHalf,
      (fun ω => circleAvg (hz ω) δ x) =ᵐ[P]
        fun ω => Real.sqrt π * W (dirCircKernel (-1) 3 δ x) ω

/-- the corner `−1/2 − i/2` of `𝕊(1/2)` -/
def halfCorner : ℂ := ⟨-1 / 2, -1 / 2⟩

lemma sqHalf_eq : Blueprint.sqHalf = ferniqueBox halfCorner 2 := by
  ext z
  rw [mem_ferniqueBox_iff]
  simp only [Blueprint.sqHalf, halfCorner, mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma sqOne_eq : (Blueprint.sqOne : Set ℂ) = sqOpen (-1) 3 := by
  ext z
  simp only [Blueprint.sqOne, TopologicalSpace.Opens.coe_mk, sqOpen, mem_inter_iff,
    mem_preimage, mem_Ioo, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma convex_ferniqueBox' (x₀ : ℂ) (b : ℝ) : Convex ℝ (ferniqueBox x₀ b) := by
  intro x hx y hy s t hs ht hst
  rw [mem_ferniqueBox_iff] at hx hy ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨h5, h6, h7, h8⟩ := hy
  have e1 : x₀.re = s * x₀.re + t * x₀.re := by rw [← add_mul, hst, one_mul]
  have e2 : x₀.im = s * x₀.im + t * x₀.im := by rw [← add_mul, hst, one_mul]
  have e3 : x₀.re + b = s * (x₀.re + b) + t * (x₀.re + b) := by rw [← add_mul, hst, one_mul]
  have e4 : x₀.im + b = s * (x₀.im + b) + t * (x₀.im + b) := by rw [← add_mul, hst, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h5 ht]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hs, mul_le_mul_of_nonneg_left h6 ht]
  · nlinarith [mul_le_mul_of_nonneg_left h3 hs, mul_le_mul_of_nonneg_left h7 ht]
  · nlinarith [mul_le_mul_of_nonneg_left h4 hs, mul_le_mul_of_nonneg_left h8 ht]

/-- `[−1/2 − δ, 3/2 + δ]²`, the closed `δ`-neighbourhood of `𝕊(1/2)` -/
def kBox (δ : ℝ) : Set ℂ := ferniqueBox ⟨-1 / 2 - δ, -1 / 2 - δ⟩ (2 + 2 * δ)

lemma kBox_subset {δ : ℝ} (hδ : δ < 1 / 2) : kBox δ ⊆ sqOpen (-1) 3 := by
  intro z hz
  rw [kBox, mem_ferniqueBox_iff] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only at * <;> linarith

lemma closedBall_subset_box {v : ℂ} {r c : ℝ} {x₀ : ℂ} {b : ℝ}
    (hv : v ∈ ferniqueBox x₀ b) (hr : r ≤ c) :
    closedBall v r ⊆ ferniqueBox ⟨x₀.re - c, x₀.im - c⟩ (b + 2 * c) := by
  intro z hz
  rw [mem_ferniqueBox_iff] at hv ⊢
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - v)).trans hz
  have him := (Complex.abs_im_le_norm (z - v)).trans hz
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  obtain ⟨h1, h2, h3, h4⟩ := hv
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith

lemma closedBall_subset_kBox {δ : ℝ} {v : ℂ} (hv : v ∈ ferniqueBox halfCorner 2) :
    closedBall v δ ⊆ kBox δ := by
  have h := closedBall_subset_box (r := δ) (c := δ) hv le_rfl
  simpa [kBox, halfCorner] using h

lemma closedBall_quarter_subset {v : ℂ} (hv : v ∈ ferniqueBox halfCorner 2) :
    closedBall v (1 / 4) ⊆ sqOpen (-1) 3 :=
  (closedBall_subset_kBox hv).trans (kBox_subset (by norm_num))

lemma bddAbove_abs_sub {Ω : Type*} {x₀ : ℂ} {b : ℝ} {F G : ℂ → Ω → ℝ} (ω : Ω)
    (hF : ContinuousOn (fun v => F v ω) (ferniqueBox x₀ b))
    (hG : ContinuousOn (fun v => G v ω) (ferniqueBox x₀ b)) :
    BddAbove (range fun v : ferniqueBox x₀ b => |F v ω - G v ω|) := by
  obtain ⟨M, hM⟩ := (isCompact_ferniqueBox x₀ b).bddAbove_image
    (f := fun v => |F v ω - G v ω|) (hF.sub hG).abs
  exact ⟨M, by rintro _ ⟨w, rfl⟩; exact hM ⟨w, w.2, rfl⟩⟩

/-- **DG Lemma 3.7** (`Blueprint.DGLem3_7`, DG:1096–1105) from the white-noise realization of
the zero-boundary GFF on `𝕊(1)`: DGo Prop. 3.3 (`dgo_prop33_sq`) + DG Lemma 3.4 (`dg_lemma34C`). -/
theorem dgLem3_7_of_realization (hR : DGZBRealization) : Blueprint.DGLem3_7 := by
  obtain ⟨Ω, _, P, W, hz, hW, hzZB, hid⟩ := hR
  have := hW.isProbabilityMeasure
  have hex : ∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧
      ∀ v ∈ Blueprint.sqHalf, Y v =ᵐ[P] fun ω => Real.sqrt π * W (dirCircKernel (-1) 3 δ v) ω := by
    intro δ hδ
    obtain ⟨Y, h1, _, h3⟩ := dgo_hat_cont_version_K hW (a := -1) (L := 3) (by norm_num) hδ.1
      (isCompact_ferniqueBox _ _) (convex_ferniqueBox' _ _) (kBox_subset hδ.2) (y := halfCorner)
      (b := 2) (by norm_num) (fun v hv => closedBall_subset_kBox hv)
    refine ⟨Y, h1, fun v hv => ?_⟩
    have := h3 v
    rwa [clampKer_of_mem (sqHalf_eq ▸ hv)] at this
  choose! Y hYc hYv using hex
  refine ⟨Ω, _, P, W, hz, Y, ⟨inferInstance, hW, hzZB, fun δ hδ ω => (hYc δ hδ ω).continuousOn,
    fun δ hδ x hx => (hYv δ hδ x hx).trans (hid δ hδ x hx).symm⟩, ?_⟩
  intro C hC ζ hζ p hp
  have hζ0 : 0 < ζ := hζ.1
  obtain ⟨σ2, K, hσ, hprop⟩ := dgo_prop33_sq hW (a := -1) (L := 3) (ε := 1 / 4) (by norm_num)
    (y := halfCorner) (b := 2) (by norm_num) fun v hv => closedBall_quarter_subset hv
  have hbdd : Bornology.IsBounded Blueprint.sqHalf :=
    sqHalf_eq ▸ (isCompact_ferniqueBox _ _).isBounded
  obtain ⟨δ₂, hδ₂, hL34⟩ := dg_lemma34C hW hbdd (ζ := ζ / 2) (by positivity)
    (C := max C 1) (le_max_right _ _) hp
  set ℓ₀ := max ((2 * K / (ζ / 2)) ^ 2) (32 * σ2 * p / ζ ^ 2)
  refine ⟨3, min (min (1 / 16) δ₂) (Real.exp (-ℓ₀)), by positivity, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ16 : δ < 1 / 16 := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδδ₂ : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδe : δ < Real.exp (-ℓ₀) := hδ.2.trans_le (min_le_right _ _)
  set ℓ := Real.log δ⁻¹
  have hℓ : ℓ₀ < ℓ := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this
    simp only [ℓ, Real.log_inv]; linarith
  have hℓ1 : (2 * K / (ζ / 2)) ^ 2 ≤ ℓ := (le_max_left _ _).trans hℓ.le
  have hℓ2 : 32 * σ2 * p / ζ ^ 2 ≤ ℓ := (le_max_right _ _).trans hℓ.le
  have hℓ0 : 0 ≤ ℓ := (sq_nonneg _).trans hℓ1
  have hδ12 : δ ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hδ0, by linarith⟩
  have hδp : δ ∈ Ioo 0 (min (1 / 4 / 4) (1 / 2)) := ⟨hδ0, lt_min (by linarith) (by linarith)⟩
  have hφ := DDDF.isPhiVersion_phiVer hW hδ0 (show δ ≤ 1 by linarith)
  set B1 := {ω | ζ / 2 * ℓ ≤ ⨆ v : ferniqueBox halfCorner 2,
    |Y δ v ω - DDDF.phiVer W P δ 1 v ω|}
  set B2 := {ω | ∃ z ∈ Blueprint.sqHalf, ∃ w ∈ Blueprint.sqHalf, ‖z - w‖ ≤ max C 1 * δ ∧
    ζ / 2 * Real.log δ⁻¹ < |DDDF.phiVer W P δ 1 z ω - DDDF.phiVer W P δ 1 w ω|}
  have hsub : {ω | ¬ ∀ z ∈ Blueprint.sqHalf, ∀ w ∈ Blueprint.sqHalf, ‖z - w‖ ≤ C * δ →
      |Y δ z ω - DDDF.phiVer W P δ 1 w ω| ≤ ζ * Real.log δ⁻¹} ⊆ B1 ∪ B2 := by
    intro ω hω
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨hn1, hn2⟩ := hn
    apply hω
    intro z hz w hw hzw
    have hzb : z ∈ ferniqueBox halfCorner 2 := sqHalf_eq ▸ hz
    have h1 : |Y δ z ω - DDDF.phiVer W P δ 1 z ω| ≤
        ⨆ v : ferniqueBox halfCorner 2, |Y δ v ω - DDDF.phiVer W P δ 1 v ω| :=
      le_ciSup (f := fun v : ferniqueBox halfCorner 2 => |Y δ v ω - DDDF.phiVer W P δ 1 v ω|)
        (bddAbove_abs_sub ω (hYc δ hδ12 ω).continuousOn (hφ.cont ω).continuousOn) ⟨z, hzb⟩
    have h1' : ¬ ζ / 2 * ℓ ≤ _ := hn1
    have h2 : |DDDF.phiVer W P δ 1 z ω - DDDF.phiVer W P δ 1 w ω| ≤ ζ / 2 * ℓ := by
      by_contra h2
      exact hn2 ⟨z, hz, w, hw, hzw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le),
        lt_of_not_ge h2⟩
    have h3 := abs_sub_le (Y δ z ω) (DDDF.phiVer W P δ 1 z ω) (DDDF.phiVer W P δ 1 w ω)
    replace h1' := lt_of_not_ge h1'
    show _ ≤ ζ * ℓ
    linarith
  have hB2 : P B2 ≤ ENNReal.ofReal (δ ^ p) := hL34 δ ⟨hδ0, hδδ₂⟩
  have hB1r := hprop δ hδp (Y δ) (DDDF.phiVer W P δ 1) (fun ω => (hYc δ hδ12 ω).continuousOn)
    (fun ω => (hφ.cont ω).continuousOn) (fun v hv => hYv δ hδ12 v (sqHalf_eq ▸ hv))
    (fun v _ => hφ.ae_eq v) (ζ / 2) (by positivity) hℓ1
  have hexp : 2 * Real.exp (-(ζ / 2 * ℓ) ^ 2 / (8 * σ2)) ≤ 2 * δ ^ p := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Real.rpow_def_of_pos hδ0]
    refine Real.exp_le_exp.2 ?_
    have hlog : Real.log δ = -ℓ := by simp only [ℓ, Real.log_inv, neg_neg]
    rw [hlog]
    have h32 : 32 * σ2 * p ≤ ℓ * ζ ^ 2 := by rwa [div_le_iff₀ (by positivity)] at hℓ2
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h32 hℓ0]
  have hB1 : P B1 ≤ ENNReal.ofReal (2 * δ ^ p) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P B1)]
    exact ENNReal.ofReal_le_ofReal (hB1r.trans hexp)
  calc P _ ≤ P (B1 ∪ B2) := measure_mono hsub
    _ ≤ P B1 + P B2 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * δ ^ p) + ENNReal.ofReal (δ ^ p) := add_le_add hB1 hB2
    _ = ENNReal.ofReal (3 * δ ^ p) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end L37P
end DG
end LQGMetric
