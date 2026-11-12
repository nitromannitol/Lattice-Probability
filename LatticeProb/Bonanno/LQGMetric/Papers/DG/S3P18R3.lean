/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18R3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18R2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18E

/-!
# DG:1774–1777: P3.22 in `𝕊(1)` coordinates for a whole-plane GFF (task P2-DG105q)

"By [L2.2] the same is true with a whole-plane GFF in place of `h^{𝕊(1)}`" (DG:1776). For a
normalized whole-plane GFF `h` with continuous circle averages `H`, L2.2
(`L22T.dg_lemma22_tr`, `U = (−1,2)²`, `K = 𝕊(1/2) = p18Half`) gives `h = hh' + hz`. Then
`H_δ = (H_δ − 𝔥) + 𝔥` with `H_δ − 𝔥` a continuous version of `hz_δ` on `p18Half`
(`r18_ae_version`), whose LFPP event has the law of the one for `h^{𝕊(1)}` (`r18_transfer`), and
`|𝔥| ≤ A = (ζ/2ξ) log δ⁻¹` on `p18Half` off an event of probability `≤ a₀e^{−a₁A²}`.

* `r18_dgLFPP_le_meas`, `r18_cmp_diam`, `r18_loc_diam`: the sup functional
  `F φ = sup_{z,w ∈ 𝕊} D_φ(z,w; X)` has the comparison and locality properties;
* `R18P322` — P3.22 in `𝕊(1)` coordinates for some zero-boundary GFF on `(−1,2)²` with a
  continuous version of its circle averages on `p18Half` (the reference coupling of
  `dgLem37V_exists_box` with the side facts of handoff/P2-DG105m.md §6, and
  `dg_prop322_sqOne_muHat`: `r18P322_of`);
* **`r18_unit`** — the same bound for `H`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint

/-- **LFPP comparison** for a measurable `ψ` bounded on `S` -/
lemma r18_dgLFPP_le_meas {ξ a : ℝ} (hξ : 0 ≤ ξ) {φ ψ : ℂ → ℝ} {S : Set ℂ}
    (hψm : Measurable ψ) {B : ℝ} (hψB : ∀ x ∈ S, |ψ x| ≤ B) (hφψ : ∀ x ∈ S, φ x ≤ ψ x + a)
    (z w : ℂ) : dgLFPP ξ φ S z w ≤ Real.exp (ξ * a) * dgLFPP ξ ψ S z w := by
  rcases isEmpty_or_nonempty {p : ℝ → ℂ // IsDGPath S z w p} with he | hne
  · simp [dgLFPP, iInf_of_isEmpty]
  have hE := Real.exp_pos (ξ * a)
  rw [← div_le_iff₀' hE]
  refine le_ciInf fun p => ?_
  rw [div_le_iff₀' hE]
  exact (ciInf_le (bddBelow_dg ξ φ S z w) p).trans
    (t18_lfppLength_le_meas hξ hψm hψB hφψ p.2)

/-- `sup_{z,w ∈ Q} D_φ(z,w; X)` -/
def r18F (ξ : ℝ) (Q X : Set ℂ) (φ : ℂ → ℝ) : ℝ≥0∞ :=
  ⨆ z ∈ Q, ⨆ w ∈ Q, ENNReal.ofReal (dgLFPP ξ φ X z w)

lemma r18_cmp_diam {ξ : ℝ} (hξ : 0 ≤ ξ) (Q X : Set ℂ) : T18Cmp ξ X (r18F ξ Q X) := by
  intro φ ψ _ hψ ⟨B, hB⟩ η _ hφψ
  simp only [r18F]
  refine iSup₂_le fun z hz => iSup₂_le fun w hw => ?_
  refine (ENNReal.ofReal_le_ofReal (r18_dgLFPP_le_meas hξ hψ hB hφψ z w)).trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr
  exact le_iSup₂_of_le z hz (le_iSup₂_of_le w hw le_rfl)

lemma r18_dgLFPP_congr {ξ : ℝ} {φ ψ : ℂ → ℝ} {X : Set ℂ} (h : EqOn φ ψ X) (z w : ℂ) :
    dgLFPP ξ φ X z w = dgLFPP ξ ψ X z w := by
  unfold dgLFPP
  congr 1; funext p
  unfold LQGDimension.lfppLength
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [h (p.2.mapsTo ht)]

lemma r18_loc_diam (ξ : ℝ) (Q X : Set ℂ) (φ ψ : ℂ → ℝ) (h : EqOn φ ψ X) :
    r18F ξ Q X φ = r18F ξ Q X ψ := by
  simp only [r18F, r18_dgLFPP_congr h]

lemma r18_diam_iff {ξ t : ℝ} (ht : 0 ≤ t) {Q X : Set ℂ} {φ : ℂ → ℝ} :
    (∀ z ∈ Q, ∀ w ∈ Q, dgLFPP ξ φ X z w ≤ t) ↔ r18F ξ Q X φ ≤ ENNReal.ofReal t := by
  simp only [r18F, iSup₂_le_iff]
  refine forall₂_congr fun z _ => forall₂_congr fun w _ => ?_
  exact (ENNReal.ofReal_le_ofReal_iff ht).symm

lemma r18_p18Half_eq : p18Half = r18X (-1 / 2) (3 / 2) := by
  ext x; simp [p18Half, r18X, Complex.mem_reProdIm]

lemma r18_ball_sqOne {x : ℂ} (hx : x ∈ p18Half) {s : ℝ} (hs : s < 1 / 2) :
    closedBall x s ⊆ (Blueprint.sqOne : Set ℂ) := fun y hy => by
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [r18_p18Half_eq] at hx
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  have hre := (Complex.abs_re_le_norm (y - x)).trans hy
  have him := (Complex.abs_im_le_norm (y - x)).trans hy
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hre.1, hre.2, him.1, him.2]

lemma r18_p18Half_compact : IsCompact p18Half :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    (Metric.isBounded_Icc _ _ |>.reProdIm (Metric.isBounded_Icc _ _))

lemma r18_sqOne_bdd : Bornology.IsBounded (Blueprint.sqOne : Set ℂ) :=
  (Metric.isBounded_Icc (-1 : ℝ) 2).reProdIm (Metric.isBounded_Icc (-1 : ℝ) 2) |>.subset
    fun x hx => ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.1.le, hx.2.2.le⟩

/-- **P3.22 in `𝕊(1)` coordinates for a zero-boundary GFF on `(−1,2)²`** whose circle averages
have a continuous version on `p18Half` (the output of `dg_prop322_sqOne_muHat` on the reference
coupling) -/
def R18P322 : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hz : Ω → DistC) (hc : ℝ → ℂ → Ω → ℝ),
    IsZeroBoundaryGFF Blueprint.sqOne (fun ω => restrictTo Blueprint.sqOne (hz ω)) P ∧
    (∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∀ ω, ContinuousOn (fun x => hc δ x ω) p18Half) ∧
    (∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∀ x ∈ p18Half, hc δ x =ᵐ[P] fun ω => circleAvg (hz ω) δ x) ∧
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ζ : ℝ, 0 < ζ →
      ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
          dgLFPP (xiGamma γ) (fun x => hc δ x ω) p18Half z w ≤ δ ^ (dgLambda γ - ζ)} ≤
          ENNReal.ofReal (C * δ ^ p)

end LQGMetric.DG
