/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L13V at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13R

/-!
# DG Lemmas 3.13, 3.14 for the vertical `2^{-m} × 2^{-m+1}` rectangles (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.13 (DG:1282–1291) and
Lemma 3.14 (DG:1328–1336, "the same holds with `2^{-m} × 2^{-m+1}` rectangles but with `∂_B`
and `∂_T` in place of `∂_L` and `∂_R`"), for the vertical rectangles `R = u + [0, δ] × [0, 2δ]`,
`δ = 2^{-m}`, with stretched rectangle `R' = u + [0, δ] × [−δ, 3δ] ⊆ Q`.

The input is DG Lemma 3.11 for the vertical rectangles at scale `2^{-j}`, transported by (3.7)
(`DGLem311ScaledV`, the verbatim analogue of `DGLem311Scaled` with left/right replaced by
bottom/top). DG obtain it from the horizontal case by the rotation invariance of `ĥ` (implicit,
DG:1335); here it is a separate hypothesis of the same form. The cores `dg_lemma313_core`,
`dg_lemma314_core` (abstract families) apply verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexOrder

namespace LQGMetric
namespace DG

open WhiteNoise Classical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the vertical stretched rectangle `b + [0, sn] × [−sn, 3sn]` -/
def l313StrV (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  Icc b.re (b.re + s * n) ×ℂ Icc (b.im - s * n) (b.im + 3 * (s * n))

/-- the bottom side of the vertical rectangle `b + [0, sn] × [0, 2sn]` -/
def l313Bot (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  {z | z.im = b.im ∧ b.re ≤ z.re ∧ z.re ≤ b.re + s * n}

/-- the top side of the vertical rectangle `b + [0, sn] × [0, 2sn]` -/
def l313Top (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  {z | z.im = b.im + 2 * (s * n) ∧ b.re ≤ z.re ∧ z.re ≤ b.re + s * n}

/-- **DG Lemma 3.11 for vertical rectangles at scale `2^{-j}`, transported by (3.7)**
(DG:1300–1310, 1335) -/
def DGLem311ScaledV (P : Measure Ω) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (γ d : ℝ)
    (Q : Set ℂ) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ a₀ a₁ A : ℝ, 0 < a₁ ∧ ∀ (j n : ℕ) (b : ℂ),
    l313StrV ((2 : ℝ)⁻¹ ^ j) b n ⊆ Q → ∀ ε : ℝ, 0 < ε →
    P {ω | ¬ (l313Set (μ ω) ε (l313StrV ((2 : ℝ)⁻¹ ^ j) b n) (l313Bot ((2 : ℝ)⁻¹ ^ j) b n)
        (l313Top ((2 : ℝ)⁻¹ ^ j) b n) : ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * max A
        (Real.exp (√(n : ℝ)) * (ε * (((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ *
          Real.exp (-(γ * sSup ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) ''
            l313StrV ((2 : ℝ)⁻¹ ^ j) b n)))) ^ (-(1 / (d - ζ₁)))))} ≤
      ENNReal.ofReal (a₀ * Real.exp (-(a₁ * n)))

/-- the vertical rectangles of level `m` with `R' ⊆ Q` -/
def l313GridV (Q : Set ℂ) (c : ℂ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2 ^ m) ×ˢ Finset.range (2 ^ m)).filter
    fun x => l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1 ⊆ Q

lemma l313StrV_scale (m k : ℕ) (b : ℂ) :
    l313StrV ((2 : ℝ)⁻¹ ^ (m + k)) b (2 ^ k) = l313StrV ((2 : ℝ)⁻¹ ^ m) b 1 := by
  unfold l313StrV; rw [l313_scale_eq]

lemma l313Bot_scale (m k : ℕ) (b : ℂ) :
    l313Bot ((2 : ℝ)⁻¹ ^ (m + k)) b (2 ^ k) = l313Bot ((2 : ℝ)⁻¹ ^ m) b 1 := by
  unfold l313Bot; rw [l313_scale_eq]

lemma l313Top_scale (m k : ℕ) (b : ℂ) :
    l313Top ((2 : ℝ)⁻¹ ^ (m + k)) b (2 ^ k) = l313Top ((2 : ℝ)⁻¹ ^ m) b 1 := by
  unfold l313Top; rw [l313_scale_eq]

theorem l313HypV_of_scaled {μ : Ω → Measure ℂ} {γ d : ℝ} {Q : Set ℂ} (c : ℂ)
    (h : DGLem311ScaledV P W μ γ d Q) :
    L313Hyp P W γ d (l313GridV Q c) (fun m x => l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
      (fun m x ε ω => (l313Set (μ ω) ε (l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Bot ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Top ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞)) := by
  intro ζ₁ h0 h1
  obtain ⟨a₀, a₁, A, ha₁, hh⟩ := h ζ₁ h0 h1
  refine ⟨a₀, a₁, A, ha₁, fun m x hx k ε hε => ?_⟩
  have hQ : l313StrV ((2 : ℝ)⁻¹ ^ (m + k)) (l313Corner c m x) (2 ^ k) ⊆ Q := by
    rw [l313StrV_scale]; exact (Finset.mem_filter.1 hx).2
  have := hh (m + k) (2 ^ k) (l313Corner c m x) hQ ε hε
  rw [l313StrV_scale, l313Bot_scale, l313Top_scale] at this
  push_cast at this
  exact this

lemma l313StrV_diam {δ : ℝ} (hδ : 0 ≤ δ) (b : ℂ) {z w : ℂ} (hz : z ∈ l313StrV δ b 1)
    (hw : w ∈ l313StrV δ b 1) : ‖z - w‖ ≤ 5 * δ := by
  simp only [l313StrV, Nat.cast_one, mul_one, Complex.mem_reProdIm, mem_Icc] at hz hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have h1 : |z.re - w.re| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |z.im - w.im| ≤ 4 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

lemma l313_corner_memV (δ : ℝ) (hδ : 0 ≤ δ) (b : ℂ) : b ∈ l313StrV δ b 1 := by
  simp only [l313StrV, Nat.cast_one, mul_one, Complex.mem_reProdIm, mem_Icc]
  constructor <;> constructor <;> linarith

lemma l313GridV_card (Q : Set ℂ) (c : ℂ) (m : ℕ) :
    ((l313GridV Q c m).card : ℝ) ≤ 1 * 4 ^ m := by
  have h := (Finset.card_filter_le (Finset.range (2 ^ m) ×ˢ Finset.range (2 ^ m))
    fun x => l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1 ⊆ Q)
  rw [Finset.card_product, Finset.card_range] at h
  have : ((2 ^ m * 2 ^ m : ℕ) : ℝ) = 1 * 4 ^ m := by push_cast; rw [← mul_pow]; norm_num
  rw [← this]
  exact_mod_cast h

/-- **DG Lemma 3.13, vertical rectangles** (DG:1282–1291) -/
theorem dg_lemma313V (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ} {Q : Set ℂ} (hQ : Bornology.IsBounded Q) (c : ℂ)
    (h311 : DGLem311ScaledV P W μ γ d Q) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ lam C : ℝ, 0 < lam ∧ ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      P {ω | ∃ x ∈ l313GridV Q c m, ¬ (l313Set (μ ω) ε
          (l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Bot ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Top ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤
        ENNReal.ofReal (l313Tgt γ d ζ ε m (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω)
          '' l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)))} ≤
        ENNReal.ofReal (C * Real.exp (-(lam * m))) :=
  dg_lemma313_core hW hγ hd (l313GridV_card Q c) hQ
    (fun m x hx => (Finset.mem_filter.1 hx).2)
    (fun m x _ => ⟨_, l313_corner_memV _ (by positivity) _⟩) (by norm_num : (1 : ℝ) ≤ 5)
    (fun m x _ z hz w hw => l313StrV_diam (by positivity) _ hz hw)
    (l313HypV_of_scaled c h311) hζ hζ1

/-- **DG Lemma 3.14, vertical rectangles** (DG:1328–1336) -/
theorem dg_lemma314V (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ} {Q : Set ℂ} (hQ : Bornology.IsBounded Q) (c : ℂ)
    (h311 : DGLem311ScaledV P W μ γ d Q) {ζ β : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (hβ : 0 < β) :
    ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P {ω | ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β ∧ ∃ x ∈ l313GridV Q c m, ¬ (l313Set (μ ω) ε
          (l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Bot ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Top ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζ))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζ) * m / d))))} ≤ ENNReal.ofReal (C * ε ^ p) :=
  dg_lemma314_core hW hγ hd (l313GridV_card Q c) hQ
    (fun m x hx => (Finset.mem_filter.1 hx).2)
    (fun m x _ => ⟨_, l313_corner_memV _ (by positivity) _⟩) (by norm_num : (1 : ℝ) ≤ 5)
    (fun m x _ z hz w hw => l313StrV_diam (by positivity) _ hz hw)
    (l313HypV_of_scaled c h311) hζ hζ1 hβ

end DG
end LQGMetric
