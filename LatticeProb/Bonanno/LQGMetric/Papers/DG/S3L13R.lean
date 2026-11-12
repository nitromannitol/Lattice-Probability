/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L13R at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L14
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L2
import Mathlib.Analysis.Complex.ReImTopology

/-!
# DG Lemmas 3.13, 3.14 for the dyadic `2^{-m+1} × 2^{-m}` rectangles (P2-DG105i)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.13 (DG:1282–1291) and
Lemma 3.14 (DG:1328–1336), for DG's horizontal rectangles `R = u + [0, 2δ] × [0, δ]`,
`δ = 2^{-m}`, with corner `u ∈ c + δ{0,…,2^m−1}²` and stretched rectangle
`R' = u + [−δ, 3δ] × [0, δ] ⊆ Q` (DG: `R ⊆ 𝕊`, corners in `2^{-m}ℤ²`, `R' ⊆ 𝕊(1/2)`).
The vertical rectangles are the same statement for the reflected field (not done here).

The input is DG Lemma 3.11 at scale `s = 2^{-j}` transported by (3.7) (`DGLem311Scaled`, the
form of `L313Hyp` for the rectangles `s ℛ_n + b`). The rectangle sets are local copies of
P10's `rectStretch`/`rectLeft`/`rectRight` (Papers/DG/S3L11Det, not imported: other owner);
they agree with them up to `3 * s * n = 3 * (s * n)`.
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

/-- `s ℛ_n' + b = b + [−sn, 3sn] × [0, sn]` (DG:1189, Definition 3.10) -/
def l313Str (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  Icc (b.re - s * n) (b.re + 3 * (s * n)) ×ℂ Icc b.im (b.im + s * n)

/-- the left side of `s ℛ_n + b` -/
def l313Left (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  {z | z.re = b.re ∧ b.im ≤ z.im ∧ z.im ≤ b.im + s * n}

/-- the right side of `s ℛ_n + b` -/
def l313Right (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  {z | z.re = b.re + 2 * (s * n) ∧ b.im ≤ z.im ∧ z.im ≤ b.im + s * n}

/-- `D^ε(A, B; U)` (copy of P10's `dgLGDSet`) -/
def l313Set (μ : Measure ℂ) (ε : ℝ) (U A B : Set ℂ) : ℕ∞ :=
  ⨅ z ∈ A, ⨅ w ∈ B, dgLGD μ ε U z w

/-- **DG Lemma 3.11 at scale `2^{-j}`, transported by (3.7)** (DG:1300–1310; D105 item 1) -/
def DGLem311Scaled (P : Measure Ω) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (γ d : ℝ)
    (Q : Set ℂ) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ a₀ a₁ A : ℝ, 0 < a₁ ∧ ∀ (j n : ℕ) (b : ℂ),
    l313Str ((2 : ℝ)⁻¹ ^ j) b n ⊆ Q → ∀ ε : ℝ, 0 < ε →
    P {ω | ¬ (l313Set (μ ω) ε (l313Str ((2 : ℝ)⁻¹ ^ j) b n) (l313Left ((2 : ℝ)⁻¹ ^ j) b n)
        (l313Right ((2 : ℝ)⁻¹ ^ j) b n) : ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * max A
        (Real.exp (√(n : ℝ)) * (ε * (((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ *
          Real.exp (-(γ * sSup ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) ''
            l313Str ((2 : ℝ)⁻¹ ^ j) b n)))) ^ (-(1 / (d - ζ₁)))))} ≤
      ENNReal.ofReal (a₀ * Real.exp (-(a₁ * n)))

/-- the corner of the rectangle of index `x` at level `m` -/
def l313Corner (c : ℂ) (m : ℕ) (x : ℕ × ℕ) : ℂ :=
  ⟨c.re + (2 : ℝ)⁻¹ ^ m * x.1, c.im + (2 : ℝ)⁻¹ ^ m * x.2⟩

/-- the rectangles of level `m` with `R' ⊆ Q` -/
def l313Grid (Q : Set ℂ) (c : ℂ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2 ^ m) ×ˢ Finset.range (2 ^ m)).filter
    fun x => l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1 ⊆ Q

lemma l313_scale_eq (m k : ℕ) :
    (2 : ℝ)⁻¹ ^ (m + k) * ((2 ^ k : ℕ) : ℝ) = (2 : ℝ)⁻¹ ^ m * ((1 : ℕ) : ℝ) := by
  push_cast
  rw [pow_add, mul_assoc, ← mul_pow]; norm_num

lemma l313Str_scale (m k : ℕ) (b : ℂ) :
    l313Str ((2 : ℝ)⁻¹ ^ (m + k)) b (2 ^ k) = l313Str ((2 : ℝ)⁻¹ ^ m) b 1 := by
  unfold l313Str; rw [l313_scale_eq]

lemma l313Left_scale (m k : ℕ) (b : ℂ) :
    l313Left ((2 : ℝ)⁻¹ ^ (m + k)) b (2 ^ k) = l313Left ((2 : ℝ)⁻¹ ^ m) b 1 := by
  unfold l313Left; rw [l313_scale_eq]

lemma l313Right_scale (m k : ℕ) (b : ℂ) :
    l313Right ((2 : ℝ)⁻¹ ^ (m + k)) b (2 ^ k) = l313Right ((2 : ℝ)⁻¹ ^ m) b 1 := by
  unfold l313Right; rw [l313_scale_eq]

/-- `DGLem311Scaled` gives `L313Hyp` for the grid rectangles (DG:1300–1305: `2^{m+n_m}(R − u_R)
= ℛ_{2^{n_m}}`) -/
theorem l313Hyp_of_scaled {μ : Ω → Measure ℂ} {γ d : ℝ} {Q : Set ℂ} (c : ℂ)
    (h : DGLem311Scaled P W μ γ d Q) :
    L313Hyp P W γ d (l313Grid Q c) (fun m x => l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
      (fun m x ε ω => (l313Set (μ ω) ε (l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Left ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Right ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞)) := by
  intro ζ₁ h0 h1
  obtain ⟨a₀, a₁, A, ha₁, hh⟩ := h ζ₁ h0 h1
  refine ⟨a₀, a₁, A, ha₁, fun m x hx k ε hε => ?_⟩
  have hQ : l313Str ((2 : ℝ)⁻¹ ^ (m + k)) (l313Corner c m x) (2 ^ k) ⊆ Q := by
    rw [l313Str_scale]; exact (Finset.mem_filter.1 hx).2
  have := hh (m + k) (2 ^ k) (l313Corner c m x) hQ ε hε
  rw [l313Str_scale, l313Left_scale, l313Right_scale] at this
  push_cast at this
  exact this

lemma l313Str_diam {δ : ℝ} (hδ : 0 ≤ δ) (b : ℂ) {z w : ℂ} (hz : z ∈ l313Str δ b 1)
    (hw : w ∈ l313Str δ b 1) : ‖z - w‖ ≤ 5 * δ := by
  simp only [l313Str, Nat.cast_one, mul_one, Complex.mem_reProdIm, mem_Icc] at hz hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have h1 : |z.re - w.re| ≤ 4 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |z.im - w.im| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

lemma l313_corner_mem (δ : ℝ) (hδ : 0 ≤ δ) (b : ℂ) : b ∈ l313Str δ b 1 := by
  simp only [l313Str, Nat.cast_one, mul_one, Complex.mem_reProdIm, mem_Icc]
  constructor <;> constructor <;> linarith

lemma l313Grid_card (Q : Set ℂ) (c : ℂ) (m : ℕ) :
    ((l313Grid Q c m).card : ℝ) ≤ 1 * 4 ^ m := by
  have h := (Finset.card_filter_le (Finset.range (2 ^ m) ×ˢ Finset.range (2 ^ m))
    fun x => l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1 ⊆ Q)
  rw [Finset.card_product, Finset.card_range] at h
  have : ((2 ^ m * 2 ^ m : ℕ) : ℝ) = 1 * 4 ^ m := by push_cast; rw [← mul_pow]; norm_num
  rw [← this]
  exact_mod_cast h

/-- **DG Lemma 3.13** (DG:1282–1291) for the horizontal grid rectangles with `R' ⊆ Q`
(`Q` bounded): with probability `1 − O(e^{−λm})`, uniformly in `ε ∈ (0,1]`, for every such `R`,
`D^ε(∂_L R, ∂_R R; R') ≤ max{m³, ε^{-1/(d−ζ)} 2^{-(2+γ²/2−ζ)m/d} e^{(γ/d) min_{R'} ĥ_{2^{-m}}}}` -/
theorem dg_lemma313 (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ} {Q : Set ℂ} (hQ : Bornology.IsBounded Q) (c : ℂ)
    (h311 : DGLem311Scaled P W μ γ d Q) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ lam C : ℝ, 0 < lam ∧ ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      P {ω | ∃ x ∈ l313Grid Q c m, ¬ (l313Set (μ ω) ε
          (l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Left ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Right ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤
        ENNReal.ofReal (l313Tgt γ d ζ ε m (sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ m) 1 z ω)
          '' l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)))} ≤
        ENNReal.ofReal (C * Real.exp (-(lam * m))) :=
  dg_lemma313_core hW hγ hd (l313Grid_card Q c) hQ
    (fun m x hx => (Finset.mem_filter.1 hx).2)
    (fun m x _ => ⟨_, l313_corner_mem _ (by positivity) _⟩) (by norm_num : (1 : ℝ) ≤ 5)
    (fun m x _ z hz w hw => l313Str_diam (by positivity) _ hz hw)
    (l313Hyp_of_scaled c h311) hζ hζ1

/-- **DG Lemma 3.14** (DG:1328–1336) for the horizontal grid rectangles with `R' ⊆ Q` -/
theorem dg_lemma314 (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ} {Q : Set ℂ} (hQ : Bornology.IsBounded Q) (c : ℂ)
    (h311 : DGLem311Scaled P W μ γ d Q) {ζ β : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (hβ : 0 < β) :
    ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P {ω | ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β ∧ ∃ x ∈ l313Grid Q c m, ¬ (l313Set (μ ω) ε
          (l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Left ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Right ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζ))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζ) * m / d))))} ≤ ENNReal.ofReal (C * ε ^ p) :=
  dg_lemma314_core hW hγ hd (l313Grid_card Q c) hQ
    (fun m x hx => (Finset.mem_filter.1 hx).2)
    (fun m x _ => ⟨_, l313_corner_mem _ (by positivity) _⟩) (by norm_num : (1 : ℝ) ≤ 5)
    (fun m x _ z hz w hw => l313Str_diam (by positivity) _ hz hw)
    (l313Hyp_of_scaled c h311) hζ hζ1 hβ

end DG
end LQGMetric
