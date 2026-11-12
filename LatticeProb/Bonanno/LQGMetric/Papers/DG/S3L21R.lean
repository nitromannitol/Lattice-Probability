/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L21R at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L21
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13R
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# DG Lemma 3.21 for the dyadic squares of side `δ_ε` (P2-DG105i)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.21 (DG:1678–1687), for
the squares `S = u + [0, δ_ε]²`, `δ_ε = 2^{-⌈log₂ ε^{-β}⌉}`, with corner
`u ∈ c + δ_ε{0,…,2^M−1}²` and `S(1) = u + [−δ_ε, 2δ_ε]² ⊆ Q` (DG: `S ⊆ 𝕊(1)`, corners in
`δ_ε ℤ²`), and DG's unrestricted distance `D^ε(S, ∂S(1))`.

The input is DG Lemma 3.19 at scale `s = 2^{-j}` transported by (3.7) (`DGLem319Scaled`, the
form of `L321Hyp` for the annuli `s𝒜_n + b`, DG:1614–1619, 1699–1706).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise Classical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the inner square `b + [0, sn]²` of `s𝒜_n + b` (DG:1614) -/
def l321In (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  Icc b.re (b.re + s * n) ×ℂ Icc b.im (b.im + s * n)

/-- the outer square `b + [−sn, 2sn]²` of `s𝒜_n + b` -/
def l321Out (s : ℝ) (b : ℂ) (n : ℕ) : Set ℂ :=
  Icc (b.re - s * n) (b.re + 2 * (s * n)) ×ℂ Icc (b.im - s * n) (b.im + 2 * (s * n))

/-- **DG Lemma 3.19 at scale `2^{-j}`, transported by (3.7)** (DG:1614–1619, 1699–1706;
D105 item 1) -/
def DGLem319Scaled (P : Measure Ω) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (γ d : ℝ)
    (Q : Set ℂ) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ a₀ a₁ εs : ℝ, 0 < a₁ ∧ 0 < εs ∧ ∀ (j n : ℕ) (b : ℂ),
    l321Out ((2 : ℝ)⁻¹ ^ j) b n ⊆ Q → ∀ ε : ℝ, 0 < ε →
    P {ω | ε * ((((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ * Real.exp (-(γ * sInf
          ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) '' l321Out ((2 : ℝ)⁻¹ ^ j) b n)))) ≤
        εs ∧
      (l313Set (μ ω) ε univ (l321In ((2 : ℝ)⁻¹ ^ j) b n)
        (frontier (l321Out ((2 : ℝ)⁻¹ ^ j) b n)) : ℝ≥0∞) <
      ENNReal.ofReal (Real.exp (-√(n : ℝ)) * (ε * ((((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ *
        Real.exp (-(γ * sInf ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) ''
          l321Out ((2 : ℝ)⁻¹ ^ j) b n))))) ^ (-(1 / (d + ζ₁))))} ≤
      ENNReal.ofReal (a₀ * Real.exp (-(a₁ * n)))

/-- `M_ε = ⌈log₂ ε^{-β}⌉`, `δ_ε = 2^{-M_ε}` (DG:1682) -/
def l321M (β ε : ℝ) : ℕ := ⌈β * Real.logb 2 ε⁻¹⌉₊

lemma l321_two_pow (M : ℕ) : (2 : ℝ)⁻¹ ^ M = (2 : ℝ) ^ (-(M : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]

lemma l321_eps_pow {β ε : ℝ} (hε : 0 < ε) :
    ε ^ β = (2 : ℝ) ^ (-(β * Real.logb 2 ε⁻¹)) := by
  rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos (by norm_num), Real.logb, Real.log_inv]
  congr 1
  have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

lemma l321M_le {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hε1 : ε < 1) :
    (2 : ℝ)⁻¹ ^ l321M β ε ≤ ε ^ β ∧ ε ^ β ≤ 2 * (2 : ℝ)⁻¹ ^ l321M β ε := by
  have hx : 0 ≤ β * Real.logb 2 ε⁻¹ :=
    mul_nonneg hβ.le (Real.logb_nonneg (by norm_num) (one_le_inv_iff₀.2 ⟨hε, hε1.le⟩))
  rw [l321_two_pow, l321_eps_pow hε]
  refine ⟨Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (Nat.le_ceil _)), ?_⟩
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (-(l321M β ε : ℝ)) = (2 : ℝ) ^ (1 - (l321M β ε : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]; ring
  rw [h2]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have := Nat.ceil_lt_add_one hx
  unfold l321M; linarith

/-- the squares of side `δ_ε` with `S(1) ⊆ Q` -/
def l321Grid (Q : Set ℂ) (c : ℂ) (β ε : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (2 ^ l321M β ε) ×ˢ Finset.range (2 ^ l321M β ε)).filter
    fun x => l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1 ⊆ Q

lemma l321_scale_sets (M k : ℕ) (b : ℂ) :
    l321In ((2 : ℝ)⁻¹ ^ (M + k)) b (2 ^ k) = l321In ((2 : ℝ)⁻¹ ^ M) b 1 ∧
      l321Out ((2 : ℝ)⁻¹ ^ (M + k)) b (2 ^ k) = l321Out ((2 : ℝ)⁻¹ ^ M) b 1 := by
  unfold l321In l321Out; rw [l313_scale_eq]; exact ⟨rfl, rfl⟩

/-- `DGLem319Scaled` gives `L321Hyp` for the grid squares (DG:1699–1702) -/
theorem l321Hyp_of_scaled {μ : Ω → Measure ℂ} {γ d β : ℝ} {Q : Set ℂ} (c : ℂ)
    (h : DGLem319Scaled P W μ γ d Q) :
    L321Hyp P W γ d (l321Grid Q c β) (l321M β)
      (fun ε x => l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)
      (fun ε x ω => (l313Set (μ ω) ε univ
        (l321In ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)
        (frontier (l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)) : ℝ≥0∞)) := by
  intro ζ₁ h0 h1
  obtain ⟨a₀, a₁, εs, ha₁, hεs, hh⟩ := h ζ₁ h0 h1
  refine ⟨a₀, a₁, εs, ha₁, hεs, fun ε hε x hx k => ?_⟩
  obtain ⟨hIn, hOut⟩ := l321_scale_sets (l321M β ε) k (l313Corner c (l321M β ε) x)
  have hQ : l321Out ((2 : ℝ)⁻¹ ^ (l321M β ε + k)) (l313Corner c (l321M β ε) x) (2 ^ k) ⊆ Q := by
    rw [hOut]; exact (Finset.mem_filter.1 hx).2
  have := hh (l321M β ε + k) (2 ^ k) (l313Corner c (l321M β ε) x) hQ ε hε
  rw [hIn, hOut] at this
  push_cast at this
  convert this using 4 <;> simp only [l321Thr, l321X] <;> ring_nf

lemma l321Out_diam {δ : ℝ} (b : ℂ) {z w : ℂ} (hz : z ∈ l321Out δ b 1)
    (hw : w ∈ l321Out δ b 1) : ‖z - w‖ ≤ 6 * δ := by
  simp only [l321Out, Nat.cast_one, mul_one, Complex.mem_reProdIm, mem_Icc] at hz hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have h1 : |z.re - w.re| ≤ 3 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |z.im - w.im| ≤ 3 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

lemma l321_corner_mem (δ : ℝ) (hδ : 0 ≤ δ) (b : ℂ) : b ∈ l321Out δ b 1 := by
  simp only [l321Out, Nat.cast_one, mul_one, Complex.mem_reProdIm, mem_Icc]
  constructor <;> constructor <;> linarith

lemma l321Grid_card (Q : Set ℂ) (c : ℂ) {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hε1 : ε < 1) :
    ((l321Grid Q c β ε).card : ℝ) ≤ 4 * ε ^ (-(2 * β)) := by
  have h := Finset.card_filter_le (Finset.range (2 ^ l321M β ε) ×ˢ Finset.range (2 ^ l321M β ε))
    fun x => l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1 ⊆ Q
  rw [Finset.card_product, Finset.card_range] at h
  have h1 : ((l321Grid Q c β ε).card : ℝ) ≤ (2 : ℝ) ^ l321M β ε * 2 ^ l321M β ε := by
    exact_mod_cast h
  have h2 : (2 : ℝ) ^ l321M β ε ≤ 2 * ε ^ (-β) := by
    have hM := (l321M_le hβ hε hε1).2
    have e : (2 : ℝ) ^ l321M β ε * (2⁻¹ ^ l321M β ε) = 1 := by rw [← mul_pow]; norm_num
    have hεβ : ε ^ β * ε ^ (-β) = 1 := by rw [← Real.rpow_add hε]; simp
    calc (2 : ℝ) ^ l321M β ε = (2 : ℝ) ^ l321M β ε * (ε ^ β * ε ^ (-β)) := by rw [hεβ, mul_one]
      _ = ((2 : ℝ) ^ l321M β ε * ε ^ β) * ε ^ (-β) := by ring
      _ ≤ ((2 : ℝ) ^ l321M β ε * (2 * 2⁻¹ ^ l321M β ε)) * ε ^ (-β) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by positivity)) (by positivity)
      _ = 2 * ε ^ (-β) := by rw [mul_left_comm, e, mul_one]
  have h3 : ε ^ (-(2 * β)) = ε ^ (-β) * ε ^ (-β) := by
    rw [← Real.rpow_add hε]; ring_nf
  rw [h3]
  calc ((l321Grid Q c β ε).card : ℝ) ≤ (2 : ℝ) ^ l321M β ε * 2 ^ l321M β ε := h1
    _ ≤ (2 * ε ^ (-β)) * (2 * ε ^ (-β)) := mul_le_mul h2 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- **DG Lemma 3.21** (DG:1678–1687) for the grid squares `S` of side `δ_ε` with `S(1) ⊆ Q`
(`Q` bounded): for `β ∈ (0, 2/(2+γ)²)`, with polynomially high probability as `ε → 0`,
`D^ε(S, ∂S(1)) ≥ ε^{-1/d + β(2+γ²/2)/d + ζ} exp((γ/d) max_{S(1)} ĥ_{ε^β})` for every such `S` -/
theorem dg_lemma321 (hW : IsWhiteNoise P W) {γ d β : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    (hβ : 0 < β) (hβγ : β < 2 / (2 + γ) ^ 2) {μ : Ω → Measure ℂ} {Q : Set ℂ}
    (hQ : Bornology.IsBounded Q) (c : ℂ) (h319 : DGLem319Scaled P W μ γ d Q) {ζ : ℝ}
    (hζ : 0 < ζ) :
    ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P {ω | ∃ x ∈ l321Grid Q c β ε, (l313Set (μ ω) ε univ
          (l321In ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)
          (frontier (l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)) : ℝ≥0∞) <
        ENNReal.ofReal (l321Tgt γ d ζ β ε (sSup ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) ''
          l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)))} ≤
        ENNReal.ofReal (C * ε ^ p) := by
  obtain ⟨p, C, ε₀, hp, hε₀, h⟩ := dg_lemma321_core hW hγ hd hβ hβγ (Cn := 4)
    (Λ := l321Grid Q c β) (fun ε hε hε1 => l321Grid_card Q c hβ hε hε1)
    (fun ε hε hε1 => (l321M_le hβ hε hε1).1) (fun ε hε hε1 => (l321M_le hβ hε hε1).2) hQ
    (fun ε x hx => (Finset.mem_filter.1 hx).2)
    (fun ε x _ => ⟨_, l321_corner_mem _ (by positivity) _⟩) (by norm_num : (1 : ℝ) ≤ 6)
    (fun ε hε hε1 x _ z hz w hw => (l321Out_diam _ hz hw).trans
      (mul_le_mul_of_nonneg_left (l321M_le hβ hε hε1).1 (by norm_num)))
    (l321Hyp_of_scaled c h319) hζ
  exact ⟨p, C, ε₀, hp, hε₀, h⟩

end DG
end LQGMetric
