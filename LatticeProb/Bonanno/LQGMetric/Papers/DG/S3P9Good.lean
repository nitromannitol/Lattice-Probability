/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P9Good at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9An

/-!
# DG Proposition 3.9 on the good event (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, proof of Proposition 3.9 (DG:1346–1389), for one realization:
if the bounds of Lemma 3.14 hold for all grid rectangles of levels `m` with `2^{-m} ≤ ε^β`
(both orientations) and the balls `B(z, ε^{β̄})`, `z ∈ 𝕊`, have mass `≤ ε` (Lemma 3.8), then
`D^ε(z, w; Q) ≤ ε^{-1/(d−ζ)}` for all `z, w ∈ 𝕊` (`p39_good`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- the ENNReal bookkeeping of `p39_det` -/
lemma p39_ennreal {B x M0 : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) (J : ℕ) {f g : ℕ → ℝ}
    (hf : ∀ i < J, f i ≤ B) (hg : ∀ i < J, g i ≤ B) (h0 : M0 ≤ B) :
    2 + 2 * (ENNReal.ofReal M0 + ∑ i ∈ Finset.range J,
        (2 * ENNReal.ofReal (f i) + ENNReal.ofReal (g i))) +
      ENNReal.ofReal x * (4 * ENNReal.ofReal M0) ≤
      ENNReal.ofReal (2 + 2 * (B + J * (3 * B)) + x * (4 * B)) := by
  have e : ENNReal.ofReal (2 + 2 * (B + J * (3 * B)) + x * (4 * B)) =
      2 + 2 * (ENNReal.ofReal B + ∑ _i ∈ Finset.range J,
        (2 * ENNReal.ofReal B + ENNReal.ofReal B)) + ENNReal.ofReal x * (4 * ENNReal.ofReal B) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_add hB (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hx, ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
    ring
  rw [e]
  gcongr with i hi
  · exact hf i (Finset.mem_range.1 hi)
  · exact hg i (Finset.mem_range.1 hi)

/-- **DG Proposition 3.9 on the good event** (DG:1346–1389) -/
theorem p39_good {μ : Measure ℂ} {Q : Set ℂ} {c : ℂ} {L r γ d ζ ζt β βb ε : ℝ}
    (hL0 : 0 ≤ L) (hr : 0 < r) (hLr : L + r ≤ 1) (hQ : p39Box c L r ⊆ Q) (hε : 0 < ε)
    (hε1 : ε < 1) (hβ : 0 < β) (hβb : 0 < βb) (hεβ : ε ^ β ≤ r / 4) (hεβb : ε ^ βb ≤ r)
    (hd : 0 < d) (hζt : 0 < d - ζt) (hg : 1 / (d - ζ) = 2 * β + 1 / (d - ζt))
    (hc : 0 ≤ 2 + γ ^ 2 / 2 - 2 * γ - ζt)
    (hA : 120 * ((β + βb) * (2 / (β / 8)) + 5) ^ 4 ≤ (ε ^ (-(β / 8))) ^ 4)
    (hH : ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β → ∀ x ∈ l313Grid Q c m,
      (l313Set μ ε (l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Left ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Right ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζt))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζt) * m / d)))))
    (hV : ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β → ∀ x ∈ l313GridV Q c m,
      (l313Set μ ε (l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Bot ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
        (l313Top ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζt))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζt) * m / d)))))
    (hM : ∀ z ∈ p39Sq c L, μ (Metric.ball z (ε ^ βb)) ≤ ENNReal.ofReal ε) :
    ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L,
      (dgLGD μ ε Q z w : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-(1 / (d - ζ)))) := by
  set t := Real.logb 2 ε⁻¹ with ht_def
  set k₀ := ⌈β * t⌉₊ with hk₀
  set K := ⌈(β + βb) * t⌉₊ + 2 with hK
  set E := ε ^ (-(1 / (d - ζt))) with hE_def
  set Mf : ℕ → ℝ := fun m => max ((m : ℝ) ^ 3) (E *
    (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζt) * m / d))) with hMf
  obtain ⟨hk1, hk2⟩ := p39_k0 hε hε1 hβ
  obtain ⟨hkK, hKρ, hKt⟩ := p39_K hε hε1 hβ hβb
  rw [← ht_def, ← hk₀] at hk1 hk2
  rw [← ht_def, ← hk₀, ← hK] at hkK
  rw [← ht_def, ← hK] at hKρ hKt
  -- the crossing paths
  have h4 : 4 * p39d k₀ ≤ r := by linarith
  obtain ⟨KH, KV, HP⟩ := p39Hyp_of_event (μ := μ) (ε := ε) (Mf := Mf) hLr hQ h4
    (fun m hm x hx => hH m ((p39d_anti hm).trans hk1) x hx)
    (fun m hm x hx => hV m ((p39d_anti hm).trans hk1) x hx)
  have hJ : k₀ + (K - k₀) = K := by omega
  have hdet := p39_det HP (K - k₀) (ρ := ε ^ βb) (by rw [hJ]; exact hKρ) (fun z hz => ⟨?_, hM z hz⟩)
  rotate_left
  · intro y hy
    apply subset_closure
    apply hQ
    have hy' := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at hy'
    simp only [p39Sq, Complex.mem_reProdIm, mem_Icc] at hz
    have h1 := Complex.abs_re_le_norm (y - z)
    have h2 := Complex.abs_im_le_norm (y - z)
    rw [Complex.sub_re, abs_le] at h1
    rw [Complex.sub_im, abs_le] at h2
    simp only [p39Box, Complex.mem_reProdIm, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  intro z hz w hw
  refine (hdet z hz w hw).trans ?_
  -- the arithmetic
  have hE1 : 1 ≤ E := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le
    (by have := one_div_pos.2 hζt; linarith)
  set u := ε ^ (-β) with hu_def
  set v := ε ^ (-(β / 8)) with hv_def
  have hu1 : 1 ≤ u := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le (by linarith)
  have hv1 : 1 ≤ v := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le (by linarith)
  have hv8 : v ^ 8 = u := by
    rw [hv_def, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num [hu_def]
  set B := ((K : ℝ) + 2) ^ 3 + E with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hMfB : ∀ m : ℕ, m ≤ K + 1 → Mf m ≤ B := by
    intro m hm
    have hm' : (m : ℝ) ≤ K + 2 := by
      have : (m : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hm
      push_cast at this; linarith
    refine max_le ?_ ?_
    · have : (m : ℝ) ^ 3 ≤ ((K : ℝ) + 2) ^ 3 := pow_le_pow_left₀ (by positivity) hm' 3
      linarith
    · have : (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζt) * m / d)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (by have : 0 ≤ (2 + γ ^ 2 / 2 - 2 * γ - ζt) * m / d := by positivity
              linarith)
      have : 0 ≤ ((K : ℝ) + 2) ^ 3 := by positivity
      nlinarith
  have hx0 : 0 ≤ 4 * (L / p39d k₀) + 4 := by have := p39d_pos k₀; positivity
  refine (p39_ennreal hB0 hx0 (K - k₀) (f := fun i => Mf (k₀ + i + 1))
    (g := fun i => Mf (k₀ + i + 1 + 1)) (fun i hi => hMfB _ (by omega))
    (fun i hi => hMfB _ (by omega)) (hMfB _ (by omega))).trans ?_
  apply ENNReal.ofReal_le_ofReal
  -- `L / 2^{-k₀} ≤ 2^{k₀} ≤ 2u`
  have hk2' : L / p39d k₀ ≤ 2 * u := by
    have e : L / p39d k₀ = L * 2 ^ k₀ := by
      rw [div_eq_iff (p39d_pos k₀).ne']
      calc L = L * (p39d k₀ * 2 ^ k₀) := by rw [p39d_mul_two_pow, mul_one]
        _ = _ := by ring
    rw [e]
    have : (0 : ℝ) ≤ 2 ^ k₀ := by positivity
    nlinarith
  have hKv : (K : ℝ) + 2 ≤ ((β + βb) * (2 / (β / 8)) + 5) * v := by
    have hlog := p39_logb_le hε (show 0 < β / 8 by positivity)
    rw [← ht_def] at hlog
    have : (β + βb) * t ≤ (β + βb) * (2 / (β / 8) * v) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have : 0 ≤ (β + βb) * (2 / (β / 8)) := by positivity
    nlinarith
  have hfin := p39_alg (K := (K : ℝ)) (J := ((K - k₀ : ℕ) : ℝ)) (k2 := L / p39d k₀) (B := B)
    (E := E) (u := u) (v := v) (A := (β + βb) * (2 / (β / 8)) + 5)
    (by exact_mod_cast Nat.sub_le K k₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hk2'
    (by have := p39d_pos k₀; positivity) hu1 hE1 rfl hKv hA hv8 (by linarith) (by positivity)
  refine hfin.trans (le_of_eq ?_)
  rw [hg, hu_def, hE_def, ← Real.rpow_natCast, ← Real.rpow_mul hε.le, ← Real.rpow_add hε]
  congr 1
  push_cast; ring

end DG
end LQGMetric
