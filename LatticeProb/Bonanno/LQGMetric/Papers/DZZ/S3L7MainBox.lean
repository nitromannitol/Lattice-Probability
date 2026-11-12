/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7MainBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7CountPsi

/-!
# DZZ Lemma 3.7: open boxes are good (P2-DZZ3E)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of Lemma 3.7, l. 975–996:
"`{M_s(B) ≤ δ²} ∩ 𝓔_{δ,α} ∩ 𝓔_{B'_i, open} ⊆ {Ψ_{B'_i, δ'} ≤ λ}`".

* `center_near_of_boxColl`: the boxes `B̃ ∈ 𝓑_∂(B'_i, ·)` of `B'_i ∈ 𝓑(B, ε)` have centres within
  `8 s_B` of `c_B` (they lie in `𝓑(B,t) ∪ 𝓑_∂(B_large,t)`, l. 978).
* `psiLe_of_boxOpen`: on `nbrFineEvent ∩ decompEvent ∩ {M_s(B) ≤ δ²} ∩ 𝓔_{B',open}`, if the mass
  bound of (eq-LQG-tilde-B-Phi) is `< δ'²`, then `Ψ_{B',δ'} ≤ 8 (2^{k''} + 2)`
  (`approxLQG_fine_le_of_mem` + `psiLe_of_bdry`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

lemma abs_sub_center_re_le {b : DyBox} {z : ℂ} (hz : z ∈ b.closedBox) :
    |z.re - b.center.re| ≤ b.side := by
  obtain ⟨h1, h2, -, -⟩ := hz
  have := b.side_pos'
  simp only [DyBox.center]
  rw [abs_le]; constructor <;> nlinarith

lemma abs_sub_center_im_le {b : DyBox} {z : ℂ} (hz : z ∈ b.closedBox) :
    |z.im - b.center.im| ≤ b.side := by
  obtain ⟨-, -, h3, h4⟩ := hz
  have := b.side_pos'
  simp only [DyBox.center]
  rw [abs_le]; constructor <;> nlinarith

/-- Boxes of `𝓑_∂(B', ·)`, `B' ∈ 𝓑(B, ε)`, have centres within `8 s_B` of `c_B`. -/
lemma center_near_of_boxColl {B B' bt : DyBox} {k k'' : ℕ} (hB' : B' ∈ boxColl B k)
    (hbt : bt ∈ boxCollBdry B' k'') : ‖B.center - bt.center‖ ≤ 8 * B.side := by
  obtain ⟨z, hzbt, hzf⟩ := hbt.2
  have hzB' : z ∈ B'.closedBox := (isClosed_closedBox B').frontier_subset hzf
  obtain ⟨hre, him⟩ := hB'.2 hzB'
  have hs : bt.side ≤ B.side := inv_two_pow_le_side (by rw [hbt.1, hB'.1]; omega)
  have h1 := abs_sub_center_re_le hzbt
  have h2 := abs_sub_center_im_le hzbt
  have hB0 := B.side_pos'
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have e1 : |B.center.re - bt.center.re| ≤ 2 * B.side := by
    calc |B.center.re - bt.center.re| = |(z.re - bt.center.re) - (z.re - B.center.re)| := by
          ring_nf
      _ ≤ |z.re - bt.center.re| + |z.re - B.center.re| := abs_sub _ _
      _ ≤ 2 * B.side := by linarith
  have e2 : |B.center.im - bt.center.im| ≤ 2 * B.side := by
    calc |B.center.im - bt.center.im| = |(z.im - bt.center.im) - (z.im - B.center.im)| := by
          ring_nf
      _ ≤ |z.im - bt.center.im| + |z.im - B.center.im| := abs_sub _ _
      _ ≤ 2 * B.side := by linarith
  linarith

lemma side_div_of_boxColl {B B' bt : DyBox} {k k'' : ℕ} (hB' : B' ∈ boxColl B k)
    (hbt : bt ∈ boxCollBdry B' k'') : bt.side / B.side = (2 : ℝ)⁻¹ ^ (k + k'') := by
  unfold DyBox.side
  rw [hbt.1, hB'.1, add_assoc, pow_add]
  field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Open boxes are good** (DZZ l. 990–996): on `nbrFineEvent ∩ decompEvent ∩ {M_s(B) ≤ δ²}`, if
`B' ∈ 𝓑(B, 2^{-k})` is open (band exponent `< a` on `𝓑_∂(B', 2^{-k''})`, band from level
`B.n + j`, `j ≤ k + k''`) and the mass bound of (eq-LQG-tilde-B-Phi) is `< δ'²`, then
`Ψ_{B',δ'} ≤ 8 (2^{k''} + 2)`. -/
theorem psiLe_of_boxOpen (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    {Cmc α δ δ' a : ℝ} {ω : Ω} (hE : ω ∈ nbrFineEvent W Cmc α δ) (hdec : ω ∈ decompEvent W)
    {B B' : DyBox} {k k'' j : ℕ} (hm : (2 : ℝ) ^ B.n ≤ δ ^ (-Cmc))
    (hjY : (2 : ℝ) ^ j ≤ (α * Real.log δ⁻¹) ^ 2) (hjk : j ≤ k + k'')
    (hM : approxLQG γ W ω B ≤ δ ^ 2) (hB' : B' ∈ boxColl B k)
    (hopen : ω ∈ boxOpen γ W B' k'' (B.n + j) a)
    (hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ (k + k'')) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log B.side⁻¹ + 4))) * Real.exp a <
      δ' ^ 2) :
    PsiLe (approxLQG γ W ω) δ' B' (8 * (2 ^ k'' + 2)) := by
  refine psiLe_of_bdry _ _ B' k'' fun bt hbt => ?_
  have hj : B.n + j ≤ bt.n := by rw [hbt.1, hB'.1]; omega
  refine (approxLQG_fine_le_of_mem hW hγ hE hdec hm hjY hj (center_near_of_boxColl hB' hbt) hM
    (hopen bt hbt).le).trans_lt ?_
  rwa [side_div_of_boxColl hB' hbt]

end DZZ
end LQGMetric
