/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32F2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32F1

/-!
# DZZ (eq-B-percolation-Psi) at `μIn`, one box, explicit parameters (P2-DZZ32F)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1104–1147), with `ε = 2^{-k}`, `t/ε = 2^{-ℓ}`,
`𝓑'_i = 𝓑_∂(B'_i, t/ε)`:

* `openBad`: the complement of `𝓔_{B'_i, open}` ("`M̃_{γ,ε²s,η}(B̃) ≤ θ` for all `B̃ ∈ 𝓑'_i`").
* `measure_openBad_le`: `P(𝓔^c_{B'_i,open}) ≤ |𝓑'_i| (ts)²/θ` (l. 1122–1130, (Eq.LQG-tildeM) and
  a union bound), with `|𝓑_∂(B', 2^{-ℓ})| ≤ 8 (2^ℓ + 2)` (`boxCollBdry_ncard_le`).
* `measurableSet_openBad`, `disjoint_thickening_bdryU`: the independence of far sites (l. 1140:
  "independent if `|B'_i − B'_{i'}| ≥ 2εs`"), via the finite range of `η` (`etaRad_le_bandHalf`)
  and `measure_biInter_eq_prod_wnSigma`.
* **`p32_enc_box`**: (eq-B-percolation-Psi) for one box `B`, all parameters explicit: on `G`
  (where (eq-M-tilde-B-bound) holds for `B`), `𝓔_{B'_i,open} ⊆ {Φ^W_{B'_i} ≤ λ}` by
  `phiLeW_of_open` (l. 1131–1139), then the percolation core `enc_core_gen` (l. 1144–1147).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `𝓑_∂(b', 2^{-ℓ})` as a finset. -/
def bdryT (b' : DyBox) (ℓ : ℕ) : Finset DyBox := (boxCollBdry_finite b' ℓ).toFinset

lemma mem_bdryT {b' b : DyBox} {ℓ : ℕ} : b ∈ bdryT b' ℓ ↔ b ∈ boxCollBdry b' ℓ := by
  simp [bdryT]

/-- The union of the boxes of `𝓑_∂(b', 2^{-ℓ})`. -/
def bdryU (b' : DyBox) (ℓ : ℕ) : Set ℂ := ⋃ b ∈ bdryT b' ℓ, b.closedBox

variable (W) in
/-- `𝓔^c_{B',open}`: some `B̃ ∈ 𝓑_∂(B', 2^{-ℓ})` has `M̃_{γ,δh,η}(B̃) ≥ θ`. -/
def openBad (γ δh : ℝ) (θ : ℝ≥0∞) (ℓ : ℕ) (b' : DyBox) : Set Ω :=
  {ω | ∃ b ∈ bdryT b' ℓ, θ ≤ etaChaos W γ δh b.closedBox ω}

lemma volume_closedBox_eq (b : DyBox) : volume b.closedBox = ENNReal.ofReal (b.side ^ 2) := by
  have h := (Complex.volume_preserving_equiv_real_prod).measure_preimage
    (s := Icc (b.j * b.side) ((b.j + 1) * b.side) ×ˢ Icc (b.k * b.side) ((b.k + 1) * b.side))
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet
  have e : Complex.measurableEquivRealProd ⁻¹'
      (Icc (b.j * b.side) ((b.j + 1) * b.side) ×ˢ Icc (b.k * b.side) ((b.k + 1) * b.side)) =
      b.closedBox := by
    ext z; simp [Complex.measurableEquivRealProd, DyBox.closedBox]; tauto
  rw [e] at h
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by have := b.side_pos'; nlinarith)]
  congr 1; ring

/-- **DZZ l. 1122–1130**: `P(𝓔^c_{B',open}) ≤ 8 (2^ℓ + 2) · (2^{-(n'+ℓ)})² / θ`. -/
lemma measure_openBad_le (hW : IsWhiteNoise P W) (γ δh : ℝ) (ℓ : ℕ) (b' : DyBox)
    {θ : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθ : θ ≠ ⊤) :
    P (openBad W γ δh θ ℓ b') ≤
      ((8 * (2 ^ ℓ + 2) : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (b'.n + ℓ)) ^ 2) / θ) := by
  refine (measure_exists_etaChaos_ge_le hW γ δh (bdryT b' ℓ) hθ0 hθ).trans ?_
  have hc : ∀ b ∈ bdryT b' ℓ, volume b.closedBox / θ =
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (b'.n + ℓ)) ^ 2) / θ := by
    intro b hb
    rw [volume_closedBox_eq, side_bdry (mem_bdryT.1 hb)]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  gcongr
  have h1 : (bdryT b' ℓ).card = (boxCollBdry b' ℓ).ncard := by
    rw [bdryT, Set.ncard_eq_toFinset_card _ (boxCollBdry_finite b' ℓ)]
  exact_mod_cast h1 ▸ boxCollBdry_ncard_le b' ℓ

lemma measurableSet_openBad (hW : IsWhiteNoise P W) {δh R ρ : ℝ}
    (hR : ∀ u ∈ Ioo 0 (δh ^ 2), etaRad u ≤ R) (hρ : 0 < ρ) (γ : ℝ) (θ : ℝ≥0∞) (ℓ : ℕ)
    (b' : DyBox) :
    MeasurableSet[wnSigma W (etaReg R ρ (bdryU b' ℓ))] (openBad W γ δh θ ℓ b') := by
  have e : openBad W γ δh θ ℓ b' = ⋃ b ∈ bdryT b' ℓ, {ω | θ ≤ etaChaos W γ δh b.closedBox ω} := by
    ext ω; simp [openBad]
  rw [e]
  refine Finset.measurableSet_biUnion _ fun b hb => ?_
  have hm := (measurable_etaChaos_loc hW hR hρ γ (isClosed_closedBox_eta b).measurableSet).mono
    (wnSigma_mono (prod_mono subset_rfl (thickening_subset_of_subset _
      (subset_biUnion_of_mem (u := fun b => DyBox.closedBox b) hb)))) le_rfl
  exact hm measurableSet_Ici

lemma re_gap_pt {b1 b2 bt1 bt2 : DyBox} {ℓ : ℕ} (hn : b1.n = b2.n)
    (h1 : bt1 ∈ boxCollBdry b1 ℓ) (h2 : bt2 ∈ boxCollBdry b2 ℓ) (hj : b1.j + 3 + 1 ≤ b2.j)
    {q1 q2 : ℂ} (hq1 : q1 ∈ bt1.closedBox) (hq2 : q2 ∈ bt2.closedBox) :
    3 * b1.side - 2 * (2 : ℝ)⁻¹ ^ (b1.n + ℓ) ≤ q2.re - q1.re := by
  obtain ⟨z1, hz1, hzB1⟩ := bdry_point h1
  obtain ⟨z2, hz2, hzB2⟩ := bdry_point h2
  have a1 := (abs_sub_le_of_mem_closedBox hq1 hz1).1
  have a2 := (abs_sub_le_of_mem_closedBox hq2 hz2).1
  rw [side_bdry h1] at a1; rw [side_bdry h2, ← hn] at a2
  have hs : b2.side = b1.side := by unfold DyBox.side; rw [hn]
  have c1 := hzB1.2.1
  have c2 := hzB2.1
  rw [hs] at c2
  have hjr : (b1.j : ℝ) + 3 + 1 ≤ b2.j := by exact_mod_cast hj
  have := b1.side_pos'
  rw [abs_le] at a1 a2
  nlinarith

lemma im_gap_pt {b1 b2 bt1 bt2 : DyBox} {ℓ : ℕ} (hn : b1.n = b2.n)
    (h1 : bt1 ∈ boxCollBdry b1 ℓ) (h2 : bt2 ∈ boxCollBdry b2 ℓ) (hk : b1.k + 3 + 1 ≤ b2.k)
    {q1 q2 : ℂ} (hq1 : q1 ∈ bt1.closedBox) (hq2 : q2 ∈ bt2.closedBox) :
    3 * b1.side - 2 * (2 : ℝ)⁻¹ ^ (b1.n + ℓ) ≤ q2.im - q1.im := by
  obtain ⟨z1, hz1, hzB1⟩ := bdry_point h1
  obtain ⟨z2, hz2, hzB2⟩ := bdry_point h2
  have a1 := (abs_sub_le_of_mem_closedBox hq1 hz1).2
  have a2 := (abs_sub_le_of_mem_closedBox hq2 hz2).2
  rw [side_bdry h1] at a1; rw [side_bdry h2, ← hn] at a2
  have hs : b2.side = b1.side := by unfold DyBox.side; rw [hn]
  have c1 := hzB1.2.2.2
  have c2 := hzB2.2.2.1
  rw [hs] at c2
  have hkr : (b1.k : ℝ) + 3 + 1 ≤ b2.k := by exact_mod_cast hk
  have := b1.side_pos'
  rw [abs_le] at a1 a2
  nlinarith

/-- far sites have disjoint `a`-thickenings of their boundary layers -/
lemma disjoint_thickening_bdryU {b1 b2 : DyBox} (hn : b1.n = b2.n) {ℓ : ℕ} {a : ℝ}
    (hfar : b1.j + 3 + 1 ≤ b2.j ∨ b2.j + 3 + 1 ≤ b1.j ∨ b1.k + 3 + 1 ≤ b2.k ∨
      b2.k + 3 + 1 ≤ b1.k)
    (ha : 2 * a + 2 * (2 : ℝ)⁻¹ ^ (b1.n + ℓ) ≤ 3 * b1.side) :
    Disjoint (thickening a (bdryU b1 ℓ)) (thickening a (bdryU b2 ℓ)) := by
  have hs : b2.side = b1.side := by unfold DyBox.side; rw [hn]
  rw [Set.disjoint_left]
  intro p hp1 hp2
  rw [mem_thickening_iff] at hp1 hp2
  obtain ⟨q1, hq1, d1⟩ := hp1
  obtain ⟨q2, hq2, d2⟩ := hp2
  simp only [bdryU, mem_iUnion, exists_prop] at hq1 hq2
  obtain ⟨bt1, hbt1, hq1⟩ := hq1
  obtain ⟨bt2, hbt2, hq2⟩ := hq2
  rw [mem_bdryT] at hbt1 hbt2
  have hd : dist q1 q2 < 2 * a := by
    have := dist_triangle_left q1 q2 p; linarith
  rw [Complex.dist_eq] at hd
  have hre := Complex.abs_re_le_norm (q1 - q2)
  have him := Complex.abs_im_le_norm (q1 - q2)
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rw [abs_le] at hre him
  rcases hfar with h | h | h | h
  · have := re_gap_pt hn hbt1 hbt2 h hq1 hq2; linarith
  · have := re_gap_pt hn.symm hbt2 hbt1 h hq2 hq1
    rw [hs, ← hn] at this; linarith
  · have := im_gap_pt hn hbt1 hbt2 h hq1 hq2; linarith
  · have := im_gap_pt hn.symm hbt2 hbt1 h hq2 hq1
    rw [hs, ← hn] at this; linarith

/-- **DZZ (eq-B-percolation-Psi) at `μIn` for one box, explicit parameters** (l. 1104–1147). -/
theorem p32_enc_box (hW : IsWhiteNoise P W) {γ : ℝ} {B : DyBox} {k h ℓ : ℕ}
    (hK : 2 ^ k = 2 * h) (h4 : 4 ≤ h) (hB1 : 1 ≤ B.n) {δ r lam : ℝ} (hr : 0 < r)
    (hlam : (4 * (2 ^ ℓ + 1) : ℝ) ≤ lam) {K θo θ : ℝ≥0∞}
    (hKθ : 4 * (K * θo) ≤ ENNReal.ofReal (δ ^ 2)) (hθo0 : θo ≠ 0) (hθoT : θo ≠ ⊤)
    (G : Set Ω)
    (hup : ∀ ω ∈ G, ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - B.center‖ ≤ 3 * B.side) →
      wickQArea γ W ω b'.closedBox ≤ K * etaChaos W γ ((2 : ℝ)⁻¹ ^ (B.n + 2 * k)) b'.closedBox ω)
    (hRs : 2 * (((2 : ℝ)⁻¹ ^ (B.n + 2 * k) * Real.log ((2 : ℝ)⁻¹ ^ (B.n + 2 * k))⁻¹ +
        (2 : ℝ)⁻¹ ^ (B.n + 2 * k)) / 2) + 2 * (2 : ℝ)⁻¹ ^ (B.n + k + ℓ) <
      3 * (2 : ℝ)⁻¹ ^ (B.n + k))
    (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ((8 * (2 ^ ℓ + 2) : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (B.n + k + ℓ)) ^ 2) / θo) ≤ θ ^ ((3 + 1) ^ 2)) :
    P (G ∩ {ω | ¬ HasEnclosure B k fun b' => PhiLeW (dzzMuIn γ W ω) δ r b' lam}) ≤
      4 * ((2 * (2 * h - 2) + 1 : ℕ) * (8 * θ) ^ ((2 * h - 2) - (h + 2) + 1)) := by
  set δh : ℝ := (2 : ℝ)⁻¹ ^ (B.n + 2 * k) with hδh
  set R : ℝ := (δh * Real.log δh⁻¹ + δh) / 2 with hRdef
  have hδh0 : 0 < δh := by positivity
  have hδh1 : δh ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hR : ∀ u ∈ Ioo 0 (δh ^ 2), etaRad u ≤ R := etaRad_le_bandHalf hδh0 hδh1
  set ρ : ℝ := (3 * (2 : ℝ)⁻¹ ^ (B.n + k) - 2 * R - 2 * (2 : ℝ)⁻¹ ^ (B.n + k + ℓ)) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hK; omega
    · exact h0
  refine enc_core_gen P B hK h4 hB1 (openBad W γ δh θo ℓ) _ G hθ hεθ
    (fun b' hb' => by
      have := measure_openBad_le hW γ δh ℓ b' hθo0 hθoT
      rwa [hb'.1] at this)
    (fun F hF hfar => le_of_eq (measure_biInter_eq_prod_wnSigma hW F
      (fun b' => etaReg R ρ (bdryU b' ℓ)) _ (fun b1 hb1 b2 hb2 hne => ?_)
      (fun b' _ => measurableSet_openBad hW hR hρ0 γ θo ℓ b'))) (fun ω hG b' hb' hnot => ?_)
  · refine Set.disjoint_prod.2 (Or.inr ?_)
    have hn : b1.n = b2.n := (hF b1 hb1).1.trans (hF b2 hb2).1.symm
    refine disjoint_thickening_bdryU hn (hfar b1 hb1 b2 hb2 hne) ?_
    rw [(hF b1 hb1).1, DyBox.side, (hF b1 hb1).1, hρ]
    linarith
  · have hopen : ∀ b ∈ boxCollBdry b' ℓ, etaChaos W γ δh b.closedBox ω ≤ θo := by
      intro b hb
      by_contra hc
      exact hnot ⟨b, mem_bdryT.2 hb, (not_le.1 hc).le⟩
    have hlev : (2⁻¹ : ℝ) ^ (b'.n + ℓ) ≤ B.side / 2 := by
      rw [hb'.1, DyBox.side, div_eq_mul_inv, ← pow_succ]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact phiLeW_of_open (hup ω hG) hb'.2 hlev (by rw [hb'.1]; omega) hr hopen hKθ hlam

end DZZ
end LQGMetric
