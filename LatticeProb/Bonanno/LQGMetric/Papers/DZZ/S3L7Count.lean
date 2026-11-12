/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7Count at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Indep

/-!
# DZZ Lemma 3.7: the count `|𝓑_∂(B', 2^{-k'})| ≤ 8(2^{k'} + 2)` and the bad-box bounds (P2-DZZ3E)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of Lemma 3.7, l. 975–995.

* `frontier_closedBox_sub`: the boundary of a closed dyadic box lies on its four edges.
* `boxCollBdry_finite`, `boxCollBdry_ncard_le`: `𝓑_∂(B', 2^{-k'})` is finite with at most
  `8 (2^{k'} + 2)` boxes (DZZ l. 980 use `|𝓑'_i| ≤ 8ε/t`; the `+2` counts the corner boxes,
  own elementary count).
* `measure_boxOpen_compl_le`: `P(𝓔_{B',open}ᶜ) ≤ 8 (2^{k'} + 2) e^{-a}` (union bound,
  `tail_bandNorm_finset`).
* `measure_biInter_band_bad_eq_prod`: the complement form of `measure_biInter_band_eq_prod`
  (independence of the bad events, DZZ (eq-B'-i-open)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

lemma isClosed_closedBox (b : DyBox) : IsClosed b.closedBox := by
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)))

/-- The boundary of a closed dyadic box lies on its four edges. -/
lemma frontier_closedBox_sub {b : DyBox} {z : ℂ} (hz : z ∈ frontier b.closedBox) :
    z ∈ b.closedBox ∧ (z.re = b.j * b.side ∨ z.re = (b.j + 1) * b.side ∨
      z.im = b.k * b.side ∨ z.im = (b.k + 1) * b.side) := by
  have hzc : z ∈ b.closedBox := (isClosed_closedBox b).frontier_subset hz
  refine ⟨hzc, ?_⟩
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2, h3, h4⟩ := hzc
  set O : Set ℂ := {w | (b.j : ℝ) * b.side < w.re ∧ w.re < (b.j + 1) * b.side ∧
    (b.k : ℝ) * b.side < w.im ∧ w.im < (b.k + 1) * b.side}
  have hO : IsOpen O :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)))
  have hOs : O ⊆ b.closedBox := fun w ⟨a1, a2, a3, a4⟩ => ⟨a1.le, a2.le, a3.le, a4.le⟩
  have hzO : z ∈ O := ⟨lt_of_le_of_ne h1 (Ne.symm hne.1), lt_of_le_of_ne h2 hne.2.1,
    lt_of_le_of_ne h3 (Ne.symm hne.2.2.1), lt_of_le_of_ne h4 hne.2.2.2⟩
  exact hz.2 (interior_maximal hOs hO hzO)

lemma l37_idx_bounds {a c d : ℕ} {s x : ℝ} (hs : 0 < s) (h1 : (a : ℝ) * s ≤ x)
    (h2 : x ≤ (a + 1) * s) (h3 : (c : ℝ) * s ≤ x) (h4 : x ≤ d * s) : c ≤ a + 1 ∧ a ≤ d := by
  constructor
  · have : (c : ℝ) ≤ a + 1 := le_of_mul_le_mul_right (h3.trans h2) hs
    exact_mod_cast this
  · have : (a : ℝ) ≤ d := le_of_mul_le_mul_right (h1.trans h4) hs
    exact_mod_cast this

lemma side_eq_pow_mul {b b' : DyBox} {k' : ℕ} (h : b'.n = b.n + k') :
    b.side = ((2 ^ k' : ℕ) : ℝ) * b'.side := by
  unfold DyBox.side; rw [h, pow_add]; push_cast
  rw [← mul_assoc, inv_pow (2 : ℝ) k', mul_comm ((2 : ℝ) ^ k'), mul_assoc,
    mul_inv_cancel₀ (by positivity), mul_one]

/-- The index box containing the indices of `𝓑_∂(B, 2^{-k'})`. -/
def bdryIdxK (bj bk K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc (bj * K - 1) (bj * K) ×ˢ Finset.Icc (bk * K - 1) (bk * K + K)) ∪
    (Finset.Icc (bj * K + K - 1) (bj * K + K) ×ˢ Finset.Icc (bk * K - 1) (bk * K + K))) ∪
  ((Finset.Icc (bj * K - 1) (bj * K + K) ×ˢ Finset.Icc (bk * K - 1) (bk * K)) ∪
    (Finset.Icc (bj * K - 1) (bj * K + K) ×ˢ Finset.Icc (bk * K + K - 1) (bk * K + K)))

/-- The index box containing the indices of `𝓑_∂(B, 2^{-k'})`. -/
def bdryIdx (b : DyBox) (k' : ℕ) : Finset (ℕ × ℕ) := bdryIdxK b.j b.k (2 ^ k')

lemma card_bdryIdxK_le (bj bk K : ℕ) : (bdryIdxK bj bk K).card ≤ 8 * (K + 2) := by
  unfold bdryIdxK
  refine (Finset.card_union_le _ _).trans ?_
  refine (add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)).trans ?_
  simp only [Finset.card_product, Nat.card_Icc]
  have e1 : bj * K + 1 - (bj * K - 1) ≤ 2 := by omega
  have e2 : bk * K + K + 1 - (bk * K - 1) ≤ K + 2 := by omega
  have e3 : bj * K + K + 1 - (bj * K + K - 1) ≤ 2 := by omega
  have e4 : bj * K + K + 1 - (bj * K - 1) ≤ K + 2 := by omega
  have e5 : bk * K + 1 - (bk * K - 1) ≤ 2 := by omega
  have e6 : bk * K + K + 1 - (bk * K + K - 1) ≤ 2 := by omega
  have := Nat.mul_le_mul e1 e2
  have := Nat.mul_le_mul e3 e2
  have := Nat.mul_le_mul e4 e5
  have := Nat.mul_le_mul e4 e6
  nlinarith

lemma card_bdryIdx_le (b : DyBox) (k' : ℕ) : (bdryIdx b k').card ≤ 8 * (2 ^ k' + 2) :=
  card_bdryIdxK_le _ _ _

lemma mem_bdryIdx {b b' : DyBox} {k' : ℕ} (hb' : b' ∈ boxCollBdry b k') :
    (b'.j, b'.k) ∈ bdryIdx b k' := by
  obtain ⟨hn, z, hz', hz⟩ := hb'
  obtain ⟨⟨c1, c2, c3, c4⟩, he⟩ := frontier_closedBox_sub hz
  obtain ⟨d1, d2, d3, d4⟩ := hz'
  have hs := side_eq_pow_mul hn
  have hs' := DyBox.side_pos' b'
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ k' = K := ⟨_, rfl⟩
  rw [hK] at hs
  rw [hs] at c1 c2 c3 c4 he
  have cast1 : ∀ x : ℕ, (x : ℝ) * ((K : ℝ) * b'.side) = ((x * K : ℕ) : ℝ) * b'.side := by
    intro x; push_cast; ring
  have cast2 : ∀ x : ℕ, ((x : ℝ) + 1) * ((K : ℝ) * b'.side) = ((x * K + K : ℕ) : ℝ) * b'.side := by
    intro x; push_cast; ring
  rw [cast1] at c1 c3; rw [cast2] at c2 c4
  have hre := l37_idx_bounds hs' d1 d2 c1 c2
  have him := l37_idx_bounds hs' d3 d4 c3 c4
  unfold bdryIdx; rw [hK]; unfold bdryIdxK
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Icc]
  rcases he with h | h | h | h
  · rw [cast1] at h
    have := l37_idx_bounds hs' d1 d2 h.symm.le h.le
    left; left; omega
  · rw [cast2] at h
    have := l37_idx_bounds hs' d1 d2 h.symm.le h.le
    left; right; omega
  · rw [cast1] at h
    have := l37_idx_bounds hs' d3 d4 h.symm.le h.le
    right; left; omega
  · rw [cast2] at h
    have := l37_idx_bounds hs' d3 d4 h.symm.le h.le
    right; right; omega

lemma injOn_idx_boxCollBdry (b : DyBox) (k' : ℕ) :
    InjOn (fun b' : DyBox => (b'.j, b'.k)) (boxCollBdry b k') := by
  intro x hx y hy h
  simp only [Prod.mk.injEq] at h
  exact DyBox.ext (hx.1.trans hy.1.symm) h.1 h.2

theorem boxCollBdry_finite (b : DyBox) (k' : ℕ) : (boxCollBdry b k').Finite :=
  Set.Finite.of_finite_image ((bdryIdx b k').finite_toSet.subset (by
    rintro _ ⟨b', hb', rfl⟩; exact mem_bdryIdx hb')) (injOn_idx_boxCollBdry b k')

/-- **`|𝓑_∂(B, 2^{-k'})| ≤ 8 (2^{k'} + 2)`.** -/
theorem boxCollBdry_ncard_le (b : DyBox) (k' : ℕ) :
    (boxCollBdry b k').ncard ≤ 8 * (2 ^ k' + 2) := by
  refine le_trans ?_ (card_bdryIdx_le b k')
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn _ (fun b' hb' => mem_bdryIdx hb')
    (injOn_idx_boxCollBdry b k') (bdryIdx b k').finite_toSet

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`P(𝓔_{B',open}ᶜ) ≤ 8 (2^{k'} + 2) e^{-a}`** (DZZ (eq-berlin1), normalized form). -/
theorem measure_boxOpen_compl_le (hW : IsWhiteNoise P W) (γ : ℝ) (B' : DyBox) (k' N : ℕ)
    (a : ℝ) : P (boxOpen γ W B' k' N a)ᶜ ≤
      ENNReal.ofReal (8 * (2 ^ k' + 2) * Real.exp (-a)) := by
  have := hW.isProbabilityMeasure
  set S := (boxCollBdry_finite B' k').toFinset
  have hS : (S.card : ℝ) ≤ 8 * (2 ^ k' + 2) := by
    rw [← Set.ncard_eq_toFinset_card _ (boxCollBdry_finite B' k')]
    exact_mod_cast boxCollBdry_ncard_le B' k'
  have hsub : (boxOpen γ W B' k' N a)ᶜ ⊆ {ω | ∃ bt ∈ S, a ≤ bandNorm γ W bt N ω} := by
    intro ω hω
    simp only [boxOpen, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt] at hω
    obtain ⟨bt, hbt, h⟩ := hω
    exact ⟨bt, (Set.Finite.mem_toFinset _).2 hbt, h⟩
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ((tail_bandNorm_finset hW S N γ a).trans ?_)
  exact mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le

/-- **Independence of bad events** (complement form of `measure_biInter_band_eq_prod`). -/
theorem measure_biInter_band_bad_eq_prod (hW : IsWhiteNoise P W) {ι : Type} (F : Finset ι)
    (S : ι → Finset ℂ) {a b R : ℝ} (ha : 0 < a) (hR : ∀ u ∈ Ioo a b, etaRad u ≤ R)
    (hdisj : Pairwise fun i j => Disjoint (bandSupp a b R (S i)) (bandSupp a b R (S j)))
    (G : ℂ → Set ℝ) (hG : ∀ w, MeasurableSet (G w)) :
    P (⋂ i ∈ F, {ω | ∃ w ∈ S i, etaField W (Ioo a b) w ω ∉ G w}) =
      ∏ i ∈ F, P {ω | ∃ w ∈ S i, etaField W (Ioo a b) w ω ∉ G w} := by
  have h := hW.iIndepFun_of_pairwise_disjoint hdisj
  refine h.meas_biInter fun i _ => ?_
  have hsupp : ∀ w ∈ S i, SupportedIn (bandSupp a b R (S i)) (etaKernelL2 (Ioo a b) w) :=
    fun w hw => supportedIn_mono (supportedIn_etaKernelL2_Ioo ha hR w)
      (prod_mono subset_rfl (subset_biUnion_of_mem (u := fun w => Metric.ball w R) hw))
  refine ⟨⋃ w : S i, {φ | Real.sqrt Real.pi * φ ⟨etaKernelL2 (Ioo a b) w, hsupp w.1 w.2⟩ ∉
    G w}, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun w =>
      ((hG w).preimage (measurable_const.mul (measurable_pi_apply _))).compl
  · ext ω
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq, etaField, Subtype.exists, exists_prop]

end DZZ
end LQGMetric
