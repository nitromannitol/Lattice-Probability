/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcK

/-!
# P-317K-SIM, part 4: the geometry of the walls as similar images of `B̄₀ = [1/4,1/2]²`

DZZ (arXiv:1807.00422) uses the walled Proposition 3.17 at the walls of Remark 5.2 (l. 2281–2284)
and of Lemma 5.4 (l. 2557–2563); every wall of `dgWalls` (D128) is the image of the fixed dyadic
box `B̄₀ = [1/4,1/2]²` under a similarity `θ = simMap a b` with `0 < ‖a‖ ≤ 1`
(`wsim_wall_image`): `a = 2/5` for the squares of side `1/10`, `a = 8(v − u)` for `𝕍̃_{u,v}`.
The pull-back `θ⁻¹` of a pair inside `(θB̄₀)^ξ` is a pair inside `B̄₀^ξ`
(`wsim_preimage_kXi`), admissible at every scale `δ'` with `δ'^{ξd} ≤ δ^ξ/‖a‖`
(`wsim_preimage_admAtIn`). Own elementary proofs (Euclidean geometry of similarities).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace LQGMetric
namespace DZZ

/-- The fixed dyadic box `B₀ = [1/4,1/2]²` (level 2, column 1, row 1). -/
def wsimB₀ : DyBox := ⟨2, 1, 1, by norm_num, by norm_num⟩

lemma wsimB₀_closedBox : wsimB₀.closedBox = sqBox ⟨3 / 8, 3 / 8⟩ (1 / 4) := by
  ext z
  simp only [DyBox.closedBox, wsimB₀, DyBox.side, sqBox, mem_ofPred_eq, abs_le]
  norm_num
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma wsimB₀_eq_tildeBox :
    wsimB₀.closedBox = tildeBox ⟨5 / 16, 3 / 8⟩ ⟨7 / 16, 3 / 8⟩ := by
  have hd : (⟨7 / 16, 3 / 8⟩ - ⟨5 / 16, 3 / 8⟩ : ℂ) = ((1 / 8 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> norm_num
  have hm : ((⟨5 / 16, 3 / 8⟩ + ⟨7 / 16, 3 / 8⟩ : ℂ) / 2) = ⟨3 / 8, 3 / 8⟩ := by
    apply Complex.ext <;> simp <;> norm_num
  rw [wsimB₀_closedBox]
  ext z
  simp only [tildeBox, sqBox, mem_ofPred_eq, hd, hm, Complex.conj_ofReal, Complex.norm_real,
    Complex.re_mul_ofReal, Complex.im_mul_ofReal, Complex.sub_re, Complex.sub_im, abs_mul]
  norm_num
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

lemma wsim_compl_nonempty : (wsimB₀.closedBox)ᶜ.Nonempty :=
  ⟨(2 : ℂ), fun h => by have := (closedBox_sub_dzzV' wsimB₀ h).2.1; norm_num at this⟩

lemma wsimB₀_subset_openSquare : wsimB₀.closedBox ⊆ openSquare := by
  intro z hz
  simp only [DyBox.closedBox, wsimB₀, DyBox.side, mem_ofPred_eq] at hz
  norm_num at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma wsimB₀_subset_dzzVXi {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 4) :
    wsimB₀.closedBox ⊆ dzzVXi ξ := by
  intro z hz
  rw [wsimB₀_closedBox] at hz
  obtain ⟨h1, h2⟩ := hz
  simp only at h1 h2
  refine mem_dzzVXi_of_near (a := 1 / 4) ?_ ?_ (by linarith) hξ0
  · rw [abs_le] at h1 ⊢; constructor <;> linarith
  · rw [abs_le] at h2 ⊢; constructor <;> linarith

lemma wsim_kXi_subset {ξ : ℝ} (hξ : 0 < ξ) : kXi wsimB₀.closedBox ξ ⊆ wsimB₀.closedBox :=
  fun _ hx => cmw_ball_sub_of_kXi hx (mem_ball_self hξ)

lemma wsim_kXi_subset_dzzVXi {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 4) :
    kXi wsimB₀.closedBox ξ ⊆ dzzVXi ξ :=
  (wsim_kXi_subset hξ).trans (wsimB₀_subset_dzzVXi hξ.le hξ1)

/-! ### The walls are similar images of `B̄₀` -/

/-- **Every wall of `dgWalls` is `θ(B̄₀)` with `0 < ‖a‖ ≤ 1`.** -/
theorem wsim_wall_image {K : Set ℂ} (hK : K ∈ dgWalls) :
    ∃ a b : ℂ, a ≠ 0 ∧ ‖a‖ ≤ 1 ∧ simMap a b '' wsimB₀.closedBox = K := by
  rcases hK with ⟨c, rfl, -, -⟩ | ⟨u, hu, v, hv, huv, rfl⟩
  · refine ⟨((2 / 5 : ℝ) : ℂ), c - ((2 / 5 : ℝ) : ℂ) * ⟨3 / 8, 3 / 8⟩, by norm_num, ?_, ?_⟩
    · rw [Complex.norm_real]; norm_num
    · rw [wsimB₀_closedBox, simMap_ofReal_image_sqBox (by norm_num)]
      congr 1
      · simp [simMap]
      · norm_num
  · set a : ℂ := 8 * (v - u)
    have ha : a ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.2 huv.symm)
    refine ⟨a, u - a * ⟨5 / 16, 3 / 8⟩, ha, ?_, ?_⟩
    · obtain ⟨hu1, hu2⟩ := near_of_mem_dzzVbar hu
      obtain ⟨hv1, hv2⟩ := near_of_mem_dzzVbar hv
      have h := Complex.norm_le_abs_re_add_abs_im (v - u)
      have e1 : |(v - u).re| ≤ 1 / 20 := by
        rw [Complex.sub_re, abs_le]; rw [abs_le] at hu1 hv1; constructor <;> linarith
      have e2 : |(v - u).im| ≤ 1 / 20 := by
        rw [Complex.sub_im, abs_le]; rw [abs_le] at hu2 hv2; constructor <;> linarith
      simp only [a, norm_mul]
      norm_num
      linarith
    · rw [wsimB₀_eq_tildeBox, simMap_image_tildeBox ha]
      congr 1
      · simp [simMap]
      · simp only [simMap, a]
        apply Complex.ext <;> simp <;> ring

lemma wsim_wall_subset_dzzVXi {K : Set ℂ} (hK : K ∈ dgWalls) : K ⊆ dzzVXi (1 / 4) := by
  rcases hK with ⟨c, rfl, hc1, hc2⟩ | ⟨u, hu, v, hv, huv, rfl⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := hz
    refine mem_dzzVXi_of_near (a := 1 / 10) ?_ ?_ (by norm_num) (by norm_num)
    · rw [abs_le] at h1 hc1 ⊢; constructor <;> linarith
    · rw [abs_le] at h2 hc2 ⊢; constructor <;> linarith
  · exact tildeBox_subset_dzzVXi hu hv huv

lemma dzzVXi_anti {ξ ξ' : ℝ} (h : ξ ≤ ξ') : dzzVXi ξ' ⊆ dzzVXi ξ :=
  fun _ hz => ⟨hz.1, h.trans hz.2⟩

lemma wsim_convex_image {S : Set ℂ} (hS : Convex ℝ S) (a b : ℂ) :
    Convex ℝ (simMap a b '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ s t hs ht hst
  refine ⟨s • x + t • y, hS hx hy hs ht hst, ?_⟩
  have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
  simp only [simMap, Complex.real_smul]
  linear_combination (-b) * hst'

/-! ### Pulling pairs back along `θ` -/

lemma wsim_dist_simMap (a b x y : ℂ) : dist (simMap a b x) (simMap a b y) = ‖a‖ * dist x y := by
  simp only [Complex.dist_eq, simMap, add_sub_add_right_eq_sub, ← mul_sub, norm_mul]

lemma wsim_lipschitz (a b : ℂ) : LipschitzWith ‖a‖₊ (simMap a b) :=
  LipschitzWith.of_dist_le_mul fun x y => by rw [wsim_dist_simMap]; rfl

lemma wsim_preimage_eq_image {a : ℂ} (ha : a ≠ 0) (b : ℂ) (A : Set ℂ) :
    simMap a b ⁻¹' A = simMap a⁻¹ (-(a⁻¹ * b)) '' A :=
  (congrFun (image_eq_preimage_of_inverse (simMap_right_inv ha b) (simMap_left_inv ha b)) A).symm

lemma wsim_image_preimage {a : ℂ} (ha : a ≠ 0) (b : ℂ) (A : Set ℂ) :
    simMap a b '' (simMap a b ⁻¹' A) = A :=
  image_preimage_eq A (simMap_surjective ha b)

/-- **Pulling back `K^ξ`**: `θ⁻¹((θK₀)^ξ) ⊆ K₀^ξ` for `‖a‖ ≤ 1`. -/
theorem wsim_preimage_kXi {a b : ℂ} (ha : a ≠ 0) (ha1 : ‖a‖ ≤ 1) {K₀ : Set ℂ}
    (hne : (K₀ᶜ).Nonempty) {ξ : ℝ} {A : Set ℂ} (hA : A ⊆ kXi (simMap a b '' K₀) ξ) :
    simMap a b ⁻¹' A ⊆ kXi K₀ ξ := by
  intro x hx
  have hb := cmw_ball_sub_of_kXi (hA hx)
  refine mem_kXi_of_ball_subset hne fun y hy => ?_
  have hy' : simMap a b y ∈ ball (simMap a b x) ξ := by
    rw [mem_ball, wsim_dist_simMap]
    rw [mem_ball] at hy
    nlinarith [norm_nonneg a, dist_nonneg (x := y) (y := x)]
  obtain ⟨y', hy'K, he⟩ := hb hy'
  rwa [← simMap_injective ha b he]

lemma wsim_preimage_singleton {a : ℂ} (ha : a ≠ 0) (b p : ℂ) :
    simMap a b ⁻¹' {p} = {simMap a⁻¹ (-(a⁻¹ * b)) p} := by
  rw [wsim_preimage_eq_image ha, image_singleton]

lemma wsim_isBounded_of_subset_dzzV {A : Set ℂ} (hA : A ⊆ dzzV) : Bornology.IsBounded A :=
  kc_isCompact_dzzV.isBounded.subset hA

/-- **Pulling back an admissible set** at a scale `δ'` with `δ'^{ξd} ≤ δ^ξ/‖a‖`. -/
theorem wsim_preimage_admSet {a : ℂ} (ha : a ≠ 0) (b : ℂ) {ξ ξd δ δ' : ℝ}
    (h : δ' ^ ξd ≤ δ ^ ξ / ‖a‖) {A : Set ℂ} (hA : IsXiAdmissibleSet ξ δ A)
    (hAb : Bornology.IsBounded A) : IsXiAdmissibleSet ξd δ' (simMap a b ⁻¹' A) := by
  rcases hA with ⟨p, rfl⟩ | ⟨hc, hd⟩
  · exact Or.inl ⟨_, wsim_preimage_singleton ha b p⟩
  · right
    have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
    have hpb : Bornology.IsBounded (simMap a b ⁻¹' A) := by
      rw [wsim_preimage_eq_image ha]; exact (wsim_lipschitz _ _).isBounded_image hAb
    refine ⟨?_, ?_⟩
    · rw [wsim_preimage_eq_image ha]
      exact hc.image _ (continuous_simMap _ _).continuousOn
    · have h1 := (wsim_lipschitz a b).diam_image_le _ hpb
      rw [wsim_image_preimage ha] at h1
      have h2 : δ ^ ξ / ‖a‖ ≤ Metric.diam (simMap a b ⁻¹' A) := by
        rw [div_le_iff₀ hna]
        have : ((‖a‖₊ : NNReal) : ℝ) = ‖a‖ := rfl
        rw [this] at h1
        linarith
      linarith

/-- **Pulling back a pair** inside `(θB̄₀)^ξ`: admissible at `δ'` and inside `B̄₀^ξ`. -/
theorem wsim_preimage_admAtIn {a b : ℂ} (ha : a ≠ 0) (ha1 : ‖a‖ ≤ 1) {ξ ξd δ δ' : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 4) (h : δ' ^ ξd ≤ δ ^ ξ / ‖a‖) {A B : Set ℂ}
    (hA : A ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ)
    (hB : B ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ) (hAV : A ⊆ dzzV) (hBV : B ⊆ dzzV)
    (hAa : IsXiAdmissibleSet ξ δ A) (hBa : IsXiAdmissibleSet ξ δ B)
    (hd : ∀ x ∈ A, ∀ y ∈ B, ξ ≤ dist x y) :
    IsXiAdmissibleAtIn wsimB₀.closedBox ξ ξd δ' (simMap a b ⁻¹' A) (simMap a b ⁻¹' B) := by
  have hA' := wsim_preimage_kXi ha ha1 wsim_compl_nonempty hA
  have hB' := wsim_preimage_kXi ha ha1 wsim_compl_nonempty hB
  refine ⟨⟨hA'.trans (wsim_kXi_subset_dzzVXi hξ hξ1), hB'.trans (wsim_kXi_subset_dzzVXi hξ hξ1),
    wsim_preimage_admSet ha b h hAa (wsim_isBounded_of_subset_dzzV hAV),
    wsim_preimage_admSet ha b h hBa (wsim_isBounded_of_subset_dzzV hBV), ?_⟩, hA', hB'⟩
  intro x hx y hy
  have := hd _ hx _ hy
  rw [wsim_dist_simMap] at this
  nlinarith [norm_nonneg a, dist_nonneg (x := x) (y := y)]

end DZZ
end LQGMetric
