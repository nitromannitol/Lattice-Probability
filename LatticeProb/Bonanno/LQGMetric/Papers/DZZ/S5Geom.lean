/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Geom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Exp

/-!
# Geometry of DZZ's boxes `𝕍̄`, `𝕍_{u,λ}`, `𝕍̃_{u,v}` (P2-DZZ56)

Elementary facts used to instantiate DZZ Proposition 3.17 at the pairs of Lemmas 5.3 and 6.1
(Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2263–2268, 2584–2590):
* points near the centre of `𝕍` lie in `𝕍^ξ` (`mem_dzzVXi_of_near`);
* the frontier of a box is connected with diameter `≥` its side (`isConnected_frontier_sqBox`,
  `side_le_diam_frontier_sqBox`) — so `∂𝕍_{u,λ}` is a `ξ`-admissible set for small `δ`;
* the ball `B((u+v)/2, |u−v|)` lies in `𝕍̃_{u,v}` and, for `u, v ∈ 𝕍̄`, in `𝕍°`.
Own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace LQGMetric
namespace DZZ

lemma sqBox_eq_reProdIm (c : ℂ) (l : ℝ) :
    sqBox c l = Icc (c.re - l / 2) (c.re + l / 2) ×ℂ Icc (c.im - l / 2) (c.im + l / 2) := by
  ext z
  simp only [sqBox, mem_setOf_eq, Complex.mem_reProdIm, mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma isConnected_reProdIm {s t : Set ℝ} (hs : IsConnected s) (ht : IsConnected t) :
    IsConnected (s ×ℂ t) := by
  have e : s ×ℂ t = (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) '' (s ×ˢ t) := by
    ext z
    simp only [Complex.mem_reProdIm, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨z.re, z.im, ⟨h1, h2⟩, Complex.re_add_im z⟩
    · rintro ⟨a, b, ⟨h1, h2⟩, rfl⟩; simpa using And.intro h1 h2
  rw [e]
  exact (hs.prod ht).image _ (by fun_prop)

/-- The frontier of a closed box, as four sides. -/
lemma frontier_sqBox {c : ℂ} {l : ℝ} (hl : 0 < l) :
    frontier (sqBox c l) =
      ((Icc (c.re - l / 2) (c.re + l / 2) ×ℂ {c.im - l / 2}) ∪
        ({c.re - l / 2} ×ℂ Icc (c.im - l / 2) (c.im + l / 2))) ∪
      (Icc (c.re - l / 2) (c.re + l / 2) ×ℂ {c.im + l / 2}) ∪
      ({c.re + l / 2} ×ℂ Icc (c.im - l / 2) (c.im + l / 2)) := by
  rw [sqBox_eq_reProdIm, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
    frontier_Icc (by linarith), frontier_Icc (by linarith)]
  ext z
  simp only [Complex.mem_reProdIm, mem_union, mem_insert_iff, mem_singleton_iff]
  tauto

lemma isConnected_frontier_sqBox (c : ℂ) {l : ℝ} (hl : 0 < l) :
    IsConnected (frontier (sqBox c l)) := by
  rw [frontier_sqBox hl]
  have hI : IsConnected (Icc (c.re - l / 2) (c.re + l / 2)) := isConnected_Icc (by linarith)
  have hJ : IsConnected (Icc (c.im - l / 2) (c.im + l / 2)) := isConnected_Icc (by linarith)
  have hpt : ∀ x : ℝ, IsConnected ({x} : Set ℝ) := fun x => isConnected_singleton
  have corner : ∀ a b : ℝ, ((a : ℂ) + b * Complex.I).re = a ∧ ((a : ℂ) + b * Complex.I).im = b :=
    fun a b => by simp
  refine (((isConnected_reProdIm hI (hpt _)).union ?_ (isConnected_reProdIm (hpt _) hJ)).union
    ?_ (isConnected_reProdIm hI (hpt _))).union ?_ (isConnected_reProdIm (hpt _) hJ)
  · refine ⟨(c.re - l / 2 : ℝ) + (c.im - l / 2 : ℝ) * Complex.I, ?_, ?_⟩ <;>
      simp only [Complex.mem_reProdIm, (corner _ _).1, (corner _ _).2, mem_Icc,
        mem_singleton_iff] <;> constructor <;> (try constructor) <;> linarith
  · refine ⟨(c.re - l / 2 : ℝ) + (c.im + l / 2 : ℝ) * Complex.I, Or.inr ?_, ?_⟩ <;>
      simp only [Complex.mem_reProdIm, (corner _ _).1, (corner _ _).2, mem_Icc,
        mem_singleton_iff] <;> constructor <;> (try constructor) <;> linarith
  · refine ⟨(c.re + l / 2 : ℝ) + (c.im - l / 2 : ℝ) * Complex.I, Or.inl (Or.inl ?_), ?_⟩ <;>
      simp only [Complex.mem_reProdIm, (corner _ _).1, (corner _ _).2, mem_Icc,
        mem_singleton_iff] <;> constructor <;> (try constructor) <;> linarith

lemma sqBox_subset_closedBall (c : ℂ) {l : ℝ} (hl : 0 ≤ l) : sqBox c l ⊆ Metric.closedBall c l := by
  intro z ⟨h1, h2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  linarith

lemma side_le_diam_frontier_sqBox (c : ℂ) {l : ℝ} (hl : 0 < l) :
    l ≤ Metric.diam (frontier (sqBox c l)) := by
  have hb : Bornology.IsBounded (frontier (sqBox c l)) :=
    (Metric.isBounded_closedBall.subset (sqBox_subset_closedBall c hl.le)).subset
      ((isClosed_sqBox c l).frontier_subset)
  set a : ℂ := (c.re - l / 2 : ℝ) + (c.im - l / 2 : ℝ) * Complex.I
  set b : ℂ := (c.re + l / 2 : ℝ) + (c.im - l / 2 : ℝ) * Complex.I
  have ha : a ∈ frontier (sqBox c l) := by
    rw [frontier_sqBox hl]
    refine Or.inl (Or.inl (Or.inl ?_))
    simp only [a, Complex.mem_reProdIm, mem_Icc, mem_singleton_iff, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im]
    constructor <;> (try constructor) <;> ring_nf <;> linarith
  have hb' : b ∈ frontier (sqBox c l) := by
    rw [frontier_sqBox hl]
    refine Or.inl (Or.inl (Or.inl ?_))
    simp only [b, Complex.mem_reProdIm, mem_Icc, mem_singleton_iff, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im]
    constructor <;> (try constructor) <;> ring_nf <;> linarith
  have hd : dist a b = l := by
    rw [dist_eq_norm]
    have : a - b = ((-l : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [a, b] <;> ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hl]
  calc l = dist a b := hd.symm
    _ ≤ _ := Metric.dist_le_diam_of_mem hb ha hb'

/-- Points whose coordinates are within `a` of the centre `1/2` lie in `𝕍^ξ` for `a + ξ ≤ 1/2`. -/
lemma mem_dzzVXi_of_near {z : ℂ} {a ξ : ℝ} (hre : |z.re - 1 / 2| ≤ a) (him : |z.im - 1 / 2| ≤ a)
    (h : a + ξ ≤ 1 / 2) (hξ : 0 ≤ ξ) : z ∈ dzzVXi ξ := by
  have ha : 0 ≤ a := (abs_nonneg _).trans hre
  rw [abs_le] at hre him
  have hV : dzzV = Icc 0 1 ×ℂ Icc 0 1 := by
    ext w; simp [dzzV, Complex.mem_reProdIm, and_assoc]
  refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
  rw [hV, Complex.frontier_reProdIm, closure_Icc, frontier_Icc zero_le_one]
  have hne : (Icc (0 : ℝ) 1 ×ℂ {0, 1} ∪ {0, 1} ×ℂ Icc 0 1).Nonempty :=
    ⟨0, Or.inl ⟨by simp, by simp⟩⟩
  refine (Metric.le_infDist hne).mpr fun y hy => ?_
  rw [dist_eq_norm]
  rcases hy with ⟨_, hy⟩ | ⟨hy, _⟩
  · have h2 := Complex.abs_im_le_norm (z - y)
    rw [Complex.sub_im] at h2
    rcases hy with hy | hy
    · rw [hy] at h2; have := le_abs_self (z.im - 0); linarith
    · rw [mem_singleton_iff] at hy; rw [hy] at h2
      have := neg_le_abs (z.im - 1); linarith
  · have h2 := Complex.abs_re_le_norm (z - y)
    rw [Complex.sub_re] at h2
    rcases hy with hy | hy
    · rw [hy] at h2; have := le_abs_self (z.re - 0); linarith
    · rw [mem_singleton_iff] at hy; rw [hy] at h2
      have := neg_le_abs (z.re - 1); linarith

lemma ball_mid_subset_tildeBox (u v : ℂ) :
    Metric.ball ((u + v) / 2) ‖v - u‖ ⊆ tildeBox u v := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hn : ‖(z - (u + v) / 2) * starRingEnd ℂ (v - u)‖ ≤ ‖v - u‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul_of_nonneg_right hz.le (norm_nonneg _)
  exact ⟨(Complex.abs_re_le_norm _).trans hn, (Complex.abs_im_le_norm _).trans hn⟩

lemma near_of_mem_dzzVbar {u : ℂ} (hu : u ∈ dzzVbar) :
    |u.re - 1 / 2| ≤ 1 / 40 ∧ |u.im - 1 / 2| ≤ 1 / 40 := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨le_of_le_of_eq h1 (by norm_num), le_of_le_of_eq h2 (by norm_num)⟩

lemma norm_sub_le_of_mem_dzzVbar {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) :
    ‖v - u‖ ≤ 1 / 10 := by
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  obtain ⟨h3, h4⟩ := near_of_mem_dzzVbar hv
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  rw [abs_le] at h1 h2 h3 h4
  have e1 : |v.re - u.re| ≤ 1 / 20 := abs_le.mpr ⟨by linarith, by linarith⟩
  have e2 : |v.im - u.im| ≤ 1 / 20 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

lemma ball_mid_subset_openSquare {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) :
    Metric.ball ((u + v) / 2) ‖v - u‖ ⊆ openSquare := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hn := norm_sub_le_of_mem_dzzVbar hu hv
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  obtain ⟨h3, h4⟩ := near_of_mem_dzzVbar hv
  have hr := Complex.abs_re_le_norm (z - (u + v) / 2)
  have hi := Complex.abs_im_le_norm (z - (u + v) / 2)
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.add_re,
    Complex.add_im] at hr hi
  norm_num at hr hi
  rw [abs_le] at h1 h2 h3 h4 hr hi
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma dzzWall_apply_of_subset {A K : Set ℂ} (hA : MeasurableSet A) (hK : K ⊆ A)
    (μ : Measure ℂ) : dzzWall A μ K = μ K := by
  unfold dzzWall
  rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply' hA.compl,
    show K ∩ Aᶜ = ∅ from by
      ext z; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
        not_not]; exact fun h => hK h]
  simp

end DZZ
end LQGMetric
