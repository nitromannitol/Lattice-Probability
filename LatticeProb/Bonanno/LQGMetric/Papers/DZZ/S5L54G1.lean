/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61F1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D123

/-!
# D117 P-54C (1): deterministic tools for the contradiction of DZZ L5.4 (P2-DZZ54C)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.4, l. 2553–2568.
The configuration used (DEC-117 §2(a), DEC-123 §1): `u₅₄ = 19/40 + i/2` (midpoint of the left side
of `𝕍̄`), the segment `L` on the right side `{x = 1/2}` of `𝕍_{u₅₄,1/20}`, the mirror point
`v₅₄ = dzzRefl u₅₄ = 21/40 + i/2`. Then the leg wall `legWall u₅₄ λ L`, the tilde box
`𝕍̃_{u₅₄,v₅₄}` and the mirror leg wall all equal `K₅₄ = 𝕍_{1/2+i/2, 1/10}`, which is
`dzzRefl`-invariant.

* `lgdDZZ_comm`, `lgdDZZ_triangle`: symmetry and the triangle inequality of `D_δ` (DZZ use them
  without comment; own elementary proofs from `lgdDZZ_le_card`, S6L61F1).
* `lgdDZZ_wall_wall_le`: an inner wall makes an outer wall redundant.
* `lgdDZZ_wall_map_refl`: `D^K_δ[ν ∘ dzzRefl⁻¹](x,y) = D^{dzzRefl⁻¹ K}_δ[ν](dzzRefl x, dzzRefl y)`
  (the reflection maps rational balls to rational balls; own elementary proof).
* the geometry of the configuration, and `legWall_eq_legSq` (a set with two points lies on one
  side only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- the image of a path on `[0,1]` -/
lemma path_image_props {x y : ℂ} (γ : Path x y) :
    IsPathConnected (γ.extend '' Icc 0 1) ∧ x ∈ γ.extend '' Icc 0 1 ∧ y ∈ γ.extend '' Icc 0 1 ∧
      γ.extend '' Icc 0 1 ⊆ range γ :=
  ⟨((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.2 zero_le_one)).image
      γ.continuous_extend, ⟨0, left_mem_Icc.2 zero_le_one, by simp⟩,
    ⟨1, right_mem_Icc.2 zero_le_one, by simp⟩, by rintro _ ⟨s, -, rfl⟩; exact ⟨_, rfl⟩⟩

/-- `D_δ` is symmetric. -/
lemma lgdDZZ_comm (μ : Measure ℂ) (δ : ℝ) (x y : ℂ) : lgdDZZ μ δ x y = lgdDZZ μ δ y x := by
  have key : ∀ x y : ℂ, lgdDZZ μ δ y x ≤ lgdDZZ μ δ x y := by
    intro x y
    rcases eq_top_or_lt_top (lgdDZZ μ δ x y) with h | h
    · rw [h]; exact le_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h.ne
    obtain ⟨F, γ, hF, hc, hr⟩ := exists_fam_of_lgdDZZ_le (μ := μ) (δ := δ) (n := n) hn.ge
    obtain ⟨hS, hx, hy, hsub⟩ := path_image_props γ
    have := lgdDZZ_le_card hF hS (hsub.trans hr) hy hx
    rw [← hn]; exact this.trans (by exact_mod_cast hc)
  exact le_antisymm (key y x) (key x y)

/-- the triangle inequality for `D_δ` -/
lemma lgdDZZ_triangle (μ : Measure ℂ) (δ : ℝ) (x y z : ℂ) :
    lgdDZZ μ δ x z ≤ lgdDZZ μ δ x y + lgdDZZ μ δ y z := by
  classical
  rcases eq_top_or_lt_top (lgdDZZ μ δ x y) with h | h
  · rw [h, top_add]; exact le_top
  rcases eq_top_or_lt_top (lgdDZZ μ δ y z) with h' | h'
  · rw [h', add_top]; exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h.ne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h'.ne
  obtain ⟨F, γ, hF, hc, hr⟩ := exists_fam_of_lgdDZZ_le (μ := μ) (δ := δ) (n := n) hn.ge
  obtain ⟨G, γ', hG, hc', hr'⟩ := exists_fam_of_lgdDZZ_le (μ := μ) (δ := δ) (n := m) hm.ge
  obtain ⟨hS1, hx1, hy1, hs1⟩ := path_image_props γ
  obtain ⟨hS2, hx2, hy2, hs2⟩ := path_image_props γ'
  have hS := hS1.union hS2 ⟨y, hy1, hx2⟩
  have hcov : γ.extend '' Icc 0 1 ∪ γ'.extend '' Icc 0 1 ⊆ famCov (F ∪ G) := by
    rw [famCov_union]; exact union_subset_union (hs1.trans hr) (hs2.trans hr')
  have := lgdDZZ_le_card (hF.union hG) hS hcov (Or.inl hx1) (Or.inr hy2)
  rw [← hn, ← hm]
  refine this.trans ?_
  have := Finset.card_union_le F G
  exact_mod_cast this.trans (add_le_add hc hc')

/-- an inner closed wall makes an outer wall redundant -/
lemma lgdDZZ_wall_wall_le {K K' : Set ℂ} (hK : IsClosed K) (hKK : K ⊆ K') (μ : Measure ℂ)
    (δ : ℝ) (x y : ℂ) :
    lgdDZZ (dzzWall K (dzzWall K' μ)) δ x y ≤ lgdDZZ (dzzWall K μ) δ x y := by
  have h := lgdDZZ_le_of_ball_le (μ := dzzWall K (dzzWall K' μ)) (ν := dzzWall K μ) (c := 0)
    (fun c r => ?_) δ x y
  · simpa using h
  rw [Real.exp_zero, ENNReal.ofReal_one, one_mul]
  by_cases hs : Metric.ball (ratPt c) r ⊆ K
  · rw [dzzWall_ball_of_subset _ hs, dzzWall_ball_of_subset _ (hs.trans hKK),
      dzzWall_ball_of_subset _ hs]
  · rw [dzzWall_ball_of_not_subset hK μ hs]; exact le_top

lemma dzzRefl_invol₅₄ (z : ℂ) : dzzRefl (dzzRefl z) = z := by
  apply Complex.ext <;> simp [dzzRefl]

lemma dzzRefl_dist (z w : ℂ) : dist (dzzRefl z) (dzzRefl w) = dist z w := by
  have : dzzRefl z - dzzRefl w = -(starRingEnd ℂ (z - w)) := by
    apply Complex.ext <;> simp [dzzRefl] <;> linarith
  rw [dist_eq_norm, dist_eq_norm, this, norm_neg, Complex.norm_conj]

lemma continuous_dzzRefl : Continuous dzzRefl := by
  have : dzzRefl = fun z : ℂ => (1 : ℂ) - starRingEnd ℂ z := by
    funext z; apply Complex.ext <;> simp [dzzRefl]
  rw [this]; fun_prop

lemma dzzRefl_preimage_ball (x : ℂ) (r : ℝ) :
    dzzRefl ⁻¹' Metric.ball (dzzRefl x) r = Metric.ball x r := by
  ext z; simp only [mem_preimage, Metric.mem_ball, dzzRefl_dist]

lemma dzzRefl_ratPt (c : ℚ × ℚ) : dzzRefl (ratPt c) = ratPt (1 - c.1, c.2) := by
  apply Complex.ext <;> simp [dzzRefl, ratPt]

/-- one direction of the reflection invariance of walled `D_δ` -/
lemma lgdDZZ_wall_map_refl_le {K : Set ℂ} (hK : IsClosed K) (ν : Measure ℂ) (δ : ℝ) (x y : ℂ) :
    lgdDZZ (dzzWall K (ν.map dzzRefl)) δ x y ≤
      lgdDZZ (dzzWall (dzzRefl ⁻¹' K) ν) δ (dzzRefl x) (dzzRefl y) := by
  unfold lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  have hcl : IsClosed (dzzRefl ⁻¹' K) := hK.preimage continuous_dzzRefl
  have hPx : dzzRefl (dzzRefl x) = x := dzzRefl_invol₅₄ x
  have hPy : dzzRefl (dzzRefl y) = y := dzzRefl_invol₅₄ y
  refine iInf₂_le N ⟨fun i => (1 - (c i).1, (c i).2), ρ,
    (P.map continuous_dzzRefl).cast hPx.symm hPy.symm, fun i => ⟨(h1 i).1, ?_⟩, fun t => ?_⟩
  · have hm := (h1 i).2
    have hsub : Metric.ball (ratPt (c i)) (ρ i) ⊆ dzzRefl ⁻¹' K := by
      by_contra hs
      rw [dzzWall_ball_of_not_subset hcl _ hs] at hm
      exact ENNReal.ofReal_ne_top (top_le_iff.1 hm)
    rw [dzzWall_ball_of_subset _ hsub] at hm
    have e : ratPt (1 - (c i).1, (c i).2) = dzzRefl (ratPt (c i)) := (dzzRefl_ratPt _).symm
    have hsub' : Metric.ball (ratPt (1 - (c i).1, (c i).2)) (ρ i) ⊆ K := by
      intro z hz
      rw [e, ← dzzRefl_preimage_ball, dzzRefl_invol₅₄] at hz
      have := hsub hz
      rwa [mem_preimage, dzzRefl_invol₅₄] at this
    rw [dzzWall_ball_of_subset _ hsub', Measure.map_apply continuous_dzzRefl.measurable
      measurableSet_ball, e, dzzRefl_preimage_ball]
    exact hm
  · obtain ⟨i, hi⟩ := h2 t
    refine ⟨i, ?_⟩
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    rw [Metric.mem_ball, ← dzzRefl_ratPt, dzzRefl_dist]
    exact hi

/-- **reflection invariance of walled `D_δ`**:
`D^K_δ[dzzRefl_* ν](x,y) = D^{dzzRefl⁻¹ K}_δ[ν](dzzRefl x, dzzRefl y)`. -/
lemma lgdDZZ_wall_map_refl {K : Set ℂ} (hK : IsClosed K) (ν : Measure ℂ) (δ : ℝ) (x y : ℂ) :
    lgdDZZ (dzzWall K (ν.map dzzRefl)) δ x y =
      lgdDZZ (dzzWall (dzzRefl ⁻¹' K) ν) δ (dzzRefl x) (dzzRefl y) := by
  refine le_antisymm (lgdDZZ_wall_map_refl_le hK ν δ x y) ?_
  have h := lgdDZZ_wall_map_refl_le (hK.preimage continuous_dzzRefl) (ν.map dzzRefl) δ
    (dzzRefl x) (dzzRefl y)
  have hmm : (ν.map dzzRefl).map dzzRefl = ν := by
    rw [Measure.map_map continuous_dzzRefl.measurable continuous_dzzRefl.measurable]
    conv_rhs => rw [← Measure.map_id (μ := ν)]
    congr 1; funext z; exact dzzRefl_invol₅₄ z
  have hKK : dzzRefl ⁻¹' (dzzRefl ⁻¹' K) = K := by
    ext z; simp only [mem_preimage, dzzRefl_invol₅₄]
  rwa [hmm, hKK, dzzRefl_invol₅₄, dzzRefl_invol₅₄] at h

/-! ### The configuration -/

/-- the centre of `𝕍` -/
def c₅₄ : ℂ := ⟨1 / 2, 1 / 2⟩

/-- the midpoint of the left side of `𝕍̄` -/
def u₅₄ : ℂ := ⟨19 / 40, 1 / 2⟩

/-- its mirror image, the midpoint of the right side of `𝕍̄` -/
def v₅₄ : ℂ := ⟨21 / 40, 1 / 2⟩

/-- the common wall `𝕍_{1/2+i/2, 1/10}` -/
def K₅₄ : Set ℂ := sqBox c₅₄ (1 / 10)

lemma u₅₄_mem_dzzVbar : u₅₄ ∈ dzzVbar := by
  refine ⟨?_, ?_⟩ <;> simp [u₅₄] <;> (try norm_num [abs_of_nonneg, abs_of_nonpos])

lemma v₅₄_mem_dzzVbar : v₅₄ ∈ dzzVbar := by
  refine ⟨?_, ?_⟩ <;> simp [v₅₄] <;> (try norm_num [abs_of_nonneg, abs_of_nonpos])

lemma u₅₄_ne_v₅₄ : u₅₄ ≠ v₅₄ := by
  intro h; have := congrArg Complex.re h; simp [u₅₄, v₅₄] at this; try norm_num at this

lemma dist_u₅₄_v₅₄ : dist u₅₄ v₅₄ = 1 / 20 := by
  rw [dist_comm, dist_eq_norm]
  have : v₅₄ - u₅₄ = ((1 / 20 : ℝ) : ℂ) := by apply Complex.ext <;> simp [u₅₄, v₅₄] <;> norm_num
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]

lemma dzzRefl_u₅₄ : dzzRefl u₅₄ = v₅₄ := by
  apply Complex.ext <;> simp [dzzRefl, u₅₄, v₅₄] <;> norm_num

lemma dzzRefl_of_re {z : ℂ} (hz : z.re = 1 / 2) : dzzRefl z = z := by
  apply Complex.ext <;> simp [dzzRefl, hz] <;> norm_num

lemma dzzRefl_preimage_K₅₄ : dzzRefl ⁻¹' K₅₄ = K₅₄ := by
  ext z
  simp only [K₅₄, sqBox, c₅₄, mem_preimage, mem_ofPred_eq, dzzRefl]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
  · rw [show z.re - 1 / 2 = -(1 - z.re - 1 / 2) by ring, abs_neg]; exact h1
  · rw [show 1 - z.re - 1 / 2 = -(z.re - 1 / 2) by ring, abs_neg]; exact h1

lemma isClosed_K₅₄ : IsClosed K₅₄ := isClosed_sqBox _ _

lemma tildeBox_u₅₄_v₅₄ : tildeBox u₅₄ v₅₄ = K₅₄ := by
  have e1 : v₅₄ - u₅₄ = ((1 / 20 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [u₅₄, v₅₄] <;> norm_num
  have e2 : (u₅₄ + v₅₄) / 2 = c₅₄ := by apply Complex.ext <;> simp [u₅₄, v₅₄, c₅₄] <;> norm_num
  ext z
  simp only [tildeBox, mem_ofPred_eq, e1, e2, Complex.norm_real, Complex.conj_ofReal,
    K₅₄, sqBox, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, mul_zero, sub_zero, add_zero]
  simp only [zero_add, abs_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith [abs_nonneg (z.re - c₅₄.re),
    abs_nonneg (z.im - c₅₄.im)]

/-- a set with two distinct points lies on at most one side of a square -/
lemma sqSide_unique {u : ℂ} {l : ℝ} (hl : 0 < l) {j j' : Fin 4} {L : Set ℂ}
    (hL : L ⊆ sqSide u l j) (hL' : L ⊆ sqSide u l j') {z₁ z₂ : ℂ} (h1 : z₁ ∈ L) (h2 : z₂ ∈ L)
    (hne : z₁ ≠ z₂) : j = j' := by
  have a1 := hL h1
  have a2 := hL h2
  have b1 := hL' h1
  have b2 := hL' h2
  by_contra hjj
  apply hne
  fin_cases j <;> fin_cases j' <;> simp only [sqSide, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Complex.mem_reProdIm, mem_Icc, mem_singleton_iff]
    at a1 a2 b1 b2 hjj <;> (try exact absurd trivial hjj) <;> (try exact absurd rfl hjj) <;>
    first
    | exact Complex.ext (by linarith) (by linarith)
    | exact absurd (by linarith : l = 0) hl.ne'

/-- the leg wall of a set with two points on side `j` is `legSq u l j` -/
lemma legWall_eq_legSq {u : ℂ} {l : ℝ} (hl : 0 < l) {j : Fin 4} {L : Set ℂ}
    (hL : L ⊆ sqSide u l j) {z₁ z₂ : ℂ} (h1 : z₁ ∈ L) (h2 : z₂ ∈ L) (hne : z₁ ≠ z₂) :
    legWall u l L = legSq u l j := by
  have hex : ∃ j, L ⊆ sqSide u l j := ⟨j, hL⟩
  unfold legWall
  rw [dif_pos hex]
  rw [sqSide_unique hl (Classical.choose_spec hex) hL h1 h2 hne]

end DZZ
end LQGMetric
