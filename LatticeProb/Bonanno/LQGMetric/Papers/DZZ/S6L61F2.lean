/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61F2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61F1

/-!
# D117 P-61G (2): the contour of Fig. glue and the deterministic gluing (P2-DZZ61G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Fig. glue and l. 2562–2566 (four
short crossings of four rectangles, each "formed by a constant number of point to point
geodesics", forming a contour enclosing `L_δ`), l. 2605 (proof of Lemma 6.1: "the union of these
short crossings, the geodesic between `L_δ` and `∂𝕍̄_u`, as well as the geodesic between `v_{L_δ}`
and `∂𝕍̄_u` contains a path between `v_{L_δ}` and `∂𝕍̄_u`"). As decided in DEC-117 §2(c), the last
geodesic is a slip for a tilde geodesic from `v_{L_δ}` to the contour (one more short crossing).

Geometry (centre `v`, scale `d > 0`): the contour is the annulus between the squares of
half-side `2d` and `4d` around `v`; its four strips are crossed by the chains of tilde geodesics
through the red points `ringC v d j + k · ringW d j`, `k = 0, …, 8` (`j = 0, 1`: bottom, top,
horizontal steps `d`; `j = 2, 3`: left, right, vertical steps `i d`); the chain `j = 4` goes up
from the bottom red point below `v` to `v`. All pairs of neighbouring red points are at distance
`d` (40 pairs).

* `ring_glue_lgd`: if every one of the 40 tilde distances is `≤ N`, then for `x` in the inner
  square and `y` outside the outer one, `D_δ(v, y) ≤ D_δ(x, y) + 40 N`.

Own elementary argument (DZZ give the picture only), using P-GLUE (`dzz_ring_sep`,
`dzz_ring_isPathConnected`, S5Top2–3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- the first red point of the five chains -/
def ringC (v : ℂ) (d : ℝ) : Fin 5 → ℂ :=
  ![v + ⟨-4 * d, -3 * d⟩, v + ⟨-4 * d, 3 * d⟩, v + ⟨-3 * d, -4 * d⟩, v + ⟨3 * d, -4 * d⟩,
    v + ⟨0, -3 * d⟩]

/-- the step of the five chains -/
def ringW (d : ℝ) : Fin 5 → ℂ := ![⟨d, 0⟩, ⟨d, 0⟩, ⟨0, d⟩, ⟨0, d⟩, ⟨0, d⟩]

/-- the eight tilde distances of a chain are `≤ N` -/
def PairsOK (μ : Measure ℂ) (δ : ℝ) (N : ℕ) (c w : ℂ) : Prop :=
  ∀ k ≤ 7, lgdDZZ (dzzWall (tildeBox (c + (k : ℕ) * w) (c + ((k : ℕ) + 1) * w)) μ) δ
    (c + (k : ℕ) * w) (c + ((k : ℕ) + 1) * w) ≤ N

lemma tildeBox_horiz {x z : ℂ} {d : ℝ} (hd : 0 < d) (hz : z ∈ tildeBox x (x + ⟨d, 0⟩)) :
    |z.im - x.im| ≤ d := by
  obtain ⟨-, h2⟩ := hz
  have hn : ‖x + (⟨d, 0⟩ : ℂ) - x‖ ^ 2 = d ^ 2 := by
    rw [add_sub_cancel_left, Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  have hk : ((z - (x + (x + ⟨d, 0⟩)) / 2) * (starRingEnd ℂ) (x + ⟨d, 0⟩ - x)).im =
      d * (z.im - x.im) := by
    simp [Complex.mul_im]; ring
  rw [hk, hn, abs_mul, abs_of_pos hd] at h2
  nlinarith [abs_nonneg (z.im - x.im)]

lemma tildeBox_vert {x z : ℂ} {d : ℝ} (hd : 0 < d) (hz : z ∈ tildeBox x (x + ⟨0, d⟩)) :
    |z.re - x.re| ≤ d := by
  obtain ⟨-, h1⟩ := hz
  have hn : ‖x + (⟨0, d⟩ : ℂ) - x‖ ^ 2 = d ^ 2 := by
    rw [add_sub_cancel_left, Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  have hk : ((z - (x + (x + ⟨0, d⟩)) / 2) * (starRingEnd ℂ) (x + ⟨0, d⟩ - x)).im =
      -(d * (z.re - x.re)) := by
    simp [Complex.mul_im]; ring
  rw [hk, hn, abs_neg, abs_mul, abs_of_pos hd] at h1
  nlinarith [abs_nonneg (z.re - x.re)]

lemma strip_im {c z : ℂ} {d : ℝ} (hd : 0 < d)
    (hz : z ∈ ⋃ k ∈ Finset.range (7 + 1), tildeBox (c + (k : ℕ) * (⟨d, 0⟩ : ℂ))
      (c + ((k : ℕ) + 1) * (⟨d, 0⟩ : ℂ))) : |z.im - c.im| ≤ d := by
  obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 hz
  have h := tildeBox_horiz hd (x := c + (k : ℕ) * (⟨d, 0⟩ : ℂ)) (z := z)
    (by convert hk using 2; ring)
  simpa using h

lemma strip_re {c z : ℂ} {d : ℝ} (hd : 0 < d)
    (hz : z ∈ ⋃ k ∈ Finset.range (7 + 1), tildeBox (c + (k : ℕ) * (⟨0, d⟩ : ℂ))
      (c + ((k : ℕ) + 1) * (⟨0, d⟩ : ℂ))) : |z.re - c.re| ≤ d := by
  obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 hz
  have h := tildeBox_vert hd (x := c + (k : ℕ) * (⟨0, d⟩ : ℂ)) (z := z)
    (by convert hk using 2; ring)
  simpa using h

/-- a horizontal chain of eight tilde geodesics -/
theorem chain8_horiz {μ : Measure ℂ} {δ : ℝ} {N : ℕ} {c : ℂ} {d : ℝ} (hd : 0 < d)
    (h : PairsOK μ δ N c ⟨d, 0⟩) :
    ∃ (F : Finset ((ℚ × ℚ) × ℝ)) (S : Set ℂ), BallFamOK μ δ F ∧ F.card ≤ (7 + 1) * N ∧
      IsPathConnected S ∧ (∀ k ≤ 7 + 1, c + (k : ℕ) * (⟨d, 0⟩ : ℂ) ∈ S) ∧ S ⊆ famCov F ∧
      ∀ z ∈ S, |z.im - c.im| ≤ d := by
  obtain ⟨F, S, hF, hc, hS, hp, hSF, hSK⟩ := chain_tilde (μ := μ) (δ := δ) c ⟨d, 0⟩ N 7 h
  exact ⟨F, S, hF, hc, hS, hp, hSF, fun z hz => strip_im hd (hSK hz)⟩

/-- a vertical chain of eight tilde geodesics -/
theorem chain8_vert {μ : Measure ℂ} {δ : ℝ} {N : ℕ} {c : ℂ} {d : ℝ} (hd : 0 < d)
    (h : PairsOK μ δ N c ⟨0, d⟩) :
    ∃ (F : Finset ((ℚ × ℚ) × ℝ)) (S : Set ℂ), BallFamOK μ δ F ∧ F.card ≤ (7 + 1) * N ∧
      IsPathConnected S ∧ (∀ k ≤ 7 + 1, c + (k : ℕ) * (⟨0, d⟩ : ℂ) ∈ S) ∧ S ⊆ famCov F ∧
      ∀ z ∈ S, |z.re - c.re| ≤ d := by
  obtain ⟨F, S, hF, hc, hS, hp, hSF, hSK⟩ := chain_tilde (μ := μ) (δ := δ) c ⟨0, d⟩ N 7 h
  exact ⟨F, S, hF, hc, hS, hp, hSF, fun z hz => strip_re hd (hSK hz)⟩

/-- **the deterministic gluing of Fig. glue** (DZZ l. 2562–2566, 2605; DEC-117 §2(c)): if the 40
tilde distances between neighbouring red points are `≤ N`, `x` lies in the inner square and `y`
outside the outer square, then `D_δ(v, y) ≤ D_δ(x, y) + 40 N`. -/
theorem ring_glue_lgd {μ : Measure ℂ} {δ : ℝ} {v : ℂ} {d : ℝ} (hd : 0 < d) {N : ℕ}
    (hpair : ∀ j : Fin 5, PairsOK μ δ N (ringC v d j) (ringW d j)) {x y : ℂ}
    (hx : |x.re - v.re| ≤ 2 * d ∧ |x.im - v.im| ≤ 2 * d)
    (hy : 4 * d ≤ |y.re - v.re| ∨ 4 * d ≤ |y.im - v.im|) :
    lgdDZZ μ δ v y ≤ lgdDZZ μ δ x y + ((40 * N : ℕ) : ℕ∞) := by
  classical
  rcases eq_top_or_lt_top (lgdDZZ μ δ x y) with htop | hlt
  · rw [htop, top_add]; exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  obtain ⟨F₁, γ₁, hF₁, hc₁, hr₁⟩ :=
    exists_fam_of_lgdDZZ_le (μ := μ) (δ := δ) (x := x) (y := y) (n := n) hn.ge
  have hsub₁ : γ₁.extend '' Icc 0 1 ⊆ range γ₁ := by
    rintro _ ⟨s, -, rfl⟩; exact ⟨_, rfl⟩
  have hT₁ : IsPathConnected (γ₁.extend '' Icc 0 1) :=
    ((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.2 zero_le_one)).image
      γ₁.continuous_extend
  have hT₁x : x ∈ γ₁.extend '' Icc 0 1 := ⟨0, left_mem_Icc.2 zero_le_one, by simp⟩
  have hT₁y : y ∈ γ₁.extend '' Icc 0 1 := ⟨1, right_mem_Icc.2 zero_le_one, by simp⟩
  -- the five chains
  obtain ⟨F0, S0, hF0, hc0, hS0, hp0, hSF0, hSK0⟩ :=
    chain8_horiz (c := ringC v d 0) hd (hpair 0)
  obtain ⟨F1, S1, hF1, hc1, hS1, hp1, hSF1, hSK1⟩ :=
    chain8_horiz (c := ringC v d 1) hd (hpair 1)
  obtain ⟨F2, S2, hF2, hc2, hS2, hp2, hSF2, hSK2⟩ :=
    chain8_vert (c := ringC v d 2) hd (hpair 2)
  obtain ⟨F3, S3, hF3, hc3, hS3, hp3, hSF3, hSK3⟩ :=
    chain8_vert (c := ringC v d 3) hd (hpair 3)
  obtain ⟨F4, S4, hF4, hc4, hS4, hp4, hSF4, hSK4⟩ :=
    chain8_vert (c := ringC v d 4) hd (hpair 4)
  have e0 : ringC v d 0 = v + ⟨-4 * d, -3 * d⟩ := rfl
  have e1 : ringC v d 1 = v + ⟨-4 * d, 3 * d⟩ := rfl
  have e2 : ringC v d 2 = v + ⟨-3 * d, -4 * d⟩ := rfl
  have e3 : ringC v d 3 = v + ⟨3 * d, -4 * d⟩ := rfl
  have e4 : ringC v d 4 = v + ⟨0, -3 * d⟩ := rfl
  rw [e0] at hp0 hSK0
  rw [e1] at hp1 hSK1
  rw [e2] at hp2 hSK2
  rw [e3] at hp3 hSK3
  rw [e4] at hp4
  -- strips
  have hI0 : ∀ z ∈ S0, z.im ∈ Icc (v.im - 4 * d) (v.im - 2 * d) := fun z hz => by
    have h := hSK0 z hz; simp only [Complex.add_im] at h
    rw [abs_le] at h; constructor <;> linarith [h.1, h.2]
  have hI1 : ∀ z ∈ S1, z.im ∈ Icc (v.im + 2 * d) (v.im + 4 * d) := fun z hz => by
    have h := hSK1 z hz; simp only [Complex.add_im] at h
    rw [abs_le] at h; constructor <;> linarith [h.1, h.2]
  have hI2 : ∀ z ∈ S2, z.re ∈ Icc (v.re - 4 * d) (v.re - 2 * d) := fun z hz => by
    have h := hSK2 z hz; simp only [Complex.add_re] at h
    rw [abs_le] at h; constructor <;> linarith [h.1, h.2]
  have hI3 : ∀ z ∈ S3, z.re ∈ Icc (v.re + 2 * d) (v.re + 4 * d) := fun z hz => by
    have h := hSK3 z hz; simp only [Complex.add_re] at h
    rw [abs_le] at h; constructor <;> linarith [h.1, h.2]
  obtain ⟨Mb, hMbS, hMb, hMbR, hMb0, hMb1⟩ := sub_LR_pc (X0 := v.re - 4 * d) (X3 := v.re + 4 * d) hS0 hI0 (hp0 0 (by norm_num))
    (hp0 8 le_rfl) (by simp; ring) (by simp; ring) (by linarith)
  obtain ⟨Mt, hMtS, hMt, hMtR, hMt0, hMt1⟩ := sub_LR_pc (X0 := v.re - 4 * d) (X3 := v.re + 4 * d) hS1 hI1 (hp1 0 (by norm_num))
    (hp1 8 le_rfl) (by simp; ring) (by simp; ring) (by linarith)
  obtain ⟨Ml, hMlS, hMl, hMlR, hMl0, hMl1⟩ := sub_BT_pc (Y0 := v.im - 4 * d) (Y3 := v.im + 4 * d) hS2 hI2 (hp2 0 (by norm_num))
    (hp2 8 le_rfl) (by simp; ring) (by simp; ring) (by linarith)
  obtain ⟨Mr, hMrS, hMr, hMrR, hMr0, hMr1⟩ := sub_BT_pc (Y0 := v.im - 4 * d) (Y3 := v.im + 4 * d) hS3 hI3 (hp3 0 (by norm_num))
    (hp3 8 le_rfl) (by simp; ring) (by simp; ring) (by linarith)
  have hxin : x ∈ Icc (v.re - 2 * d) (v.re + 2 * d) ×ℂ Icc (v.im - 2 * d) (v.im + 2 * d) := by
    rw [abs_le] at hx; rw [abs_le] at hx
    exact Complex.mem_reProdIm.2 ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩,
      ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩⟩
  have hyout : y ∉ Ioo (v.re - 4 * d) (v.re + 4 * d) ×ℂ Ioo (v.im - 4 * d) (v.im + 4 * d) := by
    intro h
    rw [Complex.mem_reProdIm] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    rcases hy with hy | hy
    · rw [le_abs] at hy; rcases hy with hy | hy <;> linarith
    · rw [le_abs] at hy; rcases hy with hy | hy <;> linarith
  have hmeet := dzz_ring_sep (by linarith : v.re - 4 * d < v.re - 2 * d)
    (by linarith : v.re + 2 * d < v.re + 4 * d) (by linarith : v.im - 4 * d < v.im - 2 * d)
    (by linarith : v.im + 2 * d < v.im + 4 * d) hMb hMbR hMb0 hMb1 hMt hMtR hMt0 hMt1
    hMl hMlR hMl0 hMl1 hMr hMrR hMr0 hMr1 hT₁ hT₁x hT₁y hxin hyout
  have hR := dzz_ring_isPathConnected (by linarith : v.re - 4 * d ≤ v.re - 2 * d)
    (by linarith : v.re - 2 * d ≤ v.re + 2 * d) (by linarith : v.re + 2 * d ≤ v.re + 4 * d)
    (by linarith : v.im - 4 * d ≤ v.im - 2 * d) (by linarith : v.im - 2 * d ≤ v.im + 2 * d)
    (by linarith : v.im + 2 * d ≤ v.im + 4 * d) hMb hMbR hMb0 hMb1 hMt hMtR hMt0 hMt1
    hMl hMlR hMl0 hMl1 hMr hMrR hMr0 hMr1
  set T₁ := γ₁.extend '' Icc 0 1 with hT₁def
  set R := Mb ∪ Mt ∪ Ml ∪ Mr with hRdef
  obtain ⟨m, hm⟩ := hMb0
  have h1 : IsPathConnected (T₁ ∪ R) := hT₁.union hR hmeet
  have h2 : IsPathConnected (T₁ ∪ R ∪ S0) :=
    h1.union hS0 ⟨m, Or.inr (Or.inl (Or.inl (Or.inl hm.1))), hMbS hm.1⟩
  have hc4 : v + (⟨0, -3 * d⟩ : ℂ) ∈ S0 := by
    convert hp0 4 (by norm_num) using 1; apply Complex.ext <;> simp
  have h3 : IsPathConnected (T₁ ∪ R ∪ S0 ∪ S4) :=
    h2.union hS4 ⟨_, Or.inr hc4, by simpa using hp4 0 (by norm_num)⟩
  have hv : v ∈ T₁ ∪ R ∪ S0 ∪ S4 := by
    refine Or.inr ?_
    convert hp4 3 (by norm_num) using 1; apply Complex.ext <;> simp
  have hcov : T₁ ∪ R ∪ S0 ∪ S4 ⊆ famCov (F₁ ∪ F0 ∪ F1 ∪ F2 ∪ F3 ∪ F4) := by
    simp only [famCov_union]
    intro z hz
    rcases hz with ((hz | hz) | hz) | hz
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hr₁ (hsub₁ hz))))))
    · rcases hz with ((hz | hz) | hz) | hz
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hSF0 (hMbS hz))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (hSF1 (hMtS hz)))))
      · exact Or.inl (Or.inl (Or.inr (hSF2 (hMlS hz))))
      · exact Or.inl (Or.inr (hSF3 (hMrS hz)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hSF0 hz)))))
    · exact Or.inr (hSF4 hz)
  have hok : BallFamOK μ δ (F₁ ∪ F0 ∪ F1 ∪ F2 ∪ F3 ∪ F4) :=
    ((((hF₁.union hF0).union hF1).union hF2).union hF3).union hF4
  have hle := lgdDZZ_le_card hok h3 hcov hv (Or.inl (Or.inl (Or.inl hT₁y)))
  have hcard : (F₁ ∪ F0 ∪ F1 ∪ F2 ∪ F3 ∪ F4).card ≤ n + 40 * N := by
    have e1 := Finset.card_union_le (F₁ ∪ F0 ∪ F1 ∪ F2 ∪ F3) F4
    have e2 := Finset.card_union_le (F₁ ∪ F0 ∪ F1 ∪ F2) F3
    have e3 := Finset.card_union_le (F₁ ∪ F0 ∪ F1) F2
    have e4 := Finset.card_union_le (F₁ ∪ F0) F1
    have e5 := Finset.card_union_le F₁ F0
    omega
  rw [← hn]
  refine hle.trans ?_
  exact_mod_cast hcard

end DZZ
end LQGMetric
