/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32F5 at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32F2

/-!
# DZZ (eq-B-good-Psi) at `μIn`: the deterministic reduction (P2-DZZ32F)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1149–1153): "Consider the balls centered at corners
of some `B̃_i` with radius `ts`. The collection of these `4/t+2` balls covers a line segment from `x`
to `∂B_large`, and each ball is covered by at most 4 boxes in `{B̂_j}`. Consequently, on the event
`{M_{γ,s}(B) ≤ δ²} ∩ 𝓔_{δ,α}`, … `D_{γ,δ}(x, ∂B_large) > δ^{-ι} λ` … implies that
`M̃_{γ,ε²s,η}(B̂_j) > 4^{-1} s² e^{−2αγ√L log L}` for some `j`".

At `μIn` the balls must lie in `𝕍` and the path in `𝕍_{−r}`; DZZ's horizontal segment through `x`
cannot be covered this way when `x` is at depth `r ≪ ts` (handoff/P2-DZZETA2.md, DV-ETA2d).
**`P32StartGeomS`** (deterministic, S3P32G3) is the cover statement used instead: for
`r ≤ s_B / 2`, a path from `x` to
`∂B_large` inside `𝕍_{−r}` covered by `≤ 8·2^{N−n_B} + 4j + 16` balls inside `𝕍`, each inside
`≤ 4` level-`N` boxes near `c_B` (`2^{-N} ≤ 2^j r`; the `4j` balls are the escape chain from the
walls).

* `ballPathLeC_of_geom`: on the open event of these boxes and (eq-M-tilde-B-bound), the path gives
  `D_δ(x, ∂B_large) ≤ R` (DZZ l. 1150–1152, deterministic).
* `exists_finset_largeBox`: the boxes of level `n` with `x ∈ B_large` are among `9` boxes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- The cover data of a start path (D102 P-4bW, (eq-B-good-Psi) at `μIn`). -/
def StartCover (B : DyBox) (N : ℕ) (r : ℝ) (x : ℂ) (M : ℝ) (S : Finset (ℂ × ℝ))
    (T : Finset DyBox) : Prop :=
  (S.card : ℝ) ≤ M ∧ T.card ≤ 4 * S.card ∧
    (∃ (w : ℂ) (p : Path x w), w ∈ frontier B.largeBox ∧ (∀ t, p t ∈ dzzVIn r) ∧
      ∀ t, ∃ q ∈ S, p t ∈ Metric.ball q.1 q.2) ∧
    (∀ q ∈ S, Metric.ball q.1 q.2 ⊆ dzzV ∧
      ∃ Tq ⊆ T, Tq.card ≤ 4 ∧ Metric.ball q.1 q.2 ⊆ ⋃ b ∈ Tq, b.closedBox) ∧
    ∀ b ∈ T, b.n = N ∧ ∀ z ∈ b.closedBox, ‖z - B.center‖ ≤ 3 * B.side

variable {Ω : Type*} [MeasurableSpace Ω] {W : WNSpace → Ω → ℝ}

/-- **DZZ l. 1150–1152 at `μIn`** (deterministic). -/
lemma ballPathLeC_of_geom {γ δh δ r M R : ℝ} {ω : Ω} {B : DyBox} {N : ℕ} {x : ℂ}
    {S : Finset (ℂ × ℝ)} {T : Finset DyBox} (hc : StartCover B N r x M S T) {K θ : ℝ≥0∞}
    (hup : ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - B.center‖ ≤ 3 * B.side) →
      wickQArea γ W ω b'.closedBox ≤ K * etaChaos W γ δh b'.closedBox ω)
    (hopen : ∀ b ∈ T, etaChaos W γ δh b.closedBox ω ≤ θ)
    (hKθ : 4 * (K * θ) ≤ ENNReal.ofReal (δ ^ 2)) (hMR : M ≤ R) :
    BallPathLeC (dzzMuIn γ W ω) δ r x (frontier B.largeBox) R := by
  obtain ⟨hS, -, ⟨w, p, hw, hpath, hcov⟩, hball, hT⟩ := hc
  refine ⟨S, w, p, hw, hS.trans hMR, hpath, fun q hq => ?_, hcov⟩
  obtain ⟨hsub, Tq, hTq, hTq4, hcovq⟩ := hball q hq
  refine (dzzMuIn_ball_le_of_boxes hup hsub Tq hcovq (fun b hb => (hT b (hTq hb)).2)
    (fun b hb => hopen b (hTq hb))).trans ?_
  refine le_trans ?_ hKθ
  exact mul_le_mul_left (by exact_mod_cast hTq4) _

lemma floor_bounds_of_largeBox {b : DyBox} {x : ℂ} (hx : x ∈ b.largeBox) :
    ⌊x.re * 2 ^ b.n⌋ - 1 ≤ (b.j : ℤ) ∧ (b.j : ℤ) ≤ ⌊x.re * 2 ^ b.n⌋ + 1 ∧
      ⌊x.im * 2 ^ b.n⌋ - 1 ≤ (b.k : ℤ) ∧ (b.k : ℤ) ≤ ⌊x.im * 2 ^ b.n⌋ + 1 := by
  obtain ⟨h1, h2⟩ := hx
  have hs : b.side * 2 ^ b.n = 1 := by
    rw [DyBox.side, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have hp : (0 : ℝ) < 2 ^ b.n := by positivity
  simp only [DyBox.center] at h1 h2
  rw [abs_le] at h1 h2
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨a3, a4⟩ := h2
  have e1 : x.re * 2 ^ b.n - ((b.j : ℝ) + 1 / 2) = (x.re - (b.j + 1 / 2) * b.side) * 2 ^ b.n := by
    rw [sub_mul, mul_assoc, hs, mul_one]
  have e2 : x.im * 2 ^ b.n - ((b.k : ℝ) + 1 / 2) = (x.im - (b.k + 1 / 2) * b.side) * 2 ^ b.n := by
    rw [sub_mul, mul_assoc, hs, mul_one]
  have m1 := mul_le_mul_of_nonneg_right a2 hp.le
  have m2 := mul_le_mul_of_nonneg_right a1 hp.le
  have m3 := mul_le_mul_of_nonneg_right a4 hp.le
  have m4 := mul_le_mul_of_nonneg_right a3 hp.le
  rw [hs] at m1 m3
  rw [neg_mul, hs] at m2 m4
  rw [← e1] at m1 m2
  rw [← e2] at m3 m4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ⌊x.re * 2 ^ b.n⌋ < (b.j : ℤ) + 2 := Int.floor_lt.2 (by push_cast; linarith)
    omega
  · have : (b.j : ℤ) - 1 ≤ ⌊x.re * 2 ^ b.n⌋ := Int.le_floor.2 (by push_cast; linarith)
    omega
  · have : ⌊x.im * 2 ^ b.n⌋ < (b.k : ℤ) + 2 := Int.floor_lt.2 (by push_cast; linarith)
    omega
  · have : (b.k : ℤ) - 1 ≤ ⌊x.im * 2 ^ b.n⌋ := Int.le_floor.2 (by push_cast; linarith)
    omega

/-- the level-`n` boxes `b` with `x ∈ b_large` are among `9` boxes -/
lemma exists_finset_largeBox (n : ℕ) (x : ℂ) :
    ∃ F : Finset DyBox, F.card ≤ 9 ∧ ∀ b : DyBox, b.n = n → x ∈ b.largeBox → b ∈ F := by
  classical
  set c : ℤ × ℤ := (⌊x.re * 2 ^ n⌋ - 1, ⌊x.im * 2 ^ n⌋ - 1)
  refine ⟨((Finset.Icc (0 : ℤ) 2) ×ˢ (Finset.Icc (0 : ℤ) 2)).image (siteBox n c), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp
  · intro b hb hx
    obtain ⟨f1, f2, f3, f4⟩ := floor_bounds_of_largeBox hx
    rw [hb] at f1 f2 f3 f4
    refine Finset.mem_image.2 ⟨boxSite c b, ?_, siteBox_boxSite c b hb⟩
    simp only [boxSite, Finset.mem_product, Finset.mem_Icc, c]
    omega

end DZZ
end LQGMetric
