/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UClip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Up

/-!
# DZZ Proposition 3.2, upper bound at the walled measure: clipped rings (D101)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Proposition 3.2, upper bound,
l. 1088–1153, and Remark 5.2 (l. 2288–2290: the §3 results "extend automatically" to the confined
distances `D^A` of l. 2268). Decision D101 (decisions/DEC-101.md): DZZ's internal distance is the
walled `lgdDZZ (dzzWall dzzV (M^W))` (D97) for the upper bound as well; since no open ball inside
the closed square contains a point of `∂𝕍`, DZZ's covering of the ring boundaries `∂B'` by balls of
radius `ts` centred at grid corners (l. 1131–1137) is replaced, for boxes touching `∂𝕍`, by the
covering of the boundary of the **clipped** box `B' ∩ 𝕍_{−r}` (`𝕍_{−r} = [r, 1−r]²`, `r ≤ ts`) by
the same balls, their centres on `∂𝕍` moved inward by `ts`. DZZ's admissible pairs lie in `𝕍^ξ`
(l. 792), so the ends are never clipped.

* `dzzVIn r`: the closed square `𝕍_{−r}`.
* `cellPhiC μ δ r b`, `PhiLeC`: `Φ` of the clipped box; `BallPathLeC`, `BallStartCondC`: the end
  conditions of `S3P32UDefs` with paths in `𝕍_{−r}`.
* `L32BallCrossingC` (open, deterministic): the clipped version of `L32BallCrossing`
  (`l32BallCrossing_holds`), for `2r` smaller than the side of every ring box.
* `L32EncPhiHPC`, `L32StartPhiHPC` (open, probabilistic): (eq-B-percolation-Psi) and
  (eq-B-good-Psi) for the clipped boxes, with a clipping depth `r δ`.
* **`l32UpperCross_ofC`**: `L32UpperCross P γ W μ ξ ξd` from these three, as `l32UpperCross_of`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The closed square `𝕍_{−r} = [r, 1−r]²`. -/
def dzzVIn (r : ℝ) : Set ℂ := {z | r ≤ z.re ∧ z.re ≤ 1 - r ∧ r ≤ z.im ∧ z.im ≤ 1 - r}

lemma dzzVIn_sub_dzzV {r : ℝ} (hr : 0 ≤ r) : dzzVIn r ⊆ dzzV := fun z hz =>
  ⟨hr.trans hz.1, hz.2.1.trans (by linarith), hr.trans hz.2.2.1, hz.2.2.2.trans (by linarith)⟩

/-- A point of `𝕍` is at distance at least its distance to the four edge lines from `∂𝕍`. -/
lemma infDist_frontier_dzzV_le {v : ℂ} (hv : v ∈ dzzV) :
    Metric.infDist v (frontier dzzV) ≤ v.re ∧ Metric.infDist v (frontier dzzV) ≤ 1 - v.re ∧
      Metric.infDist v (frontier dzzV) ≤ v.im ∧ Metric.infDist v (frontier dzzV) ≤ 1 - v.im := by
  -- a point `w ∈ dzzV` with points of `dzzVᶜ` arbitrarily close is in the frontier
  have key : ∀ w : ℂ, w ∈ dzzV → (∀ ε > 0, ∃ y : ℂ, y ∉ dzzV ∧ dist w y ≤ ε) →
      w ∈ frontier dzzV := by
    intro w hw hy
    refine ⟨subset_closure hw, fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    obtain ⟨y, hyV, hyd⟩ := hy (ε / 2) (by positivity)
    exact hyV (hball (by rw [Metric.mem_ball, dist_comm]; linarith))
  obtain ⟨h0, h1, h2, h3⟩ := hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (Metric.infDist_le_dist_of_mem (key ⟨0, v.im⟩ ⟨le_rfl, by norm_num, h2, h3⟩
      fun ε hε => ⟨⟨-ε, v.im⟩, fun h => by linarith [h.1], ?_⟩)).trans ?_
    · rw [Complex.dist_of_im_eq (by rfl), Real.dist_eq]
      show |(0 : ℝ) - -ε| ≤ ε
      rw [sub_neg_eq_add, zero_add, abs_of_pos hε]
    · rw [Complex.dist_of_im_eq (by rfl), Real.dist_eq]
      show |v.re - 0| ≤ v.re
      rw [sub_zero, abs_of_nonneg h0]
  · refine (Metric.infDist_le_dist_of_mem (key ⟨1, v.im⟩ ⟨by norm_num, le_rfl, h2, h3⟩
      fun ε hε => ⟨⟨1 + ε, v.im⟩, fun h => by linarith [h.2.1], ?_⟩)).trans ?_
    · rw [Complex.dist_of_im_eq (by rfl), Real.dist_eq]
      show |(1 : ℝ) - (1 + ε)| ≤ ε
      rw [show (1 : ℝ) - (1 + ε) = -ε by ring, abs_neg, abs_of_pos hε]
    · rw [Complex.dist_of_im_eq (by rfl), Real.dist_eq]
      show |v.re - 1| ≤ 1 - v.re
      rw [show v.re - 1 = -(1 - v.re) by ring, abs_neg, abs_of_nonneg (by linarith)]
  · refine (Metric.infDist_le_dist_of_mem (key ⟨v.re, 0⟩ ⟨h0, h1, le_rfl, by norm_num⟩
      fun ε hε => ⟨⟨v.re, -ε⟩, fun h => by linarith [h.2.2.1], ?_⟩)).trans ?_
    · rw [Complex.dist_of_re_eq (by rfl), Real.dist_eq]
      show |(0 : ℝ) - -ε| ≤ ε
      rw [sub_neg_eq_add, zero_add, abs_of_pos hε]
    · rw [Complex.dist_of_re_eq (by rfl), Real.dist_eq]
      show |v.im - 0| ≤ v.im
      rw [sub_zero, abs_of_nonneg h2]
  · refine (Metric.infDist_le_dist_of_mem (key ⟨v.re, 1⟩ ⟨h0, h1, by norm_num, le_rfl⟩
      fun ε hε => ⟨⟨v.re, 1 + ε⟩, fun h => by linarith [h.2.2.2], ?_⟩)).trans ?_
    · rw [Complex.dist_of_re_eq (by rfl), Real.dist_eq]
      show |(1 : ℝ) - (1 + ε)| ≤ ε
      rw [show (1 : ℝ) - (1 + ε) = -ε by ring, abs_neg, abs_of_pos hε]
    · rw [Complex.dist_of_re_eq (by rfl), Real.dist_eq]
      show |v.im - 1| ≤ 1 - v.im
      rw [show v.im - 1 = -(1 - v.im) by ring, abs_neg, abs_of_nonneg (by linarith)]

/-- `𝕍^ξ ⊆ 𝕍_{−r}` for `r ≤ ξ` (DZZ l. 792: admissible pairs are never clipped). -/
lemma dzzVXi_sub_dzzVIn {ξ r : ℝ} (h : r ≤ ξ) : dzzVXi ξ ⊆ dzzVIn r := by
  intro v hv
  obtain ⟨h0, h1, h2, h3⟩ := infDist_frontier_dzzV_le hv.1
  have := hv.2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `Φ` of the box `b` clipped at depth `r`: the least number of open balls of `μ`-mass at most
`δ²` covering `∂(B ∩ 𝕍_{−r})`. -/
def cellPhiC (μ : Measure ℂ) (δ r : ℝ) (b : DyBox) : ℕ∞ :=
  ⨅ (S : Finset (ℂ × ℝ)) (_ : frontier (b.closedBox ∩ dzzVIn r) ⊆ ⋃ p ∈ S, Metric.ball p.1 p.2)
    (_ : ∀ p ∈ S, μ (Metric.ball p.1 p.2) ≤ ENNReal.ofReal (δ ^ 2)), (S.card : ℕ∞)

/-- `Φ_{B ∩ 𝕍_{−r}, δ} ≤ λ`. -/
def PhiLeC (μ : Measure ℂ) (δ r : ℝ) (b : DyBox) (lam : ℝ) : Prop :=
  ∃ N : ℕ, cellPhiC μ δ r b = N ∧ (N : ℝ) ≤ lam

/-- `D_δ(x, S) ≤ R` along a path in `𝕍_{−r}`. -/
def BallPathLeC (μ : Measure ℂ) (δ r : ℝ) (x : ℂ) (S : Set ℂ) (R : ℝ) : Prop :=
  ∃ (T : Finset (ℂ × ℝ)) (w : ℂ) (p : Path x w), w ∈ S ∧ (T.card : ℝ) ≤ R ∧
    (∀ t, p t ∈ dzzVIn r) ∧ (∀ q ∈ T, μ (Metric.ball q.1 q.2) ≤ ENNReal.ofReal (δ ^ 2)) ∧
    ∀ t, ∃ q ∈ T, p t ∈ Metric.ball q.1 q.2

/-- The end condition `BallStartCond` with paths in `𝕍_{−r}`. -/
def BallStartCondC (μ : Measure ℂ) (m : DyBox → ℝ) (δ r R : ℝ) (A : Set ℂ) : Prop :=
  (∃ u, A = {u} ∧ ∀ b, IsCell m δ b → u ∈ b.largeBox →
      BallPathLeC μ δ r u (frontier b.largeBox) R) ∨
    (IsConnected A ∧ ∀ b, IsCell m δ b → ¬ A ⊆ b.largeBox)

/-- **The clipped crossing claim for balls** (open, deterministic; D101): `L32BallCrossing` with
the rings `∂B'` replaced by `∂(B' ∩ 𝕍_{−r})`, where `2r` is smaller than the side `2^{-(n+k)}` of
every ring box and the ends lie in `𝕍_{−r}`. -/
def L32BallCrossingC : Prop :=
  ∀ (m : DyBox → ℝ) (μ : Measure ℂ) (δ lam R r : ℝ) (k N₀ : ℕ) (A B : Set ℂ), 0 < δ → 1 ≤ lam →
    0 ≤ R → 0 < r → 2 * r < (2⁻¹ : ℝ) ^ (N₀ + k) →
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) → (∀ b, IsCell m δ b → b.n ≤ N₀) →
    (∀ b, IsCell m δ b → 1 ≤ b.n) →
    (∀ b, IsCell m δ b → HasEnclosure b k fun b' => PhiLeC μ δ r b' lam) →
    A ⊆ dzzVIn r → B ⊆ dzzVIn r → A.Nonempty → B.Nonempty →
    BallStartCondC μ m δ r R A → BallStartCondC μ m δ r R B →
    ((lgdMinSet μ δ A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) +
        ENNReal.ofReal (2 * R + 8)

/-- `D_δ(x, ∂𝖢_large) ≤ δ^{-ι} λ` along a path in `𝕍_{−r}`, for all cells with `x ∈ 𝖢_large`. -/
def startPhiC (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (r δ ι : ℝ) (x : ℂ) :
    Set Ω :=
  {ω | ∀ b, IsCell (approxLQG γ W ω) δ b → x ∈ b.largeBox →
    BallPathLeC (μ ω) δ r x (frontier b.largeBox) (δ ^ (-ι) * lamP32 δ)}

/-- **(eq-B-good-Psi) with paths in `𝕍_{−r δ}` + union bound** (open; D101), uniformly in
`x ∈ 𝕍_{−r δ}`. -/
def L32StartPhiHPC (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ)
    (r : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ x ∈ dzzVIn (r δ),
    P (startPhiC γ W μ (r δ) δ (dzzCMc γ / 2) x)ᶜ ≤ ENNReal.ofReal (δ ^ c)

/-- The start event of an end `A` (trivial unless `A` is a point). -/
def startPhiEvC (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (r δ ι : ℝ) (A : Set ℂ) :
    Set Ω :=
  {ω | ∀ u, A = {u} → ω ∈ startPhiC γ W μ r δ ι u}

lemma startPhiEvC_bound {P : Measure Ω} {γ r δ ι : ℝ} {W : WNSpace → Ω → ℝ}
    {μ : Ω → Measure ℂ} {A : Set ℂ} {q : ℝ≥0∞}
    (h : ∀ u ∈ dzzVIn r, P (startPhiC γ W μ r δ ι u)ᶜ ≤ q) (hA : A ⊆ dzzVIn r) :
    P (startPhiEvC γ W μ r δ ι A)ᶜ ≤ q := by
  by_cases hs : ∃ u, A = {u}
  · obtain ⟨u, rfl⟩ := hs
    have e : startPhiEvC γ W μ r δ ι {u} = startPhiC γ W μ r δ ι u := by
      ext ω
      refine ⟨fun h => h u rfl, fun h u' hu' => ?_⟩
      obtain rfl := Set.singleton_eq_singleton_iff.1 hu'
      exact h
    rw [e]; exact h u (hA rfl)
  · have e : startPhiEvC γ W μ r δ ι A = univ := by
      ext ω
      simp only [startPhiEvC, mem_ofPred_eq, mem_univ, iff_true]
      intro u hu; exact absurd ⟨u, hu⟩ hs
    rw [e, compl_univ, measure_empty]; exact bot_le

/-- The clipping depths: `0 < r δ` and `4 r δ < δ^{C_mc} 2^{-k}` (smaller than the side of every
ring box on the regularity event of Lemma 3.1), for all `δ ∈ (0,1)`. -/
def IsClipDepth (γ : ℝ) (r : ℝ → ℝ) : Prop :=
  ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < r δ ∧ 4 * r δ < δ ^ dzzCmc γ * (2⁻¹ : ℝ) ^ kL37 γ δ

end DZZ
end LQGMetric
