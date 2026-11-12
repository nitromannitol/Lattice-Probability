/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.DFLem71Sym at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.DFLem71Loc

/-!
# DF Lemma 7.1: one comparison step, used for both bounds

Dubédat–Falconet, arXiv:1809.02607, proof of Lemma 7.1 (`LiouvilleMetricStarScale.tex`
DF:1310–1342). DF's upper bound (DF:1310–1322) cuts a geodesic of the limit `e^f·d_∞` into small
pieces and estimates `e^f·d_n` along the chain; the lower bound (DF:1330–1342) does the same with
the roles exchanged (a geodesic of `e^f·d_n`, then `e^f·d_∞` along the chain). Both are one
statement (`dfl71_sym`): a path `P` parametrized by `D`-length, staying in `B_{r'}(0)`, is cut at
`P (i L / N)`; the metrics `D`, `D'` and the functions `g`, `g'` are `ε`-close on
`B̄_{r'+1}(0)` to a reference metric `D_ref` and function `F` (in the application: the limits
`D`, `f`), whose `D_ref`-modulus of continuity is `θ` at scale `δ` (DF's `ω(f, ·)`, DF:1307). The
local comparison and the triangle inequality (`dfl71_chain`) give

  `(e^{ξ g'}·D')(P 0, P L) ≤ e^ω ∫_0^L e^{ξ g(P t)} dt + N e^{|ξ|M+1} (2ε + η)`.

The sphere gap `d₁` keeps short `D'`-paths from `B̄_{r'}(0)` inside `B̄_{r'+1}(0)` (DF:1305).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS

open MetricGeometry

theorem dfl71Grid_mem {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i ≤ N) :
    dfl71Grid L N i ∈ Icc 0 L := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hiN : (i : ℝ) ≤ N := Nat.cast_le.2 hi
  refine ⟨by unfold dfl71Grid; positivity, ?_⟩
  unfold dfl71Grid
  rw [div_le_iff₀ hNr]
  nlinarith

theorem dfl71_sym {D D' : ContMetric} (hD' : D'.IsLength) {Dref : ℂ × ℂ → ℝ} {ξ M : ℝ}
    {g g' F : C(ℂ, ℝ)} (hF : ∀ z, |F z| ≤ M) {r' ε θ δ d₁ ω : ℝ} (hε : 0 ≤ ε) (hω : 0 < ω)
    (hω1 : ω ≤ 1)
    (hDD : ∀ u ∈ closedBall (0 : ℂ) (r' + 1), ∀ v ∈ closedBall (0 : ℂ) (r' + 1),
      |D.1 (u, v) - Dref (u, v)| ≤ ε)
    (hD'D : ∀ u ∈ closedBall (0 : ℂ) (r' + 1), ∀ v ∈ closedBall (0 : ℂ) (r' + 1),
      |D'.1 (u, v) - Dref (u, v)| ≤ ε)
    (hg : ∀ z ∈ closedBall (0 : ℂ) (r' + 1), |g z - F z| ≤ ε)
    (hg' : ∀ z ∈ closedBall (0 : ℂ) (r' + 1), |g' z - F z| ≤ ε)
    (hεθ : ε ≤ θ) (hθ : 2 * |ξ| * θ ≤ ω / 2)
    (hmod : ∀ u ∈ closedBall (0 : ℂ) (r' + 1), ∀ q ∈ closedBall (0 : ℂ) (r' + 1),
      Dref (u, q) ≤ δ → |F u - F q| ≤ θ)
    (hgap1 : ∀ u ∈ closedBall (0 : ℂ) r', ∀ y ∈ sphere (0 : ℂ) (r' + 1), d₁ ≤ Dref (u, y))
    {P : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hin : ∀ t ∈ Icc 0 L, P t ∈ ball (0 : ℂ) r') {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η)
    (hNδ : L / N + 3 * ε + η ≤ δ) (hNd : L / N + 3 * ε + η < d₁) :
    weylScale ξ g' D' (P 0) (P L) ≤
      ENNReal.ofReal (Real.exp ω) * (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t)))) +
        N * ENNReal.ofReal (Real.exp (|ξ| * M + 1) * (2 * ε + η)) := by
  have hξ := abs_nonneg ξ
  have hK : ∀ t ∈ Icc 0 L, P t ∈ closedBall (0 : ℂ) (r' + 1) := fun t ht =>
    ball_subset_closedBall (ball_subset_ball (by linarith) (hin t ht))
  have hK' : ∀ t ∈ Icc 0 L, P t ∈ closedBall (0 : ℂ) r' := fun t ht =>
    ball_subset_closedBall (hin t ht)
  have hlip := lipschitzOnWith_of_hasUnitSpeedOn hu
  have hDP : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) ≤ |s - t| := by
    intro s hs t ht
    have := hlip.dist_le_mul s hs t ht
    simp only [Function.comp_apply, NNReal.coe_one, one_mul, Real.dist_eq] at this
    exact this
  have hstep : ∀ i : ℕ, dfl71Grid L N (i + 1) - dfl71Grid L N i = L / N := by
    intro i; simp only [dfl71Grid]; push_cast; ring
  have hgi : ∀ i < N, dfl71Grid L N i ∈ Icc 0 L := fun i hi => dfl71Grid_mem hL hN hi.le
  have hgi1 : ∀ i < N, dfl71Grid L N (i + 1) ∈ Icc 0 L := fun i hi => dfl71Grid_mem hL hN hi
  refine dfl71_chain hD' (g := g) hL hN (ε := 2 * ε) (by linarith) hη ?_ ?_
  · -- consecutive points
    intro i hi
    have h1 := hDP _ (hgi i hi) _ (hgi1 i hi)
    rw [abs_sub_comm, abs_of_nonneg (by rw [hstep]; exact div_nonneg hL (Nat.cast_nonneg _)),
      hstep] at h1
    have h2 := abs_le.1 (hDD _ (hK _ (hgi i hi)) _ (hK _ (hgi1 i hi)))
    have h3 := abs_le.1 (hD'D _ (hK _ (hgi i hi)) _ (hK _ (hgi1 i hi)))
    linarith
  · intro i hi
    set x := P (dfl71Grid L N i)
    have hxK := hK _ (hgi i hi)
    refine ⟨ξ * F x - ω / 2, by linarith [(dfl71_abs_le (ξ := ξ) hF x).2], ?_, ?_⟩
    · intro t ht
      have htI : t ∈ Icc 0 L := ⟨(hgi i hi).1.trans ht.1, ht.2.le.trans (hgi1 i hi).2⟩
      have h1 := hDP _ (hgi i hi) _ htI
      have hlt : |dfl71Grid L N i - t| ≤ L / N := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2, hstep i]
      have h2 := abs_le.1 (hDD _ hxK _ (hK _ htI))
      have hF1 := hmod _ hxK _ (hK _ htI) (by linarith)
      have hg1 := hg _ (hK _ htI)
      have : |g (P t) - F x| ≤ 2 * θ := by
        calc |g (P t) - F x| = |(g (P t) - F (P t)) + -(F x - F (P t))| := by ring_nf
          _ ≤ |g (P t) - F (P t)| + |-(F x - F (P t))| := abs_add_le _ _
          _ ≤ 2 * θ := by rw [abs_neg]; linarith
      have h3 : |ξ * (g (P t) - F x)| ≤ |ξ| * (2 * θ) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left this hξ
      have := abs_le.1 h3
      nlinarith
    · intro q hq
      have hqball : q ∈ ball (0 : ℂ) (r' + 1) := by
        by_contra hqn
        have hxb : x ∈ ball (0 : ℂ) (r' + 1) :=
          ball_subset_ball (by linarith) (hin _ (hgi i hi))
        have hd : ∀ y ∈ sphere (0 : ℂ) (r' + 1), d₁ - ε ≤ D'.1 (x, y) := by
          intro y hy
          have := abs_le.1 (hD'D _ hxK _ (sphere_subset_closedBall hy))
          linarith [hgap1 _ (hK' _ (hgi i hi)) _ hy]
        have h1 := (dfl71_le_infEDist_compl_ball hD' hxb hd).trans
          (infEDist_le_edist_of_mem (⟨q, hqn, rfl⟩ : D'.pt q ∈ D'.pt '' (ball (0 : ℂ) (r' + 1))ᶜ))
        rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h1
        change d₁ - ε ≤ D'.1 (x, q) at h1
        linarith
      have hqK := ball_subset_closedBall hqball
      have h2 := abs_le.1 (hD'D _ hxK _ hqK)
      have hF1 := hmod _ hxK _ hqK (by linarith)
      have hg1 := hg' _ hqK
      have : |g' q - F x| ≤ 2 * θ := by
        calc |g' q - F x| = |(g' q - F q) + -(F x - F q)| := by ring_nf
          _ ≤ |g' q - F q| + |-(F x - F q)| := abs_add_le _ _
          _ ≤ 2 * θ := by rw [abs_neg]; linarith
      have h3 : |ξ * (g' q - F x)| ≤ |ξ| * (2 * θ) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left this hξ
      have := abs_le.1 h3
      nlinarith

end LQGMetric.DFGPS
