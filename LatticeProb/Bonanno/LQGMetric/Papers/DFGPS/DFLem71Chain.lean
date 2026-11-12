/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.DFLem71Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylCont

/-!
# DF Lemma 7.1, deterministic tools: exits, the local comparison, the chain bound

Dubédat–Falconet, *Liouville metric of star-scale invariant fields: tails and Weyl scaling*,
arXiv:1809.02607, Lemma 7.1 (`StabMetric`, `LiouvilleMetricStarScale.tex` DF:1280–1344), in the
form DFGPS use it (arXiv:1905.00380, Lemma 2.12, T:1026–1051; DEV-DFGPS-6). DF's proof has two
ingredients, both proved here for GM's Weyl scaling `weylScale` (GM (1.6)):

* the local comparison (DF:1301–1307) "`e^f·d(x, y) ≤ e^{osc(f, K)} e^{f(x)} d(x, y)`, where `K`
  contains a near-geodesic from `x` to `y`" (`dfl71_weylScale_le_local`; a path of length
  `≤ d(x, y) + η` stays in the `d`-ball of radius `d(x, y) + η` around `x`);
* the chain bound (DF:1310–1322 upper bound, DF:1330–1342 lower bound): along a chain
  `x₀, …, x_N` cut from a path, `e^{f'}·d'(x₀, x_N) ≤ Σ e^{f'}·d'(xᵢ, xᵢ₊₁)` (triangle
  inequality) `≤ Σ e^{osc} e^{f(xᵢ)} d'(xᵢ, xᵢ₊₁)`, and the Riemann sum is compared with the
  Weyl cost of the path (`dfl71_chain`). DF's chains are midpoint subdivisions of a geodesic;
  here they are the points `P (i L / N)` of a near-optimal length-parametrized path (GM (1.6)
  defines `e^{ξ f}·D` through such paths; strict intrinsicness, DF:1297, is not needed).

The exit lemma `dfl71_le_infEDist_compl_ball` is the "near-minimal paths stay in `S_{r'}`" step
of DFGPS (T:1044–1048) for Euclidean balls: a path from `u ∈ B_R(0)` to a point outside `B_R(0)`
crosses `∂B_R(0)` (intermediate value theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS

open MetricGeometry

/-- In a length metric, the distance from `u ∈ B_R(0)` to `(B_R(0))ᶜ` is at least any lower bound
for the distances from `u` to `∂B_R(0)`. -/
theorem dfl71_le_infEDist_compl_ball {D : ContMetric} (hD : D.IsLength) {u : ℂ} {R d : ℝ}
    (hu : u ∈ ball (0 : ℂ) R) (hd : ∀ y ∈ sphere (0 : ℂ) R, d ≤ D.1 (u, y)) :
    ENNReal.ofReal d ≤ infEDist (D.pt u) (D.pt '' (ball (0 : ℂ) R)ᶜ) := by
  refine le_infEDist.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  obtain ⟨γ, hγ⟩ := hD (D.pt u) (D.pt y) η hη
  have hg : Continuous fun t => ‖weylToC D (γ t)‖ :=
    ((continuous_weylToC D).comp γ.continuous).norm
  have hR : R ∈ Icc ‖weylToC D (γ 0)‖ ‖weylToC D (γ 1)‖ := by
    rw [γ.source, γ.target]
    refine ⟨(mem_ball_zero_iff.1 hu).le, ?_⟩
    show R ≤ ‖y‖
    simpa [mem_ball_zero_iff] using hy
  obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hg hR
  have hs : weylToC D (γ t) ∈ sphere (0 : ℂ) R := mem_sphere_zero_iff_norm.2 ht
  calc ENNReal.ofReal d ≤ ENNReal.ofReal (D.1 (u, weylToC D (γ t))) :=
        ENNReal.ofReal_le_ofReal (hd _ hs)
    _ = edist (D.pt u) (γ t) := by rw [edist_dist]; rfl
    _ ≤ pathLength γ := edist_le_pathLength_apply' γ t
    _ ≤ edist (D.pt u) (D.pt y) + ENNReal.ofReal η := hγ
    _ = edist (D.pt u) (D.pt y) + η := by rw [ENNReal.ofReal_coe_nnreal]

/-- **Local comparison** (DF:1301–1307, upper half): if `ξ g ≤ b` on the `D`-ball of radius
`D(x, y) + η` around `x`, then `(e^{ξ g}·D)(x, y) ≤ e^b (D(x, y) + η)`. -/
theorem dfl71_weylScale_le_local {D : ContMetric} (hD : D.IsLength) {ξ : ℝ} {g : C(ℂ, ℝ)}
    {x y : ℂ} {η b : ℝ} (hη : 0 < η)
    (hb : ∀ q, D.1 (x, q) ≤ D.1 (x, y) + η → ξ * g q ≤ b) :
    weylScale ξ g D x y ≤ ENNReal.ofReal (Real.exp b * (D.1 (x, y) + η)) := by
  obtain ⟨γ, hγ⟩ := hD (D.pt x) (D.pt y) η hη
  have hnn : 0 ≤ D.1 (x, y) := dist_nonneg (x := D.pt x) (y := D.pt y)
  have hlen : pathLength γ ≤ ENNReal.ofReal (D.1 (x, y) + η) := by
    refine hγ.trans (le_of_eq ?_)
    rw [edist_dist, ENNReal.ofReal_add hnn hη.le]; rfl
  have hrange : ∀ t, ξ * g (weylToC D (γ t)) ≤ b := by
    intro t
    refine hb _ ?_
    have h1 := (edist_le_pathLength_apply' γ t).trans hlen
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
    exact h1
  refine (weylScale_le_of_path γ hrange).trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr

/-- the grid `i L / N` -/
def dfl71Grid (L : ℝ) (N : ℕ) (i : ℕ) : ℝ := i * L / N

theorem dfl71_sum_lintegral_Ico (G : ℝ → ℝ≥0∞) (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) :
    ∑ i ∈ Finset.range N, ∫⁻ s in Ico (t i) (t (i + 1)), G s = ∫⁻ s in Ico (t 0) (t N), G s := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ico Ico_disjoint_Ico_same,
      Ico_union_Ico_eq_Ico (ht (Nat.zero_le n)) (ht (Nat.le_succ n))]

/-- **Chain bound** (DF:1310–1322 and 1330–1342). Let `P` be any path on `[0, L]`, cut at the
grid points `xᵢ = P (i L / N)`. If `D'(xᵢ, xᵢ₊₁) ≤ L/N + ε` and on the `i`-th piece
`ξ g ≥ a` while `ξ g' ≤ a + ω` on the `D'`-ball of radius `L/N + ε + η` around `xᵢ`, then
`(e^{ξ g'}·D')(P 0, P L) ≤ e^ω ∫_0^L e^{ξ g(P t)} dt + N e^B (ε + η)`. -/
theorem dfl71_chain {D' : ContMetric} (hD' : D'.IsLength) {ξ : ℝ} {g g' : C(ℂ, ℝ)}
    {P : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N) {ε η ω B : ℝ} (hε : 0 ≤ ε)
    (hη : 0 < η)
    (H1 : ∀ i < N, D'.1 (P (dfl71Grid L N i), P (dfl71Grid L N (i + 1))) ≤ L / N + ε)
    (H2 : ∀ i < N, ∃ a : ℝ, a + ω ≤ B ∧
      (∀ t ∈ Ico (dfl71Grid L N i) (dfl71Grid L N (i + 1)), a ≤ ξ * g (P t)) ∧
      ∀ q, D'.1 (P (dfl71Grid L N i), q) ≤ L / N + ε + η → ξ * g' q ≤ a + ω) :
    weylScale ξ g' D' (P 0) (P L) ≤
      ENNReal.ofReal (Real.exp ω) * (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t)))) +
        N * ENNReal.ofReal (Real.exp B * (ε + η)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (ξ * g (P t)))
  have hgrid0 : dfl71Grid L N 0 = 0 := by simp [dfl71Grid]
  have hgridN : dfl71Grid L N N = L := by
    simp only [dfl71Grid]; field_simp
  have hstep : ∀ i : ℕ, dfl71Grid L N (i + 1) - dfl71Grid L N i = L / N := by
    intro i; simp only [dfl71Grid]; push_cast; ring
  have hmono : Monotone (dfl71Grid L N) := by
    intro i j hij
    simp only [dfl71Grid]
    gcongr
  -- one piece
  have hpiece : ∀ i < N, weylScale ξ g' D' (P (dfl71Grid L N i)) (P (dfl71Grid L N (i + 1))) ≤
      ENNReal.ofReal (Real.exp ω) *
        (∫⁻ t in Ico (dfl71Grid L N i) (dfl71Grid L N (i + 1)), G t) +
          ENNReal.ofReal (Real.exp B * (ε + η)) := by
    intro i hi
    obtain ⟨a, haB, hag, hag'⟩ := H2 i hi
    have hd := H1 i hi
    have hloc := dfl71_weylScale_le_local hD' (g := g') (ξ := ξ) (b := a + ω) hη
      (fun q hq => hag' q (by linarith))
    refine hloc.trans ?_
    have hLN : 0 ≤ L / N := div_nonneg hL hNr.le
    have hreal : Real.exp (a + ω) *
        (D'.1 (P (dfl71Grid L N i), P (dfl71Grid L N (i + 1))) + η) ≤
        Real.exp ω * (Real.exp a * (L / N)) + Real.exp B * (ε + η) := by
      have h1 : Real.exp (a + ω) ≤ Real.exp B := Real.exp_le_exp.2 haB
      have h2 : Real.exp (a + ω) *
          (D'.1 (P (dfl71Grid L N i), P (dfl71Grid L N (i + 1))) + η) ≤
          Real.exp (a + ω) * (L / N) + Real.exp (a + ω) * (ε + η) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      have h3 : Real.exp (a + ω) * (ε + η) ≤ Real.exp B * (ε + η) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      rw [Real.exp_add] at h2 h3 ⊢
      nlinarith
    refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) le_rfl
    calc ENNReal.ofReal (Real.exp a * (L / N))
        = ∫⁻ _ in Ico (dfl71Grid L N i) (dfl71Grid L N (i + 1)),
            ENNReal.ofReal (Real.exp a) := by
          rw [setLIntegral_const, Real.volume_Ico, hstep, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ∫⁻ t in Ico (dfl71Grid L N i) (dfl71Grid L N (i + 1)), G t :=
          setLIntegral_mono' measurableSet_Ico fun t ht =>
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hag t ht))
  -- the chain
  have hsum := weylScaleOn_le_sum (ξ := ξ) (f := g') (D := D') (U := univ)
    (fun i => P (dfl71Grid L N i)) (mem_univ _) N
  simp only [weylScaleOn_univ, hgrid0, hgridN] at hsum
  refine hsum.trans ?_
  calc ∑ i ∈ Finset.range N, weylScale ξ g' D' (P (dfl71Grid L N i)) (P (dfl71Grid L N (i + 1)))
      ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (Real.exp ω) *
          (∫⁻ t in Ico (dfl71Grid L N i) (dfl71Grid L N (i + 1)), G t) +
          ENNReal.ofReal (Real.exp B * (ε + η))) :=
        Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.1 hi)
    _ = ENNReal.ofReal (Real.exp ω) * (∫⁻ t in Ico 0 L, G t) +
          N * ENNReal.ofReal (Real.exp B * (ε + η)) := by
        rw [Finset.sum_add_distrib (f := fun i => ENNReal.ofReal (Real.exp ω) *
            ∫⁻ t in Ico (dfl71Grid L N i) (dfl71Grid L N (i + 1)), G t), ← Finset.mul_sum,
          dfl71_sum_lintegral_Ico G _ hmono N, hgrid0, hgridN]
        simp
    _ ≤ ENNReal.ofReal (Real.exp ω) * (∫⁻ t in Icc 0 L, G t) +
          N * ENNReal.ofReal (Real.exp B * (ε + η)) := by
        gcongr
        exact Ico_subset_Icc_self

end LQGMetric.DFGPS
