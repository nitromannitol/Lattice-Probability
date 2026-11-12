/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuHat
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32X

/-!
# DG Lemma 3.12 (`lem-local-dist`) from DZZ Proposition 3.17 + Lemma 5.3 (P2-DG105h, D105 P9)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.12 (DG:1204–1216):
"For each `ζ ∈ (0,1)`, it holds with probability tending to 1 as `ε → 0` that
`D^ε_{ĥ^tr}(u^i_𝕊, u^j_𝕊; 𝕊(1)) ≤ ε^{−1/(d_γ−ζ)}` for all `i, j`." DG's proof (DG:1213–1215):
the analogue for a zero-boundary GFF is DZZ Proposition 3.17 + Lemma 5.3, "noting that
`D̃_{γ,δ,η}(u,v)` … denotes `δ²`-Liouville graph distance restricted to paths of disks which lie
in the box of side length `2|u−v|` centred at `(u+v)/2`, with sides parallel to `[u,v]`"; then
DG Lemma 3.2 (`lem-tr-compare-square`) passes to `ĥ^tr`.

Formalization (D105 §1 items 1, 7; §4 P9):
* the square `𝕊` has lower-left corner `c` and side `s`, `𝕊(1)` is `l312Sq1 c s` (side `3s`, same
  centre), the side midpoints `l312Mids c s`; the midpoints lie in DZZ's central box
  `𝕍̄ = 𝕍_{(1/2,1/2),1/20}` (`l312Vbar`, a verbatim copy of `DZZ.dzzVbar`) and `𝕊(1)` in the box
  `ferniqueBox y b` carrying `μ_{ĥ^tr} = muTr` (D105 item 1: DZZ's Lemma 5.3 is stated for
  `u, v ∈ 𝕍̄`, so the unit square of DG is realized at a scale inside `𝕍̄`).
* the DZZ input is the hypothesis `DZZL53Whp P ν χ` ("probability → 1" form, D105 N9): it is
  verbatim the conclusion of `DZZ.dzz_lem53_upper_whp` (Papers/DZZ/S5Defs, DZZ P3.17 + L5.3), with
  `l312Tilde u v` a verbatim copy of `DZZ.tildeBox u v` (DZZ's `𝕍̃_{u,v}`) and `ν` DZZ's measure;
  `hν` compares `μ_{h^𝕍} = muHU` with `ν` (for `ν = wickQArea γ W` it is `DZZ.le_wickQArea`).
* **Doubt of D105 item 7 resolved:** the upper bound needs no unwalled measure and no interior
  identification: `D̃` is DZZ's own distance with balls inside `𝕍̃_{u,v}` (`dzzWall`, D97),
  `𝕍̃_{u,v} ⊆ 𝕊(1)` for any two distinct midpoints (`l312Tilde_subset_of_mids`, DG:1214), and a
  `D̃`-path of rational balls is a `D(·,·;𝕊(1))`-path (`dgLGD_le_lgdDZZ_wall`).
* DG Lemma 3.2 at the pair `(h^𝕍, ĥ^tr)` via `dg_lemma32_of_tail` (S3L2) and DG Lemma 3.1's tail for
  `trMod` (`trMod_spec`); the constant `C` of L3.2 is sent to `∞` after `ε → 0`.
* `d_γ = 2/χ` (DG:214); the pair `u = v` follows from a pair `u ≠ v` (`dgLGD_self_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail

/-! ### Geometry -/

/-- `𝕊(1)` for the square `𝕊` with lower-left corner `c` and side `s` (side `3s`, same centre) -/
def l312Sq1 (c : ℂ) (s : ℝ) : Set ℂ :=
  Icc (c.re - s) (c.re + 2 * s) ×ℂ Icc (c.im - s) (c.im + 2 * s)

/-- the midpoints of the four sides of the square with lower-left corner `c` and side `s` -/
def l312Mids (c : ℂ) (s : ℝ) : Set ℂ :=
  {⟨c.re, c.im + s / 2⟩, ⟨c.re + s, c.im + s / 2⟩, ⟨c.re + s / 2, c.im⟩, ⟨c.re + s / 2, c.im + s⟩}

/-- the closed box centred at `c` with side `l` (verbatim copy of `DZZ.sqBox`) -/
def l312Box (c : ℂ) (l : ℝ) : Set ℂ := {z | |z.re - c.re| ≤ l / 2 ∧ |z.im - c.im| ≤ l / 2}

/-- DZZ's `𝕍̄` (verbatim copy of `DZZ.dzzVbar`) -/
def l312Vbar : Set ℂ := l312Box ⟨1 / 2, 1 / 2⟩ (1 / 20)

/-- DZZ's `𝕍̃_{u,v}` (verbatim copy of `DZZ.tildeBox`) -/
def l312Tilde (u v : ℂ) : Set ℂ :=
  {z | |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).re| ≤ ‖v - u‖ ^ 2 ∧
    |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).im| ≤ ‖v - u‖ ^ 2}

lemma isClosed_l312Sq1 (c : ℂ) (s : ℝ) : IsClosed (l312Sq1 c s) :=
  isClosed_Icc.reProdIm isClosed_Icc

lemma isClosed_l312Tilde (u v : ℂ) : IsClosed (l312Tilde u v) := by
  show IsClosed ({z : ℂ | |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).re| ≤ ‖v - u‖ ^ 2} ∩
    {z : ℂ | |((z - (u + v) / 2) * starRingEnd ℂ (v - u)).im| ≤ ‖v - u‖ ^ 2})
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

lemma abs_add_abs_le_of {a b s : ℝ} (h1 : a + b ≤ s) (h2 : a - b ≤ s) (h3 : -a + b ≤ s)
    (h4 : -a - b ≤ s) : |a| + |b| ≤ s := by
  rcases abs_cases a with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rcases abs_cases b with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
    rw [ha, hb] <;> linarith

/-- the coordinates of `z − (u+v)/2` are bounded by `|w.re| + |w.im|` on `𝕍̃_{u,v}`, `w = v − u` -/
lemma l312Tilde_coord {u v z : ℂ} (huv : u ≠ v) (hz : z ∈ l312Tilde u v) :
    |(z - (u + v) / 2).re| ≤ |(v - u).re| + |(v - u).im| ∧
      |(z - (u + v) / 2).im| ≤ |(v - u).re| + |(v - u).im| := by
  obtain ⟨h1, h2⟩ := hz
  set w := v - u with hw
  set q := z - (u + v) / 2 with hq
  have hw0 : w ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
  have hN : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hNpos : 0 < ‖w‖ ^ 2 := by positivity
  have pre : (q * starRingEnd ℂ w).re = q.re * w.re + q.im * w.im := by
    simp [Complex.mul_re]
  have pim : (q * starRingEnd ℂ w).im = q.im * w.re - q.re * w.im := by
    simp [Complex.mul_im]; ring
  rw [pre] at h1
  rw [pim] at h2
  set N := ‖w‖ ^ 2
  have k1 : q.re * N = (q.re * w.re + q.im * w.im) * w.re - (q.im * w.re - q.re * w.im) * w.im := by
    rw [hN]; ring
  have k2 : q.im * N = (q.re * w.re + q.im * w.im) * w.im + (q.im * w.re - q.re * w.im) * w.re := by
    rw [hN]; ring
  have b1 : |q.re| * N ≤ (|w.re| + |w.im|) * N := by
    rw [← abs_of_pos hNpos, ← abs_mul, k1, abs_of_pos hNpos]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg w.re, abs_nonneg w.im]
  have b2 : |q.im| * N ≤ (|w.re| + |w.im|) * N := by
    rw [← abs_of_pos hNpos, ← abs_mul, k2, abs_of_pos hNpos]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg w.re, abs_nonneg w.im]
  exact ⟨le_of_mul_le_mul_right b1 hNpos, le_of_mul_le_mul_right b2 hNpos⟩

/-- `𝕍̃_{u,v} ⊆ 𝕊(1)` when `(u+v)/2 ∈ [c + s/4, c + 3s/4]²` and `|w.re| + |w.im| ≤ s` -/
lemma l312Tilde_subset {c u v : ℂ} {s : ℝ} (huv : u ≠ v)
    (m1 : c.re + s / 4 ≤ (u.re + v.re) / 2) (m2 : (u.re + v.re) / 2 ≤ c.re + 3 * s / 4)
    (m3 : c.im + s / 4 ≤ (u.im + v.im) / 2) (m4 : (u.im + v.im) / 2 ≤ c.im + 3 * s / 4)
    (w1 : (v.re - u.re) + (v.im - u.im) ≤ s) (w2 : (v.re - u.re) - (v.im - u.im) ≤ s)
    (w3 : -(v.re - u.re) + (v.im - u.im) ≤ s) (w4 : -(v.re - u.re) - (v.im - u.im) ≤ s) :
    l312Tilde u v ⊆ l312Sq1 c s := by
  intro z hz
  obtain ⟨h1, h2⟩ := l312Tilde_coord huv hz
  have hw := abs_add_abs_le_of w1 w2 w3 w4
  have e1 : (z - (u + v) / 2).re = z.re - (u.re + v.re) / 2 := by simp
  have e2 : (z - (u + v) / 2).im = z.im - (u.im + v.im) / 2 := by simp
  rw [e1, Complex.sub_re, Complex.sub_im] at h1
  rw [e2, Complex.sub_re, Complex.sub_im] at h2
  obtain ⟨a1, a2⟩ := abs_le.1 (h1.trans hw)
  obtain ⟨a3, a4⟩ := abs_le.1 (h2.trans hw)
  simp only [l312Sq1, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **DG:1214**: for two distinct side midpoints `u, v` of `𝕊`, `𝕍̃_{u,v} ⊆ 𝕊(1)` -/
lemma l312Tilde_subset_of_mids {c : ℂ} {s : ℝ} (hs : 0 < s) {u v : ℂ} (hu : u ∈ l312Mids c s)
    (hv : v ∈ l312Mids c s) (huv : u ≠ v) : l312Tilde u v ⊆ l312Sq1 c s := by
  simp only [l312Mids, mem_insert_iff, mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl huv
    | (refine l312Tilde_subset huv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only <;> linarith)

/-- every midpoint has a different midpoint -/
lemma exists_ne_l312Mids {c : ℂ} {s : ℝ} (hs : 0 < s) (u : ℂ) :
    ∃ v ∈ l312Mids c s, u ≠ v := by
  by_cases h : u = ⟨c.re, c.im + s / 2⟩
  · refine ⟨⟨c.re + s, c.im + s / 2⟩, by simp [l312Mids], fun h' => ?_⟩
    have := congrArg Complex.re (h.symm.trans h')
    simp only at this; linarith
  · exact ⟨⟨c.re, c.im + s / 2⟩, by simp [l312Mids], h⟩

/-- the midpoints as a family indexed by `Fin 4` -/
def l312Mid (c : ℂ) (s : ℝ) : Fin 4 → ℂ :=
  ![⟨c.re, c.im + s / 2⟩, ⟨c.re + s, c.im + s / 2⟩, ⟨c.re + s / 2, c.im⟩, ⟨c.re + s / 2, c.im + s⟩]

lemma l312Mid_mem (c : ℂ) (s : ℝ) (i : Fin 4) : l312Mid c s i ∈ l312Mids c s := by
  fin_cases i <;> simp [l312Mid, l312Mids]

lemma exists_l312Mid {c : ℂ} {s : ℝ} {u : ℂ} (hu : u ∈ l312Mids c s) :
    ∃ i, l312Mid c s i = u := by
  simp only [l312Mids, mem_insert_iff, mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-! ### Deterministic comparisons of Liouville graph distances -/

/-- a larger domain gives a smaller restricted LGD -/
lemma dgLGD_mono_dom {μ : Measure ℂ} {ε : ℝ} {U U' : Set ℂ} (h : closure U ⊆ closure U')
    (z w : ℂ) : dgLGD μ ε U' z w ≤ dgLGD μ ε U z w := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, h1, h2⟩ := hN
  exact iInf₂_le N ⟨x, ρ, P, fun i => ⟨(h1 i).1, (h1 i).2.1.trans h, (h1 i).2.2⟩, h2⟩

/-- `D(u,u) ≤ D(u,v)`: the path `u → v → u` is covered by the same balls -/
lemma dgLGD_self_le {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ} (u v : ℂ) :
    dgLGD μ ε U u u ≤ dgLGD μ ε U u v := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, h1, h2⟩ := hN
  refine iInf₂_le N ⟨x, ρ, P.trans P.symm, h1, fun t => ?_⟩
  have hm : (P.trans P.symm) t ∈ range P := by
    rw [← Path.symm_range P, ← union_self (range P.symm)]
    nth_rewrite 1 [Path.symm_range P]
    rw [← Path.trans_range]
    exact mem_range_self t
  obtain ⟨t', ht'⟩ := hm
  obtain ⟨i, hi⟩ := h2 t'
  exact ⟨i, ht' ▸ hi⟩

/-- **a `D^T_δ(ν)`-path is a `D^ε(·,·;T)`-path of `μ`** (`T` closed): the balls of a
`lgdDZZ (dzzWall T ν)` witness lie in `T` (D97, `dzzWall_ball_of_not_subset`) and have `ν`-mass
`≤ δ²`, hence `μ`-mass `≤ ε` if `μ ≤ e^a ν` on balls and `e^a δ² ≤ ε`. -/
lemma dgLGD_le_lgdDZZ_wall {μ ν : Measure ℂ} {T : Set ℂ} (hT : IsClosed T) {a δ ε : ℝ}
    (hμν : ∀ x r, μ (Metric.ball x r) ≤ ENNReal.ofReal (Real.exp a) * ν (Metric.ball x r))
    (hε : Real.exp a * δ ^ 2 ≤ ε) (z w : ℂ) :
    dgLGD μ ε T z w ≤ lgdDZZ (DZZ.dzzWall T ν) δ z w := by
  unfold dgLGD lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  have hsub : ∀ i, Metric.ball (ratPt (c i)) (ρ i) ⊆ T := by
    intro i
    by_contra hns
    have := (h1 i).2
    rw [DZZ.dzzWall_ball_of_not_subset hT ν hns] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.1 this)
  refine iInf₂_le N ⟨fun i => ratPt (c i), ρ, P, fun i => ⟨(h1 i).1,
    (hsub i).trans subset_closure, ?_⟩, h2⟩
  have hν : ν (Metric.ball (ratPt (c i)) (ρ i)) ≤ ENNReal.ofReal (δ ^ 2) := by
    have := (h1 i).2
    rwa [DZZ.dzzWall_ball_of_subset ν (hsub i)] at this
  calc μ (Metric.ball (ratPt (c i)) (ρ i))
      ≤ ENNReal.ofReal (Real.exp a) * ν (Metric.ball (ratPt (c i)) (ρ i)) := hμν _ _
    _ ≤ ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (δ ^ 2) := by gcongr
    _ = ENNReal.ofReal (Real.exp a * δ ^ 2) := (ENNReal.ofReal_mul (Real.exp_pos a).le).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hε

/-! ### DG Lemma 3.12 -/

/-- **The DZZ input of DG Lemma 3.12** (DG:1206; D105 N9, "probability → 1" form): for `u ≠ v`
in `𝕍̄` and `ι > 0`, `P[D̃_δ(u,v) > δ^{−χ−ι}] → 0` as `δ → 0`, `D̃_δ` the `δ²`-LGD of `ν` with
balls inside `𝕍̃_{u,v}`. Verbatim the conclusion of `DZZ.dzz_lem53_upper_whp` (DZZ Proposition 3.17
+ Lemma 5.3, Papers/DZZ/S5Defs) at `μ = ν` (`l312Vbar = DZZ.dzzVbar`, `l312Tilde = DZZ.tildeBox`
by definition). -/
def DZZL53Whp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ν : Ω → Measure ℂ) (χ : ℝ) :
    Prop :=
  ∀ u ∈ l312Vbar, ∀ v ∈ l312Vbar, u ≠ v → ∀ ι : ℝ, 0 < ι →
    Tendsto (fun δ => P {ω | ¬ ((lgdDZZ (DZZ.dzzWall (l312Tilde u v) (ν ω)) δ u v : ℕ∞) :
      ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-(χ + ι)))}) (𝓝[>] 0) (𝓝 0)

lemma l312_exp_ev {K θ κ : ℝ} (hK : 0 < K) (hθ : κ < θ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sqrt (ε / K) ^ (-(2 * κ)) ≤ ε ^ (-θ) := by
  have ht := tendsto_rpow_neg_nhdsGT_zero (y := -(θ - κ)) (by linarith)
  filter_upwards [ht.eventually_ge_atTop (K ^ κ), self_mem_nhdsWithin] with ε h1 hε
  have hε0 : 0 < ε := hε
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_nonneg hε0.le hK.le), Real.div_rpow hε0.le hK.le]
  have e1 : (1 / 2 : ℝ) * -(2 * κ) = -κ := by ring
  rw [e1, Real.rpow_neg hK.le, div_inv_eq_mul]
  have e : ε ^ (-θ) = ε ^ (-κ) * ε ^ (-(θ - κ)) := by
    rw [← Real.rpow_add hε0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DG Lemma 3.12** (`lem-local-dist`, DG:1204–1216) at the square `𝕊` with corner `c`, side
`s`, midpoints in `𝕍̄` and `𝕊(1) ⊆ ferniqueBox y b`: for `0 < ζ < d_γ = 2/χ`, with probability
tending to `1` as `ε → 0`, `D^ε_{ĥ^tr}(u^i, u^j; 𝕊(1)) ≤ ε^{−1/(d_γ−ζ)}` for all side midpoints
`u^i, u^j`. Inputs: DZZ P3.17 + L5.3 (`hDZZ`, for DZZ's measure `ν` with `μ_{h^𝕍} ≤ e^a ν` on
balls) and DG Lemmas 3.1/3.2 at `(h^𝕍, ĥ^tr)`. -/
theorem dg_lemma312 (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {ν : Ω → Measure ℂ} {a : ℝ}
    (hν : ∀ ω x r, muHU W γ ω (Metric.ball x r) ≤
      ENNReal.ofReal (Real.exp a) * ν ω (Metric.ball x r))
    {χ : ℝ} (hχ : 0 < χ) (hDZZ : DZZL53Whp P ν χ)
    {c : ℂ} {s : ℝ} (hs : 0 < s) (hmid : l312Mids c s ⊆ l312Vbar)
    (hS : l312Sq1 c s ⊆ ferniqueBox y b) {ζ : ℝ} (hζ : 0 < ζ) (hζd : ζ < 2 / χ) :
    Tendsto (fun ε => P {ω | ¬ ∀ u ∈ l312Mids c s, ∀ v ∈ l312Mids c s,
      ((dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) u v : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-(1 / (2 / χ - ζ))))}) (𝓝[>] 0) (𝓝 0) := by
  have hP := hW.isProbabilityMeasure
  set θ := 1 / (2 / χ - ζ) with hθ
  have hθκ : χ / 2 < θ := by
    have h1 : 0 < 2 / χ - ζ := by linarith
    have h2 : 2 / χ - ζ < 2 / χ := by linarith
    have := one_div_lt_one_div_of_lt h1 h2
    rw [one_div_div, one_div] at this
    rw [hθ, one_div]; exact this
  set ι := θ - χ / 2 with hι
  have hι0 : 0 < ι := by linarith
  have hκ0 : 0 < (χ + ι) / 2 := by positivity
  have hκθ : (χ + ι) / 2 < θ := by rw [hι]; linarith
  -- DG Lemma 3.1 (tail of `trMod`) and DG Lemma 3.2 at `(h^𝕍, ĥ^tr)` on `𝕊(1)`
  obtain ⟨-, -, ⟨b₀, b₁, hb₁, htail⟩, -⟩ := trMod_spec hW hb hK
  obtain ⟨a₀, a₁, ha₁, h32⟩ := dg_lemma32_of_tail (K := l312Sq1 c s) P hγ
    (fun ω => (muHU W γ ω).restrict (ferniqueBox y b)) (fun ω z => -trMod hW hb hK z ω) hb₁
    (fun A hA => by
      refine (measure_mono fun ω hω => ?_).trans (htail A (by linarith))
      intro hall
      apply hω
      intro z hz
      rw [abs_neg]
      exact hall z (hS ((isClosed_l312Sq1 c s).closure_eq ▸ hz)))
  have h32' : ∀ C : ℝ, 1 < C → ∀ ε : ℝ,
      P {ω | ¬ ∀ z w : ℂ, dgLGD (muTr hW γ hb hK ω) (C * ε) (l312Sq1 c s) z w ≤
        dgLGD (muHU W γ ω) ε (l312Sq1 c s) z w} ≤
        ENNReal.ofReal (a₀ * Real.exp (-a₁ * Real.log C ^ 2)) := by
    intro C hC ε
    refine le_trans (measure_mono ?_) (h32 C hC ε)
    intro ω hω h
    apply hω
    intro z w
    exact ((h z w).1).trans (dgLGD_le_of_ball (fun x ρ _ hB =>
      (Measure.restrict_apply_le _ _).trans hB) z w)
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηt
  · exact Eventually.of_forall fun _ => le_top
  set r := η.toReal / 2 with hr
  have hr0 : 0 < r := by have := ENNReal.toReal_pos hη.ne' hηt; positivity
  have hrr : ENNReal.ofReal r + ENNReal.ofReal r = η := by
    rw [← ENNReal.ofReal_add hr0.le hr0.le, hr, add_halves, ENNReal.ofReal_toReal hηt]
  -- choose the constant `C = e^T` of Lemma 3.2 with `a₀ e^{−a₁ T²} < r`
  have hT : Tendsto (fun T : ℝ => a₀ * Real.exp (-a₁ * T ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => -a₁ * T ^ 2) atTop atBot := by
      have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).const_mul_atTop ha₁
      exact (tendsto_neg_atTop_atBot.comp this).congr fun T => by simp
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul a₀
  obtain ⟨T, hT1, hT0⟩ := ((hT.eventually (gt_mem_nhds hr0)).and (eventually_gt_atTop 0)).exists
  have hC1 : 1 < Real.exp T := Real.one_lt_exp_iff.2 hT0
  have hCpos : 0 < Real.exp T := Real.exp_pos T
  set K := Real.exp T * Real.exp a with hKdef
  have hK0 : 0 < K := by positivity
  have hδt : Tendsto (fun ε => Real.sqrt (ε / K)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (Real.continuous_sqrt.comp (continuous_id.div_const K)).tendsto 0
      simpa [Function.comp_def] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact Real.sqrt_pos.2 (div_pos hε hK0)
  -- the pairs of distinct midpoints and their DZZ events
  set S := (Finset.univ : Finset (Fin 4 × Fin 4)).filter
    (fun ij => l312Mid c s ij.1 ≠ l312Mid c s ij.2) with hSdef
  set E : Fin 4 × Fin 4 → ℝ → Set Ω := fun ij δ => {ω | ¬ ((lgdDZZ (DZZ.dzzWall
    (l312Tilde (l312Mid c s ij.1) (l312Mid c s ij.2)) (ν ω)) δ (l312Mid c s ij.1)
      (l312Mid c s ij.2) : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-(χ + ι)))} with hEdef
  have hsum : Tendsto (fun ε => ∑ ij ∈ S, P (E ij (Real.sqrt (ε / K)))) (𝓝[>] 0) (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ ij ∈ S, (0 : ℝ≥0∞) by simp]
    refine tendsto_finsetSum S fun ij hij => ?_
    have hne := (Finset.mem_filter.1 hij).2
    exact (hDZZ _ (hmid (l312Mid_mem c s ij.1)) _ (hmid (l312Mid_mem c s ij.2)) hne ι hι0).comp
      hδt
  filter_upwards [hsum.eventually (Iic_mem_nhds (ENNReal.ofReal_pos.2 hr0)),
    l312_exp_ev hK0 hκθ, self_mem_nhdsWithin] with ε hε1 hε2 hε
  have hε0 : 0 < ε := hε
  have h2κ : 2 * ((χ + ι) / 2) = χ + ι := by ring
  rw [h2κ] at hε2
  have hmass : Real.exp a * Real.sqrt (ε / K) ^ 2 ≤ ε / Real.exp T := by
    rw [Real.sq_sqrt (div_nonneg hε0.le hK0.le), hKdef]
    apply le_of_eq
    field_simp
  have hincl : {ω | ¬ ∀ u ∈ l312Mids c s, ∀ v ∈ l312Mids c s,
      ((dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) u v : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-θ))} ⊆
      {ω | ¬ ∀ z w : ℂ, dgLGD (muTr hW γ hb hK ω) (Real.exp T * (ε / Real.exp T))
        (l312Sq1 c s) z w ≤ dgLGD (muHU W γ ω) (ε / Real.exp T) (l312Sq1 c s) z w} ∪
      ⋃ ij ∈ S, E ij (Real.sqrt (ε / K)) := by
    intro ω hω
    by_contra hcon
    rw [mem_union, not_or] at hcon
    obtain ⟨hG, hE⟩ := hcon
    have hG' := not_not.1 hG
    have hE' : ∀ ij ∈ S, ω ∉ E ij (Real.sqrt (ε / K)) := fun ij hij h =>
      hE (mem_biUnion hij h)
    apply hω
    have key : ∀ u ∈ l312Mids c s, ∀ v ∈ l312Mids c s, u ≠ v →
        ((dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) u v : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (ε ^ (-θ)) := by
      intro u hu v hv huv
      obtain ⟨i, rfl⟩ := exists_l312Mid hu
      obtain ⟨j, rfl⟩ := exists_l312Mid hv
      have hij : (i, j) ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, huv⟩
      have hDZ := not_not.1 (hE' _ hij)
      have chain : dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) (l312Mid c s i) (l312Mid c s j) ≤
          lgdDZZ (DZZ.dzzWall (l312Tilde (l312Mid c s i) (l312Mid c s j)) (ν ω))
            (Real.sqrt (ε / K)) (l312Mid c s i) (l312Mid c s j) := by
        calc dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) (l312Mid c s i) (l312Mid c s j)
            = dgLGD (muTr hW γ hb hK ω) (Real.exp T * (ε / Real.exp T)) (l312Sq1 c s)
                (l312Mid c s i) (l312Mid c s j) := by rw [mul_div_cancel₀ _ hCpos.ne']
          _ ≤ dgLGD (muHU W γ ω) (ε / Real.exp T) (l312Sq1 c s)
                (l312Mid c s i) (l312Mid c s j) := hG' _ _
          _ ≤ dgLGD (muHU W γ ω) (ε / Real.exp T) (l312Tilde (l312Mid c s i) (l312Mid c s j))
                (l312Mid c s i) (l312Mid c s j) := by
              refine dgLGD_mono_dom ?_ _ _
              rw [(isClosed_l312Tilde _ _).closure_eq, (isClosed_l312Sq1 c s).closure_eq]
              exact l312Tilde_subset_of_mids hs hu hv huv
          _ ≤ _ := dgLGD_le_lgdDZZ_wall (isClosed_l312Tilde _ _) (hν ω) hmass _ _
      calc ((dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) (l312Mid c s i) (l312Mid c s j) : ℕ∞) :
            ℝ≥0∞) ≤ _ := ENat.toENNReal_le.2 chain
        _ ≤ ENNReal.ofReal (Real.sqrt (ε / K) ^ (-(χ + ι))) := hDZ
        _ ≤ ENNReal.ofReal (ε ^ (-θ)) := ENNReal.ofReal_le_ofReal hε2
    intro u hu v hv
    by_cases huv : u = v
    · subst huv
      obtain ⟨v', hv', hne⟩ := exists_ne_l312Mids hs u
      exact (ENat.toENNReal_le.2 (dgLGD_self_le u v')).trans (key u hu v' hv' hne)
    · exact key u hu v hv huv
  calc _ ≤ _ := measure_mono hincl
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
        refine add_le_add ((h32' _ hC1 _).trans (ENNReal.ofReal_le_ofReal ?_))
          ((measure_biUnion_finset_le S _).trans hε1)
        rw [Real.log_exp]; exact hT1.le
    _ = η := hrr

end DG
end LQGMetric
