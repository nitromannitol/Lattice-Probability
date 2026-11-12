/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import Mathlib.Algebra.Order.Round
import Mathlib.Order.Interval.Finset.Defs

/-!
# GM §3.3: the events `𝖤_r(z)` and Lemmas 3.7–3.9 (task P2-M2E, WP-M2e, row 7 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.

* `goodAnnulus D D' α A C' r z` — the event `𝖤_r(z) = 𝖤_r(z; α, A, C')` of GM l. 1325–1331
  (GM.S3.6), a set of fields, as the intersection of its three conditions `gaCompare` (condition 1,
  comparison of `D_h` and `D̃_h`), `gaLong` (condition 2, lower bound for paths in
  `𝔸_{αr,r}(z)`) and `gaAround` (condition 3, a short disconnecting path in `𝔸_{αr,r}(z)`).
* `L3_7`, `L3_8`, `L3_9`: the statements of GM Lemmas 3.7 (`lem-attained-msrble`, l. 1340–1344),
  3.8 (`lem-shorter-annulus`, l. 1366–1373, read as in DEVIATIONS GA-6) and 3.9
  (`lem-shorter-annulus-all`, l. 1398–1401).
* `gm_L3_9`: GM Lemma 3.9 from Lemma 3.8, by GM's proof (l. 1403–1404): "Upon choosing `q`
  sufficiently large, this follows from Lemma 3.8 and a union bound over all
  `w ∈ (ε^{1+ν}𝕣/100) ℤ² ∩ (𝕣U)`". Here `q = 3 + 2ν > 2(1 + ν)`, and the union is over the grid
  points of a box containing `𝕣U` (`(2M + 1)²` points, `M ≈ 100 R₀ ε^{-1-ν}`).

Readings (proposed DEVIATIONS entries, see the task report):
* the interval of L3.8 is `[ε^{1+ν}𝕣, ε𝕣]` (GA-6), and the count in (B) is `(ν − μ)/2 · log₈ ε⁻¹`
  as in the Lean statement of P3.6 (GA-5);
* L3.8 and L3.9 hold for every `C'` (GM: `C' ∈ (0, C_*)`; the restriction is not used);
* in L3.9 `U` is also bounded (otherwise the union bound has infinitely many terms) and the grid
  point `w` is within `ε^{1+ν}𝕣/100` of `z` instead of in `𝕣U` (the nearest grid point of a point
  near `∂(𝕣U)` need not lie in `𝕣U`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-! ## GM.S3.6: the event `𝖤_r(z)` (GM l. 1325–1331) -/

/-- condition 1 of `𝖤_r(z)` (GM l. 1327): for `u ∈ ∂B_{αr}(z)`, `v ∈ ∂B_r(z)` whose
`D_h`-geodesic is unique and contained in `cl 𝔸_{αr,r}(z)`, `D̃_h(u,v) ≤ C' D_h(u,v)` -/
def gaCompare (D D' : DistC → ContMetric) (α C' r : ℝ) (z : ℂ) : Set DistC :=
  {g | ∀ u ∈ Metric.sphere z (α * r), ∀ v ∈ Metric.sphere z r,
    UniqueGeodIn (D g) u v (closure (annulus z (α * r) r : Set ℂ)) →
      (D' g).1 (u, v) ≤ C' * (D g).1 (u, v)}

/-- condition 2 of `𝖤_r(z)` (GM l. 1328): if `D_h(u,v) > D_h(u, ∂𝔸_{r/2,2r}(z))` or
`D̃_h(u,v) > D̃_h(u, ∂𝔸_{r/2,2r}(z))`, then every path from `u` to `v` in `cl 𝔸_{αr,r}(z)` has
`D_h`-length `> D_h(u, v; 𝔸_{r/2,2r}(z))` -/
def gaLong (D D' : DistC → ContMetric) (α r : ℝ) (z : ℂ) : Set DistC :=
  {g | ∀ u ∈ Metric.sphere z (α * r), ∀ v ∈ Metric.sphere z r,
    (setDist (D g) {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) <
        ENNReal.ofReal ((D g).1 (u, v)) ∨
      setDist (D' g) {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) <
        ENNReal.ofReal ((D' g).1 (u, v))) →
    ∀ (a b : ℝ) (P : ℝ → ℂ), a ≤ b → ContinuousOn P (Icc a b) → P a = u → P b = v →
      P '' Icc a b ⊆ closure (annulus z (α * r) r : Set ℂ) →
      (D g).internal (annulus z (r / 2) (2 * r)) u v < (D g).len P a b}

/-- condition 3 of `𝖤_r(z)` (GM l. 1329): a path in `𝔸_{αr,r}(z)` which disconnects its inner and
outer boundaries and has `D_h`-length `≤ A D_h(∂B_{αr}(z), ∂B_r(z))` -/
def gaAround (D : DistC → ContMetric) (α A r : ℝ) (z : ℂ) : Set DistC :=
  {g | ∃ (a b : ℝ) (G : ℝ → ℂ), a ≤ b ∧ ContinuousOn G (Icc a b) ∧
    G '' Icc a b ⊆ (annulus z (α * r) r : Set ℂ) ∧
    Disconnects (G '' Icc a b) (Metric.sphere z (α * r)) (Metric.sphere z r) ∧
    (D g).len G a b ≤ ENNReal.ofReal A *
      setDist (D g) (Metric.sphere z (α * r)) (Metric.sphere z r)}

/-- **GM.S3.6** (l. 1325–1331): the event `𝖤_r(z) = 𝖤_r(z; α, A, C')` -/
def goodAnnulus (D D' : DistC → ContMetric) (α A C' r : ℝ) (z : ℂ) : Set DistC :=
  gaCompare D D' α C' r z ∩ gaLong D D' α r z ∩ gaAround D α A r z

/-! ## Statements of GM Lemmas 3.7–3.9 -/

/-- **GM Lemma 3.7** (`lem-attained-msrble`, l. 1340–1344): `𝖤_r(z) ∈ σ((h − h_{4r}(z))|_{𝔸_{r/2,2r}(z)})`,
read as "a.s. equal to an event of this σ-algebra" (decision D30). -/
def L3_7 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
  ∀ {α : ℝ}, 1 / 2 < α → α < 1 → ∀ A C' : ℝ, ∀ (z : ℂ) (r : ℝ), 0 < r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (4 * r) z))
      (annulus z (r / 2) (2 * r))) (h ⁻¹' goodAnnulus D D' α A C' r z)

/-- condition (B) of GM P3.6 (l. 1294) for `(𝕣, ε)` with the count `(ν − μ)/2 · log₈ ε⁻¹` (GA-5) -/
def condB (D D' : DistC → ContMetric) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (μ ν p α C' R ε : ℝ) : Prop :=
  (ν - μ) / 2 * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν (fun k =>
    ENNReal.ofReal (1 - p) ≤ P (h ⁻¹' badScale D D' α ((8 : ℝ)⁻¹ ^ k * R) C'))

/-- **GM Lemma 3.8** (`lem-shorter-annulus`, l. 1366–1373), interval `[ε^{1+ν}𝕣, ε𝕣]` (GA-6):
for each `q > 0` there are `α_* ∈ (1/2,1)`, `p ∈ (0,1)` such that for `α ∈ [α_*,1)` there is
`A > 1` with: if (B) holds for `(𝕣, ε)`, then for every `z`,
`P[no 𝖤_r(z), r ∈ [ε^{1+ν}𝕣, ε𝕣] ∩ 8^{-ℕ}𝕣] ≤ K₀ ε^q`, `K₀` uniform in `z`, `𝕣`, `ε`, `C'`. -/
def L3_8 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
  ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν < 1 → ∀ q : ℝ, 0 < q →
  ∃ α₀ p : ℝ, α₀ ∈ Ioo (1 / 2 : ℝ) 1 ∧ p ∈ Ioo (0 : ℝ) 1 ∧ ∀ α ∈ Ico α₀ 1, ∃ A : ℝ, 1 < A ∧
  ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ C' : ℝ,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ R : ℝ, 0 < R → ∀ ε ∈ Ioo (0 : ℝ) 1,
    condB D D' P h μ ν p α C' R ε → ∀ z : ℂ,
      P {ω | ∀ k : ℕ, ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k → (8 : ℝ)⁻¹ ^ k ≤ ε →
        h ω ∉ goodAnnulus D D' α A C' ((8 : ℝ)⁻¹ ^ k * R) z} ≤ ENNReal.ofReal (K₀ * ε ^ q)

/-- the grid point `δ m ∈ δ ℤ²` -/
def gridPt (δ : ℝ) (m : ℤ × ℤ) : ℂ := (δ : ℂ) * ((m.1 : ℂ) + (m.2 : ℂ) * Complex.I)

/-- **GM Lemma 3.9** (`lem-shorter-annulus-all`, l. 1398–1401), `U` bounded: if (B) holds for
`(𝕣, ε)`, then with probability `→ 1` as `ε → 0` (uniformly in `𝕣`), every `x ∈ 𝕣U` has a scale
`r = 8^{-k}𝕣 ∈ [ε^{1+ν}𝕣, ε𝕣]` and a grid point `w ∈ (ε^{1+ν}𝕣/100) ℤ²` with
`|x − w| ≤ ε^{1+ν}𝕣/100`, `x ∈ B_{r/2}(w)` and `𝖤_r(w)`. -/
def L3_9 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
  ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν < 1 →
  ∃ α₀ p : ℝ, α₀ ∈ Ioo (1 / 2 : ℝ) 1 ∧ p ∈ Ioo (0 : ℝ) 1 ∧ ∀ α ∈ Ico α₀ 1, ∃ A : ℝ, 1 < A ∧
  ∀ C' : ℝ, ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → ∀ η : ℝ, 0 < η →
  ∃ ε₁ : ℝ, 0 < ε₁ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ R : ℝ, 0 < R → ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    condB D D' P h μ ν p α C' R ε →
      P {ω | ∀ x ∈ (fun u => (R : ℂ) * u) '' U, ∃ k : ℕ, ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧
        (8 : ℝ)⁻¹ ^ k ≤ ε ∧ ∃ m : ℤ × ℤ,
          ‖x - gridPt (ε ^ (1 + ν) * R / 100) m‖ ≤ ε ^ (1 + ν) * R / 100 ∧
          ‖x - gridPt (ε ^ (1 + ν) * R / 100) m‖ < (8 : ℝ)⁻¹ ^ k * R / 2 ∧
          h ω ∈ goodAnnulus D D' α A C' ((8 : ℝ)⁻¹ ^ k * R)
            (gridPt (ε ^ (1 + ν) * R / 100) m)}ᶜ ≤ ENNReal.ofReal η

/-! ## GM Lemma 3.9 from Lemma 3.8 (GM l. 1403–1404) -/

lemma gridPt_re (δ : ℝ) (m : ℤ × ℤ) : (gridPt δ m).re = δ * m.1 := by
  simp [gridPt]

lemma gridPt_im (δ : ℝ) (m : ℤ × ℤ) : (gridPt δ m).im = δ * m.2 := by
  simp [gridPt]

/-- rounding to the grid `δ ℤ`: `|t − δ ⌊t/δ⌉| ≤ δ/2` and `|⌊t/δ⌉| ≤ M` if `|t| ≤ δ(M − 1)` -/
lemma round_grid {δ t : ℝ} (hδ : 0 < δ) {M : ℕ} (ht : |t| / δ + 1 ≤ M) :
    |t - δ * (round (t / δ) : ℝ)| ≤ δ / 2 ∧ round (t / δ) ∈ Finset.Icc (-(M : ℤ)) M := by
  have h1 := abs_sub_round (t / δ)
  have e : t - δ * (round (t / δ) : ℝ) = δ * (t / δ - round (t / δ)) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [e, abs_mul, abs_of_pos hδ]
    nlinarith
  · have h2 : |t / δ| = |t| / δ := by rw [abs_div, abs_of_pos hδ]
    have h3 := abs_le.1 h1
    have h4 := abs_le.1 (le_of_eq h2 : |t / δ| ≤ |t| / δ)
    have hlo : ((-(M : ℤ) : ℤ) : ℝ) ≤ (round (t / δ) : ℝ) := by push_cast; linarith
    have hhi : (round (t / δ) : ℝ) ≤ ((M : ℤ) : ℝ) := by push_cast; linarith
    exact Finset.mem_Icc.2 ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- the arithmetic of the union bound: `(2M + 1)² K₀ ε^{3+2ν} ≤ K₀ (200R₀ + 5)² ε` for
`M ≤ 100R₀ ε^{-(1+ν)} + 2` -/
lemma unionBound_arith {ε ν R₀ K₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hν : 0 < ν)
    (hK₀ : 0 < K₀) {M : ℕ} (hM : (M : ℝ) * ε ^ (1 + ν) ≤ 100 * R₀ + 2 * ε ^ (1 + ν)) :
    (2 * M + 1 : ℝ) ^ 2 * (K₀ * ε ^ (3 + 2 * ν)) ≤ K₀ * (200 * R₀ + 5) ^ 2 * ε := by
  set x := ε ^ (1 + ν) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hε0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one hε0.le hε1.le (by linarith)
  have hq : ε ^ (3 + 2 * ν) = x ^ 2 * ε := by
    rw [show (3 + 2 * ν) = (1 + ν) + (1 + ν) + 1 by ring, Real.rpow_add hε0,
      Real.rpow_add hε0, Real.rpow_one, hx]
    ring
  have hb : (2 * M + 1 : ℝ) * x ≤ 200 * R₀ + 5 := by nlinarith
  have hb0 : 0 ≤ (2 * M + 1 : ℝ) * x := by positivity
  have hsq : ((2 * M + 1 : ℝ) * x) ^ 2 ≤ (200 * R₀ + 5) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  rw [hq]
  have : (2 * M + 1 : ℝ) ^ 2 * (K₀ * (x ^ 2 * ε)) = K₀ * ε * ((2 * M + 1 : ℝ) * x) ^ 2 := by ring
  rw [this]
  have hKε : 0 ≤ K₀ * ε := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq hKε]

/-- **GM Lemma 3.9** (l. 1398–1404), from GM Lemma 3.8 with `q = 3 + 2ν` and a union bound over
the grid points of a box containing `𝕣U`. -/
theorem gm_L3_9 (h38 : L3_8) : L3_9 := by
  intro γ D D' c hS μ ν hμ hμν hν1
  have hν : 0 < ν := hμ.trans hμν
  obtain ⟨α₀, p, hα₀, hp, H⟩ := h38 hS hμ hμν hν1 (3 + 2 * ν) (by linarith)
  refine ⟨α₀, p, hα₀, hp, fun α hα => ?_⟩
  obtain ⟨A, hA, K₀, hK₀, H2⟩ := H α hα
  refine ⟨A, hA, fun C' U _ hUb η hη => ?_⟩
  obtain ⟨R₀, hR₀, hUR⟩ := hUb.subset_closedBall_lt 0 (0 : ℂ)
  set B : ℝ := (200 * R₀ + 5) ^ 2 with hB
  have hB0 : 0 < B := by positivity
  refine ⟨min 1 (η / (K₀ * B)), lt_min one_pos (by positivity), ?_⟩
  intro Ω _ P _ h hh R hR ε hε hBad
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have hεη : ε ≤ η / (K₀ * B) := hε.2.le.trans (min_le_right _ _)
  set x := ε ^ (1 + ν) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hε0 _
  set δ : ℝ := x * R / 100 with hδ
  have hδ0 : 0 < δ := by positivity
  set M : ℕ := ⌈100 * R₀ / x⌉₊ + 1 with hMdef
  have hMlt : (M : ℝ) < 100 * R₀ / x + 2 := by
    rw [hMdef]; push_cast
    linarith [Nat.ceil_lt_add_one (show 0 ≤ 100 * R₀ / x by positivity)]
  have hMge : 100 * R₀ / x + 1 ≤ (M : ℝ) := by
    rw [hMdef]; push_cast
    linarith [Nat.le_ceil (100 * R₀ / x)]
  have hMx : (M : ℝ) * x ≤ 100 * R₀ + 2 * x := by
    have := mul_le_mul_of_nonneg_right hMlt.le hx0.le
    rwa [add_mul, div_mul_cancel₀ _ hx0.ne'] at this
  set Box : Finset (ℤ × ℤ) := Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M with hBox
  set F : ℤ × ℤ → Set Ω := fun m => {ω | ∀ k : ℕ, ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k →
    (8 : ℝ)⁻¹ ^ k ≤ ε → h ω ∉ goodAnnulus D D' α A C' ((8 : ℝ)⁻¹ ^ k * R) (gridPt δ m)} with hF
  have hsub : {ω | ∀ y ∈ (fun u => (R : ℂ) * u) '' U, ∃ k : ℕ, ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧
        (8 : ℝ)⁻¹ ^ k ≤ ε ∧ ∃ m : ℤ × ℤ,
          ‖y - gridPt (ε ^ (1 + ν) * R / 100) m‖ ≤ ε ^ (1 + ν) * R / 100 ∧
          ‖y - gridPt (ε ^ (1 + ν) * R / 100) m‖ < (8 : ℝ)⁻¹ ^ k * R / 2 ∧
          h ω ∈ goodAnnulus D D' α A C' ((8 : ℝ)⁻¹ ^ k * R)
            (gridPt (ε ^ (1 + ν) * R / 100) m)}ᶜ ⊆ ⋃ m ∈ Box, F m := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_exists, not_and] at hω
    obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ := hω
    have hun : ‖u‖ ≤ R₀ := by simpa using hUR hu
    have hyn : ‖(R : ℂ) * u‖ ≤ R * R₀ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
      exact mul_le_mul_of_nonneg_left hun hR.le
    have hbd : ∀ t : ℝ, |t| ≤ ‖(R : ℂ) * u‖ → |t| / δ + 1 ≤ M := by
      intro t ht
      have : |t| / δ ≤ 100 * R₀ / x := by
        rw [div_le_div_iff₀ hδ0 hx0, hδ]
        nlinarith
      linarith
    obtain ⟨hre1, hre2⟩ := round_grid hδ0 (hbd _ (Complex.abs_re_le_norm _))
    obtain ⟨him1, him2⟩ := round_grid hδ0 (hbd _ (Complex.abs_im_le_norm _))
    set m : ℤ × ℤ := (round (((R : ℂ) * u).re / δ), round (((R : ℂ) * u).im / δ)) with hm
    have hdist : ‖(R : ℂ) * u - gridPt δ m‖ ≤ δ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.sub_re, Complex.sub_im, gridPt_re, gridPt_im]
      linarith
    refine mem_biUnion (x := m) (Finset.mem_coe.2 (Finset.mem_product.2 ⟨hre2, him2⟩)) ?_
    intro k hk1 hk2 hgood
    have hlt : ‖(R : ℂ) * u - gridPt δ m‖ < (8 : ℝ)⁻¹ ^ k * R / 2 := by
      have : δ < (8 : ℝ)⁻¹ ^ k * R / 2 := by
        rw [hδ]; nlinarith
      linarith
    exact hy k hk1 hk2 m hdist hlt hgood
  have hcard : (Box.card : ℝ) = (2 * M + 1 : ℝ) ^ 2 := by
    rw [hBox, Finset.card_product, Int.card_Icc]
    have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [this]; push_cast; ring
  calc P _ ≤ P (⋃ m ∈ Box, F m) := measure_mono hsub
    _ ≤ ∑ m ∈ Box, P (F m) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Box, ENNReal.ofReal (K₀ * ε ^ (3 + 2 * ν)) :=
        Finset.sum_le_sum fun m _ => H2 C' P h hh R hR ε ⟨hε0, hε1⟩ hBad (gridPt δ m)
    _ = ENNReal.ofReal ((Box.card : ℝ) * (K₀ * ε ^ (3 + 2 * ν))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (p := (Box.card : ℝ)) (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal η := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcard]
        refine (unionBound_arith hε0 hε1 hν hK₀ hMx).trans ?_
        have : K₀ * B * ε ≤ η := by
          rw [le_div_iff₀ (by positivity)] at hεη; linarith
        rw [← hB]; linarith

end LQGMetric.GM
