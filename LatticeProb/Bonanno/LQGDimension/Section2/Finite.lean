/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.Finite at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2
import LatticeProb.Bonanno.LQGDimension.Gaussian.Chaining

/-!
# Lemma 2.1, finiteness: `a₁ < ∞`

We prove `Blueprint.AOneFinite`, i.e. `aE 1 ≠ ⊤`: the expected maxima
`E max_{f ∈ F} (Z_f - E(f))` over finite families `F ⊆ V₁` are bounded uniformly in `F`
(by `9/2 + 768`).

## Proof

A function `f ∈ V₁` is the linear interpolation of its values at the mesh points `k/16`.
Write `δ_k(f) = f((k+1)/16) - f(k/16)` (`incr f k`), `k < 16`.  Then

* `E(f) = 8 ∑_k δ_k(f)²` (`V1_energy`);
* the canonical distance of `Z` is `‖Z_f - Z_g‖₂² = 2π ∫₀¹ |f - g| ≤ 2π ∑_k |δ_k(f) - δ_k(g)|`
  (`zCov_dist`, `integral_abs_sub_le`), because `|f - g| ≤ max_i |f(i/16) - g(i/16)|` and
  `f(i/16) = ∑_{k < i} δ_k(f)`.

We compare `Z` (realised by Gram vectors, `GramRepresentation` + `ZCovPSD` + `GramBridge`) with
the Gaussian family
`Y_f = ∑_k (3 δ_k(f) G_k + 4 T_k(δ_k(f)))`,
where the `G_k` are independent standard Gaussians and the `T_k` are independent copies of the
periodic 4-adic tree process of `LQGDimension.Tree` (depth `J` chosen so that `4^{-J}` is below
every nonzero `|δ_k(f) - δ_k(g)|`, `f, g ∈ F`).  Coordinatewise, `2π |h| ≤ 9 h² + 16 d_T²` for
`h = δ_k(f) - δ_k(g)`: the linear part covers `|h| ≥ 1` and the tree covers `|h| < 1`.  Hence
`d_Z ≤ d_Y` on `F` and Sudakov–Fernique (with the drift `-E`) gives
`E max_F (Z_f - E(f)) ≤ E max_F (Y_f - E(f))`.  Finally, pointwise,
`Y_f - E(f) ≤ ∑_k (9/32 G_k² + 4 max_t T_k(t))` since `3 δ G - 8 δ² ≤ 9 G² / 32`, and the tree
bound `E max T_k ≤ 12` (a consequence of the Gaussian maximal inequality) gives
`E max_F (Y_f - E(f)) ≤ 16 · 9/32 + 16 · 4 · 12 = 9/2 + 768`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.Section2Finite

open LQGDimension.Tree

/-! ### Functions of `V 1` -/

/-- The value of `f` at the mesh point `i / 16`. -/
def node (f : ℝ → ℝ) (i : ℕ) : ℝ := f ((i : ℝ) / 16)

/-- The increment of `f` on the `k`-th mesh interval `[k/16, (k+1)/16]`. -/
def incr (f : ℝ → ℝ) (k : ℕ) : ℝ := node f (k + 1) - node f k

variable {f g : ℝ → ℝ}

theorem V1_zero (hf : f ∈ V 1) : f 0 = 0 := by
  obtain ⟨h, -⟩ := hf
  exact h

/-- On the `k`-th mesh interval, `f ∈ V 1` is the linear interpolation of its end values. -/
theorem V1_piece (hf : f ∈ V 1) {k : ℕ} (hk : k < 16) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 16) (((k : ℝ) + 1) / 16)) :
    f x = node f k + (16 * x - k) * incr f k := by
  obtain ⟨-, -, -, hpiece⟩ := hf
  obtain ⟨α, β, h⟩ := hpiece k (by simpa using hk)
  simp only [pow_one] at h
  have hk0 : (k : ℝ) / 16 ≤ ((k : ℝ) + 1) / 16 := by linarith
  have e1 := h x hx
  have e2 := h ((k : ℝ) / 16) ⟨le_rfl, hk0⟩
  have e3 := h (((k : ℝ) + 1) / 16) ⟨hk0, le_rfl⟩
  simp only [incr, node]
  push_cast
  rw [e1, e2, e3]
  ring

/-- The derivative of `f ∈ V 1` inside the `k`-th mesh interval is `16 δ_k(f)`. -/
theorem V1_deriv (hf : f ∈ V 1) {k : ℕ} (hk : k < 16) {x : ℝ}
    (hx : x ∈ Ioo ((k : ℝ) / 16) (((k : ℝ) + 1) / 16)) :
    deriv f x = 16 * incr f k := by
  have hev : f =ᶠ[𝓝 x] fun y => node f k + (16 * y - k) * incr f k := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    exact V1_piece hf hk hy
  have hd : HasDerivAt (fun y => node f k + (16 * y - k) * incr f k) (16 * incr f k) x := by
    have := ((((hasDerivAt_id x).const_mul 16).sub_const (k : ℝ)).mul_const
      (incr f k)).const_add (node f k)
    simpa using this
  exact (hd.congr_of_eventuallyEq hev).deriv

theorem V1_intervalIntegrable_deriv_sq_piece (hf : f ∈ V 1) {k : ℕ} (hk : k < 16) :
    IntervalIntegrable (fun x => (deriv f x) ^ 2) volume ((k : ℝ) / 16)
      (((k : ℝ) + 1) / 16) := by
  have hle : (k : ℝ) / 16 ≤ ((k : ℝ) + 1) / 16 := by linarith
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
  exact (integrableOn_const (C := (16 * incr f k) ^ 2) (hs := measure_Ioo_lt_top.ne)).congr_fun
    (fun x hx => by simp only [V1_deriv hf hk hx]) measurableSet_Ioo

theorem V1_integral_deriv_sq_piece (hf : f ∈ V 1) {k : ℕ} (hk : k < 16) :
    ∫ x in (k : ℝ) / 16..((k : ℝ) + 1) / 16, (deriv f x) ^ 2 = 16 * (incr f k) ^ 2 := by
  have hle : (k : ℝ) / 16 ≤ ((k : ℝ) + 1) / 16 := by linarith
  rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (16 * incr f k) ^ 2)
      (fun x hx => by simp only [V1_deriv hf hk hx]),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- `E(f) = 8 ∑_{k < 16} δ_k(f)²` for `f ∈ V 1`. -/
theorem V1_energy (hf : f ∈ V 1) : energy f = 8 * ∑ k ∈ Finset.range 16, (incr f k) ^ 2 := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x => (deriv f x) ^ 2) (a := fun k : ℕ => (k : ℝ) / 16) (n := 16)
    (fun k hk => by
      simpa only [Nat.cast_add, Nat.cast_one] using V1_intervalIntegrable_deriv_sq_piece hf hk)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, zero_div] at h
  rw [Finset.sum_congr rfl fun k hk =>
    V1_integral_deriv_sq_piece hf (Finset.mem_range.1 hk)] at h
  have h1 : (16 : ℝ) / 16 = 1 := by norm_num
  rw [h1] at h
  unfold energy
  rw [← h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Functions of `V 1` are interval integrable on `[0, 1]`. -/
theorem V1_intervalIntegrable (hf : f ∈ V 1) : IntervalIntegrable f volume 0 1 := by
  have h := IntervalIntegrable.trans_iterate (μ := volume) (f := f)
    (a := fun k : ℕ => (k : ℝ) / 16) (n := 16) (fun k hk => by
      have hle : (k : ℝ) / 16 ≤ ((k : ℝ) + 1) / 16 := by linarith
      simp only [Nat.cast_add, Nat.cast_one]
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hle]
      refine ContinuousOn.congr (f := fun x => node f k + (16 * x - k) * incr f k)
        (by fun_prop) ?_
      intro x hx
      exact V1_piece hf hk hx)
  convert h using 1 <;> norm_num

theorem node_eq_sum (hf : f ∈ V 1) (i : ℕ) : node f i = ∑ k ∈ Finset.range i, incr f k := by
  simp only [incr]
  rw [Finset.sum_range_sub (fun k => node f k)]
  simp [node, V1_zero hf]

theorem abs_node_sub_le (hf : f ∈ V 1) (hg : g ∈ V 1) {i : ℕ} (hi : i ≤ 16) :
    |node f i - node g i| ≤ ∑ k ∈ Finset.range 16, |incr f k - incr g k| := by
  rw [node_eq_sum hf, node_eq_sum hg, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) fun _ _ _ => abs_nonneg _)

theorem exists_piece {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < 16 ∧ x ∈ Icc ((k : ℝ) / 16) (((k : ℝ) + 1) / 16) := by
  rcases lt_or_eq_of_le hx.2 with h1 | h1
  · refine ⟨⌊16 * x⌋₊, ?_, ?_, ?_⟩
    · have h0 : (0 : ℝ) ≤ 16 * x := by linarith [hx.1]
      exact (Nat.floor_lt (n := 16) h0).2 (by norm_num; linarith)
    · have := Nat.floor_le (by linarith [hx.1] : (0 : ℝ) ≤ 16 * x)
      linarith
    · have := Nat.lt_floor_add_one (16 * x)
      linarith
  · refine ⟨15, by norm_num, ?_, ?_⟩ <;> rw [h1] <;> norm_num

/-- Pointwise, `|f - g| ≤ ∑_k |δ_k(f) - δ_k(g)|` on `[0, 1]`. -/
theorem abs_sub_le_sum_of_V1 (hf : f ∈ V 1) (hg : g ∈ V 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |f x - g x| ≤ ∑ k ∈ Finset.range 16, |incr f k - incr g k| := by
  obtain ⟨k, hk, hxk⟩ := exists_piece hx
  have hA := abs_node_sub_le hf hg (i := k) (by omega)
  have hB := abs_node_sub_le hf hg (i := k + 1) (by omega)
  set S := ∑ k ∈ Finset.range 16, |incr f k - incr g k|
  rw [V1_piece hf hk hxk, V1_piece hg hk hxk]
  simp only [incr]
  have hθ0 : 0 ≤ 16 * x - k := by linarith [hxk.1]
  have hθ1 : 16 * x - k ≤ 1 := by linarith [hxk.2]
  set θ := 16 * x - k
  rw [abs_le] at hA hB ⊢
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (neg_le_iff_add_nonneg.1 hA.1),
      mul_nonneg hθ0 (neg_le_iff_add_nonneg.1 hB.1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hA.2),
      mul_nonneg hθ0 (sub_nonneg.2 hB.2)]

/-- `∫₀¹ |f - g| ≤ ∑_k |δ_k(f) - δ_k(g)|` for `f, g ∈ V 1`. -/
theorem integral_abs_sub_le (hf : f ∈ V 1) (hg : g ∈ V 1) :
    ∫ x in (0 : ℝ)..1, |f x - g x| ≤ ∑ k : Fin 16, |incr f k - incr g k| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := ∑ k ∈ Finset.range 16, |incr f k - incr g k|) (f := fun x => |f x - g x|)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_abs]
      rw [uIoc_of_le zero_le_one] at hx
      exact abs_sub_le_sum_of_V1 hf hg ⟨hx.1.le, hx.2⟩)
  rw [Finset.sum_range (fun k => |incr f k - incr g k|)] at h
  simp only [sub_zero, abs_one, mul_one] at h
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)

/-- The canonical distance of `Z`: `Var(Z_f - Z_g) = 2π ∫₀¹ |f - g|`. -/
theorem zCov_dist (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) :
    zCov f f + zCov g g - 2 * zCov f g = 2 * π * ∫ x in (0 : ℝ)..1, |f x - g x| := by
  unfold zCov
  simp only [sub_self, abs_zero, sub_zero]
  rw [intervalIntegral.integral_sub (hf.abs.add hg.abs) (hf.sub hg).abs,
    intervalIntegral.integral_add hf.abs hg.abs, intervalIntegral.integral_add hf.abs hf.abs,
    intervalIntegral.integral_add hg.abs hg.abs]
  ring

/-! ### The comparison family -/

/-- Index set of the comparison family: for each of the 16 mesh intervals, one linear coordinate
(`none`) and one copy of the tree of depth `J`. -/
abbrev CompIdx (J : ℕ) : Type := Fin 16 × Option (TreeIdx J)

/-- The unit coordinate vectors. -/
def ev (J : ℕ) (p : CompIdx J) : EuclideanSpace ℝ (CompIdx J) := EuclideanSpace.single p 1

theorem norm_ev (J : ℕ) (p : CompIdx J) : ‖ev J p‖ = 1 := by
  simp [ev]

theorem inner_ev (J : ℕ) (p : CompIdx J) (x : EuclideanSpace ℝ (CompIdx J)) :
    ⟪ev J p, x⟫ = x p := by
  simp [ev, EuclideanSpace.inner_single_left]

/-- The comparison vector of `f`: `3 δ_k(f)` on the linear coordinate of the interval `k`, and
`4 ×` the tree vector of `δ_k(f)` on the `k`-th copy of the tree. -/
def compVec (J : ℕ) (f : ℝ → ℝ) : EuclideanSpace ℝ (CompIdx J) :=
  WithLp.toLp 2 fun p => p.2.elim (3 * incr f p.1) fun i => 4 * treeCoord J (incr f p.1) i

theorem norm_compVec_sub_sq (J : ℕ) (f g : ℝ → ℝ) :
    ‖compVec J f - compVec J g‖ ^ 2 = ∑ k : Fin 16, ((3 * incr f k - 3 * incr g k) ^ 2 +
      ∑ i : TreeIdx J, (4 * treeCoord J (incr f k) i - 4 * treeCoord J (incr g k) i) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_option]
  simp [compVec]

/-- Coordinatewise domination: `2π |s - t| ≤ 9 (s - t)² + 16 d_tree(s, t)²`. -/
theorem two_pi_abs_le (J : ℕ) {s t : ℝ} (h : s = t ∨ 1 / 4 ^ J ≤ |s - t|) :
    2 * π * |s - t| ≤ (3 * s - 3 * t) ^ 2 +
      ∑ i : TreeIdx J, (4 * treeCoord J s i - 4 * treeCoord J t i) ^ 2 := by
  have hpi := Real.pi_le_four
  have hnn : 0 ≤ ∑ i : TreeIdx J, (4 * treeCoord J s i - 4 * treeCoord J t i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have habs := abs_nonneg (s - t)
  have h4 := mul_nonneg (sub_nonneg.2 hpi) habs
  rcases h with rfl | hJ
  · simp
  · rcases le_or_gt 1 |s - t| with h1 | h1
    · have hsq : (3 * s - 3 * t) ^ 2 = 9 * |s - t| ^ 2 := by
        rw [sq_abs]
        ring
      nlinarith [mul_nonneg (sub_nonneg.2 h1) habs]
    · have htree := abs_sub_le_two_mul_sum_sq_treeCoord hJ h1
      have h16 : ∑ i : TreeIdx J, (4 * treeCoord J s i - 4 * treeCoord J t i) ^ 2 =
          16 * ∑ i : TreeIdx J, (treeCoord J s i - treeCoord J t i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      nlinarith [sq_nonneg (3 * s - 3 * t)]

theorem inner_compVec (J : ℕ) (f : ℝ → ℝ) (x : EuclideanSpace ℝ (CompIdx J)) :
    ⟪compVec J f, x⟫ = ∑ k : Fin 16, (3 * incr f k * ⟪ev J (k, none), x⟫ +
      4 * ∑ i : TreeIdx J, treeCoord J (incr f k) i * ⟪ev J (k, some i), x⟫) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_option]
  simp only [inner_ev, compVec, PiLp.toLp_apply, Option.elim, RCLike.inner_apply, conj_trivial,
    Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- Pointwise bound: `Y_f - E(f) ≤ ∑_k (9/32 G_k² + 4 max T_k)`. -/
theorem inner_compVec_sub_energy_le (J : ℕ) (hf : f ∈ V 1) (x : EuclideanSpace ℝ (CompIdx J)) :
    ⟪compVec J f, x⟫ + -energy f ≤ ∑ k : Fin 16, 9 / 32 * ⟪ev J (k, none), x⟫ ^ 2 +
      ∑ k : Fin 16, 4 * treeMax J (fun i => ev J (k, some i)) x := by
  rw [inner_compVec, V1_energy hf, Finset.sum_range (fun k => incr f k ^ 2)]
  have hk : ∀ k : Fin 16, 3 * incr f k * ⟪ev J (k, none), x⟫ +
      4 * ∑ i : TreeIdx J, treeCoord J (incr f k) i * ⟪ev J (k, some i), x⟫ - 8 * incr f k ^ 2 ≤
      9 / 32 * ⟪ev J (k, none), x⟫ ^ 2 + 4 * treeMax J (fun i => ev J (k, some i)) x := by
    intro k
    have h1 := sum_treeCoord_mul_inner_le J (fun i => ev J (k, some i)) (incr f k) x
    nlinarith [sq_nonneg (3 * ⟪ev J (k, none), x⟫ - 16 * incr f k)]
  calc _ = ∑ k : Fin 16, (3 * incr f k * ⟪ev J (k, none), x⟫ +
        4 * ∑ i : TreeIdx J, treeCoord J (incr f k) i * ⟪ev J (k, some i), x⟫ -
          8 * incr f k ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        ring
    _ ≤ ∑ k : Fin 16, (9 / 32 * ⟪ev J (k, none), x⟫ ^ 2 +
          4 * treeMax J (fun i => ev J (k, some i)) x) := Finset.sum_le_sum fun k _ => hk k
    _ = _ := Finset.sum_add_distrib

/-- The integrable majorant `∑_k (9/32 G_k² + 4 max T_k)` of the comparison family. -/
def compBound (J : ℕ) (x : EuclideanSpace ℝ (CompIdx J)) : ℝ :=
  ∑ k : Fin 16, 9 / 32 * ⟪ev J (k, none), x⟫ ^ 2 +
    ∑ k : Fin 16, 4 * treeMax J (fun i => ev J (k, some i)) x

theorem integrable_levelMax_ev (hMI : Blueprint.MaxIntegrable) (J : ℕ) (k : Fin 16)
    (j : Fin (J + 1)) :
    Integrable (levelMax J (fun i => ev J (k, some i)) j)
      (stdGaussian (EuclideanSpace ℝ (CompIdx J))) := by
  have := hMI (Fin (2 * 4 ^ (j : ℕ))) (EuclideanSpace ℝ (CompIdx J)) Finset.univ
    (fun m => ev J (k, some ⟨j, m⟩)) (fun _ => 0)
  simp only [add_zero] at this
  exact this

theorem integrable_compBound_aux (hMI : Blueprint.MaxIntegrable) (J : ℕ) :
    (∀ k ∈ (Finset.univ : Finset (Fin 16)), Integrable
      (fun x => 9 / 32 * ⟪ev J (k, none), x⟫ ^ 2) (stdGaussian (EuclideanSpace ℝ (CompIdx J)))) ∧
    (∀ k ∈ (Finset.univ : Finset (Fin 16)), Integrable
      (fun x => 4 * treeMax J (fun i => ev J (k, some i)) x)
      (stdGaussian (EuclideanSpace ℝ (CompIdx J)))) :=
  ⟨fun _ _ => (GaussianMax.integrable_inner_sq _).const_mul _,
    fun k _ => (integrable_treeMax _ _ (integrable_levelMax_ev hMI J k)).const_mul _⟩

theorem integrable_compBound (hMI : Blueprint.MaxIntegrable) (J : ℕ) :
    Integrable (compBound J) (stdGaussian (EuclideanSpace ℝ (CompIdx J))) :=
  (integrable_finsetSum _ (integrable_compBound_aux hMI J).1).add
    (integrable_finsetSum _ (integrable_compBound_aux hMI J).2)

theorem integral_compBound_le (hMI : Blueprint.MaxIntegrable) (J : ℕ) :
    ∫ x, compBound J x ∂stdGaussian (EuclideanSpace ℝ (CompIdx J)) ≤ 9 / 2 + 768 := by
  obtain ⟨hint1, hint2⟩ := integrable_compBound_aux hMI J
  unfold compBound
  rw [integral_add (integrable_finsetSum _ hint1) (integrable_finsetSum _ hint2),
    integral_finsetSum _ hint1, integral_finsetSum _ hint2]
  have e1 : ∀ k : Fin 16, ∫ x, 9 / 32 * ⟪ev J (k, none), x⟫ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (CompIdx J)) = 9 / 32 := by
    intro k
    rw [integral_const_mul, GaussianMax.integral_inner_sq, norm_ev]
    norm_num
  have e2 : ∀ k : Fin 16, ∫ x, 4 * treeMax J (fun i => ev J (k, some i)) x
      ∂stdGaussian (EuclideanSpace ℝ (CompIdx J)) ≤ 4 * 12 := by
    intro k
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_treeMax_le _ _ (fun i => (norm_ev J _).le) (integrable_levelMax_ev hMI J k))
      (by norm_num)
  simp only [e1]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin 16))) => e2 k
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hsum ⊢
  linarith

/-- The expected maximum of the comparison family with drift `-E` is at most `9/2 + 768`. -/
theorem vecExpectedMax_compVec_le (hMI : Blueprint.MaxIntegrable) (J : ℕ) (F : Finset (V 1)) :
    vecExpectedMax F (fun f : V 1 => compVec J f) (fun f => -energy f) ≤ 9 / 2 + 768 := by
  unfold vecExpectedMax
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp only [iSup_of_empty', Real.sSup_empty, integral_zero]
    norm_num
  have : Nonempty F := hF.to_subtype
  refine (integral_mono (hMI (V 1) (EuclideanSpace ℝ (CompIdx J)) F
    (fun f : V 1 => compVec J f) (fun f => -energy f)) (integrable_compBound hMI J)
    (fun x => ciSup_le fun f => inner_compVec_sub_energy_le J f.1.2 x)).trans ?_
  exact integral_compBound_le hMI J

/-- A depth `J` with `4^{-J}` below every positive value of `φ` on a finite set. -/
theorem exists_one_div_pow_four_le {α : Type*} (S : Finset α) (φ : α → ℝ) :
    ∃ J : ℕ, ∀ p ∈ S, 0 < φ p → 1 / 4 ^ J ≤ φ p := by
  classical
  by_cases hD : (S.filter fun p => 0 < φ p).Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := (S.filter fun p => 0 < φ p).exists_min_image φ hD
    have hpos : 0 < φ p₀ := (Finset.mem_filter.1 hp₀).2
    obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 4 : ℝ) < 1)
    refine ⟨J, fun p hp hpp => ?_⟩
    have := hmin p (Finset.mem_filter.2 ⟨hp, hpp⟩)
    rw [one_div_pow] at hJ
    linarith
  · exact ⟨0, fun p hp hpp => absurd ⟨p, Finset.mem_filter.2 ⟨hp, hpp⟩⟩ hD⟩

theorem gaussianExpectedMax_congr_of_eqOn {ι : Type*} (F : Finset ι) {C C' : ι → ι → ℝ}
    (b : ι → ℝ) (h : ∀ i ∈ F, ∀ j ∈ F, C i j = C' i j) :
    gaussianExpectedMax F C b = gaussianExpectedMax F C' b := by
  have hM : (Matrix.of fun i j : F => C i j) = Matrix.of fun i j : F => C' i j := by
    ext i j
    exact h _ i.2 _ j.2
  unfold gaussianExpectedMax
  rw [hM]

/-- The uniform bound: `E max_{f ∈ F} (Z_f - E(f)) ≤ 9/2 + 768` for every finite `F ⊆ V₁`. -/
theorem gaussianExpectedMax_V1_le (hSF : Blueprint.SudakovFernique)
    (hGB : Blueprint.GramBridge) (hGR : Blueprint.GramRepresentation)
    (hMI : Blueprint.MaxIntegrable) (hPSD : Blueprint.ZCovPSD) (F : Finset (V 1)) :
    gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy f) ≤ 9 / 2 + 768 := by
  classical
  -- Gram vectors for `Z` on `F`.
  set F' : Finset (ℝ → ℝ) := F.map (Function.Embedding.subtype _) with hF'
  have hmemF' : ∀ f : V 1, f ∈ F → (f : ℝ → ℝ) ∈ F' := fun f hf =>
    Finset.mem_map_of_mem _ hf
  have hint' : ∀ f ∈ F', IntervalIntegrable f volume 0 1 := by
    intro f hf
    obtain ⟨g, -, rfl⟩ := Finset.mem_map.1 hf
    exact V1_intervalIntegrable g.2
  obtain ⟨v, hv⟩ := hGR (ℝ → ℝ) F' zCov (hPSD F' hint')
  -- The depth of the trees.
  obtain ⟨J, hJ⟩ := exists_one_div_pow_four_le ((F ×ˢ F) ×ˢ (Finset.univ : Finset (Fin 16)))
    (fun p => |incr p.1.1 p.2 - incr p.1.2 p.2|)
  -- Comparison of canonical distances.
  have hdist : ∀ f ∈ F, ∀ g ∈ F, ‖v f - v g‖ ≤ ‖compVec J f - compVec J g‖ := by
    intro f hf g hg
    have h1 : ‖v f - v g‖ ^ 2 = 2 * π * ∫ x in (0 : ℝ)..1, |(f : ℝ → ℝ) x - (g : ℝ → ℝ) x| := by
      rw [← zCov_dist (V1_intervalIntegrable f.2) (V1_intervalIntegrable g.2), norm_sub_sq_real,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        hv _ (hmemF' f hf) _ (hmemF' f hf), hv _ (hmemF' g hg) _ (hmemF' g hg),
        hv _ (hmemF' f hf) _ (hmemF' g hg)]
      ring
    have h2 := integral_abs_sub_le f.2 g.2
    have h3 : 2 * π * ∑ k : Fin 16, |incr f k - incr g k| ≤
        ‖compVec J f - compVec J g‖ ^ 2 := by
      rw [norm_compVec_sub_sq, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => two_pi_abs_le J ?_
      by_cases heq : incr f k = incr g k
      · exact Or.inl heq
      · exact Or.inr (hJ ((f, g), k)
          (Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hf, hg⟩, Finset.mem_univ _⟩)
          (abs_pos.2 (sub_ne_zero.2 heq)))
    have h4 : ‖v f - v g‖ ^ 2 ≤ ‖compVec J f - compVec J g‖ ^ 2 := by
      rw [h1]
      nlinarith [Real.pi_pos]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4
  calc gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy f)
      = gaussianExpectedMax F (fun f g : V 1 => ⟪v f, v g⟫) (fun f => -energy f) :=
        gaussianExpectedMax_congr_of_eqOn F _ fun f hf g hg =>
          (hv _ (hmemF' f hf) _ (hmemF' g hg)).symm
    _ = vecExpectedMax F (fun f : V 1 => v f) (fun f => -energy f) :=
        hGB (V 1) (EuclideanSpace ℝ F') F (fun f : V 1 => v f) (fun f => -energy f)
    _ ≤ vecExpectedMax F (fun f : V 1 => compVec J f) (fun f => -energy f) :=
        hSF (V 1) (EuclideanSpace ℝ F') (EuclideanSpace ℝ (CompIdx J)) F
          (fun f : V 1 => v f) (fun f : V 1 => compVec J f) (fun f => -energy f) hdist
    _ ≤ 9 / 2 + 768 := vecExpectedMax_compVec_le hMI J F

end LQGDimension.Section2Finite

namespace LQGDimension

/-- **Lemma 2.1 (finiteness)**: `a₁ < ∞`. -/
theorem aOneFinite_of (hSF : Blueprint.SudakovFernique) (hGB : Blueprint.GramBridge)
    (hGR : Blueprint.GramRepresentation) (hMI : Blueprint.MaxIntegrable)
    (hPSD : Blueprint.ZCovPSD) :
    Blueprint.AOneFinite := by
  unfold Blueprint.AOneFinite aE
  refine ne_top_of_le_ne_top (EReal.coe_ne_top (9 / 2 + 768)) (iSup_le fun F => ?_)
  exact EReal.coe_le_coe_iff.2
    (Section2Finite.gaussianExpectedMax_V1_le hSF hGB hGR hMI hPSD F)

end LQGDimension
