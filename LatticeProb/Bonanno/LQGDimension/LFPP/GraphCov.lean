/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.GraphCov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Section2.SubadditiveAux
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Node `L32g`: the graph covariance limit (Lemma 3.2, `g = 0`)

We prove `Blueprint.Draft.GraphCovLimit`:
`δ⁻¹ logCov(μ_{δ,f} - μ_{δ,0}, μ_{δ,f'} - μ_{δ,0}) → zCov f f'` as `δ ↓ 0`.

Structure.

1. **The kernel `lk c u = log (1 + c²/u²)`** (`lk`): nonnegative, even, monotone in `|c|`,
   `1/|u|`-Lipschitz in `c`, integrable on `ℝ` with `∫ lk c = 2π|c|` (explicit antiderivative
   `u lk c u + 2|c| arctan (u/|c|)`).
2. **Segment combinations of piecewise-affine curves** (`pc`): `logCov` is bilinear; for curves
   that are affine on the mesh intervals, `logCov (pc M P) (pc M' Q)` is the double integral
   `∫₀¹∫₀¹ -log ‖P x - Q y‖ dy dx` (the weight `1/M` of an edge times the uniform
   parametrization is `dx`).
3. **Substitution** `y = x + δ w` (in general form `y = (δ w + a - β')/α'`): the four-term
   integrand becomes `Σ σ_k lk (b_k) w` with `b_k` differences of profile values.
4. **Dominated convergence** (`core_tendsto`), for a general countably generated filter (so that
   it also gives uniformity over parameters in node `L32c`), with the majorant `2 lk B w`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.GraphCov

open Blueprint.Draft

/-! ## 1. The kernel `lk` -/

/-- `lk c u = log (1 + c² / u²)`. -/
def lk (c u : ℝ) : ℝ := Real.log (1 + c ^ 2 / u ^ 2)

lemma lk_nonneg (c u : ℝ) : 0 ≤ lk c u :=
  Real.log_nonneg (by have : 0 ≤ c ^ 2 / u ^ 2 := by positivity
                      linarith)

@[simp] lemma lk_neg_right (c u : ℝ) : lk c (-u) = lk c u := by simp [lk]

@[simp] lemma lk_neg_left (c u : ℝ) : lk (-c) u = lk c u := by simp [lk]

@[simp] lemma lk_zero_left (u : ℝ) : lk 0 u = 0 := by simp [lk]

lemma lk_abs_right (c u : ℝ) : lk c |u| = lk c u := by simp [lk, sq_abs]

lemma lk_mono {c c' : ℝ} (h : |c| ≤ |c'|) (u : ℝ) : lk c u ≤ lk c' u := by
  unfold lk
  have h2 : c ^ 2 ≤ c' ^ 2 := sq_le_sq.2 h
  apply Real.log_le_log (by positivity)
  have : c ^ 2 / u ^ 2 ≤ c' ^ 2 / u ^ 2 := div_le_div_of_nonneg_right h2 (sq_nonneg u)
  linarith

lemma measurable_lk : Measurable (fun p : ℝ × ℝ => lk p.1 p.2) := by
  unfold lk; fun_prop

/-- For `u ≠ 0`, `lk c u = log (u² + c²) - log (u²)`. -/
lemma lk_eq_log_sub {u : ℝ} (hu : u ≠ 0) (c : ℝ) :
    lk c u = Real.log (u ^ 2 + c ^ 2) - Real.log (u ^ 2) := by
  have hu2 : 0 < u ^ 2 := by positivity
  unfold lk
  rw [← Real.log_div (by positivity) hu2.ne']
  congr 1
  field_simp

/-- `lk · u` is `1/|u|`-Lipschitz. -/
lemma lk_lip {u : ℝ} (hu : u ≠ 0) (b b' : ℝ) : |lk b u - lk b' u| ≤ |b - b'| / |u| := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hau : 0 < |u| := abs_pos.2 hu
  rw [lk_eq_log_sub hu, lk_eq_log_sub hu]
  have hderiv : ∀ c ∈ (univ : Set ℝ), HasDerivWithinAt (fun c => Real.log (u ^ 2 + c ^ 2))
      (2 * c / (u ^ 2 + c ^ 2)) univ c := by
    intro c _
    have h1 : HasDerivAt (fun c : ℝ => u ^ 2 + c ^ 2) (2 * c) c := by
      simpa using (hasDerivAt_pow 2 c).const_add (u ^ 2)
    have h2 := h1.log (by positivity)
    exact h2.hasDerivWithinAt
  have hbound : ∀ c ∈ (univ : Set ℝ), ‖2 * c / (u ^ 2 + c ^ 2)‖ ≤ 1 / |u| := by
    intro c _
    have hpos : 0 < u ^ 2 + c ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hau]
    have : |2 * c| * |u| = 2 * (|c| * |u|) := by rw [abs_mul]; norm_num; ring
    rw [this]
    nlinarith [sq_nonneg (|c| - |u|), sq_abs c, sq_abs u]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound convex_univ
    (mem_univ b') (mem_univ b)
  simp only [Real.norm_eq_abs] at this
  calc |Real.log (u ^ 2 + b ^ 2) - Real.log (u ^ 2) - (Real.log (u ^ 2 + b' ^ 2) - Real.log (u ^ 2))|
      = |Real.log (u ^ 2 + b ^ 2) - Real.log (u ^ 2 + b' ^ 2)| := by ring_nf
    _ ≤ 1 / |u| * |b - b'| := this
    _ = |b - b'| / |u| := by ring

/-- Antiderivative of `lk c` on `(0, ∞)` (for `a = |c| > 0`). -/
def lkPrim (c : ℝ) (u : ℝ) : ℝ :=
  u * Real.log (u ^ 2 + c ^ 2) - 2 * (u * Real.log u) + 2 * |c| * Real.arctan (u / |c|)

lemma continuous_lkPrim {c : ℝ} (hc : c ≠ 0) : Continuous (lkPrim c) := by
  have hc2 : ∀ u : ℝ, u ^ 2 + c ^ 2 ≠ 0 := fun u => by positivity
  unfold lkPrim
  refine Continuous.add (Continuous.sub ?_ ?_) ?_
  · exact continuous_id.mul (Continuous.log (by fun_prop) hc2)
  · exact continuous_const.mul Real.continuous_mul_log
  · fun_prop

lemma lkPrim_zero (c : ℝ) : lkPrim c 0 = 0 := by simp [lkPrim]

lemma hasDerivAt_lkPrim {c : ℝ} (hc : c ≠ 0) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (lkPrim c) (lk c u) u := by
  have hac : 0 < |c| := abs_pos.2 hc
  have hpos : 0 < u ^ 2 + c ^ 2 := by positivity
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2 + c ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (c ^ 2)
  have h2 : HasDerivAt (fun u : ℝ => u * Real.log (u ^ 2 + c ^ 2))
      (1 * Real.log (u ^ 2 + c ^ 2) + u * (2 * u / (u ^ 2 + c ^ 2))) u :=
    (hasDerivAt_id u).mul (h1.log hpos.ne')
  have h3 : HasDerivAt (fun u : ℝ => u * Real.log u) (1 * Real.log u + u * u⁻¹) u :=
    (hasDerivAt_id u).mul (Real.hasDerivAt_log hu.ne')
  have h4 : HasDerivAt (fun u : ℝ => Real.arctan (u / |c|))
      (1 / (1 + (u / |c|) ^ 2) * (1 / |c|)) u := by
    have := ((hasDerivAt_id u).div_const |c|).arctan
    simpa using this
  have h : HasDerivAt (lkPrim c) _ u := (h2.sub (h3.const_mul 2)).add (h4.const_mul (2 * |c|))
  refine h.congr_deriv ?_
  rw [lk_eq_log_sub hu.ne', Real.log_pow]
  have hc2 : |c| ^ 2 = c ^ 2 := sq_abs c
  field_simp
  rw [hc2]
  ring

lemma tendsto_lkPrim {c : ℝ} (hc : c ≠ 0) :
    Tendsto (lkPrim c) atTop (𝓝 (π * |c|)) := by
  have hac : 0 < |c| := abs_pos.2 hc
  -- `lkPrim c u = u * lk c u + 2|c| arctan (u/|c|)` for `u > 0`
  have heq : ∀ᶠ u in atTop, lkPrim c u = u * lk c u + 2 * |c| * Real.arctan (u / |c|) := by
    filter_upwards [eventually_gt_atTop 0] with u hu
    rw [lk_eq_log_sub hu.ne', Real.log_pow]
    unfold lkPrim
    push_cast
    ring
  have hA : Tendsto (fun u => u * lk c u) atTop (𝓝 0) := by
    have hup : ∀ᶠ u in atTop, u * lk c u ≤ c ^ 2 * u⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with u hu
      have hl : lk c u ≤ c ^ 2 / u ^ 2 := by
        unfold lk
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + c ^ 2 / u ^ 2 by positivity)
        linarith
      calc u * lk c u ≤ u * (c ^ 2 / u ^ 2) := mul_le_mul_of_nonneg_left hl hu.le
        _ = c ^ 2 * u⁻¹ := by field_simp
    have hlow : ∀ᶠ u in atTop, 0 ≤ u * lk c u := by
      filter_upwards [eventually_gt_atTop 0] with u hu
      exact mul_nonneg hu.le (lk_nonneg c u)
    have h0 : Tendsto (fun u : ℝ => c ^ 2 * u⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (c ^ 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 hlow hup
  have hB : Tendsto (fun u => 2 * |c| * Real.arctan (u / |c|)) atTop (𝓝 (2 * |c| * (π / 2))) := by
    have := (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (tendsto_id.atTop_div_const hac)
    exact this.const_mul (2 * |c|)
  have := hA.add hB
  rw [zero_add] at this
  refine (this.congr' (heq.mono fun u hu => hu.symm)).trans ?_
  apply le_of_eq; congr 1; ring

lemma integrableOn_lk_Ioi (c : ℝ) : IntegrableOn (lk c) (Ioi 0) := by
  by_cases hc : c = 0
  · subst hc
    have : lk 0 = fun _ => 0 := funext lk_zero_left
    rw [this]; exact integrableOn_zero
  · exact integrableOn_Ioi_deriv_of_nonneg (continuous_lkPrim hc).continuousWithinAt
      (fun u hu => hasDerivAt_lkPrim hc hu) (fun u _ => lk_nonneg c u) (tendsto_lkPrim hc)

lemma integral_lk_Ioi (c : ℝ) : ∫ u in Ioi (0 : ℝ), lk c u = π * |c| := by
  by_cases hc : c = 0
  · subst hc; simp
  · rw [integral_Ioi_of_hasDerivAt_of_nonneg (continuous_lkPrim hc).continuousWithinAt
      (fun u hu => hasDerivAt_lkPrim hc hu) (fun u _ => lk_nonneg c u) (tendsto_lkPrim hc),
      lkPrim_zero, sub_zero]

lemma integrable_lk (c : ℝ) : Integrable (lk c) := by
  have hIi : IntegrableOn (lk c) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, lk_neg_right, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_lk_Ioi c)
  have := hIi.union (integrableOn_lk_Ioi c)
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- `∫_ℝ log (1 + c²/u²) du = 2π|c|`. -/
lemma integral_lk (c : ℝ) : ∫ u, lk c u = 2 * π * |c| := by
  have h := integral_comp_abs (f := lk c)
  simp_rw [lk_abs_right] at h
  rw [h, integral_lk_Ioi]; ring


/-! ## 2. Segment combinations -/

lemma logCov_cons_left (p : ℝ × ℂ × ℂ) (c e : SegComb) :
    SegComb.logCov (p :: c) e =
      (e.map fun p' => p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2).sum +
        SegComb.logCov c e := by
  simp [SegComb.logCov]

lemma logCov_nil_left (e : SegComb) : SegComb.logCov [] e = 0 := by simp [SegComb.logCov]

lemma logCov_append_left (c d e : SegComb) :
    SegComb.logCov (c ++ d) e = SegComb.logCov c e + SegComb.logCov d e := by
  induction c with
  | nil => simp [logCov_nil_left]
  | cons p c ih => rw [List.cons_append, logCov_cons_left, logCov_cons_left, ih]; ring

lemma logCov_append_right (c d e : SegComb) :
    SegComb.logCov c (d ++ e) = SegComb.logCov c d + SegComb.logCov c e := by
  induction c with
  | nil => simp [logCov_nil_left]
  | cons p c ih =>
    rw [logCov_cons_left, logCov_cons_left, logCov_cons_left, ih, List.map_append,
      List.sum_append]
    ring

lemma list_sum_map_neg' {α : Type*} (l : List α) (F : α → ℝ) :
    (l.map fun a => -F a).sum = -(l.map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma logCov_neg_left (c e : SegComb) :
    SegComb.logCov (c.map fun p => (-p.1, p.2)) e = -SegComb.logCov c e := by
  induction c with
  | nil => simp [logCov_nil_left]
  | cons p c ih =>
    rw [List.map_cons, logCov_cons_left, logCov_cons_left, ih]
    simp only [neg_mul]
    rw [list_sum_map_neg']
    ring

lemma logCov_neg_right (c e : SegComb) :
    SegComb.logCov c (e.map fun p => (-p.1, p.2)) = -SegComb.logCov c e := by
  induction c with
  | nil => simp [logCov_nil_left]
  | cons p c ih =>
    rw [logCov_cons_left, logCov_cons_left, ih, List.map_map]
    have : (e.map ((fun p' : ℝ × ℂ × ℂ => p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2) ∘
        fun p : ℝ × ℂ × ℂ => (-p.1, p.2))).sum =
        -(e.map fun p' => p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2).sum := by
      rw [← list_sum_map_neg']
      congr 1
      refine List.map_congr_left (fun p' _ => ?_)
      simp only [Function.comp]
      ring
    rw [this]; ring

/-- Bilinearity of `logCov` on differences. -/
lemma logCov_sub_sub (c d c' d' : SegComb) :
    (c.sub d).logCov (c'.sub d') =
      c.logCov c' - c.logCov d' - d.logCov c' + d.logCov d' := by
  unfold SegComb.sub
  rw [logCov_append_left, logCov_append_right, logCov_append_right, logCov_neg_left,
    logCov_neg_left, logCov_neg_right, logCov_neg_right]
  ring

lemma list_sum_map_range (n : ℕ) (F : ℕ → ℝ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The segment combination of a curve `P` on the mesh `i/M`: the edges
`[P(i/M), P((i+1)/M)]`, `i < M`, with weight `1/M` each. -/
def pc (M : ℕ) (P : ℝ → ℂ) : SegComb :=
  (List.range M).map fun i : ℕ => ((1 : ℝ) / M, P ((i : ℝ) / M), P (((i : ℝ) + 1) / M))

lemma logCov_pc (M M' : ℕ) (P Q : ℝ → ℂ) :
    (pc M P).logCov (pc M' Q) = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M',
      (1 / (M : ℝ)) * (1 / (M' : ℝ)) * segLogPair (P ((i : ℝ) / M)) (P (((i : ℝ) + 1) / M))
        (Q ((j : ℝ) / M')) (Q (((j : ℝ) + 1) / M')) := by
  unfold SegComb.logCov pc
  rw [List.map_map, list_sum_map_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Function.comp, List.map_map]
  rw [list_sum_map_range]
  rfl

/-- The graph point `x + i δ f(x)`. -/
def gc (δ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℂ := (x : ℂ) + ((δ * f x : ℝ) : ℂ) * Complex.I

lemma edges_map_range (v : ℕ → ℂ) (M : ℕ) :
      edges ((List.range (M + 1)).map v) = (List.range M).map fun i : ℕ => (v i, v (i + 1)) := by
  unfold edges
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

lemma range_cast_eq (n : ℕ) :
    (do let a ← List.range n; pure (a : ℝ) : List ℝ) = (List.range n).map (fun a : ℕ => (a : ℝ)) := by
  rw [List.bind_eq_flatMap]; exact List.flatMap_pure_eq_map _ _

lemma graphVerts_eq (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) :
    graphVerts M δ f = (List.range (M + 1)).map fun i : ℕ => gc δ f ((i : ℝ) / M) := by
  unfold graphVerts gc
  rw [range_cast_eq, List.map_map]
  refine List.map_congr_left (fun i _ => ?_)
  simp only [Function.comp]
  push_cast
  ring

lemma graphComb_eq (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) : graphComb M δ f = pc M (gc δ f) := by
  unfold graphComb pc
  rw [graphVerts_eq, edges_map_range, List.map_map]
  refine List.map_congr_left (fun i _ => ?_)
  simp only [Function.comp, Nat.cast_add, Nat.cast_one]


/-! ## 3. From segment sums to double integrals -/

/-- `P` is affine on each mesh interval `[i/M, (i+1)/M]`, `i < M`. -/
def MeshAff (M : ℕ) (P : ℝ → ℂ) : Prop :=
  ∀ i : ℕ, i < M → ∀ s ∈ Icc (0 : ℝ) 1,
    P (((i : ℝ) + s) / M) = P ((i : ℝ) / M) + (s : ℂ) * (P (((i : ℝ) + 1) / M) - P ((i : ℝ) / M))

lemma segLogPair_meshAff {M M' : ℕ} {P Q : ℝ → ℂ} (hP : MeshAff M P) (hQ : MeshAff M' Q)
    {i j : ℕ} (hi : i < M) (hj : j < M') :
    segLogPair (P ((i : ℝ) / M)) (P (((i : ℝ) + 1) / M)) (Q ((j : ℝ) / M'))
        (Q (((j : ℝ) + 1) / M')) =
      ∫ s in (0:ℝ)..1, ∫ s' in (0:ℝ)..1,
        -Real.log ‖P (((i : ℝ) + s) / M) - Q (((j : ℝ) + s') / M')‖ := by
  unfold segLogPair
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  refine intervalIntegral.integral_congr (fun s' hs' => ?_)
  rw [uIcc_of_le zero_le_one] at hs hs'
  rw [hP i hi s hs, hQ j hj s' hs']

/-- One mesh interval: `(1/M) ∫₀¹ g((i+s)/M) ds = ∫_{i/M}^{(i+1)/M} g`. -/
lemma piece_integral {M : ℕ} (hM : 0 < M) (g : ℝ → ℝ) (i : ℕ) :
    (1 / (M : ℝ)) * ∫ s in (0:ℝ)..1, g (((i : ℝ) + s) / M) =
      ∫ x in (i : ℝ) / M..((i : ℝ) + 1) / M, g x := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have h1 : (fun s : ℝ => g (((i : ℝ) + s) / M)) = fun s => g (s / M + (i : ℝ) / M) := by
    funext s; congr 1; ring
  rw [h1, intervalIntegral.integral_comp_div_add _ hM', smul_eq_mul, ← mul_assoc,
    one_div_mul_cancel hM', one_mul]
  congr 1 <;> ring

lemma piece_subset {M : ℕ} (hM : 0 < M) {k : ℕ} (hk : k < M) :
    uIcc ((k : ℝ) / M) (((k : ℝ) + 1) / M) ⊆ uIcc 0 1 := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hk' : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
  rw [uIcc_of_le zero_le_one, uIcc_of_le (by gcongr; linarith)]
  refine Icc_subset_Icc (by positivity) ?_
  rw [div_le_one hM']; exact hk'

lemma sum_pieces {M : ℕ} (hM : 0 < M) (g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 1) :
    ∑ i ∈ Finset.range M, ∫ x in (i : ℝ) / M..((i : ℝ) + 1) / M, g x = ∫ x in (0:ℝ)..1, g x := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have key := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) / M) (n := M) (fun k hk => by
      show IntervalIntegrable g volume ((k : ℝ) / M) (((k + 1 : ℕ) : ℝ) / M)
      push_cast
      exact hg.mono_set (piece_subset hM hk))
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hM'.ne'] at key
  exact key

lemma ae_ne_real (c : ℝ) : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ c :=
  (measure_eq_zero_iff_ae_notMem.1 (measure_singleton c)).mono fun _ hy => hy

lemma intervalIntegrable_abs_log_sub (c : ℝ) :
    IntervalIntegrable (fun y => |Real.log (y - c)|) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 0 - c) (b := 1 - c)).comp_sub_right c
  simp only [sub_add_cancel] at h
  exact h.abs

lemma integral_abs_log_sub_le {c K : ℝ} (hc : |c| ≤ K) :
    ∫ y in (0:ℝ)..1, |Real.log (y - c)| ≤ ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  rw [intervalIntegral.integral_comp_sub_right (fun u => |Real.log u|) c]
  have := abs_le.1 hc
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    (ae_of_all _ fun _ => abs_nonneg _) intervalIntegral.intervalIntegrable_log'.abs

/-- Domination hypotheses for a kernel `h` on `[0,1]²`: measurable, and for `x ∈ [0,1]` bounded
on `[0,1]` by `C + |log (y - c)|` away from one point `c` with `|c| ≤ K`. -/
structure LogDom (h : ℝ → ℝ → ℝ) : Prop where
  meas : Measurable (Function.uncurry h)
  bound : ∃ C K : ℝ, ∀ x ∈ Icc (0:ℝ) 1, ∃ c : ℝ, |c| ≤ K ∧
    ∀ y ∈ Icc (0:ℝ) 1, y ≠ c → |h x y| ≤ C + |Real.log (y - c)|

namespace LogDom

variable {h : ℝ → ℝ → ℝ}

lemma measurable_section (hd : LogDom h) (x : ℝ) : Measurable (h x) :=
  hd.meas.comp measurable_prodMk_left

lemma ii (hd : LogDom h) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : IntervalIntegrable (h x) volume 0 1 := by
  obtain ⟨C, K, hb⟩ := hd.bound
  obtain ⟨c, -, hc⟩ := hb x hx
  refine IntervalIntegrable.mono_fun' ((intervalIntegrable_const (c := C)).add
    (intervalIntegrable_abs_log_sub c)) (hd.measurable_section x).aestronglyMeasurable ?_
  rw [uIoc_of_le zero_le_one]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (ae_ne_real c)] with y hy hne
  exact hc y (Ioc_subset_Icc_self hy) hne

lemma integral_abs_le (hd : LogDom h) : ∃ C' : ℝ, ∀ x ∈ Icc (0:ℝ) 1,
    ∫ y in (0:ℝ)..1, |h x y| ≤ C' := by
  obtain ⟨C, K, hb⟩ := hd.bound
  refine ⟨C + ∫ u in (-(K + 1))..(K + 1), |Real.log u|, fun x hx => ?_⟩
  obtain ⟨c, hcK, hc⟩ := hb x hx
  have h1 : ∫ y in (0:ℝ)..1, |h x y| ≤ ∫ y in (0:ℝ)..1, (C + |Real.log (y - c)|) := by
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one (hd.ii hx).abs
      (intervalIntegrable_const.add (intervalIntegrable_abs_log_sub c)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (ae_ne_real c)]
      with y hy hne
    exact hc y hy hne
  rw [intervalIntegral.integral_add intervalIntegrable_const (intervalIntegrable_abs_log_sub c),
    intervalIntegral.integral_const] at h1
  have h2 := integral_abs_log_sub_le hcK
  simp only [sub_zero, smul_eq_mul, one_mul] at h1
  linarith

lemma ii_integral (hd : LogDom h) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun x => ∫ y in a..b, h x y) volume 0 1 := by
  obtain ⟨C', hC'⟩ := hd.integral_abs_le
  have hmeas : StronglyMeasurable (fun x => ∫ y in a..b, h x y) := by
    have := hd.meas.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc a b))
    simp only [Function.uncurry_apply_pair] at this
    convert this using 2 with x
    rw [intervalIntegral.integral_of_le hab]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := C') (by simp) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx' := Ioc_subset_Icc_self hx
  rw [Real.norm_eq_abs]
  calc |∫ y in a..b, h x y| ≤ ∫ y in a..b, |h x y| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ y in (0:ℝ)..1, |h x y| :=
        intervalIntegral.integral_mono_interval ha hab hb (ae_of_all _ fun _ => abs_nonneg _)
          (hd.ii hx').abs
    _ ≤ C' := hC' x hx'

end LogDom

/-- The double sum over mesh squares equals the double integral. -/
lemma double_sum_eq {M M' : ℕ} (hM : 0 < M) (hM' : 0 < M') {h : ℝ → ℝ → ℝ} (hd : LogDom h) :
    ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M', (1 / (M : ℝ)) * (1 / (M' : ℝ)) *
      ∫ s in (0:ℝ)..1, ∫ s' in (0:ℝ)..1, h (((i : ℝ) + s) / M) (((j : ℝ) + s') / M') =
    ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, h x y := by
  have hM'r : (0:ℝ) < M' := by exact_mod_cast hM'
  set k : ℕ → ℝ → ℝ := fun j x => ∫ y in (j : ℝ) / M'..((j : ℝ) + 1) / M', h x y with hk
  have hkint : ∀ j ∈ Finset.range M', IntervalIntegrable (k j) volume 0 1 := by
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ M' := by exact_mod_cast Finset.mem_range.1 hj
    exact hd.ii_integral (by positivity) (by gcongr; linarith)
      (by rw [div_le_one hM'r]; exact hj')
  -- step 1: each term is a mesh-interval integral of `k j`
  have step1 : ∀ i j : ℕ, (1 / (M : ℝ)) * (1 / (M' : ℝ)) *
      ∫ s in (0:ℝ)..1, ∫ s' in (0:ℝ)..1, h (((i : ℝ) + s) / M) (((j : ℝ) + s') / M') =
      ∫ x in (i : ℝ) / M..((i : ℝ) + 1) / M, k j x := by
    intro i j
    rw [← piece_integral hM (k j) i, mul_assoc, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    exact piece_integral hM' (h (((i : ℝ) + s) / M)) j
  simp_rw [step1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j hj => sum_pieces hM (k j) (hkint j hj))]
  rw [← intervalIntegral.integral_finsetSum hkint]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [uIcc_of_le zero_le_one] at hx
  exact sum_pieces hM' (h x) (hd.ii hx)

/-- **Segment sums of mesh-affine curves as double integrals.** -/
theorem logCov_pc_eq {M M' : ℕ} (hM : 0 < M) (hM' : 0 < M') {P Q : ℝ → ℂ}
    (hP : MeshAff M P) (hQ : MeshAff M' Q) (hd : LogDom fun x y => -Real.log ‖P x - Q y‖) :
    (pc M P).logCov (pc M' Q) = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, -Real.log ‖P x - Q y‖ := by
  rw [logCov_pc, ← double_sum_eq hM hM' hd]
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
  rw [segLogPair_meshAff hP hQ (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)]

lemma abs_log_le_of_bounds {D κ t Cu : ℝ} (hκ : 0 < κ) (ht : t ≠ 0) (hlow : κ * |t| ≤ D)
    (hup : D ≤ Cu) : |Real.log D| ≤ |Cu| + |Real.log κ| + |Real.log t| := by
  have hm : 0 < κ * |t| := mul_pos hκ (abs_pos.2 ht)
  have hD : 0 < D := lt_of_lt_of_le hm hlow
  have h1' := abs_nonneg (Real.log κ)
  have h2' := abs_nonneg (Real.log t)
  rcases le_or_gt 1 D with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_sub_one_of_pos hD
    have := le_abs_self Cu
    linarith
  · rw [abs_of_neg (Real.log_neg hD h1)]
    have hlog := Real.log_le_log hm hlow
    rw [Real.log_mul hκ.ne' (abs_pos.2 ht).ne', Real.log_abs] at hlog
    have := neg_abs_le (Real.log κ)
    have := neg_abs_le (Real.log t)
    have := abs_nonneg Cu
    linarith

/-- Domination for the log kernel between two continuous curves whose distance is bounded below
by `κ |y - c(x)|` (a transversality condition) and above by `Cu` on `[0,1]²`. -/
lemma logDom_curve {P Q : ℝ → ℂ} (hP : Continuous P) (hQ : Continuous Q) {κ Cu K : ℝ}
    (hκ : 0 < κ) (c : ℝ → ℝ) (hcK : ∀ x ∈ Icc (0:ℝ) 1, |c x| ≤ K)
    (hlow : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, κ * |y - c x| ≤ ‖P x - Q y‖)
    (hup : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, ‖P x - Q y‖ ≤ Cu) :
    LogDom (fun x y => -Real.log ‖P x - Q y‖) where
  meas := by
    have : Continuous (fun p : ℝ × ℝ => ‖P p.1 - Q p.2‖) := by fun_prop
    exact this.measurable.log.neg
  bound := ⟨|Cu| + |Real.log κ|, K, fun x hx => ⟨c x, hcK x hx, fun y hy hne => by
    rw [abs_neg]
    exact abs_log_le_of_bounds hκ (sub_ne_zero.2 hne) (hlow x hx y hy) (hup x hx y hy)⟩⟩

/-- **The four-term covariance as a double integral.** -/
theorem logCov_four {M₁ M₂ M₃ M₄ : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) (h₄ : 0 < M₄)
    {P₁ P₂ P₃ P₄ : ℝ → ℂ} (m₁ : MeshAff M₁ P₁) (m₂ : MeshAff M₂ P₂) (m₃ : MeshAff M₃ P₃)
    (m₄ : MeshAff M₄ P₄)
    (d₁₃ : LogDom fun x y => -Real.log ‖P₁ x - P₃ y‖)
    (d₁₄ : LogDom fun x y => -Real.log ‖P₁ x - P₄ y‖)
    (d₂₃ : LogDom fun x y => -Real.log ‖P₂ x - P₃ y‖)
    (d₂₄ : LogDom fun x y => -Real.log ‖P₂ x - P₄ y‖) :
    ((pc M₁ P₁).sub (pc M₂ P₂)).logCov ((pc M₃ P₃).sub (pc M₄ P₄)) =
      ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (-Real.log ‖P₁ x - P₃ y‖ + Real.log ‖P₁ x - P₄ y‖ +
        Real.log ‖P₂ x - P₃ y‖ - Real.log ‖P₂ x - P₄ y‖) := by
  rw [logCov_sub_sub, logCov_pc_eq h₁ h₃ m₁ m₃ d₁₃, logCov_pc_eq h₁ h₄ m₁ m₄ d₁₄,
    logCov_pc_eq h₂ h₃ m₂ m₃ d₂₃, logCov_pc_eq h₂ h₄ m₂ m₄ d₂₄]
  have i₁₃ := d₁₃.ii_integral le_rfl zero_le_one le_rfl
  have i₁₄ := d₁₄.ii_integral le_rfl zero_le_one le_rfl
  have i₂₃ := d₂₃.ii_integral le_rfl zero_le_one le_rfl
  have i₂₄ := d₂₄.ii_integral le_rfl zero_le_one le_rfl
  rw [← intervalIntegral.integral_sub i₁₃ i₁₄, ← intervalIntegral.integral_sub (i₁₃.sub i₁₄) i₂₃,
    ← intervalIntegral.integral_add ((i₁₃.sub i₁₄).sub i₂₃) i₂₄]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [uIcc_of_le zero_le_one] at hx
  have j₁₃ := d₁₃.ii hx
  have j₁₄ := d₁₄.ii hx
  have j₂₃ := d₂₃.ii hx
  have j₂₄ := d₂₄.ii hx
  rw [← intervalIntegral.integral_sub j₁₃ j₁₄, ← intervalIntegral.integral_sub (j₁₃.sub j₁₄) j₂₃,
    ← intervalIntegral.integral_add ((j₁₃.sub j₁₄).sub j₂₃) j₂₄]
  congr 1; funext y; ring


/-! ## 4. Curves `A(x) + i δ F(x)` and the substitution -/

/-- The curve `x ↦ A(x) + i δ F(x)`. -/
def dc (A : ℝ → ℝ) (δ : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℂ :=
  ((A x : ℝ) : ℂ) + ((δ * F x : ℝ) : ℂ) * Complex.I

lemma gc_eq_dc (δ : ℝ) (f : ℝ → ℝ) : gc δ f = dc id δ f := rfl

lemma dc_sub (A A' : ℝ → ℝ) (δ : ℝ) (F G : ℝ → ℝ) (x y : ℝ) :
    dc A δ F x - dc A' δ G y = ((A x - A' y : ℝ) : ℂ) + ((δ * (F x - G y) : ℝ) : ℂ) * Complex.I := by
  unfold dc; push_cast; ring

lemma continuous_dc {A F : ℝ → ℝ} (hA : Continuous A) (hF : Continuous F) (δ : ℝ) :
    Continuous (dc A δ F) := by
  unfold dc; fun_prop

/-- Log-domination for a pair of `dc` curves, the second with affine real part. -/
lemma logDom_dc {A A' : ℝ → ℝ} (hA : Continuous A) {α' β' δ : ℝ} (hα : 0 < α')
    (hA' : ∀ y, A' y = α' * y + β') {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) {KA B : ℝ} (hAb : ∀ x ∈ Icc (0:ℝ) 1, |A x| ≤ KA)
    (hFB : ∀ x ∈ Icc (0:ℝ) 1, |F x| ≤ B) (hGB : ∀ x ∈ Icc (0:ℝ) 1, |G x| ≤ B) :
    LogDom (fun x y => -Real.log ‖dc A δ F x - dc A' δ G y‖) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hFB 0 ⟨le_rfl, zero_le_one⟩)
  have hA'c : Continuous A' := by
    have : A' = fun y => α' * y + β' := funext hA'
    rw [this]; fun_prop
  refine logDom_curve (continuous_dc hA hF δ) (continuous_dc hA'c hG δ) hα
    (fun x => (A x - β') / α') (K := (KA + |β'|) / α') (Cu := KA + α' + |β'| + |δ| * (2 * B))
    ?_ ?_ ?_
  · intro x hx
    rw [abs_div, abs_of_pos hα]
    gcongr
    calc |A x - β'| ≤ |A x| + |β'| := abs_sub _ _
      _ ≤ KA + |β'| := by linarith [hAb x hx]
  · intro x _ y _
    rw [dc_sub]
    refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
    have hre : ((((A x - A' y) : ℝ) : ℂ) + ((δ * (F x - G y) : ℝ) : ℂ) * Complex.I).re =
        A x - A' y := by simp
    rw [hre, hA']
    have : A x - (α' * y + β') = -(α' * (y - (A x - β') / α')) := by field_simp; ring
    rw [this, abs_neg, abs_mul, abs_of_pos hα]
  · intro x hx y hy
    rw [dc_sub]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : ((((A x - A' y) : ℝ) : ℂ) + ((δ * (F x - G y) : ℝ) : ℂ) * Complex.I).re =
        A x - A' y := by simp
    have him : ((((A x - A' y) : ℝ) : ℂ) + ((δ * (F x - G y) : ℝ) : ℂ) * Complex.I).im =
        δ * (F x - G y) := by simp
    rw [hre, him, hA']
    have h1 : |A x - (α' * y + β')| ≤ KA + α' + |β'| := by
      have := hAb x hx
      have hy' : |α' * y| ≤ α' := by
        rw [abs_mul, abs_of_pos hα, abs_of_nonneg hy.1]; nlinarith [hy.2]
      calc |A x - (α' * y + β')| ≤ |A x| + |α' * y + β'| := abs_sub _ _
        _ ≤ |A x| + (|α' * y| + |β'|) := by gcongr; exact abs_add_le _ _
        _ ≤ KA + α' + |β'| := by linarith
    have h2 : |δ * (F x - G y)| ≤ |δ| * (2 * B) := by
      rw [abs_mul]
      gcongr
      calc |F x - G y| ≤ |F x| + |G y| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hFB x hx, hGB y hy]
    linarith

lemma neglog_norm_eq {δ w t : ℝ} (hδ : 0 < δ) (hw : w ≠ 0) :
    -Real.log ‖(((-(δ * w)) : ℝ) : ℂ) + ((δ * t : ℝ) : ℂ) * Complex.I‖ =
      -Real.log δ - Real.log |w| - lk t w / 2 := by
  rw [Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]
  have hw2 : 0 < w ^ 2 := by positivity
  have e : (-(δ * w)) ^ 2 + (δ * t) ^ 2 = δ ^ 2 * w ^ 2 * (1 + t ^ 2 / w ^ 2) := by
    field_simp
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_abs]
  unfold lk
  push_cast
  ring

/-- Signed kernel `Σ σ_k lk (v k) w`. -/
def Kf {κ : Type*} [Fintype κ] (σ : κ → ℝ) (w : ℝ) (v : κ → ℝ) : ℝ := ∑ k, σ k * lk (v k) w

/-- Signs of the four-term combination `(1 - 2) ⊗ (3 - 4)`. -/
def σ4 : Fin 4 → ℝ := ![-1 / 2, 1 / 2, 1 / 2, -1 / 2]

/-- The four profile differences `(u₁ - v₃, u₁ - v₄, u₂ - v₃, u₂ - v₄)`. -/
def bvec (u₁ u₂ v₃ v₄ : ℝ) : Fin 4 → ℝ := ![u₁ - v₃, u₁ - v₄, u₂ - v₃, u₂ - v₄]

lemma Kf_σ4 (w u₁ u₂ v₃ v₄ : ℝ) :
    Kf σ4 w (bvec u₁ u₂ v₃ v₄) = -lk (u₁ - v₃) w / 2 + lk (u₁ - v₄) w / 2 +
      lk (u₂ - v₃) w / 2 - lk (u₂ - v₄) w / 2 := by
  simp [Kf, σ4, bvec, Fin.sum_univ_four]
  ring

/-- **The substitution.**  For fixed `x`, with the second pair of curves having affine real part
`A' y = α' y + β'`, the inner integral of the four-term log kernel becomes `(δ/α') ∫ Kf` over
`w ∈ [(β' - A x)/δ, (α' + β' - A x)/δ]`, with `y = (δ/α') w + (A x - β')/α'`. -/
lemma inner_subst {δ α' β' : ℝ} (hδ : 0 < δ) (hα : 0 < α') (A A' : ℝ → ℝ)
    (hA' : ∀ y, A' y = α' * y + β') (F₁ F₂ F₃ F₄ : ℝ → ℝ) (x : ℝ) :
    ∫ y in (0:ℝ)..1, (-Real.log ‖dc A δ F₁ x - dc A' δ F₃ y‖ +
        Real.log ‖dc A δ F₁ x - dc A' δ F₄ y‖ +
        Real.log ‖dc A δ F₂ x - dc A' δ F₃ y‖ -
        Real.log ‖dc A δ F₂ x - dc A' δ F₄ y‖) =
      (δ / α') * ∫ w in ((β' - A x) / δ)..((α' + β' - A x) / δ),
        Kf σ4 w (bvec (F₁ x) (F₂ x) (F₃ ((δ / α') * w + (A x - β') / α'))
          (F₄ ((δ / α') * w + (A x - β') / α'))) := by
  set c := δ / α' with hc
  set d := (A x - β') / α' with hd
  have hc0 : c ≠ 0 := by positivity
  set Φ : ℝ → ℝ := fun y => -Real.log ‖dc A δ F₁ x - dc A' δ F₃ y‖ +
        Real.log ‖dc A δ F₁ x - dc A' δ F₄ y‖ +
        Real.log ‖dc A δ F₂ x - dc A' δ F₃ y‖ -
        Real.log ‖dc A δ F₂ x - dc A' δ F₄ y‖ with hΦ
  have e0 : c * ((β' - A x) / δ) + d = 0 := by rw [hc, hd]; field_simp; ring
  have e1 : c * ((α' + β' - A x) / δ) + d = 1 := by rw [hc, hd]; field_simp; ring
  have key : ∫ w in ((β' - A x) / δ)..((α' + β' - A x) / δ), Φ (c * w + d) =
      c⁻¹ * ∫ y in (0:ℝ)..1, Φ y := by
    rw [intervalIntegral.integral_comp_mul_add Φ hc0 d, e0, e1, smul_eq_mul]
  calc ∫ y in (0:ℝ)..1, Φ y = c * ∫ w in ((β' - A x) / δ)..((α' + β' - A x) / δ), Φ (c * w + d) := by
        rw [key]; field_simp
    _ = _ := by
      congr 1
      refine intervalIntegral.integral_congr_ae ((ae_ne_real 0).mono fun w hw _ => ?_)
      have hre : ∀ F G : ℝ → ℝ, dc A δ F x - dc A' δ G (c * w + d) =
          (((-(δ * w)) : ℝ) : ℂ) + ((δ * (F x - G (c * w + d)) : ℝ) : ℂ) * Complex.I := by
        intro F G
        rw [dc_sub, hA']
        congr 3
        rw [hc, hd]; field_simp; ring
      have hL : ∀ t : ℝ, Real.log ‖(((-(δ * w)) : ℝ) : ℂ) + ((δ * t : ℝ) : ℂ) * Complex.I‖ =
          Real.log δ + Real.log |w| + lk t w / 2 := by
        intro t; have := neglog_norm_eq hδ hw (t := t); linarith
      simp only [hΦ, hre, hL, Kf_σ4]
      ring

/-! ## 5. Dominated convergence -/

lemma abs_Kf_le {κ : Type*} [Fintype κ] (σ : κ → ℝ) (w : ℝ) (v : κ → ℝ) {B : ℝ}
    (hv : ∀ k, |v k| ≤ B) : |Kf σ w v| ≤ (∑ k, |σ k|) * lk B w := by
  unfold Kf
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (lk_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left (lk_mono ((hv k).trans (le_abs_self B)) w) (abs_nonneg _)

lemma abs_Kf_sub_le {κ : Type*} [Fintype κ] (σ : κ → ℝ) {w : ℝ} (hw : w ≠ 0) (v v' : κ → ℝ) :
    |Kf σ w v - Kf σ w v'| ≤ ∑ k, |σ k| * (|v k - v' k| / |w|) := by
  unfold Kf
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (lk_lip hw _ _) (abs_nonneg _)

lemma measurable_Kf {κ : Type*} [Fintype κ] (σ : κ → ℝ) {α : Type*} [MeasurableSpace α]
    {W : α → ℝ} {V : α → κ → ℝ} (hW : Measurable W) (hV : ∀ k, Measurable fun a => V a k) :
    Measurable fun a => Kf σ (W a) (V a) := by
  unfold Kf
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (measurable_lk.comp ((hV k).prodMk hW)).const_mul _

lemma integrable_Kf {κ : Type*} [Fintype κ] (σ : κ → ℝ) (v : κ → ℝ) :
    Integrable (fun w => Kf σ w v) := by
  unfold Kf
  exact integrable_finsetSum _ fun k _ => (integrable_lk _).const_mul _

lemma integral_Kf {κ : Type*} [Fintype κ] (σ : κ → ℝ) (v : κ → ℝ) :
    ∫ w, Kf σ w v = 2 * π * ∑ k, σ k * |v k| := by
  unfold Kf
  rw [integral_finsetSum _ fun k _ => (integrable_lk _).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_lk]
  ring

lemma ae_fst_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.1 ≠ c :=
  Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_ne_real c)

lemma ae_snd_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.2 ≠ c :=
  Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_ne_real c)

/-- **Dominated convergence for the substituted kernel**, along any countably generated filter.
If the profile differences `b i x w` stay bounded, converge (for fixed `x ∈ (0,1)` and `w`) to
`b0 i x` uniformly in the sense `b - b0 → 0`, and the `w`-range `[w0, w1]` exhausts `ℝ`, then
`∫₀¹ (∫_{w0}^{w1} Kf σ w (b i x w) dw - 2π Σ σ_k |b0 i x k|) dx → 0`. -/
theorem core_tendsto {ι κ : Type*} [Fintype κ] {l : Filter ι} [l.IsCountablyGenerated]
    (σ : κ → ℝ) (B : ℝ) (b : ι → ℝ → ℝ → κ → ℝ) (b0 : ι → ℝ → κ → ℝ) (w0 w1 : ι → ℝ → ℝ)
    (hmeas : ∀ᶠ i in l, (∀ k, Measurable (fun p : ℝ × ℝ => b i p.1 p.2 k)) ∧
      (∀ k, Measurable (fun x => b0 i x k)) ∧ Measurable (w0 i) ∧ Measurable (w1 i))
    (hle : ∀ᶠ i in l, ∀ x ∈ Icc (0:ℝ) 1, w0 i x ≤ w1 i x)
    (hbB : ∀ᶠ i in l, ∀ x ∈ Icc (0:ℝ) 1,
      (∀ w ∈ Icc (w0 i x) (w1 i x), ∀ k, |b i x w k| ≤ B) ∧ ∀ k, |b0 i x k| ≤ B)
    (hconv : ∀ x ∈ Ioo (0:ℝ) 1, ∀ w k, Tendsto (fun i => b i x w k - b0 i x k) l (𝓝 0))
    (hw0 : ∀ x ∈ Ioo (0:ℝ) 1, Tendsto (fun i => w0 i x) l atBot)
    (hw1 : ∀ x ∈ Ioo (0:ℝ) 1, Tendsto (fun i => w1 i x) l atTop) :
    (∀ᶠ i in l, IntervalIntegrable (fun x => (∫ w in (w0 i x)..(w1 i x), Kf σ w (b i x w)) -
      2 * π * ∑ k, σ k * |b0 i x k|) volume 0 1) ∧
    Tendsto (fun i => ∫ x in (0:ℝ)..1, ((∫ w in (w0 i x)..(w1 i x), Kf σ w (b i x w)) -
      2 * π * ∑ k, σ k * |b0 i x k|)) l (𝓝 0) := by
  classical
  set S : ℝ := ∑ k, |σ k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg _
  -- the integrand on the plane
  set G : ι → ℝ × ℝ → ℝ := fun i p => if p.1 ∈ Icc (0:ℝ) 1 then
      ((if w0 i p.1 ≤ p.2 ∧ p.2 ≤ w1 i p.1 then Kf σ p.2 (b i p.1 p.2) else 0) -
        Kf σ p.2 (b0 i p.1)) else 0 with hG
  set bound : ℝ × ℝ → ℝ := fun p =>
    (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) p.1 * (2 * S * lk B p.2) with hbound
  have hbound_int : Integrable bound (volume.prod volume) := by
    refine Integrable.mul_prod ?_ ((integrable_lk B).const_mul _)
    exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hGmeas : ∀ᶠ i in l, Measurable (G i) := by
    filter_upwards [hmeas] with i hi
    obtain ⟨hb, hb0, hw0m, hw1m⟩ := hi
    refine Measurable.ite (measurableSet_Icc.preimage measurable_fst) ?_ measurable_const
    refine Measurable.sub (Measurable.ite ?_ ?_ measurable_const) ?_
    · exact (measurableSet_le (hw0m.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hw1m.comp measurable_fst))
    · exact measurable_Kf σ measurable_snd hb
    · exact measurable_Kf σ measurable_snd (fun k => (hb0 k).comp measurable_fst)
  have hGbound : ∀ᶠ i in l, ∀ p, ‖G i p‖ ≤ bound p := by
    filter_upwards [hbB] with i hi
    intro p
    by_cases hp : p.1 ∈ Icc (0:ℝ) 1
    · have h1 : |Kf σ p.2 (b0 i p.1)| ≤ S * lk B p.2 :=
        abs_Kf_le σ _ _ (fun k => (hi p.1 hp).2 k)
      have h2 : |(if w0 i p.1 ≤ p.2 ∧ p.2 ≤ w1 i p.1 then Kf σ p.2 (b i p.1 p.2) else 0)| ≤
          S * lk B p.2 := by
        split_ifs with hw
        · exact abs_Kf_le σ _ _ (fun k => (hi p.1 hp).1 p.2 ⟨hw.1, hw.2⟩ k)
        · rw [abs_zero]; exact mul_nonneg hS0 (lk_nonneg _ _)
      have hGp : G i p = (if w0 i p.1 ≤ p.2 ∧ p.2 ≤ w1 i p.1 then Kf σ p.2 (b i p.1 p.2) else 0) -
          Kf σ p.2 (b0 i p.1) := by
        simp only [hG]; rw [if_pos hp]
      have hbp : bound p = 2 * S * lk B p.2 := by
        simp only [hbound]; rw [Set.indicator_of_mem hp, one_mul]
      rw [hGp, hbp, Real.norm_eq_abs]
      have h3 := abs_sub (if w0 i p.1 ≤ p.2 ∧ p.2 ≤ w1 i p.1 then Kf σ p.2 (b i p.1 p.2) else 0)
        (Kf σ p.2 (b0 i p.1))
      linarith
    · have hGp : G i p = 0 := by simp only [hG]; rw [if_neg hp]
      have hbp : bound p = 0 := by
        simp only [hbound]; rw [Set.indicator_of_notMem hp, zero_mul]
      rw [hGp, hbp, norm_zero]
  have hlim : ∀ᵐ p ∂(volume.prod volume), Tendsto (fun i => G i p) l (𝓝 0) := by
    filter_upwards [ae_fst_ne 0, ae_fst_ne 1, ae_snd_ne 0] with p hp0 hp1 hp2
    by_cases hp : p.1 ∈ Icc (0:ℝ) 1
    · have hpo : p.1 ∈ Ioo (0:ℝ) 1 :=
        ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
      have hev : (fun i => Kf σ p.2 (b i p.1 p.2) - Kf σ p.2 (b0 i p.1)) =ᶠ[l]
          fun i => G i p := by
        filter_upwards [(hw0 p.1 hpo).eventually (eventually_le_atBot p.2),
          (hw1 p.1 hpo).eventually (eventually_ge_atTop p.2)] with i h0 h1
        simp only [hG]; rw [if_pos hp, if_pos ⟨h0, h1⟩]
      refine Tendsto.congr' hev ?_
      have hsum : Tendsto (fun i => ∑ k, |σ k| * (|b i p.1 p.2 k - b0 i p.1 k| / |p.2|)) l
          (𝓝 0) := by
        have := tendsto_finsetSum (Finset.univ : Finset κ)
          (fun k _ => (((hconv p.1 hpo p.2 k).abs).div_const |p.2|).const_mul |σ k|)
        simpa using this
      exact squeeze_zero_norm (fun i => by rw [Real.norm_eq_abs]; exact abs_Kf_sub_le σ hp2 _ _)
        hsum
    · simp only [hG]; simp only [if_neg hp]; exact tendsto_const_nhds
  have hDCT := tendsto_integral_filter_of_dominated_convergence bound
    (hGmeas.mono fun i hi => hi.aestronglyMeasurable)
    (hGbound.mono fun i hi => ae_of_all _ hi) hbound_int hlim
  rw [integral_zero] at hDCT
  -- identify `∫ G i`
  have hid : ∀ᶠ i in l, Integrable (G i) (volume.prod volume) ∧ ∀ x,
      ∫ w, G i (x, w) = (Icc (0:ℝ) 1).indicator (fun x =>
        (∫ w in (w0 i x)..(w1 i x), Kf σ w (b i x w)) - 2 * π * ∑ k, σ k * |b0 i x k|) x := by
    filter_upwards [hGmeas, hGbound, hmeas, hbB, hle] with i hGm hGb hmi hbi hlei
    refine ⟨hbound_int.mono' hGm.aestronglyMeasurable (ae_of_all _ hGb), fun x => ?_⟩
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hx]
      simp only [hG, hx, if_true]
      have hind : (fun w => if w0 i x ≤ w ∧ w ≤ w1 i x then Kf σ w (b i x w) else 0) =
          (Icc (w0 i x) (w1 i x)).indicator (fun w => Kf σ w (b i x w)) := by
        funext w; simp [Set.indicator, mem_Icc]
      have hmw : Measurable fun w => Kf σ w (b i x w) :=
        measurable_Kf σ measurable_id (fun k => (hmi.1 k).comp measurable_prodMk_left)
      have hint1 : Integrable (fun w => if w0 i x ≤ w ∧ w ≤ w1 i x then Kf σ w (b i x w) else 0) := by
        rw [hind, integrable_indicator_iff measurableSet_Icc]
        refine ((integrable_lk B).const_mul S).integrableOn.mono'
          hmw.aestronglyMeasurable.restrict ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
        rw [Real.norm_eq_abs]
        exact abs_Kf_le σ _ _ (fun k => (hbi x hx).1 w hw k)
      rw [integral_sub hint1 (integrable_Kf σ _), hind, integral_indicator measurableSet_Icc,
        integral_Kf, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hlei x hx)]
    · rw [Set.indicator_of_notMem hx]
      simp only [hG]; simp only [if_neg hx, integral_zero]
  refine ⟨?_, ?_⟩
  · filter_upwards [hid] with i hi
    obtain ⟨hint, hx⟩ := hi
    have := hint.integral_prod_left
    simp_rw [hx] at this
    rw [integrable_indicator_iff measurableSet_Icc] at this
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 this
  · refine hDCT.congr' ?_
    filter_upwards [hid] with i hi
    obtain ⟨hint, hx⟩ := hi
    rw [integral_prod _ hint]
    simp_rw [hx]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]

/-! ## 6. The graph covariance limit -/

lemma meshAff_gc {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (δ : ℝ) : MeshAff (16 ^ n) (gc δ f) := by
  intro i hi s hs
  have hN : (0:ℝ) < (16:ℝ) ^ n := by positivity
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hx : ((i:ℝ) + s) / (16:ℝ) ^ n ∈ Icc ((i : ℝ) / 16 ^ n) (((i : ℝ) + 1) / 16 ^ n) := by
    constructor
    · exact div_le_div_of_nonneg_right (by linarith [hs.1]) hN.le
    · exact div_le_div_of_nonneg_right (by linarith [hs.2]) hN.le
  have hp := Subadd.V_piece hf hi hx
  have hs' : (16:ℝ) ^ n * (((i:ℝ) + s) / 16 ^ n) - i = s := by field_simp; ring
  rw [hs'] at hp
  unfold gc
  rw [hp]
  push_cast
  ring

lemma meshAff_gc_zero (M : ℕ) (δ : ℝ) : MeshAff M (gc δ 0) := by
  intro i _ s _
  unfold gc
  simp only [Pi.zero_apply, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
  push_cast
  ring

lemma exists_bound_V {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) : ∃ B, ∀ x, |f x| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Subadd.V_continuous hf).continuousOn (s := Icc (0:ℝ) 1))
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · have := hC x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [hf.2.2.1 x hx, abs_zero]; exact le_max_right _ _

lemma continuous_bvec {α : Type*} [TopologicalSpace α] {u₁ u₂ v₃ v₄ : α → ℝ}
    (h₁ : Continuous u₁) (h₂ : Continuous u₂) (h₃ : Continuous v₃) (h₄ : Continuous v₄)
    (k : Fin 4) : Continuous fun a => bvec (u₁ a) (u₂ a) (v₃ a) (v₄ a) k := by
  fin_cases k <;> simp [bvec] <;> fun_prop

lemma abs_bvec_le {u₁ u₂ v₃ v₄ B : ℝ} (h₁ : |u₁| ≤ B) (h₂ : |u₂| ≤ B) (h₃ : |v₃| ≤ B)
    (h₄ : |v₄| ≤ B) (k : Fin 4) : |bvec u₁ u₂ v₃ v₄ k| ≤ 2 * B := by
  have a₁ := abs_le.1 h₁; have a₂ := abs_le.1 h₂; have a₃ := abs_le.1 h₃; have a₄ := abs_le.1 h₄
  fin_cases k <;> simp only [bvec] <;> simp <;> rw [abs_le] <;> constructor <;> linarith

lemma abs_bvec_sub_le (u₁ u₂ v₃ v₄ u₁' u₂' v₃' v₄' : ℝ) (k : Fin 4) :
    |bvec u₁ u₂ v₃ v₄ k - bvec u₁' u₂' v₃' v₄' k| ≤
      |u₁ - u₁'| + |u₂ - u₂'| + |v₃ - v₃'| + |v₄ - v₄'| := by
  have e₁ := le_abs_self (u₁ - u₁'); have e₁' := neg_abs_le (u₁ - u₁')
  have e₂ := le_abs_self (u₂ - u₂'); have e₂' := neg_abs_le (u₂ - u₂')
  have e₃ := le_abs_self (v₃ - v₃'); have e₃' := neg_abs_le (v₃ - v₃')
  have e₄ := le_abs_self (v₄ - v₄'); have e₄' := neg_abs_le (v₄ - v₄')
  fin_cases k <;> simp only [bvec] <;> simp <;> rw [abs_le] <;> constructor <;> linarith

/-- **Node `L32g`.** -/
theorem graphCovLimit : GraphCovLimit := by
  intro n f f' hf hf'
  have hM : 0 < 16 ^ n := by positivity
  have hfc := Subadd.V_continuous hf
  have hf'c := Subadd.V_continuous hf'
  obtain ⟨B₁, hB₁⟩ := exists_bound_V hf
  obtain ⟨B₂, hB₂⟩ := exists_bound_V hf'
  set B := max B₁ B₂ with hBdef
  have hfB : ∀ x, |f x| ≤ B := fun x => (hB₁ x).trans (le_max_left _ _)
  have hf'B : ∀ x, |f' x| ≤ B := fun x => (hB₂ x).trans (le_max_right _ _)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have h0B : ∀ x, |(0 : ℝ → ℝ) x| ≤ B := fun x => by simp [hB0]
  have hA' : ∀ y : ℝ, id y = 1 * y + 0 := fun y => by simp
  have hAb : ∀ x ∈ Icc (0:ℝ) 1, |id x| ≤ 1 := fun x hx => by
    rw [id, abs_of_nonneg hx.1]; exact hx.2
  have hdom : ∀ δ : ℝ, ∀ F G : ℝ → ℝ, Continuous F → Continuous G → (∀ x, |F x| ≤ B) →
      (∀ x, |G x| ≤ B) → LogDom (fun x y => -Real.log ‖gc δ F x - gc δ G y‖) :=
    fun δ F G hF hG hFB hGB => logDom_dc continuous_id one_pos hA' hF hG hAb
      (fun x _ => hFB x) (fun x _ => hGB x)
  -- the covariance as an iterated integral in `(x, w)`
  have hrepr : ∀ δ > 0, δ⁻¹ * ((graphComb (16 ^ n) δ f).sub (graphComb (16 ^ n) δ 0)).logCov
      ((graphComb (16 ^ n) δ f').sub (graphComb (16 ^ n) δ 0)) =
      ∫ x in (0:ℝ)..1, ∫ w in (-x / δ)..((1 - x) / δ),
        Kf σ4 w (bvec (f x) 0 (f' (δ * w + x)) 0) := by
    intro δ hδ
    simp only [graphComb_eq]
    rw [logCov_four hM hM hM hM (meshAff_gc hf δ) (meshAff_gc_zero _ δ) (meshAff_gc hf' δ)
      (meshAff_gc_zero _ δ) (hdom δ f f' hfc hf'c hfB hf'B)
      (hdom δ f 0 hfc continuous_const hfB h0B) (hdom δ 0 f' continuous_const hf'c h0B hf'B)
      (hdom δ 0 0 continuous_const continuous_const h0B h0B)]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have := inner_subst hδ one_pos id id hA' f 0 f' 0 x
    simp only [gc_eq_dc]
    rw [this]
    simp only [div_one, sub_zero, id, zero_sub, add_zero, Pi.zero_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
  set Bf : ℝ → ℝ := fun x => 2 * π * ∑ k, σ4 k * |bvec (f x) 0 (f' x) 0 k| with hBf
  have hzCov : zCov f f' = ∫ x in (0:ℝ)..1, Bf x := by
    unfold zCov
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp [hBf, σ4, bvec, Fin.sum_univ_four]
    ring
  have hBc : Continuous Bf :=
    continuous_const.mul (continuous_finset_sum _ fun k _ => continuous_const.mul
      (continuous_bvec hfc continuous_const hf'c continuous_const k).abs)
  -- hypotheses of the dominated convergence
  have hf'lim : ∀ x w : ℝ, Tendsto (fun δ => f' (δ * w + x)) (𝓝[>] 0) (𝓝 (f' x)) := by
    intro x w
    have h1 : Tendsto (fun δ : ℝ => δ * w + x) (𝓝 0) (𝓝 x) := by
      have h0 : Tendsto (fun δ : ℝ => δ * w + x) (𝓝 0) (𝓝 (0 * w + x)) :=
        ((continuous_id.mul continuous_const).add continuous_const).tendsto 0
      rwa [zero_mul, zero_add] at h0
    exact ((hf'c.tendsto x).comp h1).mono_left nhdsWithin_le_nhds
  have hcore := core_tendsto (l := 𝓝[>] (0:ℝ)) σ4 (2 * B)
    (fun δ x w => bvec (f x) 0 (f' (δ * w + x)) 0) (fun _ x => bvec (f x) 0 (f' x) 0)
    (fun δ x => -x / δ) (fun δ x => (1 - x) / δ)
    (Eventually.of_forall fun δ => ⟨fun k => (continuous_bvec (by fun_prop) continuous_const
      (hf'c.comp (by fun_prop)) continuous_const k).measurable,
      fun k => (continuous_bvec hfc continuous_const hf'c continuous_const k).measurable,
      by fun_prop, by fun_prop⟩)
    (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ x hx
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ))
    (Eventually.of_forall fun δ x _ =>
      ⟨fun w _ k => abs_bvec_le (hfB _) (by simp [hB0]) (hf'B _) (by simp [hB0]) k,
        fun k => abs_bvec_le (hfB _) (by simp [hB0]) (hf'B _) (by simp [hB0]) k⟩)
    (by
      intro x _ w k
      refine squeeze_zero_norm (fun δ => ?_) (a := fun δ => |f' (δ * w + x) - f' x|) ?_
      · rw [Real.norm_eq_abs]
        refine (abs_bvec_sub_le _ _ _ _ _ _ _ _ k).trans (le_of_eq ?_)
        simp
      · simpa using ((hf'lim x w).sub_const (f' x)).abs)
    (by
      intro x hx
      exact (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (neg_neg_of_pos hx.1)).congr
        fun δ => by ring)
    (by
      intro x hx
      exact (tendsto_inv_nhdsGT_zero.const_mul_atTop (sub_pos.2 hx.2)).congr fun δ => by ring)
  obtain ⟨hII, hT⟩ := hcore
  have hlim := hT.add (tendsto_const_nhds (x := ∫ x in (0:ℝ)..1, Bf x))
  rw [zero_add, ← hzCov] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hII] with δ hδ hIIδ
  rw [hrepr δ hδ, hzCov, ← intervalIntegral.integral_add hIIδ (hBc.intervalIntegrable 0 1)]
  congr 1; funext x; simp only [hBf]; ring

end LQGDimension.GraphCov

namespace LQGDimension

/-- **Node `L32g` (Lemma 3.2, graph form).** -/
theorem graphCovLimit : Blueprint.Draft.GraphCovLimit := GraphCov.graphCovLimit

end LQGDimension
