/-
The second-order expansion of `|x|^p` for `p ≥ 2`.

For `p ≥ 2` the function `x ↦ |x|^p` is twice differentiable away from the
origin and its second-order error is controlled by the two natural terms:

  `|a + b|^p ≤ |a|^p + p |a|^{p-2} a b + C_p (|a|^{p-2} b^2 + |b|^p)`.

This is the pointwise inequality behind the `2`-smoothness of `L^p` for
`p ≥ 2`, hence behind the Burkholder square-function bound and the Rosenthal
inequality for `p ≥ 2`: integrating it against a product measure kills the
linear term whenever `b` has mean zero given `a`, and Hölder turns the
remaining cross term into the `L^p` norms.

Both sides are homogeneous of degree `p` in `(a, b)`, so everything reduces to
the one-variable statement `|1 + t|^p ≤ 1 + p t + C_p (t^2 + |t|^p)`, and that
splits into two regimes.  For `|t| ≥ 1/2` the left side is at most
`3^p |t|^p` and the right side already carries `|t|^p`.  For `|t| ≤ 1/2` the
base `1 + t` is positive and the bound is the second-order Taylor estimate,
proved by applying the mean value theorem twice: once to `(1+s)^{p-1}` to see
that the derivative of the error vanishes to first order, and once to the error
itself.
-/
import Mathlib

noncomputable section

namespace LatticeProb

open Set

/-- The interval `[0, t]` sits inside `[-1/2, 1/2]` when `|t| ≤ 1/2`. -/
theorem uIcc_subset_of_abs_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    Set.uIcc (0 : ℝ) t ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
  have h1 : -(1 / 2 : ℝ) ≤ t := by
    have := abs_le.mp ht
    linarith [this.1]
  have h2 : t ≤ 1 / 2 := (abs_le.mp ht).2
  intro s hs
  rw [Set.mem_uIcc] at hs
  rw [Set.mem_Icc]
  rcases hs with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> constructor <;> linarith

/-- On `[-1/2, 1/2]` the base `1 + s` is at least `1/2`. -/
theorem one_add_pos {s : ℝ} (hs : s ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) : 0 < 1 + s := by
  have := (Set.mem_Icc.mp hs).1
  linarith

/-- The derivative of `s ↦ (1 + s)^q` on `[-1/2, 1/2]`. -/
theorem hasDerivWithinAt_one_add_rpow (q : ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    HasDerivWithinAt (fun u : ℝ => (1 + u) ^ q) (q * (1 + s) ^ (q - 1))
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) s := by
  have hbase : HasDerivWithinAt (fun u : ℝ => 1 + u) 1
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) s :=
    ((hasDerivAt_id s).const_add 1).hasDerivWithinAt
  have := hbase.rpow_const (p := q) (Or.inl (ne_of_gt (one_add_pos hs)))
  simpa [one_mul, mul_comm] using this

/-- The near regime: the second-order Taylor bound for `(1 + t)^p` on
`|t| ≤ 1/2`. -/
theorem abs_one_add_rpow_sub_le {p : ℝ} (hp : 2 ≤ p) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(1 + t) ^ p - 1 - p * t| ≤ p * (p - 1) * (3 / 2 : ℝ) ^ (p - 2) * t ^ 2 := by
  set I : Set ℝ := Set.Icc (-(1 / 2) : ℝ) (1 / 2) with hI
  have hconvI : Convex ℝ I := convex_Icc _ _
  have hzeroI : (0 : ℝ) ∈ I := by
    rw [hI, Set.mem_Icc]; norm_num
  have htI : t ∈ I := by
    rw [hI, Set.mem_Icc]
    have := abs_le.mp ht
    constructor <;> linarith [this.1, this.2]
  set K : ℝ := (p - 1) * (3 / 2 : ℝ) ^ (p - 2) with hK
  -- the derivative of the error, through the mean value theorem for `(1+s)^{p-1}`
  have hbound2 : ∀ s ∈ I, ‖(p - 1) * (1 + s) ^ (p - 1 - 1)‖ ≤ K := by
    intro s hs
    have hpos : 0 < 1 + s := one_add_pos hs
    have hle : (1 + s) ^ (p - 2) ≤ (3 / 2 : ℝ) ^ (p - 2) := by
      refine Real.rpow_le_rpow (le_of_lt hpos) ?_ (by linarith)
      have := (Set.mem_Icc.mp hs).2
      linarith
    have hnn : (0 : ℝ) ≤ (1 + s) ^ (p - 2) := Real.rpow_nonneg (le_of_lt hpos) _
    have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
    have hexp : p - 1 - 1 = p - 2 := by ring
    rw [hexp, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp1 hnn), hK]
    exact mul_le_mul_of_nonneg_left hle hp1
  have hderiv1 : ∀ s ∈ I,
      |(1 + s) ^ (p - 1) - 1| ≤ K * |s| := by
    intro s hs
    have := hconvI.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u : ℝ => (1 + u) ^ (p - 1))
      (f' := fun u : ℝ => (p - 1) * (1 + u) ^ (p - 1 - 1))
      (fun x hx => hasDerivWithinAt_one_add_rpow (p - 1) hx) hbound2 hzeroI hs
    simpa [Real.norm_eq_abs, Real.one_rpow] using this
  -- the error itself
  set J : Set ℝ := Set.uIcc (0 : ℝ) t with hJ
  have hJI : J ⊆ I := uIcc_subset_of_abs_le ht
  have hconvJ : Convex ℝ J := convex_uIcc _ _
  have hzeroJ : (0 : ℝ) ∈ J := Set.left_mem_uIcc
  have htJ : t ∈ J := Set.right_mem_uIcc
  have hderivg : ∀ s ∈ J,
      HasDerivWithinAt (fun u : ℝ => (1 + u) ^ p - 1 - p * u)
        (p * (1 + s) ^ (p - 1) - p) J s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun u : ℝ => (1 + u) ^ p) (p * (1 + s) ^ (p - 1)) J s :=
      (hasDerivWithinAt_one_add_rpow p (hJI hs)).mono hJI
    have h2 : HasDerivWithinAt (fun u : ℝ => (1 : ℝ) + p * u) p J s := by
      simpa using (((hasDerivAt_id s).const_mul p).const_add (1 : ℝ)).hasDerivWithinAt
    have h3 := h1.sub h2
    have hfun : ((fun u : ℝ => (1 + u) ^ p) - fun u : ℝ => 1 + p * u)
        = fun u : ℝ => (1 + u) ^ p - 1 - p * u := by
      funext u
      show (1 + u) ^ p - (1 + p * u) = (1 + u) ^ p - 1 - p * u
      ring
    rwa [hfun] at h3
  have hboundg : ∀ s ∈ J, ‖p * (1 + s) ^ (p - 1) - p‖ ≤ p * K * |t| := by
    intro s hs
    have hs' : s ∈ I := hJI hs
    have h1 : |(1 + s) ^ (p - 1) - 1| ≤ K * |s| := hderiv1 s hs'
    have hst : |s| ≤ |t| := by
      rw [hJ, Set.mem_uIcc] at hs
      rcases hs with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [abs_of_nonneg h3, abs_of_nonneg (le_trans h3 h4)]; exact h4
      · rw [abs_of_nonpos h4, abs_of_nonpos (le_trans h3 h4)]; linarith
    have hKnn : 0 ≤ K := by
      rw [hK]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    have hpnn : (0 : ℝ) ≤ p := by linarith
    have hfac : p * (1 + s) ^ (p - 1) - p = p * ((1 + s) ^ (p - 1) - 1) := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul, abs_of_nonneg hpnn]
    calc p * |(1 + s) ^ (p - 1) - 1| ≤ p * (K * |s|) :=
          mul_le_mul_of_nonneg_left h1 hpnn
      _ ≤ p * (K * |t|) := by
          refine mul_le_mul_of_nonneg_left ?_ hpnn
          exact mul_le_mul_of_nonneg_left hst hKnn
      _ = p * K * |t| := by ring
  have hmvt := hconvJ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => (1 + u) ^ p - 1 - p * u)
    (f' := fun u : ℝ => p * (1 + u) ^ (p - 1) - p)
    hderivg hboundg hzeroJ htJ
  simp only [Real.norm_eq_abs, add_zero, Real.one_rpow, mul_zero, sub_zero, sub_self] at hmvt
  have habs : |t| * |t| = t ^ 2 := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg t)]
    ring
  calc |(1 + t) ^ p - 1 - p * t| ≤ p * K * |t| * |t| := hmvt
    _ = p * K * (|t| * |t|) := by ring
    _ = p * K * t ^ 2 := by rw [habs]
    _ = p * (p - 1) * (3 / 2 : ℝ) ^ (p - 2) * t ^ 2 := by rw [hK]; ring

/-- The far regime: for `|t| ≥ 1/2` the left side is dominated by `|t|^p`. -/
theorem abs_one_add_rpow_le_of_half_le {p : ℝ} (hp : 2 ≤ p) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |1 + t| ^ p ≤ (3 : ℝ) ^ p * |t| ^ p := by
  have h3 : |1 + t| ≤ 3 * |t| := by
    have h1 : |1 + t| ≤ 1 + |t| := by
      calc |1 + t| ≤ |(1 : ℝ)| + |t| := abs_add_le _ _
        _ = 1 + |t| := by rw [abs_one]
    have h2 : (1 : ℝ) ≤ 2 * |t| := by linarith
    linarith
  have hnn : (0 : ℝ) ≤ |1 + t| := abs_nonneg _
  calc |1 + t| ^ p ≤ (3 * |t|) ^ p := Real.rpow_le_rpow hnn h3 (by linarith)
    _ = (3 : ℝ) ^ p * |t| ^ p := Real.mul_rpow (by norm_num) (abs_nonneg _)

/-- **The one-variable second-order bound.**  For `p ≥ 2`,
`|1 + t|^p ≤ 1 + p t + C (t^2 + |t|^p)`. -/
theorem exists_one_add_rpow_bound {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |1 + t| ^ p ≤ 1 + p * t + C * (t ^ 2 + |t| ^ p) := by
  set K : ℝ := p * (p - 1) * (3 / 2 : ℝ) ^ (p - 2) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (Real.rpow_nonneg (by norm_num) _)
  have h3p : (0 : ℝ) < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨(3 : ℝ) ^ p + 2 * p + K, by linarith, ?_⟩
  set C : ℝ := (3 : ℝ) ^ p + 2 * p + K with hC
  intro t
  have htsq : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have htp : (0 : ℝ) ≤ |t| ^ p := Real.rpow_nonneg (abs_nonneg _) _
  rcases le_or_gt (|t|) (1 / 2) with hcase | hcase
  · -- near regime
    have hpos : (0 : ℝ) < 1 + t := by
      have := (abs_le.mp hcase).1
      linarith
    have habs : |1 + t| = 1 + t := abs_of_pos hpos
    have hnear := abs_one_add_rpow_sub_le hp hcase
    have hle : (1 + t) ^ p - 1 - p * t ≤ K * t ^ 2 := by
      have := (abs_le.mp hnear).2
      rw [hK]
      linarith [this]
    rw [habs]
    have hKC : K * t ^ 2 ≤ C * (t ^ 2 + |t| ^ p) := by
      have h1 : K * t ^ 2 ≤ C * t ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ htsq
        rw [hC]; linarith
      have h2 : C * t ^ 2 ≤ C * (t ^ 2 + |t| ^ p) := by
        refine mul_le_mul_of_nonneg_left (by linarith) ?_
        rw [hC]; linarith
      linarith
    linarith
  · -- far regime
    have hcase' : 1 / 2 ≤ |t| := le_of_lt hcase
    have hfar := abs_one_add_rpow_le_of_half_le hp hcase'
    have habs2 : |t| ≤ 2 * t ^ 2 := by
      have h1 : |t| * 1 ≤ |t| * (2 * |t|) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
      have h2 : |t| * |t| = t ^ 2 := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg t)]; ring
      nlinarith
    have hlin : -(p * (2 * t ^ 2)) ≤ p * t := by
      have h1 : -|t| ≤ t := neg_abs_le t
      nlinarith [abs_nonneg t]
    have hbig : (3 : ℝ) ^ p * |t| ^ p ≤ C * |t| ^ p := by
      refine mul_le_mul_of_nonneg_right ?_ htp
      rw [hC]; linarith
    have hrest : C * (t ^ 2 + |t| ^ p) - C * |t| ^ p = C * t ^ 2 := by ring
    have hCp : 2 * p * t ^ 2 ≤ C * t ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ htsq
      rw [hC]; linarith
    have hone : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

/-- **The pointwise second-order bound.**  For `p ≥ 2` there is a constant `C`
with `|a + b|^p ≤ |a|^p + p |a|^{p-2} a b + C (|a|^{p-2} b^2 + |b|^p)` for all
reals `a` and `b`. -/
theorem exists_abs_add_rpow_bound {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℝ,
      |a + b| ^ p ≤ |a| ^ p + p * |a| ^ (p - 2) * a * b
        + C * (|a| ^ (p - 2) * b ^ 2 + |b| ^ p) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_one_add_rpow_bound hp
  refine ⟨max 1 C₀, le_max_left _ _, ?_⟩
  set C : ℝ := max 1 C₀ with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCC : C₀ ≤ C := le_max_right _ _
  intro a b
  rcases eq_or_ne a 0 with rfl | ha
  · have h1 : |(0 : ℝ)| ^ p = 0 := by
      rw [abs_zero]
      exact Real.zero_rpow (by linarith)
    have h2 : (0 : ℝ) ≤ |(0 : ℝ)| ^ (p - 2) * b ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg b)
    have h3 : (0 : ℝ) ≤ |b| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    have h4 : |b| ^ p ≤ C * (|(0 : ℝ)| ^ (p - 2) * b ^ 2 + |b| ^ p) := by
      nlinarith
    rw [abs_zero] at h1 ⊢
    rw [zero_add, h1, zero_add]
    simpa using h4
  · have hA : (0 : ℝ) < |a| := abs_pos.mpr ha
    set t : ℝ := b / a with hT
    have hfac : a + b = a * (1 + t) := by
      rw [hT]; field_simp
    have hlhs : |a + b| ^ p = |a| ^ p * |1 + t| ^ p := by
      rw [hfac, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    have hApow : |a| ^ p = |a| ^ (p - 2) * a ^ 2 := by
      have h1 : |a| ^ p = |a| ^ (p - 2) * |a| ^ (2 : ℝ) := by
        rw [← Real.rpow_add hA]
        ring_nf
      rw [h1]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hmul1 : |a| ^ p * (p * t) = p * |a| ^ (p - 2) * a * b := by
      rw [hApow, hT]
      field_simp
    have hmul2 : |a| ^ p * (C * t ^ 2) = C * (|a| ^ (p - 2) * b ^ 2) := by
      rw [hApow, hT]
      field_simp
    have hmul3 : |a| ^ p * (C * |t| ^ p) = C * |b| ^ p := by
      have habs : |t| = |b| / |a| := by rw [hT, abs_div]
      rw [habs, Real.div_rpow (abs_nonneg _) (le_of_lt hA)]
      field_simp
    have hstep := hbound t
    have hstep' : |1 + t| ^ p ≤ 1 + p * t + C * (t ^ 2 + |t| ^ p) := by
      refine hstep.trans ?_
      have hnn : (0 : ℝ) ≤ t ^ 2 + |t| ^ p :=
        add_nonneg (sq_nonneg t) (Real.rpow_nonneg (abs_nonneg _) _)
      have := mul_le_mul_of_nonneg_right hCC hnn
      linarith
    have hApos : (0 : ℝ) < |a| ^ p := Real.rpow_pos_of_pos hA _
    calc |a + b| ^ p = |a| ^ p * |1 + t| ^ p := hlhs
      _ ≤ |a| ^ p * (1 + p * t + C * (t ^ 2 + |t| ^ p)) :=
          mul_le_mul_of_nonneg_left hstep' (le_of_lt hApos)
      _ = |a| ^ p + |a| ^ p * (p * t) + (|a| ^ p * (C * t ^ 2) + |a| ^ p * (C * |t| ^ p)) := by
          ring
      _ = |a| ^ p + p * |a| ^ (p - 2) * a * b
            + C * (|a| ^ (p - 2) * b ^ 2 + |b| ^ p) := by
          rw [hmul1, hmul2, hmul3]; ring

/-! ### The algebraic step of the `2`-smoothness of `L^p` -/

/-- The tangent line to `x ↦ x^q` at `u`, for `q ≥ 1`. -/
theorem rpow_add_tangent {q u w : ℝ} (hq : 1 ≤ q) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    u ^ q + q * u ^ (q - 1) * w ≤ (u + w) ^ q := by
  rcases eq_or_lt_of_le hu with hu0 | hupos
  · rcases eq_or_lt_of_le hq with hq1 | hq1
    · rw [← hu0, ← hq1]
      simp
    · rw [← hu0]
      have h1 : (0 : ℝ) ^ q = 0 := Real.zero_rpow (by linarith)
      have h2 : (0 : ℝ) ^ (q - 1) = 0 := Real.zero_rpow (by linarith)
      rw [h1, h2, zero_add, mul_zero, zero_mul, zero_add]
      exact Real.rpow_nonneg hw q
  · have hune : u ≠ 0 := ne_of_gt hupos
    have hwu : (0 : ℝ) ≤ w / u := div_nonneg hw (le_of_lt hupos)
    have hber := one_add_mul_self_le_rpow_one_add (s := w / u)
      (by linarith) hq
    have hupow : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hupos q
    have hfac : u + w = u * (1 + w / u) := by field_simp
    have hsplit : (u + w) ^ q = u ^ q * (1 + w / u) ^ q := by
      rw [hfac, Real.mul_rpow (le_of_lt hupos) (by positivity)]
    have hshift : u ^ q * (w / u) = u ^ (q - 1) * w := by
      rw [Real.rpow_sub hupos, Real.rpow_one]
      field_simp
    calc u ^ q + q * u ^ (q - 1) * w = u ^ q * (1 + q * (w / u)) := by
          have : u ^ q * (1 + q * (w / u)) = u ^ q + q * (u ^ q * (w / u)) := by ring
          rw [this, hshift]
          ring
      _ ≤ u ^ q * (1 + w / u) ^ q := mul_le_mul_of_nonneg_left hber (le_of_lt hupow)
      _ = (u + w) ^ q := hsplit.symm

/-- **The algebraic step of the `2`-smoothness of `L^p`.**  For `p ≥ 2` and any
`C₁ ≥ 0` there is a `C` with
`u^{p/2} + C₁ (u^{(p-2)/2} v + v^{p/2}) ≤ (u + C v)^{p/2}` on the nonnegative
quadrant.  With `u = ‖X‖_p^2` and `v = ‖Y‖_p^2` this is what turns the
integrated pointwise bound into `‖X + Y‖_p^2 ≤ ‖X‖_p^2 + C ‖Y‖_p^2`. -/
theorem exists_two_smooth_const {p : ℝ} (hp : 2 ≤ p) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      u ^ (p / 2) + C₁ * (u ^ ((p - 2) / 2) * v + v ^ (p / 2))
        ≤ (u + C * v) ^ (p / 2) := by
  set q : ℝ := p / 2 with hq
  have hq1 : (1 : ℝ) ≤ q := by rw [hq]; linarith
  have hqpos : (0 : ℝ) < q := by linarith
  set C' : ℝ := C₁ / q with hC'
  set C'' : ℝ := C₁ ^ (1 / q) + 1 with hC''
  have hC'nn : 0 ≤ C' := div_nonneg hC₁ (le_of_lt hqpos)
  have hC''pos : 0 < C'' := by
    rw [hC'']
    have : (0 : ℝ) ≤ C₁ ^ (1 / q) := Real.rpow_nonneg hC₁ _
    linarith
  refine ⟨C' + C'', by linarith, ?_⟩
  intro u v hu hv
  have hexp : (p - 2) / 2 = q - 1 := by rw [hq]; ring
  rw [hexp]
  have hC'v : 0 ≤ C' * v := mul_nonneg hC'nn hv
  have hC''v : 0 ≤ C'' * v := mul_nonneg (le_of_lt hC''pos) hv
  have hsuper : (u + C' * v) ^ q + (C'' * v) ^ q ≤ ((u + C' * v) + C'' * v) ^ q :=
    Real.add_rpow_le_rpow_add (by linarith) hC''v hq1
  have htan : u ^ q + q * u ^ (q - 1) * (C' * v) ≤ (u + C' * v) ^ q :=
    rpow_add_tangent hq1 hu hC'v
  have hqC' : q * C' = C₁ := by
    rw [hC']
    field_simp
  have hlin : u ^ q + C₁ * (u ^ (q - 1) * v) ≤ (u + C' * v) ^ q := by
    have hrw : q * u ^ (q - 1) * (C' * v) = C₁ * (u ^ (q - 1) * v) := by
      rw [← hqC']; ring
    rw [hrw] at htan
    exact htan
  have hpow : C₁ * v ^ q ≤ (C'' * v) ^ q := by
    have h1 : (C'' * v) ^ q = C'' ^ q * v ^ q :=
      Real.mul_rpow (le_of_lt hC''pos) hv
    have h2 : C₁ ≤ C'' ^ q := by
      have hbase : C₁ ^ (1 / q) ≤ C'' := by rw [hC'']; linarith
      have h3 : (C₁ ^ (1 / q)) ^ q ≤ C'' ^ q :=
        Real.rpow_le_rpow (Real.rpow_nonneg hC₁ _) hbase (le_of_lt hqpos)
      have h4 : (C₁ ^ (1 / q)) ^ q = C₁ := by
        rw [← Real.rpow_mul hC₁, one_div, inv_mul_cancel₀ (ne_of_gt hqpos), Real.rpow_one]
      rw [h4] at h3
      exact h3
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hv q)
  have hcomb : (u + (C' + C'') * v) ^ q = ((u + C' * v) + C'' * v) ^ q := by
    congr 1
    ring
  rw [hcomb]
  calc u ^ q + C₁ * (u ^ (q - 1) * v + v ^ q)
      = (u ^ q + C₁ * (u ^ (q - 1) * v)) + C₁ * v ^ q := by ring
    _ ≤ (u + C' * v) ^ q + (C'' * v) ^ q := add_le_add hlin hpow
    _ ≤ ((u + C' * v) + C'' * v) ^ q := hsuper

end LatticeProb

end
