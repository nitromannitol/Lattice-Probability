/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.PolygonWindingBasic at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.Polygon
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Winding numbers of closed polygons: the logarithm along a segment (EXT-CA node H2, part 1)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H2.
This module contains the definition `wind p a := (2πi)⁻¹ ∮_p dz/(z-a)` of the winding number of a
polygon `p` about a point `a` (nodes H1/H2 of the blueprint), together with the analytic core:

* `exp_curveIntegral_segment_inv_sub`: along a segment `[u,v]` avoiding `a`, the integral of
  `dz/(z-a)` is the increment of a continuous logarithm of `z - a`, `exp ∮ = (v-a)/(u-a)`;
* `exp_walkIntegral_inv_sub`: the same along a whole polygonal walk, by telescoping;
* `exists_int_wind`: for a closed polygon (`p.last = p.head`) and `a ∉ p.carrier`, `wind p a` is an
  integer;
* `norm_walkIntegral_sub_le`: Lipschitz-type bound on differences of walk integrals.

The estimates far from the carrier, the local constancy of `wind` and the vanishing on the
unbounded component of the complement are in `Proofs/Complex/PolygonWinding.lean`, which imports
this file.

## Sources

R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021), Chapter 4: Definition 4.2
(printed p. 189) for the index of a loop, Corollary 4.4(1) (printed p. 190) for its integral form
`(2πi)⁻¹ ∮ dz/(z−a)`, and Corollary 4.3 (printed p. 189) for integer valuedness, local constancy
and vanishing on the unbounded component.  Ahlfors, *Complex Analysis* (3rd ed. 1979), Ch. 4 §4
(the index `n(γ,a)`) states the same facts.  The integral of the 1-form is the node-H1
`curveIntegral` of each edge, and the winding number is built from the total `walkIntegral`, so no
separate parametrization of the polygonal loop is needed.  (Citations corrected by AUDIT10 C10-3:
an earlier version cited "Definition 4.2 and Corollary 4.3" for the integral form.)

**Two winding notions.**  This `wind` (a polygon integral) is *not* connected in Lean to the degree
`loopDeg` of node T1 (`Proofs/Complex/TopoDegree.lean`); they agree by Burckel Cor 4.4(1).  The
blueprint (`EXT_CA_BLUEPRINT.md` §3 H2) asks for a single notion; the project carries both, and H2
is the one used by the Cauchy theory.

**Deviation in proof route** (mathematics unchanged).  Instead of lifting the polygonal loop
through `exp` and reading off the degree (node T1), the logarithm along a segment is produced
explicitly: the segment `[u,v]` lies in the open half plane bounded by the line through `a`
perpendicular to it (own elementary argument, `ray_midpoint_disjoint`), in which the branch
`z ↦ log ((a-z)/w)` of the logarithm of `z - a` is holomorphic
(`Complex.hasDerivAt_log`/`HasDerivAt.clog_real`), and the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`) gives the increment.  Telescoping over the
edges of the walk gives `exp ∮ = (last - a)/(head - a)`, which is `1` for a closed polygon, and
`Complex.exp_eq_one_iff` makes the winding number an integer.
-/

noncomputable section

open Set Metric Filter Complex Real AffineMap MeasureTheory
open scoped Topology Convex

namespace QuantumZipper.CA.Homology

/-! ## The winding number -/

/-- The winding number of the polygon `p` about the point `a`: `(2πi)⁻¹ ∮_p dz/(z-a)`
(Burckel, Definition 4.2 with Corollary 4.4(1), printed pp. 189–190: the integral form of the
index). -/
def wind (p : Polygon) (a : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * walkIntegral (fun z => (z - a)⁻¹) p.head p.rest

@[simp] theorem wind_def (p : Polygon) (a : ℂ) :
    wind p a = (2 * π * I)⁻¹ * walkIntegral (fun z => (z - a)⁻¹) p.head p.rest := rfl

theorem twoPiI_ne_zero : (2 * π * I : ℂ) ≠ 0 := by
  simp [Complex.I_ne_zero]

/-! ## Calculus helpers for the 1-form `dz/(z-a)` -/

@[simp] theorem dzForm_apply (f : ℂ → ℂ) (z w : ℂ) : dzForm f z w = f z * w := by
  simp only [dzForm, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

@[simp] theorem dzForm_sub_apply (f g : ℂ → ℂ) (z w : ℂ) :
    (dzForm f z - dzForm g z) w = (f z - g z) * w := by
  simp only [sub_apply, dzForm_apply, sub_mul]

/-- Real scalar multiplication on `ℂ` is multiplication by the coerced scalar. -/
theorem smul_eq_mul_coe (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := by
  refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im]

/-- The affine map `lineMap` on `ℂ`, in complex-arithmetic form. -/
theorem lineMap_eq (u v : ℂ) (c : ℝ) : lineMap u v c = u + (c : ℂ) * (v - u) := by
  rw [lineMap_apply_module', smul_eq_mul_coe]
  ring

/-- `lineMap` is continuous. -/
theorem continuous_lineMap (u v : ℂ) : Continuous fun t : ℝ => lineMap u v t := by
  have h : (fun t : ℝ => lineMap u v t) = fun t : ℝ => u + (t : ℂ) * (v - u) := by
    funext t
    exact lineMap_eq u v t
  rw [h]
  exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- The point `lineMap u v t` of the segment `[u,v]`. -/
theorem lineMap_mem_segment (u v : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lineMap u v t ∈ segment ℝ u v := by
  rw [segment_eq_image_lineMap]
  exact mem_image_of_mem _ ht

/-- A point outside the slit plane is a nonpositive real number. -/
theorem exists_nonpos_of_notMem_slitPlane {z : ℂ} (hz : z ∉ Complex.slitPlane) :
    ∃ r : ℝ, r ≤ 0 ∧ z = r := by
  have h : ¬(0 < z.re ∨ z.im ≠ 0) := fun h => hz (by
    rw [Complex.slitPlane_eq_union]
    simpa only [Set.mem_union, Set.mem_ofPred_eq] using h)
  rw [not_or, not_lt, not_not] at h
  refine ⟨z.re, h.1, ?_⟩
  refine Complex.ext (by simp) ?_
  simpa using h.2

/-- Integrability of `f (lineMap u v ·) · (v - u)` over `[0,1]` for `f` continuous on the segment. -/
theorem intervalIntegrable_segment_mul {f : ℂ → ℂ} {u v : ℂ}
    (hf : ContinuousOn f (segment ℝ u v)) :
    IntervalIntegrable (fun t : ℝ => f (lineMap u v t) * (v - u)) volume 0 1 := by
  have h : ContinuousOn (fun t : ℝ => f (lineMap u v t)) (Icc (0 : ℝ) 1) :=
    hf.comp (continuous_lineMap u v).continuousOn (fun t ht => lineMap_mem_segment u v ht)
  exact (h.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one

/-- A curve integral of `f dz` along a segment, as an interval integral of an explicit function. -/
theorem curveIntegral_segment_dzForm_eq (f : ℂ → ℂ) (u v : ℂ) :
    (∫ᶜ z in Path.segment u v, dzForm f z) = ∫ t in 0..1, f (lineMap u v t) * (v - u) := by
  rw [curveIntegral_segment (ω := dzForm f) u v]
  exact intervalIntegral.integral_congr fun t _ => dzForm_apply f (lineMap u v t) (v - u)

/-! ## Norm bounds -/

/-- The difference of the `dz/(z-a)` edge integrals is bounded by `C · ‖v-u‖` when the coefficient
functions differ by at most `C` on the segment. -/
theorem norm_curveIntegral_segment_dzForm_sub_le {f g : ℂ → ℂ} {u v : ℂ} {C : ℝ}
    (hf : ContinuousOn f (segment ℝ u v)) (hg : ContinuousOn g (segment ℝ u v))
    (hC : ∀ z ∈ segment ℝ u v, ‖f z - g z‖ ≤ C) :
    ‖(∫ᶜ z in Path.segment u v, dzForm f z) - (∫ᶜ z in Path.segment u v, dzForm g z)‖
      ≤ C * ‖v - u‖ := by
  have hsub : (∫ t in 0..1, f (lineMap u v t) * (v - u))
      - (∫ t in 0..1, g (lineMap u v t) * (v - u))
      = ∫ t in 0..1, (f (lineMap u v t) - g (lineMap u v t)) * (v - u) := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_segment_mul hf)
      (intervalIntegrable_segment_mul hg)]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [curveIntegral_segment_dzForm_eq f u v, curveIntegral_segment_dzForm_eq g u v, hsub]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * ‖v - u‖) ?_) ?_
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hz : lineMap u v t ∈ segment ℝ u v := lineMap_mem_segment u v ht'
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC _ hz) (norm_nonneg _)
  · rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) - 0), sub_zero, mul_one]

/-- The difference of the `dz/(z-a)` walk integrals is bounded by `C · length`, when the
coefficient functions differ by at most `C` on the carrier (Lipschitz estimate for the winding
number). -/
theorem norm_walkIntegral_sub_le {f g : ℂ → ℂ} (u : ℂ) (l : List ℂ) {A : Set ℂ}
    (hA : walkCarrier u l ⊆ A) (hf : ContinuousOn f A) (hg : ContinuousOn g A) {C : ℝ}
    (hC : ∀ z ∈ A, ‖f z - g z‖ ≤ C) :
    ‖walkIntegral f u l - walkIntegral g u l‖ ≤ walkLength u l * C := by
  induction l generalizing u with
  | nil => simp [walkLength, walkIntegral]
  | cons v t ih =>
    have hseg : segment ℝ u v ⊆ A := fun z hz => hA (Or.inl hz)
    have htail : walkCarrier v t ⊆ A := fun z hz => hA (Or.inr hz)
    have hEdge := norm_curveIntegral_segment_dzForm_sub_le (hf.mono hseg) (hg.mono hseg)
      (fun z hz => hC z (hseg hz))
    have hRec := ih v htail
    have hsplit : walkIntegral f u (v :: t) - walkIntegral g u (v :: t)
        = ((∫ᶜ z in Path.segment u v, dzForm f z) - (∫ᶜ z in Path.segment u v, dzForm g z))
          + (walkIntegral f v t - walkIntegral g v t) := by
      simp only [walkIntegral, walkIntegralCLM_cons]
      abel
    rw [hsplit, walkLength_cons]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add hEdge hRec) (le_of_eq ?_)
    rw [norm_sub_rev v u]
    ring

/-! ## Logarithms along a segment -/

/-- **The ray through `a` along `a - midpoint(u,v)` misses the segment `[u,v]`** whenever `a` is
not on it (own elementary proof). If a point `a + t·w` of that ray were on `[u,v]`, the unique `s`
with `lineMap u v s` equal to it would satisfy `a = midpoint + ((s - 1/2)/(1+t))·(v-u)` with
`|(s-1/2)/(1+t)| ≤ 1/2`, so `a` would be a point of `[u,v]`. -/
theorem ray_midpoint_disjoint {u v a : ℂ} (ha : a ∉ segment ℝ u v) :
    ∀ t : ℝ, 0 ≤ t → a + (t : ℂ) * (a - (u + v) / 2) ∉ segment ℝ u v := by
  intro t ht hmem
  rw [segment_eq_image_lineMap] at hmem
  obtain ⟨s, hs, hsv⟩ := hmem
  rw [lineMap_eq] at hsv
  have htne : (1 : ℂ) + (t : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 + t := by linarith
    exact_mod_cast (ne_of_gt this)
  have hmain : a = (u + v) / 2 + ((↑s - 1 / 2) / (1 + ↑t)) * (v - u) := by
    have hkey : (1 + ↑t) * a = u + ↑s * (v - u) + ↑t * ((u + v) / 2) := by
      linear_combination -hsv
    have h2 : (1 + ↑t) * ((u + v) / 2 + ((↑s - 1 / 2) / (1 + ↑t)) * (v - u))
        = u + ↑s * (v - u) + ↑t * ((u + v) / 2) := by
      field_simp
      ring
    rw [← h2] at hkey
    exact mul_left_cancel₀ htne hkey
  refine ha ?_
  rw [segment_eq_image_lineMap]
  refine ⟨(s - 1 / 2) / (1 + t) + 1 / 2, ⟨?_, ?_⟩, ?_⟩
  · have h1 : (0 : ℝ) < 1 + t := by linarith
    have h2 : -(1 / 2) * (1 + t) ≤ s - 1 / 2 := by nlinarith [hs.1]
    have h3 := (le_div_iff₀ h1).mpr h2
    linarith
  · have h1 : (0 : ℝ) < 1 + t := by linarith
    have h2 : s - 1 / 2 ≤ (1 / 2) * (1 + t) := by nlinarith [hs.2]
    have h3 := (div_le_iff₀ h1).mpr h2
    linarith
  · rw [lineMap_eq]
    push_cast
    linear_combination -hmain

/-- **Segment logarithm.** If the segment `[u,v]` avoids the point `a`, then the integral of
`dz/(z-a)` along it is a logarithm increment: `exp ∮ = (v-a)/(u-a)` (Burckel, Corollary 4.4(1),
printed p. 190, applied to a single segment). -/
theorem exp_curveIntegral_segment_inv_sub (a u v : ℂ) (ha : a ∉ segment ℝ u v) :
    Complex.exp (∫ᶜ z in Path.segment u v, dzForm (fun z => (z - a)⁻¹) z)
      = (v - a) / (u - a) := by
  have hu : u ∈ segment ℝ u v := left_mem_segment ℝ u v
  have hv : v ∈ segment ℝ u v := right_mem_segment ℝ u v
  have hua : u ≠ a := fun h => ha (h ▸ hu)
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  -- the direction whose forward ray misses the segment
  set w : ℂ := a - (u + v) / 2 with hw
  have hw_ne : w ≠ 0 := by
    intro h0
    apply ha
    rw [segment_eq_image_lineMap]
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [lineMap_eq]
    have h1 : a = (u + v) / 2 := by rw [hw] at h0; linear_combination h0
    rw [h1]
    push_cast
    ring
  have hray : ∀ t : ℝ, 0 ≤ t → a + (t : ℂ) * w ∉ segment ℝ u v := by
    intro t ht
    rw [hw]
    exact ray_midpoint_disjoint ha t ht
  -- the rotated logarithm is holomorphic on the segment
  have hslit : ∀ z ∈ segment ℝ u v, (a - z) / w ∈ Complex.slitPlane := by
    intro z hz
    by_contra hznot
    obtain ⟨r, hr, hrz⟩ := exists_nonpos_of_notMem_slitPlane hznot
    have hzw : a - z = (r : ℂ) * w := by
      rw [← hrz]
      exact (div_mul_cancel₀ (a - z) hw_ne).symm
    have hz' : z = a + ((-r : ℝ) : ℂ) * w := by
      rw [show z = a - (r : ℂ) * w from by linear_combination -hzw]
      push_cast
      ring
    exact hray (-r) (by linarith) (hz' ▸ hz)
  -- the parametrized logarithm and its derivative
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.log ((a - lineMap u v s) / w))
        ((lineMap u v t - a)⁻¹ * (v - u)) t := by
    intro t ht
    have hz : lineMap u v t ∈ segment ℝ u v := lineMap_mem_segment u v ht
    have hΦ : (a - lineMap u v t) / w ∈ Complex.slitPlane := hslit _ hz
    have hne : (a - lineMap u v t) / w ≠ 0 := Complex.slitPlane_ne_zero hΦ
    have hzero : a - lineMap u v t ≠ 0 := fun h => hne (by rw [h, zero_div])
    have hza : lineMap u v t - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (fun h => ha (h ▸ hz)))
    have hlin : HasDerivAt (fun s : ℝ => lineMap u v s) (v - u) t := hasDerivAt_lineMap
    have h1 : HasDerivAt (fun s : ℝ => (a - lineMap u v s) / w) (-(v - u) / w) t :=
      (hlin.const_sub a).div_const w
    have h2 := HasDerivAt.clog_real h1 hΦ
    convert h2 using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun s : ℝ => Complex.log ((a - lineMap u v s) / w))
      (Icc (0 : ℝ) 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t : ℝ => (lineMap u v t - a)⁻¹ * (v - u)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    exact ContinuousOn.inv₀ (((continuous_lineMap u v).sub continuous_const).continuousOn)
      (fun t ht => by
        have hz : lineMap u v t ∈ segment ℝ u v := lineMap_mem_segment u v ht
        intro hzero
        exact ha (sub_eq_zero.mp hzero ▸ hz))
  have hFTC : ∫ t in 0..1, (lineMap u v t - a)⁻¹ * (v - u)
      = Complex.log ((a - v) / w) - Complex.log ((a - u) / w) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := 1)
      zero_le_one hcont (fun t ht => hderiv t (Ioo_subset_Icc_self ht)) hint
    simpa only [lineMap_apply_one, lineMap_apply_zero] using this
  rw [curveIntegral_segment_dzForm_eq (fun z => (z - a)⁻¹) u v, hFTC, Complex.exp_sub,
    Complex.exp_log (Complex.slitPlane_ne_zero (hslit u hu)),
    Complex.exp_log (Complex.slitPlane_ne_zero (hslit v hv))]
  have h1 : (a - u) / w ≠ 0 := Complex.slitPlane_ne_zero (hslit u hu)
  have h2 : (a - v) / w ≠ 0 := Complex.slitPlane_ne_zero (hslit v hv)
  have h3 : u - a ≠ 0 := sub_ne_zero.mpr hua
  have h4 : v - a ≠ 0 := sub_ne_zero.mpr hva
  field_simp
  ring

/-! ## Telescoping along a walk, and integrality of the winding number -/

theorem walkIntegral_cons (f : ℂ → ℂ) (u v : ℂ) (t : List ℂ) :
    walkIntegral f u (v :: t) = (∫ᶜ z in Path.segment u v, dzForm f z) + walkIntegral f v t := rfl

/-- **Telescoping.** Along a walk that avoids `a`, `exp ∮ dz/(z-a) = (last - a)/(head - a)`. -/
theorem exp_walkIntegral_inv_sub (a u : ℂ) (l : List ℂ) (hu : u ≠ a)
    (h : ∀ z ∈ walkCarrier u l, z ≠ a) :
    Complex.exp (walkIntegral (fun z => (z - a)⁻¹) u l) = (walkLast u l - a) / (u - a) := by
  induction l generalizing u with
  | nil =>
    have h1 : walkIntegral (fun z => (z - a)⁻¹) u [] = 0 := rfl
    rw [h1, walkLast_nil, Complex.exp_zero]
    exact (div_self (sub_ne_zero.mpr hu)).symm
  | cons v t ih =>
    have hva : v ≠ a := h v (Or.inl (right_mem_segment ℝ u v))
    have hua : u ≠ a := h u (Or.inl (left_mem_segment ℝ u v))
    have hseg : a ∉ segment ℝ u v := fun hz => h a (Or.inl hz) rfl
    have hstep := exp_curveIntegral_segment_inv_sub a u v hseg
    have hIH := ih v hva (fun z hz => h z (Or.inr hz))
    rw [walkIntegral_cons, walkLast_cons, Complex.exp_add, hstep, hIH]
    have h1 : v - a ≠ 0 := sub_ne_zero.mpr hva
    have h2 : u - a ≠ 0 := sub_ne_zero.mpr hua
    field_simp

/-- **H2, integrality.** For a closed walk (`last = head`) that avoids `a`, the winding number
`(2πi)⁻¹ ∮ dz/(z-a)` is an integer (Burckel, Corollary 4.3, printed p. 189). -/
theorem exists_int_wind_of_closed_walk (a u : ℂ) (l : List ℂ) (hne : l ≠ [])
    (hlast : walkLast u l = u) (h : ∀ z ∈ walkCarrier u l, z ≠ a) :
    ∃ n : ℤ, (2 * π * I)⁻¹ * walkIntegral (fun z => (z - a)⁻¹) u l = n := by
  cases l with
  | nil => exact absurd rfl hne
  | cons v t =>
    have hua : u ≠ a := h u (Or.inl (left_mem_segment ℝ u v))
    have hexp := exp_walkIntegral_inv_sub a u (v :: t) hua h
    rw [hlast, div_self (sub_ne_zero.mpr hua)] at hexp
    have hmul : (2 * π * I)
        * ((2 * π * I)⁻¹ * walkIntegral (fun z => (z - a)⁻¹) u (v :: t))
        = walkIntegral (fun z => (z - a)⁻¹) u (v :: t) := by
      rw [← mul_assoc, mul_inv_cancel₀ twoPiI_ne_zero, one_mul]
    have hexp1 : Complex.exp ((2 * π * I)
        * ((2 * π * I)⁻¹ * walkIntegral (fun z => (z - a)⁻¹) u (v :: t))) = 1 := by
      rw [hmul]
      exact hexp
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
    refine ⟨n, ?_⟩
    rw [mul_comm (2 * π * I)] at hn
    exact mul_right_cancel₀ twoPiI_ne_zero hn

/-- **H2, integrality for polygons.** For a closed polygon `p` and `a` off its carrier, the winding
number `wind p a` is an integer. -/
theorem exists_int_wind (p : Polygon) (hcl : p.last = p.head) (a : ℂ) (ha : a ∉ p.carrier) :
    ∃ n : ℤ, wind p a = n := by
  cases hrest : p.rest with
  | nil => exact ⟨0, by rw [wind, hrest]; simp [walkIntegral]⟩
  | cons v t =>
    have hlast : walkLast p.head (v :: t) = p.head := by
      have h1 : walkLast p.head p.rest = p.head := by
        rw [← Polygon.last_def]
        exact hcl
      rwa [hrest] at h1
    have h : ∀ z ∈ walkCarrier p.head (v :: t), z ≠ a := by
      intro z hz hza
      have hcar : p.carrier = walkCarrier p.head (v :: t) := by
        rw [Polygon.carrier_def, hrest]
      exact ha (hza ▸ hcar.symm ▸ hz)
    obtain ⟨n, hn⟩ := exists_int_wind_of_closed_walk a p.head (v :: t) (by simp) hlast h
    exact ⟨n, by rw [wind, hrest]; exact hn⟩

end QuantumZipper.CA.Homology
