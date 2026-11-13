/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.Lemma25Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.Lemma25TailCore
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.Lemma25

/-!
# [18] Lemma 2.5: exponential tail of mated-CRT degrees

Gwynne--Miller, *Harmonic functions on mated-CRT maps*, Lemma 2.5 (source copy
, lines 925--941): for `γ ∈ (0, 2)` there are constants
`c₀, c₁ > 0`, depending only on `γ`, such that for `n ∈ ℕ`, `ε > 0` and `x ∈ εℤ`,
`P[deg(x; G^ε) > n] ≤ c₀ e^{-c₁ n}`. The proof follows,
Details (c1).

The degree of `x` is `2` (the two consecutive edges) plus, for each coordinate `X ∈ {L, R}` and
each direction, the number of `y` with `|y - x| ≥ 2` satisfying the side condition (1.1). After
the affine change of time `t ↦ ε (x - 1) + ε t` (to the right) or `t ↦ ε x - ε t` (to the left)
and the scaling `X ↦ (X - X_c) / √ε`, the coordinate becomes a standard Brownian motion
(`lemma25Tail_proc_isPreBrownianReal`) and the side condition for `y = x ± b` becomes the
counted-block condition of the block `[b, b + 1]` (`lemma25TailCounted`), whose count has an
exponential tail by `lemma25Tail_count_tail`.

Main results:
* `lemma25Tail_degree_tail`: the raw degree `lemma25Degree ε ω x` (equal to the frozen graph
  degree on the a.s. event of local finiteness) satisfies
  `μ {n < deg} ≤ c₀ e^{-c₁ n}` with absolute constants (uniform in `γ`, `ε`, `x`).
* `lemma25_degree_tail_holds`: [18] Lemma 2.5 as cited, for the frozen `MatedCRT.graph`.
* `lemma25Tail_lintegral_degree_pow_lt_top`: every moment of the degree is finite.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

/-! ### Two-sided Brownian covariance -/

/-- The two-sided Brownian covariance in absolute-value form. -/
theorem lemma25Tail_twoSidedMin_eq (u v : ℝ) :
    twoSidedMin u v = (|u| + |v| - |u - v|) / 2 := by
  unfold twoSidedMin
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · rw [max_eq_left hu, max_eq_left hv, max_eq_right (by linarith : -u ≤ 0),
      max_eq_right (by linarith : -v ≤ 0), abs_of_nonneg hu, abs_of_nonneg hv, min_self]
    rcases le_total u v with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      ring
  · rw [max_eq_left hu, max_eq_right hv, max_eq_right (by linarith : -u ≤ 0),
      max_eq_left (by linarith : 0 ≤ -v), abs_of_nonneg hu, abs_of_nonpos hv,
      abs_of_nonneg (by linarith : 0 ≤ u - v), min_eq_right hu, min_eq_left (by linarith : 0 ≤ -v)]
    ring
  · rw [max_eq_right hu, max_eq_left hv, max_eq_left (by linarith : 0 ≤ -u),
      max_eq_right (by linarith : -v ≤ 0), abs_of_nonpos hu, abs_of_nonneg hv,
      abs_of_nonpos (by linarith : u - v ≤ 0), min_eq_left hv, min_eq_right (by linarith : 0 ≤ -u)]
    ring
  · rw [max_eq_right hu, max_eq_right hv, max_eq_left (by linarith : 0 ≤ -u),
      max_eq_left (by linarith : 0 ≤ -v), abs_of_nonpos hu, abs_of_nonpos hv, min_self]
    rcases le_total u v with h | h
    · rw [min_eq_right (by linarith : -v ≤ -u), abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_left (by linarith : -u ≤ -v), abs_of_nonneg (by linarith)]
      ring

/-- The covariance of two increments from a common base point. -/
theorem lemma25Tail_twoSidedMin_incr (c p q : ℝ) :
    twoSidedMin p q - twoSidedMin p c - twoSidedMin c q + twoSidedMin c c =
      (|p - c| + |c - q| - |p - q|) / 2 := by
  simp only [lemma25Tail_twoSidedMin_eq, sub_self, abs_zero]
  ring

/-! ### Restarted, rescaled coordinates -/

/-- The coordinate `i` restarted at time `c`, run forward (`σ = 1`) or backward (`σ = -1`) in
time at speed `ε`, and rescaled: `t ↦ (X (c + σ ε t) - X c) / √ε`. -/
def lemma25TailProc (i : Fin 2) (ε c σ : ℝ) (t : ℝ≥0) (ω : Path2) : ℝ :=
  (Real.sqrt ε)⁻¹ * (lrCoord i (c + σ * ε * t) ω - lrCoord i c ω)

theorem lemma25TailProc_continuous (i : Fin 2) (ε c σ : ℝ) (ω : Path2) :
    Continuous fun t : ℝ≥0 => lemma25TailProc i ε c σ t ω := by
  unfold lemma25TailProc lrCoord
  split_ifs <;> fun_prop

theorem lemma25TailProc_measurable (i : Fin 2) (ε c σ : ℝ) (t : ℝ≥0) :
    Measurable (lemma25TailProc i ε c σ t) := by
  unfold lemma25TailProc
  exact ((measurable_lrCoord (i, c + σ * ε * t)).sub (measurable_lrCoord (i, c))).const_mul _

/-- **The restarted coordinate is a standard Brownian motion.** -/
theorem lemma25Tail_proc_isPreBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {ε : ℝ} (hε : 0 < ε) (c : ℝ) {σ : ℝ}
    (hσ : |σ| = 1) :
    IsPreBrownianReal (lemma25TailProc i ε c σ) μ := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hGP : IsGaussianProcess (lemma25TailProc i ε c σ) μ := by
    apply hμ.isGaussianProcess.of_isGaussianProcess
    intro t
    let p : Fin 2 × ℝ := (i, c + σ * ε * t)
    let q : Fin 2 × ℝ := (i, c)
    let I : Finset (Fin 2 × ℝ) := {p, q}
    let L : (I → ℝ) →L[ℝ] ℝ := (Real.sqrt ε)⁻¹ •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨p, by simp [I]⟩ -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨q, by simp [I]⟩)
    refine ⟨I, L, ?_⟩
    intro ω
    simp [lemma25TailProc, p, q, I, L]
  have hmem (u : ℝ) : MemLp (fun ω => lrCoord i u ω) 2 μ :=
    (hμ.isGaussianProcess.hasGaussianLaw_eval (i, u)).memLp_two
  refine hGP.isPreBrownianReal_of_covariance ?_ ?_
  · intro t
    change ∫ ω, (Real.sqrt ε)⁻¹ * (lrCoord i (c + σ * ε * t) ω - lrCoord i c ω) ∂μ = 0
    rw [integral_const_mul, integral_sub, hμ.integral_eq_zero, hμ.integral_eq_zero, sub_self,
      mul_zero]
    · exact (hμ.isGaussianProcess.hasGaussianLaw_eval (i, c + σ * ε * t)).integrable
    · exact (hμ.isGaussianProcess.hasGaussianLaw_eval (i, c)).integrable
  · intro s t hst
    change cov[fun ω => (Real.sqrt ε)⁻¹ * (lrCoord i (c + σ * ε * s) ω - lrCoord i c ω),
      fun ω => (Real.sqrt ε)⁻¹ * (lrCoord i (c + σ * ε * t) ω - lrCoord i c ω); μ] = (s : ℝ)
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_fun_sub_fun_sub (hmem _) (hmem _) (hmem _) (hmem _),
      hμ.covariance_eq, hμ.covariance_eq, hμ.covariance_eq, hμ.covariance_eq]
    have hii : lrCov γ i i = 1 := by simp [lrCov]
    rw [hii, one_mul, one_mul, one_mul, one_mul]
    rw [show twoSidedMin (c + σ * ε * s) (c + σ * ε * t) - twoSidedMin (c + σ * ε * s) c -
        twoSidedMin c (c + σ * ε * t) + twoSidedMin c c =
        twoSidedMin (c + σ * ε * s) (c + σ * ε * t) - twoSidedMin (c + σ * ε * s) c -
        twoSidedMin c (c + σ * ε * t) + twoSidedMin c c from rfl]
    rw [lemma25Tail_twoSidedMin_incr]
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hs0 : (0 : ℝ) ≤ s := s.2
    have h1 : |c + σ * ε * s - c| = ε * s := by
      rw [show c + σ * ε * s - c = σ * (ε * s) by ring, abs_mul, hσ, one_mul,
        abs_of_nonneg (by positivity)]
    have h2 : |c - (c + σ * ε * t)| = ε * t := by
      rw [show c - (c + σ * ε * t) = -(σ * (ε * t)) by ring, abs_neg, abs_mul, hσ, one_mul,
        abs_of_nonneg (by positivity)]
    have h3 : |c + σ * ε * s - (c + σ * ε * t)| = ε * (t - s) := by
      rw [show c + σ * ε * s - (c + σ * ε * t) = -(σ * (ε * (t - s))) by ring, abs_neg,
        abs_mul, hσ, one_mul, abs_of_nonneg (by nlinarith)]
    rw [h1, h2, h3]
    have hsq : (Real.sqrt ε)⁻¹ * (Real.sqrt ε)⁻¹ = ε⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hε.le]
    rw [← mul_assoc, hsq]
    field_simp
    ring

/-! ### Interval infima under the change of time -/

/-- Interval infima of a coordinate over an image of an interval of times of the restarted
process are affine images of the restarted process's infima. -/
theorem lemma25Tail_sInf_image_proc {i : Fin 2} {ε : ℝ} (hε : 0 < ε) (c σ : ℝ) (ω : Path2)
    {u v : ℝ≥0} (huv : u ≤ v) {S : Set ℝ}
    (hS : (fun t => lrCoord i t ω) '' S =
      (fun t : ℝ≥0 => lrCoord i (c + σ * ε * t) ω) '' Icc u v) :
    sInf ((fun t => lrCoord i t ω) '' S) =
      lrCoord i c ω + Real.sqrt ε * lemma25TailInf (lemma25TailProc i ε c σ) u v ω := by
  set P := lemma25TailProc i ε c σ
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  set g : ℝ → ℝ := fun y => lrCoord i c ω + Real.sqrt ε * y with hg
  have hgP : ∀ t : ℝ≥0, g (P t ω) = lrCoord i (c + σ * ε * t) ω := by
    intro t
    simp only [hg, P, lemma25TailProc]
    rw [← mul_assoc, mul_inv_cancel₀ hsq.ne', one_mul]
    ring
  have himg : (fun t : ℝ≥0 => lrCoord i (c + σ * ε * t) ω) '' Icc u v =
      g '' ((fun t => P t ω) '' Icc u v) := by
    rw [Set.image_image]
    exact Set.image_congr fun t _ => (hgP t).symm
  have hgm : Monotone g := fun y z hyz => by
    simp only [hg]
    nlinarith
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hK : IsCompact ((fun t => P t ω) '' Icc u v) :=
    isCompact_Icc.image (lemma25TailProc_continuous i ε c σ ω)
  have hne : ((fun t => P t ω) '' Icc u v).Nonempty := ⟨P u ω, u, ⟨le_rfl, huv⟩, rfl⟩
  rw [hS, himg, ← hgm.map_csInf_of_continuousAt hgc.continuousAt hne hK.bddBelow]
  rfl

/-- Forward change of time: `inf_{[c + ε u, c + ε v]} X = X c + √ε inf_{[u, v]} P`. -/
theorem lemma25Tail_intervalInf_fwd {i : Fin 2} {ε : ℝ} (hε : 0 < ε) (c : ℝ) (ω : Path2)
    {u v : ℝ≥0} (huv : u ≤ v) :
    intervalInf (fun t => lrCoord i t ω) (c + ε * u) (c + ε * v) =
      lrCoord i c ω + Real.sqrt ε * lemma25TailInf (lemma25TailProc i ε c 1) u v ω := by
  apply lemma25Tail_sInf_image_proc hε c 1 ω huv
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    have h0 : 0 ≤ (r - c) / ε := div_nonneg (by nlinarith [hr.1, u.2]) hε.le
    refine ⟨⟨(r - c) / ε, h0⟩, ⟨?_, ?_⟩, ?_⟩
    · change (u : ℝ) ≤ (r - c) / ε
      rw [le_div_iff₀ hε]
      linarith [hr.1]
    · change (r - c) / ε ≤ (v : ℝ)
      rw [div_le_iff₀ hε]
      linarith [hr.2]
    · change lrCoord i (c + 1 * ε * ((r - c) / ε)) ω = lrCoord i r ω
      congr 1
      field_simp
      ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨c + 1 * ε * t, ⟨?_, ?_⟩, rfl⟩
    · have : (u : ℝ) ≤ t := ht.1
      nlinarith
    · have : (t : ℝ) ≤ v := ht.2
      nlinarith

/-- Backward change of time: `inf_{[c - ε v, c - ε u]} X = X c + √ε inf_{[u, v]} P`. -/
theorem lemma25Tail_intervalInf_bwd {i : Fin 2} {ε : ℝ} (hε : 0 < ε) (c : ℝ) (ω : Path2)
    {u v : ℝ≥0} (huv : u ≤ v) :
    intervalInf (fun t => lrCoord i t ω) (c - ε * v) (c - ε * u) =
      lrCoord i c ω + Real.sqrt ε * lemma25TailInf (lemma25TailProc i ε c (-1)) u v ω := by
  apply lemma25Tail_sInf_image_proc hε c (-1) ω huv
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    have h0 : 0 ≤ (c - r) / ε := div_nonneg (by nlinarith [hr.2, u.2]) hε.le
    refine ⟨⟨(c - r) / ε, h0⟩, ⟨?_, ?_⟩, ?_⟩
    · change (u : ℝ) ≤ (c - r) / ε
      rw [le_div_iff₀ hε]
      linarith [hr.2]
    · change (c - r) / ε ≤ (v : ℝ)
      rw [div_le_iff₀ hε]
      linarith [hr.1]
    · change lrCoord i (c + -1 * ε * ((c - r) / ε)) ω = lrCoord i r ω
      congr 1
      field_simp
      ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨c + -1 * ε * t, ⟨?_, ?_⟩, rfl⟩
    · have : (t : ℝ) ≤ v := ht.2
      nlinarith
    · have : (u : ℝ) ≤ t := ht.1
      nlinarith

/-! ### The side condition as a counted block -/

/-- The coordinate of the `side`-edges of [18] (1.1) (`false ↦ L`, `true ↦ R`). -/
def lemma25TailSide (s : Bool) : Fin 2 := if s then 1 else 0

theorem lemma25TailSide_coord (s : Bool) (ω : Path2) :
    (fun t => if s then (ω t).2 else (ω t).1) = fun t => lrCoord (lemma25TailSide s) t ω := by
  cases s <;> simp [lemma25TailSide, lrCoord]

/-- The restarted coordinate looking to the right of the vertex `x`. -/
def lemma25TailRight (ε : ℝ) (x : ℤ) (s : Bool) : ℝ≥0 → Path2 → ℝ :=
  lemma25TailProc (lemma25TailSide s) ε (ε * ((x : ℝ) - 1)) 1

/-- The restarted coordinate looking to the left of the vertex `x` (time reversed). -/
def lemma25TailLeft (ε : ℝ) (x : ℤ) (s : Bool) : ℝ≥0 → Path2 → ℝ :=
  lemma25TailProc (lemma25TailSide s) ε (ε * (x : ℝ)) (-1)

private theorem lemma25Tail_le_of_affine {a b c X q : ℝ} (hq : 0 < q)
    (h : max (X + q * a) (X + q * b) ≤ X + q * c) : max a b ≤ c := by
  have h1 := (le_max_left _ _).trans h
  have h2 := (le_max_right _ _).trans h
  refine max_le ?_ ?_ <;> nlinarith

/-- The side condition (1.1) for an edge from `x` to `x + b` is the counted-block condition of
the block `[b, b + 1]` for the coordinate restarted at `ε (x - 1)`. -/
theorem lemma25Tail_counted_right {ε : ℝ} (hε : 0 < ε) {ω : Path2} {x : ℤ} (s : Bool) {b : ℕ}
    (hb : 1 ≤ b) (h : SideCond ε (fun t => if s then (ω t).2 else (ω t).1) x (x + b)) :
    lemma25TailCounted (lemma25TailRight ε x s) b ω := by
  rw [lemma25TailSide_coord] at h
  set i := lemma25TailSide s
  set c : ℝ := ε * ((x : ℝ) - 1) with hc
  have hb' : (1 : ℝ≥0) ≤ b := by exact_mod_cast hb
  have hA := lemma25Tail_intervalInf_fwd (i := i) hε c ω (u := 0) (v := 1) zero_le_one
  have hB := lemma25Tail_intervalInf_fwd (i := i) hε c ω (u := b) (v := b + 1) le_self_add
  have hC := lemma25Tail_intervalInf_fwd (i := i) hε c ω (u := 1) (v := b) hb'
  have e0 : c + ε * ((0 : ℝ≥0) : ℝ) = ε * ((x : ℝ) - 1) := by simp [hc]
  have e1 : c + ε * ((1 : ℝ≥0) : ℝ) = ε * (x : ℝ) := by simp [hc]; ring
  have eb : c + ε * ((b : ℝ≥0) : ℝ) = ε * (((x + b : ℤ) : ℝ) - 1) := by
    simp [hc]; ring
  have eb1 : c + ε * (((b : ℝ≥0) + 1 : ℝ≥0) : ℝ) = ε * ((x + b : ℤ) : ℝ) := by
    simp [hc]; ring
  rw [e0, e1] at hA
  rw [eb, eb1] at hB
  rw [e1, eb] at hC
  unfold SideCond at h
  rw [hA, hB, hC] at h
  exact lemma25Tail_le_of_affine (Real.sqrt_pos.mpr hε) h

/-- The side condition (1.1) for an edge from `x - b` to `x` is the counted-block condition of
the block `[b, b + 1]` for the coordinate restarted at `ε x` and run backward in time. -/
theorem lemma25Tail_counted_left {ε : ℝ} (hε : 0 < ε) {ω : Path2} {x : ℤ} (s : Bool) {b : ℕ}
    (hb : 1 ≤ b) (h : SideCond ε (fun t => if s then (ω t).2 else (ω t).1) (x - b) x) :
    lemma25TailCounted (lemma25TailLeft ε x s) b ω := by
  rw [lemma25TailSide_coord] at h
  set i := lemma25TailSide s
  set c : ℝ := ε * (x : ℝ) with hc
  have hb' : (1 : ℝ≥0) ≤ b := by exact_mod_cast hb
  have hA := lemma25Tail_intervalInf_bwd (i := i) hε c ω (u := 0) (v := 1) zero_le_one
  have hB := lemma25Tail_intervalInf_bwd (i := i) hε c ω (u := b) (v := b + 1) le_self_add
  have hC := lemma25Tail_intervalInf_bwd (i := i) hε c ω (u := 1) (v := b) hb'
  have e0 : c - ε * ((0 : ℝ≥0) : ℝ) = ε * (x : ℝ) := by simp [hc]
  have e1 : c - ε * ((1 : ℝ≥0) : ℝ) = ε * ((x : ℝ) - 1) := by simp [hc]; ring
  have eb : c - ε * ((b : ℝ≥0) : ℝ) = ε * ((x - b : ℤ) : ℝ) := by
    simp [hc]; ring
  have eb1 : c - ε * (((b : ℝ≥0) + 1 : ℝ≥0) : ℝ) = ε * (((x - b : ℤ) : ℝ) - 1) := by
    simp [hc]; ring
  rw [e1, e0] at hA
  rw [eb1, eb] at hB
  rw [eb, e1] at hC
  unfold SideCond at h
  rw [hA, hB, hC, max_comm] at h
  exact lemma25Tail_le_of_affine (Real.sqrt_pos.mpr hε) h

/-! ### The degree as two plus four record-block counts -/

/-- **Degree decomposition.** The degree of `x` is at most `2` (the consecutive edges) plus the
four record-block counts (two coordinates, two directions). -/
theorem lemma25Degree_le_counts {ε : ℝ} (hε : 0 < ε) (ω : Path2) (x : ℤ) :
    lemma25Degree ε ω x ≤ 2 +
      ((lemma25TailCount (lemma25TailRight ε x false) ω +
          lemma25TailCount (lemma25TailRight ε x true) ω) +
        (lemma25TailCount (lemma25TailLeft ε x false) ω +
          lemma25TailCount (lemma25TailLeft ε x true) ω)) := by
  let R : Bool → Set ((ℤ × ℤ × Bool) × Bool) := fun s =>
    (fun b : ℕ => ((x, x + (b : ℤ), s), false)) ''
      {b : ℕ | 2 ≤ b ∧ lemma25TailCounted (lemma25TailRight ε x s) b ω}
  let L : Bool → Set ((ℤ × ℤ × Bool) × Bool) := fun s =>
    (fun b : ℕ => ((x - (b : ℤ), x, s), true)) ''
      {b : ℕ | 2 ≤ b ∧ lemma25TailCounted (lemma25TailLeft ε x s) b ω}
  have hsub : lemma25IncidentDarts ε ω x ⊆
      ({((x, x + 1, false), false), ((x - 1, x, false), true)} :
        Set ((ℤ × ℤ × Bool) × Bool)) ∪ ((R false ∪ R true) ∪ (L false ∪ L true)) := by
    rintro ⟨⟨a, y, s⟩, f⟩ ⟨hE, hx⟩
    obtain ⟨hay, hcases⟩ := hE
    cases f with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hx
      subst hx
      rcases hcases with ⟨hy, hs⟩ | ⟨hy, hside⟩
      · left
        simp only at hy hs
        subst hy
        subst hs
        exact Or.inl rfl
      · right
        left
        simp only at hay hy hside
        have hb2 : 2 ≤ (y - a).toNat := by omega
        have hyb : y = a + ((y - a).toNat : ℤ) := by omega
        rw [hyb] at hside
        have hcnt := lemma25Tail_counted_right hε s (by omega) hside
        have hmem : ((a, y, s), false) ∈ R s :=
          ⟨(y - a).toNat, ⟨hb2, hcnt⟩, by simp only; rw [← hyb]⟩
        cases s
        · exact Or.inl hmem
        · exact Or.inr hmem
    | true =>
      simp only [↓reduceIte] at hx
      subst hx
      rcases hcases with ⟨hy, hs⟩ | ⟨hy, hside⟩
      · left
        simp only at hy hs
        subst hs
        have ha : a = y - 1 := by omega
        subst ha
        exact Or.inr rfl
      · right
        right
        simp only at hay hy hside
        have hb2 : 2 ≤ (y - a).toNat := by omega
        have hab : a = y - ((y - a).toNat : ℤ) := by omega
        rw [hab] at hside
        have hcnt := lemma25Tail_counted_left hε s (by omega) hside
        have hmem : ((a, y, s), true) ∈ L s :=
          ⟨(y - a).toNat, ⟨hb2, hcnt⟩, by simp only; rw [← hab]⟩
        cases s
        · exact Or.inl hmem
        · exact Or.inr hmem
  have hpair : (({((x, x + 1, false), false), ((x - 1, x, false), true)} :
      Set ((ℤ × ℤ × Bool) × Bool))).encard ≤ 2 := by
    refine (Set.encard_insert_le _ _).trans ?_
    rw [Set.encard_singleton]
    norm_num
  have hR : ∀ s, (R s).encard ≤ lemma25TailCount (lemma25TailRight ε x s) ω := fun s =>
    Set.encard_image_le _ _
  have hL : ∀ s, (L s).encard ≤ lemma25TailCount (lemma25TailLeft ε x s) ω := fun s =>
    Set.encard_image_le _ _
  calc lemma25Degree ε ω x = (lemma25IncidentDarts ε ω x).encard := rfl
    _ ≤ (({((x, x + 1, false), false), ((x - 1, x, false), true)} :
          Set ((ℤ × ℤ × Bool) × Bool)) ∪ ((R false ∪ R true) ∪ (L false ∪ L true))).encard :=
        Set.encard_le_encard hsub
    _ ≤ _ := by
        refine (Set.encard_union_le _ _).trans (add_le_add hpair ?_)
        refine (Set.encard_union_le _ _).trans (add_le_add ?_ ?_)
        · exact (Set.encard_union_le _ _).trans (add_le_add (hR false) (hR true))
        · exact (Set.encard_union_le _ _).trans (add_le_add (hL false) (hL true))

/-! ### The degree tail -/

/-- The rate `c₁ = c / 4` of [18] Lemma 2.5 (`c = lemma25TailRate`; absolute). -/
def lemma25TailC₁ : ℝ := lemma25TailRate / 4

/-- The constant `c₀ = 48 e^{5c/4}` of [18] Lemma 2.5 (`c = lemma25TailRate`; absolute). -/
def lemma25TailC₀ : ℝ := 48 * Real.exp (5 * lemma25TailRate / 4)

theorem lemma25TailC₁_pos : 0 < lemma25TailC₁ := by
  unfold lemma25TailC₁
  linarith [lemma25TailRate_pos]

theorem lemma25TailC₀_pos : 0 < lemma25TailC₀ := by
  unfold lemma25TailC₀
  positivity

/-- The tail of one record-block count of the restarted coordinates. -/
theorem lemma25Tail_proc_count_tail {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {ε : ℝ} (hε : 0 < ε) (c : ℝ) {σ : ℝ} (hσ : |σ| = 1) (n : ℕ) :
    μ {ω | (n : ℕ∞) < lemma25TailCount (lemma25TailProc i ε c σ) ω} ≤
      ENNReal.ofReal (12 * Real.exp (-(lemma25TailRate * n))) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact lemma25Tail_count_tail (lemma25Tail_proc_isPreBrownianReal hμ i hε c hσ)
    (lemma25TailProc_measurable i ε c σ) (lemma25TailProc_continuous i ε c σ) n

/-- The degree exceeds `4 n + 2` with probability at most `48 e^{-c n}`. -/
theorem lemma25Tail_degree_tail_aux {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {ε : ℝ} (hε : 0 < ε) (x : ℤ) (n : ℕ) :
    μ {ω | ((4 * n + 2 : ℕ) : ℕ∞) < lemma25Degree ε ω x} ≤
      ENNReal.ofReal (48 * Real.exp (-(lemma25TailRate * n))) := by
  set Q : ℝ≥0∞ := ENNReal.ofReal (12 * Real.exp (-(lemma25TailRate * n)))
  have hσ1 : |(1 : ℝ)| = 1 := abs_one
  have hσ2 : |(-1 : ℝ)| = 1 := by norm_num
  have hcover : {ω | ((4 * n + 2 : ℕ) : ℕ∞) < lemma25Degree ε ω x} ⊆
      ({ω | (n : ℕ∞) < lemma25TailCount (lemma25TailRight ε x false) ω} ∪
        {ω | (n : ℕ∞) < lemma25TailCount (lemma25TailRight ε x true) ω}) ∪
      ({ω | (n : ℕ∞) < lemma25TailCount (lemma25TailLeft ε x false) ω} ∪
        {ω | (n : ℕ∞) < lemma25TailCount (lemma25TailLeft ε x true) ω}) := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hnot
    have hdeg := lemma25Degree_le_counts hε ω x
    have hsum : (2 : ℕ∞) + ((lemma25TailCount (lemma25TailRight ε x false) ω +
          lemma25TailCount (lemma25TailRight ε x true) ω) +
        (lemma25TailCount (lemma25TailLeft ε x false) ω +
          lemma25TailCount (lemma25TailLeft ε x true) ω)) ≤ ((4 * n + 2 : ℕ) : ℕ∞) := by
      calc (2 : ℕ∞) + ((lemma25TailCount (lemma25TailRight ε x false) ω +
            lemma25TailCount (lemma25TailRight ε x true) ω) +
          (lemma25TailCount (lemma25TailLeft ε x false) ω +
            lemma25TailCount (lemma25TailLeft ε x true) ω))
          ≤ 2 + (((n : ℕ∞) + n) + ((n : ℕ∞) + n)) := by gcongr
        _ = ((4 * n + 2 : ℕ) : ℕ∞) := by
          push_cast
          ring
    exact absurd (hω.trans_le (hdeg.trans hsum)) (lt_irrefl _)
  have hR := fun s => lemma25Tail_proc_count_tail hμ (lemma25TailSide s) hε
    (ε * ((x : ℝ) - 1)) hσ1 n
  have hL := fun s => lemma25Tail_proc_count_tail hμ (lemma25TailSide s) hε
    (ε * (x : ℝ)) hσ2 n
  calc μ {ω | ((4 * n + 2 : ℕ) : ℕ∞) < lemma25Degree ε ω x}
      ≤ μ (({ω | (n : ℕ∞) < lemma25TailCount (lemma25TailRight ε x false) ω} ∪
          {ω | (n : ℕ∞) < lemma25TailCount (lemma25TailRight ε x true) ω}) ∪
        ({ω | (n : ℕ∞) < lemma25TailCount (lemma25TailLeft ε x false) ω} ∪
          {ω | (n : ℕ∞) < lemma25TailCount (lemma25TailLeft ε x true) ω})) :=
        measure_mono hcover
    _ ≤ (Q + Q) + (Q + Q) := by
        refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
        · exact (measure_union_le _ _).trans (add_le_add (hR false) (hR true))
        · exact (measure_union_le _ _).trans (add_le_add (hL false) (hL true))
    _ = ENNReal.ofReal (48 * Real.exp (-(lemma25TailRate * n))) := by
        have h0 : 0 ≤ 12 * Real.exp (-(lemma25TailRate * n)) := by positivity
        simp only [Q]
        rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **[18] Lemma 2.5, raw-degree form, with absolute constants.** For every correlated
two-sided Brownian law (any `γ`), every mesh `ε > 0`, vertex `x ∈ ℤ` (the point `εx ∈ εℤ`) and
`n ∈ ℕ`, the degree of `x` in the ε-mated-CRT map exceeds `n` with probability at most
`c₀ e^{-c₁ n}`; `c₀ = lemma25TailC₀`, `c₁ = lemma25TailC₁` are absolute constants. -/
theorem lemma25Tail_degree_tail {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {ε : ℝ} (hε : 0 < ε) (x : ℤ) (n : ℕ) :
    μ {ω | (n : ℕ∞) < lemma25Degree ε ω x} ≤
      ENNReal.ofReal (lemma25TailC₀ * Real.exp (-(lemma25TailC₁ * n))) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hr := lemma25TailRate_pos
  by_cases hn : n < 2
  · calc μ {ω | (n : ℕ∞) < lemma25Degree ε ω x} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (lemma25TailC₀ * Real.exp (-(lemma25TailC₁ * n))) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hn' : (n : ℝ) ≤ 1 := by
          have : n ≤ 1 := by omega
          exact_mod_cast this
        have hexp : 1 ≤ Real.exp (5 * lemma25TailRate / 4) * Real.exp (-(lemma25TailC₁ * n)) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          unfold lemma25TailC₁
          nlinarith
        unfold lemma25TailC₀
        nlinarith
  · rw [not_lt] at hn
    set k : ℕ := (n - 2) / 4 with hk
    have hkn : 4 * k + 2 ≤ n := by omega
    have hnk : n ≤ 4 * k + 5 := by omega
    have hsub : {ω | (n : ℕ∞) < lemma25Degree ε ω x} ⊆
        {ω | ((4 * k + 2 : ℕ) : ℕ∞) < lemma25Degree ε ω x} := by
      intro ω hω
      have hle : ((4 * k + 2 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hkn
      exact lt_of_le_of_lt hle hω
    calc μ {ω | (n : ℕ∞) < lemma25Degree ε ω x}
        ≤ μ {ω | ((4 * k + 2 : ℕ) : ℕ∞) < lemma25Degree ε ω x} := measure_mono hsub
      _ ≤ ENNReal.ofReal (48 * Real.exp (-(lemma25TailRate * k))) :=
          lemma25Tail_degree_tail_aux hμ hε x k
      _ ≤ ENNReal.ofReal (lemma25TailC₀ * Real.exp (-(lemma25TailC₁ * n))) := by
          apply ENNReal.ofReal_le_ofReal
          have hnk' : (n : ℝ) ≤ 4 * k + 5 := by exact_mod_cast hnk
          have hexp : Real.exp (-(lemma25TailRate * k)) ≤
              Real.exp (5 * lemma25TailRate / 4) * Real.exp (-(lemma25TailC₁ * n)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            unfold lemma25TailC₁
            nlinarith
          unfold lemma25TailC₀
          nlinarith [Real.exp_pos (-(lemma25TailRate * k))]

/-- **[18] Lemma 2.5** (Gwynne--Miller, *Harmonic functions on mated-CRT maps*). Let `γ ∈ (0, 2)`. There are constants
`c₀, c₁ > 0`, depending only on `γ`, such that for the law `μ` of the correlated two-sided
Brownian motion of [18] §1.1, every `n ∈ ℕ`, `ε > 0` and `x ∈ εℤ` (the vertex `x : ℤ`),
`P[deg(x; G^ε) > n] ≤ c₀ e^{-c₁ n}`. The ε-mated-CRT map `G^ε = graph ε ω h` exists on the
almost sure event `h : IsLocallyFinite ε ω` (`ae_isLocallyFinite`). (The constants are in fact
absolute: `lemma25Tail_degree_tail`.) -/
theorem lemma25_degree_tail_holds (γ : ℝ) (_hγ0 : 0 < γ) (_hγ2 : γ < 2) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∀ x : ℤ,
        μ {ω | ∃ h : IsLocallyFinite ε ω, n < LFMultigraph.deg (graph ε ω h) x} ≤
          ENNReal.ofReal (c₀ * Real.exp (-(c₁ * n))) := by
  refine ⟨lemma25TailC₀, lemma25TailC₁, lemma25TailC₀_pos, lemma25TailC₁_pos, ?_⟩
  intro μ hμ n ε hε x
  refine le_trans (measure_mono ?_) (lemma25Tail_degree_tail hμ hε x n)
  rintro ω ⟨h, hdeg⟩
  change (n : ℕ∞) < lemma25Degree ε ω x
  rw [lemma25Degree_eq_graph_deg h]
  exact_mod_cast hdeg

/-! ### Moments of the degree -/

private theorem lemma25Tail_pow_le_tsum (d : ℕ∞) {k : ℕ} (hk : 1 ≤ k) :
    ((d : ℝ≥0∞)) ^ k ≤
      ∑' n : ℕ, ((n : ℝ≥0∞) + 1) ^ k * {e : ℕ∞ | (n : ℕ∞) < e}.indicator 1 d := by
  induction d using ENat.recTopCoe with
  | top =>
    have hterm : ∀ n : ℕ, (1 : ℝ≥0∞) ≤
        ((n : ℝ≥0∞) + 1) ^ k * {e : ℕ∞ | (n : ℕ∞) < e}.indicator 1 (⊤ : ℕ∞) := by
      intro n
      rw [Set.indicator_of_mem (show (⊤ : ℕ∞) ∈ {e : ℕ∞ | (n : ℕ∞) < e} from
        ENat.natCast_lt_top n), Pi.one_apply, mul_one]
      exact one_le_pow₀ le_add_self
    have htop : ∑' n : ℕ, ((n : ℝ≥0∞) + 1) ^ k *
        {e : ℕ∞ | (n : ℕ∞) < e}.indicator 1 (⊤ : ℕ∞) = ⊤ := by
      refine top_unique ?_
      calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero
            one_ne_zero).symm
        _ ≤ _ := ENNReal.tsum_le_tsum hterm
    rw [htop]
    exact le_top
  | coe d =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have h0 : (((0 : ℕ) : ℕ∞) : ℝ≥0∞) = 0 := by simp
      rw [h0, zero_pow (n := k) (by omega)]
      exact zero_le
    · obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
      have hmem : ((m + 1 : ℕ) : ℕ∞) ∈ {e : ℕ∞ | (m : ℕ∞) < e} := by
        change (m : ℕ∞) < ((m + 1 : ℕ) : ℕ∞)
        exact_mod_cast Nat.lt_succ_self m
      calc (((m + 1 : ℕ) : ℕ∞) : ℝ≥0∞) ^ k
          = ((m : ℝ≥0∞) + 1) ^ k *
              {e : ℕ∞ | (m : ℕ∞) < e}.indicator 1 ((m + 1 : ℕ) : ℕ∞) := by
            rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
            push_cast
            rfl
        _ ≤ _ := ENNReal.le_tsum (f := fun n : ℕ => ((n : ℝ≥0∞) + 1) ^ k *
              {e : ℕ∞ | (n : ℕ∞) < e}.indicator 1 ((m + 1 : ℕ) : ℕ∞)) m

/-- **Finite moments of the degree.** For every `k`, `E[deg(x; G^ε)^k] < ∞`, uniformly
summable from the exponential tail (`lemma25Tail_degree_tail`). -/
theorem lemma25Tail_lintegral_degree_pow_lt_top {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {ε : ℝ} (hε : 0 < ε) (x : ℤ) (k : ℕ) :
    ∫⁻ ω, ((lemma25Degree ε ω x : ℕ∞) : ℝ≥0∞) ^ k ∂μ < ⊤ := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  set c₀ := lemma25TailC₀
  set c₁ := lemma25TailC₁
  have hc₁ : 0 < c₁ := lemma25TailC₁_pos
  have hc₀ : 0 < c₀ := lemma25TailC₀_pos
  set f : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ k * (c₀ * Real.exp (-(c₁ * n))) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hfsum : Summable f := by
    have h1 := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul k hc₁)
    have h2 := h1.mul_left (c₀ * Real.exp c₁)
    refine h2.congr fun n => ?_
    simp only [hf]
    push_cast
    rw [show -(c₁ * (n : ℝ)) = c₁ + -c₁ * ((n : ℝ) + 1) by ring, Real.exp_add]
    ring
  have hmeas : ∀ n : ℕ, MeasurableSet {ω : Path2 | (n : ℕ∞) < lemma25Degree ε ω x} :=
    fun n => measurable_lemma25Degree ε x (MeasurableSet.of_discrete (s := Ioi (n : ℕ∞)))
  calc ∫⁻ ω, ((lemma25Degree ε ω x : ℕ∞) : ℝ≥0∞) ^ k ∂μ
      ≤ ∫⁻ ω, ∑' n : ℕ, ((n : ℝ≥0∞) + 1) ^ k *
          {ω : Path2 | (n : ℕ∞) < lemma25Degree ε ω x}.indicator 1 ω ∂μ := by
        refine lintegral_mono fun ω => ?_
        exact lemma25Tail_pow_le_tsum (lemma25Degree ε ω x) hk
    _ = ∑' n : ℕ, ((n : ℝ≥0∞) + 1) ^ k * μ {ω | (n : ℕ∞) < lemma25Degree ε ω x} := by
        rw [lintegral_tsum (f := fun (n : ℕ) ω => ((n : ℝ≥0∞) + 1) ^ k *
          {ω : Path2 | (n : ℕ∞) < lemma25Degree ε ω x}.indicator 1 ω) fun n =>
          ((measurable_one.indicator (hmeas n)).const_mul _).aemeasurable]
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul _ (measurable_one.indicator (hmeas n)),
          lintegral_indicator_one (hmeas n)]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (f n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        have hpow : ((n : ℝ≥0∞) + 1) ^ k = ENNReal.ofReal (((n : ℝ) + 1) ^ k) := by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
            ENNReal.ofReal_natCast, ENNReal.ofReal_one]
        rw [hpow, hf, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact lemma25Tail_degree_tail hμ hε x n
    _ = ENNReal.ofReal (∑' n, f n) := (ENNReal.ofReal_tsum_of_nonneg hf0 hfsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end MatedCRTHarmonic.MatedCRT
