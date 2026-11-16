import LatticeProb.Analysis.Schauder.UnitCube
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.MaxPrinciple`.

# The weak maximum principle on the unit cube

If `u ∈ C²(ℝ^d)` vanishes on the boundary of `Q = (0,1)^d` and `|Δu| ≤ K` on `Q`, then
`|u| ≤ K/8` on `Q̄`: compare `±u` with the barrier `K|z − z₀|²/(2d)` plus a small strictly
subharmonic correction, and use the second-derivative test at an interior maximum.
-/

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace LatticeProb.Analysis.Schauder

/-- The centre of the unit cube exists in `Euc d`, with all coordinates equal to `1/2`. -/
theorem exists_euc_const_half (d : ℕ) : ∃ z₀ : Euc d, ∀ i, z₀ i = 1 / 2 :=
  ⟨WithLp.toLp 2 fun _ => (1 / 2 : ℝ), fun _ => rfl⟩

variable {d : ℕ}

/-- The second derivative of a real function with a local maximum is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {a : ℝ} (hg : IsLocalMax g a)
    (hc : ContinuousAt g a) : deriv (deriv g) a ≤ 0 := by
  by_contra h
  push Not at h
  have hmin := isLocalMin_of_deriv_deriv_pos h hg.deriv_eq_zero hc
  have hconst : g =ᶠ[𝓝 a] fun _ => g a := by
    filter_upwards [hg, hmin] with t h1 h2 using le_antisymm h1 h2
  have h1 : deriv g =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
    simpa using hconst.deriv
  have h2 : deriv (deriv g) a = 0 := by
    simpa using h1.deriv_eq
  linarith

/-- The restriction of a `C²` function to the line `s ↦ z + s v` has derivative
`D w (z + t v) v`. -/
theorem hasDerivAt_comp_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E → ℝ} (hw : ContDiff ℝ 2 w) (z v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => w (z + s • v)) (fderiv ℝ w (z + t • v) v) t := by
  have hline : HasDerivAt (fun s : ℝ => z + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  exact ((hw.differentiable (by norm_num)) (z + t • v)).hasFDerivAt.comp_hasDerivAt t hline

/-- The map `t ↦ D w (z + t v) v` has derivative `D² w z (v, v)` at `t = 0`. -/
theorem hasDerivAt_fderiv_comp_add_smul_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {w : E → ℝ} (hw : ContDiff ℝ 2 w) (z v : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ w (z + t • v) v) (fderiv ℝ (fderiv ℝ w) z v v) 0 := by
  have hline : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hw2 : Differentiable ℝ (fderiv ℝ w) :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := ((hw2 (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline)
  simp only [zero_smul, add_zero] at h
  have := h.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using this

/-- The second derivative of a `C²` function in the direction `v` is the second derivative at `0`
of its restriction to the line `s ↦ z + s v`. -/
theorem iteratedFDeriv_two_eq_deriv_deriv_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {w : E → ℝ} (hw : ContDiff ℝ 2 w) (z v : E) :
    iteratedFDeriv ℝ 2 w z ![v, v] = deriv (deriv (fun s : ℝ => w (z + s • v))) 0 := by
  have hg1' : deriv (fun s : ℝ => w (z + s • v)) = fun t => fderiv ℝ w (z + t • v) v :=
    funext fun t => (hasDerivAt_comp_add_smul hw z v t).deriv
  rw [hg1', (hasDerivAt_fderiv_comp_add_smul_zero hw z v).deriv]
  simp [iteratedFDeriv_two_apply]

/-- The second derivative of a `C²` function with a local maximum is nonpositive in every
direction. -/
theorem iteratedFDeriv_two_self_nonpos_of_isLocalMax {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {w : E → ℝ} (hw : ContDiff ℝ 2 w) {z : E} (hz : IsLocalMax w z) (v : E) :
    iteratedFDeriv ℝ 2 w z ![v, v] ≤ 0 := by
  have hcont : Tendsto (fun s : ℝ => z + s • v) (𝓝 0) (𝓝 z) := by
    have : Continuous (fun s : ℝ => z + s • v) := by fun_prop
    simpa using this.tendsto 0
  have hmax : IsLocalMax (fun s : ℝ => w (z + s • v)) 0 := by
    refine (hcont.eventually hz).mono fun s hs => ?_
    simpa using hs
  have hc : ContinuousAt (fun s : ℝ => w (z + s • v)) 0 :=
    (hasDerivAt_comp_add_smul hw z v 0).continuousAt
  rw [iteratedFDeriv_two_eq_deriv_deriv_line hw z v]
  exact deriv_deriv_nonpos_of_isLocalMax hmax hc

/-- The second derivative of `y ↦ ‖y - z₀‖²` in the direction `v` is `2 ‖v‖²`. -/
theorem iteratedFDeriv_two_norm_sq_sub (z₀ z v : Euc d) :
    iteratedFDeriv ℝ 2 (fun y : Euc d => ‖y - z₀‖ ^ 2) z ![v, v] = 2 * ‖v‖ ^ 2 := by
  have hq : ContDiff ℝ 2 (fun y : Euc d => ‖y - z₀‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  rw [iteratedFDeriv_two_eq_deriv_deriv_line hq z v]
  have hg : (fun s : ℝ => ‖z + s • v - z₀‖ ^ 2) =
      fun s => ‖z - z₀‖ ^ 2 + 2 * inner ℝ (z - z₀) v * s + ‖v‖ ^ 2 * s ^ 2 := by
    funext s
    have h : z + s • v - z₀ = (z - z₀) + s • v := by abel
    rw [h, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h1 : deriv (fun s : ℝ => ‖z - z₀‖ ^ 2 + 2 * inner ℝ (z - z₀) v * s + ‖v‖ ^ 2 * s ^ 2) =
      fun s => 2 * inner ℝ (z - z₀) v + ‖v‖ ^ 2 * (2 * s) := by
    funext s
    have h2 := (((hasDerivAt_id s).const_mul (2 * inner ℝ (z - z₀) v)).const_add
      (‖z - z₀‖ ^ 2)).add (((hasDerivAt_id s).pow 2).const_mul (‖v‖ ^ 2))
    exact (h2.congr_deriv (by simp)).deriv
  simp only [hg]
  rw [h1]
  have h3 := (((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_mul (‖v‖ ^ 2)).const_add
    (2 * inner ℝ (z - z₀) v)
  exact h3.deriv.trans (by simp; ring)

/-- **Strict maximum principle on the cube**: a `C²` function with strictly positive Laplacian in
`Q` attains its maximum over `Q̄` on `∂Q`. -/
theorem exists_isMaxOn_boundary_of_pos_laplacian (w : Euc d → ℝ) (hw : ContDiff ℝ 2 w)
    (hpos : ∀ z ∈ unitCube d,
      0 < ∑ i, iteratedFDeriv ℝ 2 w z ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]) :
    ∃ z ∈ closure (unitCube d) \ unitCube d, ∀ y ∈ closure (unitCube d), w y ≤ w z := by
  obtain ⟨z₀, hz₀⟩ := exists_euc_const_half d
  have hne : (closure (unitCube d)).Nonempty :=
    ⟨z₀, subset_closure fun i => by simp [hz₀]; norm_num⟩
  obtain ⟨z, hz, hmax⟩ :=
    isCompact_closure_unitCube.exists_isMaxOn hne hw.continuous.continuousOn
  refine ⟨z, ⟨hz, fun hzQ => ?_⟩, fun y hy => isMaxOn_iff.mp hmax y hy⟩
  have hloc : IsLocalMax w z :=
    hmax.isLocalMax (Filter.mem_of_superset (isOpen_unitCube.mem_nhds hzQ) subset_closure)
  have hle : ∑ i, iteratedFDeriv ℝ 2 w z
      ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] ≤ 0 :=
    Finset.sum_nonpos fun i _ => iteratedFDeriv_two_self_nonpos_of_isLocalMax hw hloc _
  linarith [hpos z hzQ]

/-- On the closure of the unit cube, `‖z - z₀‖² ≤ d / 4` for the centre `z₀`. -/
theorem norm_sq_sub_centre_le {z₀ z : Euc d} (hz₀ : ∀ i, z₀ i = 1 / 2)
    (hz : z ∈ closure (unitCube d)) : ‖z - z₀‖ ^ 2 ≤ d / 4 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc ∑ i, (z - z₀) i ^ 2 ≤ ∑ _i : Fin d, (1 / 4 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := coord_mem_Icc_of_mem_closure_unitCube hz i
        simp only [PiLp.sub_apply, hz₀]
        nlinarith [h.1, h.2]
    _ = d / 4 := by simp; ring

/-- **One-sided weak maximum principle on the unit cube**: if `u ∈ C²` vanishes on `∂Q` and
`Δu ≥ -K` on `Q`, then `u ≤ K / 8` on `Q̄`. -/
theorem le_div_eight_of_neg_le_laplacian (hd : 1 ≤ d) (u : Euc d → ℝ) (hu : ContDiff ℝ 2 u)
    (K : ℝ) (hK : 0 ≤ K) (hzero : ∀ z ∈ closure (unitCube d) \ unitCube d, u z = 0)
    (hlap : ∀ z ∈ unitCube d,
      -K ≤ ∑ i, iteratedFDeriv ℝ 2 u z ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]) :
    ∀ z ∈ closure (unitCube d), u z ≤ K / 8 := by
  obtain ⟨z₀, hz₀⟩ := exists_euc_const_half d
  intro y hy
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set c : ℝ := K / (2 * d) + 4 * δ / d with hc
  have hc0 : 0 ≤ c := by positivity
  have hcd : c * d / 4 = K / 8 + δ := by
    rw [hc]; field_simp; ring
  have hq : ContDiff ℝ 2 (fun z : Euc d => ‖z - z₀‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hw : ContDiff ℝ 2 (fun z : Euc d => u z + c • ‖z - z₀‖ ^ 2) :=
    hu.add (hq.const_smul c)
  have hpos : ∀ x ∈ unitCube d, 0 < ∑ i, iteratedFDeriv ℝ 2
      (fun z : Euc d => u z + c • ‖z - z₀‖ ^ 2) x
      ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] := by
    intro x hx
    have key : ∀ i : Fin d, iteratedFDeriv ℝ 2 (fun z : Euc d => u z + c • ‖z - z₀‖ ^ 2) x
        ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] =
        iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]
          + c * 2 := by
      intro i
      rw [fun_iteratedFDeriv_add_apply hu.contDiffAt (hq.const_smul c).contDiffAt,
        iteratedFDeriv_const_smul_apply' hq.contDiffAt]
      simp [iteratedFDeriv_two_norm_sq_sub]
    simp only [key, Finset.sum_add_distrib]
    have h2 : ∑ _i : Fin d, c * 2 = K + 8 * δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hc]; field_simp; ring
    rw [h2]
    linarith [hlap x hx]
  obtain ⟨z, hz, hmax⟩ := exists_isMaxOn_boundary_of_pos_laplacian _ hw hpos
  have h1 : u z = 0 := hzero z hz
  have h2 : c * ‖z - z₀‖ ^ 2 ≤ c * (d / 4) :=
    mul_le_mul_of_nonneg_left (norm_sq_sub_centre_le hz₀ hz.1) hc0
  have h3 := hmax y hy
  have h4 : 0 ≤ c * ‖y - z₀‖ ^ 2 := by positivity
  simp only [smul_eq_mul, h1] at h3
  linarith

/-- **The weak maximum principle on the unit cube**: if `u ∈ C²(ℝ^d)` vanishes on `∂Q` and
`|Δu| ≤ K` on `Q = (0,1)^d`, then `|u| ≤ K/8` on `Q̄` (compare `±u` with the barrier
`K |z − z₀|²/(2d)`, `z₀` the centre, `|z − z₀|² ≤ d/4` on `Q̄`). -/
theorem abs_le_of_abs_laplacian_le (hd : 1 ≤ d) (u : Euc d → ℝ) (hu : ContDiff ℝ 2 u) (K : ℝ)
    (hzero : ∀ z ∈ closure (unitCube d) \ unitCube d, u z = 0)
    (hlap : ∀ z ∈ unitCube d,
      |∑ i, iteratedFDeriv ℝ 2 u z ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]| ≤ K) :
    ∀ z ∈ closure (unitCube d), |u z| ≤ K / 8 := by
  obtain ⟨z₀, hz₀⟩ := exists_euc_const_half d
  have hz₀Q : z₀ ∈ unitCube d := fun i => by simp [hz₀]; norm_num
  have hK : 0 ≤ K := (abs_nonneg _).trans (hlap z₀ hz₀Q)
  intro z hz
  have h1 := le_div_eight_of_neg_le_laplacian hd u hu K hK hzero
    (fun x hx => (abs_le.mp (hlap x hx)).1) z hz
  have h2 := le_div_eight_of_neg_le_laplacian hd (-u) hu.neg K hK
    (fun x hx => by simp [hzero x hx]) (fun x hx => by
      have := (abs_le.mp (hlap x hx)).2
      simp [iteratedFDeriv_neg_apply, Finset.sum_neg_distrib]
      linarith) z hz
  rw [Pi.neg_apply] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

end LatticeProb.Analysis.Schauder

end
