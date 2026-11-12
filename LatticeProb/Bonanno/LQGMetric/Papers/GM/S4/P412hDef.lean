/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hDef at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eStep3
import Mathlib.Data.Rat.Denumerable

/-!
# GM L4.14 with canonical choices (D98 §2, packet P-L414B): the data

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.14 (`lem-dc-set`,
l. 2097–2102), proof l. 2457–2520 (repaired in DEC-86 (1), formalized as `p412d_GML4_14`);
decision D98 §2 (decisions/DEC-98.md): the four choices of that proof made canonical.

* `p412hG ε m` — the grid `(ε/8)ℤ²` (GM l. 2477 use `(ε/4)ℤ²`);
* `p412hT K ε` — the net `T = {m | B̄_{3ε+ε/8}(g_m) ∩ K ≠ ∅}` (finite: `p412h_T_finite`; an
  `ε/4`-net of `cthickening (3ε) K`: `p412h_T_cover`);
* `p412hRho K y ε` — the radius `ρ = ρ_j`, `ρ_j = 3ε/2 + ε/(2(j+1))`, `j` least with
  `y ∉ ∂B_{ρ_j}(g_m)` for all `m ∈ T` (`p412h_rho`);
* `p412hIx` — an enumeration of `ℤ² × ℚ`; index `i ↦` centre `g_m` and the point
  `g_m + ρe^{2πiθ}` of rational angle (every arc of `∂B ∖ K` contains one: `p412h_rat_pt`);
* `p412hMx K y ε i` — `i` is admissible (`p412hOK`, the conditions of the family `F` of
  `p412d_GML4_14`) and its bounded side `p412hBs` is maximal among admissible ones;
* **`p412hGd K y ε`** — the output function `gd(K, y)`: the centre of the least maximal index
  (a fixed grid point if there is none).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut

namespace LQGMetric.GM

/-- the grid `(ε/8)ℤ²` -/
def p412hG (ε : ℝ) (m : ℤ × ℤ) : ℂ := ((ε / 8 : ℝ) : ℂ) * ((m.1 : ℂ) + (m.2 : ℂ) * Complex.I)

/-- the net `T` of grid points within `3ε + ε/8` of `K` -/
def p412hT (K : Set ℂ) (ε : ℝ) : Set (ℤ × ℤ) :=
  {m | (closedBall (p412hG ε m) (3 * ε + ε / 8) ∩ K).Nonempty}

/-- the candidate radii `ρ_j ∈ (3ε/2, 2ε]` -/
def p412hRad (ε : ℝ) (j : ℕ) : ℝ := 3 / 2 * ε + ε / (2 * ((j : ℝ) + 1))

/-- `ρ_j` avoids all distances `|y − g_m|`, `m ∈ T` -/
def p412hRhoOK (K : Set ℂ) (y : ℂ) (ε : ℝ) (j : ℕ) : Prop :=
  ∀ m ∈ p412hT K ε, dist y (p412hG ε m) ≠ p412hRad ε j

open Classical in
/-- the radius `ρ`: least admissible `ρ_j` -/
def p412hRho (K : Set ℂ) (y : ℂ) (ε : ℝ) : ℝ :=
  if h : ∃ j, p412hRhoOK K y ε j then p412hRad ε (Nat.find h)
  else 2 * ε

/-- the point of angle `2πθ` on `∂B_ρ(c)` -/
def p412hPt (c : ℂ) (ρ θ : ℝ) : ℂ := c + (ρ : ℂ) * Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)

/-- enumeration of `ℤ² × ℚ` -/
def p412hIx (i : ℕ) : (ℤ × ℤ) × ℚ := Denumerable.ofNat ((ℤ × ℤ) × ℚ) i

/-- centre of the index `i` -/
def p412hC (ε : ℝ) (i : ℕ) : ℂ := p412hG ε (p412hIx i).1

/-- the point of rational angle of the index `i`, on `∂B_ρ(c_i)` -/
def p412hY (ε ρ : ℝ) (i : ℕ) : ℂ := p412hPt (p412hC ε i) ρ ((p412hIx i).2 : ℝ)

/-- the conditions of the family `F` in `p412d_GML4_14` for the arc `cc(∂B_ρ(c) ∖ K, y₀)` -/
def p412hArc (K : Set ℂ) (y : ℂ) (ρ : ℝ) (c y₀ : ℂ) : Prop :=
  y₀ ∈ sphere c ρ ∧ y₀ ∉ K ∧
    connectedComponentIn (sphere c ρ \ K) y₀ ⊆ closure (dgW (closedBall c ρ ∪ K)) ∧
    y ∈ closure (dgB (connectedComponentIn (sphere c ρ \ K) y₀ ∪ K))

/-- bounded side `U(α)` of the arc `α = cc(∂B_ρ(c) ∖ K, y₀)` -/
def p412hBs (K : Set ℂ) (ρ : ℝ) (c y₀ : ℂ) : Set ℂ :=
  dgB (connectedComponentIn (sphere c ρ \ K) y₀ ∪ K)

/-- admissible index -/
def p412hOK (K : Set ℂ) (y : ℂ) (ε : ℝ) (i : ℕ) : Prop :=
  (p412hIx i).1 ∈ p412hT K ε ∧
    p412hArc K y (p412hRho K y ε) (p412hC ε i) (p412hY ε (p412hRho K y ε) i)

/-- admissible index with maximal bounded side -/
def p412hMx (K : Set ℂ) (y : ℂ) (ε : ℝ) (i : ℕ) : Prop :=
  p412hOK K y ε i ∧ ∀ j, p412hOK K y ε j →
    p412hBs K (p412hRho K y ε) (p412hC ε i) (p412hY ε (p412hRho K y ε) i) ⊆
      p412hBs K (p412hRho K y ε) (p412hC ε j) (p412hY ε (p412hRho K y ε) j) →
    p412hBs K (p412hRho K y ε) (p412hC ε j) (p412hY ε (p412hRho K y ε) j) ⊆
      p412hBs K (p412hRho K y ε) (p412hC ε i) (p412hY ε (p412hRho K y ε) i)

open Classical in
/-- **the output function `gd(K, y)`** (D98 §2) -/
def p412hGd (K : Set ℂ) (y : ℂ) (ε : ℝ) : ℂ :=
  if h : ∃ i, p412hMx K y ε i then p412hC ε (Nat.find h)
  else p412hG ε (0, 0)

/-! ### elementary properties -/

theorem p412h_norm_pt (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : ‖p412hPt c ρ θ - c‖ = ρ := by
  rw [p412hPt, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]

theorem p412h_pt_mem (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : p412hPt c ρ θ ∈ sphere c ρ := by
  rw [mem_sphere, dist_eq_norm, p412h_norm_pt c hρ]

theorem p412h_Ix_surj (m : ℤ × ℤ) (θ : ℚ) : ∃ i, p412hIx i = (m, θ) :=
  ⟨(Denumerable.eqv ((ℤ × ℤ) × ℚ)) (m, θ), (Denumerable.eqv ((ℤ × ℤ) × ℚ)).symm_apply_apply _⟩

/-- every component of `∂B_ρ(c) ∖ K` contains a point of rational angle -/
theorem p412h_rat_pt {K : Set ℂ} (hK : IsClosed K) (hKne : K.Nonempty) {c y₀ : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hy₀ : y₀ ∈ sphere c ρ) (hy₀K : y₀ ∉ K) :
    ∃ θ : ℚ, p412hPt c ρ θ ∈ connectedComponentIn (sphere c ρ \ K) y₀ := by
  obtain ⟨δ, hδ, hsub⟩ := cc_sphere_open hK hKne hρ hy₀ hy₀K
  have hcont : Continuous (p412hPt c ρ) := by unfold p412hPt; fun_prop
  have hφ : p412hPt c ρ (Complex.arg (y₀ - c) / (2 * Real.pi)) = y₀ := by
    have hn : ‖y₀ - c‖ = ρ := by rw [← dist_eq_norm]; exact mem_sphere.1 hy₀
    have h2 : (2 * Real.pi * (Complex.arg (y₀ - c) / (2 * Real.pi))) = Complex.arg (y₀ - c) := by
      field_simp
    rw [p412hPt, h2, ← hn, Complex.norm_mul_exp_arg_mul_I]; ring
  obtain ⟨θ, hθ⟩ := Rat.denseRange_cast.exists_mem_open
    ((isOpen_ball (x := y₀) (ε := δ)).preimage hcont)
    ⟨_, show p412hPt c ρ _ ∈ ball y₀ δ by rw [hφ]; exact mem_ball_self hδ⟩
  exact ⟨θ, hsub ⟨hθ, p412h_pt_mem c hρ.le _⟩⟩

theorem p412h_rad_mem {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    3 / 2 * ε < p412hRad ε j ∧ p412hRad ε j ≤ 2 * ε := by
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := j.cast_nonneg (α := ℝ); linarith
  constructor
  · unfold p412hRad; have : 0 < ε / (2 * ((j : ℝ) + 1)) := by positivity
    linarith
  · unfold p412hRad
    have : ε / (2 * ((j : ℝ) + 1)) ≤ ε / 2 := div_le_div_of_nonneg_left hε.le (by norm_num)
      (by linarith)
    linarith

theorem p412h_rad_inj {ε : ℝ} (hε : 0 < ε) : Function.Injective (p412hRad ε) := by
  intro i j h
  unfold p412hRad at h
  have h' : ε / (2 * ((i : ℝ) + 1)) = ε / (2 * ((j : ℝ) + 1)) := by linarith
  rw [div_eq_div_iff (by positivity) (by positivity)] at h'
  have : ((i : ℝ) + 1) = (j : ℝ) + 1 := by nlinarith
  exact_mod_cast (by linarith : (i : ℝ) = j)

/-- `T` is finite -/
theorem p412h_T_finite {K : Set ℂ} (hK : IsBounded K) {ε : ℝ} (hε : 0 < ε) :
    (p412hT K ε).Finite := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK
  set N : ℤ := ⌈8 / ε * (R + 4 * ε)⌉
  refine ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset fun m hm => ?_
  obtain ⟨k, hkB, hkK⟩ := hm
  have hg : ‖p412hG ε m‖ ≤ R + 4 * ε := by
    have := hR k hkK
    have h2 := mem_closedBall.1 hkB
    rw [dist_eq_norm] at h2
    have := norm_sub_norm_le (p412hG ε m) k
    have := norm_sub_rev k (p412hG ε m)
    linarith
  have hz : ‖((m.1 : ℂ) + (m.2 : ℂ) * Complex.I)‖ ≤ 8 / ε * (R + 4 * ε) := by
    rw [p412hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hg
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
  have hre : |(m.1 : ℝ)| ≤ 8 / ε * (R + 4 * ε) := by
    have := Complex.abs_re_le_norm ((m.1 : ℂ) + (m.2 : ℂ) * Complex.I)
    simp at this; linarith
  have him : |(m.2 : ℝ)| ≤ 8 / ε * (R + 4 * ε) := by
    have := Complex.abs_im_le_norm ((m.1 : ℂ) + (m.2 : ℂ) * Complex.I)
    simp at this; linarith
  have hN : 8 / ε * (R + 4 * ε) ≤ (N : ℝ) := Int.le_ceil _
  have h1 := abs_le.1 (hre.trans hN)
  have h2 := abs_le.1 (him.trans hN)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [skip; skip; skip; skip] <;>
    first | exact_mod_cast h1.1 | exact_mod_cast h1.2 | exact_mod_cast h2.1 | exact_mod_cast h2.2

end LQGMetric.GM
