/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordsAux3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux2
import Mathlib.Data.Int.Log

/-!
# Records (node `R44`), auxiliary part 3: grids at dyadic scales, chord geometry

A chord `[x, y]` of length `R` gets the dyadic scale exponent `σ = ⌊log₂ R⌋` (so
`2^σ ≤ R < 2^{σ+1}`) and the square grid of side `η δ 2^σ`, `η = M⁻²`.  Its *location* is
`(σ, cell(x), cell(y))`.  The normalizing similarity of a location sends `0, 1` to the lower-left
corners of the two cells.  This file proves the geometric facts relating actual chords to their
locations: the normalized cell radius is at most `cellRad M * δ = 4 η δ`, scales separate by
`4 / M` from parent to child, and followed children are close to the corresponding straight
positions.
-/

noncomputable section

open Real
open scoped Classical

namespace LQGDimension.LFPPRecords

open Blueprint.Draft

/-! ## Parameters -/

/-- `M = 16 ^ n`. -/
abbrev Mn (n : ℕ) : ℕ := 16 ^ n

theorem Mn_pos (n : ℕ) : (0 : ℝ) < (Mn n : ℝ) := by positivity

theorem Mn_ge_sixteen {n : ℕ} (hn : 1 ≤ n) : (16 : ℝ) ≤ (Mn n : ℝ) := by
  have : 16 ≤ 16 ^ n := by
    calc 16 = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact_mod_cast this

theorem four_n_add_three_le : ∀ n : ℕ, 1 ≤ n → 4 * n + 3 ≤ 16 ^ n
  | 0, h => absurd h (by norm_num)
  | 1, _ => by norm_num
  | n + 2, _ => by
    have := four_n_add_three_le (n + 1) (by omega)
    rw [pow_succ]; omega

theorem two_zpow_eq (n : ℕ) : (2 : ℝ) ^ (4 * (n : ℤ) + 2) = 4 * (Mn n : ℝ) := by
  have e : (4 * (n : ℤ) + 2) = ((4 * n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_natCast, pow_add, pow_mul]
  push_cast
  norm_num
  ring

/-- Grid side `η δ 2^σ` (`η = M⁻²`) at scale exponent `σ`. -/
def side (n : ℕ) (δ : ℝ) (σ : ℤ) : ℝ := δ / (Mn n : ℝ) ^ 2 * (2 : ℝ) ^ σ

theorem side_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (σ : ℤ) : 0 < side n δ σ := by
  unfold side; have := Mn_pos n; positivity

theorem side_mono {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) {σ σ' : ℤ} (h : σ ≤ σ') :
    side n δ σ ≤ side n δ σ' := by
  unfold side
  have := Mn_pos n
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) h) (by positivity)

theorem eta_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ1 : δ < 1) : δ / (Mn n : ℝ) ^ 2 ≤ 1 / 256 := by
  have h16 := Mn_ge_sixteen hn
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem eta_nonneg (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ δ / (Mn n : ℝ) ^ 2 := by
  have := Mn_pos n; positivity

theorem side_eq (n : ℕ) (δ : ℝ) (σ : ℤ) : side n δ σ = δ / (Mn n : ℝ) ^ 2 * (2 : ℝ) ^ σ := rfl

theorem one_le_sqrt_succ (k : ℕ) : (1 : ℝ) ≤ √((k : ℝ) + 1) := by
  apply Real.le_sqrt_of_sq_le
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem sqrt_succ_le (k : ℕ) : √((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
  have h : (1 : ℝ) ≤ (k : ℝ) + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-! ## Locations -/

/-- A location: a dyadic scale exponent and the grid cells of the two endpoints. -/
abbrev Loc := ℤ × (ℤ × ℤ) × (ℤ × ℤ)

/-- Record data: current location, (bin, large-excess flag), location of the followed child. -/
abbrev RecData := Loc × (ℕ × Bool) × Loc

/-- Reference point (cell corner) of the first endpoint. -/
def refX (n : ℕ) (δ : ℝ) (l : Loc) : ℂ := gridPt (side n δ l.1) l.2.1

/-- Reference point (cell corner) of the second endpoint. -/
def refY (n : ℕ) (δ : ℝ) (l : Loc) : ℂ := gridPt (side n δ l.1) l.2.2

/-- Scale of the normalizing similarity of a location. -/
def locAlpha (n : ℕ) (δ : ℝ) (l : Loc) : ℂ := refY n δ l - refX n δ l

/-- The straight position `j / M` along the reference segment of a location. -/
def straight (n : ℕ) (δ : ℝ) (l : Loc) (j : ℕ) : ℂ :=
  refX n δ l + ((j : ℝ) / (Mn n : ℝ)) • locAlpha n δ l

/-- Admissible distance of a followed small-excess child from its straight position. -/
def rho (n : ℕ) (δ : ℝ) (σ : ℤ) (k : ℕ) : ℝ :=
  28 * (Mn n : ℝ) * (2 : ℝ) ^ σ * δ * √((k : ℝ) + 1)

/-- The dyadic scale exponent `⌊log₂ |y - x|⌋`. -/
def scl (x y : ℂ) : ℤ := Int.log 2 ‖y - x‖

/-- The location of the chord `[x, y]`. -/
def locOf (n : ℕ) (δ : ℝ) (x y : ℂ) : Loc :=
  (scl x y, gridIdx (side n δ (scl x y)) x, gridIdx (side n δ (scl x y)) y)

/-! ## Geometry of a single chord -/

section chord

variable {n : ℕ} {δ : ℝ} {x y : ℂ}

theorem scl_bounds (hR : 0 < ‖y - x‖) :
    (2 : ℝ) ^ scl x y ≤ ‖y - x‖ ∧ ‖y - x‖ < 2 * (2 : ℝ) ^ scl x y := by
  have h1 := Int.zpow_log_le_self (R := ℝ) (b := 2) (by norm_num) hR
  have h2 := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) (by norm_num) ‖y - x‖
  simp only [Nat.cast_ofNat] at h1 h2
  rw [zpow_add_one₀ two_ne_zero] at h2
  exact ⟨h1, by rw [scl]; linarith⟩

theorem side_scl_le (hδ : 0 ≤ δ) (hR : 0 < ‖y - x‖) :
    side n δ (scl x y) ≤ δ / (Mn n : ℝ) ^ 2 * ‖y - x‖ :=
  mul_le_mul_of_nonneg_left (scl_bounds hR).1 (eta_nonneg n hδ)

theorem refX_close (hδ : 0 < δ) : ‖x - refX n δ (locOf n δ x y)‖ ≤ 2 * side n δ (scl x y) :=
  norm_sub_gridPt_le (side_pos hδ n _) x

theorem refY_close (hδ : 0 < δ) : ‖y - refY n δ (locOf n δ x y)‖ ≤ 2 * side n δ (scl x y) :=
  norm_sub_gridPt_le (side_pos hδ n _) y

theorem alpha_close (hδ : 0 < δ) :
    ‖locAlpha n δ (locOf n δ x y) - (y - x)‖ ≤ 4 * side n δ (scl x y) := by
  have e : locAlpha n δ (locOf n δ x y) - (y - x) =
      (x - refX n δ (locOf n δ x y)) - (y - refY n δ (locOf n δ x y)) := by
    unfold locAlpha; ring
  rw [e]
  calc _ ≤ ‖x - refX n δ (locOf n δ x y)‖ + ‖y - refY n δ (locOf n δ x y)‖ := norm_sub_le _ _
    _ ≤ 2 * side n δ (scl x y) + 2 * side n δ (scl x y) :=
        add_le_add (refX_close hδ) (refY_close hδ)
    _ = 4 * side n δ (scl x y) := by ring

theorem alpha_bounds (hδ : 0 < δ) (hR : 0 < ‖y - x‖) :
    (1 - 4 * (δ / (Mn n : ℝ) ^ 2)) * ‖y - x‖ ≤ ‖locAlpha n δ (locOf n δ x y)‖ ∧
      ‖locAlpha n δ (locOf n δ x y)‖ ≤ (1 + 4 * (δ / (Mn n : ℝ) ^ 2)) * ‖y - x‖ := by
  have h1 := alpha_close (n := n) (x := x) (y := y) hδ
  have h2 := side_scl_le (n := n) hδ.le hR
  have t1 : ‖locAlpha n δ (locOf n δ x y)‖ ≤ ‖y - x‖ + 4 * side n δ (scl x y) := by
    calc ‖locAlpha n δ (locOf n δ x y)‖
        = ‖(locAlpha n δ (locOf n δ x y) - (y - x)) + (y - x)‖ := by ring_nf
      _ ≤ ‖locAlpha n δ (locOf n δ x y) - (y - x)‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ ‖y - x‖ + 4 * side n δ (scl x y) := by linarith
  have t2 : ‖y - x‖ - 4 * side n δ (scl x y) ≤ ‖locAlpha n δ (locOf n δ x y)‖ := by
    have : ‖y - x‖ ≤ ‖locAlpha n δ (locOf n δ x y)‖ +
        ‖locAlpha n δ (locOf n δ x y) - (y - x)‖ := by
      calc ‖y - x‖ = ‖locAlpha n δ (locOf n δ x y) -
            (locAlpha n δ (locOf n δ x y) - (y - x))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  constructor <;> nlinarith

theorem alpha_half (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) :
    ‖y - x‖ / 2 ≤ ‖locAlpha n δ (locOf n δ x y)‖ := by
  have := (alpha_bounds (n := n) hδ hR).1
  have := eta_le hn hδ1
  nlinarith

theorem alpha_ne_zero (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) :
    locAlpha n δ (locOf n δ x y) ≠ 0 := by
  intro h
  have := alpha_half hn hδ hδ1 hR
  rw [h, norm_zero] at this
  linarith

theorem cells_ne (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) :
    (locOf n δ x y).2.1 ≠ (locOf n δ x y).2.2 := by
  intro h
  apply alpha_ne_zero hn hδ hδ1 hR
  unfold locAlpha refX refY
  rw [h, sub_self]

theorem cell_small (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) {z w : ℂ}
    (hzw : ‖z - w‖ ≤ 2 * side n δ (scl x y)) :
    ‖z - w‖ ≤ cellRad (Mn n) * δ * ‖locAlpha n δ (locOf n δ x y)‖ := by
  have h1 := (alpha_bounds (n := n) hδ hR).1
  have h2 := side_scl_le (n := n) hδ.le hR
  have h3 := eta_le hn hδ1
  have h4 := eta_nonneg n hδ.le
  have e : cellRad (Mn n) * δ = 4 * (δ / (Mn n : ℝ) ^ 2) := by unfold cellRad; ring
  rw [e]
  set η := δ / (Mn n : ℝ) ^ 2
  have h5 : 2 * η * ‖y - x‖ ≤ 4 * η * ((1 - 4 * η) * ‖y - x‖) := by
    have : 0 ≤ η * ‖y - x‖ := mul_nonneg h4 hR.le
    nlinarith
  have h6 : 4 * η * ((1 - 4 * η) * ‖y - x‖) ≤ 4 * η * ‖locAlpha n δ (locOf n δ x y)‖ :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

theorem cell_x (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) :
    ‖x - refX n δ (locOf n δ x y)‖ ≤
      cellRad (Mn n) * δ * ‖locAlpha n δ (locOf n δ x y)‖ :=
  cell_small hn hδ hδ1 hR (refX_close hδ)

theorem cell_y (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) :
    ‖y - (locAlpha n δ (locOf n δ x y) + refX n δ (locOf n δ x y))‖ ≤
      cellRad (Mn n) * δ * ‖locAlpha n δ (locOf n δ x y)‖ := by
  have e : locAlpha n δ (locOf n δ x y) + refX n δ (locOf n δ x y) =
      refY n δ (locOf n δ x y) := by unfold locAlpha; ring
  rw [e]
  exact cell_small hn hδ hδ1 hR (refY_close hδ)

/-- Grid corners of the followed child's endpoints, in the large-excess case. -/
theorem large_pos (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) {σ'' : ℤ}
    (hσ : σ'' ≤ scl x y) {z : ℂ} (hz : ‖z - x‖ ≤ 4 * ‖y - x‖) :
    ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - refX n δ (locOf n δ x y)‖ ≤
      12 * (2 : ℝ) ^ scl x y := by
  have h1 : ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - z‖ ≤ 2 * side n δ σ'' := by
    rw [norm_sub_rev]; exact norm_sub_gridPt_le (side_pos hδ n _) z
  have h2 := side_mono hδ.le n hσ
  have h3 := refX_close (n := n) (x := x) (y := y) hδ
  have h4 : side n δ (scl x y) ≤ (2 : ℝ) ^ scl x y / 256 := by
    rw [side_eq]
    have := eta_le hn hδ1
    have : (0 : ℝ) < (2 : ℝ) ^ scl x y := by positivity
    nlinarith
  have h5 := (scl_bounds hR).2
  calc ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - refX n δ (locOf n δ x y)‖
      = ‖(gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - z) + (z - x) +
          (x - refX n δ (locOf n δ x y))‖ := by ring_nf
    _ ≤ ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - z‖ + ‖z - x‖ +
          ‖x - refX n δ (locOf n δ x y)‖ := norm_add₃_le
    _ ≤ 12 * (2 : ℝ) ^ scl x y := by nlinarith

/-- Grid corners of the followed child's endpoints, in the small-excess case. -/
theorem small_pos (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖) {σ'' : ℤ}
    (hσ : σ'' ≤ scl x y) {k : ℕ} {z : ℂ}
    (hz : ∃ j ≤ 3 * Mn n, ‖z - (x + ((j : ℝ) / (Mn n : ℝ)) • (y - x))‖ ≤
      6 * (Mn n : ℝ) * ‖y - x‖ * δ * √((k : ℝ) + 1)) :
    ∃ j ≤ 3 * Mn n, ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) -
      straight n δ (locOf n δ x y) j‖ ≤ rho n δ (scl x y) k := by
  obtain ⟨j, hj, hzj⟩ := hz
  refine ⟨j, hj, ?_⟩
  have hM := Mn_pos n
  have hM16 := Mn_ge_sixteen hn
  set c : ℝ := (j : ℝ) / (Mn n : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc3 : c ≤ 3 := by
    rw [hc, div_le_iff₀ hM]
    have : (j : ℝ) ≤ 3 * (Mn n : ℝ) := by exact_mod_cast hj
    linarith
  set s := side n δ (scl x y)
  have h1 : ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - z‖ ≤ 2 * s := by
    rw [norm_sub_rev]
    exact (norm_sub_gridPt_le (side_pos hδ n _) z).trans
      (by have := side_mono hδ.le n hσ; linarith)
  have hX := refX_close (n := n) (x := x) (y := y) hδ
  have hY := refY_close (n := n) (x := x) (y := y) hδ
  have hstr : ‖(x + c • (y - x)) - straight n δ (locOf n δ x y) j‖ ≤ 14 * s := by
    have e : (x + c • (y - x)) - straight n δ (locOf n δ x y) j =
        (x - refX n δ (locOf n δ x y)) +
          c • ((y - refY n δ (locOf n δ x y)) - (x - refX n δ (locOf n δ x y))) := by
      unfold straight locAlpha
      rw [← hc]
      simp only [smul_sub]
      abel
    rw [e]
    calc _ ≤ ‖x - refX n δ (locOf n δ x y)‖ +
          ‖c • ((y - refY n δ (locOf n δ x y)) - (x - refX n δ (locOf n δ x y)))‖ :=
          norm_add_le _ _
      _ = ‖x - refX n δ (locOf n δ x y)‖ +
          c * ‖(y - refY n δ (locOf n δ x y)) - (x - refX n δ (locOf n δ x y))‖ := by
          rw [norm_smul, Real.norm_of_nonneg hc0]
      _ ≤ 2 * s + c * (2 * s + 2 * s) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hY hX)
      _ ≤ 14 * s := by
          have : 0 ≤ s := (side_pos hδ n _).le
          nlinarith
  have hs : s ≤ δ * (2 : ℝ) ^ scl x y := by
    simp only [s, side_eq]
    have : (0 : ℝ) < (2 : ℝ) ^ scl x y := by positivity
    have h256 : (1 : ℝ) ≤ (Mn n : ℝ) ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h256 (show 0 ≤ δ * (2 : ℝ) ^ scl x y by positivity)
    linarith
  have hRb := (scl_bounds hR).2
  have hsq : (1 : ℝ) ≤ √((k : ℝ) + 1) := one_le_sqrt_succ k
  have hp : (0 : ℝ) < (2 : ℝ) ^ scl x y := by positivity
  calc ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - straight n δ (locOf n δ x y) j‖
      = ‖(gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - z) +
          (z - (x + c • (y - x))) + ((x + c • (y - x)) - straight n δ (locOf n δ x y) j)‖ := by
        ring_nf
    _ ≤ ‖gridPt (side n δ σ'') (gridIdx (side n δ σ'') z) - z‖ +
          ‖z - (x + c • (y - x))‖ + ‖(x + c • (y - x)) - straight n δ (locOf n δ x y) j‖ :=
        norm_add₃_le
    _ ≤ 2 * s + 6 * (Mn n : ℝ) * ‖y - x‖ * δ * √((k : ℝ) + 1) + 14 * s := by
        gcongr
    _ ≤ 16 * (δ * (2 : ℝ) ^ scl x y) +
          6 * (Mn n : ℝ) * (2 * (2 : ℝ) ^ scl x y) * δ * √((k : ℝ) + 1) := by
        have : 0 ≤ (Mn n : ℝ) * δ * √((k : ℝ) + 1) := by positivity
        nlinarith
    _ ≤ rho n δ (scl x y) k := by
        unfold rho
        have : 0 ≤ δ * (2 : ℝ) ^ scl x y := by positivity
        have : δ * (2 : ℝ) ^ scl x y ≤ (Mn n : ℝ) * √((k : ℝ) + 1) * (δ * (2 : ℝ) ^ scl x y) := by
          have : (1 : ℝ) ≤ (Mn n : ℝ) * √((k : ℝ) + 1) := by nlinarith
          nlinarith
        nlinarith

end chord

/-! ## Parent and child chords -/

section parent

variable {n : ℕ} {δ : ℝ} {x y x' y' : ℂ}

theorem scl_child_le (hR : 0 < ‖y - x‖) (hR' : 0 < ‖y' - x'‖) (hle : ‖y' - x'‖ ≤ ‖y - x‖) :
    scl x' y' ≤ scl x y := by
  have a := (scl_bounds hR').1
  have b := (scl_bounds hR).2
  have : (2 : ℝ) ^ scl x' y' < (2 : ℝ) ^ (scl x y + 1) := by
    rw [zpow_add_one₀ two_ne_zero]; linarith
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
  omega

theorem scl_le_child (hR : 0 < ‖y - x‖) (hR' : 0 < ‖y' - x'‖)
    (h1 : ‖y - x‖ / (2 * (Mn n : ℝ)) ≤ ‖y' - x'‖) :
    scl x y ≤ scl x' y' + (4 * n + 2) := by
  have a := (scl_bounds hR).1
  have b := (scl_bounds hR').2
  have hM := Mn_pos n
  have c : ‖y - x‖ ≤ 2 * (Mn n : ℝ) * ‖y' - x'‖ := by
    rw [div_le_iff₀ (by positivity)] at h1; linarith
  have : (2 : ℝ) ^ scl x y < (2 : ℝ) ^ (scl x' y' + (4 * (n : ℤ) + 2)) := by
    rw [zpow_add₀ two_ne_zero, two_zpow_eq]
    nlinarith
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
  omega

theorem alpha_child (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < ‖y - x‖)
    (hR' : 0 < ‖y' - x'‖) (h2 : ‖y' - x'‖ ≤ 3 * ‖y - x‖ / (2 * (Mn n : ℝ))) :
    ‖locAlpha n δ (locOf n δ x' y')‖ ≤ 4 / (Mn n : ℝ) * ‖locAlpha n δ (locOf n δ x y)‖ := by
  have a := (alpha_bounds (n := n) hδ hR').2
  have b := (alpha_bounds (n := n) hδ hR).1
  have hη := eta_le hn hδ1
  have hη0 := eta_nonneg n hδ.le
  have hM := Mn_pos n
  set η := δ / (Mn n : ℝ) ^ 2
  have e1 : 3 * ‖y - x‖ / (2 * (Mn n : ℝ)) = (3 / 2) * (‖y - x‖ / (Mn n : ℝ)) := by
    field_simp
  have e2 : 4 / (Mn n : ℝ) * ‖locAlpha n δ (locOf n δ x y)‖ =
      4 * (‖locAlpha n δ (locOf n δ x y)‖ / (Mn n : ℝ)) := by ring
  rw [e1] at h2
  rw [e2]
  have b' : (1 - 4 * η) * (‖y - x‖ / (Mn n : ℝ)) ≤ ‖locAlpha n δ (locOf n δ x y)‖ / (Mn n : ℝ) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right b hM.le
  have hq : 0 ≤ ‖y - x‖ / (Mn n : ℝ) := by positivity
  calc ‖locAlpha n δ (locOf n δ x' y')‖ ≤ (1 + 4 * η) * ‖y' - x'‖ := a
    _ ≤ (1 + 4 * η) * ((3 / 2) * (‖y - x‖ / (Mn n : ℝ))) := by gcongr
    _ ≤ 4 * ((1 - 4 * η) * (‖y - x‖ / (Mn n : ℝ))) := by nlinarith
    _ ≤ 4 * (‖locAlpha n δ (locOf n δ x y)‖ / (Mn n : ℝ)) := by linarith

end parent

end LQGDimension.LFPPRecords
