/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.WaypointNet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces

/-!
# Explicit polar net for the environment centers in the scaled-grid estimate

The net has 93 radial intervals across the annulus and 4200 angular intervals. Both spacings are
bounded by `s₀ r / 100`; their product is below the `⌈4·10⁵/s₀²⌉` budget in the fixed waypoint
input. The construction is an image of a finite integer box.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open Set Metric

namespace MatedCRTHarmonic.CellFamily

/-- Number of radial subdivisions for the fixed polar net. -/
private def waypointRadialCount (s₀ : ℝ) : ℕ := ⌈93 / s₀⌉₊

/-- Number of angular subdivisions for the fixed polar net. -/
private def waypointAngularCount (s₀ : ℝ) : ℕ := ⌈4200 / s₀⌉₊

/-- A point on one radial-angular grid line, with radius between `0.85r` and `1.15r`. -/
private def waypointPolarPoint (z : ℂ) (r : ℝ) (s₀ : ℝ) (i j : ℕ) : ℂ :=
  z + (((17 / 20 + (3 / 10) * (i : ℝ) / waypointRadialCount s₀) * r : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * (j : ℝ) / waypointAngularCount s₀ : ℝ) : ℂ) * Complex.I)

private theorem waypointRadialCount_pos {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀le : s₀ ≤ 1 / 10) :
    0 < waypointRadialCount s₀ := by
  apply Nat.ceil_pos.mpr
  positivity

private theorem waypointAngularCount_pos {s₀ : ℝ} (hs₀ : 0 < s₀) :
    0 < waypointAngularCount s₀ := by
  apply Nat.ceil_pos.mpr
  positivity

private theorem waypointRadialCount_lower {s₀ : ℝ} (hs₀ : 0 < s₀) :
    93 / s₀ ≤ (waypointRadialCount s₀ : ℝ) := by
  exact_mod_cast (Nat.le_ceil (93 / s₀))

private theorem waypointAngularCount_lower {s₀ : ℝ} (hs₀ : 0 < s₀) :
    4200 / s₀ ≤ (waypointAngularCount s₀ : ℝ) := by
  exact_mod_cast (Nat.le_ceil (4200 / s₀))

private theorem waypointRadialCount_upper {s₀ : ℝ} (hs₀ : 0 < s₀) :
    (waypointRadialCount s₀ : ℝ) ≤ 93 / s₀ + 1 := by
  have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 93 / s₀)
  exact_mod_cast h.le

private theorem waypointAngularCount_upper {s₀ : ℝ} (hs₀ : 0 < s₀) :
    (waypointAngularCount s₀ : ℝ) ≤ 4200 / s₀ + 1 := by
  have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 4200 / s₀)
  exact_mod_cast h.le

private theorem waypoint_exp_chord_bound (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have he : Complex.exp ((a : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) * Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  have hfactor : Complex.exp ((b : ℂ) * Complex.I) * Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) -
      Complex.exp ((b : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsin := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  have hrewrite : Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) =
      Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) := by
    congr 1
    ring
  rw [hrewrite] at hsin
  simpa [Real.norm_eq_abs] using hsin

private theorem waypoint_polar_norm {z : ℂ} {r R : ℝ} {θ : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) :
    ‖z + ((R * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - z‖ = R * r := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hR hr.le),
    Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem waypointPolarPoint_annulus {z : ℂ} {r s₀ : ℝ} {i j : ℕ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hs₀le : s₀ ≤ 1 / 10)
    (hi : i ≤ waypointRadialCount s₀)
    (hj : j < waypointAngularCount s₀) :
    (17 / 20) * r ≤ ‖waypointPolarPoint z r s₀ i j - z‖ ∧
      ‖waypointPolarPoint z r s₀ i j - z‖ ≤ (23 / 20) * r := by
  have hN : 0 < (waypointRadialCount s₀ : ℝ) := by
    exact_mod_cast waypointRadialCount_pos hs₀ hs₀le
  have hfrac : 0 ≤ (i : ℝ) / waypointRadialCount s₀ ∧
      (i : ℝ) / waypointRadialCount s₀ ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one₀ hN).2 (by exact_mod_cast hi)
  have hradlo : 0 ≤ 17 / 20 + 3 / 10 * (i : ℝ) / waypointRadialCount s₀ := by
    positivity
  have hradlower : 17 / 20 ≤ 17 / 20 + 3 / 10 * (i : ℝ) / waypointRadialCount s₀ := by
    have heq : 3 / 10 * (i : ℝ) / waypointRadialCount s₀ =
        3 / 10 * ((i : ℝ) / waypointRadialCount s₀) := by field_simp
    rw [heq]
    nlinarith [hfrac.1]
  have hradhi : 17 / 20 + 3 / 10 * (i : ℝ) / waypointRadialCount s₀ ≤ 23 / 20 := by
    have heq : 3 / 10 * (i : ℝ) / waypointRadialCount s₀ =
        3 / 10 * ((i : ℝ) / waypointRadialCount s₀) := by field_simp
    rw [heq]
    nlinarith [hfrac.2]
  rw [waypointPolarPoint, waypoint_polar_norm hr hradlo]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hradlower hr.le,
    mul_le_mul_of_nonneg_right hradhi hr.le]

/-- Construct a polar net for the entire template annulus. The net points lie in the annulus
`[0.85r,1.15r]`, cover it to radius `s₀r/200`, and have the explicit cardinality budget used by
`WaypointStrongMarkovInputFixed2`. -/
theorem exists_waypoint_polar_annular_net (z : ℂ) {r s₀ : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hs₀le : s₀ ≤ 1 / 10) :
    ∃ W : Finset ℂ,
      W.card ≤ ⌈4 * 10 ^ 5 / s₀ ^ 2⌉₊ ∧
      (∀ w ∈ W, (17 / 20) * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ (23 / 20) * r) ∧
      (∀ y, (17 / 20) * r ≤ ‖y - z‖ → ‖y - z‖ ≤ (23 / 20) * r →
        ∃ w ∈ W, ‖w - y‖ ≤ s₀ * r / 200) := by
  classical
  let nr := waypointRadialCount s₀
  let na := waypointAngularCount s₀
  let W := (Finset.range (nr + 1)).product (Finset.range na) |>.image
    (fun ij : ℕ × ℕ => waypointPolarPoint z r s₀ ij.1 ij.2)
  have hnrpos : 0 < (nr : ℝ) := by
    exact_mod_cast waypointRadialCount_pos hs₀ hs₀le
  have hnapos : 0 < (na : ℝ) := by
    exact_mod_cast waypointAngularCount_pos hs₀
  have hnrlo : 93 / s₀ ≤ (nr : ℝ) := by
    exact waypointRadialCount_lower hs₀
  have hnalo : 4200 / s₀ ≤ (na : ℝ) := by
    exact waypointAngularCount_lower hs₀
  have hnrhi : (nr : ℝ) ≤ 93 / s₀ + 1 := by
    exact waypointRadialCount_upper hs₀
  have hnahi : (na : ℝ) ≤ 4200 / s₀ + 1 := by
    exact waypointAngularCount_upper hs₀
  have hcard : W.card ≤ ⌈4 * 10 ^ 5 / s₀ ^ 2⌉₊ := by
    have hle : (W.card : ℝ) ≤ 400000 / s₀ ^ 2 := by
      have hnrplus : ((nr + 1 : ℕ) : ℝ) ≤ 94 / s₀ := by
        have hnr' : (nr : ℝ) + 1 ≤ 93 / s₀ + 2 := by linarith [hnrhi]
        have hsinv : 10 ≤ 1 / s₀ := by
          apply (le_div_iff₀ hs₀).2
          nlinarith [hs₀le]
        have h94 : 93 / s₀ + 2 ≤ 94 / s₀ := by
          have : 2 ≤ 1 / s₀ := by linarith
          have hsinv' : 2 ≤ s₀⁻¹ := by simpa [one_div] using this
          rw [div_eq_mul_inv, div_eq_mul_inv]
          nlinarith [hsinv']
        have hcast : ((nr + 1 : ℕ) : ℝ) = (nr : ℝ) + 1 := by norm_num
        rw [hcast]
        exact hnr'.trans h94
      have hnaplus : (na : ℝ) ≤ 4201 / s₀ := by
        have hsinv : 1 ≤ 1 / s₀ := by
          apply (le_div_iff₀ hs₀).2
          nlinarith [hs₀le]
        have h4201 : 4200 / s₀ + 1 ≤ 4201 / s₀ := by
          have : 1 ≤ 1 / s₀ := hsinv
          have hsinv' : 1 ≤ s₀⁻¹ := by simpa [one_div] using this
          rw [div_eq_mul_inv, div_eq_mul_inv]
          nlinarith [hsinv']
        exact hnahi.trans h4201
      have hbox : ((Finset.range (nr + 1)).product (Finset.range na)).card = (nr + 1) * na := by
        simp
      have hcardNat : W.card ≤ (nr + 1) * na := by
        dsimp [W]
        calc
          _ ≤ ((Finset.range (nr + 1)).product (Finset.range na)).card :=
            Finset.card_image_le
          _ = (nr + 1) * na := hbox
      have hcard' : (W.card : ℝ) ≤ ((nr + 1 : ℕ) : ℝ) * (na : ℝ) := by
        exact_mod_cast hcardNat
      have hmul : ((nr + 1 : ℕ) : ℝ) * (na : ℝ) ≤ 400000 / s₀ ^ 2 := by
        have hna_nonneg : 0 ≤ (na : ℝ) := Nat.cast_nonneg _
        have hnr_nonneg : 0 ≤ (nr + 1 : ℝ) := by positivity
        calc
          _ ≤ (94 / s₀) * (4201 / s₀) := mul_le_mul hnrplus hnaplus hna_nonneg (by positivity)
          _ ≤ 400000 / s₀ ^ 2 := by field_simp; norm_num
      exact hcard'.trans hmul
    have hceil : (W.card : ℝ) ≤ (⌈4 * 10 ^ 5 / s₀ ^ 2⌉₊ : ℕ) := by
      exact_mod_cast hle.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  have hmem_ann (ij : ℕ × ℕ) (hij : ij ∈ (Finset.range (nr + 1)).product (Finset.range na)) :
      (17 / 20) * r ≤ ‖waypointPolarPoint z r s₀ ij.1 ij.2 - z‖ ∧
        ‖waypointPolarPoint z r s₀ ij.1 ij.2 - z‖ ≤ (23 / 20) * r := by
    have hi : ij.1 ≤ nr := by simpa using (Finset.mem_product.mp hij).1
    have hj : ij.2 < na := by simpa using (Finset.mem_product.mp hij).2
    exact waypointPolarPoint_annulus hr hs₀ hs₀le (by simpa [nr] using hi) (by simpa [na] using hj)
  have hnetann : ∀ w ∈ W, (17 / 20) * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ (23 / 20) * r := by
    intro w hw
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hw
    exact hmem_ann ij hij
  have hcover : ∀ y, (17 / 20) * r ≤ ‖y - z‖ → ‖y - z‖ ≤ (23 / 20) * r →
      ∃ w ∈ W, ‖w - y‖ ≤ s₀ * r / 200 := by
    intro y hylo hyhi
    let R := ‖y - z‖ / r
    have hRlo : 17 / 20 ≤ R := (le_div_iff₀ hr).2 (by nlinarith [hylo])
    have hRhi : R ≤ 23 / 20 := (div_le_iff₀ hr).2 (by nlinarith [hyhi])
    have hyne : y - z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hylo
      nlinarith [hr]
    let a := (if (y - z).arg < 0 then (y - z).arg + 2 * Real.pi else (y - z).arg)
    have ha0 : 0 ≤ a := by
      dsimp [a]
      split_ifs with harg
      · linarith [Complex.neg_pi_lt_arg (y - z), Real.pi_pos]
      · exact le_of_not_gt harg
    have ha2pi : a < 2 * Real.pi := by
      dsimp [a]
      split_ifs with harg
      · linarith
      ·
        exact (Complex.arg_le_pi (y - z)).trans_lt (by nlinarith [Real.pi_pos])
    have harg_repr : Complex.exp (((y - z).arg : ℝ) * Complex.I) =
        Complex.exp ((a : ℂ) * Complex.I) := by
      dsimp [a]
      by_cases harg : (y - z).arg < 0
      · simp only [if_pos harg]
        have hcast : (((y - z).arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
            ((y - z).arg : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
          push_cast
          ring
        calc
          _ = Complex.exp (((y - z).arg : ℝ) * Complex.I) * 1 := by rw [mul_one]
          _ = Complex.exp (((y - z).arg : ℝ) * Complex.I) *
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I) := by rw [Complex.exp_two_pi_mul_I]
          _ = Complex.exp (((y - z).arg : ℝ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I) :=
            (Complex.exp_add _ _).symm
          _ = Complex.exp ((((y - z).arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by rw [hcast]
      · simp only [if_neg harg]
    have hnormrepr := Complex.norm_mul_exp_arg_mul_I (y - z)
    rw [harg_repr] at hnormrepr
    have hyrepr : y - z = ((R * r : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) := by
      have hR : R * r = ‖y - z‖ := by
        dsimp [R]
        field_simp
      rw [← hnormrepr, hR]
    let tr := (R - 17 / 20) * nr / (3 / 10)
    let i := Nat.floor tr
    have htr0 : 0 ≤ tr := by
      dsimp [tr]
      positivity
    have htrhi : tr ≤ (nr : ℝ) := by
      dsimp [tr]
      have hn : (0 : ℝ) < nr := hnrpos
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 10)]
      nlinarith [hRhi, hRlo, hn]
    have hiFloor : (i : ℝ) ≤ tr := by simpa [i] using Nat.floor_le htr0
    have hiFloor' : tr < (i : ℝ) + 1 := by simpa [i] using Nat.lt_floor_add_one tr
    have hiLe : i ≤ nr := by exact_mod_cast hiFloor.trans htrhi
    let tt := a * na / (2 * Real.pi)
    let j := Nat.floor tt
    have htt0 : 0 ≤ tt := by
      dsimp [tt]
      positivity
    have httn : tt < (na : ℝ) := by
      dsimp [tt]
      rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
      nlinarith [ha2pi, hnapos]
    have hjFloor : (j : ℝ) ≤ tt := by simpa [j] using Nat.floor_le htt0
    have hjFloor' : tt < (j : ℝ) + 1 := by simpa [j] using Nat.lt_floor_add_one tt
    have hjLt : j < na := by exact_mod_cast lt_of_le_of_lt hjFloor httn
    let R' := 17 / 20 + 3 / 10 * (i : ℝ) / nr
    let θ := 2 * Real.pi * (j : ℝ) / na
    have hR'lo : 0 ≤ R' := by dsimp [R']; positivity
    have hR'hi : R' ≤ 23 / 20 := by
      dsimp [R']
      have hi' : (i : ℝ) / nr ≤ 1 := (div_le_one₀ hnrpos).2 (by exact_mod_cast hiLe)
      have heq : 3 / 10 * (i : ℝ) / nr = 3 / 10 * ((i : ℝ) / nr) := by field_simp
      rw [heq]
      nlinarith [hi']
    have hraderr : 0 ≤ R - R' ∧ R - R' ≤ 3 / (10 * nr) := by
      have hprodlo : (3 / 10) * (i : ℝ) ≤ (R - 17 / 20) * nr := by
        have h := hiFloor
        dsimp [tr] at h
        simpa [mul_comm] using
          (le_div_iff₀ (by norm_num : (0 : ℝ) < 3 / 10)).1 h
      have hprodhi : (R - 17 / 20) * nr < (3 / 10) * ((i : ℝ) + 1) := by
        have h := hiFloor'
        dsimp [tr] at h
        simpa [mul_comm] using
          (div_lt_iff₀ (by norm_num : (0 : ℝ) < 3 / 10)).1 h
      have hradlo' : (3 / 10) * (i : ℝ) / nr ≤ R - 17 / 20 :=
        (div_le_iff₀ hnrpos).2 hprodlo
      have hradhi' : R - 17 / 20 < (3 / 10) * ((i : ℝ) + 1) / nr :=
        (lt_div_iff₀ hnrpos).2 hprodhi
      have hsplit : (3 / 10) * ((i : ℝ) + 1) / nr =
          (3 / 10) * (i : ℝ) / nr + (3 / 10) / nr := by field_simp
      constructor
      · dsimp [R']
        nlinarith [hradlo']
      · dsimp [R']
        rw [hsplit] at hradhi'
        have hdivEq : 3 / (10 * (nr : ℝ)) = (3 / 10) / nr := by field_simp
        rw [hdivEq]
        linarith [hradhi']
    have htheta : 0 ≤ a - θ ∧ a - θ ≤ 2 * Real.pi / na := by
      have hprodlo : (2 * Real.pi) * (j : ℝ) ≤ a * na := by
        have h := hjFloor
        dsimp [tt] at h
        simpa [mul_comm] using
          (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 h
      have hprodhi : a * na < (2 * Real.pi) * ((j : ℝ) + 1) := by
        have h := hjFloor'
        dsimp [tt] at h
        simpa [mul_comm] using
          (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 h
      have hθlo : θ ≤ a := by
        dsimp [θ]
        exact (div_le_iff₀ hnapos).2 hprodlo
      have hθhi : a < (2 * Real.pi) * ((j : ℝ) + 1) / na :=
        (lt_div_iff₀ hnapos).2 hprodhi
      have hθsplit : (2 * Real.pi) * ((j : ℝ) + 1) / na = θ + 2 * Real.pi / na := by
        dsimp [θ]
        field_simp [ne_of_gt hnapos]
      constructor
      · linarith [hθlo]
      · dsimp [θ]
        rw [hθsplit] at hθhi
        linarith [hθhi]
    have hradSmall : 3 / (10 * nr) ≤ s₀ / 310 := by
      have hnr := hnrlo
      have hprod : 93 ≤ (nr : ℝ) * s₀ := (div_le_iff₀ hs₀).1 hnr
      rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 10) hnrpos)]
      field_simp [ne_of_gt hs₀]
      nlinarith [hprod]
    have hthetaSmall : 2 * Real.pi / na ≤ s₀ / 650 := by
      have hna := hnalo
      have hprod : 4200 ≤ (na : ℝ) * s₀ := (div_le_iff₀ hs₀).1 hna
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      rw [div_le_iff₀ hnapos]
      field_simp [ne_of_gt hs₀]
      nlinarith [hprod]
    have hθchord : ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ s₀ / 650 := by
      exact (waypoint_exp_chord_bound a θ).trans
        (by rw [abs_of_nonneg htheta.1]; exact htheta.2.trans hthetaSmall)
    have hdistNorm : ‖((R * r : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) -
        ((R' * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ s₀ * r / 200 := by
      have hdecomp : ((R * r : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) -
          ((R' * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
          (((R - R') * r : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) +
          ((R' * r : ℝ) : ℂ) *
            (Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)) := by
        push_cast
        ring
      rw [hdecomp]
      calc
        _ ≤ ‖(((R - R') * r : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I)‖ +
            ‖((R' * r : ℝ) : ℂ) *
              (Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I))‖ := norm_add_le _ _
        _ = (R - R') * r + R' * r *
            ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hraderr.1 hr.le),
            Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (mul_nonneg hR'lo hr.le)]
        _ ≤ s₀ * r / 310 + ((23 / 20) * r) * (s₀ / 650) := by
          have hradpart : (R - R') * r ≤ s₀ * r / 310 := by
            calc
              _ ≤ (3 / (10 * nr)) * r := mul_le_mul_of_nonneg_right hraderr.2 hr.le
              _ ≤ (s₀ / 310) * r := mul_le_mul_of_nonneg_right hradSmall hr.le
              _ = s₀ * r / 310 := by ring
          have hR'r : R' * r ≤ (23 / 20) * r := mul_le_mul_of_nonneg_right hR'hi hr.le
          have hanglepart : R' * r *
              ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)‖ ≤
                (23 / 20 * r) * (s₀ / 650) := by
            calc
              _ ≤ R' * r * (s₀ / 650) :=
                mul_le_mul_of_nonneg_left hθchord (mul_nonneg hR'lo hr.le)
              _ ≤ (23 / 20 * r) * (s₀ / 650) :=
                mul_le_mul_of_nonneg_right hR'r (by positivity)
          exact add_le_add hradpart hanglepart
        _ ≤ s₀ * r / 200 := by nlinarith [hs₀, hr]
    let w := waypointPolarPoint z r s₀ i j
    have hwi : w ∈ W := by
      dsimp [w, W, nr, na]
      apply Finset.mem_image.mpr
      refine ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr ?_⟩, rfl⟩
      simpa [nr, na] using hjLt
    refine ⟨w, hwi, ?_⟩
    have hpoint : w - z = ((R' * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      dsimp [w, waypointPolarPoint, R', θ, nr, na]
      congr 1
      push_cast
      ring
    have hwy : w - y = (w - z) - (y - z) := by ring
    rw [hwy, norm_sub_rev]
    have hvec : (y - z) - (w - z) =
        ((R * r : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) -
          ((R' * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [hyrepr, hpoint]
    rw [hvec]
    exact hdistNorm
  exact ⟨W, by simpa [W, nr, na] using hcard, hnetann, hcover⟩

end MatedCRTHarmonic.CellFamily

