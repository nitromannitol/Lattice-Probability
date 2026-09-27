import LatticeProb.Site
import LatticeProb.Network.KilledGreen
import LatticeProb.Graph.Zd
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Walk.SRW
import LatticeProb.Walk.GreenTwoSided
import LatticeProb.Walk.Harnack.Basics
import LatticeProb.Walk.Harnack.Dirichlet

/-!
# Box geometry, the shell representation, and the Green estimate at scale R

The geometry of the three nested boxes `box d R ⊆ harnackBox d (R+R/2) ⊆ harnackBox d (2R-1)` used
in the balayage argument; the Riesz representation of a function harmonic on `box d (2R-1)` and
nonnegative on `box d (2R)` as a nonnegative-charge sum over the shell; and the two-sided bound
`harnackGreen ≍ R^{2-d}` on the shell, obtained from
`LatticeProb.GreenTwoSided.killedGreenReal_le_box` and `killedGreenReal_ge_box`.
-/

open Finset
open scoped Classical

namespace LatticeProb

variable {d : ℕ}

/-! ### Geometry of the three boxes (R ≥ 4) -/

-- intro x; rw [mem_harnackBox_iff_mem_box, mem_harnackBox_iff_mem_box]; mem_box_of_le with R + R/2
-- ≤ 2R - 1 (omega)
/-- `harnackBox d (R + R/2) ⊆ harnackBox d (2R-1)` for `R ≥ 4`. -/
private theorem harnackBox_add_div_two_subset {R : ℕ} (hR : 4 ≤ R) :
    harnackBox d (R + R / 2) ⊆ harnackBox d (2 * R - 1) := by
  intro x hx
  rw [mem_harnackBox_iff_mem_box] at hx ⊢
  exact mem_box_of_le (by omega) hx


-- (mem_harnackBox_iff_mem_box).2 (mem_box_of_le (by omega) hx)
/-- `x ∈ box d R` implies `x ∈ harnackBox d (R + R/2)`. -/
private theorem mem_harnackBox_add_div_two_of_mem_box {R : ℕ} {x : Site d} (hx : x ∈ box d R) : x ∈
    harnackBox d (R + R / 2) := by
  rw [mem_harnackBox_iff_mem_box]
  exact mem_box_of_le (by omega) hx


-- y ∉ shell and y ∈ harnackBox (R+R/2) ⇒ y ∈ harnackBox (R+R/2-1) (harnackShell, Finset.mem_sdiff);
-- then mem_harnackBox_iff_mem_box, unit_add_sub_mem_box_succ, and R + R/2 - 1 + 1 = R + R/2 (omega,
-- R ≥ 4).
/-- The unit-neighbours of a point in `harnackBox d (R+R/2)` outside the shell stay in
`harnackBox d (R+R/2)`. -/
private theorem unit_add_sub_mem_harnackBox_of_not_mem_shell {R : ℕ} (hR : 4 ≤ R) {y : Site d}
    (hy : y ∈ harnackBox d (R + R / 2))
    (hyS : y ∉ harnackShell d R) (i : Fin d) :
    y + unit i ∈ harnackBox d (R + R / 2) ∧ y - unit i ∈ harnackBox d (R + R / 2) := by
  have hy1 : y ∈ harnackBox d (R + R / 2 - 1) := (by
    by_contra hh
    exact hyS (by rw [harnackShell]; exact Finset.mem_sdiff.mpr ⟨hy, hh⟩))
  have hybox : y ∈ box d (R + R / 2 - 1) := (mem_harnackBox_iff_mem_box (R + R / 2 - 1) y).mp hy1
  obtain ⟨h1, h2⟩ := unit_add_sub_mem_box_succ (R + R / 2 - 1) y i hybox
  have heq : R + R / 2 - 1 + 1 = R + R / 2 := (by omega)
  rw [heq] at h1 h2
  exact ⟨(mem_harnackBox_iff_mem_box (R + R / 2) (y + unit i)).mpr h1,
    (mem_harnackBox_iff_mem_box (R + R / 2) (y - unit i)).mpr h2⟩


-- Finset.sdiff_subset.trans (harnackBox_add_div_two_subset hR)
/-- `harnackShell d R ⊆ harnackBox d (2R-1)` for `R ≥ 4`. -/
private theorem harnackShell_subset_harnackBox {R : ℕ} (hR : 4 ≤ R) :
    harnackShell d R ⊆ harnackBox d (2 * R - 1) := by
  intro x hx
  rw [harnackShell, Finset.mem_sdiff] at hx
  exact harnackBox_add_div_two_subset hR hx.1


/-! ### The shell representation -/

-- Riesz eq_sum_harnackGreen_mul_laplacian for v := harnackExt B K u (vanishes off B by
-- harnackExt_eq_zero_of_not_mem + harnackBox_add_div_two_subset),
-- then Finset.sum_subset (harnackShell_subset_harnackBox): for y ∈ B \ shell either y ∉ K, where
-- the charge is 0 by
-- nbrSum_harnackExt_eq_of_mem_sdiff, or y ∈ K \ shell, where it is 0 by
-- two_mul_harnackExt_sub_nbrSum_eq_zero + unit_add_sub_mem_harnackBox_of_not_mem_shell (harmonic at
-- y
-- from hharm, mem_harnackBox_iff_mem_box, harnackBox_add_div_two_subset).  SPLIT?
/-- The Riesz representation `eq_sum_harnackGreen_mul_laplacian` specialized to `v = harnackExt
(harnackBox (2R-1)) (harnackBox (R+R/2)) u`: the sum localizes to the shell, since the charge
vanishes off it. -/
private theorem harnackExt_eq_sum_shell_mul_charge (hd : 1 ≤ d) {R : ℕ} (hR : 4 ≤ R)
    (u : Site d → ℝ)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) (x : Site d) :
    harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u x
      = ∑ y ∈ harnackShell d R, harnackGreen (harnackBox d (2 * R - 1)) x y *
          (2 * (d : ℝ) * harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u y
            - nbrSum (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u) y) := by
  have hKB : harnackBox d (R + R / 2) ⊆ harnackBox d (2 * R - 1) := harnackBox_add_div_two_subset hR
  rw [eq_sum_harnackGreen_mul_laplacian hd (harnackBox d (2 * R - 1))
      (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u)
      (fun z hz => harnackExt_eq_zero_of_not_mem hd _ _ hKB u hz) x]
  symm
  refine Finset.sum_subset (s₁ := harnackShell d R) (s₂ := harnackBox d (2 * R - 1))
    (f := fun y => harnackGreen (harnackBox d (2 * R - 1)) x y *
      (2 * (d : ℝ) * harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u y
        - nbrSum (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u) y))
    (harnackShell_subset_harnackBox hR) ?_
  intro y hyB hyS
  apply mul_eq_zero.mpr
  right
  by_cases hyK : y ∈ harnackBox d (R + R / 2)
  · exact two_mul_harnackExt_sub_nbrSum_eq_zero hd _ _ u hyK
      (unit_add_sub_mem_harnackBox_of_not_mem_shell hR hyK hyS)
      (hharm y ((mem_harnackBox_iff_mem_box (2 * R - 1) y).1 hyB))
  · have h17 := nbrSum_harnackExt_eq_of_mem_sdiff hd (harnackBox d (2 * R - 1))
        (harnackBox d (R + R / 2)) u hyB hyK
    linarith


-- hBD: mem_harnackBox_iff_mem_box then mem_box_of_le (2R-1 ≤ 2R).  hnb: unit_add_sub_mem_box_succ
-- at radius 2R-1, and
-- 2R-1+1 = 2R (omega, 1 ≤ R).
/-- `harnackBox d (2R-1) ⊆ box d (2R)`, and its unit-neighbours also lie in `box d (2R)`. -/
private theorem harnackBox_subset_box_and_unit_mem {R : ℕ} (hR : 1 ≤ R) :
    (∀ x ∈ harnackBox d (2 * R - 1), x ∈ box d (2 * R)) ∧
    (∀ x ∈ harnackBox d (2 * R - 1), ∀ i : Fin d,
      x + unit i ∈ box d (2 * R) ∧ x - unit i ∈ box d (2 * R)) := by
  have hR2 : 2 * R - 1 + 1 = 2 * R := by omega
  refine ⟨fun x hx => mem_box_of_le (by
    omega) ((mem_harnackBox_iff_mem_box _ x).1 hx), fun x hx i => ?_⟩
  have h := unit_add_sub_mem_box_succ (2 * R - 1) x i ((mem_harnackBox_iff_mem_box _ x).1 hx)
  rw [hR2] at h
  exact h

-- unfold harnackShell; Finset.mem_sdiff.
/-- `harnackShell d R ⊆ harnackBox d (R + R/2)`. -/
private theorem harnackShell_subset_harnackBox_add_div_two {R : ℕ} {y : Site d}
    (hy : y ∈ harnackShell d R) :
    y ∈ harnackBox d (R + R / 2) := by
  unfold harnackShell at hy
  exact (Finset.mem_sdiff.mp hy).1

-- ν y := 2d v y - nbrSum v y on the shell, 0 elsewhere (v := harnackExt ...).  Nonneg by
-- zero_le_two_mul_harnackExt_sub_nbrSum with D := box d (2R) (hBD, hnb from
-- mem_harnackBox_iff_mem_box/2/3, omega on 2R-1+1 = 2R).
-- u x = v x by harnackExt_eq_of_mem + mem_harnackBox_add_div_two_of_mem_box, then
-- harnackExt_eq_sum_shell_mul_charge and Finset.sum_congr (if_pos).
/-- For `u` nonnegative on `box d (2R)` and harmonic on `box d (2R-1)`, there is a nonnegative
charge `ν` supported on the shell with `u x = ∑_{y ∈ shell} harnackGreen (harnackBox (2R-1))
x y * ν y` on `box d R`. -/
private theorem exists_nonneg_eq_sum_shell_mul (hd : 1 ≤ d) {R : ℕ} (hR : 4 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) :
    ∃ ν : Site d → ℝ, (∀ y, 0 ≤ ν y) ∧ ∀ x ∈ box d R,
      u x = ∑ y ∈ harnackShell d R, harnackGreen (harnackBox d (2 * R - 1)) x y * ν y := by
  have hKB : harnackBox d (R + R / 2) ⊆ harnackBox d (2 * R - 1) := harnackBox_add_div_two_subset hR
  obtain ⟨hBD, hnb⟩ := harnackBox_subset_box_and_unit_mem (d := d) (R := R) (by omega)
  have hharmB : ∀ x ∈ harnackBox d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x :=
    fun x hx => hharm x ((mem_harnackBox_iff_mem_box _ x).1 hx)
  refine ⟨fun y => if y ∈ harnackShell d R then
      2 * (d : ℝ) * harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u y
        - nbrSum (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u) y
    else 0, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ harnackShell d R
    · simp only [if_pos hy]
      exact zero_le_two_mul_harnackExt_sub_nbrSum hd _ _ hKB (box d (2 * R)) u hBD hnb hpos hharmB
          (harnackShell_subset_harnackBox_add_div_two hy)
    · simp only [if_neg hy, le_refl]
  · intro x hx
    rw [← harnackExt_eq_of_mem hd (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u
      (mem_harnackBox_add_div_two_of_mem_box hx), harnackExt_eq_sum_shell_mul_charge hd hR u hharm
          x]
    exact Finset.sum_congr rfl fun y hy => by simp only [if_pos hy]

/-! ### Green function estimates at scale `R` (the analytic input) -/

-- This is `LatticeProb.GreenTwoSided.killedGreenReal_le_box`, whose statement (`box`,
-- `graphNorm`, `Graph.killedGreenReal` are all shared top-level library definitions, not local
-- to the `GreenTwoSided` namespace) is byte-identical to this one, and which already has a
-- complete proof in scratch/decomp/green-two-sided/node.lean (line 658): head
-- `∑_{k<N} killedHeat ≤ N·C/r^d` from `srwHeat_gaussian`, tail via the killed Chapman–Kolmogorov
-- identity and `Network.sum_range_survival_le`.  Wire this file to that module (or a shared
-- `Network.KilledGreen`-adjacent module) instead of reproving it here.
/-- Implementation lemma for `killedGreenReal_le_box_of_mem`, obtained directly from
`LatticeProb.GreenTwoSided.killedGreenReal_le_box`. -/
private theorem killedGreenReal_le_box_of_mem' (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) →
      ∀ x y : Site d, x ≠ y →
        Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
          ≤ C * ((L : ℝ) + 1) ^ 2 * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) :=
  LatticeProb.GreenTwoSided.killedGreenReal_le_box hd

/-- The two-sided Green function upper bound `LatticeProb.GreenTwoSided.killedGreenReal_le_box`,
restated for use in the Harnack argument. -/
private theorem killedGreenReal_le_box_of_mem (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) →
      ∀ x y : Site d, x ≠ y →
        Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
          ≤ C * ((L : ℝ) + 1) ^ 2 * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := by
  exact killedGreenReal_le_box_of_mem' hd

-- y ∈ shell: y ∈ harnackBox (R+R/2) \ harnackBox (R+R/2-1) (unfold harnackShell,
-- Finset.mem_sdiff, mem_harnackBox_iff_mem_box), so some coordinate has R + R/2 - 1 < |y i| (not ∀,
-- box);
-- |x i| ≤ R, hence |y i - x i| ≥ R/2 ≥ 2 (abs_le, omega).  (y - x) i ≠ 0 gives y ≠ x;
-- |y i - x i|.natAbs ≤ graphNorm (y - x) (Finset.single_le_sum, unfold graphNorm), and
-- (R:ℝ)/4 ≤ R/2 (Nat.cast_div_le-type bound, R ≥ 4; or push_cast after omega on 4*(R/2) ≥ R).
/-- A shell point `y` is distinct from any `x ∈ box d R` and satisfies `graphNorm (y-x) ≥ R/4`. -/
private theorem ne_and_div_le_graphNorm_sub_of_mem_shell {R : ℕ} (hR : 4 ≤ R) {x y : Site d}
    (hx : x ∈ box d R)
    (hy : y ∈ harnackShell d R) : y ≠ x ∧ (R : ℝ) / 4 ≤ (graphNorm (y - x) : ℝ) := by
  rw [harnackShell] at hy
  obtain ⟨hybox, hynotmem⟩ := Finset.mem_sdiff.mp hy
  have hyboxed : y ∈ box d (R + R / 2) := (mem_harnackBox_iff_mem_box (R + R / 2) y).mp hybox
  have hne : ∃ i : Fin d, ((R + R / 2 - 1 : ℕ) : ℤ) < |y i|
  · obtain ⟨i, hi⟩ := not_forall.mp
      (fun hc => hynotmem ((mem_harnackBox_iff_mem_box (R + R / 2 - 1) y).mpr hc))
    exact ⟨i, not_le.mp hi⟩
  obtain ⟨i, _⟩ := hne
  have hxi : |x i| ≤ (R : ℤ) := hx i
  have hcast : ((R + R / 2 : ℕ) : ℤ) = ((R + R / 2 - 1 : ℕ) : ℤ) + 1
  · have h2 : R + R / 2 - 1 + 1 = R + R / 2
    · omega
    rw [← h2, Nat.cast_add]
    push_cast
    ring
  have hnatsub : ((R + R / 2 : ℕ) : ℤ) - (R : ℤ) = ((R / 2 : ℕ) : ℤ)
  · rw [Nat.cast_add]
    ring
  have hylow : ((R + R / 2 : ℕ) : ℤ) ≤ |y i|
  · rw [hcast]
    omega
  have hgeo : ((R / 2 : ℕ) : ℤ) ≤ |y i - x i|
  · have h1 : ((R / 2 : ℕ) : ℤ) ≤ |y i| - |x i|
    · linarith [hylow, hxi, hnatsub]
    have h2 : |y i| - |x i| ≤ |y i - x i|
    · have h := abs_add_le (y i - x i) (x i)
      have he : (y i - x i) + x i = y i
      · ring
      rw [he] at h
      linarith
    linarith
  have hnat : (R / 2 : ℕ) ≤ (y i - x i).natAbs
  · apply Int.ofNat_le.mp
    have hcast2 : (((y i - x i).natAbs : ℕ) : ℤ) = |y i - x i|
    · rw [← Int.natAbs_abs (y i - x i), Int.natAbs_of_nonneg (abs_nonneg (y i - x i))]
    rw [hcast2]
    exact hgeo
  have hgraph : (R / 2 : ℕ) ≤ graphNorm (y - x)
  · have h5 : (R / 2 : ℕ) ≤ ((y - x) i).natAbs
    · simpa only [Pi.sub_apply] using hnat
    rw [graphNorm]
    exact le_trans h5
        (Finset.single_le_sum (f := fun j => ((y - x) j).natAbs) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i))
  have h1R : ((R / 2 : ℕ) : ℝ) ≤ (graphNorm (y - x) : ℝ)
  · exact_mod_cast hgraph
  have h2R : (R : ℝ) / 4 ≤ ((R / 2 : ℕ) : ℝ)
  · have ha : R ≤ 2 * (R / 2) + 2
    · omega
    have hb : (2 : ℝ) ≤ ((R / 2 : ℕ) : ℝ)
    · have hbb : 2 ≤ R / 2
      · omega
      exact_mod_cast hbb
    have hc : (R : ℝ) ≤ 2 * ((R / 2 : ℕ) : ℝ) + 2
    · exact_mod_cast ha
    linarith
  refine ⟨?_, ?_⟩
  · intro hxy
    have hz : |y i - x i| = 0
    · rw [hxy]
      simp
    have h6 : ((R / 2 : ℕ) : ℤ) ≤ 0
    · rw [← hz]
      exact hgeo
    have h7 : (R / 2 : ℕ) ≤ 0
    · exact Int.ofNat_le.mp h6
    omega
  · linarith [h1R, h2R]


-- ((2R-1 : ℕ) : ℝ) + 1 = 2R (Nat.cast_sub, R ≥ 1); 1/r^d ≤ 4^d/R^d (one_div_le_one_div_of_le,
-- pow_le_pow_left₀, (R/4)^d = R^d/4^d); 1/(2R)^d ≤ 1/R^d; (2R)^2 = 4R^2; R^2/R^d = R^(2-d)
-- (zpow_sub₀, zpow_natCast).  SPLIT?
/-- Arithmetic bound converting the two-sided box estimate at radius `2R-1` and distance `≥ R/4`
into `C * 4 * (4^d+1) * R^{2-d}`. -/
private theorem mul_add_one_sq_mul_le_mul_rpow_two_sub (C : ℝ) (hC : 0 < C) {R : ℕ} (hR : 4 ≤ R)
    (r : ℝ) (hr : (R : ℝ) / 4 ≤ r) :
    C * (((2 * R - 1 : ℕ) : ℝ) + 1) ^ 2 * (1 / r ^ d + 1 / (((2 * R - 1 : ℕ) : ℝ) + 1) ^ d)
      ≤ C * 4 * (4 ^ d + 1) * (R : ℝ) ^ ((2 : ℤ) - d) := by
  have hRpos : (0:ℝ) < (R:ℝ) := (by
    have h4 : (4:ℝ) ≤ (R:ℝ) := (by exact_mod_cast hR)
    linarith)
  have hcast : ((2 * R - 1 : ℕ) : ℝ) + 1 = 2 * (R : ℝ) := (by
    have hle : 1 ≤ 2 * R := (by omega)
    rw [Nat.cast_sub hle]
    push_cast
    ring)
  have hz : (R:ℝ) ^ ((2:ℤ) - d) = (R:ℝ)^2 / (R:ℝ)^d := (by
    rw [zpow_sub₀ hRpos.ne' 2 (d:ℤ), zpow_ofNat, zpow_natCast])
  have hq : (0:ℝ) < (R:ℝ)/4 := (by linarith)
  have hvpos : (0:ℝ) < (2:ℝ) * (R:ℝ) := (by linarith)
  have hA1 : ((R:ℝ)/4) ^ d ≤ r ^ d := pow_le_pow_left₀ hq.le hr d
  have hA : (1:ℝ)/r^d ≤ (4:ℝ)^d/(R:ℝ)^d := (by
    have h := one_div_le_one_div_of_le (pow_pos hq d) hA1
    have h2 : (1:ℝ)/((R:ℝ)/4)^d = (4:ℝ)^d/(R:ℝ)^d := (by rw [div_pow, one_div_div])
    rwa [h2] at h)
  have hB1 : (R:ℝ)^d ≤ (2*(R:ℝ))^d := pow_le_pow_left₀ hRpos.le (by linarith) d
  have hB : (1:ℝ)/(2*(R:ℝ))^d ≤ (1:ℝ)/(R:ℝ)^d :=
    one_div_le_one_div_of_le (pow_pos hRpos d) hB1
  have hsum : (1:ℝ)/r^d + 1/(2*(R:ℝ))^d ≤ (4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d :=
    add_le_add hA hB
  have hmain : (2*(R:ℝ))^2 * ((4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d)
      = 4 * (4^d + 1) * ((R:ℝ)^2/(R:ℝ)^d) := (by
    rw [← add_div]
    field_simp
    ring)
  calc C * (((2*R-1:ℕ):ℝ) + 1)^2 * (1/r^d + 1/(((2*R-1:ℕ):ℝ)+1)^d)
      = C * (2*(R:ℝ))^2 * (1/r^d + 1/(2*(R:ℝ))^d) := (by rw [hcast])
    _ ≤ C * (2*(R:ℝ))^2 * ((4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hC.le (pow_nonneg hvpos.le 2))
    _ = C * ((2*(R:ℝ))^2 * ((4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d)) := (by ring)
    _ = C * (4 * (4^d + 1) * ((R:ℝ)^2/(R:ℝ)^d)) := (by rw [hmain])
    _ = C * 4 * (4^d + 1) * (R:ℝ)^((2:ℤ) - d) := (by rw [hz]; ring)


-- C' := C * 4 * (4^d + 1) from killedGreenReal_le_box_of_mem.  harnackGreen B x y = killedGreenReal
-- B y x
-- (unfold harnackGreen); apply killedGreenReal_le_box_of_mem with L := 2R-1, B := harnackBox d
-- (2R-1)
-- (members in box via mem_harnackBox_iff_mem_box), the pair (y, x)
-- (ne_and_div_le_graphNorm_sub_of_mem_shell); then mul_add_one_sq_mul_le_mul_rpow_two_sub
-- with r := graphNorm (y - x), and ((2R-1:ℕ):ℝ) is the L of killedGreenReal_le_box_of_mem
-- (Nat.cast).
/-- The Green function upper bound on the shell: `harnackGreen (harnackBox (2R-1)) x y ≤ C
R^{2-d}` for `x ∈ box d R`, `y ∈ harnackShell d R`. -/
private theorem harnackGreen_le_mul_rpow_two_sub (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 4 ≤ R → ∀ x ∈ box d R, ∀ y ∈ harnackShell d R,
      harnackGreen (harnackBox d (2 * R - 1)) x y ≤ C * (R : ℝ) ^ ((2 : ℤ) - d) := by
  obtain ⟨C, hC, hup⟩ := killedGreenReal_le_box_of_mem hd
  refine ⟨C * 4 * (4 ^ d + 1), by positivity, fun R hR x hx y hy => ?_⟩
  obtain ⟨hyx, hr⟩ := ne_and_div_le_graphNorm_sub_of_mem_shell hR hx hy
  unfold harnackGreen
  refine le_trans (hup (2 * R - 1) (harnackBox d (2 * R - 1))
    (fun z hz => (mem_harnackBox_iff_mem_box _ z).1 hz) y x hyx) ?_
  exact mul_add_one_sq_mul_le_mul_rpow_two_sub C hC hR _ hr

-- This is `LatticeProb.GreenTwoSided.killedGreenReal_ge_box` (same shared top-level definitions
-- as `killedGreenReal_le_box_of_mem'`), which is itself still an open lemma in
-- scratch/decomp/green-two-sided/node.lean (line 1966); once that file's carving of it lands,
-- wire this file to it instead of reproving it here.  Route (there): lazy killed walk (binomial
-- mixture of `killedHeat`), free lazy near-diagonal lower bound from `iterate_delta0_eq` and the
-- 1D local CLT `exists_srwHeat_one_sub_gauss_le_int`, killing correction from the off-diagonal
-- bound, chaining over `O_K(1)` cubes of side `≍ ρ` at `s²` different times; small `ρ` by a
-- lattice path.
/-- Implementation lemma for `killedGreenReal_ge_box_of_mem`, obtained directly from
`LatticeProb.GreenTwoSided.killedGreenReal_ge_box`. -/
private theorem killedGreenReal_ge_box_of_mem' (hd : 1 ≤ d) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ρ : ℕ), 1 ≤ ρ → m ≤ K * ρ → ∀ B : Finset (Site d),
      (∀ z ∈ box d (m + ρ), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
        c * (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y :=
  LatticeProb.GreenTwoSided.killedGreenReal_ge_box hd K

/-- The two-sided Green function lower bound `LatticeProb.GreenTwoSided.killedGreenReal_ge_box`,
restated for use in the Harnack argument. -/
private theorem killedGreenReal_ge_box_of_mem (hd : 1 ≤ d) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ρ : ℕ), 1 ≤ ρ → m ≤ K * ρ → ∀ B : Finset (Site d),
      (∀ z ∈ box d (m + ρ), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
        c * (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  exact killedGreenReal_ge_box_of_mem' hd K

-- omega.
/-- Arithmetic facts about the gap `2R-1-(R+R/2)` between the two nested boxes, needed to apply
the Green-function lower bound at that scale. -/
private theorem harnackBox_gap_bounds {R : ℕ} (hR : 4 ≤ R) :
    1 ≤ 2 * R - 1 - (R + R / 2) ∧ R + R / 2 ≤ 6 * (2 * R - 1 - (R + R / 2)) ∧
      R + R / 2 + (2 * R - 1 - (R + R / 2)) = 2 * R - 1 ∧
      R ≤ 4 * (2 * R - 1 - (R + R / 2)) ∧ 2 * R - 1 - (R + R / 2) ≤ R := by
  omega

-- d = 1: zpow_one, R ≤ 4ρ.  d ≥ 2: exponent 2 - d ≤ 0 and ρ ≤ R give R^(2-d) ≤ ρ^(2-d)
-- (zpow_le_zpow_left₀ on inverses / one_div_le_one_div_of_le after zpow_neg), then R^(2-d)/4 ≤
-- R^(2-d).
/-- For `ρ ≤ R ≤ 4ρ`, `(1/4) R^{2-d} ≤ ρ^{2-d}`. -/
private theorem rpow_two_sub_div_four_le_rpow_two_sub {R ρ : ℕ} (hρ : 1 ≤ ρ) (hρR : ρ ≤ R)
    (hRρ : R ≤ 4 * ρ) (hd : 1 ≤ d) :
    (1 / 4 : ℝ) * (R : ℝ) ^ ((2 : ℤ) - d) ≤ (ρ : ℝ) ^ ((2 : ℤ) - d) := by
  have hρ1 : (1 : ℝ) ≤ (ρ : ℝ) := Nat.one_le_cast.mpr hρ
  have hρR' : (ρ : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr hρR
  have hR4 : (R : ℝ) ≤ 4 * (ρ : ℝ) := (Nat.cast_le.mpr hRρ).trans (le_of_eq (Nat.cast_mul 4 ρ))
  have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hρ1.trans hρR')
  have hρpos : (0 : ℝ) < (ρ : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hρ1
  rcases eq_or_lt_of_le hd with h1 | h1
  · subst h1
    norm_num
    linarith
  · have hd2 : 2 ≤ d := Nat.succ_le_of_lt h1
    have he : (2 : ℤ) - (d : ℤ) = -(((d - 2 : ℕ) : ℤ)) :=
      (neg_sub (d : ℤ) 2).symm.trans (congrArg Neg.neg (Nat.cast_sub hd2)).symm
    rw [he, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    have hk : (ρ : ℝ) ^ (d - 2) ≤ (R : ℝ) ^ (d - 2) := pow_le_pow_left₀ hρpos.le hρR' (d - 2)
    have hp : 0 < (ρ : ℝ) ^ (d - 2) := pow_pos hρpos (d - 2)
    have hq : 0 < (R : ℝ) ^ (d - 2) := pow_pos hRpos (d - 2)
    have hinv : ((R : ℝ) ^ (d - 2))⁻¹ ≤ ((ρ : ℝ) ^ (d - 2))⁻¹ := (inv_le_inv₀ hq hp).mpr hk
    have h4 : (1 / 4 : ℝ) * ((R : ℝ) ^ (d - 2))⁻¹ ≤ ((R : ℝ) ^ (d - 2))⁻¹ :=
      mul_le_of_le_one_left (inv_nonneg.mpr hq.le) (by norm_num)
    linarith


-- c' := c/4 from killedGreenReal_ge_box_of_mem with K := 6, m := R + R/2, ρ := 2R-1-(R+R/2)
-- (harnackBox_gap_bounds);
-- B := harnackBox d (2R-1) contains box (m + ρ) = box (2R-1) (mem_harnackBox_iff_mem_box);
-- x' ∈ box m by mem_box_of_le, y ∈ box m by harnackShell_subset_harnackBox_add_div_two +
-- mem_harnackBox_iff_mem_box;
-- harnackGreen B x' y = killedGreenReal B y x' (unfold); rpow_two_sub_div_four_le_rpow_two_sub,
-- mul_le_mul_of_nonneg_left.
/-- The Green function lower bound on the shell: `c R^{2-d} ≤ harnackGreen (harnackBox (2R-1)) x
y` for `x ∈ box d R`, `y ∈ harnackShell d R`. -/
private theorem mul_rpow_two_sub_le_harnackGreen (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℕ, 4 ≤ R → ∀ x ∈ box d R, ∀ y ∈ harnackShell d R,
      c * (R : ℝ) ^ ((2 : ℤ) - d) ≤ harnackGreen (harnackBox d (2 * R - 1)) x y := by
  obtain ⟨c, hc, hlow⟩ := killedGreenReal_ge_box_of_mem hd 6
  refine ⟨c / 4, by positivity, fun R hR x hx y hy => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := harnackBox_gap_bounds hR
  have hB : ∀ z ∈ box d (R + R / 2 + (2 * R - 1 - (R + R / 2))), z ∈ harnackBox d (2 * R - 1) := by
    intro z hz
    rw [h3] at hz
    exact (mem_harnackBox_iff_mem_box _ z).2 hz
  have hyK : y ∈ box d (R + R / 2) := (mem_harnackBox_iff_mem_box _ y).1
      (harnackShell_subset_harnackBox_add_div_two hy)
  have hxK : x ∈ box d (R + R / 2) := mem_box_of_le (by omega) hx
  have key := hlow (R + R / 2) (2 * R - 1 - (R + R / 2)) h1 h2 (harnackBox d (2 * R - 1)) hB
    y hyK x hxK
  have hconv := rpow_two_sub_div_four_le_rpow_two_sub h1 h5 h4 hd
  unfold harnackGreen
  calc c / 4 * (R : ℝ) ^ ((2 : ℤ) - d)
      = c * ((1 / 4 : ℝ) * (R : ℝ) ^ ((2 : ℤ) - d)) := by ring
    _ ≤ c * ((2 * R - 1 - (R + R / 2) : ℕ) : ℝ) ^ ((2 : ℤ) - d) :=
        mul_le_mul_of_nonneg_left hconv hc.le
    _ ≤ _ := key

-- C := C₁ / c₀ from harnackGreen_le_mul_rpow_two_sub / mul_rpow_two_sub_le_harnackGreen; R^(2-d) >
-- 0 by zpow_pos;
-- g(x,y) ≤ C₁ R^(2-d) = (C₁/c₀) (c₀ R^(2-d)) ≤ (C₁/c₀) g(x',y)  (div_mul_cancel₀,
-- mul_le_mul_of_nonneg_left).
/-- A Harnack comparison for the Green function itself: `harnackGreen (harnackBox (2R-1)) x y ≤ C
* harnackGreen (harnackBox (2R-1)) x' y` for `x, x' ∈ box d R`, `y` on the shell, combining
the upper and lower bounds. -/
private theorem harnackGreen_le_mul_harnackGreen (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 4 ≤ R → ∀ x ∈ box d R, ∀ x' ∈ box d R,
      ∀ y ∈ harnackShell d R,
        harnackGreen (harnackBox d (2 * R - 1)) x y
          ≤ C * harnackGreen (harnackBox d (2 * R - 1)) x' y := by
  obtain ⟨C1, hC1pos, hC1⟩ := harnackGreen_le_mul_rpow_two_sub hd
  obtain ⟨c0, hc0pos, hc0⟩ := mul_rpow_two_sub_le_harnackGreen hd
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0pos
  have hCpos : (0 : ℝ) < C1 / c0 := div_pos hC1pos hc0pos
  refine ⟨C1 / c0, hCpos, fun R hR x hx x' hx' y hy => ?_⟩
  have h1 : harnackGreen (harnackBox d (2 * R - 1)) x y ≤ C1 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)) :=
    hC1 R hR x hx y hy
  have h2 : c0 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)) ≤ harnackGreen (harnackBox d (2 * R - 1)) x' y :=
    hc0 R hR x' hx' y hy
  have hA : (C1 / c0) * (c0 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)))
      = C1 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)) :=
    (mul_assoc _ _ _).symm.trans
      (congrArg (· * ((R : ℝ) ^ ((2 : ℤ) - (d : ℤ)))) (div_mul_cancel₀ C1 hc0ne))
  exact le_trans h1 (le_trans (le_of_eq hA.symm) (mul_le_mul_of_nonneg_left h2 (le_of_lt hCpos)))


-- exists_nonneg_eq_sum_shell_mul gives ν; u x = ∑ g(x,y)ν y ≤ ∑ C g(x',y) ν y = C u x'
-- (Finset.sum_le_sum, mul_le_mul_of_nonneg_right with ν ≥ 0, Finset.mul_sum, mul_assoc); C from
-- harnackGreen_le_mul_harnackGreen.
/-- The Harnack inequality for `R ≥ 4`: `u x ≤ C u y` for `x, y ∈ box d R`, from the Riesz
representation `exists_nonneg_eq_sum_shell_mul` and the Green-function comparison
`harnackGreen_le_mul_harnackGreen`. -/
theorem le_mul_of_nonneg_harmonicOn (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (u : Site d → ℝ), 4 ≤ R →
      (∀ x ∈ box d (2 * R), 0 ≤ u x) →
      (∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) →
      ∀ x ∈ box d R, ∀ y ∈ box d R, u x ≤ C * u y := by
  obtain ⟨C, hCpos, hC⟩ := harnackGreen_le_mul_harnackGreen hd
  refine ⟨C, hCpos, ?_⟩
  intro R u hR hpos hharm x hx y hy
  obtain ⟨ν, hν, hu⟩ := exists_nonneg_eq_sum_shell_mul hd hR u hpos hharm
  rw [hu x hx, hu y hy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have h1 : harnackGreen (harnackBox d (2 * R - 1)) x z ≤
      C * harnackGreen (harnackBox d (2 * R - 1)) y z := hC R hR x hx y hy z hz
  have h2 : 0 ≤ ν z := hν z
  nlinarith [h1, h2]

end LatticeProb
