module

public import LatticeProb.Walk.PotentialKernel
public import LatticeProb.Walk.Harnack.Basics
public import LatticeProb.Walk.Lazy
public import LatticeProb.Walk.Ball
public import LatticeProb.Network.MaximumPrinciple
public import LatticeProb.Network.KilledGreen

@[expose] public section

/-!
# Logarithmic lower bound for the killed Green function of the planar box

For the simple random walk on `ℤ²` killed outside the box `originBox 2 L`, the killed Green
function at the origin is at least `(1 / (2π)) log (L + 1)` up to an additive constant.

The proof compares `-(a / 4 + g)` with the maximum principle, where `a` is the potential kernel
and `g = g_D(0, ·)` is the killed Green function on the box `D`. The function `a / 4 + g` is
harmonic on all of `D`, including the source, since `Δa = 4 δ₀` and `Δg = -δ₀` on `D`.
Off `D` it equals `a / 4`, which the potential kernel asymptotic bounds below by a logarithm of the
radius. The maximum principle then transfers this bound to the origin, where `a(0) = 0`.
-/

namespace LatticeProb

/-- A site with a coordinate of absolute value above `L` lies outside the box of radius `L`. -/
theorem notMem_originBox_of_lt {L : ℕ} {x : Site 2} {i : Fin 2} (h : (L : ℤ) < x i) :
    x ∉ originBox 2 L := by
  intro hx
  unfold originBox at hx
  have hi := Fintype.mem_piFinset.mp hx i
  simp only [Finset.mem_Icc] at hi
  exact absurd hi.2 (not_le.mpr h)

/-- The origin lies in every box. -/
theorem zero_mem_originBox (L : ℕ) : (0 : Site 2) ∈ originBox 2 L := by
  unfold originBox
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;> simp

/-- Each coordinate of a site is at most its Euclidean norm in absolute value. -/
theorem abs_coord_le_euclidNorm (x : Site 2) (i : Fin 2) :
    |((x i : ℤ) : ℝ)| ≤ euclidNorm x := by
  rw [euclidNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j : Fin 2 => ((x j : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- Off the box of radius `L`, the Euclidean norm is at least `L + 1`. -/
theorem euclidNorm_ge_of_notMem_originBox {L : ℕ} {x : Site 2} (hx : x ∉ originBox 2 L) :
    (L : ℝ) + 1 ≤ euclidNorm x := by
  obtain ⟨i, hi⟩ := exists_of_notMem_box hx
  have hi' : (L : ℤ) + 1 ≤ |x i| := Int.add_one_le_of_lt hi
  have hr : (L : ℝ) + 1 ≤ |((x i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hi'
  exact hr.trans (abs_coord_le_euclidNorm x i)

/-- Off the box of radius `L`, for `L` at least a fixed threshold, the potential kernel is at
least `(2/π) log (L + 1)` up to an additive constant. -/
theorem potentialKernel_ge_log_outside_box :
    ∃ K R : ℝ, 1 ≤ R ∧ ∀ L : ℕ, R ≤ (L : ℝ) →
      ∀ x : Site 2, x ∉ originBox 2 L →
      2 / Real.pi * Real.log ((L : ℝ) + 1) + K ≤ potentialKernel x := by
  obtain ⟨κ, C, R, hR, h⟩ := exists_abs_potentialKernel_sub_log_le
  refine ⟨κ - |C|, R, hR, fun L hLR x hx => ?_⟩
  have hN : (L : ℝ) + 1 ≤ euclidNorm x := euclidNorm_ge_of_notMem_originBox hx
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hpos : (1 : ℝ) ≤ euclidNorm x := by linarith
  have hb := h x (by linarith)
  have ht0 : 0 ≤ euclidNorm x ^ (-2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have ht1 : euclidNorm x ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hpos (by norm_num)
  have hlow := (abs_le.mp hb).1
  have hCt : C * euclidNorm x ^ (-2 : ℝ) ≤ |C| := by
    calc
      C * euclidNorm x ^ (-2 : ℝ) ≤ |C| * euclidNorm x ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) ht0
      _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) ht1
  have hlog : Real.log ((L : ℝ) + 1) ≤ Real.log (euclidNorm x) :=
    Real.log_le_log (by linarith) hN
  have hmul : 2 / Real.pi * Real.log ((L : ℝ) + 1) ≤ 2 / Real.pi * Real.log (euclidNorm x) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- The potential kernel has discrete Laplacian `4 δ₀`. -/
theorem laplacian_potentialKernel (x : Site 2) :
    Graph.laplacian (lattice 2) potentialKernel x = 4 * (if x = 0 then 1 else 0) := by
  have h1 := laplacian_eq_nbrSum_sub (d := 2) (by norm_num) potentialKernel x
  have h2 := walkOp_potentialKernel_sub x
  have h3 : nbrSum potentialKernel x = 4 * walkOp potentialKernel x := by
    simp only [walkOp, Nat.cast_ofNat]
    ring_nf
  rw [h1]
  push_cast
  linear_combination 4 * h2 + h3

/-- The Laplacian of `-(u / 4 + v)` is `-(Δu / 4 + Δv)`. -/
theorem laplacian_neg_combo (u v : Site 2 → ℝ) (x : Site 2) :
    Graph.laplacian (lattice 2) (fun y => -(u y / 4 + v y)) x
      = -(Graph.laplacian (lattice 2) u x / 4 + Graph.laplacian (lattice 2) v x) := by
  have h1 : ∑ y ∈ (lattice 2).neighborFinset x, (-(u y / 4 + v y) - -(u x / 4 + v x))
      = -((∑ y ∈ (lattice 2).neighborFinset x, (u y - u x)) / 4
          + ∑ y ∈ (lattice 2).neighborFinset x, (v y - v x)) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring_nf
  exact h1

/-- Maximum principle comparison: if `m ≤ a / 4` off the box `D` of radius `L`, where `a` is the
potential kernel, then `m ≤ g_D(0, 0)`. -/
theorem killedGreen_zero_zero_ge_of_outside (L : ℕ) (m : ℝ)
    (hm : ∀ x : Site 2, x ∉ originBox 2 L → m ≤ potentialKernel x / 4) :
    m ≤ Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 0 := by
  haveI : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  have hG : (lattice 2).Connected := Graph.Zd.latticeConnected 2
  have hq : (![(L : ℤ) + 1, 0] : Site 2) ∉ originBox 2 L :=
    notMem_originBox_of_lt (i := 0) (by simp)
  have hharm : ∀ x ∈ originBox 2 L, x ∉ (∅ : Set (Site 2)) →
      Network.netLaplacian (lattice 2) (Network.unitCond (lattice 2))
        (fun y => -(potentialKernel y / 4
          + Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 y)) x = 0 := by
    intro x hx _
    rw [Network.netLaplacian_unitCond,
      laplacian_neg_combo potentialKernel (Graph.killedGreenReal (lattice 2)
        (originBox 2 L : Set (Site 2)) 0),
      laplacian_potentialKernel,
      Network.laplacian_killedGreenReal hG (originBox 2 L) (zero_mem_originBox L) hq
        (Finset.mem_coe.mpr hx)]
    ring_nf
  have hout : ∀ x : Site 2, x ∉ originBox 2 L →
      (fun y => -(potentialKernel y / 4
        + Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 y)) x ≤ -m := by
    intro x hx
    have hg := Network.killedGreenReal_eq_zero_of_not_mem hG (originBox 2 L) hq hx 0
    have hmx := hm x hx
    show -(potentialKernel x / 4
      + Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 x) ≤ -m
    rw [hg]
    linarith
  have hS : ∀ x ∈ (∅ : Set (Site 2)),
      (fun y => -(potentialKernel y / 4
        + Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 y)) x ≤ -m :=
    fun x hx => absurd hx (Set.notMem_empty x)
  have hF := Network.le_of_harmonicOn hG Network.isCond_unitCond (originBox 2 L) ∅
    (fun y => -(potentialKernel y / 4
      + Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 y))
    (-m) hq hharm hout hS 0
  have h00 : -(potentialKernel 0 / 4
      + Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 0) ≤ -m := hF
  rw [potentialKernel_zero] at h00
  linarith

/-- **Planar killed Green logarithmic lower bound.** There are a constant `c > 0` and a threshold
`L0 ≥ 1` such that the killed Green function at the origin of the box of radius `L` is at least
`c log (L + 2)` for all `L ≥ L0`. -/
theorem planar_killedGreen_zero_zero_log_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L : ℕ, L0 ≤ L →
      c * Real.log ((L : ℝ) + 2)
        ≤ Graph.killedGreenReal (lattice 2) (originBox 2 L : Set (Site 2)) 0 0 := by
  obtain ⟨K, R, hR1, hK⟩ := potentialKernel_ge_log_outside_box
  obtain ⟨N, hN⟩ := exists_nat_gt (max R (Real.exp (-(Real.pi * K))))
  have hRN : R < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hEN : Real.exp (-(Real.pi * K)) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : (1 : ℝ) ≤ N := le_trans hR1 hRN.le
  refine ⟨1 / (8 * Real.pi), by positivity, N, by exact_mod_cast hN1, fun L hL => ?_⟩
  have hNL : (N : ℝ) ≤ L := by exact_mod_cast hL
  have hLR : R ≤ (L : ℝ) := le_trans hRN.le hNL
  have hL1 : (1 : ℝ) ≤ L := le_trans hN1 hNL
  have hg := killedGreen_zero_zero_ge_of_outside L
    ((2 / Real.pi * Real.log ((L : ℝ) + 1) + K) / 4)
    (fun x hx => by have := hK L hLR x hx; linarith)
  have hEL : Real.exp (-(Real.pi * K)) < (L : ℝ) + 1 := by linarith
  have hlogL : -(Real.pi * K) < Real.log ((L : ℝ) + 1) := by
    have h := Real.log_lt_log (Real.exp_pos _) hEL
    rwa [Real.log_exp] at h
  have hlog2 : Real.log ((L : ℝ) + 2) ≤ 2 * Real.log ((L : ℝ) + 1) := by
    have hsq : Real.log (((L : ℝ) + 1) ^ 2) = 2 * Real.log ((L : ℝ) + 1) := by
      rw [Real.log_pow]
      norm_num
    rw [← hsq]
    have hpoly : (L : ℝ) + 2 ≤ ((L : ℝ) + 1) ^ 2 := by
      calc
        (L : ℝ) + 2 = ((L : ℝ) + 1) + 1 := by ring_nf
        _ ≤ ((L : ℝ) + 1) + ((L : ℝ) + 1) :=
          add_le_add le_rfl (hL1.trans (le_add_of_nonneg_right zero_le_one))
        _ = (1 + 1) * ((L : ℝ) + 1) := by ring_nf
        _ ≤ ((L : ℝ) + 1) * ((L : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (add_le_add hL1 le_rfl) (by positivity)
        _ = ((L : ℝ) + 1) ^ 2 := (pow_two _).symm
    exact Real.log_le_log (by linarith) hpoly
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
  have key1 : 1 / (8 * Real.pi) * Real.log ((L : ℝ) + 2)
      ≤ 1 / (8 * Real.pi) * (2 * Real.log ((L : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hid : (2 / Real.pi * Real.log ((L : ℝ) + 1) + K) / 4
      - 1 / (8 * Real.pi) * (2 * Real.log ((L : ℝ) + 1))
      = (Real.log ((L : ℝ) + 1) + Real.pi * K) / (4 * Real.pi) := by
    field_simp
    ring_nf
  have hnn : 0 ≤ (Real.log ((L : ℝ) + 1) + Real.pi * K) / (4 * Real.pi) :=
    div_nonneg (by linarith) (by positivity)
  linarith

end LatticeProb
