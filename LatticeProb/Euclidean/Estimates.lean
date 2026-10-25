module

public import LatticeProb.Euclidean.Lattice
public import LatticeProb.Euclidean.Shell
public import LatticeProb.Euclidean.Series

@[expose] public section

/-!
# Upper and exterior bounds for scaled radial sums

For `d ≥ 1`, `α ≥ 0` and `ε ∈ (0,1)`, the scaled sums `ε^d ∑ |ε z|^{-α}` over the nonzero integer
points `z` with `ε z` in the closed unit ball, `unitBallIndices d ε`, are bounded uniformly in `ε`
when `α < d`.  The upper bound has three regimes: at `α = d` it is at most `C (1 + |log ε|)`, and
at `α > d` it is at most `C ε^{d-α}`.  The exterior bound, for `α > d`, asserts summability of the
indicator sum and bounds `ε^d` times it uniformly in `ε`.  Each constant depends only on `α` and
`d`.
-/

noncomputable section

open scoped BigOperators
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell LatticeProb.Euclidean.Series

namespace LatticeProb.Euclidean.Estimates

/-- One Euclidean shell.  A finite set of lattice points whose radii all lie in `[n, n+1)`,
with `n ≥ 1`, contributes at most `shellConstant d · n^{d-1-α}` to `∑ |w|^{-α}`. -/
lemma shell_rpow_sum_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α) {n : ℕ} (hn : 1 ≤ n)
    (s : Finset (Site d)) (hs : ∀ w ∈ s, Nat.floor (radius (physical 1 w)) = n) :
    ∑ w ∈ s, (radius (physical 1 w)) ^ (-α) ≤
      shellConstant d * (n : ℝ) ^ ((d : ℝ) - 1 - α) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdom : ∀ w ∈ s, (n : ℝ) ≤ radius (physical 1 w) ∧ radius (physical 1 w) < n + 1 := by
    intro w hw
    constructor
    · rw [← hs w hw]
      exact Nat.floor_le (radius_nonneg _)
    · rw [← hs w hw]
      exact Nat.lt_floor_add_one _
  have hc := shell_card d hd n hnreal s hdom
  have hp : ∀ w ∈ s, (radius (physical 1 w)) ^ (-α) ≤ (n : ℝ) ^ (-α) := by
    intro w hw
    exact Real.rpow_le_rpow_of_nonpos hnpos (hdom w hw).1 (by linarith)
  have he : (n : ℝ) ^ ((d : ℝ) - 1 - α) = (n : ℝ) ^ (d - 1) * (n : ℝ) ^ (-α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hnpos, Nat.cast_sub hd]
    congr 1
    push_cast
    ring
  rw [he]
  calc
    ∑ w ∈ s, (radius (physical 1 w)) ^ (-α) ≤ ∑ _w ∈ s, (n : ℝ) ^ (-α) := Finset.sum_le_sum hp
    _ = (s.card : ℝ) * (n : ℝ) ^ (-α) := by simp
    _ ≤ (shellConstant d * (n : ℝ) ^ (d - 1)) * (n : ℝ) ^ (-α) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hnpos.le _)
    _ = shellConstant d * ((n : ℝ) ^ (d - 1) * (n : ℝ) ^ (-α)) := by ring

/-- A finite set of nonzero lattice points, grouped by the integer part of its radius. -/
lemma shell_rpow_sum_le_fiber {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α)
    (u : Finset (Site d)) (hu : ∀ w ∈ u, w ≠ 0) :
    ∑ w ∈ u, (radius (physical 1 w)) ^ (-α) ≤
      shellConstant d * ∑ n ∈ u.image (fun w => Nat.floor (radius (physical 1 w))),
        (n : ℝ) ^ ((d : ℝ) - 1 - α) := by
  classical
  have hmem : ∀ w ∈ u, 1 ≤ Nat.floor (radius (physical 1 w)) := fun w hw =>
    (Nat.one_le_floor_iff _).mpr (lattice_radius_ge_one (hu w hw))
  have he := Finset.sum_fiberwise_of_maps_to (s := u)
    (t := u.image (fun w => Nat.floor (radius (physical 1 w))))
    (g := fun w => Nat.floor (radius (physical 1 w)))
    (fun w hw => Finset.mem_image_of_mem _ hw) (fun w => (radius (physical 1 w)) ^ (-α))
  refine he.symm.le.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    exact hmem w hw
  exact shell_rpow_sum_le hd hα hn1 _ (fun w hw => (Finset.mem_filter.mp hw).2)

/-- The cutoff sum over `unitBallIndices d ε` is at most `shellConstant d` times the shell sums up
to `⌊1/ε⌋₊`, reduced to the integer part of the radius. -/
lemma unitBallIndices_rpow_sum_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∑ z ∈ unitBallIndices d ε, (radius (physical 1 z)) ^ (-α) ≤
      shellConstant d * ∑ n ∈ Finset.Icc 1 ⌊1 / ε⌋₊, (n : ℝ) ^ ((d : ℝ) - 1 - α) := by
  classical
  have hnz : ∀ z ∈ unitBallIndices d ε, z ≠ 0 := fun z hz => ((mem_unitBallIndices hε z).mp hz).1
  have hle : ∀ z ∈ unitBallIndices d ε,
      Nat.floor (radius (physical 1 z)) ∈ Finset.Icc 1 ⌊1 / ε⌋₊ := by
    intro z hz
    have hr : ε * radius (physical 1 z) ≤ 1 := by
      have h := ((mem_unitBallIndices hε z).mp hz).2
      rwa [radius_physical_eq_mul hε.le] at h
    have hr' : radius (physical 1 z) ≤ 1 / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact hr
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_floor_iff _).mpr (lattice_radius_ge_one (hnz z hz)),
      Nat.floor_le_floor hr'⟩
  have h2 : ∑ n ∈ (unitBallIndices d ε).image (fun w => Nat.floor (radius (physical 1 w))),
      (n : ℝ) ^ ((d : ℝ) - 1 - α)
      ≤ ∑ n ∈ Finset.Icc 1 ⌊1 / ε⌋₊, (n : ℝ) ^ ((d : ℝ) - 1 - α) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
      exact hle w hw
    · intro n _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    _ ≤ shellConstant d *
          ∑ n ∈ (unitBallIndices d ε).image (fun w => Nat.floor (radius (physical 1 w))),
          (n : ℝ) ^ ((d : ℝ) - 1 - α) := shell_rpow_sum_le_fiber hd hα (unitBallIndices d ε) hnz
    _ ≤ shellConstant d * ∑ n ∈ Finset.Icc 1 ⌊1 / ε⌋₊, (n : ℝ) ^ ((d : ℝ) - 1 - α) :=
        mul_le_mul_of_nonneg_left h2 (shellConstant_pos hd).le

/-- Scaling identity: `ε^d ∑ |ε z|^{-α} = ε^(d-α) ∑ |z|^{-α}`, summing over
`unitBallIndices d ε`. -/
lemma scaled_sum_eq {d : ℕ} {α ε : ℝ} (hε : 0 < ε) :
    ε ^ d * (∑ z ∈ unitBallIndices d ε, (radius (physical ε z)) ^ (-α)) =
      ε ^ ((d : ℝ) - α) * ∑ z ∈ unitBallIndices d ε, (radius (physical 1 z)) ^ (-α) := by
  have hsplit : ε ^ ((d : ℝ) - α) = ε ^ d * ε ^ (-α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hε, sub_eq_add_neg]
  rw [hsplit, mul_assoc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [radius_physical_eq_mul hε.le z, Real.mul_rpow hε.le (radius_nonneg (physical 1 z))]

/-- **Upper bound for scaled radial sums.** For `d ≥ 1` and `α ≥ 0`, the sum `ε^d ∑ |ε z|^{-α}`
over `unitBallIndices d ε` is bounded uniformly in `ε ∈ (0,1)` when `α < d`; at `α = d` it is at
most `C (1 + |log ε|)`, and for `α > d` it is at most `C ε^{d-α}`.  The constant `C` depends only on
`α` and `d`. -/
theorem rpow_sum_upper_bound (d : ℕ) (hd : 1 ≤ d) :
    ∀ α : ℝ, 0 ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε ^ d * (∑ z ∈ unitBallIndices d ε, (radius (physical ε z)) ^ (-α)) ≤
        if α < (d : ℝ) then C
        else if α = (d : ℝ) then C * (1 + |Real.log ε|)
        else C * ε ^ ((d : ℝ) - α) := by
  intro α hα
  have hS := shellConstant_pos hd
  rcases lt_trichotomy α (d : ℝ) with hlt | heq | hgt
  · -- regime `α < d`: the exponent `γ = d - α` is positive and the sum is `≍ ε^{-γ}`
    have hγpos : 0 < (d : ℝ) - α := by linarith
    have hβ : -1 < (d : ℝ) - 1 - α := by linarith
    refine ⟨shellConstant d * (1 + 1 / ((d : ℝ) - α)), ?_, ?_⟩
    · have h1 : 0 < 1 + 1 / ((d : ℝ) - α) := by
        have := one_div_pos.mpr hγpos
        linarith
      exact mul_pos hS h1
    · intro ε hε
      rw [if_pos hlt, scaled_sum_eq hε.1]
      have hsum := unitBallIndices_rpow_sum_le hd hα hε.1
      have hT := sum_rpow_Icc_le_unified hβ ⌊1 / ε⌋₊
      have hβγ : (d : ℝ) - 1 - α + 1 = (d : ℝ) - α := by ring
      rw [hβγ] at hT
      have hinvε : 0 ≤ 1 / ε := div_nonneg zero_le_one hε.1.le
      have hNle : ((⌊1 / ε⌋₊ : ℕ) : ℝ) ≤ 1 / ε := Nat.floor_le hinvε
      have hNpow : ((⌊1 / ε⌋₊ : ℕ) : ℝ) ^ ((d : ℝ) - α) ≤ (1 / ε) ^ ((d : ℝ) - α) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hNle hγpos.le
      have hγinv : 0 ≤ 1 + 1 / ((d : ℝ) - α) := by
        have := one_div_pos.mpr hγpos
        linarith
      have hepow : ε ^ ((d : ℝ) - α) * (1 / ε) ^ ((d : ℝ) - α) = 1 := by
        rw [← Real.mul_rpow hε.1.le hinvε, mul_one_div_cancel hε.1.ne', Real.one_rpow]
      have hε0 : 0 ≤ ε ^ ((d : ℝ) - α) := Real.rpow_nonneg hε.1.le _
      calc ε ^ ((d : ℝ) - α) * ∑ z ∈ unitBallIndices d ε, (radius (physical 1 z)) ^ (-α)
          ≤ ε ^ ((d : ℝ) - α) * (shellConstant d *
              ∑ n ∈ Finset.Icc 1 ⌊1 / ε⌋₊, (n : ℝ) ^ ((d : ℝ) - 1 - α)) :=
            mul_le_mul_of_nonneg_left hsum hε0
        _ ≤ ε ^ ((d : ℝ) - α) * (shellConstant d *
              ((1 + 1 / ((d : ℝ) - α)) * (1 / ε) ^ ((d : ℝ) - α))) := by
            refine mul_le_mul_of_nonneg_left ?_ hε0
            refine mul_le_mul_of_nonneg_left ?_ (shellConstant_pos hd).le
            exact hT.trans (mul_le_mul_of_nonneg_left hNpow hγinv)
        _ = shellConstant d * (1 + 1 / ((d : ℝ) - α)) *
              (ε ^ ((d : ℝ) - α) * (1 / ε) ^ ((d : ℝ) - α)) := by ring
        _ = shellConstant d * (1 + 1 / ((d : ℝ) - α)) := by rw [hepow, mul_one]
  · -- regime `α = d`: the sum is harmonic growth `≤ C(1 + |ln ε|)`
    have hnlt : ¬ α < (d : ℝ) := not_lt.mpr heq.ge
    refine ⟨shellConstant d, hS, ?_⟩
    intro ε hε
    rw [if_neg hnlt, if_pos heq, scaled_sum_eq hε.1]
    have hγ0 : (d : ℝ) - α = 0 := by rw [heq, sub_self]
    rw [hγ0, Real.rpow_zero, one_mul]
    have hsum := unitBallIndices_rpow_sum_le hd hα hε.1
    have hβ1 : (d : ℝ) - 1 - α = -1 := by linarith
    rw [hβ1] at hsum
    have hlogsum := sum_inv_Icc_le_one_add_log ⌊1 / ε⌋₊
    have hlogε : Real.log ε < 0 := Real.log_neg hε.1 hε.2
    have hN1 : (1 : ℝ) ≤ ((⌊1 / ε⌋₊ : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ 1 / ε := one_le_one_div hε.1 hε.2.le
      exact_mod_cast (Nat.one_le_floor_iff _).mpr h1
    have hNle : ((⌊1 / ε⌋₊ : ℕ) : ℝ) ≤ 1 / ε := Nat.floor_le (div_nonneg zero_le_one hε.1.le)
    have hlog1 : Real.log (1 / ε) = |Real.log ε| := by
      rw [one_div, Real.log_inv, abs_of_neg hlogε]
    have hlogle : Real.log ((⌊1 / ε⌋₊ : ℕ) : ℝ) ≤ |Real.log ε| := by
      rw [← hlog1]
      exact Real.log_le_log (by linarith) hNle
    calc ∑ z ∈ unitBallIndices d ε, (radius (physical 1 z)) ^ (-α)
        ≤ shellConstant d * ∑ n ∈ Finset.Icc 1 ⌊1 / ε⌋₊, (n : ℝ) ^ (-1 : ℝ) := hsum
      _ ≤ shellConstant d * (1 + |Real.log ε|) :=
          mul_le_mul_of_nonneg_left (by linarith [hlogsum, hlogle]) hS.le
  · -- regime `α > d`: the normalized partial sums are bounded by the convergent full series
    have hnlt : ¬ α < (d : ℝ) := not_lt.mpr hgt.le
    have hneq : ¬ α = (d : ℝ) := ne_of_gt hgt
    have hβ : (d : ℝ) - 1 - α < -1 := by linarith
    set M : ℝ := ∑' n : ℕ, (n : ℝ) ^ ((d : ℝ) - 1 - α) with hMdef
    have hM0 : 0 ≤ M := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hCpos : 0 < shellConstant d * M + 1 := by
      have := mul_nonneg hS.le hM0
      linarith
    refine ⟨shellConstant d * M + 1, hCpos, ?_⟩
    intro ε hε
    rw [if_neg hnlt, if_neg hneq, scaled_sum_eq hε.1]
    have hsum := unitBallIndices_rpow_sum_le hd hα hε.1
    have hT := sum_rpow_Icc_le_tsum hβ ⌊1 / ε⌋₊
    rw [← hMdef] at hT
    have hS': ∑ z ∈ unitBallIndices d ε, (radius (physical 1 z)) ^ (-α) ≤
        shellConstant d * M + 1 := by
      have h1 := mul_le_mul_of_nonneg_left hT hS.le
      linarith
    calc ε ^ ((d : ℝ) - α) * ∑ z ∈ unitBallIndices d ε, (radius (physical 1 z)) ^ (-α)
        ≤ ε ^ ((d : ℝ) - α) * (shellConstant d * M + 1) :=
          mul_le_mul_of_nonneg_left hS' (Real.rpow_nonneg hε.1.le _)
      _ = (shellConstant d * M + 1) * ε ^ ((d : ℝ) - α) := mul_comm _ _

/-- `(1/ε)^{-m} = ε^m`. -/
lemma one_div_rpow_neg_eq {ε m : ℝ} (hε : 0 < ε) : (1 / ε) ^ (-m) = ε ^ m := by
  rw [one_div, Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]

/-- The exponent identity `ε^d · (ε^{-α} · ε^{α-d}) = 1`. -/
lemma pow_mul_rpow_identity {ε α : ℝ} (d : ℕ) (hε : 0 < ε) :
    ε ^ d * (ε ^ (-α) * ε ^ (α - (d : ℝ))) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hε, ← Real.rpow_add hε]
  have h0 : (d : ℝ) + (-α + (α - (d : ℝ))) = 0 := by ring
  rw [h0, Real.rpow_zero]

/-- Finite exterior bound: every finite sum of the indicator summand is at most
`ε^{-α} · shellConstant d · (1 + 1/m) · 4^m · (1/ε)^{-m}`. -/
lemma exterior_finset_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hαd : (d : ℝ) < α) {ε : ℝ}
    (hε : 0 < ε) (hR : 1 ≤ 1 / ε) (u : Finset (Site d)) :
    ∑ z ∈ u, (if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-α) else 0)
      ≤ ε ^ (-α) * (shellConstant d * ((1 + 1 / (α - (d : ℝ))) *
          ((4 : ℝ) ^ (α - (d : ℝ)) * (1 / ε) ^ (-(α - (d : ℝ)))))) := by
  classical
  have hm : 0 < α - (d : ℝ) := by linarith
  have hα0 : 0 ≤ α := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  set m : ℝ := α - (d : ℝ) with hm_def
  rw [← Finset.sum_filter (fun z => 1 ≤ radius (physical ε z))
      (fun z => (radius (physical ε z)) ^ (-α))]
  have hterm : ∑ z ∈ u.filter (fun z => 1 ≤ radius (physical ε z)), (radius (physical ε z)) ^ (-α)
      = ε ^ (-α) * ∑ z ∈ u.filter (fun z => 1 ≤ radius (physical ε z)),
          (radius (physical 1 z)) ^ (-α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [radius_physical_eq_mul hε.le z, Real.mul_rpow hε.le (radius_nonneg (physical 1 z))]
  have hnz : ∀ z ∈ u.filter (fun z => 1 ≤ radius (physical ε z)), z ≠ 0 := by
    intro z hz hz0
    have h1 := (Finset.mem_filter.mp hz).2
    rw [hz0] at h1
    norm_num [radius, physical] at h1
  have hfiber := shell_rpow_sum_le_fiber hd hα0 (u.filter (fun z => 1 ≤ radius (physical ε z))) hnz
  have hexp : (d : ℝ) - 1 - α = -m - 1 := by rw [hm_def]; ring
  rw [hexp] at hfiber
  have hfloor : ∀ n ∈ (u.filter (fun z => 1 ≤ radius (physical ε z))).image
      (fun w => Nat.floor (radius (physical 1 w))), Nat.floor (1 / ε) ≤ n := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    have h1 : 1 ≤ radius (physical ε z) := (Finset.mem_filter.mp hz).2
    rw [radius_physical_eq_mul hε.le z] at h1
    have hr : 1 / ε ≤ radius (physical 1 z) := by
      rw [div_le_iff₀ hε]
      linarith
    exact Nat.floor_le_floor hr
  have htail := tail_finset_bound (m := m) (R := 1 / ε) hm hR
    ((u.filter (fun z => 1 ≤ radius (physical ε z))).image
      (fun w => Nat.floor (radius (physical 1 w)))) hfloor
  rw [hterm]
  have hpos : 0 ≤ ε ^ (-α) := Real.rpow_nonneg hε.le _
  calc ε ^ (-α) * ∑ z ∈ u.filter (fun z => 1 ≤ radius (physical ε z)),
      (radius (physical 1 z)) ^ (-α)
      ≤ ε ^ (-α) * (shellConstant d * ∑ n ∈ (u.filter (fun z => 1 ≤ radius (physical ε z))).image
          (fun w => Nat.floor (radius (physical 1 w))), (n : ℝ) ^ (-m - 1)) :=
        mul_le_mul_of_nonneg_left hfiber hpos
    _ ≤ ε ^ (-α) * (shellConstant d * ((1 + 1 / m) * ((4 : ℝ) ^ m * (1 / ε) ^ (-m)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail (shellConstant_pos hd).le) hpos

/-- **Exterior bound for scaled radial sums.** For `d ≥ 1` and `α > d`, and for each `ε ∈ (0,1)`,
the indicator sum over the points outside the unit ball is summable, and `ε^d` times its total is
at most a constant `C(α, d)`. -/
theorem exterior_rpow_sum_bound (d : ℕ) (hd : 1 ≤ d) :
    ∀ α : ℝ, (d : ℝ) < α → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun z : Site d =>
          if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-α) else 0) ∧
      ε ^ d * (∑' z : Site d,
          if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-α) else 0) ≤ C := by
  intro α hαd
  have hm : 0 < α - (d : ℝ) := by linarith
  have hS := shellConstant_pos hd
  have hK : 0 < (1 + 1 / (α - (d : ℝ))) * (4 : ℝ) ^ (α - (d : ℝ)) := by
    have h1 : 0 < 1 + 1 / (α - (d : ℝ)) := by
      have := one_div_pos.mpr hm
      linarith
    exact mul_pos h1 (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨shellConstant d * ((1 + 1 / (α - (d : ℝ))) * (4 : ℝ) ^ (α - (d : ℝ))), mul_pos hS hK, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := hε.1
  have hR : 1 ≤ 1 / ε := one_le_one_div hε0 hε.2.le
  have hfnn : ∀ z : Site d,
      0 ≤ (if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-α) else 0) := by
    intro z
    split_ifs
    · exact Real.rpow_nonneg (radius_nonneg _) _
    · exact le_rfl
  have hbound : ∀ u : Finset (Site d),
      ∑ z ∈ u, (if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-α) else 0)
        ≤ ε ^ (-α) * (shellConstant d * ((1 + 1 / (α - (d : ℝ))) *
            ((4 : ℝ) ^ (α - (d : ℝ)) * (1 / ε) ^ (-(α - (d : ℝ)))))) :=
    fun u => exterior_finset_le hd hαd hε0 hR u
  have hsum : Summable (fun z : Site d =>
      if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-α) else 0) :=
    summable_of_sum_le hfnn hbound
  refine ⟨hsum, ?_⟩
  have htsum := hsum.tsum_le_of_sum_le hbound
  have hpd : (0 : ℝ) ≤ ε ^ d := pow_nonneg hε0.le d
  have hB : ε ^ (-α) * (shellConstant d * ((1 + 1 / (α - (d : ℝ))) *
      ((4 : ℝ) ^ (α - (d : ℝ)) * (1 / ε) ^ (-(α - (d : ℝ)))))) =
      ε ^ (-α) * (shellConstant d * ((1 + 1 / (α - (d : ℝ))) *
        ((4 : ℝ) ^ (α - (d : ℝ)) * ε ^ (α - (d : ℝ))))) := by
    rw [one_div_rpow_neg_eq hε0]
  calc ε ^ d * (∑' z : Site d,
          if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-α) else 0)
      ≤ ε ^ d * (ε ^ (-α) * (shellConstant d * ((1 + 1 / (α - (d : ℝ))) *
          ((4 : ℝ) ^ (α - (d : ℝ)) * ε ^ (α - (d : ℝ)))))) := by
        rw [← hB]
        exact mul_le_mul_of_nonneg_left htsum hpd
    _ = shellConstant d * ((1 + 1 / (α - (d : ℝ))) * (4 : ℝ) ^ (α - (d : ℝ))) *
          (ε ^ d * (ε ^ (-α) * ε ^ (α - (d : ℝ)))) := by ring
    _ = shellConstant d * ((1 + 1 / (α - (d : ℝ))) * (4 : ℝ) ^ (α - (d : ℝ))) := by
        rw [pow_mul_rpow_identity d hε0, mul_one]

end LatticeProb.Euclidean.Estimates
