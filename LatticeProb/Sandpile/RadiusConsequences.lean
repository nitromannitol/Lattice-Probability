module

public import LatticeProb.External.FeyDenBoerRedigCubicalCluster
public import LatticeProb.External.FeyLevinePeresRadius

@[expose] public section

/-!
# Radius consequences for the parallel toppling odometer

The parallel toppling odometer `podo` of the background `2d - 2` plus `N` extra chips at the
origin is controlled by two cited propositions, each taken as an explicit hypothesis:

* `LatticeProb.External.FeyDenBoerRedigCubicalCluster` (Theorem 4.1 of Fey-den Boer and Redig),
  whose cubical lower-radius conclusion gives a legal stabilizing procedure with an integer cube
  as terminal positive support;
* `LatticeProb.External.FeyLevinePeresRadius` (Theorem 1.1 of Fey, Levine and Peres), whose
  eventual outer-radius bound yields a dimensional constant `A` and threshold `N0`.

The parallel odometer is itself a legal toppling procedure, so the terminal identity below
applies to it. The file proves no further property of the cited propositions.
-/

namespace LatticeProb.Sandpile

open LatticeProb MeasureTheory

/-- The parallel toppling odometer `podo s0` is a legal toppling procedure for `s0`. -/
theorem podo_isLegal {d : ℕ} (s0 : Site d → ℤ) : IsLegalToppling s0 (podo s0) := by
  refine ⟨funext fun y => rfl, fun k x => ?_⟩
  rw [podo_succ]
  by_cases h : 2 * (d : ℤ) ≤ pconf s0 k x
  · right
    exact ⟨by simp [h], h⟩
  · left
    simp [h]

/-- A monotone integer-valued sequence that is bounded above is eventually constant. -/
theorem eventually_const_of_monotone_le (f : ℕ → ℤ) (hf : Monotone f) (M : ℤ)
    (hM : ∀ k, f k ≤ M) : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → f k = f K := by
  classical
  have hex : ∃ n : ℕ, ∃ K : ℕ, (M - f K).toNat = n := ⟨_, 0, rfl⟩
  obtain ⟨K, hK⟩ := Nat.find_spec hex
  refine ⟨K, fun k hk => ?_⟩
  have hmin : ¬ (M - f k).toNat < Nat.find hex := fun hlt => Nat.find_min hex hlt ⟨k, rfl⟩
  have h1 : f K ≤ f k := hf hk
  have h2 := hM k
  have h3 := hM K
  omega

/-- **Terminal cube of the parallel process.** Assume the cubical lower-radius input
`LatticeProb.External.FeyDenBoerRedigCubicalCluster`. For the background `2d - 2` with `N ≥ 2`
extra chips at the origin, the parallel odometer `podo s0` is globally stabilizable. At every
time `T` after which it no longer changes, its positive-odometer support is the integer cube
`{x : max_i |x_i| ≤ r}` for a natural radius `r` with `((N + 2d - 2)^(1/d) - 3) / 2 ≤ r`. -/
theorem fdbr_parallel_terminal
    (hFdBR : LatticeProb.External.FeyDenBoerRedigCubicalCluster)
    (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (hN : 2 ≤ N) (s0 : Site d → ℤ)
    (hs0 : ∀ x : Site d, s0 x = (2 * (d : ℤ) - 2) + (N : ℤ) * dirac (0 : Site d) x) :
    Stabilizable s0 ∧ ∃ r : ℕ,
      (∀ T : ℕ, (∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T) →
        {x : Site d | 0 < podo s0 T x} = {x : Site d | ∀ i : Fin d, |x i| ≤ (r : ℤ)}) ∧
      ((((N : ℝ) + 2 * (d : ℝ) - 2) ^ (1 / (d : ℝ)) - 3) / 2 ≤ (r : ℝ)) := by
  classical
  obtain ⟨u, T0, hu, _, hstable, r, hsupp, hbound⟩ := hFdBR d hd N hN s0 hs0
  have hwnn : ∀ y, 0 ≤ u T0 y := fun y => hu.nonneg T0 y
  have hle : ∀ k y, podo s0 k y ≤ u T0 y := fun k y =>
    le_of_isLegalToppling (podo_isLegal s0) hwnn hstable k y
  have hmono : ∀ y, Monotone (fun k => podo s0 k y) := fun y =>
    monotone_nat_of_le_succ (fun k => podo_mono_step s0 k y)
  have hev : ∀ y, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → podo s0 k y = podo s0 K y := fun y =>
    eventually_const_of_monotone_le (fun k => podo s0 k y) (hmono y) (u T0 y) (fun k => hle k y)
  choose Ky hKy using hev
  set B : Finset (Site d) := Finset.Icc (fun _ => -(r : ℤ)) (fun _ => (r : ℤ)) with hB
  have hBcube : ∀ y : Site d, (∀ i : Fin d, |y i| ≤ (r : ℤ)) → y ∈ B := by
    intro y hy
    rw [hB, Finset.mem_Icc]
    exact ⟨fun i => (abs_le.mp (hy i)).1, fun i => (abs_le.mp (hy i)).2⟩
  have hout : ∀ y : Site d, y ∉ B → ∀ k, podo s0 k y = 0 := by
    intro y hyB k
    have hnc : ¬ (∀ i : Fin d, |y i| ≤ (r : ℤ)) := fun h => hyB (hBcube y h)
    have hnpos : ¬ (0 < u T0 y) := by
      intro hpos
      apply hnc
      have hm : y ∈ {x : Site d | 0 < u T0 x} := hpos
      rw [hsupp] at hm
      exact hm
    have h0 : u T0 y ≤ 0 := not_lt.mp hnpos
    exact le_antisymm ((hle k y).trans h0) ((podo_isLegal s0).nonneg k y)
  have hglobal : ∀ t : ℕ, B.sup Ky ≤ t → podo s0 t = podo s0 (B.sup Ky) := by
    intro t ht
    funext y
    by_cases hyB : y ∈ B
    · have h1 := hKy y t ((Finset.le_sup hyB).trans ht)
      have h2 := hKy y (B.sup Ky) (Finset.le_sup hyB)
      rw [h1, h2]
    · rw [hout y hyB t, hout y hyB (B.sup Ky)]
  set K := B.sup Ky with hK
  have hstab : ∀ y : Site d, pconf s0 K y < 2 * (d : ℤ) := by
    intro y
    by_contra hc
    have hc' : 2 * (d : ℤ) ≤ pconf s0 K y := not_lt.mp hc
    have h1 : podo s0 (K + 1) y = podo s0 K y := congrFun (hglobal (K + 1) (by omega)) y
    rw [podo_succ, if_pos hc'] at h1
    omega
  have hpk0 : ∀ y, 0 ≤ podo s0 K y := fun y => (podo_isLegal s0).nonneg K y
  have hwp : ∀ y, u T0 y ≤ podo s0 K y := fun y =>
    le_of_isLegalToppling hu hpk0 (fun x => hstab x) T0 y
  have hpk : podo s0 K = u T0 := funext fun y => le_antisymm (hle K y) (hwp y)
  have hst : Stabilizable s0 := by
    unfold Stabilizable
    exact ⟨K, hglobal⟩
  refine ⟨hst, r, fun T hT => ?_, hbound⟩
  have hTK : podo s0 T = podo s0 K := by
    have hM1 := hT (max T K) (le_max_left _ _)
    have hM2 := hglobal (max T K) (le_max_right _ _)
    exact hM1.symm.trans hM2
  rw [hTK, hpk]
  exact hsupp

/-- The Lebesgue volume of the Euclidean unit ball in `ℝ^d` is strictly positive. -/
theorem euclidean_unit_ball_volume_toReal_pos (d : ℕ) :
    0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

/-- **Uniform outer radius from the Fey-Levine-Peres input.** Assume
`LatticeProb.External.FeyLevinePeresRadius`. For each dimension `d ≥ 2` there are a constant
`A > 0` and a threshold `N0 ≥ 2`, both depending only on `d`, such that for every `N ≥ N0`
every site that topples at some time of the parallel process started from `(2d - 2) + N δ₀`
has every coordinate bounded by `A N^(1/d)` in absolute value. -/
theorem flp_specialization (hFLP : LatticeProb.External.FeyLevinePeresRadius)
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ x : Site d,
        (∃ t : ℕ, 0 < podo (fun y : Site d =>
          (2 * (d : ℤ) - 2) + (N : ℤ) * dirac (0 : Site d) y) t x) →
          ∀ i : Fin d, |(x i : ℝ)| ≤ A * (N : ℝ) ^ (1 / (d : ℝ)) := by
  obtain ⟨n0, hn0⟩ := hFLP d (2 * (d : ℤ) - 2) (by omega) le_rfl 1 one_pos
  have hωpos := euclidean_unit_ball_volume_toReal_pos d
  set ω := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hω
  refine ⟨((d : ℝ) + 1) / ω ^ (1 / (d : ℝ)), ?_, max n0 2, le_max_right _ _, ?_⟩
  · exact div_pos (by positivity) (Real.rpow_pos_of_pos hωpos _)
  · intro N hN x hx i
    have hsub := hn0 N (le_trans (le_max_left _ _) hN) hx i
    have h1 : (2 * (d : ℝ) - 1 - ((2 * (d : ℤ) - 2 : ℤ) : ℝ)) = 1 := by push_cast; ring
    have key : (((d : ℝ) + 1) / (2 * (d : ℝ) - 1 - ((2 * (d : ℤ) - 2 : ℤ) : ℝ))) *
        (((N : ℝ) / ω) ^ (1 / (d : ℝ))) =
          ((d : ℝ) + 1) / ω ^ (1 / (d : ℝ)) * (N : ℝ) ^ (1 / (d : ℝ)) := by
      rw [Real.div_rpow (Nat.cast_nonneg N) hωpos.le, h1, div_one]
      ring
    exact hsub.trans_eq key

end LatticeProb.Sandpile
