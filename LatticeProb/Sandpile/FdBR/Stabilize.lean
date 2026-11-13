import LatticeProb.Sandpile.LeastAction

/-!
# Stabilization of the parallel odometer for the cubical FdBR background

For the background `2d - 2` with `N` extra chips at the origin, the parallel
toppling odometer `podo s0` stabilizes. The proof uses the supersolution
`fdbrStabilizer K`, a triangular function of the supremum norm `‖x‖_∞`:

* its Laplacian satisfies `s0 + Δ (fdbrStabilizer K) < 2d` at every site once
  `N ≤ 2dK + 1`;
* by the least action principle every legal toppling procedure for `s0` lies
  below `fdbrStabilizer K`, so the odometer vanishes outside a finite box;
* a bounded monotone integer sequence is eventually constant, so `podo s0` is
  constant from some time on, and the constant odometer is stable.
-/

namespace LatticeProb.Sandpile

open LatticeProb

/-- The supremum norm `‖x‖_∞` of a site, as a natural number. -/
def supNormNat {d : ℕ} (x : Site d) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- The triangular supersolution `T_{K - ‖x‖_∞}`, where `T_n = n (n + 1) / 2`. -/
def fdbrStabilizer {d : ℕ} (K : ℕ) (x : Site d) : ℤ :=
  (((K - supNormNat x) * (K - supNormNat x + 1) / 2 : ℕ) : ℤ)

/-- The profile `n ↦ T_{K - n}` of `fdbrStabilizer`, as a function of the norm value. -/
private def fdbrTri (K n : ℕ) : ℤ := (((K - n) * (K - n + 1) / 2 : ℕ) : ℤ)

private theorem fdbrStabilizer_eq_fdbrTri (K : ℕ) {d : ℕ} (x : Site d) :
    fdbrStabilizer K x = fdbrTri K (supNormNat x) := rfl

theorem fdbrStabilizer_nonneg {d : ℕ} (K : ℕ) (x : Site d) : 0 ≤ fdbrStabilizer K x :=
  Nat.cast_nonneg _

private theorem natAbs_le_supNormNat {d : ℕ} (x : Site d) (i : Fin d) :
    (x i).natAbs ≤ supNormNat x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

private theorem add_unit_apply_self {d : ℕ} (x : Site d) (i : Fin d) :
    (x + unit i) i = x i + 1 := by
  simp [unit]

private theorem sub_unit_apply_self {d : ℕ} (x : Site d) (i : Fin d) :
    (x - unit i) i = x i - 1 := by
  simp [unit]

private theorem add_unit_apply_of_ne {d : ℕ} (x : Site d) {i j : Fin d} (h : j ≠ i) :
    (x + unit i) j = x j := by
  simp [unit, h]

private theorem sub_unit_apply_of_ne {d : ℕ} (x : Site d) {i j : Fin d} (h : j ≠ i) :
    (x - unit i) j = x j := by
  simp [unit, h]

private theorem two_mul_fdbrTri (K n : ℕ) :
    2 * fdbrTri K n = ((K - n : ℕ) : ℤ) * (((K - n : ℕ) : ℤ) + 1) := by
  have h : 2 * ((K - n) * (K - n + 1) / 2) = (K - n) * (K - n + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self _)
  unfold fdbrTri
  exact_mod_cast h

private theorem fdbrTri_anti (K : ℕ) {m n : ℕ} (h : m ≤ n) : fdbrTri K n ≤ fdbrTri K m := by
  unfold fdbrTri
  apply Nat.cast_le.mpr
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul <;> omega

private theorem fdbrTri_eq_zero {K n : ℕ} (h : K ≤ n) : fdbrTri K n = 0 := by
  unfold fdbrTri
  have : K - n = 0 := by omega
  simp [this]

private theorem fdbrTri_one_add (K : ℕ) : fdbrTri K 1 + K = fdbrTri K 0 := by
  cases K with
  | zero => simp [fdbrTri]
  | succ n =>
    have h0 := two_mul_fdbrTri (n + 1) 0
    have h1 := two_mul_fdbrTri (n + 1) 1
    simp only [Nat.sub_zero, Nat.add_sub_cancel] at h0 h1
    push_cast at h0 h1 ⊢
    linarith

private theorem fdbrTri_sec_diff (K j : ℕ) :
    fdbrTri K (j + 2) + fdbrTri K j ≤ 2 * fdbrTri K (j + 1) + 1 := by
  have h2 := two_mul_fdbrTri K (j + 2)
  have h1 := two_mul_fdbrTri K (j + 1)
  have h0 := two_mul_fdbrTri K j
  rcases Nat.lt_or_ge K (j + 2) with hK | hK
  · rcases Nat.lt_or_ge K (j + 1) with hK' | hK'
    · have e2 : K - (j + 2) = 0 := by omega
      have e1 : K - (j + 1) = 0 := by omega
      have e0 : K - j = 0 := by omega
      rw [e2] at h2
      rw [e1] at h1
      rw [e0] at h0
      norm_num at h2 h1 h0
      linarith
    · have e2 : K - (j + 2) = 0 := by omega
      have e1 : K - (j + 1) = 0 := by omega
      have e0 : K - j = 1 := by omega
      rw [e2] at h2
      rw [e1] at h1
      rw [e0] at h0
      norm_num at h2 h1 h0
      linarith
  · obtain ⟨a, ha⟩ : ∃ a, K - (j + 2) = a := ⟨_, rfl⟩
    have e1 : K - (j + 1) = a + 1 := by omega
    have e0 : K - j = a + 2 := by omega
    rw [ha] at h2
    rw [e1] at h1
    rw [e0] at h0
    push_cast at h2 h1 h0
    linarith

private theorem fdbrTri_neighbour_sum (K : ℕ) (a : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (ha : a.natAbs = k) :
    fdbrTri K (a + 1).natAbs + fdbrTri K (a - 1).natAbs ≤ 2 * fdbrTri K k + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hcases : a = (j : ℤ) + 1 ∨ a = -((j : ℤ) + 1) := by omega
  rcases hcases with h | h
  · have h1 : (a + 1).natAbs = j + 2 := by omega
    have h2 : (a - 1).natAbs = j := by omega
    rw [h1, h2]
    exact fdbrTri_sec_diff K j
  · have h1 : (a + 1).natAbs = j := by omega
    have h2 : (a - 1).natAbs = j + 2 := by omega
    rw [h1, h2]
    linarith [fdbrTri_sec_diff K j]

private theorem fdbrStabilizer_le_fdbrTri {d : ℕ} {K a : ℕ} {x : Site d}
    (h : a ≤ supNormNat x) : fdbrStabilizer K x ≤ fdbrTri K a :=
  fdbrTri_anti K h

private theorem fdbrStabilizer_eq_zero {d : ℕ} {K : ℕ} {x : Site d} (h : K ≤ supNormNat x) :
    fdbrStabilizer K x = 0 :=
  fdbrTri_eq_zero h

/-- The Laplacian of the supersolution is at most `1` away from the origin. -/
private theorem lap_fdbrStabilizer_le_one {d : ℕ} (K : ℕ) {x : Site d} (hx : x ≠ 0) :
    lap (fdbrStabilizer K) x ≤ 1 := by
  classical
  have hk : 0 < supNormNat x := by
    rcases Nat.eq_zero_or_pos (supNormNat x) with h | h
    · exfalso
      apply hx
      funext i
      have h1 : (x i).natAbs = 0 := by
        have := natAbs_le_supNormNat x i
        omega
      simpa using h1
    · exact h
  obtain ⟨j0, hj0⟩ : ∃ j, supNormNat x ≤ (x j).natAbs := by
    by_contra hne
    push Not at hne
    have hlt : supNormNat x < supNormNat x :=
      (Finset.sup_lt_iff (show (⊥ : ℕ) < supNormNat x from hk)).mpr fun j _ => hne j
    exact lt_irrefl _ hlt
  have hj0' : (x j0).natAbs = supNormNat x := le_antisymm (natAbs_le_supNormNat x j0) hj0
  have hxi : ∀ i : Fin d, (∀ j, j ≠ i → (x j).natAbs < supNormNat x) →
      (x i).natAbs = supNormNat x := by
    intro i hi
    by_cases h : j0 = i
    · rw [← h]
      exact hj0'
    · exact absurd hj0' (ne_of_lt (hi j0 h))
  have hdir : ∀ i : Fin d,
      -2 * fdbrStabilizer K x + fdbrStabilizer K (x + unit i) + fdbrStabilizer K (x - unit i)
        ≤ if ∀ j, j ≠ i → (x j).natAbs < supNormNat x then 1 else 0 := by
    intro i
    by_cases hi : ∀ j, j ≠ i → (x j).natAbs < supNormNat x
    · rw [ite_eq_left hi]
      have hp : fdbrStabilizer K (x + unit i) ≤ fdbrTri K (x i + 1).natAbs := by
        apply fdbrStabilizer_le_fdbrTri
        have h := natAbs_le_supNormNat (x + unit i) i
        rwa [add_unit_apply_self] at h
      have hm : fdbrStabilizer K (x - unit i) ≤ fdbrTri K (x i - 1).natAbs := by
        apply fdbrStabilizer_le_fdbrTri
        have h := natAbs_le_supNormNat (x - unit i) i
        rwa [sub_unit_apply_self] at h
      have key := fdbrTri_neighbour_sum K (x i) (supNormNat x) hk (hxi i hi)
      have hx' : fdbrStabilizer K x = fdbrTri K (supNormNat x) := rfl
      linarith
    · rw [ite_eq_right hi]
      push Not at hi
      obtain ⟨j, hji, hkj⟩ := hi
      have hp : fdbrStabilizer K (x + unit i) ≤ fdbrTri K (supNormNat x) := by
        apply fdbrStabilizer_le_fdbrTri
        have h := natAbs_le_supNormNat (x + unit i) j
        rw [add_unit_apply_of_ne x hji] at h
        exact le_trans hkj h
      have hm : fdbrStabilizer K (x - unit i) ≤ fdbrTri K (supNormNat x) := by
        apply fdbrStabilizer_le_fdbrTri
        have h := natAbs_le_supNormNat (x - unit i) j
        rw [sub_unit_apply_of_ne x hji] at h
        exact le_trans hkj h
      have hx' : fdbrStabilizer K x = fdbrTri K (supNormNat x) := rfl
      linarith
  rw [lap_eq_sum_second_diff]
  calc ∑ i : Fin d, (-2 * fdbrStabilizer K x + fdbrStabilizer K (x + unit i)
        + fdbrStabilizer K (x - unit i))
      ≤ ∑ i : Fin d, (if ∀ j, j ≠ i → (x j).natAbs < supNormNat x then (1 : ℤ) else 0) :=
        Finset.sum_le_sum fun i _ => hdir i
    _ ≤ 1 := by
      rw [Finset.sum_boole]
      have hcard : (Finset.univ.filter fun i : Fin d =>
          ∀ j, j ≠ i → (x j).natAbs < supNormNat x).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [Finset.mem_filter] at ha hb
        by_contra hab
        have h2 := hb.2 a hab
        have h3 := hxi a ha.2
        omega
      exact_mod_cast hcard

/-- The Laplacian of the supersolution at the origin is at most `-2dK`. -/
private theorem lap_fdbrStabilizer_zero {d : ℕ} (K : ℕ) :
    lap (fdbrStabilizer K) (0 : Site d) ≤ -2 * (d : ℤ) * K := by
  have hsup : supNormNat (0 : Site d) = 0 :=
    le_antisymm (Finset.sup_le fun i _ => by simp) (Nat.zero_le _)
  have h0 : fdbrStabilizer K (0 : Site d) = fdbrTri K 0 := by
    rw [fdbrStabilizer_eq_fdbrTri, hsup]
  have hbd : ∀ i : Fin d,
      -2 * fdbrStabilizer K (0 : Site d) + fdbrStabilizer K ((0 : Site d) + unit i)
        + fdbrStabilizer K ((0 : Site d) - unit i) ≤ -2 * fdbrTri K 0 + 2 * fdbrTri K 1 := by
    intro i
    have hp : fdbrStabilizer K ((0 : Site d) + unit i) ≤ fdbrTri K 1 := by
      apply fdbrStabilizer_le_fdbrTri
      have h := natAbs_le_supNormNat ((0 : Site d) + unit i) i
      rw [add_unit_apply_self] at h
      simpa using h
    have hm : fdbrStabilizer K ((0 : Site d) - unit i) ≤ fdbrTri K 1 := by
      apply fdbrStabilizer_le_fdbrTri
      have h := natAbs_le_supNormNat ((0 : Site d) - unit i) i
      rw [sub_unit_apply_self] at h
      simpa using h
    rw [h0]
    linarith
  have hsum := fdbrTri_one_add K
  rw [lap_eq_sum_second_diff]
  calc ∑ i : Fin d, (-2 * fdbrStabilizer K (0 : Site d) + fdbrStabilizer K ((0 : Site d) + unit i)
        + fdbrStabilizer K ((0 : Site d) - unit i))
      ≤ ∑ _i : Fin d, (-2 * fdbrTri K 0 + 2 * fdbrTri K 1) :=
        Finset.sum_le_sum fun i _ => hbd i
    _ = (d : ℤ) * (-2 * fdbrTri K 0 + 2 * fdbrTri K 1) := by simp
    _ = (d : ℤ) * (-2 * (K : ℤ)) := by
        rw [show -2 * fdbrTri K 0 + 2 * fdbrTri K 1 = -2 * (K : ℤ) by linarith]
    _ = -2 * (d : ℤ) * K := by ring

/-- The supersolution `fdbrStabilizer K` is stable at every site when `N ≤ 2dK + 1`. -/
theorem fdbrStabilizer_stable {d : ℕ} (_hd : 1 ≤ d) {N K : ℕ} (hK : N ≤ 2 * d * K + 1)
    (x : Site d) :
    (2 * (d : ℤ) - 2) + (N : ℤ) * dirac 0 x + lap (fdbrStabilizer K) x < 2 * (d : ℤ) := by
  by_cases hx : x = 0
  · subst hx
    have h0 := lap_fdbrStabilizer_zero (d := d) K
    have hK' : (N : ℤ) ≤ 2 * (d : ℤ) * K + 1 := by exact_mod_cast hK
    rw [dirac_self]
    linarith
  · rw [dirac_of_ne hx]
    have h := lap_fdbrStabilizer_le_one K hx
    linarith

/-- The parallel toppling odometer is a legal toppling procedure. -/
private theorem isLegalToppling_podo {d : ℕ} (s0 : Site d → ℤ) :
    IsLegalToppling s0 (podo s0) := by
  refine ⟨funext fun y => rfl, fun k x => ?_⟩
  rw [podo_succ]
  by_cases h : 2 * (d : ℤ) ≤ pconf s0 k x
  · right
    exact ⟨by simp [h], h⟩
  · left
    simp [h]

/-- A monotone integer sequence bounded above is eventually constant. -/
private theorem eventually_const_of_monotone_bdd (f : ℕ → ℤ) (hf : Monotone f) (M : ℤ)
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

/-- **Stabilization of the parallel odometer.** For the background `2d - 2` with `N` extra chips
at the origin, the odometer `podo s0` is constant from some time `T` on, the configuration
`pconf s0 T` is stable, and `podo s0 T` vanishes outside the box of supremum radius `N`. -/
theorem fdbr_podo_stabilizes {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (s0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x = (2 * (d : ℤ) - 2) + (N : ℤ) * dirac 0 x) :
    ∃ T : ℕ, (∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T) ∧
      (∀ x : Site d, s0 x + lap (podo s0 T) x < 2 * (d : ℤ)) ∧
      ∃ K : ℕ, ∀ x : Site d, K ≤ supNormNat x → podo s0 T x = 0 := by
  classical
  have hNd : N ≤ 2 * d * N + 1 := by nlinarith
  have hw : ∀ x, s0 x + lap (fdbrStabilizer N) x < 2 * (d : ℤ) := fun x => by
    rw [hs0 x]
    exact fdbrStabilizer_stable hd hNd x
  have hle : ∀ t x, podo s0 t x ≤ fdbrStabilizer N x := fun t x =>
    le_of_isLegalToppling (isLegalToppling_podo s0) (fun y => fdbrStabilizer_nonneg N y) hw t x
  have hmono : ∀ y, Monotone (fun k => podo s0 k y) := fun y =>
    monotone_nat_of_le_succ (fun k => podo_mono_step s0 k y)
  have hev : ∀ y, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → podo s0 k y = podo s0 K y := fun y =>
    eventually_const_of_monotone_bdd (fun k => podo s0 k y) (hmono y) (fdbrStabilizer N y)
      (fun k => hle k y)
  choose Ky hKy using hev
  set B : Finset (Site d) := Finset.Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ)) with hB
  have hBcube : ∀ y : Site d, (∀ i : Fin d, |y i| ≤ (N : ℤ)) → y ∈ B := by
    intro y hy
    rw [hB, Finset.mem_Icc]
    exact ⟨fun i => (abs_le.mp (hy i)).1, fun i => (abs_le.mp (hy i)).2⟩
  have hout : ∀ y : Site d, y ∉ B → ∀ k, podo s0 k y = 0 := by
    intro y hyB k
    have hnc : ¬ (∀ i : Fin d, |y i| ≤ (N : ℤ)) := fun h => hyB (hBcube y h)
    push Not at hnc
    obtain ⟨i, hi⟩ := hnc
    have hNy : N ≤ supNormNat y := by
      have h1 : ((y i).natAbs : ℤ) = |y i| := (Int.abs_eq_natAbs (y i)).symm
      have h2 : N < (y i).natAbs := by omega
      exact le_trans (le_of_lt h2) (natAbs_le_supNormNat y i)
    have h0 : fdbrStabilizer N y = 0 := fdbrStabilizer_eq_zero hNy
    exact le_antisymm (by have := hle k y; rw [h0] at this; exact this)
      ((isLegalToppling_podo s0).nonneg k y)
  have hglobal : ∀ t : ℕ, B.sup Ky ≤ t → podo s0 t = podo s0 (B.sup Ky) := by
    intro t ht
    funext y
    by_cases hyB : y ∈ B
    · have h1 := hKy y t ((Finset.le_sup hyB).trans ht)
      have h2 := hKy y (B.sup Ky) (Finset.le_sup hyB)
      rw [h1, h2]
    · rw [hout y hyB t, hout y hyB (B.sup Ky)]
  set T := B.sup Ky with hT
  have hstab : ∀ y : Site d, pconf s0 T y < 2 * (d : ℤ) := by
    intro y
    by_contra hc
    have hc' : 2 * (d : ℤ) ≤ pconf s0 T y := not_lt.mp hc
    have h1 : podo s0 (T + 1) y = podo s0 T y := congrFun (hglobal (T + 1) (by omega)) y
    rw [podo_succ, ite_eq_left hc'] at h1
    omega
  refine ⟨T, hglobal, fun y => hstab y, N, fun x hx => ?_⟩
  have h0 : fdbrStabilizer N x = 0 := fdbrStabilizer_eq_zero hx
  exact le_antisymm (by have := hle T x; rw [h0] at this; exact this)
    ((isLegalToppling_podo s0).nonneg T x)

end LatticeProb.Sandpile
