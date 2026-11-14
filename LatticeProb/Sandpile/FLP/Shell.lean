import LatticeProb.Sandpile.FLP.GreenComparison
import LatticeProb.Sandpile.FLP.BoxBounds
import LatticeProb.Sandpile.FLP.LowStabilize
import LatticeProb.External.LevinePeresShell

/-!
# The shell bound of Levine and Peres

For the background height `d - 1` with `n` chips at the origin, the parallel odometer is bounded
on the shell `c'₁ r - 1 < |x| ≤ c'₁ r`, uniformly in `n` and in time, where `r = (n / ω_d)^{1/d}`
and `c'₁ = (1 - ε)^{-1/d}`. This is the outer estimate in the proof of Theorem 4.1 of L. Levine
and Y. Peres, *Strong spherical asymptotics for rotor-router aggregation and the divisible
sandpile*, Potential Anal. 30 (2009), 1–27, [arXiv:0704.0688](https://arxiv.org/abs/0704.0688).

The proof compares the sum of the final odometer `w` over the cube `x + [-k, k]^d` with the sum
over the same cube of `(1 - ε) |y|² + n g(y)`, where `g` is the Green function of
`exists_greenComparison`. By the Le Borgne–Rossin count `box_sum_ge`, the difference is
subharmonic on the finite set of sites whose whole cube lies in the support of `w`. Off this set
it is bounded, by `le_of_lap_le_of_eq_zero` and the lower Green comparison, so the maximum
principle bounds it everywhere. The upper Green comparison then bounds `w` on the shell.

## Main results

* `podo_eq_zero_of_lt_abs`: when only the origin can be unstable, the parallel odometer at time
  `t` vanishes outside the box `[-t, t]^d`.
* `le_of_subharmonic`: the maximum principle for subharmonic functions on a finite set of sites.
* `exists_podo_le_of_radius`: the odometer bound near the sphere of radius `r`, where
  `ω_d r^d (1 - ε) = n`.
* `levinePeresShellBound`: the shell bound `LatticeProb.External.LevinePeresShellBound`.
-/

namespace LatticeProb.Sandpile.FLP

open LatticeProb

/-! ### The cube of offsets -/

/-- The cube `[-k, k]^d` of offsets. -/
def cube (d k : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(k : ℤ)) k

theorem mem_cube {d k : ℕ} {j : Site d} : j ∈ cube d k ↔ ∀ i, |j i| ≤ k := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem zero_mem_cube (d k : ℕ) : (0 : Site d) ∈ cube d k :=
  mem_cube.2 fun _ => by simp

theorem card_cube (d k : ℕ) : (cube d k).card = (2 * k + 1) ^ d := by
  rw [cube, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  congr 1
  omega

/-- A sum over the box `Q_k(x)` is a sum over the cube of offsets. -/
theorem sum_piFinset_Icc_eq {M : Type*} [AddCommMonoid M] {d : ℕ} (k : ℕ) (x : Site d)
    (F : Site d → M) :
    ∑ y ∈ Fintype.piFinset (fun i => Finset.Icc (x i - k) (x i + k)), F y =
      ∑ j ∈ cube d k, F (x + j) := by
  symm
  refine Finset.sum_nbij' (fun j => x + j) (fun y => y - x) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := mem_cube.1 hj
    simp only [Fintype.mem_piFinset, Finset.mem_Icc, Pi.add_apply]
    intro i
    have := abs_le.1 (hj' i)
    constructor <;> linarith [this.1, this.2]
  · intro y hy
    simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hy
    refine mem_cube.2 fun i => abs_le.2 ⟨?_, ?_⟩ <;> simp only [Pi.sub_apply] <;>
      linarith [(hy i).1, (hy i).2]
  · intro j _
    simp
  · intro y _
    simp
  · intro j _
    rfl

/-! ### Neighbour sums -/

/-- The neighbour sum of a sum of translates is the sum of the translated neighbour sums. -/
theorem nbrSum_sum_add {d : ℕ} (s : Finset (Site d)) (G : Site d → ℝ) (x : Site d) :
    nbrSum (fun y => ∑ j ∈ s, G (y + j)) x = ∑ j ∈ s, nbrSum G (x + j) := by
  simp only [nbrSum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show x + unit i + j = x + j + unit i by abel, show x - unit i + j = x + j - unit i by abel]

private theorem nbrSum_add_fun {d : ℕ} (f g : Site d → ℝ) (x : Site d) :
    nbrSum (fun y => f y + g y) x = nbrSum f x + nbrSum g x := by
  simp only [nbrSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem nbrSum_sub_fun {d : ℕ} (f g : Site d → ℝ) (x : Site d) :
    nbrSum (fun y => f y - g y) x = nbrSum f x - nbrSum g x := by
  simp only [nbrSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem nbrSum_mul_fun {d : ℕ} (c : ℝ) (f : Site d → ℝ) (x : Site d) :
    nbrSum (fun y => c * f y) x = c * nbrSum f x := by
  simp only [nbrSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem nbrSum_const_fun {d : ℕ} (c : ℝ) (x : Site d) :
    nbrSum (fun _ => c) x = 2 * d * c := by
  simp only [nbrSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem nbrSum_intCast {d : ℕ} (u : Site d → ℤ) (x : Site d) :
    nbrSum (fun y => (u y : ℝ)) x = (nbrSumZ u x : ℝ) := by
  simp [nbrSum, nbrSumZ]

private theorem euclidNorm_sq' {d : ℕ} (x : Site d) :
    euclidNorm x ^ 2 = ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem euclidNorm_add_unit_sq {d : ℕ} (y : Site d) (i : Fin d) :
    euclidNorm (y + unit i) ^ 2 = euclidNorm y ^ 2 + (2 * (y i : ℝ) + 1) := by
  rw [euclidNorm_sq', euclidNorm_sq']
  have h : ∀ l, (((y + unit i) l : ℤ) : ℝ) ^ 2 =
      ((y l : ℤ) : ℝ) ^ 2 + if i = l then 2 * (y i : ℝ) + 1 else 0 := by
    intro l
    by_cases hl : i = l
    · rw [ite_eq_left hl]
      subst hl
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      push_cast
      ring
    · rw [ite_eq_right hl]
      simp only [Pi.add_apply, unit, Pi.single_eq_of_ne (Ne.symm hl), add_zero]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem euclidNorm_sub_unit_sq {d : ℕ} (y : Site d) (i : Fin d) :
    euclidNorm (y - unit i) ^ 2 = euclidNorm y ^ 2 + (1 - 2 * (y i : ℝ)) := by
  rw [euclidNorm_sq', euclidNorm_sq']
  have h : ∀ l, (((y - unit i) l : ℤ) : ℝ) ^ 2 =
      ((y l : ℤ) : ℝ) ^ 2 + if i = l then 1 - 2 * (y i : ℝ) else 0 := by
    intro l
    by_cases hl : i = l
    · rw [ite_eq_left hl]
      subst hl
      simp only [Pi.sub_apply, unit, Pi.single_eq_same]
      push_cast
      ring
    · rw [ite_eq_right hl]
      simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne (Ne.symm hl), sub_zero, add_zero]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The neighbour sum of `|y|²` is `2d (|y|² + 1)`, so `Δ |y|² = 1` for the averaged Laplacian. -/
theorem nbrSum_euclidNorm_sq {d : ℕ} (y : Site d) :
    nbrSum (fun z => euclidNorm z ^ 2) y = 2 * d * euclidNorm y ^ 2 + 2 * d := by
  have h : ∀ i : Fin d, euclidNorm (y + unit i) ^ 2 + euclidNorm (y - unit i) ^ 2 =
      2 * euclidNorm y ^ 2 + 2 := fun i => by
    rw [euclidNorm_add_unit_sq, euclidNorm_sub_unit_sq]
    ring
  simp only [nbrSum, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private noncomputable def siteE {d : ℕ} (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

private theorem siteE_norm {d : ℕ} (x : Site d) : ‖siteE x‖ = euclidNorm x := by
  simp only [siteE, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]

private theorem siteE_add {d : ℕ} (x y : Site d) : siteE (x + y) = siteE x + siteE y := by
  ext i
  simp [siteE]

private theorem abs_euclidNorm_add_sub_le {d : ℕ} (x j : Site d) :
    |euclidNorm (x + j) - euclidNorm x| ≤ euclidNorm j := by
  rw [← siteE_norm, ← siteE_norm, ← siteE_norm, siteE_add]
  calc |‖siteE x + siteE j‖ - ‖siteE x‖| ≤ ‖siteE x + siteE j - siteE x‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖siteE j‖ := by rw [add_sub_cancel_left]

/-! ### The maximum principle and the support of the odometer -/

/-- **Maximum principle.** A function that is subharmonic at every site of a finite set `A` and
at most `M` off `A` is at most `M` everywhere. -/
theorem le_of_subharmonic {d : ℕ} (hd : 1 ≤ d) (A : Finset (Site d)) (V : Site d → ℝ) (M : ℝ)
    (hsub : ∀ x ∈ A, 2 * (d : ℝ) * V x ≤ nbrSum V x) (hout : ∀ x, x ∉ A → V x ≤ M)
    (x : Site d) : V x ≤ M := by
  classical
  by_contra hx
  push Not at hx
  have hxA : x ∈ A := by
    by_contra h
    exact absurd (hout x h) (not_le.mpr hx)
  let i₀ : Fin d := ⟨0, hd⟩
  obtain ⟨m, hmA, hmax⟩ := Finset.exists_max_image A V ⟨x, hxA⟩
  have hVm : M < V m := lt_of_lt_of_le hx (hmax x hxA)
  have hle : ∀ y, V y ≤ V m := fun y => by
    by_cases hy : y ∈ A
    · exact hmax y hy
    · exact (hout y hy).trans hVm.le
  obtain ⟨z, hzS, hzmax⟩ := Finset.exists_max_image (A.filter fun y => V y = V m)
    (fun y => y i₀) ⟨m, Finset.mem_filter.2 ⟨hmA, rfl⟩⟩
  obtain ⟨hzA, hzV⟩ := Finset.mem_filter.1 hzS
  have heq : V (z + unit i₀) = V m := by
    by_contra hne
    have hlt : V (z + unit i₀) < V m := lt_of_le_of_ne (hle _) hne
    have hsum : nbrSum V z < 2 * (d : ℝ) * V m := by
      unfold nbrSum
      calc ∑ i, (V (z + unit i) + V (z - unit i)) < ∑ _i : Fin d, (V m + V m) := by
            apply Finset.sum_lt_sum
            · exact fun i _ => add_le_add (hle _) (hle _)
            · exact ⟨i₀, Finset.mem_univ _, by linarith [hle (z - unit i₀)]⟩
        _ = 2 * (d : ℝ) * V m := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have := hsub z hzA
    rw [hzV] at this
    linarith
  have hA : z + unit i₀ ∈ A := by
    by_contra h
    have := hout _ h
    linarith
  have h1 := hzmax _ (Finset.mem_filter.2 ⟨hA, heq⟩)
  have h2 : (z + unit i₀) i₀ = z i₀ + 1 := by simp [unit]
  omega

/-- When every site other than the origin is stable in the initial configuration, the parallel
odometer at time `t` vanishes at every site with a coordinate of absolute value above `t`. -/
theorem podo_eq_zero_of_lt_abs {d : ℕ} (s0 : Site d → ℤ) (hs0 : ∀ x, x ≠ 0 → s0 x < 2 * d) :
    ∀ (t : ℕ) (x : Site d) (i : Fin d), (t : ℤ) < |x i| → podo s0 t x = 0 := by
  intro t
  induction t with
  | zero => intro x i _; rfl
  | succ t ih =>
    intro x i hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
      omega
    have hnb : ∀ j : Fin d, podo s0 t (x + unit j) = 0 ∧ podo s0 t (x - unit j) = 0 := by
      intro j
      rw [lt_abs] at hx
      constructor
      · refine ih _ i ?_
        rw [lt_abs]
        by_cases h : i = j
        · subst h; simp only [Pi.add_apply, unit, Pi.single_eq_same]; omega
        · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne h, add_zero]; push_cast at hx ⊢; omega
      · refine ih _ i ?_
        rw [lt_abs]
        by_cases h : i = j
        · subst h; simp only [Pi.sub_apply, unit, Pi.single_eq_same]; omega
        · simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne h, sub_zero]; push_cast at hx ⊢; omega
    have hself : podo s0 t x = 0 := ih x i (by push_cast at hx; omega)
    have hlap : lap (podo s0 t) x = 0 := by
      simp only [lap, nbrSumZ, hself, (hnb _).1, (hnb _).2]
      simp
    rw [podo_succ, pconf, hself, hlap, add_zero, ite_eq_right (not_le.mpr (hs0 x hx0)), add_zero]

/-! ### The odometer near the sphere -/

/-- The final odometer of `(d - 1) + n δ₀` is bounded, uniformly in `n` and in time, at every site
within distance `1` of the sphere of radius `r ≥ 1`, where `ω_d r^d (1 - ε) = n`. -/
theorem exists_podo_le_of_radius (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ c : ℝ, ∀ n : ℕ, ∀ r : ℝ, 1 ≤ r → omegaD d * r ^ d * (1 - ε) = n →
      ∀ x : Site d, |euclidNorm x - r| ≤ 1 → ∀ t : ℕ,
        ((podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) t x : ℤ) : ℝ) ≤ c := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h2d : (0 : ℝ) < 2 * d := by linarith
  obtain ⟨g, hg, a, hgc⟩ := exists_greenComparison d hd
  have hgN : ∀ z, nbrSum g z = 2 * d * (g z - if z = 0 then 1 else 0) := by
    intro z
    have h := hg z
    unfold LatticeProb.walkOp at h
    rw [div_eq_iff h2d.ne'] at h
    linarith
  set k : ℕ := ⌈(d : ℝ) / ε⌉₊ with hk
  have hkε : (d : ℝ) ≤ ε * k := by
    have := Nat.le_ceil ((d : ℝ) / ε)
    rw [div_le_iff₀ hε] at this
    rw [← hk] at this
    linarith
  obtain ⟨C₀, hC₀⟩ := le_of_lap_le_of_eq_zero d d (d * (2 * k))
  obtain ⟨CK, hCK⟩ := hgc (1 + Real.sqrt d * k)
  refine ⟨((2 * (k : ℝ) + 1) ^ d * (2 * d * C₀ + |a|) + (2 * (k : ℝ) + 1) ^ d * |CK|) / (2 * d),
    ?_⟩
  intro n r hr hrn x hx t
  obtain ⟨T, hT, hstable⟩ := stabilizable_of_le d hd1 ((d : ℤ) - 1) (by omega) n
  set w := podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) T with hw
  have hw0 : ∀ y, 0 ≤ w y := fun y => (podo_isLegal _).nonneg T y
  have hle : ∀ t y, podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) t y ≤ w y :=
    fun t y => podo_le_podo_of_le_n d hd1 ((d : ℤ) - 1) (by omega) le_rfl T hT t y
  have hdirac : ∀ y : Site d, 0 ≤ dirac 0 y := fun y => by
    unfold dirac
    split_ifs <;> norm_num
  have hlap : ∀ y, lap w y ≤ d := by
    intro y
    have h1 := hstable y
    have h2 : 0 ≤ (n : ℤ) * dirac 0 y := mul_nonneg (by positivity) (hdirac y)
    linarith
  have hsupp : ∀ (y : Site d) (i : Fin d), (T : ℤ) < |y i| → w y = 0 := fun y i hy =>
    podo_eq_zero_of_lt_abs _ (fun z hz => by
      show ((d : ℤ) - 1) + (n : ℤ) * dirac 0 z < 2 * d
      rw [dirac_of_ne hz]
      omega) T y i hy
  obtain ⟨A, hA⟩ : ∃ A : Finset (Site d), ∀ y, y ∈ A ↔ ∀ j ∈ cube d k, 0 < w (y + j) := by
    refine ⟨(Fintype.piFinset fun _ : Fin d => Finset.Icc (-(T : ℤ)) T).filter
      fun y => ∀ j ∈ cube d k, 0 < w (y + j), fun y => ?_⟩
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
    rw [Finset.mem_Icc]
    by_contra hi
    have hTi : (T : ℤ) < |y i| := by
      rw [lt_abs]
      omega
    have h0 := h 0 (zero_mem_cube d k)
    rw [add_zero, hsupp y i hTi] at h0
    exact lt_irrefl _ h0
  obtain ⟨G, hG⟩ : ∃ G : Site d → ℝ, ∀ z, G z = 2 * d * ((w z : ℤ) : ℝ) - (1 - ε) *
      (euclidNorm z ^ 2 + omegaD d * r ^ d * g z - (euclidNorm x ^ 2 + omegaD d * r ^ d * g x)) :=
    ⟨_, fun _ => rfl⟩
  have hD : ∀ z, nbrSum G z - 2 * d * G z =
      2 * d * (((lap w z : ℤ) : ℝ) + n * ((dirac 0 z : ℤ) : ℝ) - (1 - ε)) := by
    intro z
    have hdz : ((dirac 0 z : ℤ) : ℝ) = if z = 0 then 1 else 0 := by
      unfold dirac
      split_ifs <;> simp
    have hlz : ((lap w z : ℤ) : ℝ) = (nbrSumZ w z : ℝ) - 2 * d * ((w z : ℤ) : ℝ) := by
      rw [lap_eq]
      push_cast
      ring
    rw [show G = fun z => 2 * d * ((w z : ℤ) : ℝ) - (1 - ε) *
      (euclidNorm z ^ 2 + omegaD d * r ^ d * g z - (euclidNorm x ^ 2 + omegaD d * r ^ d * g x))
      from funext hG]
    simp only [nbrSum_sub_fun, nbrSum_add_fun, nbrSum_mul_fun, nbrSum_const_fun, nbrSum_intCast,
      nbrSum_euclidNorm_sq, hgN]
    rw [hdz, hlz]
    linear_combination (2 * (d : ℝ) * (if z = 0 then 1 else 0)) * hrn
  have hsub : ∀ y ∈ A, 2 * (d : ℝ) * (∑ j ∈ cube d k, G (y + j)) ≤
      nbrSum (fun y => ∑ j ∈ cube d k, G (y + j)) y := by
    intro y hy
    have hy' := (hA y).1 hy
    have hpos : ∀ y' : Site d, (∀ i, |y' i - y i| ≤ (k : ℤ)) →
        0 < podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) T y' := by
      intro y' hy''
      have := hy' (y' - y) (mem_cube.2 fun i => by simpa using hy'' i)
      simpa using this
    have hb := box_sum_ge d ((d : ℤ) - 1) n T k y hpos
    rw [sum_piFinset_Icc_eq, ← hw] at hb
    have hbR : (d : ℝ) * (2 * k) * (2 * k + 1) ^ (d - 1) ≤ ∑ j ∈ cube d k,
        (((d : ℝ) - 1) + n * ((dirac 0 (y + j) : ℤ) : ℝ) + ((lap w (y + j) : ℤ) : ℝ)) := by
      exact_mod_cast hb
    have hV : nbrSum (fun y => ∑ j ∈ cube d k, G (y + j)) y -
        2 * (d : ℝ) * (∑ j ∈ cube d k, G (y + j)) = ∑ j ∈ cube d k,
          (2 * (d : ℝ) * (((d : ℝ) - 1) + n * ((dirac 0 (y + j) : ℤ) : ℝ) +
            ((lap w (y + j) : ℤ) : ℝ)) - 2 * d * (d - ε)) := by
      rw [nbrSum_sum_add, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hD (y + j)]
      ring
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, card_cube,
      nsmul_eq_mul] at hV
    push_cast at hV
    have hP : (0 : ℝ) ≤ (2 * k + 1) ^ (d - 1) := by positivity
    have hpow : (2 * (k : ℝ) + 1) ^ d = (2 * k + 1) ^ (d - 1) * (2 * k + 1) := by
      rw [← pow_succ, Nat.sub_add_cancel hd1]
    have hkey : ((d : ℝ) - ε) * (2 * k + 1) ≤ d * (2 * k) := by nlinarith
    have := mul_le_mul_of_nonneg_left hkey hP
    rw [hpow] at hV
    nlinarith
  have hout : ∀ y, y ∉ A →
      (∑ j ∈ cube d k, G (y + j)) ≤ (2 * (k : ℝ) + 1) ^ d * (2 * d * C₀ + |a|) := by
    intro y hy
    rw [hA] at hy
    push Not at hy
    obtain ⟨j₀, hj₀, hw₀⟩ := hy
    have hz : w (y + j₀) = 0 := le_antisymm hw₀ (hw0 _)
    calc ∑ j ∈ cube d k, G (y + j) ≤ ∑ _j ∈ cube d k, (2 * d * C₀ + |a| : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [hG]
          have hdist : ∑ i, |(y + j) i - (y + j₀) i| ≤ ((d * (2 * k) : ℕ) : ℤ) := by
            calc ∑ i, |(y + j) i - (y + j₀) i| ≤ ∑ _i : Fin d, (2 * (k : ℤ)) :=
                  Finset.sum_le_sum fun i _ => by
                    have h1 := abs_le.1 (mem_cube.1 hj i)
                    have h2 := abs_le.1 (mem_cube.1 hj₀ i)
                    simp only [Pi.add_apply]
                    rw [abs_le]
                    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
              _ = ((d * (2 * k) : ℕ) : ℤ) := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  push_cast
                  ring
          have h1 : w (y + j) ≤ C₀ := hC₀ w hw0 hlap (y + j) (y + j₀) hdist hz
          have h1' : ((w (y + j) : ℤ) : ℝ) ≤ C₀ := by exact_mod_cast h1
          have h2 := (hCK r hr x (y + j) hx).1
          have h3 : 0 ≤ (1 - ε) * (euclidNorm (y + j) ^ 2 + omegaD d * r ^ d * g (y + j) -
              (euclidNorm x ^ 2 + omegaD d * r ^ d * g x) + a) :=
            mul_nonneg (by linarith) (by linarith)
          have h4 : 0 ≤ ε * |a| := mul_nonneg hε.le (abs_nonneg a)
          have h5 : 0 ≤ (1 - ε) * (|a| - a) :=
            mul_nonneg (by linarith) (by linarith [le_abs_self a])
          nlinarith
      _ = (2 * (k : ℝ) + 1) ^ d * (2 * d * C₀ + |a|) := by
          rw [Finset.sum_const, card_cube, nsmul_eq_mul]
          push_cast
          ring
  have hmax : (∑ j ∈ cube d k, G (x + j)) ≤ (2 * (k : ℝ) + 1) ^ d * (2 * d * C₀ + |a|) :=
    le_of_subharmonic hd1 A (fun y => ∑ j ∈ cube d k, G (y + j)) _ hsub hout x
  have hterm : ∀ j ∈ cube d k, 2 * d * ((w (x + j) : ℤ) : ℝ) ≤ G (x + j) + |CK| := by
    intro j hj
    rw [hG]
    have hK : |euclidNorm (x + j) - r| ≤ 1 + Real.sqrt d * k := by
      have h1 := abs_euclidNorm_add_sub_le x j
      have h2 : euclidNorm j ≤ Real.sqrt d * k := by
        have h3 := euclidNorm_le_sqrt_mul_supNorm j
        have h4 : supNorm j ≤ k := supNorm_le_iff.2 (mem_cube.1 hj)
        have h5 : (supNorm j : ℝ) ≤ k := by exact_mod_cast h4
        exact h3.trans (mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _))
      have h6 := abs_sub_le (euclidNorm (x + j)) (euclidNorm x) r
      linarith
    have h2 := (hCK r hr x (x + j) hx).2 hK
    have h3 : 0 ≤ (1 - ε) * (CK - (euclidNorm (x + j) ^ 2 + omegaD d * r ^ d * g (x + j) -
        (euclidNorm x ^ 2 + omegaD d * r ^ d * g x))) :=
      mul_nonneg (by linarith) (by linarith)
    have h4 : 0 ≤ ε * |CK| := mul_nonneg hε.le (abs_nonneg CK)
    have h5 : 0 ≤ (1 - ε) * (|CK| - CK) := mul_nonneg (by linarith) (by linarith [le_abs_self CK])
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, card_cube, nsmul_eq_mul] at hsum
  push_cast at hsum
  have hsingle : 2 * d * ((w x : ℤ) : ℝ) ≤ ∑ j ∈ cube d k, 2 * d * ((w (x + j) : ℤ) : ℝ) := by
    have := Finset.single_le_sum (f := fun j => 2 * (d : ℝ) * ((w (x + j) : ℤ) : ℝ))
      (fun j _ => mul_nonneg h2d.le (by exact_mod_cast hw0 (x + j))) (zero_mem_cube d k)
    simpa using this
  have hpodo : ((podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) t x : ℤ) : ℝ) ≤
      ((w x : ℤ) : ℝ) := by exact_mod_cast hle t x
  rw [le_div_iff₀ h2d]
  nlinarith

/-! ### The shell bound -/

/-- **The shell bound of Levine and Peres** (Theorem 4.1 of Levine and Peres, outer estimate,
for the background height `d - 1`). -/
theorem levinePeresShellBound : LatticeProb.External.LevinePeresShellBound := by
  intro d hd ε hε hε1
  obtain ⟨c, hc⟩ := exists_podo_le_of_radius d hd ε hε hε1
  have hω := omegaD_pos d
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  obtain ⟨T₀, hT₀, -⟩ := stabilizable_of_le d (by omega) ((d : ℤ) - 1) (by omega) ⌈omegaD d⌉₊
  refine ⟨max ⌈c⌉₊ (podo (fun y : Site d => ((d : ℤ) - 1) + (⌈omegaD d⌉₊ : ℤ) * dirac 0 y)
    T₀ 0).toNat, ?_⟩
  intro n _ x hx1 hx2 t
  set r := (1 - ε) ^ (-(1 / (d : ℝ))) * ((n : ℝ) / omegaD d) ^ (1 / (d : ℝ)) with hr
  have hc1 : ((1 - ε) ^ (-(1 / (d : ℝ)))) ^ d = (1 - ε)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
      show -(1 / (d : ℝ)) * (d : ℝ) = -1 by field_simp, Real.rpow_neg_one]
  have hq : (((n : ℝ) / omegaD d) ^ (1 / (d : ℝ))) ^ d = (n : ℝ) / omegaD d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (Nat.cast_nonneg n) hω.le),
      show 1 / (d : ℝ) * (d : ℝ) = 1 by field_simp, Real.rpow_one]
  have h1ε : (1 - ε) ≠ 0 := by linarith
  have hrn : omegaD d * r ^ d * (1 - ε) = n := by
    rw [hr, mul_pow, hc1, hq]
    field_simp
  by_cases h1 : 1 ≤ r
  · have h2 := (hc n r h1 hrn x (abs_le.2 ⟨by linarith, by linarith⟩) t).trans (Nat.le_ceil c)
    have h3 : podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) t x ≤ (⌈c⌉₊ : ℤ) := by
      exact_mod_cast h2
    exact h3.trans (by exact_mod_cast le_max_left _ _)
  · push Not at h1
    have hr0 : 0 ≤ r := by
      rw [hr]
      exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) hω.le) _)
    have hx0 : x = 0 := by
      have h2 : (supNorm x : ℝ) < 1 := (supNorm_le_euclidNorm x).trans_lt (hx2.trans_lt h1)
      have h3 : supNorm x = 0 := by
        have : supNorm x < 1 := by exact_mod_cast h2
        omega
      funext i
      have h4 := supNorm_le_iff.mp h3.le i
      simp only [Nat.cast_zero, abs_nonpos_iff] at h4
      simpa using h4
    have hnN : n ≤ ⌈omegaD d⌉₊ := by
      have hrd : r ^ d < 1 := pow_lt_one₀ hr0 h1 (by omega)
      have h5 : r ^ d * (1 - ε) < 1 := by nlinarith [pow_nonneg hr0 d]
      have h6 : (n : ℝ) < omegaD d := by
        rw [← hrn]
        nlinarith
      have h7 : (n : ℝ) < ⌈omegaD d⌉₊ := h6.trans_le (Nat.le_ceil _)
      exact_mod_cast h7.le
    subst hx0
    have h8 := podo_le_podo_of_le_n d (by omega) ((d : ℤ) - 1) (by omega) hnN T₀ hT₀ t 0
    refine h8.trans ((Int.self_le_toNat _).trans ?_)
    exact_mod_cast le_max_right _ _

end LatticeProb.Sandpile.FLP
