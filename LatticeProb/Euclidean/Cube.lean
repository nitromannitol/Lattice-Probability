import LatticeProb.Euclidean.Lattice

/-!
# Half-open unit cubes centered at integer points

The cube `cube w` of an integer point `w` is the half-open unit cube centered at `w`.  The
module proves that these cubes have volume one and are pairwise disjoint, and it compares the
critical radial power `|x|^{-d}` on a cube with its value at the center, with an explicit
constant.  No hypothesis is assumed beyond those stated on each declaration.
-/

noncomputable section

open scoped BigOperators
open LatticeProb.Euclidean.Lattice MeasureTheory Set

namespace LatticeProb.Euclidean.Cube

/-- The half-open unit cube centered at the integer point `w`. -/
def cube {d : ℕ} (w : Site d) : Set (Fin d → ℝ) :=
  {x | ∀ k, (w k : ℝ) - 1/2 ≤ x k ∧ x k < (w k : ℝ) + 1/2}

/-- The unit cube is the product of its half-open coordinate intervals. -/
lemma cube_eq_pi {d : ℕ} (w : Site d) :
    cube w = Set.pi Set.univ (fun k => Set.Ico ((w k : ℝ)-1/2) ((w k : ℝ)+1/2)) := by
  ext x
  simp only [cube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico, forall_const]

/-- A unit cube is measurable. -/
lemma cube_measurable {d : ℕ} (w : Site d) : MeasurableSet (cube w) := by
  rw [cube_eq_pi]
  exact MeasurableSet.pi (Set.countable_univ) (fun _ _ => measurableSet_Ico)

/-- A unit cube has Lebesgue volume one. -/
lemma cube_volume {d : ℕ} (w : Site d) : volume (cube w) = 1 := by
  rw [cube_eq_pi, Real.volume_pi_Ico]
  simp only [show ∀ k : Fin d, (w k : ℝ)+1/2 - ((w k : ℝ)-1/2) = 1 by intro k; ring,
    ENNReal.ofReal_one, Finset.prod_const_one]

/-- Distinct integer points have disjoint unit cubes. -/
lemma cubes_disjoint {d : ℕ} {w z : Site d} (hwz : w ≠ z) :
    Disjoint (cube w) (cube z) := by
  rw [Set.disjoint_left]
  intro x hx hz
  apply hwz
  funext k
  have h1 : ((w k : ℝ) - z k) < 1 := by linarith [(hx k).1, (hz k).2]
  have h2 : (-1:ℝ) < (w k : ℝ) - z k := by linarith [(hx k).2, (hz k).1]
  have h1' : w k - z k < 1 := by exact_mod_cast h1
  have h2' : -1 < w k - z k := by exact_mod_cast h2
  omega

/-- The constant `(d √d / 2) (4/3)^(d+1)` of the cube-to-center comparison. -/
def comparisonConstant (d : ℕ) : ℝ :=
  ((d : ℝ) * Real.sqrt d / 2) * (4/3 : ℝ) ^ (d+1)

/-- The constant of the disjoint-cube comparison is nonnegative. -/
lemma comparisonConstant_nonneg (d : ℕ) : 0 ≤ comparisonConstant d := by
  unfold comparisonConstant
  positivity

/-- For `c - 1/2 ≤ x < c + 1/2`, the square `(x - c)²` is at most `1/4`. -/
private lemma sq_sub_le_quarter {x c : ℝ} (h1 : c - 1 / 2 ≤ x) (h2 : x < c + 1 / 2) :
    (x - c) ^ 2 ≤ 1 / 4 := by
  calc (x - c) ^ 2 ≤ (1 / 2) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    _ = 1 / 4 := by norm_num

/-- A nonnegative `r` with `r ^ 2 ≤ s ^ 2 / 4` satisfies `r ≤ s / 2`, for `s ≥ 0`. -/
private lemma le_half_of_sq_le_quarter {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : r ^ 2 ≤ s ^ 2 / 4) : r ≤ s / 2 := by
  refine (sq_le_sq₀ hr (div_nonneg hs (by norm_num))).mp ?_
  calc r ^ 2 ≤ s ^ 2 / 4 := h
    _ = (s / 2) ^ 2 := by ring

/-- On the unit cube centered at `w`, the radius differs from the radius of `w` by at most
`√d / 2`. -/
lemma cube_radius_error {d : ℕ} (w : Site d) {x : Fin d → ℝ}
    (hx : x ∈ cube w) :
    |radius x - radius (physical 1 w)| ≤ Real.sqrt d / 2 := by
  apply (radius_difference x (physical 1 w)).trans
  have hs : ∑ k, (x k - (w k : ℝ))^2 ≤ (d : ℝ) / 4 := by
    calc
      _ ≤ ∑ _k : Fin d, (1/4 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact sq_sub_le_quarter (hx k).1 (hx k).2
      _ = _ := by simp [div_eq_mul_inv]
  have hn := radius_nonneg (x - physical 1 w)
  have he := radius_sq (x - physical 1 w)
  have hd := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  simp only [Pi.sub_apply, physical, one_mul] at he
  have hsq : radius (x - physical 1 w) ^ 2 ≤ Real.sqrt d ^ 2 / 4 := by
    rw [hd]
    linarith
  exact le_half_of_sq_le_quarter hn (Real.sqrt_nonneg _) hsq

/-- On the unit cube centered at `w` with `2√d ≤ |w|`, the radius is at least `3|w|/4`. -/
lemma cube_radius_lower {d : ℕ} (w : Site d) {x : Fin d → ℝ}
    (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) (hx : x ∈ cube w) :
    3 * radius (physical 1 w) / 4 ≤ radius x := by
  have h := (abs_le.mp (cube_radius_error w hx)).1
  linarith

/-- Scalar derivative comparison on a positive radial interval. -/
lemma radial_power_difference (d : ℕ) {a b : ℝ} (hb : 0 < b)
    (ha : 3*b/4 ≤ a) :
    |a ^ (-(d : ℤ)) - b ^ (-(d : ℤ))| ≤
      (d : ℝ) * (3*b/4) ^ (-((d+1 : ℕ) : ℤ)) * |a-b| := by
  let f : ℝ → ℝ := fun t => t ^ (-(d : ℤ))
  let f' : ℝ → ℝ := fun t => ((-(d : ℤ) : ℤ) : ℝ) * t ^ (-(d : ℤ) - 1)
  have hl : 0 < 3*b/4 := by linarith
  have hf : ∀ t ∈ Set.Ici (3*b/4), HasDerivWithinAt f (f' t) (Set.Ici (3*b/4)) t := by
    intro t ht
    exact hasDerivWithinAt_zpow _ t (Or.inl (ne_of_gt (hl.trans_le ht))) _
  have hbound : ∀ t ∈ Set.Ici (3*b/4), ‖f' t‖ ≤ (d:ℝ) * (3*b/4)^(-((d+1:ℕ):ℤ)) := by
    intro t ht
    have htpos := hl.trans_le ht
    have hi : t⁻¹ ≤ (3*b/4)⁻¹ := inv_anti₀ hl ht
    have hp := pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) hi (d+1)
    have hexp : -(d : ℤ) - 1 = -((d+1 : ℕ) : ℤ) := by omega
    have hmag : ‖f' t‖ = (d:ℝ) * t^(-((d+1:ℕ):ℤ)) := by
      change |((-(d:ℤ):ℤ):ℝ) * t^(-(d:ℤ)-1)| = _
      rw [abs_mul, hexp]
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d),
        abs_of_nonneg (zpow_nonneg htpos.le _)]
    rw [hmag]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hp
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound
    (convex_Ici (3*b/4)) (show b ∈ Set.Ici (3*b/4) by change 3*b/4 ≤ b; linarith) ha
  simpa only [f, Real.norm_eq_abs] using hm

/-- **Pointwise comparison on a unit cube.** For `2√d ≤ |w|`, the value of `|x|^{-d}` at a point
`x` of the unit cube centered at `w` differs from its value at `w` by at most
`comparisonConstant d · |w|^{-(d+1)}`. -/
theorem cube_radius_power_comparison (d : ℕ) (hd : 1 ≤ d) (w : Site d)
    (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) (x : Fin d → ℝ)
    (hx : x ∈ cube w) :
    |radius x ^ (-(d : ℤ)) - radius (physical 1 w) ^ (-(d : ℤ))| ≤
      comparisonConstant d * radius (physical 1 w) ^ (-((d+1 : ℕ) : ℤ)) := by
  have hdpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hb : 0 < radius (physical 1 w) := lt_of_lt_of_le (by positivity) hw
  have hl := cube_radius_lower w hw hx
  have hm := radial_power_difference d hb hl
  have hc : (0:ℝ) ≤ (d:ℝ) * (3 * radius (physical 1 w) / 4) ^ (-((d+1:ℕ):ℤ)) :=
    mul_nonneg (Nat.cast_nonneg d) (zpow_nonneg (by positivity) _)
  have h := hm.trans (mul_le_mul_of_nonneg_left (cube_radius_error w hx) hc)
  have he : (3 * radius (physical 1 w) / 4) ^ (-((d+1:ℕ):ℤ)) =
      (4/3 : ℝ) ^ (d+1) * radius (physical 1 w)^(-((d+1:ℕ):ℤ)) := by
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    rw [show 3 * radius (physical 1 w) / 4 = (3/4 : ℝ) * radius (physical 1 w) by ring,
      mul_pow, mul_inv_rev]
    simp only [← inv_pow]
    norm_num
    ring
  rw [he] at h
  calc
    _ ≤ (d:ℝ) * ((4/3:ℝ)^(d+1) * radius (physical 1 w)^(-((d+1:ℕ):ℤ))) * (Real.sqrt d/2) := h
    _ = _ := by unfold comparisonConstant; ring

/-- Real-exponent form of `cube_radius_power_comparison`. -/
theorem cube_radius_rpow_comparison (d : ℕ) (hd : 1 ≤ d) (w : Site d)
    (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) (x : Fin d → ℝ)
    (hx : x ∈ cube w) :
    |Real.rpow (radius x) (-(d:ℝ)) - Real.rpow (radius (physical 1 w)) (-(d:ℝ))| ≤
      comparisonConstant d * Real.rpow (radius (physical 1 w)) (-(d:ℝ)-1) := by
  have he : -(d:ℝ)-1 = -((d+1:ℕ):ℝ) := by push_cast; ring
  have hxpow : Real.rpow (radius x) (-(d:ℝ)) = radius x^(-(d:ℤ)) :=
    Real.rpow_neg_natCast _ d
  have hwpow : Real.rpow (radius (physical 1 w)) (-(d:ℝ)) =
      radius (physical 1 w)^(-(d:ℤ)) := Real.rpow_neg_natCast _ d
  have hnext : Real.rpow (radius (physical 1 w)) (-((d+1:ℕ):ℝ)) =
      radius (physical 1 w)^(-((d+1:ℕ):ℤ)) := Real.rpow_neg_natCast _ (d+1)
  rw [hxpow, hwpow, he, hnext]
  exact cube_radius_power_comparison d hd w hw x hx

end LatticeProb.Euclidean.Cube
