import LatticeProb.Analysis.Elliptic.Holder

/-!
# Hölder norms and composition on convex sets

Component bounds for the coordinate Hölder norm.
-/

namespace LatticeProb.Elliptic

open scoped ENNReal BigOperators Topology

noncomputable section

variable {d : ℕ} {σ : ℝ} {S T : Set (Fin d → ℝ)} {u : (Fin d → ℝ) → ℝ}
  {φ : (Fin d → ℝ) → (Fin d → ℝ)}

/-- The supremum norm is controlled by the coordinate Hölder norm. -/
theorem supNorm_le_c2HolderNorm : supNorm S u ≤ c2HolderNorm σ S u := by
  unfold c2HolderNorm
  exact le_self_add.trans (le_self_add.trans le_self_add)

/-- Each first derivative is controlled by the coordinate Hölder norm. -/
theorem partialDeriv_supNorm_le_c2HolderNorm (i : Fin d) :
    supNorm S (partialDeriv i u) ≤ c2HolderNorm σ S u := by
  have hi : supNorm S (partialDeriv i u) ≤ ∑ k, supNorm S (partialDeriv k u) :=
    Finset.single_le_sum (f := fun k : Fin d => supNorm S (partialDeriv k u))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  exact hi.trans (le_add_self.trans (le_self_add.trans le_self_add))

/-- Each second derivative is controlled by the coordinate Hölder norm. -/
theorem secondPartial_supNorm_le_c2HolderNorm (i j : Fin d) :
    supNorm S (secondPartial i j u) ≤ c2HolderNorm σ S u := by
  have hj : supNorm S (secondPartial i j u) ≤ ∑ k, supNorm S (secondPartial i k u) :=
    Finset.single_le_sum (f := fun k : Fin d => supNorm S (secondPartial i k u))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  have hi : (∑ k, supNorm S (secondPartial i k u)) ≤
      ∑ l, ∑ k, supNorm S (secondPartial l k u) :=
    Finset.single_le_sum (f := fun l : Fin d => ∑ k, supNorm S (secondPartial l k u))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  exact hj.trans (hi.trans (le_add_self.trans le_self_add))

/-- Each Hölder seminorm of a second derivative is controlled by the full norm. -/
theorem secondPartial_holderSeminorm_le_c2HolderNorm (i j : Fin d) :
    holderSeminorm σ S (secondPartial i j u) ≤ c2HolderNorm σ S u := by
  have hj : holderSeminorm σ S (secondPartial i j u) ≤
      ∑ k, holderSeminorm σ S (secondPartial i k u) :=
    Finset.single_le_sum (f := fun k : Fin d => holderSeminorm σ S (secondPartial i k u))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  have hi : (∑ k, holderSeminorm σ S (secondPartial i k u)) ≤
      ∑ l, ∑ k, holderSeminorm σ S (secondPartial l k u) :=
    Finset.single_le_sum (f := fun l : Fin d => ∑ k, holderSeminorm σ S (secondPartial l k u))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  exact hj.trans (hi.trans le_add_self)

/-- A uniform real bound controls the extended supremum norm. -/
theorem supNorm_le_of_abs_bound {f : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hf : ∀ x ∈ S, |f x| ≤ B) : supNorm S f ≤ ENNReal.ofReal B := by
  exact iSup_le fun x => iSup_le fun hx => ENNReal.ofReal_le_ofReal (hf x hx)

/-- A uniform increment bound controls the Euclidean Hölder seminorm. -/
theorem holderSeminorm_le_of_increment_bound {f : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤
      B * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) :
    holderSeminorm σ S f ≤ ENNReal.ofReal B := by
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => ENNReal.ofReal_le_ofReal ?_
  exact (div_le_iff₀ (Real.rpow_pos_of_pos
    (LatticeProb.Euclidean.Lattice.radius_pos (sub_ne_zero.mpr hxy)) σ)).mpr
      (hf x hx y hy)

/-- A finite norm bounds each value by the real value of the full norm. -/
theorem abs_le_c2HolderNorm_toReal (hn : c2HolderNorm σ S u < ⊤)
    {x : Fin d → ℝ} (hx : x ∈ S) : |u x| ≤ (c2HolderNorm σ S u).toReal := by
  exact (abs_le_supNorm_toReal (lt_of_le_of_lt supNorm_le_c2HolderNorm hn) hx).trans
    (ENNReal.toReal_mono hn.ne supNorm_le_c2HolderNorm)

/-- A finite norm bounds each coordinate derivative. -/
theorem abs_partialDeriv_le_c2HolderNorm_toReal (hn : c2HolderNorm σ S u < ⊤)
    (i : Fin d) {x : Fin d → ℝ} (hx : x ∈ S) :
    |partialDeriv i u x| ≤ (c2HolderNorm σ S u).toReal := by
  exact (abs_le_supNorm_toReal
    (lt_of_le_of_lt (partialDeriv_supNorm_le_c2HolderNorm i) hn) hx).trans
      (ENNReal.toReal_mono hn.ne (partialDeriv_supNorm_le_c2HolderNorm i))

/-- A finite norm bounds each coordinate second derivative. -/
theorem abs_secondPartial_le_c2HolderNorm_toReal (hn : c2HolderNorm σ S u < ⊤)
    (i j : Fin d) {x : Fin d → ℝ} (hx : x ∈ S) :
    |secondPartial i j u x| ≤ (c2HolderNorm σ S u).toReal := by
  exact (abs_le_supNorm_toReal
    (lt_of_le_of_lt (secondPartial_supNorm_le_c2HolderNorm i j) hn) hx).trans
      (ENNReal.toReal_mono hn.ne (secondPartial_supNorm_le_c2HolderNorm i j))

/-- A finite norm bounds the Hölder increments of the second derivatives. -/
theorem abs_sub_secondPartial_le_c2HolderNorm_toReal (hn : c2HolderNorm σ S u < ⊤)
    (i j : Fin d) {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |secondPartial i j u x - secondPartial i j u y| ≤
      (c2HolderNorm σ S u).toReal * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  have h₂ := secondPartial_supNorm_le_c2HolderNorm (σ := σ) (S := S) (u := u) i j
  have hH := secondPartial_holderSeminorm_le_c2HolderNorm (σ := σ) (S := S) (u := u) i j
  have hfinite : c0HolderNorm σ S (secondPartial i j u) < ⊤ := by
    simp only [c0HolderNorm, ENNReal.add_lt_top]
    exact ⟨lt_of_le_of_lt h₂ hn, lt_of_le_of_lt hH hn⟩
  exact (abs_sub_le_holderSeminorm_toReal hfinite hx hy).trans
    (mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hn.ne hH)
      (Real.rpow_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg _) _))

/-- Coordinate bounds control a linear functional in the supremum norm. -/
theorem norm_linearMap_le_of_coordinate_bound (L : (Fin d → ℝ) →L[ℝ] ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hL : ∀ i, |L (Pi.single i 1)| ≤ B) :
    ‖L‖ ≤ d * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro v
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    simp
  calc
    ‖L v‖ = ‖∑ i, v i * L (Pi.single i 1)‖ := by
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul, smul_eq_mul]
    _ ≤ ∑ i, ‖v i * L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖v‖ * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm v i) (hL i) (abs_nonneg _) (norm_nonneg _)
    _ = (d * B) * ‖v‖ := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring

/-- On an open convex set, bounded coordinate Hessian entries bound increments of a first
partial derivative. -/
theorem abs_sub_partialDeriv_le_of_convex (hS : IsOpen S) (hSc : Convex ℝ S)
    (hu : ContDiffOn ℝ 2 u S) (hn : c2HolderNorm σ S u < ⊤) (i : Fin d)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |partialDeriv i u x - partialDeriv i u y| ≤
      (d * (c2HolderNorm σ S u).toReal) * ‖x - y‖ := by
  have hd (z : Fin d → ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fderiv ℝ u) z := by
    exact ((hu.fderiv_of_isOpen (m := 1) hS (by norm_num)).contDiffAt (hS.mem_nhds hz)).differentiableAt
      (by norm_num)
  have hp (z : Fin d → ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (partialDeriv i u) z := by
    exact (hd z hz).clm_apply (differentiableAt_const _)
  have hbound (z : Fin d → ℝ) (hz : z ∈ S) :
      ‖fderiv ℝ (partialDeriv i u) z‖ ≤ d * (c2HolderNorm σ S u).toReal := by
    apply norm_linearMap_le_of_coordinate_bound _ ENNReal.toReal_nonneg
    intro j
    have heq : fderiv ℝ (partialDeriv i u) z (Pi.single j 1) =
        secondPartial j i u z := by
      change fderiv ℝ (fun w => fderiv ℝ u w (Pi.single i 1)) z (Pi.single j 1) = _
      rw [fderiv_clm_apply (hd z hz) (differentiableAt_const _)]
      simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply, secondPartial, iteratedFDeriv_two_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [heq]
    exact abs_secondPartial_le_c2HolderNorm_toReal hn j i hz
  simpa only [Real.norm_eq_abs] using
    (hSc.norm_image_sub_le_of_norm_fderiv_le hp hbound hy hx)

/-- On a convex set, the full norm controls Hölder increments of first partials. -/
theorem abs_sub_partialDeriv_le_c2HolderNorm_of_convex
    (hσ : 0 < σ) (hσ' : σ < 1) (hS : IsOpen S) (hSc : Convex ℝ S)
    (hu : ContDiffOn ℝ 2 u S) (hn : c2HolderNorm σ S u < ⊤) (i : Fin d)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |partialDeriv i u x - partialDeriv i u y| ≤
      (d + 2) * (c2HolderNorm σ S u).toReal *
        LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  let r := LatticeProb.Euclidean.Lattice.radius (x - y)
  let N := (c2HolderNorm σ S u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hr : 0 ≤ r := LatticeProb.Euclidean.Lattice.radius_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hnr : ‖x - y‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg hr).2
    intro j
    simpa only [Real.norm_eq_abs] using
      LatticeProb.Euclidean.Lattice.abs_coord_le_radius (x - y) j
  by_cases hsmall : r ≤ 1
  · have hrpow : r ≤ r ^ σ := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hr hsmall hσ.le hσ'.le)
    have h := abs_sub_partialDeriv_le_of_convex hS hSc hu hn i hx hy
    have hstep := mul_le_mul_of_nonneg_left (hnr.trans hrpow) (mul_nonneg hd hN)
    have hrest : 0 ≤ 2 * N * r ^ σ := by positivity
    dsimp only [N, r] at hstep ⊢
    linarith
  · have hlarge : 1 ≤ r ^ σ := Real.one_le_rpow (le_of_not_ge hsmall) hσ.le
    have hxy : |partialDeriv i u x - partialDeriv i u y| ≤ 2 * N := by
      calc
        _ ≤ |partialDeriv i u x| + |partialDeriv i u y| := abs_sub _ _
        _ ≤ N + N := add_le_add (abs_partialDeriv_le_c2HolderNorm_toReal hn i hx)
          (abs_partialDeriv_le_c2HolderNorm_toReal hn i hy)
        _ = 2 * N := by ring
    have hstep := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2 * N by positivity)
    have hrest : 0 ≤ d * N * r ^ σ := by positivity
    dsimp only [N, r] at hstep hxy hrest ⊢
    nlinarith

/-- The first partial Hölder seminorm is controlled on an open convex set. -/
theorem holderSeminorm_partialDeriv_le_c2HolderNorm_of_convex
    (hσ : 0 < σ) (hσ' : σ < 1) (hS : IsOpen S) (hSc : Convex ℝ S)
    (hu : ContDiffOn ℝ 2 u S) (hn : c2HolderNorm σ S u < ⊤) (i : Fin d) :
    holderSeminorm σ S (partialDeriv i u) ≤
      ENNReal.ofReal (d + 2) * c2HolderNorm σ S u := by
  calc
    holderSeminorm σ S (partialDeriv i u) ≤
        ENNReal.ofReal ((d + 2) * (c2HolderNorm σ S u).toReal) :=
      holderSeminorm_le_of_increment_bound fun _ hx _ hy =>
        abs_sub_partialDeriv_le_c2HolderNorm_of_convex hσ hσ' hS hSc hu hn i hx hy
    _ = ENNReal.ofReal (d + 2) * c2HolderNorm σ S u := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hn.ne]

/-- Euclidean distance is bounded by a fixed multiple of the supremum norm. -/
theorem radius_le_pi_norm (v : Fin d → ℝ) :
    LatticeProb.Euclidean.Lattice.radius v ≤
      ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ *
        ‖v‖ := by
  simpa only [LatticeProb.Euclidean.Lattice.radius_norm, ContinuousLinearEquiv.coe_coe,
    PiLp.coe_symm_continuousLinearEquiv] using
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.le_opNorm v)

/-- The supremum norm is bounded by the Euclidean radius. -/
theorem pi_norm_le_radius (v : Fin d → ℝ) :
    ‖v‖ ≤ LatticeProb.Euclidean.Lattice.radius v := by
  apply (pi_norm_le_iff_of_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg v)).2
  intro i
  simpa only [Real.norm_eq_abs] using LatticeProb.Euclidean.Lattice.abs_coord_le_radius v i

/-- A map Lipschitz for the coordinate supremum norm is Lipschitz for Euclidean radius. -/
theorem radius_sub_le_of_lipschitzOnWith {φ : (Fin d → ℝ) → (Fin d → ℝ)}
    {K : NNReal} (hφ : LipschitzOnWith K φ S) {x y : Fin d → ℝ}
    (hx : x ∈ S) (hy : y ∈ S) :
    LatticeProb.Euclidean.Lattice.radius (φ x - φ y) ≤
      (‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) *
        LatticeProb.Euclidean.Lattice.radius (x - y) := by
  have h := hφ.dist_le_mul x hx y hy
  rw [dist_eq_norm, dist_eq_norm] at h
  calc
    _ ≤ ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ *
        ‖φ x - φ y‖ := radius_le_pi_norm _
    _ ≤ ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ *
        (K * LatticeProb.Euclidean.Lattice.radius (x - y)) := by
      gcongr
      exact h.trans (mul_le_mul_of_nonneg_left (pi_norm_le_radius (x - y)) K.coe_nonneg)
    _ = _ := by ring

/-- A Lipschitz coordinate map transports scalar Hölder increments. -/
theorem abs_sub_comp_le_holderSeminorm_toReal {T : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)}
    (hσ : 0 ≤ σ) (hf : c0HolderNorm σ T f < ⊤) (hmap : Set.MapsTo φ S T)
    {K : NNReal} (hφ : LipschitzOnWith K φ S) {x y : Fin d → ℝ}
    (hx : x ∈ S) (hy : y ∈ S) :
    |f (φ x) - f (φ y)| ≤
      (holderSeminorm σ T f).toReal *
        (‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ *
          LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  have hM : 0 ≤ ‖(PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * (K : ℝ) := by positivity
  have hr := LatticeProb.Euclidean.Lattice.radius_nonneg (x - y)
  calc
    _ ≤ (holderSeminorm σ T f).toReal *
        LatticeProb.Euclidean.Lattice.radius (φ x - φ y) ^ σ :=
      abs_sub_le_holderSeminorm_toReal hf (hmap hx) (hmap hy)
    _ ≤ (holderSeminorm σ T f).toReal *
        ((‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) *
          LatticeProb.Euclidean.Lattice.radius (x - y)) ^ σ := by
      gcongr
      · exact LatticeProb.Euclidean.Lattice.radius_nonneg _
      · exact radius_sub_le_of_lipschitzOnWith hφ hx hy
    _ = _ := by rw [Real.mul_rpow hM hr]; ring

/-- Product increments are controlled by the bounds and increments of their factors. -/
theorem abs_mul_sub_mul_le_of_bounds {a b c e A B H J R : ℝ}
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (ha : |a| ≤ A) (he : |e| ≤ B)
    (hac : |a - c| ≤ H * R) (hbe : |b - e| ≤ J * R) :
    |a * b - c * e| ≤ (H * B + A * J) * R := by
  have hident : a * b - c * e = (a - c) * e + a * (b - e) := by ring
  rw [hident]
  calc
    _ ≤ |(a - c) * e| + |a * (b - e)| := abs_add_le _ _
    _ = |a - c| * |e| + |a| * |b - e| := by rw [abs_mul, abs_mul]
    _ ≤ (H * R) * B + A * (J * R) := by
      gcongr
    _ = _ := by ring

/-- Coordinate form of the first-order chain rule. -/
theorem partialDeriv_comp {φ : (Fin d → ℝ) → (Fin d → ℝ)} {x : Fin d → ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hu : DifferentiableAt ℝ u (φ x)) (i : Fin d) :
    partialDeriv i (u ∘ φ) x =
      ∑ j, partialDeriv j u (φ x) * partialDeriv i (fun y => φ y j) x := by
  change fderiv ℝ (u ∘ φ) x (Pi.single i 1) = _
  rw [fderiv_comp x hu hφ, ContinuousLinearMap.comp_apply]
  have hv (v : Fin d → ℝ) : v = ∑ j, v j • Pi.single j (1 : ℝ) := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    simp
  conv_lhs => rw [hv (fderiv ℝ φ x (Pi.single i 1))]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have heq : (fderiv ℝ φ x (Pi.single i 1)) j =
      partialDeriv i (fun y => φ y j) x := by
    rw [partialDeriv, fderiv_apply hφ j, ContinuousLinearMap.comp_apply]
    rfl
  rw [heq]
  simp only [partialDeriv]
  ring

/-- Bounds for values, coordinate derivatives, and their increments control the full norm. -/
theorem c2HolderNorm_le_of_bounds {B₀ B₁ B₂ H : ℝ}
    (h₀ : ∀ x ∈ S, |u x| ≤ B₀)
    (h₁ : ∀ i x, x ∈ S → |partialDeriv i u x| ≤ B₁)
    (h₂ : ∀ i j x, x ∈ S → |secondPartial i j u x| ≤ B₂)
    (hH : ∀ i j x, x ∈ S → ∀ y ∈ S,
      |secondPartial i j u x - secondPartial i j u y| ≤
        H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) :
    c2HolderNorm σ S u ≤ ENNReal.ofReal B₀ +
      (∑ _ : Fin d, ENNReal.ofReal B₁) +
      (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal B₂) +
      (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal H) := by
  unfold c2HolderNorm
  apply add_le_add
  · apply add_le_add
    · apply add_le_add (supNorm_le_of_abs_bound h₀)
      exact Finset.sum_le_sum fun i _ => supNorm_le_of_abs_bound (h₁ i)
    · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        supNorm_le_of_abs_bound (h₂ i j)
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      holderSeminorm_le_of_increment_bound (hH i j)

/-- Differentiating a coordinate partial gives the corresponding Hessian entry. -/
theorem fderiv_partialDeriv_apply {x : Fin d → ℝ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : Fin d) :
    fderiv ℝ (partialDeriv i u) x (Pi.single j 1) = secondPartial j i u x := by
  change fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x (Pi.single j 1) = _
  rw [fderiv_clm_apply hu (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, secondPartial, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The second derivative of a composition is obtained by differentiating the first-order chain rule. -/
theorem secondPartial_comp_as_fderiv_sum (hS : IsOpen S) (hT : IsOpen T)
    (hφ : ContDiffOn ℝ 2 φ S) (hu : ContDiffOn ℝ 2 u T) (hmap : Set.MapsTo φ S T)
    {x : Fin d → ℝ} (hx : x ∈ S) (i j : Fin d) :
    secondPartial j i (u ∘ φ) x =
      fderiv ℝ (fun z => ∑ k, partialDeriv k u (φ z) *
        partialDeriv i (fun y => φ y k) z) x (Pi.single j 1) := by
  have heq : partialDeriv i (u ∘ φ) =ᶠ[𝓝 x]
      fun z => ∑ k, partialDeriv k u (φ z) * partialDeriv i (fun y => φ y k) z := by
    filter_upwards [hS.mem_nhds hx] with z hz
    exact partialDeriv_comp ((hφ.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num))
      ((hu.contDiffAt (hT.mem_nhds (hmap hz))).differentiableAt (by norm_num)) i
  have hc : ContDiffOn ℝ 2 (u ∘ φ) S := hu.comp hφ hmap
  have hd : DifferentiableAt ℝ (fderiv ℝ (u ∘ φ)) x :=
    ((hc.fderiv_of_isOpen (m := 1) hS (by norm_num)).contDiffAt
      (hS.mem_nhds hx)).differentiableAt (by norm_num)
  rw [← fderiv_partialDeriv_apply hd i j, heq.fderiv_eq]

/-- Coordinate chain rule for a first partial derivative. -/
theorem partialDeriv_comp_partialDeriv {φ : (Fin d → ℝ) → (Fin d → ℝ)}
    {x : Fin d → ℝ} (hφ : DifferentiableAt ℝ φ x)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) (φ x)) (i j : Fin d) :
    partialDeriv j ((partialDeriv i u) ∘ φ) x =
      ∑ k, secondPartial k i u (φ x) * partialDeriv j (fun y => φ y k) x := by
  have hd : DifferentiableAt ℝ (partialDeriv i u) (φ x) :=
    hu.clm_apply (differentiableAt_const _)
  rw [partialDeriv_comp hφ hd j]
  apply Finset.sum_congr rfl
  intro k _
  change fderiv ℝ (partialDeriv i u) (φ x) (Pi.single k 1) * _ = _
  rw [fderiv_partialDeriv_apply hu]


/-- Coordinate form of the second-order chain rule. -/
theorem secondPartial_comp (hS : IsOpen S) (hT : IsOpen T)
    (hφ : ContDiffOn ℝ 2 φ S) (hu : ContDiffOn ℝ 2 u T) (hmap : Set.MapsTo φ S T)
    {x : Fin d → ℝ} (hx : x ∈ S) (i j : Fin d) :
    secondPartial j i (u ∘ φ) x =
      ∑ k, ((∑ l, secondPartial l k u (φ x) *
        partialDeriv j (fun y => φ y l) x) * partialDeriv i (fun y => φ y k) x +
        partialDeriv k u (φ x) * secondPartial j i (fun y => φ y k) x) := by
  have hp : DifferentiableAt ℝ φ x :=
    (hφ.contDiffAt (hS.mem_nhds hx)).differentiableAt (by norm_num)
  have hud : DifferentiableAt ℝ (fderiv ℝ u) (φ x) :=
    ((hu.fderiv_of_isOpen (m := 1) hT (by norm_num)).contDiffAt
      (hT.mem_nhds (hmap hx))).differentiableAt (by norm_num)
  have hcoord (k : Fin d) : ContDiffOn ℝ 2 (fun y => φ y k) S :=
    (contDiff_apply ℝ ℝ k).comp_contDiffOn hφ
  have hpd (k : Fin d) : DifferentiableAt ℝ (partialDeriv i (fun y => φ y k)) x := by
    have h := (((hcoord k).fderiv_of_isOpen (m := 1) hS (by norm_num)).contDiffAt
      (hS.mem_nhds hx)).differentiableAt (by norm_num)
    exact h.clm_apply (differentiableAt_const _)
  have hpc (k : Fin d) : DifferentiableAt ℝ ((partialDeriv k u) ∘ φ) x :=
    (hud.clm_apply (differentiableAt_const _)).comp x hp
  rw [secondPartial_comp_as_fderiv_sum hS hT hφ hu hmap hx i j]
  rw [fderiv_fun_sum (A := fun k z => partialDeriv k u (φ z) *
    partialDeriv i (fun y => φ y k) z) (fun k _ => (hpc k).mul (hpd k))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hmul := fderiv_fun_mul (hpc k) (hpd k)
  simp only [Function.comp_apply] at hmul
  rw [hmul]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change partialDeriv k u (φ x) * partialDeriv j (partialDeriv i (fun y => φ y k)) x +
    partialDeriv i (fun y => φ y k) x * partialDeriv j ((partialDeriv k u) ∘ φ) x = _
  rw [partialDeriv_comp_partialDeriv hp hud k j]
  have hφd : DifferentiableAt ℝ (fderiv ℝ (fun y => φ y k)) x :=
    (((hcoord k).fderiv_of_isOpen (m := 1) hS (by norm_num)).contDiffAt
      (hS.mem_nhds hx)).differentiableAt (by norm_num)
  rw [show partialDeriv j (partialDeriv i (fun y => φ y k)) x =
    secondPartial j i (fun y => φ y k) x from fderiv_partialDeriv_apply hφd i j]
  ring


/-- A pointwise bound for the second derivatives of a composition. -/
theorem abs_secondPartial_comp_le (hS : IsOpen S) (hT : IsOpen T)
    (hφ : ContDiffOn ℝ 2 φ S) (hu : ContDiffOn ℝ 2 u T) (hmap : Set.MapsTo φ S T)
    (hn : c2HolderNorm σ T u < ⊤) {M : ℝ} (hM : 0 ≤ M)
    (hφbound : ∀ k, (c2HolderNorm σ S (fun y => φ y k)).toReal ≤ M)
    (hφn : ∀ k, c2HolderNorm σ S (fun y => φ y k) < ⊤)
    {x : Fin d → ℝ} (hx : x ∈ S) (i j : Fin d) :
    |secondPartial j i (u ∘ φ) x| ≤
      ((d : ℝ) ^ 2 * M ^ 2 + d * M) * (c2HolderNorm σ T u).toReal := by
  let N := (c2HolderNorm σ T u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hfirst (k a : Fin d) : |partialDeriv a (fun y => φ y k) x| ≤ M :=
    (abs_partialDeriv_le_c2HolderNorm_toReal (hφn k) a hx).trans (hφbound k)
  have hsecond (k : Fin d) : |secondPartial j i (fun y => φ y k) x| ≤ M :=
    (abs_secondPartial_le_c2HolderNorm_toReal (hφn k) j i hx).trans (hφbound k)
  rw [secondPartial_comp hS hT hφ hu hmap hx i j]
  calc
    _ ≤ ∑ k, |(∑ l, secondPartial l k u (φ x) *
        partialDeriv j (fun y => φ y l) x) * partialDeriv i (fun y => φ y k) x +
        partialDeriv k u (φ x) * secondPartial j i (fun y => φ y k) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, ((d : ℝ) * (N * M) * M + N * M) := by
      apply Finset.sum_le_sum
      intro k _
      have hs : |∑ l, secondPartial l k u (φ x) *
          partialDeriv j (fun y => φ y l) x| ≤ (d : ℝ) * (N * M) := by
        calc
          _ ≤ ∑ l, |secondPartial l k u (φ x) *
              partialDeriv j (fun y => φ y l) x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _l : Fin d, N * M := by
            apply Finset.sum_le_sum
            intro l _
            rw [abs_mul]
            exact mul_le_mul (abs_secondPartial_le_c2HolderNorm_toReal hn l k (hmap hx))
              (hfirst l j) (abs_nonneg _) hN
          _ = _ := by simp
      calc
        _ ≤ |(∑ l, secondPartial l k u (φ x) *
            partialDeriv j (fun y => φ y l) x) * partialDeriv i (fun y => φ y k) x| +
            |partialDeriv k u (φ x) * secondPartial j i (fun y => φ y k) x| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul hs (hfirst k i) (abs_nonneg _) (by positivity))
            (mul_le_mul (abs_partialDeriv_le_c2HolderNorm_toReal hn k (hmap hx))
              (hsecond k) (abs_nonneg _) hN)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring


/-- A pointwise bound for the first derivatives of a composition. -/
theorem abs_partialDeriv_comp_le (hS : IsOpen S) (hT : IsOpen T)
    (hφ : ContDiffOn ℝ 2 φ S) (hu : ContDiffOn ℝ 2 u T) (hmap : Set.MapsTo φ S T)
    (hn : c2HolderNorm σ T u < ⊤) {M : ℝ}
    (hφbound : ∀ k, (c2HolderNorm σ S (fun y => φ y k)).toReal ≤ M)
    (hφn : ∀ k, c2HolderNorm σ S (fun y => φ y k) < ⊤)
    {x : Fin d → ℝ} (hx : x ∈ S) (i : Fin d) :
    |partialDeriv i (u ∘ φ) x| ≤
      (d : ℝ) * M * (c2HolderNorm σ T u).toReal := by
  have hp := (hφ.contDiffAt (hS.mem_nhds hx)).differentiableAt (by norm_num)
  have hud := (hu.contDiffAt (hT.mem_nhds (hmap hx))).differentiableAt (by norm_num)
  rw [partialDeriv_comp hp hud i]
  calc
    _ ≤ ∑ k, |partialDeriv k u (φ x) * partialDeriv i (fun y => φ y k) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, (c2HolderNorm σ T u).toReal * M := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (abs_partialDeriv_le_c2HolderNorm_toReal hn k (hmap hx))
        ((abs_partialDeriv_le_c2HolderNorm_toReal (hφn k) i hx).trans (hφbound k))
        (abs_nonneg _) ENNReal.toReal_nonneg
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring


/-- A Hölder increment bound for a product of three scalar factors. -/
theorem abs_mul_mul_sub_mul_mul_le_of_bounds
    {a a' b b' c c' A B C H J L R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hR : 0 ≤ R)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hb' : |b'| ≤ B) (hc' : |c'| ≤ C)
    (haa : |a - a'| ≤ H * R) (hbb : |b - b'| ≤ J * R)
    (hcc : |c - c'| ≤ L * R) :
    |a * b * c - a' * b' * c'| ≤ ((H * B + A * J) * C + A * B * L) * R := by
  have hab : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hA
  have hab' : |a * b - a' * b'| ≤ (H * B + A * J) * R :=
    abs_mul_sub_mul_le_of_bounds hH hR hA ha hb' haa hbb
  exact abs_mul_sub_mul_le_of_bounds (by positivity) hR (mul_nonneg hA hB)
    hab hc' hab' hcc


/-- Transport a Hölder increment bound along a Lipschitz coordinate map. -/
theorem abs_sub_comp_le_of_holder_bound {f : (Fin d → ℝ) → ℝ}
    (hσ : 0 ≤ σ) {H : ℝ} (hH : 0 ≤ H)
    (hf : ∀ x ∈ T, ∀ y ∈ T, |f x - f y| ≤
      H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ)
    (hmap : Set.MapsTo φ S T) {K : NNReal} (hφ : LipschitzOnWith K φ S)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |f (φ x) - f (φ y)| ≤
      (H * (‖(PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ) *
          LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  have hM : 0 ≤ ‖(PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * (K : ℝ) := by positivity
  have hr := LatticeProb.Euclidean.Lattice.radius_nonneg (x - y)
  calc
    _ ≤ H * LatticeProb.Euclidean.Lattice.radius (φ x - φ y) ^ σ := hf _ (hmap hx) _ (hmap hy)
    _ ≤ H * ((‖(PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) *
        LatticeProb.Euclidean.Lattice.radius (x - y)) ^ σ := by
      gcongr
      · exact LatticeProb.Euclidean.Lattice.radius_nonneg _
      · exact radius_sub_le_of_lipschitzOnWith hφ hx hy
    _ = _ := by rw [Real.mul_rpow hM hr]; ring


/-- Hölder increments of a composed Hessian are controlled by the two component norms. -/
theorem abs_sub_secondPartial_comp_le (hσ : 0 < σ) (hσ' : σ < 1)
    (hS : IsOpen S) (hT : IsOpen T) (hSc : Convex ℝ S) (hTc : Convex ℝ T)
    (hφ : ContDiffOn ℝ 2 φ S) (hu : ContDiffOn ℝ 2 u T) (hmap : Set.MapsTo φ S T)
    (hn : c2HolderNorm σ T u < ⊤) {M : ℝ} (hM : 0 ≤ M)
    (hφbound : ∀ k, (c2HolderNorm σ S (fun y => φ y k)).toReal ≤ M)
    (hφn : ∀ k, c2HolderNorm σ S (fun y => φ y k) < ⊤)
    {K : NNReal} (hLip : LipschitzOnWith K φ S)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) (i j : Fin d) :
    |secondPartial j i (u ∘ φ) x - secondPartial j i (u ∘ φ) y| ≤
      ((d : ℝ) ^ 2 * (M ^ 2 *
          ((‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ + 2 * (d + 2))) +
        d * M * ((d + 2) *
          (‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ + 1)) *
      (c2HolderNorm σ T u).toReal * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  let N := (c2HolderNorm σ T u).toReal
  let A : ℝ := d + 2
  let Q : ℝ := (‖(PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ
  let R := LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := Real.rpow_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg _) _
  have hp (k a : Fin d) (z : Fin d → ℝ) (hz : z ∈ S) :
      |partialDeriv a (fun w => φ w k) z| ≤ M :=
    (abs_partialDeriv_le_c2HolderNorm_toReal (hφn k) a hz).trans (hφbound k)
  have hs (k a b : Fin d) (z : Fin d → ℝ) (hz : z ∈ S) :
      |secondPartial a b (fun w => φ w k) z| ≤ M :=
    (abs_secondPartial_le_c2HolderNorm_toReal (hφn k) a b hz).trans (hφbound k)
  have hpi (k a : Fin d) : |partialDeriv a (fun w => φ w k) x -
      partialDeriv a (fun w => φ w k) y| ≤ (A * M) * R := by
    have hc : ContDiffOn ℝ 2 (fun w => φ w k) S := (contDiff_apply ℝ ℝ k).comp_contDiffOn hφ
    have h := abs_sub_partialDeriv_le_c2HolderNorm_of_convex hσ hσ' hS hSc hc (hφn k) a hx hy
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hφbound k) hA) hR)
  have hsi (k a b : Fin d) : |secondPartial a b (fun w => φ w k) x -
      secondPartial a b (fun w => φ w k) y| ≤ M * R := by
    exact (abs_sub_secondPartial_le_c2HolderNorm_toReal (hφn k) a b hx hy).trans
      (mul_le_mul_of_nonneg_right (hφbound k) hR)
  have houter1 (k : Fin d) : |partialDeriv k u (φ x) - partialDeriv k u (φ y)| ≤
      (A * N * Q) * R := by
    exact abs_sub_comp_le_of_holder_bound hσ.le (mul_nonneg hA hN)
      (fun _ hx' _ hy' => abs_sub_partialDeriv_le_c2HolderNorm_of_convex
        hσ hσ' hT hTc hu hn k hx' hy') hmap hLip hx hy
  have houter2 (k l : Fin d) : |secondPartial l k u (φ x) - secondPartial l k u (φ y)| ≤
      (N * Q) * R := by
    exact abs_sub_comp_le_of_holder_bound hσ.le hN
      (fun _ hx' _ hy' => abs_sub_secondPartial_le_c2HolderNorm_toReal hn l k hx' hy')
      hmap hLip hx hy
  have hprod3 (k l : Fin d) :
      |secondPartial l k u (φ x) * partialDeriv j (fun w => φ w l) x *
          partialDeriv i (fun w => φ w k) x -
        secondPartial l k u (φ y) * partialDeriv j (fun w => φ w l) y *
          partialDeriv i (fun w => φ w k) y| ≤
      (((N * Q) * M + N * (A * M)) * M + N * M * (A * M)) * R := by
    apply abs_mul_mul_sub_mul_mul_le_of_bounds hN hM (mul_nonneg hN hQ)
      (mul_nonneg hA hM) hR
    · exact abs_secondPartial_le_c2HolderNorm_toReal hn l k (hmap hx)
    · exact hp l j x hx
    · exact hp l j y hy
    · exact hp k i y hy
    · exact houter2 k l
    · exact hpi l j
    · exact hpi k i
  have hprod2 (k : Fin d) :
      |partialDeriv k u (φ x) * secondPartial j i (fun w => φ w k) x -
        partialDeriv k u (φ y) * secondPartial j i (fun w => φ w k) y| ≤
      ((A * N * Q) * M + N * M) * R := by
    exact abs_mul_sub_mul_le_of_bounds (by positivity) hR hN
      (abs_partialDeriv_le_c2HolderNorm_toReal hn k (hmap hx)) (hs k j i y hy)
      (houter1 k) (hsi k j i)
  rw [secondPartial_comp hS hT hφ hu hmap hx i j,
    secondPartial_comp hS hT hφ hu hmap hy i j, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k, |((∑ l, secondPartial l k u (φ x) *
        partialDeriv j (fun w => φ w l) x) * partialDeriv i (fun w => φ w k) x +
        partialDeriv k u (φ x) * secondPartial j i (fun w => φ w k) x) -
        ((∑ l, secondPartial l k u (φ y) *
        partialDeriv j (fun w => φ w l) y) * partialDeriv i (fun w => φ w k) y +
        partialDeriv k u (φ y) * secondPartial j i (fun w => φ w k) y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, ((d : ℝ) *
        ((((N * Q) * M + N * (A * M)) * M + N * M * (A * M)) * R) +
          ((A * N * Q) * M + N * M) * R) := by
      apply Finset.sum_le_sum
      intro k _
      have hsum : |(∑ l, secondPartial l k u (φ x) *
          partialDeriv j (fun w => φ w l) x) * partialDeriv i (fun w => φ w k) x -
          (∑ l, secondPartial l k u (φ y) *
          partialDeriv j (fun w => φ w l) y) * partialDeriv i (fun w => φ w k) y| ≤
          (d : ℝ) * ((((N * Q) * M + N * (A * M)) * M + N * M * (A * M)) * R) := by
        simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (by
          calc
            _ ≤ ∑ _l : Fin d, ((((N * Q) * M + N * (A * M)) * M + N * M * (A * M)) * R) :=
              Finset.sum_le_sum fun l _ => hprod3 k l
            _ = _ := by simp)
      have hsplit : ∀ a b c e : ℝ, |(a + b) - (c + e)| ≤ |a - c| + |b - e| := by
        intro a b c e
        have hid : (a + b) - (c + e) = (a - c) + (b - e) := by ring
        rw [hid]
        exact abs_add_le _ _
      exact (hsplit _ _ _ _).trans (add_le_add hsum (hprod2 k))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; dsimp [A, N, Q, R]; ring


/-- A smooth coordinate change with bounded Hölder norm acts boundedly on `C^{2,σ}`. -/
theorem c2HolderNorm_comp {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1)
    (S T : Set (Fin d → ℝ)) (hS : IsOpen S) (hT : IsOpen T)
    (hSconvex : Convex ℝ S) (hTconvex : Convex ℝ T) (φ : (Fin d → ℝ) → Fin d → ℝ)
    (hφ : ContDiffOn ℝ 2 φ S) (hmap : Set.MapsTo φ S T)
    (hφn : ∀ i, c2HolderNorm σ S (fun x => φ x i) < ⊤)
    (K : NNReal) (hLip : LipschitzOnWith K φ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ 2 u T → c2HolderNorm σ T u < ⊤ →
      ContDiffOn ℝ 2 (u ∘ φ) S ∧
      c2HolderNorm σ S (u ∘ φ) ≤ ENNReal.ofReal C * c2HolderNorm σ T u := by
  let M : ℝ := 1 + ∑ k : Fin d, (c2HolderNorm σ S (fun y => φ y k)).toReal
  let Q : ℝ := (‖(PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ
  let P₁ : ℝ := d * M
  let P₂ : ℝ := (d : ℝ) ^ 2 * M ^ 2 + d * M
  let P₃ : ℝ := (d : ℝ) ^ 2 * (M ^ 2 * (Q + 2 * (d + 2))) +
    d * M * ((d + 2) * Q + 1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP₁ : 0 ≤ P₁ := by dsimp [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by dsimp [P₂]; positivity
  have hP₃ : 0 ≤ P₃ := by dsimp [P₃]; positivity
  have hbound (k : Fin d) : (c2HolderNorm σ S (fun y => φ y k)).toReal ≤ M := by
    have h := Finset.single_le_sum (f := fun l : Fin d =>
      (c2HolderNorm σ S (fun y => φ y l)).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ k)
    dsimp [M]
    linarith
  let C : ℝ := 1 + (∑ _ : Fin d, P₁) + (∑ _ : Fin d, ∑ _ : Fin d, P₂) +
    (∑ _ : Fin d, ∑ _ : Fin d, P₃)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun u hu hn => ⟨hu.comp hφ hmap, ?_⟩⟩
  let N := (c2HolderNorm σ T u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hb := c2HolderNorm_le_of_bounds (σ := σ) (S := S) (u := u ∘ φ)
    (B₀ := N) (B₁ := P₁ * N) (B₂ := P₂ * N) (H := P₃ * N)
    (fun x hx => abs_le_c2HolderNorm_toReal hn (hmap hx))
    (fun i x hx => abs_partialDeriv_comp_le hS hT hφ hu hmap hn hbound hφn hx i)
    (fun i j x hx => by
      simpa only using abs_secondPartial_comp_le hS hT hφ hu hmap hn hM hbound hφn hx j i)
    (fun i j x hx y hy => by
      simpa only using abs_sub_secondPartial_comp_le hσ hσ' hS hT hSconvex hTconvex
        hφ hu hmap hn hM hbound hφn hLip hx hy j i)
  have hcoef : ENNReal.ofReal C = 1 + (∑ _ : Fin d, ENNReal.ofReal P₁) +
      (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal P₂) +
      (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal P₃) := by
    dsimp [C]
    have hsum₁ : 0 ≤ ∑ _ : Fin d, P₁ := Finset.sum_nonneg fun _ _ => hP₁
    have hsum₂ : 0 ≤ ∑ _ : Fin d, ∑ _ : Fin d, P₂ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hP₂
    have hsum₃ : 0 ≤ ∑ _ : Fin d, ∑ _ : Fin d, P₃ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hP₃
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg (by norm_num) hsum₁) hsum₂) hsum₃,
      ENNReal.ofReal_add (add_nonneg (by norm_num) hsum₁) hsum₂,
      ENNReal.ofReal_add (by norm_num) hsum₁]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg (fun _ _ => hP₁),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => hP₂),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => hP₃),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => hP₂),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => hP₃)]
  calc
    _ ≤ ENNReal.ofReal N + (∑ _ : Fin d, ENNReal.ofReal (P₁ * N)) +
        (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal (P₂ * N)) +
        (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal (P₃ * N)) := hb
    _ = ENNReal.ofReal C * c2HolderNorm σ T u := by
      rw [hcoef]
      dsimp only [N]
      simp only [ENNReal.ofReal_mul hP₁, ENNReal.ofReal_mul hP₂, ENNReal.ofReal_mul hP₃,
        ENNReal.ofReal_toReal hn.ne, one_mul, add_mul, Finset.sum_mul]

end

end LatticeProb.Elliptic
