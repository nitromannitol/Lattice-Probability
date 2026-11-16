import LatticeProb.Analysis.Schauder.DirichletInverse

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.SineSum`.

# The sine series of a test function on the whole space

For a test function `f` of the unit cube and `D > 0`, the sine series `F = sineSum f` is smooth
on `ℝ^d`, `−DΔu = F` on `ℝ^d` for `u = (−DΔ_Q)⁻¹ f`, and the derivatives of `F` of order at most
`3` are bounded by `c3Norm f`: `F` is the odd
`2`-periodic extension of `f`, and the coordinate reflections and even translations are isometries.
The odd `2`-periodicity is proved for every sine series `sineSeries a`, and the smoothness of
`sineSum f` is the smoothness of `sineSeries (sineCoeff f)`.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- The sine series of a test function is smooth on `ℝ^d`: the termwise derivatives of every
order are summable since the coefficients decay faster than any power of `λ_k`. -/
theorem contDiff_sineSum (hd : 1 ≤ d) (f : Euc d → ℝ) (hf : Sobolev.IsTestFn (unitCube d) f) :
    ContDiff ℝ (⊤ : ℕ∞) (sineSum f) := by
  rw [sineSum_eq_sineSeries]
  exact contDiff_sineSeries (summable_pow_mul_abs_sineCoeff hd f hf)

/-- The sine series of a test function solves `−DΔu = F` at every point for the Dirichlet
inverse `u`, since each term does. -/
theorem neg_mul_laplacianSum_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (z : Euc d) :
    -(D * laplacianSum (dirichletInverse D f) z) = sineSum f z := by
  rw [laplacianSum_dirichletInverse hd hD f hf z]
  have h1 : ∀ k : Fin d → ℕ, -((D * dirichletEigenvalue k)⁻¹ * sineCoeff f k *
      (dirichletEigenvalue k * sineMode k z)) = -(D⁻¹ * (sineCoeff f k * sineMode k z)) :=
    fun k => by
      have := (dirichletEigenvalue_pos hd k).ne'
      field_simp
  simp_rw [h1]
  rw [tsum_neg, tsum_mul_left]
  unfold sineSum
  field_simp

/-- The linear isometry of `ℝ^d` negating the coordinates flagged by `σ`. -/
def flipIso (σ : Fin d → Bool) : Euc d ≃ₗᵢ[ℝ] Euc d :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i =>
    cond (σ i) (LinearIsometryEquiv.neg ℝ) (LinearIsometryEquiv.refl ℝ ℝ)

/-- The coordinates of `flipIso σ z`. -/
theorem flipIso_apply (σ : Fin d → Bool) (z : Euc d) (i : Fin d) :
    flipIso σ z i = if σ i then -z i else z i := by
  unfold flipIso
  rw [LinearIsometryEquiv.piLpCongrRight_apply]
  cases hσ : σ i <;> simp [hσ]

/-- The translation of `ℝ^d` by the even integer vector `2 n`. -/
def evenShift (n : Fin d → ℤ) : Euc d := WithLp.toLp 2 fun i => 2 * (n i : ℝ)

/-- A sine mode is odd in each coordinate and `2`-periodic: composing with a flip and an even
shift multiplies it by the product of the signs. -/
theorem sineMode_flipIso_add (k : Fin d → ℕ) (σ : Fin d → Bool) (n : Fin d → ℤ) (z : Euc d) :
    sineMode k (flipIso σ z + evenShift n) =
      (∏ i, if σ i then (-1 : ℝ) else 1) * sineMode k z := by
  unfold sineMode
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : Real.sin (Real.pi * ((k i : ℝ) + 1) * (flipIso σ z + evenShift n) i) =
      (if σ i then -1 else 1) * Real.sin (Real.pi * ((k i : ℝ) + 1) * z i) := by
    have hi : (flipIso σ z + evenShift n) i = (if σ i then -z i else z i) + 2 * (n i : ℝ) := by
      rw [PiLp.add_apply, flipIso_apply]
      rfl
    rw [hi]
    have h2 : Real.pi * ((k i : ℝ) + 1) * ((if σ i then -z i else z i) + 2 * (n i : ℝ)) =
        Real.pi * ((k i : ℝ) + 1) * (if σ i then -z i else z i) +
          ((((k i : ℤ) + 1) * n i : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [h2, Real.sin_add_int_mul_two_pi]
    split_ifs <;> simp [mul_neg, Real.sin_neg]
  rw [h]
  ring

/-- A sine series is odd in each coordinate and `2`-periodic. -/
theorem sineSeries_flipIso_add (a : (Fin d → ℕ) → ℝ) (σ : Fin d → Bool) (n : Fin d → ℤ)
    (z : Euc d) :
    sineSeries a (flipIso σ z + evenShift n) =
      (∏ i, if σ i then (-1 : ℝ) else 1) * sineSeries a z := by
  unfold sineSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [sineMode_flipIso_add]
  ring

/-- The sine series of a test function is odd in each coordinate and `2`-periodic. -/
theorem sineSum_flipIso_add (f : Euc d → ℝ) (σ : Fin d → Bool) (n : Fin d → ℤ) (z : Euc d) :
    sineSum f (flipIso σ z + evenShift n) = (∏ i, if σ i then (-1 : ℝ) else 1) * sineSum f z := by
  rw [sineSum_eq_sineSeries]
  exact sineSeries_flipIso_add (sineCoeff f) σ n z

/-- Every point of `ℝ^d` is mapped into the closed cube by a coordinate flip followed by an even
integer shift. -/
theorem exists_flipIso_add_mem_closedCube (z : Euc d) :
    ∃ (σ : Fin d → Bool) (n : Fin d → ℤ), flipIso σ z + evenShift n ∈ closedCube d := by
  have h1 : ∀ t : ℝ, ∃ (b : Bool) (m : ℤ), 0 ≤ (if b then -t else t) + 2 * (m : ℝ) ∧
      (if b then -t else t) + 2 * (m : ℝ) ≤ 1 := by
    intro t
    have h2 : (⌊t / 2⌋ : ℝ) ≤ t / 2 := Int.floor_le _
    have h3 : t / 2 < (⌊t / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    by_cases h : t - 2 * (⌊t / 2⌋ : ℝ) ≤ 1
    · refine ⟨!true, -⌊t / 2⌋, ?_, ?_⟩ <;> push_cast <;> simp <;> linarith
    · refine ⟨true, ⌊t / 2⌋ + 1, ?_, ?_⟩ <;> push_cast <;> simp <;> linarith
  choose σ n hσ using fun i => h1 (z i)
  refine ⟨σ, n, fun i => ?_⟩
  have hi : (flipIso σ z + evenShift n) i = (if σ i then -z i else z i) + 2 * (n i : ℝ) := by
    rw [PiLp.add_apply, flipIso_apply]
    rfl
  rw [hi]
  exact hσ i

/-- The iterated derivative of the sine series has the same norm at a point and at its image
under a coordinate flip followed by an even integer shift. -/
theorem norm_iteratedFDeriv_sineSum_flipIso_add (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (σ : Fin d → Bool) (n : Fin d → ℤ) (m : ℕ)
    (z : Euc d) :
    ‖iteratedFDeriv ℝ m (sineSum f) (flipIso σ z + evenShift n)‖ =
      ‖iteratedFDeriv ℝ m (sineSum f) z‖ := by
  set s : ℝ := ∏ i, if σ i then (-1 : ℝ) else 1 with hs
  have hs1 : |s| = 1 := by
    rw [hs, Finset.abs_prod]
    exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp
  have hcomp : ((fun w => sineSum f (w + evenShift n)) ∘ flipIso σ) =
      fun w => s • sineSum f w := by
    funext w
    exact sineSum_flipIso_add f σ n w
  have hg : ContDiffAt ℝ m (sineSum f) z :=
    ((contDiff_sineSum hd f hf).of_le (by exact_mod_cast le_top)).contDiffAt
  have h1 := (flipIso σ).norm_iteratedFDeriv_comp_right (fun w => sineSum f (w + evenShift n)) z m
  rw [iteratedFDeriv_comp_add_right, hcomp, iteratedFDeriv_const_smul_apply' hg, norm_smul,
    Real.norm_eq_abs, hs1, one_mul] at h1
  exact h1.symm

/-- A derivative of a test function of order at most `3` is bounded by `c3Norm`. -/
theorem norm_iteratedFDeriv_le_c3Norm {f : Euc d → ℝ} (hf : Sobolev.IsTestFn (unitCube d) f)
    {m : ℕ} (hm : m ≤ 3) (z : Euc d) : ‖iteratedFDeriv ℝ m f z‖ ≤ c3Norm f := by
  have hc : Continuous (iteratedFDeriv ℝ m f) :=
    hf.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hb : BddAbove (Set.range fun w => ‖iteratedFDeriv ℝ m f w‖) :=
    hc.norm.bddAbove_range_of_hasCompactSupport (hf.2.1.iteratedFDeriv m).norm
  have hb' : BddAbove (Set.range fun k : Fin 4 => ⨆ w, ‖iteratedFDeriv ℝ k f w‖) :=
    (Set.finite_range _).bddAbove
  calc ‖iteratedFDeriv ℝ m f z‖
      ≤ ⨆ w, ‖iteratedFDeriv ℝ ((⟨m, by omega⟩ : Fin 4) : ℕ) f w‖ := le_ciSup hb z
    _ ≤ c3Norm f := le_ciSup hb' (⟨m, by omega⟩ : Fin 4)

/-- A derivative of the sine series of order at most `3` is bounded by `c3Norm` on the closed
cube: it equals the derivative of `f` in the open cube, and both sides are continuous. -/
theorem norm_iteratedFDeriv_sineSum_le_of_mem_closedCube (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) {m : ℕ} (hm : m ≤ 3) {z : Euc d}
    (hz : z ∈ closedCube d) : ‖iteratedFDeriv ℝ m (sineSum f) z‖ ≤ c3Norm f := by
  have hcl : IsClosed {w : Euc d | ‖iteratedFDeriv ℝ m (sineSum f) w‖ ≤ c3Norm f} :=
    isClosed_le ((contDiff_sineSum hd f hf).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).norm continuous_const
  have hsub : unitCube d ⊆ {w : Euc d | ‖iteratedFDeriv ℝ m (sineSum f) w‖ ≤ c3Norm f} :=
    fun w hw => by
      have heq : sineSum f =ᶠ[nhds w] f :=
        Filter.eventually_of_mem (isOpen_unitCube.mem_nhds hw)
          fun y hy => sineSum_eq hd f hf y hy
      have h1 := (heq.iteratedFDeriv ℝ m).eq_of_nhds
      show ‖iteratedFDeriv ℝ m (sineSum f) w‖ ≤ c3Norm f
      rw [h1]
      exact norm_iteratedFDeriv_le_c3Norm hf hm w
  exact closure_minimal hsub hcl (closedCube_subset_closure_unitCube hz)

/-- **The sine series of a test function on the whole space**: for a test function `f` of the unit
cube and `D > 0`, the sine series `F = sineSum f` of `f` is smooth on `ℝ^d`, `−DΔu = F` on `ℝ^d`
for `u = (−DΔ_Q)⁻¹ f`, and every
derivative of `F` of order at most `3` is bounded by `c3Norm f`: each sine mode is odd about every
integer in each coordinate, so `F` is the odd `2`-periodic extension of `f`, and reflections are
isometries. -/
theorem sineSum_spec (hd : 1 ≤ d) (D : ℝ) (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) :
    (∀ k : ℕ, ContDiff ℝ k (sineSum f)) ∧
      (∀ z, -(D * laplacianSum (dirichletInverse D f) z) = sineSum f z) ∧
      ∀ m : ℕ, m ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ m (sineSum f) z‖ ≤ c3Norm f := by
  refine ⟨fun k => (contDiff_sineSum hd f hf).of_le (by exact_mod_cast le_top),
    fun z => neg_mul_laplacianSum_dirichletInverse hd hD f hf z, fun m hm z => ?_⟩
  obtain ⟨σ, n, hmem⟩ := exists_flipIso_add_mem_closedCube z
  rw [← norm_iteratedFDeriv_sineSum_flipIso_add hd f hf σ n m z]
  exact norm_iteratedFDeriv_sineSum_le_of_mem_closedCube hd f hf hm hmem

end LatticeProb.Analysis.Schauder

end
