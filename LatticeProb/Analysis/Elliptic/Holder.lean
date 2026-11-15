import LatticeProb.Euclidean.Lattice

/-!
# Euclidean Hölder norms

Scalar Hölder quotients use the Euclidean radius on the coordinate carrier. The extended
nonnegative real norms record finiteness explicitly before passage to real constants.
-/

namespace LatticeProb.Elliptic

open LatticeProb.Euclidean.Lattice
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- The supremum of the absolute value on `S`, with infinity allowed. -/
def supNorm (S : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ S, ENNReal.ofReal |f x|

/-- The scalar Hölder seminorm with Euclidean distance and exponent `σ`. -/
def holderSeminorm (σ : ℝ) (S : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ S, ⨆ y ∈ S, ⨆ (_ : x ≠ y),
    ENNReal.ofReal (|f x - f y| / radius (x - y) ^ σ)

/-- The sum of the supremum norm and the Euclidean Hölder seminorm. -/
def c0HolderNorm (σ : ℝ) (S : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  supNorm S f + holderSeminorm σ S f

/-- The coordinate derivative in the direction of the `i`th standard basis vector. -/
def partialDeriv (i : Fin d) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The second coordinate derivative, evaluated using the iterated Fréchet derivative. -/
def secondPartial (i j : Fin d) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single j 1]

/-- The coordinate trace of the Hessian, giving the Euclidean Laplacian. -/
def laplacian (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, secondPartial i i f x

/-- The coordinate `C^{2,σ}` norm, summing all first and second coordinate derivatives. -/
def c2HolderNorm (σ : ℝ) (S : Set (Fin d → ℝ))
    (u : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  supNorm S u + ∑ i, supNorm S (partialDeriv i u) +
    ∑ i, ∑ j, supNorm S (secondPartial i j u) +
    ∑ i, ∑ j, holderSeminorm σ S (secondPartial i j u)

/-- Point evaluation is bounded by the real supremum norm whenever that norm is finite. -/
theorem abs_le_supNorm_toReal {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (h : supNorm S f < ⊤) {x : Fin d → ℝ} (hx : x ∈ S) :
    |f x| ≤ (supNorm S f).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal h.ne).mp
  exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

/-- A finite Hölder norm bounds every Euclidean Hölder increment, including the diagonal. -/
theorem abs_sub_le_holderSeminorm_toReal {σ : ℝ} {S : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (h : c0HolderNorm σ S f < ⊤)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |f x - f y| ≤ (holderSeminorm σ S f).toReal * radius (x - y) ^ σ := by
  by_cases hxy : x = y
  · subst y
    simpa only [sub_self, abs_zero] using
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (radius_nonneg _) _)
  have hr : 0 < radius (x - y) ^ σ :=
    Real.rpow_pos_of_pos (radius_pos (sub_ne_zero.mpr hxy)) _
  have hfinite : holderSeminorm σ S f < ⊤ :=
    lt_of_le_of_lt (le_add_self) h
  apply (div_le_iff₀ hr).mp
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).mp
  exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y
    (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl))))

/-- A finite `C^{0,σ}` norm also bounds point evaluations by its supremum component. -/
theorem abs_le_supNorm_toReal_of_c0HolderNorm_lt_top {σ : ℝ}
    {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (h : c0HolderNorm σ S f < ⊤) {x : Fin d → ℝ} (hx : x ∈ S) :
    |f x| ≤ (supNorm S f).toReal :=
  abs_le_supNorm_toReal (lt_of_le_of_lt le_self_add h) hx

/-- A uniform real bound gives a finite supremum norm. -/
theorem supNorm_lt_top_of_bound {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (C : ℝ) (h : ∀ x ∈ S, |f x| ≤ C) : supNorm S f < ⊤ := by
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  exact iSup_le fun x => iSup_le fun hx => ENNReal.ofReal_le_ofReal (h x hx)

/-- A continuous scalar function has finite supremum norm on a bounded set. -/
theorem supNorm_lt_top_of_continuous {S : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (hS : Bornology.IsBounded S) (hf : Continuous f) :
    supNorm S f < ⊤ := by
  obtain ⟨C, hC⟩ := hS.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact supNorm_lt_top_of_bound C fun x hx =>
    by simpa only [Real.norm_eq_abs] using hC x (subset_closure hx)

/-- A uniform bound on the Euclidean Hölder quotient gives a finite seminorm. -/
theorem holderSeminorm_lt_top_of_bound {σ : ℝ} {S : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (C : ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |f x - f y| / radius (x - y) ^ σ ≤ C) : holderSeminorm σ S f < ⊤ := by
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  exact iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => ENNReal.ofReal_le_ofReal (h x hx y hy hxy)

/-- Constant functions have zero Hölder seminorm on every set. -/
theorem holderSeminorm_const (σ : ℝ) (S : Set (Fin d → ℝ)) (c : ℝ) :
    holderSeminorm σ S (fun _ => c) = 0 := by
  apply le_antisymm _ bot_le
  refine iSup_le fun x => iSup_le fun _ => iSup_le fun y => iSup_le fun _ =>
    iSup_le fun _ => ?_
  simp only [sub_self, abs_zero, zero_div, ENNReal.ofReal_zero]
  exact le_rfl

end

end LatticeProb.Elliptic
