import LatticeProb.Analysis.Elliptic.Dirichlet
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Traces of Hölder jets on a half-space

Finite coordinate Hölder norms give continuous boundary traces for the value,
first derivatives, and second derivatives of a twice differentiable function.
-/

namespace LatticeProb.Elliptic.HolderExtension

open Set Filter LatticeProb.Euclidean.Lattice
open scoped Topology ENNReal NNReal ContDiff BigOperators

noncomputable section

abbrev E (d : ℕ) := Fin d → ℝ

/-- The open coordinate half-space. -/
def halfSpace {d : ℕ} (i : Fin d) : Set (E d) := {x | 0 < x i}

private theorem continuous_extension {d : ℕ} {S : Set (E d)} {f : E d → ℝ}
    (hf : UniformContinuousOn f S) :
    ∃ g : E d → ℝ, ContinuousOn g (closure S) ∧ EqOn g f S := by
  have hlim : ∀ x ∈ closure S, ∃ y, Tendsto f (𝓝[S] x) (𝓝 y) := by
    intro x hx
    have : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    have : NeBot (𝓝 x ⊓ 𝓟 S) := mem_closure_iff_nhdsWithin_neBot.mp hx
    exact cauchy_map_iff_exists_tendsto.mp
      ((cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hf inf_le_right)
  exact ⟨extendFrom S f, continuousOn_extendFrom (Subset.refl _) hlim,
    extendFrom_extends hf.continuousOn⟩

private theorem radius_le {d : ℕ} (x : E d) :
    radius x ≤ ‖(EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin d)).symm.toContinuousLinearMap‖ * ‖x‖ := by
  rw [radius_norm]
  exact ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin d)).symm.toContinuousLinearMap).le_opNorm x

private theorem uniform_of_holder {d : ℕ} {σ : ℝ} {S : Set (E d)} {f : E d → ℝ}
    (hσ : 0 < σ) (hf : c0HolderNorm σ S f < ⊤) : UniformContinuousOn f S := by
  let C := ‖(EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin d)).symm.toContinuousLinearMap‖
  let H := (holderSeminorm σ S f).toReal * C ^ σ
  have hH : 0 ≤ H := mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  have hh : HolderOnWith ⟨H, hH⟩ ⟨σ, hσ.le⟩ f S := by
    intro x hx y hy
    have h := abs_sub_le_holderSeminorm_toReal hf hx hy
    have hr := Real.rpow_le_rpow (radius_nonneg (x-y)) (radius_le (x-y)) hσ.le
    have hm := mul_le_mul_of_nonneg_left hr (ENNReal.toReal_nonneg (a := holderSeminorm σ S f))
    have hxyn : 0 ≤ ‖x-y‖ := norm_nonneg _
    have hxy : |f x - f y| ≤ H * ‖x-y‖ ^ σ := by
      calc
        _ ≤ (holderSeminorm σ S f).toReal * radius (x-y) ^ σ := h
        _ ≤ (holderSeminorm σ S f).toReal * (C * ‖x-y‖) ^ σ := hm
        _ = H * ‖x-y‖ ^ σ := by rw [Real.mul_rpow (norm_nonneg _) hxyn]; ring
    have he := ENNReal.ofReal_le_ofReal hxy
    change edist (f x) (f y) ≤ (↑(NNReal.mk H hH) : ℝ≥0∞) * edist x y ^ σ
    simpa only [edist_dist, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, ENNReal.ofReal_mul hH,
      ← ENNReal.ofReal_rpow_of_nonneg hxyn hσ.le,
      ENNReal.ofReal_eq_coe_nnreal hH, NNReal.coe_mk, NNReal.coe_mk] using he
  exact hh.uniformContinuousOn hσ

private theorem norm_linear_le_sum {d : ℕ} (L : E d →L[ℝ] ℝ) (x : E d) :
    ‖L x‖ ≤ (∑ j, ‖L (Pi.single j 1)‖) * ‖x‖ := by
  have hx : x = ∑ j : Fin d, (x j) • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    ‖L x‖ = ‖∑ j : Fin d, L ((x j) • Pi.single j (1 : ℝ))‖ := by
      congr 1
      exact (congrArg L hx).trans (map_sum L _ _)
    _ ≤ ∑ j : Fin d, ‖L ((x j) • Pi.single j (1 : ℝ))‖ := by
      let F : Fin d → ℝ := fun j => L ((x j) • Pi.single j 1)
      exact norm_sum_le Finset.univ F
    _ ≤ ∑ j : Fin d, ‖L (Pi.single j (1 : ℝ))‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem uniform_of_bounded_partials {d : ℕ} {S : Set (E d)} {f : E d → ℝ}
    (hconv : Convex ℝ S) (hdf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hb : ∀ j, supNorm S (partialDeriv j f) < ⊤) : UniformContinuousOn f S := by
  let B : ℝ := ∑ j, (supNorm S (partialDeriv j f)).toReal
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hbound (x : E d) (hx : x ∈ S) : ‖fderiv ℝ f x‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    refine (norm_linear_le_sum (fderiv ℝ f x) v).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    simpa only [partialDeriv, Real.norm_eq_abs] using
      (abs_le_supNorm_toReal (hb j) hx)
  have hlip : LipschitzOnWith ⟨B, hB⟩ f S := by
    apply hconv.lipschitzOnWith_of_nnnorm_fderiv_le hdf
    intro x hx
    exact hbound x hx
  exact hlip.uniformContinuousOn


/-- The value and the first two coordinate jets extend continuously to the closed half-space. -/
theorem halfSpace_jet_traces {d : ℕ} (i : Fin d) {σ : ℝ}
    (hσ : 0 < σ) (_hσ' : σ < 1) (u : E d → ℝ)
    (hu : ContDiffOn ℝ 2 u (halfSpace i))
    (hn : c2HolderNorm σ (halfSpace i) u < ⊤) :
    ∃ f : E d → ℝ, ∃ g : Fin d → E d → ℝ,
      ∃ h : Fin d → Fin d → E d → ℝ,
        ContinuousOn f (closure (halfSpace i)) ∧
        (∀ j, ContinuousOn (g j) (closure (halfSpace i))) ∧
        (∀ j k, ContinuousOn (h j k) (closure (halfSpace i))) ∧
        Set.EqOn f u (halfSpace i) ∧
        (∀ j, Set.EqOn (g j) (partialDeriv j u) (halfSpace i)) ∧
        (∀ j k, Set.EqOn (h j k) (secondPartial j k u) (halfSpace i)) := by
  have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
  have hconv : Convex ℝ (halfSpace i) := by
    change Convex ℝ ((LinearMap.proj i : E d →ₗ[ℝ] ℝ) ⁻¹' Set.Ioi 0)
    exact (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.proj i : E d →ₗ[ℝ] ℝ)
  have hn' := hn
  simp only [c2HolderNorm, ENNReal.add_lt_top, ENNReal.sum_lt_top,
    Finset.mem_univ, true_implies] at hn'
  have hdf : ∀ x ∈ halfSpace i, DifferentiableAt ℝ u x := by
    intro x hx
    exact (hu.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by norm_num)
  have hdu (j : Fin d) : ContDiffOn ℝ 1 (partialDeriv j u) (halfSpace i) := by
    exact (hu.fderiv_of_isOpen hopen (by norm_num)).clm_apply contDiffOn_const
  have hsecond (j k : Fin d) (x : E d) (hx : x ∈ halfSpace i) :
      secondPartial j k u x = partialDeriv j (partialDeriv k u) x := by
    have hlocal := hu.contDiffAt (hopen.mem_nhds hx)
    have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
      (hlocal.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    simp only [secondPartial, partialDeriv, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    change ((fderiv ℝ (fderiv ℝ u) x) (Pi.single j 1)) (Pi.single k 1) =
      (fderiv ℝ (fun y => (fderiv ℝ u y) (Pi.single k 1)) x) (Pi.single j 1)
    rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single k 1))]
    simp
  have huuc : UniformContinuousOn u (halfSpace i) :=
    uniform_of_bounded_partials hconv hdf hn'.1.1.2
  have hguc (k : Fin d) : UniformContinuousOn (partialDeriv k u) (halfSpace i) := by
    apply uniform_of_bounded_partials hconv
    · intro x hx
      exact ((hdu k).contDiffAt (hopen.mem_nhds hx)).differentiableAt (by norm_num)
    · intro j
      have heq : supNorm (halfSpace i) (partialDeriv j (partialDeriv k u)) =
          supNorm (halfSpace i) (secondPartial j k u) := by
        unfold supNorm
        apply iSup_congr
        intro x
        apply iSup_congr
        intro hx
        rw [hsecond j k x hx]
      rw [heq]
      exact hn'.1.2 j k
  have hhuc (j k : Fin d) : UniformContinuousOn (secondPartial j k u) (halfSpace i) := by
    apply uniform_of_holder hσ
    exact ENNReal.add_lt_top.mpr ⟨hn'.1.2 j k, hn'.2 j k⟩
  obtain ⟨f, hf, hfeq⟩ := continuous_extension huuc
  choose g hg hgeq using fun j => continuous_extension (hguc j)
  choose h hh hheq using fun j k => continuous_extension (hhuc j k)
  exact ⟨f, g, h, hf, hg, hh, hfeq, hgeq, hheq⟩

end
end LatticeProb.Elliptic.HolderExtension
