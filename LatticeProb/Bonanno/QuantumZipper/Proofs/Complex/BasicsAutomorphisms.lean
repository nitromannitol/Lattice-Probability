/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.BasicsAutomorphisms at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Automorphisms of the disk and of the half-plane (EXT-CA node A6)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.A, node **A6**.

* `exists_rotation_of_bijOn_ball`: a holomorphic bijection of `𝔻` fixing `0` is a rotation.
* `exists_diskMobius_of_bijOn_ball`: every holomorphic bijection of `𝔻` is `u · diskMobius a`.
* `exists_realMobius_of_bijOn_H`: every holomorphic bijection of `ℍ` is a real Möbius map
  `z ↦ (a z + b)/(c z + d)` with `ad - bc > 0`.
* `exists_mul_of_bijOn_H_of_tendsto`: an automorphism of `ℍ` with `χ z → 0` as `z → 0` and
  `χ z → ∞` as `z → ∞` (within `ℍ`) is `z ↦ a z`, `a > 0`.

Source: R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021),
Theorem 6.2 (ii), p. 399 (PDF p. 424): Schwarz's lemma for `f` and `f⁻¹` gives `|f z| = |z|`,
hence a rotation; the general case by composing with `f_{-a}`, `a = f⁻¹(0)`. Mathlib's Schwarz
lemma and its equality case (`Complex.norm_le_norm_of_mapsTo_ball`,
`Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'`) are used; holomorphy of `f⁻¹`
is `differentiableOn_univalentOPH_symm` (A2). The half-plane case transports through the Cayley
map (A1) (Ahlfors, *Complex Analysis*, 3rd ed. 1979, Ch. 4 §3.4, p. 136, Ex. 5-6); the real
coefficients come from writing the rotation factor as `μ / conj μ` (own elementary algebra).
-/

noncomputable section

open Set Metric Filter Topology Complex Bornology
open scoped ComplexConjugate

namespace QuantumZipper.CA

/-- A holomorphic bijection of the unit disk fixing `0` is a rotation
(Burckel, Thm 6.2 (ii), first step). -/
theorem exists_rotation_of_bijOn_ball {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hbij : BijOn f (ball 0 1) (ball 0 1)) (h0 : f 0 = 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ EqOn f (fun z => u * z) (ball 0 1) := by
  set B : Set ℂ := ball 0 1 with hB
  set e := univalentOPH isOpen_ball hf hbij.injOn with he
  have himg : f '' B = B := hbij.image_eq
  have hgd : DifferentiableOn ℂ e.symm B := by
    have := differentiableOn_univalentOPH_symm isOpen_ball hf hbij.injOn
    rwa [himg] at this
  have hgmaps : MapsTo e.symm B (closedBall 0 1) := by
    intro w hw
    have hw' : w ∈ e.target := by
      rw [he, univalentOPH_target, himg]; exact hw
    exact ball_subset_closedBall (e.map_target hw')
  have hg0 : e.symm 0 = 0 := by
    have := univalentOPH_symm_apply_apply isOpen_ball hf hbij.injOn (mem_ball_self one_pos)
    rwa [h0] at this
  have hfmaps : MapsTo f B (closedBall 0 1) := fun z hz => ball_subset_closedBall (hbij.mapsTo hz)
  have hnorm : ∀ z ∈ B, ‖f z‖ = ‖z‖ := by
    intro z hz
    refine le_antisymm (Complex.norm_le_norm_of_mapsTo_ball hf hfmaps h0
      (mem_ball_zero_iff.1 hz)) ?_
    have h := Complex.norm_le_norm_of_mapsTo_ball hgd hgmaps hg0
      (mem_ball_zero_iff.1 (hbij.mapsTo hz))
    rwa [univalentOPH_symm_apply_apply isOpen_ball hf hbij.injOn hz] at h
  have hhalf : (1 / 2 : ℂ) ∈ B := by
    rw [mem_ball_zero_iff]; norm_num
  have hslope : ‖dslope f 0 (1 / 2)‖ = 1 / 1 := by
    rw [dslope_of_ne _ (by norm_num), slope_def_module, h0, sub_zero, sub_zero, norm_smul,
      hnorm _ hhalf]
    norm_num
  have hmaps' : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by rw [h0]; exact hfmaps
  obtain ⟨C, hC, hEq⟩ :=
    Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hf hmaps' ⟨_, hhalf, hslope⟩
  refine ⟨C, by rw [hC]; norm_num, fun z hz => ?_⟩
  rw [hEq hz, h0]
  simp [mul_comm]

/-- The rotation `w ↦ (μ / conj μ) w` of the disk, conjugated by the Cayley map, is the real
Möbius map with matrix `[[α, β], [-β, α]]`, `μ = α + β i`. -/
theorem cayleyInv_rot_cayley {μ : ℂ} (hμ : μ ≠ 0) {z : ℂ} (hz : z ∈ H) :
    cayleyInv (μ / conj μ * cayley z) = realMobius μ.re μ.im (-μ.im) μ.re z := by
  set α := μ.re
  set β := μ.im
  have hμ' : μ = α + β * I := (re_add_im μ).symm
  have hc : conj μ = α - β * I := by rw [hμ']; simp [conj_ofReal, sub_eq_add_neg]
  have hcne : conj μ ≠ 0 := (map_ne_zero _).2 hμ
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
  have hdet : 0 < α * α - β * -β := by
    have : 0 < normSq μ := normSq_pos.2 hμ
    rw [normSq_apply] at this; linarith
  have hden : ((-β : ℝ) : ℂ) * z + α ≠ 0 := realMobius_denom_ne_zero hdet hz
  have hden' : (α : ℂ) - β * z ≠ 0 := by
    intro h; apply hden; push_cast; linear_combination h
  have hden2 : conj μ * (z + I) - μ * (z - I) = 2 * I * (α - β * z) := by
    rw [hc, hμ']; ring
  have hnum2 : conj μ * (z + I) + μ * (z - I) = 2 * (α * z + β) := by
    rw [hc, hμ']; linear_combination (-2 * (β : ℂ)) * I_sq
  have hden2ne : conj μ * (z + I) - μ * (z - I) ≠ 0 := by
    rw [hden2]; exact mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hden'
  have h1w : 1 - μ / conj μ * cayley z ≠ 0 := by
    unfold cayley
    rw [show (1 : ℂ) - μ / conj μ * ((z - I) / (z + I)) =
      (conj μ * (z + I) - μ * (z - I)) / (conj μ * (z + I)) by field_simp]
    exact div_ne_zero hden2ne (mul_ne_zero hcne hzI)
  have e1 : cayleyInv (μ / conj μ * cayley z) =
      I * (conj μ * (z + I) + μ * (z - I)) / (conj μ * (z + I) - μ * (z - I)) := by
    unfold cayleyInv
    rw [div_eq_div_iff h1w hden2ne]
    unfold cayley
    field_simp
  rw [e1, hnum2, hden2, realMobius]
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hden') hden]
  push_cast
  ring

/-- Every holomorphic bijection of `ℍ` is a real Möbius map `z ↦ (a z + b)/(c z + d)` with
`ad - bc > 0` (Burckel Thm 6.2 (ii) transported by the Cayley map). -/
theorem exists_realMobius_of_bijOn_H {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f H)
    (hbij : BijOn f H H) :
    ∃ a b c d : ℝ, 0 < a * d - b * c ∧ EqOn f (realMobius a b c d) H := by
  have hIH : I ∈ H := by show (0 : ℝ) < I.im; simp
  set p := (f I).re with hp
  set q := (f I).im with hq
  have hq0 : 0 < q := hbij.mapsTo hIH
  set T : ℂ → ℂ := fun w => ((q⁻¹ : ℝ) : ℂ) * w + ((-p / q : ℝ) : ℂ) with hT
  have hTbij : BijOn T H H := bijOn_affine_H (inv_pos.2 hq0)
  have hTI : T (f I) = I := by
    apply Complex.ext <;> simp [hT, ← hp, ← hq] <;> field_simp <;> ring
  set φ : ℂ → ℂ := cayley ∘ T ∘ f ∘ cayleyInv with hφ
  have hB1 : ∀ w ∈ ball (0 : ℂ) 1, w ≠ 1 := by
    intro w hw h; subst h; simp at hw
  have hCinv : BijOn cayleyInv (ball 0 1) H := by
    refine ⟨fun w hw => cayleyInv_mem_H hw, fun w hw w' hw' h => ?_, fun z hz => ?_⟩
    · rw [← cayley_cayleyInv (hB1 w hw), h, cayley_cayleyInv (hB1 w' hw')]
    · exact ⟨cayley z, cayley_mem_ball hz,
        cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hz))⟩
  have hφbij : BijOn φ (ball 0 1) (ball 0 1) :=
    bijOn_cayley_H.comp (hTbij.comp (hbij.comp hCinv))
  have hφd : DifferentiableOn ℂ φ (ball 0 1) := by
    intro w hw
    have h1 : cayleyInv w ∈ H := cayleyInv_mem_H hw
    have h2 : f (cayleyInv w) ∈ H := hbij.mapsTo h1
    have h3 : T (f (cayleyInv w)) ∈ H := hTbij.mapsTo h2
    have d0 : DifferentiableAt ℂ cayleyInv w := differentiableAt_cayleyInv (hB1 w hw)
    have d1 : DifferentiableAt ℂ f (cayleyInv w) := hf.differentiableAt (isOpen_H.mem_nhds h1)
    have d2 : DifferentiableAt ℂ T (f (cayleyInv w)) := by rw [hT]; fun_prop
    have d3 : DifferentiableAt ℂ cayley (T (f (cayleyInv w))) :=
      differentiableAt_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt h3))
    exact (d3.comp w (d2.comp w (d1.comp w d0))).differentiableWithinAt
  have hφ0 : φ 0 = 0 := by
    have : cayleyInv 0 = I := by simp [cayleyInv]
    simp only [hφ, Function.comp_apply, this, hTI]
    simp [cayley]
  obtain ⟨u, hu, hEq⟩ := exists_rotation_of_bijOn_ball hφd hφbij hφ0
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_eq_mul_self u
  have hν1 : ‖ν‖ = 1 := by
    have : ‖ν‖ * ‖ν‖ = 1 := by rw [← norm_mul, ← hν, hu]
    nlinarith [norm_nonneg ν]
  have hν0 : ν ≠ 0 := by intro h; rw [h, norm_zero] at hν1; exact zero_ne_one hν1
  have hconj : conj ν = ν⁻¹ := by
    rw [inv_def, normSq_eq_norm_sq, hν1]; simp
  have hu' : u = ν / conj ν := by rw [hν, hconj, div_inv_eq_mul]
  set α := ν.re
  set β := ν.im
  refine ⟨q * α - p * β, q * β + p * α, -β, α, ?_, fun z hz => ?_⟩
  · have : α * α + β * β = 1 := by
      have := hν1; rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, ← normSq_eq_norm_sq,
        normSq_apply] at this; exact this
    nlinarith
  · have hcz : cayley z ∈ ball (0 : ℂ) 1 := cayley_mem_ball hz
    have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
    have h1 := hEq hcz
    simp only [hφ, Function.comp_apply, cayleyInv_cayley hzI] at h1
    have hTf : T (f z) ∈ H := hTbij.mapsTo (hbij.mapsTo hz)
    have h2 := congrArg cayleyInv h1
    rw [cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hTf)), hu',
      cayleyInv_rot_cayley hν0 hz] at h2
    have hdet : 0 < α * α - β * -β := by
      have : 0 < normSq ν := normSq_pos.2 hν0
      rw [normSq_apply] at this; linarith
    have hden : ((-β : ℝ) : ℂ) * z + α ≠ 0 := realMobius_denom_ne_zero hdet hz
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    simp only [hT, realMobius] at h2 ⊢
    rw [eq_div_iff hden] at h2 ⊢
    push_cast at h2 ⊢
    field_simp at h2
    linear_combination h2

end QuantumZipper.CA
