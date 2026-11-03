/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GreenFnSquare at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.GreenFn
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Green functions of convex domains in `ℍ`; the unit square (task P2-ZB, WP-14)

* `exists_isConformalOnto_H_of_convex` : a nonempty convex open `U ⊆ ℂ`, `U ≠ ℂ`, has a
  conformal map `m : U → ℍ` (QZ's Riemann mapping theorem `CA.RMT.riemann_mapping_of_hasHoloSqrt`
  — Ahlfors, *Complex Analysis*, Ch. 6 §1.1 Thm 1 — whose hypothesis holds by QZ
  `CA.RMT.hasHoloSqrt_of_unbounded_compl` since every complementary component of a convex set
  contains a ray; composed with the Cayley transform `CA.cayleyInv : 𝔻 → ℍ`, as in QZ
  `CA.Uniformizer.exists_conformal_H_leftComponent`);
* `zeroGFFTestCov_eq_green_of_convex` : for convex `U ⊆ ℍ` (squares, discs, rectangles inside
  `ℍ`) the covariance of the zero-boundary GFF is `∫∫ φ(x) ψ(y) G_ℍ(m x, m y)`, i.e. `U` has the
  Green function `G_U(x,y) = G_ℍ(m x, m y)`;
* `zeroGFFTestCov_openSquare_eq_green` : the case of the open unit square `(0,1)²` of §8.

The ray argument (a point `a ∉ U` and `c ∈ U` give the ray `c + t(a − c)`, `t ≥ 1`, in `ℂ ∖ U`)
is an own elementary argument.
-/

noncomputable section

open MeasureTheory TopologicalSpace Set Metric

namespace LQGMetric

open QuantumZipper QuantumZipper.K3

/-- every complementary component of a convex set with a point `c` is unbounded -/
lemma not_isBounded_connectedComponentIn_compl_of_convex {U : Set ℂ} (hU : Convex ℝ U)
    {c : ℂ} (hc : c ∈ U) {a : ℂ} (ha : a ∉ U) :
    ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a) := by
  set R : Set ℂ := (fun t : ℝ => c + t • (a - c)) '' Ici 1
  have hRc : IsPreconnected R := isPreconnected_Ici.image _ (by fun_prop)
  have haR : a ∈ R := ⟨1, mem_Ici.2 le_rfl, by simp⟩
  have hRsub : R ⊆ Uᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hy
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hmem := hU.add_smul_sub_mem hc hy (t := t⁻¹)
      ⟨inv_nonneg.2 ht0.le, inv_le_one_of_one_le₀ ht⟩
    have e : c + t⁻¹ • (c + t • (a - c) - c) = a := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, add_sub_cancel]
    exact ha (e ▸ hmem)
  have hsub := hRc.subset_connectedComponentIn haR hRsub
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hb.subset hsub)
  have hac : 0 < ‖a - c‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => ha (h ▸ hc))
  set t : ℝ := max 1 ((C + ‖c‖ + 1) / ‖a - c‖)
  have h1 := hC _ ⟨t, mem_Ici.2 (le_max_left _ _), rfl⟩
  have h2 : ‖t • (a - c)‖ ≤ ‖c + t • (a - c)‖ + ‖c‖ := by
    have := norm_sub_le (c + t • (a - c)) c
    rwa [add_sub_cancel_left] at this
  have ht0 : 0 ≤ t := le_trans zero_le_one (le_max_left _ _)
  rw [norm_smul, Real.norm_of_nonneg ht0] at h2
  have h3 : (C + ‖c‖ + 1) / ‖a - c‖ * ‖a - c‖ ≤ t * ‖a - c‖ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hac.le
  rw [div_mul_cancel₀ _ hac.ne'] at h3
  linarith

/-- **Conformal map onto `ℍ`** for a nonempty convex open proper subset of `ℂ`. -/
theorem exists_isConformalOnto_H_of_convex {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) (hU : U ≠ univ) : ∃ m : ℂ → ℂ, IsConformalOnto m U H := by
  obtain ⟨c, hc⟩ := hne
  have hsq := CA.RMT.hasHoloSqrt_of_unbounded_compl hUo hUc.isPreconnected
    fun a ha => not_isBounded_connectedComponentIn_compl_of_convex hUc hc ha
  obtain ⟨φ₀, hφb, hφd, -, -, -, -⟩ :=
    CA.RMT.riemann_mapping_of_hasHoloSqrt hUo hUc.isPreconnected ⟨c, hc⟩ hU hsq
  have hne1 : ∀ w ∈ ball (0 : ℂ) 1, w ≠ 1 := fun w hw h => by simp [h] at hw
  have hcay : BijOn CA.cayleyInv (ball (0 : ℂ) 1) H :=
    CA.bijOn_cayley_H.symm ⟨fun w hw => CA.cayley_cayleyInv (hne1 w hw),
      fun z hz => CA.cayleyInv_cayley (CA.add_I_ne_zero_of_im_nonneg (le_of_lt hz))⟩
  have hb := hcay.comp hφb
  have hd : DifferentiableOn ℂ (CA.cayleyInv ∘ φ₀) U :=
    (CA.differentiableOn_cayleyInv_closedBall.mono fun w hw =>
      ⟨ball_subset_closedBall hw, hne1 w hw⟩).comp hφd hφb.mapsTo
  exact ⟨CA.cayleyInv ∘ φ₀, ⟨hUo, hd, hb.injOn, hb.image_eq,
    fun z hz => CA.Koebe.deriv_ne_zero_of_injOn hUo hd hb.injOn hz⟩⟩

lemma convex_openSquare : Convex ℝ openSquare := by
  have h1 : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_gt Complex.reLm.isLinear 0
  have h2 : Convex ℝ {z : ℂ | z.re < 1} := convex_halfSpace_lt Complex.reLm.isLinear 1
  have h3 : Convex ℝ {z : ℂ | 0 < z.im} := convex_halfSpace_gt Complex.imLm.isLinear 0
  have h4 : Convex ℝ {z : ℂ | z.im < 1} := convex_halfSpace_lt Complex.imLm.isLinear 1
  exact h1.inter (h2.inter (h3.inter h4))

end LQGMetric
