/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HarmLocA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.Green
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepRad
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HarmonicPart
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of the harmonic part, analytic helpers (task P2-HARMLOC, part A)

* `integral_mul_laplacian_of_harmonic`: a harmonic `H` on an open `U` is weakly harmonic,
  `∫ H Δf = 0` for `f ∈ C²_c` with `supp f ⊆ U` (Green's identity: cut `H` off by a smooth `χ = 1`
  near `supp f`, then integrate by parts twice with QuantumZipper's F3,
  `K3.integral_gradInner_eq_neg_integral_mul_laplacian`). Own elementary proof (standard).
* `unitBump δ x`: the radial bump `radBump δ x` of `GM.SpatialIndepRad` normalized to `∫ = 1`;
  `integral_mul_unitBump`: `∫ g · unitBump δ x = g x` for `g` harmonic near `B̄(x, δ)` (mean value
  property, `GM.integral_mul_radial_of_harmonic`).
* `exists_unit_test`: a test function with `∫ = 1` supported in a given nonempty open set.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace Laplacian

namespace LQGMetric
namespace HarmLoc

open QuantumZipper QuantumZipper.K3

/-- **Weak harmonicity**: `∫ H Δf = 0` for `H` harmonic on an open `U ⊇ supp f`, `f ∈ C²_c`. -/
theorem integral_mul_laplacian_of_harmonic {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℝ}
    (hH : HarmonicOnNhd H U) {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) : ∫ x, H x * Δ f x = 0 := by
  obtain ⟨χ, hχd, -, hχc, hχU, hχ1⟩ := FrozenMart.exists_cutoff_of_isCompact hfc hU hfU
  set u : ℂ → ℝ := fun x => χ x * H x with hu_def
  have hu : ContDiff ℝ 2 u := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact (hχd.contDiffAt.of_le (by norm_num)).mul (hH x hx).1
    · have hx' : x ∉ tsupport χ := fun h' => hx (hχU h')
      have h0 : u =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
        simp [hu_def, hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  have huc : HasCompactSupport u := hχc.mul_right
  have e1 : ∫ x, H x * Δ f x = ∫ x, u x * Δ f x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have : χ x = 1 := (hχ1 x hx).self_of_nhds
      simp [hu_def, this]
    · simp [laplacian_eq_zero_of_notMem_tsupport hx]
  have e2 : ∫ x, u x * Δ f x = -∫ x, gradInner u f x := by
    rw [integral_gradInner_eq_neg_integral_mul_laplacian (hu.of_le (by norm_num)) hf hfc,
      neg_neg]
  have e3 : ∫ x, gradInner u f x = -∫ x, f x * Δ u x := by
    simp_rw [gradInner_comm_k3 u f]
    exact integral_gradInner_eq_neg_integral_mul_laplacian (hf.of_le (by norm_num)) hu huc
  have e4 : ∫ x, f x * Δ u x = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have hev : u =ᶠ[𝓝 x] H := by
        filter_upwards [hχ1 x hx] with y hy
        simp [hu_def, hy]
      have : Δ u x = 0 := by
        rw [(laplacian_congr_nhds hev).eq_of_nhds]
        exact (hH x (hfU hx)).2.self_of_nhds
      simp [this]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [e1, e2, e3, e4]; simp

/-- `∫ H · (−Δf/2π) = 0` for `H` harmonic on an open `U ⊇ supp f` -/
theorem integral_mul_cmTest_of_harmonic {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℝ}
    (hH : HarmonicOnNhd H U) (φ : TestC) (hφU : tsupport (φ : ℂ → ℝ) ⊆ U) :
    ∫ x, H x * cmTest φ x = 0 := by
  simp_rw [cmTest_apply]
  have e : (fun x => H x * (-(2 * Real.pi)⁻¹ * Δ (⇑φ) x)) =
      fun x => -(2 * Real.pi)⁻¹ * (H x * Δ (⇑φ) x) := funext fun x => by ring
  rw [e, integral_const_mul, integral_mul_laplacian_of_harmonic hU hH
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport hφU, mul_zero]

/-- the radial bump `radBump δ x` normalized to total mass `1` -/
def unitBump (δ : ℝ) (hδ : 0 < δ) (x : ℂ) : TestC :=
  (∫ y, GM.radProf δ y)⁻¹ • GM.radBump δ hδ.le x

lemma unitBump_apply (δ : ℝ) (hδ : 0 < δ) (x y : ℂ) :
    unitBump δ hδ x y = (∫ y, GM.radProf δ y)⁻¹ * GM.radProf δ (y - x) := rfl

lemma integral_unitBump (δ : ℝ) (hδ : 0 < δ) (x : ℂ) : ∫ y, unitBump δ hδ x y = 1 := by
  simp_rw [unitBump_apply]
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => GM.radProf δ y) x,
    inv_mul_cancel₀ (GM.integral_radProf_pos hδ).ne']

lemma tsupport_unitBump (δ : ℝ) (hδ : 0 < δ) (x : ℂ) :
    tsupport (unitBump δ hδ x : ℂ → ℝ) ⊆ closedBall x δ := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra hy'
  rw [mem_closedBall, dist_eq_norm, not_le] at hy'
  exact hy (by rw [unitBump_apply, GM.radProf_eq_zero hδ.le hy'.le, mul_zero])

/-- **mean value property**: `∫ g · unitBump δ x = g x` for `g` harmonic near `B̄(x, δ)` -/
theorem integral_mul_unitBump {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℝ} (hg : HarmonicOnNhd g V)
    {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hB : closedBall x δ ⊆ V) :
    ∫ y, g y * unitBump δ hδ x y = g x := by
  have hI := GM.integral_radProf_pos hδ
  have h2 : ∫ y, g y * GM.radProf δ (y - x) = ∫ y, g (x + y) * GM.radProf δ y := by
    rw [← integral_add_left_eq_self (fun y => g y * GM.radProf δ (y - x)) x]
    congr 1; funext y
    rw [add_sub_cancel_left]
  have hmv := GM.integral_mul_radial_of_harmonic hV hg hB (GM.contDiff_radProf δ).continuous
    (fun y hy => GM.radProf_eq_zero hδ.le hy.le) (GM.radProf_rot δ)
  simp_rw [unitBump_apply]
  have e : (fun y => g y * ((∫ y, GM.radProf δ y)⁻¹ * GM.radProf δ (y - x))) =
      fun y => (∫ y, GM.radProf δ y)⁻¹ * (g y * GM.radProf δ (y - x)) :=
    funext fun y => by ring
  rw [e, integral_const_mul, h2, hmv]
  field_simp

/-- a test function of mass `1` supported in a nonempty open set -/
theorem exists_unit_test {W : Set ℂ} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ W ∧ ∫ y, ψ y = 1 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW x hx
  refine ⟨unitBump (ε / 2) (by positivity) x, (tsupport_unitBump _ _ x).trans
    ((closedBall_subset_ball (by linarith)).trans hεW), integral_unitBump _ _ x⟩

end HarmLoc
end LQGMetric
