/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18S4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18S3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18T5

/-!
# DG:1593–1595: `DGProp3_17SqRef` from `R17Unit` by scaling (task P2-DG105s, P-118d)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, DG:1593–1595 (as
DG:1774–1777: scale and translation invariance of the whole-plane GFF modulo additive constant).
Same affine map `A y = 2r y + c₀` as in S3P18S1; `K, U ⊆ t18Sq c r` are pulled back to
`A⁻¹K, A⁻¹U ⊆ 𝕊`, and every path of `p17SetDist` in `Ū` is the `A`-image of a path in
`closure (A⁻¹U) = A⁻¹ Ū` (`s17_scale`: `2r e^{ξa} D_φ(A⁻¹K, ∂A⁻¹U) ≤ D_Φ(K, ∂U)` when
`Φ ∘ A = φ + a`). The Gaussian constant `H_R(c₀) ≥ −(ζ/4ξ) log δ⁻¹` off probability `≤ 2δ`.

* **`dgProp3_17SqRef_of_unit : R17Unit → DGProp3_17SqRef`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint

/-- the affine map `A y = 2r y + c₀` -/
def s17A (c : ℂ) (r : ℝ) (y : ℂ) : ℂ := ((2 * r : ℝ) : ℂ) * y + s18c0 c r

lemma s17A_homeo (c : ℂ) {r : ℝ} (hr : 0 < r) : ∃ e : ℂ ≃ₜ ℂ, ⇑e = s17A c r := by
  have hne : ((2 * r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * r : ℝ) ≠ 0)
  refine ⟨(Homeomorph.mulLeft₀ _ hne).trans (Homeomorph.addRight (s18c0 c r)), ?_⟩
  ext y; simp [s17A]

lemma s17A_inv (c : ℂ) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    s17A c r (((1 / (2 * r) : ℝ) : ℂ) * x + -(((1 / (2 * r) : ℝ) : ℂ) * s18c0 c r)) = x := by
  have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [s17A]
  push_cast
  field_simp
  ring

/-- `A⁻¹ U ⊆ 𝕊` for `U ⊆ t18Sq c r` -/
lemma s17A_pre_sub {c : ℂ} {r : ℝ} (hr : 0 < r) {U : Set ℂ} (hUS : U ⊆ t18Sq c r) :
    s17A c r ⁻¹' U ⊆ closedUnitSquare := fun x hx => by
  obtain ⟨e, he⟩ := s17A_homeo c hr
  obtain ⟨z', hz', hA⟩ := s18_A_surj hr (hUS hx)
  have : z' = x := e.injective (by rw [he]; exact hA)
  exact this ▸ hz'

/-- **`p17SetDist` under `A`** -/
lemma s17_scale (ξ : ℝ) {c : ℂ} {r : ℝ} (hr : 0 < r) {Φ φ : ℂ → ℝ} {a : ℝ}
    (hφ : ∀ x, Φ (((2 * r : ℝ) : ℂ) * x + s18c0 c r) = φ x + a) (K U : Set ℂ) :
    ENNReal.ofReal (2 * r * Real.exp (ξ * a)) *
        p17SetDist ξ φ (s17A c r ⁻¹' K) (s17A c r ⁻¹' U) ≤ p17SetDist ξ Φ K U := by
  obtain ⟨e, he⟩ := s17A_homeo c hr
  have hcl : closure (s17A c r ⁻¹' U) = s17A c r ⁻¹' closure U := by
    rw [← he, e.preimage_closure]
  have hfr : frontier (s17A c r ⁻¹' U) = s17A c r ⁻¹' frontier U := by
    rw [← he, e.preimage_frontier]
  set k := ((1 / (2 * r) : ℝ) : ℂ)
  set c' := -(k * s18c0 c r)
  conv_rhs => rw [p17SetDist]
  refine le_iInf fun z => le_iInf fun hz => le_iInf fun w => le_iInf fun hw =>
    le_iInf fun q => ?_
  have hq' := DFGPS.L36.isDGPath_affine q.2 (1 / (2 * r)) c'
  have hS : (fun x => k * x + c') '' closure U ⊆ closure (s17A c r ⁻¹' U) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hcl, mem_preimage, s17A_inv c hr]; exact hy
  have hq'' : IsDGPath (closure (s17A c r ⁻¹' U)) (k * z + c') (k * w + c')
      (fun t => k * q.1 t + c') :=
    ⟨hq'.source, hq'.target, hq'.mapsTo.mono_right hS, hq'.continuousOn, hq'.piecewise_contDiff⟩
  have hz' : k * z + c' ∈ s17A c r ⁻¹' K := by rw [mem_preimage, s17A_inv c hr]; exact hz
  have hw' : k * w + c' ∈ frontier (s17A c r ⁻¹' U) := by
    rw [hfr, mem_preimage, s17A_inv c hr]; exact hw
  have hqeq : q.1 = fun t => ((2 * r : ℝ) : ℂ) * (k * q.1 t + c') + s18c0 c r := by
    funext t; exact (s17A_inv c hr (q.1 t)).symm
  have hlen := DFGPS.L36.lfppLength_affine (by positivity : 0 < 2 * r) (s18c0 c r) ξ a hφ
    (fun t => k * q.1 t + c')
  calc ENNReal.ofReal (2 * r * Real.exp (ξ * a)) *
        p17SetDist ξ φ (s17A c r ⁻¹' K) (s17A c r ⁻¹' U)
      ≤ ENNReal.ofReal (2 * r * Real.exp (ξ * a)) *
          ENNReal.ofReal (LQGDimension.lfppLength ξ φ fun t => k * q.1 t + c') := by
        gcongr
        exact iInf_le_of_le _ (iInf_le_of_le hz' (iInf_le_of_le _ (iInf_le_of_le hw'
          (iInf_le_of_le ⟨_, hq''⟩ le_rfl))))
    _ = ENNReal.ofReal (LQGDimension.lfppLength ξ Φ q.1) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← hlen, ← hqeq]

/-- `δ^{λ+ζ} ≤ m δ^{λ+ζ/2}` for `δ ≤ m^{2/ζ}` -/
lemma s17_absorb {m δ ζ lam : ℝ} (hm : 0 < m) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδm : δ ≤ m ^ (2 / ζ)) : δ ^ (lam + ζ) ≤ m * δ ^ (lam + ζ / 2) := by
  have h1 : δ ^ (ζ / 2) ≤ m := by
    calc δ ^ (ζ / 2) ≤ (m ^ (2 / ζ)) ^ (ζ / 2) := Real.rpow_le_rpow hδ.le hδm (by positivity)
      _ = m := by
          rw [← Real.rpow_mul hm.le, show 2 / ζ * (ζ / 2) = 1 by field_simp, Real.rpow_one]
  rw [show lam + ζ = ζ / 2 + (lam + ζ / 2) by ring, Real.rpow_add hδ]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hδ.le _)

end LQGMetric.DG
