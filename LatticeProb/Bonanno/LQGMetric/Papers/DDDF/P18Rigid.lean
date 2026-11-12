/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Rigid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Law
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Invariance of the law of `ψ_{0,n}` under rigid motions (for DDDF Prop 18, Step 1)

DDDF (arXiv:1904.08021, `tightness.tex` l. 900–905, proof of Prop 18, Step 1) use the four
`3 × 1` rectangles around a unit square, two of them vertical: their crossing lengths have the
law of `L^{(n)}_{3,1}(ψ)`, which is the invariance of the law of `ψ` under rigid motions
`z ↦ u z + c` (`|u| = 1`), implicit in DDDF (the kernel `p_{t/2}(x − y) Φ((x − y)/σ_t)` is
radial). Generalizes `map_psiMN_add` (P16Law.lean); same proof with the measure-preserving
map `(t, y) ↦ (t, u⁻¹(y − c))` of `ℝ × ℂ` (rotations preserve Lebesgue measure,
`LinearIsometryEquiv.measurePreserving`). Own routine step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the space motion `(t, y) ↦ (t, u⁻¹ (y − c))` of `ℝ × ℂ` -/
def spMotion (u : Circle) (c : ℂ) (p : ℝ × ℂ) : ℝ × ℂ := (p.1, rotation u⁻¹ (p.2 - c))

lemma measurePreserving_spMotion (u : Circle) (c : ℂ) :
    MeasurePreserving (spMotion u c) (volume : Measure (ℝ × ℂ)) volume := by
  have h1 : MeasurePreserving (fun y : ℂ => rotation u⁻¹ (y - c)) volume volume :=
    (LinearIsometryEquiv.measurePreserving (rotation u⁻¹)).comp
      (measurePreserving_sub_right (volume : Measure ℂ) c)
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod h1

/-- the motion as a linear isometry of `L²(ℝ × ℂ)` -/
def motionL2 (u : Circle) (c : ℂ) : WNSpace →ₗᵢ[ℝ] WNSpace :=
  Lp.compMeasurePreservingₗᵢ ℝ (spMotion u c) (measurePreserving_spMotion u c)

lemma norm_motion_sub (u : Circle) (x c : ℂ) (p : ℝ × ℂ) :
    ‖x - (spMotion u c p).2‖ = ‖(u : ℂ) * x + c - p.2‖ := by
  have hu : (u : ℂ) ≠ 0 := by
    intro h; have := Circle.norm_coe u; rw [h, norm_zero] at this; exact zero_ne_one this
  have e : x - rotation u⁻¹ (p.2 - c) = (u : ℂ)⁻¹ * ((u : ℂ) * x + c - p.2) := by
    rw [rotation_apply, Circle.coe_inv]; field_simp; ring
  simp only [spMotion]
  rw [e, norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul]

lemma phiKernel_motion (a b : ℝ) (u : Circle) (x c : ℂ) (p : ℝ × ℂ) :
    phiKernel a b ((u : ℂ) * x + c) p = phiKernel a b x (spMotion u c p) := by
  have hn' : ‖(u : ℂ) * x + c - p.2‖ = ‖x - (spMotion u c p).2‖ :=
    (norm_motion_sub u x c p).symm
  simp only [phiKernel, heatKernel, indicator, Set.mem_prod, hn', Set.mem_univ, and_true]
  rfl

lemma psiKernel_motion (Q : PsiParams) (a b : ℝ) (u : Circle) (x c : ℂ) (p : ℝ × ℂ) :
    Q.psiKernel a b ((u : ℂ) * x + c) p = Q.psiKernel a b x (spMotion u c p) := by
  have hn := norm_motion_sub u x c p
  have ht : Q.trunc ((u : ℂ) * x + c) p = Q.trunc x (spMotion u c p) := by
    refine Q.cut.radial _ _ ?_
    simp only [spMotion] at hn ⊢
    rw [norm_smul, norm_smul, hn]
  rw [PsiParams.psiKernel, PsiParams.psiKernel, ht, phiKernel_motion]

lemma phiKernelL2_motion {a : ℝ} (ha : 0 < a) (b : ℝ) (u : Circle) (x c : ℂ) :
    phiKernelL2 a b ((u : ℂ) * x + c) = motionL2 u c (phiKernelL2 a b x) := by
  have hmp := measurePreserving_spMotion u c
  refine Lp.ext ?_
  have h1 := coeFn_phiKernelL2 a b ha ((u : ℂ) * x + c)
  have h2 : (motionL2 u c (phiKernelL2 a b x) : ℝ × ℂ → ℝ) =ᵐ[volume]
      (phiKernelL2 a b x : ℝ × ℂ → ℝ) ∘ spMotion u c :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h3 : (phiKernelL2 a b x : ℝ × ℂ → ℝ) ∘ spMotion u c =ᵐ[volume]
      phiKernel a b x ∘ spMotion u c :=
    hmp.quasiMeasurePreserving.ae_eq_comp (coeFn_phiKernelL2 a b ha x)
  filter_upwards [h1, h2, h3] with p e1 e2 e3
  rw [e1, e2, e3, Function.comp_apply, phiKernel_motion]

/-- a white noise composed with a linear isometry of `L²` is a white noise -/
lemma isWhiteNoise_isometry {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (T : WNSpace →ₗᵢ[ℝ] WNSpace) : IsWhiteNoise P (fun f => W (T f)) := by
  refine ⟨fun f => hW.measurable _, fun {ι} _ f c => ?_⟩
  have h := hW.hasLaw (fun i => T (f i)) c
  have e : ‖∑ i, c i • T (f i)‖ = ‖∑ i, c i • f i‖ := by
    rw [← T.norm_map (∑ i, c i • f i), map_sum]; simp only [map_smul]
  rw [e] at h; exact h

omit [MeasurableSpace Ω] in
/-- `φ_{a,b}(u x + c)` for the noise `W` is `φ_{a,b}(x)` for the moved noise `W ∘ T_{u,c}` -/
lemma phi_motion (W : WNSpace → Ω → ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) (u : Circle) (x c : ℂ) :
    phi W a b ((u : ℂ) * x + c) = phi (fun f => W (motionL2 u c f)) a b x := by
  funext ω; simp only [phi, phiKernelL2_motion ha]

lemma psiKernelL2_motion (Q : PsiParams) {a : ℝ} (ha : 0 < a) (b : ℝ) (u : Circle) (x c : ℂ) :
    Q.psiKernelL2 a b ((u : ℂ) * x + c) = motionL2 u c (Q.psiKernelL2 a b x) := by
  have hmp := measurePreserving_spMotion u c
  refine Lp.ext ?_
  have h1 := Q.coeFn_psiKernelL2 a b ha ((u : ℂ) * x + c)
  have h2 : (motionL2 u c (Q.psiKernelL2 a b x) : ℝ × ℂ → ℝ) =ᵐ[volume]
      (Q.psiKernelL2 a b x : ℝ × ℂ → ℝ) ∘ spMotion u c :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h3 : (Q.psiKernelL2 a b x : ℝ × ℂ → ℝ) ∘ spMotion u c =ᵐ[volume]
      Q.psiKernel a b x ∘ spMotion u c :=
    hmp.quasiMeasurePreserving.ae_eq_comp (Q.coeFn_psiKernelL2 a b ha x)
  filter_upwards [h1, h2, h3] with p e1 e2 e3
  rw [e1, e2, e3, Function.comp_apply, psiKernel_motion]

/-- **Invariance of the law of `ψ_{0,n}` under rigid motions** `x ↦ u x + c`, `|u| = 1`. -/
theorem map_psiMN_motion {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (n : ℕ)
    (u : Circle) (c : ℂ) :
    P.map (fun ω => (fun x => psiMN Q W P 0 n ((u : ℂ) * x + c) ω)) =
      P.map (fun ω => (psiMN Q W P 0 n · ω)) := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  refine (map_ker_eq hW (Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0)) (motionL2 u c)
    (Y := psiMN Q W P 0 n) (Y₂ := fun x => psiMN Q W P 0 n ((u : ℂ) * x + c)) hψ.meas
    (fun x => hψ.meas _) (fun x => hψ.ae_eq x) (fun x => ?_)).symm
  refine (hψ.ae_eq ((u : ℂ) * x + c)).trans (Filter.Eventually.of_forall fun ω => ?_)
  simp only [psi, psiKernelL2_motion Q ha]

end DDDF
end LQGMetric
