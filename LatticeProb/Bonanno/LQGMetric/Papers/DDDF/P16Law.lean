/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P16Law at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Push
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

/-!
# Translation invariance of the law of `ψ_{0,n}` (for DDDF Proposition 16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 836–841, proof of Prop 16 = `Prop:LowerTail`) compare
the crossings of `[0,1] × [0,3]` and `[2,3] × [0,3]` by `ψ`; that the second has the law of the
first is the translation invariance of `ψ` (implicit in DDDF). Here:
* `map_ker_eq`: versions of `x ↦ √π W(k x)` and `x ↦ √π W(T(k x))` (`T` a linear isometry of
  `L²(ℝ × ℂ)`) have the same law on `ℂ → ℝ` (finite-dimensional laws through characteristic
  functionals, as `map_phi_eq` in P10Law.lean);
* `psiKernelL2_add`: the kernel of `ψ_{a,b}(x + c)` is the space translate of that of `ψ_{a,b}(x)`;
* `map_psiMN_add`: the law of `x ↦ ψ_{0,n}(x + c)` is that of `ψ_{0,n}`;
* `crossLenIn_image_add`: crossing lengths of translated domains;
* `exists_set_crossLenIn`: crossing-length events of continuous fields are preimages of
  product-measurable sets of `ℂ → ℝ` (from the proof of `measure_crossLenIn_eq`).
Standard measure theory (own routine steps).
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

/-- The law of a linear functional of `(Y(x_i))_{i ∈ I}` for a version `Y` of `√π W(k ·)`. -/
lemma hasLaw_dual_ker {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (k : ℂ → WNSpace)
    (I : Finset ℂ) (L : StrongDual ℝ (I → ℝ)) {Y : ℂ → Ω → ℝ}
    (hY : ∀ x, Y x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (k x) ω) :
    HasLaw (fun ω => L (fun i : I => Y i ω)) (gaussianReal 0
      (‖∑ i : I, (Real.sqrt Real.pi * L (Pitt.unitVec i)) • k i‖ ^ 2).toNNReal) P := by
  classical
  refine (hW.hasLaw (fun i : I => k i)
    (fun i => Real.sqrt Real.pi * L (Pitt.unitVec i))).congr ?_
  have hall : ∀ᵐ ω ∂P, ∀ i : I, Y i ω = Real.sqrt Real.pi * W (k i) ω :=
    ae_all_iff.2 fun i => hY i
  filter_upwards [hall] with ω hω
  rw [Pitt.dual_apply_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hω i]; ring

/-- Equal finite-dimensional laws of versions of `√π W(k ·)` and `√π W(T(k ·))`. -/
lemma map_restrict_ker_eq {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (k : ℂ → WNSpace)
    (T : WNSpace →ₗᵢ[ℝ] WNSpace) {Y Y₂ : ℂ → Ω → ℝ}
    (hYm : ∀ x, Measurable (Y x)) (hY₂m : ∀ x, Measurable (Y₂ x))
    (hY : ∀ x, Y x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (k x) ω)
    (hY₂ : ∀ x, Y₂ x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (T (k x)) ω) (I : Finset ℂ) :
    P.map (fun ω => I.restrict (Y · ω)) = P.map (fun ω => I.restrict (Y₂ · ω)) := by
  have := hW.isProbabilityMeasure
  have hm : Measurable (fun ω => I.restrict (Y · ω)) := measurable_pi_iff.2 fun i => hYm i
  have hm₂ : Measurable (fun ω => I.restrict (Y₂ · ω)) := measurable_pi_iff.2 fun i => hY₂m i
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.continuous.measurable hm, Measure.map_map L.continuous.measurable hm₂]
  congr 1
  have h1 := (hasLaw_dual_ker hW k I L hY).map_eq
  have h2 := (hasLaw_dual_ker hW (fun x => T (k x)) I L hY₂).map_eq
  have e : ∑ i : I, (Real.sqrt Real.pi * L (Pitt.unitVec i)) • T (k i) =
      T (∑ i : I, (Real.sqrt Real.pi * L (Pitt.unitVec i)) • k i) := by
    simp [map_sum, map_smul]
  rw [e, T.norm_map] at h2
  exact h1.trans h2.symm

/-- Equal laws on `ℂ → ℝ` of versions of `√π W(k ·)` and `√π W(T(k ·))`. -/
theorem map_ker_eq {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (k : ℂ → WNSpace)
    (T : WNSpace →ₗᵢ[ℝ] WNSpace) {Y Y₂ : ℂ → Ω → ℝ}
    (hYm : ∀ x, Measurable (Y x)) (hY₂m : ∀ x, Measurable (Y₂ x))
    (hY : ∀ x, Y x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (k x) ω)
    (hY₂ : ∀ x, Y₂ x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (T (k x)) ω) :
    P.map (fun ω => (Y · ω)) = P.map (fun ω => (Y₂ · ω)) := by
  have := hW.isProbabilityMeasure
  have h1 := isProjectiveLimit_map (P := P) (X := Y) (measurable_pi_iff.2 hYm).aemeasurable
  have h2 := isProjectiveLimit_map (P := P) (X := Y₂) (measurable_pi_iff.2 hY₂m).aemeasurable
  have e : (fun I : Finset ℂ => P.map (fun ω => I.restrict (Y · ω))) =
      fun I => P.map (fun ω => I.restrict (Y₂ · ω)) :=
    funext fun I => map_restrict_ker_eq hW k T hYm hY₂m hY hY₂ I
  rw [e] at h1
  exact h1.unique h2

/-- the space translation `(t, y) ↦ (t, y - c)` of `ℝ × ℂ` -/
def spShift (c : ℂ) (p : ℝ × ℂ) : ℝ × ℂ := (p.1, p.2 - c)

lemma measurePreserving_spShift (c : ℂ) :
    MeasurePreserving (spShift c) (volume : Measure (ℝ × ℂ)) volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_sub_right (volume : Measure ℂ) c)
  exact h

/-- the translation as a linear isometry of `L²(ℝ × ℂ)` -/
def shiftL2 (c : ℂ) : WNSpace →ₗᵢ[ℝ] WNSpace :=
  Lp.compMeasurePreservingₗᵢ ℝ (spShift c) (measurePreserving_spShift c)

lemma psiKernel_add (Q : PsiParams) (a b : ℝ) (x c : ℂ) (p : ℝ × ℂ) :
    Q.psiKernel a b (x + c) p = Q.psiKernel a b x (spShift c p) := by
  have h1 : x - (p.2 - c) = x + c - p.2 := by ring
  simp [PsiParams.psiKernel, phiKernel, PsiParams.trunc, heatKernel, spShift, indicator,
    Set.mem_prod, h1]

/-- the kernel of `ψ_{a,b}(x + c)` is the translate of that of `ψ_{a,b}(x)` -/
lemma psiKernelL2_add (Q : PsiParams) {a : ℝ} (ha : 0 < a) (b : ℝ) (x c : ℂ) :
    Q.psiKernelL2 a b (x + c) = shiftL2 c (Q.psiKernelL2 a b x) := by
  have hmp := measurePreserving_spShift c
  refine Lp.ext ?_
  have h1 := Q.coeFn_psiKernelL2 a b ha (x + c)
  have h2 : (shiftL2 c (Q.psiKernelL2 a b x) : ℝ × ℂ → ℝ) =ᵐ[volume]
      (Q.psiKernelL2 a b x : ℝ × ℂ → ℝ) ∘ spShift c :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h3 : (Q.psiKernelL2 a b x : ℝ × ℂ → ℝ) ∘ spShift c =ᵐ[volume]
      Q.psiKernel a b x ∘ spShift c :=
    hmp.quasiMeasurePreserving.ae_eq_comp (Q.coeFn_psiKernelL2 a b ha x)
  filter_upwards [h1, h2, h3] with p e1 e2 e3
  rw [e1, e2, e3, Function.comp_apply, psiKernel_add]

/-- **Translation invariance of the law of `ψ_{0,n}`**. -/
theorem map_psiMN_add {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (n : ℕ)
    (c : ℂ) :
    P.map (fun ω => (fun x => psiMN Q W P 0 n (x + c) ω)) =
      P.map (fun ω => (psiMN Q W P 0 n · ω)) := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  refine (map_ker_eq hW (Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0)) (shiftL2 c)
    (Y := psiMN Q W P 0 n) (Y₂ := fun x => psiMN Q W P 0 n (x + c)) hψ.meas
    (fun x => hψ.meas _) (fun x => hψ.ae_eq x) (fun x => ?_)).symm
  refine (hψ.ae_eq (x + c)).trans (Filter.Eventually.of_forall fun ω => ?_)
  simp only [psi, psiKernelL2_add Q ha]

/-- crossing lengths of a translated domain -/
theorem crossLenIn_image_add (ξ : ℝ) (g : ℂ → ℝ) (K A B : Set ℂ) (c : ℂ) :
    crossLenIn ξ g ((· + c) '' K) ((· + c) '' A) ((· + c) '' B) =
      crossLenIn ξ (fun x => g (x + c)) K A B := by
  have hd : ∀ c' : ℂ, ∀ x ∈ (univ : Set ℂ), ‖deriv (· + c') x‖ ≤ 1 := fun c' x _ => by
    simp
  have hD : ∀ c' : ℂ, DifferentiableOn ℂ (· + c') univ := fun c' => by fun_prop
  refine le_antisymm ?_ ?_
  · have h := crossLenIn_image_le (ξ := ξ) (g := g) (K := K) (A := A) (B := B) isOpen_univ
      (subset_univ _) (hD c) one_pos (fun x hx => hd c x (mem_univ _))
    rw [ENNReal.ofReal_one, one_mul] at h
    exact h
  · have h := crossLenIn_image_le (ξ := ξ) (g := fun x => g (x + c))
      (K := (· + c) '' K) (A := (· + c) '' A) (B := (· + c) '' B) isOpen_univ
      (subset_univ _) (hD (-c)) one_pos (fun x hx => hd (-c) x (mem_univ _))
    have e : ∀ S : Set ℂ, (· + -c) '' ((· + c) '' S) = S := fun S => by
      rw [image_image]; simp
    have e2 : ((fun x => g (x + c)) ∘ (· + -c)) = g := funext fun x => by simp
    rw [e, e, e, e2, ENNReal.ofReal_one, one_mul] at h
    exact h

/-- crossing-length events of continuous fields are preimages of product-measurable sets -/
theorem exists_set_crossLenIn {ξ : ℝ} {K : Set ℂ} (hK : IsCompact K) (A B : Set ℂ)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    ∃ T : Set (ℂ → ℝ), MeasurableSet T ∧
      ∀ g : ℂ → ℝ, Continuous g → (crossLenIn ξ g K A B ∈ S ↔ g ∈ T) := by
  have hgm : Measurable fun f : C(ℂ, ℝ) => crossLenIn ξ (fun x => f x) K A B :=
    measurable_crossLenIn (Y := fun x (f : C(ℂ, ℝ)) => f x) hK (fun f => f.continuous)
      (fun x => ContinuousMap.measurable_eval x)
  have hE : MeasurableSet[MeasurableSpace.comap (fun f : C(ℂ, ℝ) => (f : ℂ → ℝ))
      MeasurableSpace.pi] {f : C(ℂ, ℝ) | crossLenIn ξ (fun x => f x) K A B ∈ S} := by
    rw [← measurableSpace_continuousMap_eq_comap]; exact hgm hS
  obtain ⟨T, hT, hTE⟩ := hE
  refine ⟨T, hT, fun g hg => ?_⟩
  have := congrArg (fun E => (⟨g, hg⟩ : C(ℂ, ℝ)) ∈ E) hTE
  simp only [mem_preimage, ContinuousMap.coe_mk, mem_ofPred_eq, eq_iff_iff] at this
  exact this.symm

end DDDF
end LQGMetric
