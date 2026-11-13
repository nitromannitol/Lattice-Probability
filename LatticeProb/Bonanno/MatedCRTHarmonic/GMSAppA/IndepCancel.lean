/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.IndepCancel at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Removing an independent Gaussian summand preserves independence

If `X + Y` is independent of `C`, the summand `Y` is Gaussian and independent of `(X, C)`, then `X` is independent of
`C` (the characteristic function of `Y` never vanishes, so it can be cancelled). We apply it to the Markov
decomposition `(h − h_1(0))|_𝔻 = (𝔥 − h_1(0)) + h̊` of a whole-plane GFF normalized on a circle enclosing `𝔻`:
`(h − h_1(0))|_𝔻` is independent of `h_1(0)` (Newton's theorem, `GMSAppA.indepFun_circleAvg_restrict_nested`) and
`h̊` is a Gaussian process independent of `(𝔥, h_1(0))`, so `𝔥 − h_1(0)` is independent of `h_1(0)` — the fact
behind "`h − h_1(0)` and `h̃ − h̃_1(0)` are i.i.d." in the proof of [18] Lemma A.5
.

* `GMSAppA.indepFun_of_add_of_hasGaussianLaw` — finite-dimensional version.
* `GMSAppA.indepFun_of_add_of_isGaussianProcess` — processes `T → ℝ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex

namespace MatedCRTHarmonic.GMSAppA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F]

/-- **Cancellation of an independent Gaussian summand** (finite dimensions). -/
theorem indepFun_of_add_of_hasGaussianLaw {X Y : Ω → E} {C : Ω → F} (hX : Measurable X)
    (hY : Measurable Y) (hC : Measurable C) (hsum : IndepFun (X + Y) C P)
    (hYXC : IndepFun Y (fun ω => (X ω, C ω)) P) (hYG : HasGaussianLaw Y P) :
    IndepFun X C P := by
  have hXY : IndepFun X Y P := (hYXC.comp measurable_id measurable_fst).symm
  rw [indepFun_iff_charFunDual_prod hX.aemeasurable hC.aemeasurable]
  intro L
  set L₁ := L.comp (ContinuousLinearMap.inl ℝ E F)
  set L₂ := L.comp (ContinuousLinearMap.inr ℝ E F)
  -- `V = (X, C)` and `W = (Y, 0)` are independent, `V + W = (X + Y, C)`
  set V : Ω → E × F := fun ω => (X ω, C ω)
  set W : Ω → E × F := fun ω => ContinuousLinearMap.inl ℝ E F (Y ω)
  have hVm : Measurable V := hX.prodMk hC
  have hWm : Measurable W := (ContinuousLinearMap.inl ℝ E F).continuous.measurable.comp hY
  have hVW : IndepFun V W P :=
    (hYXC.comp (ContinuousLinearMap.inl ℝ E F).continuous.measurable measurable_id).symm
  have h1 := hVW.charFunDual_map_add_eq_mul hVm.aemeasurable hWm.aemeasurable
  have hsumVW : V + W = fun ω => ((X + Y) ω, C ω) := by
    funext ω; simp [V, W]
  have h2 := (indepFun_iff_charFunDual_prod (hX.add hY).aemeasurable hC.aemeasurable).1 hsum L
  have h3 := hXY.charFunDual_map_add_eq_mul hX.aemeasurable hY.aemeasurable
  have hWmap : charFunDual (P.map W) L = charFunDual (P.map Y) L₁ := by
    have e : W = (ContinuousLinearMap.inl ℝ E F) ∘ Y := rfl
    rw [e, ← Measure.map_map (ContinuousLinearMap.inl ℝ E F).continuous.measurable hY,
      charFunDual_map]
  have hne : charFunDual (P.map Y) L₁ ≠ 0 := by
    rw [hYG.charFunDual_map_eq]; exact Complex.exp_ne_zero _
  have key : charFunDual (P.map V) L * charFunDual (P.map Y) L₁ =
      charFunDual (P.map X) L₁ * charFunDual (P.map C) L₂ * charFunDual (P.map Y) L₁ := by
    have := congrFun h1 L
    rw [Pi.mul_apply, hsumVW, h2, hWmap, h3, Pi.mul_apply] at this
    rw [← this]
    ring
  exact mul_right_cancel₀ hne key

lemma measurable_finsetRestrict {T : Type*} (J : Finset T) :
    Measurable (fun f : T → ℝ => J.restrict f) :=
  measurable_pi_iff.2 fun j => measurable_pi_apply (j : T)

/-- **Cancellation of an independent Gaussian summand** for processes indexed by an arbitrary `T`: if `X + Y` is
independent of `C`, `Y` is a Gaussian process independent of `(X, C)`, then `X` is independent of `C`. -/
theorem indepFun_of_add_of_isGaussianProcess {T : Type*} {X Y : Ω → T → ℝ} {C : Ω → F}
    (hX : Measurable X) (hY : Measurable Y) (hC : Measurable C) (hsum : IndepFun (X + Y) C P)
    (hYXC : IndepFun Y (fun ω => (X ω, C ω)) P)
    (hYG : IsGaussianProcess (fun t ω => Y ω t) P) :
    IndepFun X C P := by
  classical
  -- the finite restrictions
  have hfin : ∀ J : Finset T, IndepFun (fun ω => J.restrict (X ω)) C P := by
    intro J
    have hR : Measurable (fun f : T → ℝ => J.restrict f) := measurable_finsetRestrict J
    refine indepFun_of_add_of_hasGaussianLaw (hR.comp hX) (hR.comp hY) hC ?_ ?_ (hYG.hasGaussianLaw J)
    · have := hsum.comp hR measurable_id
      convert this using 1
      · funext ω; rfl
      · rfl
    · exact hYXC.comp hR ((hR.comp measurable_fst).prodMk measurable_snd)
  have hfin' : ∀ J : Finset T, Indep (MeasurableSpace.comap (fun ω => J.restrict (X ω)) inferInstance)
      (MeasurableSpace.comap C inferInstance) P := fun J => (IndepFun_iff_Indep _ _ _).1 (hfin J)
  rw [IndepFun_iff_Indep]
  set m : Finset T → MeasurableSpace Ω := fun J =>
    MeasurableSpace.comap (fun ω => J.restrict (X ω)) inferInstance
  have hmle : ∀ J, m J ≤ mΩ := fun J => ((measurable_finsetRestrict J).comp hX).comap_le
  have hdir : Directed (· ≤ ·) m := by
    intro J₁ J₂
    refine ⟨J₁ ∪ J₂, ?_, ?_⟩
    · refine MeasurableSpace.comap_le_iff_le_map.2 ?_
      intro s hs
      have hres : Measurable fun g : ((J₁ ∪ J₂ : Finset T) → ℝ) =>
          (fun j : J₁ => g ⟨j.1, Finset.mem_union_left _ j.2⟩) :=
        measurable_pi_iff.2 fun j => measurable_pi_apply _
      exact ⟨_, hres hs, rfl⟩
    · refine MeasurableSpace.comap_le_iff_le_map.2 ?_
      intro s hs
      have hres : Measurable fun g : ((J₁ ∪ J₂ : Finset T) → ℝ) =>
          (fun j : J₂ => g ⟨j.1, Finset.mem_union_right _ j.2⟩) :=
        measurable_pi_iff.2 fun j => measurable_pi_apply _
      exact ⟨_, hres hs, rfl⟩
  have hsup := indep_iSup_of_directed_le hfin' hmle hC.comap_le hdir
  refine indep_of_indep_of_le_left hsup ?_
  -- `σ(X) ≤ ⨆_J σ(X_J)`
  have h1 : ∀ t : T, Measurable[m {t}] fun ω => X ω t := by
    intro t
    have : (fun ω => X ω t) =
        (fun g : (({t} : Finset T) → ℝ) => g ⟨t, Finset.mem_singleton_self t⟩) ∘
          fun ω => ({t} : Finset T).restrict (X ω) := rfl
    rw [this]
    exact (measurable_pi_apply _).comp (comap_measurable _)
  show MeasurableSpace.comap X MeasurableSpace.pi ≤ ⨆ J, m J
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun t => ?_
  rw [MeasurableSpace.comap_comp]
  exact (h1 t).comap_le.trans (le_iSup m {t})

end MatedCRTHarmonic.GMSAppA
