import Mathlib

/-!
# Zero-one law for variables determined by two independent sources; singularity of graph laws

* `LatticeProb.exists_ae_eq_const_of_indepFun_self`: a random element `U` with values in a space with
  measurable diagonal which is independent of itself is almost surely constant.
* `LatticeProb.exists_ae_eq_const_of_indepFun_of_ae_eq`: two independent random elements which are
  almost surely equal are almost surely constant.
* `LatticeProb.exists_ae_eq_const_of_ae_eq_comp_indep`: if `c` is almost surely equal to a
  (almost everywhere) measurable function of `X` and also to one of `Y`, with `X` independent of `Y`,
  then `c` is almost surely constant.
* `LatticeProb.mutuallySingular_map_graph_of_ae_ne`: if `f (Y ω) ≠ g (Y ω)` almost surely, then the
  laws of `(Y, f Y)` and `(Y, g Y)` are mutually singular.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb

section ZeroOne

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace E] [MeasurableEq E]

/-- A random element which is independent of itself is almost surely constant. -/
theorem exists_ae_eq_const_of_indepFun_self {U : Ω → E} (hU : Measurable U)
    (h : IndepFun U U μ) : ∃ k : E, U =ᵐ[μ] fun _ => k := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hU.aemeasurable).1 h
  have hdiag : MeasurableSet (diagonal E) := measurableSet_diagonal
  have h1 : ((μ.map U).prod (μ.map U)) (diagonal E) = 1 := by
    rw [← hmap, Measure.map_apply (hU.prodMk hU) hdiag]
    have : (fun ω => (U ω, U ω)) ⁻¹' diagonal E = univ := by ext ω; simp
    rw [this, measure_univ]
  have h2 : ((μ.map U).prod (μ.map U)) (diagonal E) = ∫⁻ x, (μ.map U) {x} ∂(μ.map U) := by
    rw [Measure.prod_apply hdiag]
    refine lintegral_congr fun x => ?_
    congr 1
    ext y
    simp [eq_comm]
  have h3 : (fun x => (μ.map U) {x}) =ᵐ[μ.map U] fun _ => (1 : ℝ≥0∞) := by
    refine ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall fun x => prob_le_one)
      ?_ aemeasurable_const ?_
    · rw [← h2, h1]; exact ENNReal.one_ne_top
    · rw [lintegral_const, measure_univ, mul_one, ← h2, h1]
  obtain ⟨k, hk⟩ := h3.exists
  refine ⟨k, ?_⟩
  have hk1 : μ (U ⁻¹' {k}) = 1 := by
    rw [← Measure.map_apply hU (measurableSet_singleton k)]; exact hk
  rw [Filter.EventuallyEq, ae_iff]
  have : {a | ¬ U a = k} = (U ⁻¹' {k})ᶜ := by ext a; simp
  rw [this, prob_compl_eq_zero_iff (hU (measurableSet_singleton k))]
  exact hk1

/-- Two independent random elements which are almost surely equal are almost surely constant. -/
theorem exists_ae_eq_const_of_indepFun_of_ae_eq {U V : Ω → E} (hU : Measurable U)
    (hind : IndepFun U V μ) (huv : U =ᵐ[μ] V) : ∃ k : E, U =ᵐ[μ] fun _ => k :=
  exists_ae_eq_const_of_indepFun_self hU (hind.congr (Filter.EventuallyEq.refl _ _) huv.symm)

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- If `c` is almost surely equal to a function of `X` and to a function of `Y`, with `X`
independent of `Y`, then `c` is almost surely constant (the functions need only be almost
everywhere measurable for the laws of `X`, `Y`). -/
theorem exists_ae_eq_const_of_ae_eq_comp_indep {X : Ω → S} {Y : Ω → T} (hX : Measurable X)
    (hY : Measurable Y) (hind : IndepFun X Y μ) {c : Ω → E} {f : S → E} {g : T → E}
    (hf : AEMeasurable f (μ.map X)) (hg : AEMeasurable g (μ.map Y))
    (hcf : c =ᵐ[μ] fun ω => f (X ω)) (hcg : c =ᵐ[μ] fun ω => g (Y ω)) :
    ∃ k : E, c =ᵐ[μ] fun _ => k := by
  have hf' : (fun ω => f (X ω)) =ᵐ[μ] fun ω => hf.mk f (X ω) :=
    ae_of_ae_map hX.aemeasurable hf.ae_eq_mk
  have hg' : (fun ω => g (Y ω)) =ᵐ[μ] fun ω => hg.mk g (Y ω) :=
    ae_of_ae_map hY.aemeasurable hg.ae_eq_mk
  have hind' : IndepFun (fun ω => hf.mk f (X ω)) (fun ω => hg.mk g (Y ω)) μ :=
    hind.comp hf.measurable_mk hg.measurable_mk
  have huv : (fun ω => hf.mk f (X ω)) =ᵐ[μ] fun ω => hg.mk g (Y ω) :=
    hf'.symm.trans (hcf.symm.trans (hcg.trans hg'))
  obtain ⟨k, hk⟩ := exists_ae_eq_const_of_indepFun_of_ae_eq
    (hf.measurable_mk.comp hX) hind' huv
  exact ⟨k, hcf.trans (hf'.trans hk)⟩

end ZeroOne

section Singular

variable {Ω S E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableSpace S]
  [MeasurableSpace E] [MeasurableEq E]

/-- If `f (Y ω) ≠ g (Y ω)` almost surely, the laws of `(Y, f Y)` and `(Y, g Y)` are mutually
singular. -/
theorem mutuallySingular_map_graph_of_ae_ne {Y : Ω → S} (hY : Measurable Y) {f g : S → E}
    (hf : Measurable f) (hg : Measurable g) (hne : ∀ᵐ ω ∂μ, f (Y ω) ≠ g (Y ω)) :
    (μ.map fun ω => (Y ω, f (Y ω))) ⟂ₘ (μ.map fun ω => (Y ω, g (Y ω))) := by
  have hs : MeasurableSet {p : S × E | p.2 = f p.1} :=
    measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  have hfY : Measurable fun ω => f (Y ω) := hf.comp hY
  have hgY : Measurable fun ω => g (Y ω) := hg.comp hY
  refine ⟨{p : S × E | p.2 = f p.1}ᶜ, hs.compl, ?_, ?_⟩
  · rw [Measure.map_apply (hY.prodMk hfY) hs.compl]
    have : (fun ω => (Y ω, f (Y ω))) ⁻¹' {p : S × E | p.2 = f p.1}ᶜ = ∅ := by
      ext ω; simp
    rw [this, measure_empty]
  · rw [compl_compl, Measure.map_apply (hY.prodMk hgY) hs]
    have : (fun ω => (Y ω, g (Y ω))) ⁻¹' {p : S × E | p.2 = f p.1} =
        {ω | ¬ f (Y ω) ≠ g (Y ω)} := by
      ext ω; simp [eq_comm]
    rw [this]
    exact ae_iff.1 hne

end Singular

end LatticeProb
