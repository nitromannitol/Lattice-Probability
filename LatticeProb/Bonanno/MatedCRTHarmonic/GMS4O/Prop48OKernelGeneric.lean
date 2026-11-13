/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OKernelGeneric at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Kernel versions of families of conditional expectations

For a jointly measurable family `(Y(·, θ), X(·, θ))`, indexed by a parameter `θ`, with `Y` valued in a
countably generated space, Mathlib's `Kernel.condKernel` disintegrates the kernel
`θ ↦ law(Y(·, θ), X(·, θ))`. The value `g(θ, y) = ∫ x⁺ d condKernel(θ, y)` is jointly measurable, and
`g(θ, Y(·, θ))` is a version of `E[X(·, θ) | Y(·, θ)]` for **every** `θ`.

The identities are stated at the level of laws (`p48o_condValueG_ae_eq_condExp_of_law`): any random
pair on any probability space with the same joint law is conditioned by the same function. This is
what transports conditional means along equalities of laws (far pairs of [18] Prop. 4.8).

`p48o_condValueG_frozen` is the frozen-parameter form used with an independent phase: for `V ⟂ U`
and `X = F(V, U)`, the kernel function of the frozen family `ψ ↦ (a(V), F(V, ψ))`, read at `ψ = U`, is
a version of `E[F(V, U) | a(V), U]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4O

section KernelG

variable {Ω Θ β : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
  [MeasurableSpace.CountablyGenerated β] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The kernel `θ ↦ law(Y(·, θ), X(·, θ))`. -/
def p48oPairKernelG (Y : Ω → Θ → β) (X : Ω → Θ → ℝ) : Kernel Θ (β × ℝ) :=
  (Kernel.const Θ P ×ₖ Kernel.id).map (fun p : Ω × Θ => (Y p.1 p.2, X p.1 p.2))

instance p48oPairKernelG.instIsFiniteKernel (Y : Ω → Θ → β) (X : Ω → Θ → ℝ) :
    IsFiniteKernel (p48oPairKernelG P Y X) := by
  unfold p48oPairKernelG
  infer_instance

omit [MeasurableSpace.CountablyGenerated β] in
lemma p48oPairKernelG_apply {Y : Ω → Θ → β} {X : Ω → Θ → ℝ}
    (hY : Measurable fun p : Ω × Θ => Y p.1 p.2) (hX : Measurable fun p : Ω × Θ => X p.1 p.2)
    (θ : Θ) : p48oPairKernelG P Y X θ = P.map (fun ω => (Y ω θ, X ω θ)) := by
  have hF : Measurable fun p : Ω × Θ => (Y p.1 p.2, X p.1 p.2) := hY.prodMk hX
  rw [p48oPairKernelG, Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.const_apply,
    Kernel.id_apply, Measure.prod_dirac,
    Measure.map_map hF (measurable_prodMk_right (y := θ) : Measurable fun x : Ω => (x, θ))]
  rfl

/-- The kernel value `g(θ, y) = ∫ x⁺ d condKernel(θ, y)`. -/
def p48oCondValueG (Y : Ω → Θ → β) (X : Ω → Θ → ℝ) (p : Θ × β) : ℝ :=
  ∫ x, max x 0 ∂(Kernel.condKernel (p48oPairKernelG P Y X) p)

lemma measurable_p48oCondValueG (Y : Ω → Θ → β) (X : Ω → Θ → ℝ) :
    Measurable (p48oCondValueG P Y X) := by
  have h : StronglyMeasurable fun q : (Θ × β) × ℝ => max q.2 0 :=
    (measurable_snd.max measurable_const).stronglyMeasurable
  exact (h.integral_kernel_prod_right'
    (κ := Kernel.condKernel (p48oPairKernelG P Y X))).measurable

lemma p48oCondValueG_nonneg (Y : Ω → Θ → β) (X : Ω → Θ → ℝ) (p : Θ × β) :
    0 ≤ p48oCondValueG P Y X p :=
  integral_nonneg fun x => le_max_right x 0

/-- **Law-level defining identity.** If a random pair `(T', X')` on any probability space has the
joint law of the kernel's fibre at `θ`, then `g(θ, T')` is integrable and has the same integral as
`X'` over every event `{T' ∈ B}`. -/
theorem p48o_condValueG_setIntegral_of_law {Y : Ω → Θ → β} {X : Ω → Θ → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {T' : Ω' → β} {X' : Ω' → ℝ} (hT' : Measurable T') (hX' : Measurable X') (θ : Θ)
    (hlaw : P'.map (fun ω => (T' ω, X' ω)) = p48oPairKernelG P Y X θ)
    (hXint : Integrable X' P') (hX0 : ∀ ω, 0 ≤ X' ω) :
    Integrable (fun ω => p48oCondValueG P Y X (θ, T' ω)) P' ∧
      ∀ B : Set β, MeasurableSet B →
        ∫ ω in T' ⁻¹' B, p48oCondValueG P Y X (θ, T' ω) ∂P' =
          ∫ ω in T' ⁻¹' B, X' ω ∂P' := by
  set κ := p48oPairKernelG P Y X with hκ
  have hF : Measurable fun ω => (T' ω, X' ω) := hT'.prodMk hX'
  have hfst : κ.fst θ = P'.map T' := by
    rw [Kernel.fst_apply, ← hlaw, Measure.map_map measurable_fst hF]
    rfl
  have hdis : (κ.fst ⊗ₖ Kernel.condKernel κ) θ = κ θ := by rw [Kernel.disintegrate]
  have hgm : Measurable fun y : β => p48oCondValueG P Y X (θ, y) :=
    (measurable_p48oCondValueG P Y X).comp (measurable_const.prodMk measurable_id)
  have hpos : Integrable (fun q : β × ℝ => max q.2 0) (κ θ) := by
    rw [← hlaw, integrable_map_measure
      (measurable_snd.max measurable_const).aestronglyMeasurable hF.aemeasurable]
    refine hXint.congr (Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, max_eq_left (hX0 ω)]
  have hpos' : Integrable (fun q : β × ℝ => max q.2 0)
      ((κ.fst ⊗ₖ Kernel.condKernel κ) θ) := by rw [hdis]; exact hpos
  have hgint : Integrable (fun y : β => p48oCondValueG P Y X (θ, y)) (κ.fst θ) :=
    hpos'.integral_compProd
  have hgintP : Integrable (fun ω => p48oCondValueG P Y X (θ, T' ω)) P' := by
    rw [hfst] at hgint
    exact (integrable_map_measure hgm.aestronglyMeasurable hT'.aemeasurable).1 hgint
  refine ⟨hgintP, fun B hB => ?_⟩
  have hBset : MeasurableSet (B ×ˢ (univ : Set ℝ)) := hB.prod MeasurableSet.univ
  set G : β × ℝ → ℝ := (B ×ˢ (univ : Set ℝ)).indicator fun q => max q.2 0 with hG
  have hGint : Integrable G ((κ.fst ⊗ₖ Kernel.condKernel κ) θ) := hpos'.indicator hBset
  have hGm : Measurable G := (measurable_snd.max measurable_const).indicator hBset
  calc ∫ ω in T' ⁻¹' B, p48oCondValueG P Y X (θ, T' ω) ∂P'
      = ∫ y in B, p48oCondValueG P Y X (θ, y) ∂(P'.map T') := by
        rw [setIntegral_map hB hgm.aestronglyMeasurable hT'.aemeasurable]
    _ = ∫ y, B.indicator (fun y => p48oCondValueG P Y X (θ, y)) y ∂(κ.fst θ) := by
        rw [integral_indicator hB, hfst]
    _ = ∫ y, ∫ x, G (y, x) ∂(Kernel.condKernel κ (θ, y)) ∂(κ.fst θ) := by
        congr 1
        funext y
        by_cases hy : y ∈ B
        · rw [Set.indicator_of_mem hy]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hG, Set.indicator_of_mem (show (y, x) ∈ B ×ˢ (univ : Set ℝ) from
            ⟨hy, mem_univ x⟩)]
        · rw [Set.indicator_of_notMem hy]
          symm
          refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
          simp only [hG, Set.indicator_of_notMem (show (y, x) ∉ B ×ˢ (univ : Set ℝ) from
            fun h => hy h.1), Pi.zero_apply]
    _ = ∫ q, G q ∂((κ.fst ⊗ₖ Kernel.condKernel κ) θ) := (integral_compProd hGint).symm
    _ = ∫ q, G q ∂(P'.map fun ω => (T' ω, X' ω)) := by rw [hdis, hlaw]
    _ = ∫ ω, G (T' ω, X' ω) ∂P' := integral_map hF.aemeasurable hGm.aestronglyMeasurable
    _ = ∫ ω in T' ⁻¹' B, X' ω ∂P' := by
        rw [← integral_indicator (hT' hB)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        by_cases hω : ω ∈ T' ⁻¹' B
        · rw [Set.indicator_of_mem hω]
          simp only [hG, Set.indicator_of_mem (show (T' ω, X' ω) ∈ B ×ˢ (univ : Set ℝ) from
            ⟨hω, mem_univ _⟩), max_eq_left (hX0 ω)]
        · rw [Set.indicator_of_notMem hω]
          simp only [hG, Set.indicator_of_notMem (show (T' ω, X' ω) ∉ B ×ˢ (univ : Set ℝ) from
            fun h => hω h.1)]

/-- **Law-level conditional expectation.** Under the law hypothesis, `g(θ, T')` is a version of
`E[X' | σ(T'')]` for any measurable `T''` a.s. equal to `T'`. -/
theorem p48o_condValueG_ae_eq_condExp_of_law {Y : Ω → Θ → β} {X : Ω → Θ → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {T' : Ω' → β} {X' : Ω' → ℝ} (hT' : Measurable T') (hX' : Measurable X') (θ : Θ)
    (hlaw : P'.map (fun ω => (T' ω, X' ω)) = p48oPairKernelG P Y X θ)
    (hX0 : ∀ ω, 0 ≤ X' ω)
    {T'' : Ω' → β} (hT'' : Measurable T'') (hTT : T' =ᵐ[P'] T'')
    {X'' : Ω' → ℝ} (hX'' : Integrable X'' P') (hXX : X' =ᵐ[P'] X'') :
    (fun ω => p48oCondValueG P Y X (θ, T' ω)) =ᵐ[P']
      P'[X'' | MeasurableSpace.comap T'' inferInstance] := by
  have hXint : Integrable X' P' := hX''.congr hXX.symm
  obtain ⟨hgint, hset⟩ := p48o_condValueG_setIntegral_of_law P hT' hX' θ hlaw hXint hX0
  have hm : MeasurableSpace.comap T'' inferInstance ≤ ‹MeasurableSpace Ω'› := hT''.comap_le
  have hgm : Measurable fun y : β => p48oCondValueG P Y X (θ, y) :=
    (measurable_p48oCondValueG P Y X).comp (measurable_const.prodMk measurable_id)
  set g' : Ω' → ℝ := fun ω => p48oCondValueG P Y X (θ, T'' ω) with hg'
  have hgg' : (fun ω => p48oCondValueG P Y X (θ, T' ω)) =ᵐ[P'] g' := by
    filter_upwards [hTT] with ω hω
    simp only [hg', hω]
  have hg'int : Integrable g' P' := hgint.congr hgg'
  have hg'm : StronglyMeasurable[MeasurableSpace.comap T'' inferInstance] g' :=
    (hgm.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have hpre : ∀ B : Set β, T' ⁻¹' B =ᵐ[P'] T'' ⁻¹' B := by
    intro B
    filter_upwards [hTT] with ω hω
    simp only [Set.mem_preimage, hω]
  refine hgg'.trans (ae_eq_condExp_of_forall_setIntegral_eq hm hX''
    (fun s _ _ => hg'int.integrableOn) (fun s hs _ => ?_) hg'm.aestronglyMeasurable)
  obtain ⟨B, hB, rfl⟩ := hs
  calc ∫ ω in T'' ⁻¹' B, g' ω ∂P'
      = ∫ ω in T' ⁻¹' B, g' ω ∂P' := setIntegral_congr_set (hpre B).symm
    _ = ∫ ω in T' ⁻¹' B, p48oCondValueG P Y X (θ, T' ω) ∂P' :=
        integral_congr_ae (ae_restrict_of_ae hgg'.symm)
    _ = ∫ ω in T' ⁻¹' B, X' ω ∂P' := hset B hB
    _ = ∫ ω in T' ⁻¹' B, X'' ω ∂P' := integral_congr_ae (ae_restrict_of_ae hXX)
    _ = ∫ ω in T'' ⁻¹' B, X'' ω ∂P' := setIntegral_congr_set (hpre B)

/-- The parameter-family version: `g(θ, Y(·, θ))` is a version of `E[X(·, θ) | Y(·, θ)]` at every
`θ`. -/
theorem p48o_condValueG_ae_eq_condExp {Y : Ω → Θ → β} {X : Ω → Θ → ℝ}
    (hY : Measurable fun p : Ω × Θ => Y p.1 p.2) (hX : Measurable fun p : Ω × Θ => X p.1 p.2)
    (θ : Θ) (hX0 : ∀ ω, 0 ≤ X ω θ) (hXint : Integrable (fun ω => X ω θ) P) :
    (fun ω => p48oCondValueG P Y X (θ, Y ω θ)) =ᵐ[P]
      P[fun ω => X ω θ | MeasurableSpace.comap (fun ω => Y ω θ) inferInstance] := by
  have hYθ : Measurable fun ω => Y ω θ := hY.comp (measurable_id.prodMk measurable_const)
  have hXθ : Measurable fun ω => X ω θ := hX.comp (measurable_id.prodMk measurable_const)
  exact p48o_condValueG_ae_eq_condExp_of_law P hYθ hXθ θ
    (p48oPairKernelG_apply P hY hX θ).symm hX0 hYθ (ae_eq_refl _) hXint (ae_eq_refl _)

end KernelG

/-! ### Freezing an independent parameter -/

section Frozen

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountablyGenerated β] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Lower integrals of a function of an independent pair split as an iterated integral. -/
lemma p48o_lintegral_indep_split {V : Ω → α} {U : Ω → ℝ} (hV : Measurable V) (hU : Measurable U)
    (hind : IndepFun V U P) {Φ : α × ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (V ω, U ω) ∂P = ∫⁻ ψ, ∫⁻ ω, Φ (V ω, ψ) ∂P ∂(P.map U) := by
  have hlaw : P.map (fun ω => (V ω, U ω)) = (P.map V).prod (P.map U) :=
    (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hU.aemeasurable).1 hind
  have : IsProbabilityMeasure (P.map V) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  rw [← lintegral_map hΦ (hV.prodMk hU), hlaw, lintegral_prod_symm' _ hΦ]
  refine lintegral_congr fun ψ => ?_
  exact lintegral_map (f := fun x => Φ (x, ψ)) (hΦ.comp measurable_prodMk_right) hV

/-- **Freezing an independent parameter.** For `V ⟂ U` and `X = F(V, U) ≥ 0` integrable, the kernel
function of the frozen family `ψ ↦ (a(V), F(V, ψ))`, read at `ψ = U`, is a version of
`E[F(V, U) | a(V), U]`. -/
theorem p48o_condValueG_frozen {V : Ω → α} {U : Ω → ℝ} (hV : Measurable V) (hU : Measurable U)
    (hind : IndepFun V U P) {a : α → β} (ha : Measurable a) {F : α × ℝ → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hint : Integrable (fun ω => F (V ω, U ω)) P) :
    (fun ω => p48oCondValueG P (fun ω (_ψ : ℝ) => a (V ω)) (fun ω ψ => F (V ω, ψ))
        (U ω, a (V ω))) =ᵐ[P]
      P[fun ω => F (V ω, U ω) | MeasurableSpace.comap (fun ω => (a (V ω), U ω)) inferInstance] := by
  set Yf : Ω → ℝ → β := fun ω _ => a (V ω) with hYf
  set Xf : Ω → ℝ → ℝ := fun ω ψ => F (V ω, ψ) with hXf
  have hYfm : Measurable fun p : Ω × ℝ => Yf p.1 p.2 := ha.comp (hV.comp measurable_fst)
  have hXfm : Measurable fun p : Ω × ℝ => Xf p.1 p.2 :=
    hF.comp ((hV.comp measurable_fst).prodMk measurable_snd)
  set g : ℝ × β → ℝ := p48oCondValueG P Yf Xf with hg
  have hgm : Measurable g := measurable_p48oCondValueG P Yf Xf
  have hTm : Measurable fun ω => (a (V ω), U ω) := (ha.comp hV).prodMk hU
  have hm : MeasurableSpace.comap (fun ω => (a (V ω), U ω)) inferInstance ≤
      ‹MeasurableSpace Ω› := hTm.comap_le
  -- the frozen parameter values for which the frozen variable is integrable
  have hlin : ∫⁻ ω, ENNReal.ofReal (F (V ω, U ω)) ∂P < ⊤ := by
    have h := hint.2
    rw [HasFiniteIntegral] at h
    refine lt_of_le_of_lt (le_of_eq ?_) h
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (hF0 _)]
  have hsplit := p48o_lintegral_indep_split hV hU hind
    (Φ := fun x => ENNReal.ofReal (F x)) (ENNReal.measurable_ofReal.comp hF)
  have hfin : ∀ᵐ ψ ∂(P.map U), ∫⁻ ω, ENNReal.ofReal (F (V ω, ψ)) ∂P < ⊤ := by
    refine ae_lt_top ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp hXfm).lintegral_prod_left'
    · rw [← hsplit]; exact hlin.ne
  have hintψ : ∀ᵐ ψ ∂(P.map U), Integrable (fun ω => F (V ω, ψ)) P := by
    filter_upwards [hfin] with ψ hψ
    refine ⟨(hXfm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) hψ
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (hF0 _)]
  -- the defining identity at almost every frozen value, in lower-integral form
  have hdefψ : ∀ᵐ ψ ∂(P.map U), ∀ B : Set β, MeasurableSet B →
      ∫⁻ ω in (fun ω => a (V ω)) ⁻¹' B, ENNReal.ofReal (g (ψ, a (V ω))) ∂P =
        ∫⁻ ω in (fun ω => a (V ω)) ⁻¹' B, ENNReal.ofReal (F (V ω, ψ)) ∂P := by
    filter_upwards [hintψ] with ψ hψ B hB
    have hYψ : Measurable fun ω => Yf ω ψ := ha.comp hV
    have hXψ : Measurable fun ω => Xf ω ψ := hXfm.comp (measurable_id.prodMk measurable_const)
    obtain ⟨hgi, hset⟩ := p48o_condValueG_setIntegral_of_law P hYψ hXψ ψ
      (p48oPairKernelG_apply P hYfm hXfm ψ).symm hψ (fun ω => hF0 _)
    have hpre : MeasurableSet ((fun ω => a (V ω)) ⁻¹' B) := (ha.comp hV) hB
    rw [← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
        (Eventually.of_forall fun ω => p48oCondValueG_nonneg P Yf Xf _),
      ← ofReal_integral_eq_lintegral_ofReal hψ.integrableOn
        (Eventually.of_forall fun ω => hF0 _)]
    exact congrArg ENNReal.ofReal (hset B hB)
  -- set lower integrals of the frozen version
  have hsetL : ∀ B' : Set (β × ℝ), MeasurableSet B' →
      ∫⁻ ω in (fun ω => (a (V ω), U ω)) ⁻¹' B', ENNReal.ofReal (g (U ω, a (V ω))) ∂P =
        ∫⁻ ω in (fun ω => (a (V ω), U ω)) ⁻¹' B', ENNReal.ofReal (F (V ω, U ω)) ∂P := by
    intro B' hB'
    have hind1 : Measurable fun x : α × ℝ =>
        B'.indicator (fun _ => (1 : ℝ≥0∞)) (a x.1, x.2) :=
      (measurable_const.indicator hB').comp ((ha.comp measurable_fst).prodMk measurable_snd)
    have hΦ1 : Measurable fun x : α × ℝ => B'.indicator (fun _ => (1 : ℝ≥0∞)) (a x.1, x.2) *
        ENNReal.ofReal (g (x.2, a x.1)) :=
      hind1.mul (ENNReal.measurable_ofReal.comp
        (hgm.comp (measurable_snd.prodMk (ha.comp measurable_fst))))
    have hΦ2 : Measurable fun x : α × ℝ => B'.indicator (fun _ => (1 : ℝ≥0∞)) (a x.1, x.2) *
        ENNReal.ofReal (F x) := hind1.mul (ENNReal.measurable_ofReal.comp hF)
    have hlhs : ∫⁻ ω in (fun ω => (a (V ω), U ω)) ⁻¹' B', ENNReal.ofReal (g (U ω, a (V ω))) ∂P =
        ∫⁻ ω, B'.indicator (fun _ => (1 : ℝ≥0∞)) (a (V ω), U ω) *
          ENNReal.ofReal (g (U ω, a (V ω))) ∂P := by
      rw [← lintegral_indicator (hTm hB')]
      refine lintegral_congr fun ω => ?_
      by_cases hω : (a (V ω), U ω) ∈ B'
      · rw [Set.indicator_of_mem (show ω ∈ (fun ω => (a (V ω), U ω)) ⁻¹' B' from hω),
          Set.indicator_of_mem hω, one_mul]
      · rw [Set.indicator_of_notMem (show ω ∉ (fun ω => (a (V ω), U ω)) ⁻¹' B' from hω),
          Set.indicator_of_notMem hω, zero_mul]
    have hrhs : ∫⁻ ω in (fun ω => (a (V ω), U ω)) ⁻¹' B', ENNReal.ofReal (F (V ω, U ω)) ∂P =
        ∫⁻ ω, B'.indicator (fun _ => (1 : ℝ≥0∞)) (a (V ω), U ω) *
          ENNReal.ofReal (F (V ω, U ω)) ∂P := by
      rw [← lintegral_indicator (hTm hB')]
      refine lintegral_congr fun ω => ?_
      by_cases hω : (a (V ω), U ω) ∈ B'
      · rw [Set.indicator_of_mem (show ω ∈ (fun ω => (a (V ω), U ω)) ⁻¹' B' from hω),
          Set.indicator_of_mem hω, one_mul]
      · rw [Set.indicator_of_notMem (show ω ∉ (fun ω => (a (V ω), U ω)) ⁻¹' B' from hω),
          Set.indicator_of_notMem hω, zero_mul]
    rw [hlhs, hrhs, p48o_lintegral_indep_split hV hU hind hΦ1,
      p48o_lintegral_indep_split hV hU hind hΦ2]
    refine lintegral_congr_ae ?_
    filter_upwards [hdefψ] with ψ hψ
    have hsec : MeasurableSet ((fun b => (b, ψ)) ⁻¹' B') := measurable_prodMk_right hB'
    have hpre' : MeasurableSet ((fun ω => a (V ω)) ⁻¹' ((fun b => (b, ψ)) ⁻¹' B')) :=
      (ha.comp hV) hsec
    have e1 : ∫⁻ ω, B'.indicator (fun _ => (1 : ℝ≥0∞)) (a (V ω), ψ) *
        ENNReal.ofReal (g (ψ, a (V ω))) ∂P =
        ∫⁻ ω in (fun ω => a (V ω)) ⁻¹' ((fun b => (b, ψ)) ⁻¹' B'),
          ENNReal.ofReal (g (ψ, a (V ω))) ∂P := by
      rw [← lintegral_indicator hpre']
      refine lintegral_congr fun ω => ?_
      by_cases hω : (a (V ω), ψ) ∈ B'
      · rw [Set.indicator_of_mem hω, one_mul, Set.indicator_of_mem (show ω ∈
          (fun ω => a (V ω)) ⁻¹' ((fun b => (b, ψ)) ⁻¹' B') from hω)]
      · rw [Set.indicator_of_notMem hω, zero_mul, Set.indicator_of_notMem (show ω ∉
          (fun ω => a (V ω)) ⁻¹' ((fun b => (b, ψ)) ⁻¹' B') from hω)]
    have e2 : ∫⁻ ω, B'.indicator (fun _ => (1 : ℝ≥0∞)) (a (V ω), ψ) *
        ENNReal.ofReal (F (V ω, ψ)) ∂P =
        ∫⁻ ω in (fun ω => a (V ω)) ⁻¹' ((fun b => (b, ψ)) ⁻¹' B'),
          ENNReal.ofReal (F (V ω, ψ)) ∂P := by
      rw [← lintegral_indicator hpre']
      refine lintegral_congr fun ω => ?_
      by_cases hω : (a (V ω), ψ) ∈ B'
      · rw [Set.indicator_of_mem hω, one_mul, Set.indicator_of_mem (show ω ∈
          (fun ω => a (V ω)) ⁻¹' ((fun b => (b, ψ)) ⁻¹' B') from hω)]
      · rw [Set.indicator_of_notMem hω, zero_mul, Set.indicator_of_notMem (show ω ∉
          (fun ω => a (V ω)) ⁻¹' ((fun b => (b, ψ)) ⁻¹' B') from hω)]
    rw [e1, e2, hψ _ hsec]
  -- integrability of the frozen version
  have hgfin : ∫⁻ ω, ENNReal.ofReal (g (U ω, a (V ω))) ∂P < ⊤ := by
    have h := hsetL univ MeasurableSet.univ
    rw [Set.preimage_univ, Measure.restrict_univ] at h
    rw [h]
    exact hlin
  have hgM : Measurable fun ω => g (U ω, a (V ω)) := hgm.comp (hU.prodMk (ha.comp hV))
  have hgint : Integrable (fun ω => g (U ω, a (V ω))) P := by
    refine ⟨hgM.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) hgfin
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (p48oCondValueG_nonneg P Yf Xf _)]
  have hgSM : StronglyMeasurable[MeasurableSpace.comap (fun ω => (a (V ω), U ω)) inferInstance]
      (fun ω => g (U ω, a (V ω))) := by
    have hc : Measurable[MeasurableSpace.comap (fun ω => (a (V ω), U ω)) inferInstance]
        (fun ω => (a (V ω), U ω)) := Measurable.of_comap_le le_rfl
    exact ((hgm.comp (measurable_snd.prodMk measurable_fst)).comp hc).stronglyMeasurable
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hint (fun s _ _ => hgint.integrableOn)
    (fun s hs _ => ?_) hgSM.aestronglyMeasurable
  obtain ⟨B', hB', rfl⟩ := hs
  have hpre := hTm hB'
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω =>
      p48oCondValueG_nonneg P Yf Xf _) hgM.aestronglyMeasurable.restrict,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => hF0 _)
      hint.aestronglyMeasurable.restrict, hsetL B' hB']

end Frozen

end MatedCRTHarmonic.GMS4O
