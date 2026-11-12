/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HarmLocC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HarmLocB
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jEDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of the harmonic part (task P2-HARMLOC, part C): `GM.P412jHarmLoc`

* `condExp_pair_version` (general, arbitrary additive constant): for a bounded open `U` with
  `R = H₀¹(U) ⊥ 𝟙_s` (`s ∈ σ(h|_{ℂ∖U})`) and a mean-zero `χ` supported in an open `W ⊇ U`,
  `E[⟨h, χ⟩ | σ(h|_{ℂ∖U})]` has a `σ(h|_W)`-measurable version (it is `⟨h, χ⟩ − Π_R⟨h, χ⟩`,
  `HarmLocB`).
* `p412jHarmLoc_raw` (the core of `GM.P412jHarmLoc`, for the raw harmonic part `IsHarmPartRaw`,
  i.e. the pre-D110 `Blueprint.IsHarmPart`; `GM.P412jHarmLoc` itself is in `HarmLocD`, D110 P2).
  Proof: for a raw harmonic part `H`, `IsHarmPartRaw` with `φ = −Δf/2π` and weak harmonicity of
  `H` give `R ⊥ L²(𝒢)`;
  with `φ₀` a unit radial bump at `u` and `ψ` a unit bump in `V ∖ cl U`, the mean value property
  gives `H(u) − ⟨h, ψ⟩ = E[⟨h, φ₀ − ψ⟩ | 𝒢]` a.s., which is `σ(h|_V)`-measurable; finally
  `⟨h, ψ⟩` and `h_ρ(w)` are `σ(h|_V)`-measurable.

Sources: Sheffield, *Gaussian free fields for mathematicians* (math/0312099) §2.6, Thm 2.17;
Berestycki–Powell (arXiv:2404.16642) Thm 1.52 (the harmonic part is the projection of `h` onto
`Harm(U)`, i.e. `E[· | h|_{ℂ∖U}]`, and `h − 𝔥^U ∈ H₀¹(U)` is a function of `h|_U`). Note: since
`V ⊇ cl U` contains `U`, no localisation to a neighbourhood of `∂U` is needed (contrary to
`handoff/P2-M2J2h.md` route (b)): `𝔥^U = h − h̊` on `U` with `h̊` in the span of `h|_U`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace HarmLoc

open MarkovGauss MarkovZB MarkovGermVer MarkovHarm Blueprint QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **The conditional expectation of a mean-zero pairing given `σ(h|_{ℂ∖U})` is
`σ(h|_W)`-measurable** for open `W ⊇ U ∪ supp χ` (bounded `U`, any additive constant), provided
the Dirichlet pairings on `U` are orthogonal to `σ(h|_{ℂ∖U})`. -/
theorem condExp_pair_version (hh : IsWholePlaneGFF h P) {U : Opens ℂ}
    (hUb : Bornology.IsBounded (U : Set ℂ))
    (hperp : ∀ f : zsSub (U : Set ℂ), ∀ s, MeasurableSet[fieldSigmaClosed h (U : Set ℂ)ᶜ] s →
      ∫ ω in s, h ω (cmTest (zsTest f.2)) ∂P = 0)
    (χ : TestC0) {W : Opens ℂ} (hUW : (U : Set ℂ) ⊆ W) (hχW : tsupport (χ.1 : ℂ → ℝ) ⊆ W) :
    ∃ G : Ω → ℝ, Measurable[fieldSigma h W] G ∧
      P[fun ω => h ω χ.1 | fieldSigmaClosed h (U : Set ℂ)ᶜ] =ᵐ[P] G := by
  set hN := isNormalized_recF hh
  set R := rangeR hh U
  have hm : fieldSigmaClosed h (U : Set ℂ)ᶜ ≤ ‹MeasurableSpace Ω› := fieldSigmaClosed_le hh _
  set X := (memLp_pair hN.1 χ).toLp (pairProc (recF h) χ)
  set A := X - R.starProjection X
  obtain ⟨G₁, hG₁m, hAG₁⟩ := exists_germ_version_of_mem hh (U : Set ℂ)ᶜ (f := (A : Ω → ℝ))
    fun ε hε => ⟨A, sub_proj_mem_germSpan hh hUb hε χ, ae_eq_refl _⟩
  have hAW : A ∈ germSpan hh (W : Set ℂ) := by
    refine sub_mem ?_ (germSpan_mono hh hUW (rangeR_le_germSpan hh U (R.starProjection_apply_mem X)))
    rw [← germSpan_recF hh]
    exact toLp_mem_germSpan hN.1 χ hχW
  obtain ⟨G₂, hG₂m, hAG₂⟩ := exists_version_of_mem_germSpan hh W hAW
  refine ⟨G₂, hG₂m, ?_⟩
  have hXh : (X : Ω → ℝ) =ᵐ[P] fun ω => h ω χ.1 :=
    (memLp_pair hN.1 χ).coeFn_toLp.mono fun ω hω => hω.trans (recF_pair h ω χ)
  have hf : Integrable (fun ω => h ω χ.1) P := (memLp_pair hh χ).integrable one_le_two
  have hG₁i : Integrable G₁ P := ((Lp.memLp A).integrable one_le_two).congr hAG₁
  have key : G₁ =ᵐ[P] P[fun ω => h ω χ.1 | fieldSigmaClosed h (U : Set ℂ)ᶜ] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hG₁i.integrableOn)
      (fun s hs _ => ?_) (hG₁m.stronglyMeasurable.aestronglyMeasurable)
    have h1 : ∫ ω in s, G₁ ω ∂P = ∫ ω in s, (A : Ω → ℝ) ω ∂P :=
      setIntegral_congr_ae (hm s hs) (hAG₁.mono fun ω hω _ => hω.symm)
    have h2 : ∫ ω in s, h ω χ.1 ∂P = ∫ ω in s, (X : Ω → ℝ) ω ∂P :=
      setIntegral_congr_ae (hm s hs) (hXh.mono fun ω hω _ => hω.symm)
    rw [h1, h2, ← L2.inner_indicatorConstLp_one (hm s hs) (measure_ne_top P s),
      ← L2.inner_indicatorConstLp_one (hm s hs) (measure_ne_top P s), inner_sub_right,
      inner_indicator_rangeR hh hperp hs (R.starProjection_apply_mem X), sub_zero]
  exact key.symm.trans (hAG₁.symm.trans hAG₂)

/-- the **raw** harmonic part (the pre-D110 `Blueprint.IsHarmPart`): conditioning on the raw
`σ(h|_{ℂ∖U})` (`fieldSigmaClosed h Uᶜ`). False to exist for a field with a random additive
constant (DEC-110 §1); used as a proof device for normalized fields (`CONF.normIn`), where it
coincides with `Blueprint.IsHarmPart` (`HarmLocD`, `CONF.isHarmPart0_of_isHarmPart_normIn`). -/
def IsHarmPartRaw (P : Measure Ω) (h : Ω → DistC) (U : Set ℂ) (H : Ω → ℂ → ℝ) : Prop :=
  (∀ ω, InnerProductSpace.HarmonicOnNhd (H ω) U) ∧
  ∀ φ ψ : TestC, tsupport ⇑φ ⊆ U → tsupport ⇑ψ ⊆ (closure U)ᶜ → ∫ x, ψ x = 1 →
    P[fun ω => h ω (φ - (∫ x, φ x) • ψ) | fieldSigmaClosed h Uᶜ] =ᵐ[P]
      fun ω => (∫ x, H ω x * φ x) - (∫ x, φ x) * h ω ψ

/-- **locality of the raw harmonic part** (core of `GM.P412jHarmLoc`): if `H` is a raw harmonic
part of `h|_U`, then `H(u) − h_ρ(w)` is a.s. `σ(h|_V)`-measurable. -/
theorem p412jHarmLoc_raw (hh : IsWholePlaneGFF h P) (U V : Set ℂ) (hV : IsOpen V) (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUV : closure U ⊆ V) (ρ : ℝ) (w : ℂ) (hρ : 0 < ρ)
    (hS : sphere w ρ ⊆ V) (u : ℂ) (hu : u ∈ U) {H : Ω → ℂ → ℝ} (hH : IsHarmPartRaw P h U H) :
    ∃ G : Ω → ℝ, Measurable[fieldSigma h (toOpens V hV)] G ∧
      (fun ω => H ω u - circleAvg (h ω) ρ w) =ᵐ[P] G := by
  have hcirc : Measurable[fieldSigma h (toOpens V hV)] fun ω => circleAvg (h ω) ρ w := by
    obtain ⟨ε, hε, hεV⟩ := (isCompact_sphere w ρ).exists_thickening_subset_open hV hS
    have hεV' : thickening ε (sphere w |ρ|) ⊆ V := by rwa [abs_of_pos hρ]
    exact (GM.measurable_circleAvg_fieldSigma h ρ w hε).mono
      (GM.fieldSigma_mono h (V := nbhdO ε (sphere w |ρ|)) (W := toOpens V hV) hεV') le_rfl
  have hm : fieldSigmaClosed h Uᶜ ≤ ‹MeasurableSpace Ω› := fieldSigmaClosed_le hh _
  -- the unit bump `ψ` in `V ∖ cl U`
  have hWne : (V ∩ (closure U)ᶜ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, ← Set.sdiff_eq, Set.sdiff_eq_empty] at hne
    have hcl : closure U = V := le_antisymm hUV hne
    have hclopen : IsClopen (closure U) := ⟨isClosed_closure, hcl ▸ hV⟩
    rcases isClopen_iff.1 hclopen with h0 | h1
    · rw [closure_empty_iff] at h0
      exact (h0 ▸ hu : u ∈ (∅ : Set ℂ))
    · exact NormedSpace.unbounded_univ ℝ ℂ (h1 ▸ hUb.closure)
  obtain ⟨ψ, hψW, hψ1⟩ := exists_unit_test (hV.inter isClosed_closure.isOpen_compl) hWne
  have hψV : tsupport (ψ : ℂ → ℝ) ⊆ V := hψW.trans inter_subset_left
  have hψU : tsupport (ψ : ℂ → ℝ) ⊆ (closure U)ᶜ := hψW.trans inter_subset_right
  -- the unit radial bump `φ₀` at `u`
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo u hu
  have hδU : closedBall u (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  set φ₀ := unitBump (ε / 2) (by positivity) u
  have hφ₀U : tsupport (φ₀ : ℂ → ℝ) ⊆ U := (tsupport_unitBump _ _ u).trans hδU
  have hφ₀1 : ∫ x, φ₀ x = 1 := integral_unitBump _ _ u
  have hχ0 : ∫ x, (φ₀ - ψ) x = 0 := by
    show ∫ x, (φ₀ x - ψ x) = 0
    rw [integral_sub (φ₀.continuous.integrable_of_hasCompactSupport φ₀.hasCompactSupport)
      (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport), hφ₀1, hψ1, sub_self]
  set χ : TestC0 := ⟨φ₀ - ψ, hχ0⟩
  have hχV : tsupport (χ.1 : ℂ → ℝ) ⊆ V := by
    refine (tsupport_sub (φ₀ : ℂ → ℝ) ψ).trans (union_subset ?_ hψV)
    exact hφ₀U.trans (subset_closure.trans hUV)
  -- `R ⊥ 𝒢` from `IsHarmPart` and weak harmonicity
  have hperp : ∀ f : zsSub ((toOpens U hUo : Opens ℂ) : Set ℂ), ∀ s, MeasurableSet[fieldSigmaClosed h Uᶜ] s →
      ∫ ω in s, h ω (cmTest (zsTest f.2)) ∂P = 0 := by
    intro f s hs
    have hsupp : tsupport (cmTest (zsTest f.2) : ℂ → ℝ) ⊆ U :=
      (tsupport_cmTest_subset f.2).trans f.2.2.2
    have hc := hH.2 (cmTest (zsTest f.2)) ψ hsupp hψU hψ1
    rw [integral_cmTest] at hc
    simp only [zero_smul, sub_zero, zero_mul] at hc
    have hint : Integrable (fun ω => h ω (cmTest (zsTest f.2))) P :=
      (memLp_pair hh (cmTest0 (zsTest f.2))).integrable one_le_two
    rw [← setIntegral_condExp hm hint hs, setIntegral_congr_ae (hm s hs)
      (hc.mono fun ω hω _ => hω)]
    exact (integral_congr_ae (Eventually.of_forall fun ω =>
      integral_mul_cmTest_of_harmonic hUo (hH.1 ω) (zsTest f.2) f.2.2.2)).trans (integral_zero _ _)
  obtain ⟨G, hGm, hGe⟩ := condExp_pair_version hh (U := toOpens U hUo) hUb hperp χ
    (W := toOpens V hV) (subset_closure.trans hUV) hχV
  have hc := hH.2 φ₀ ψ hφ₀U hψU hψ1
  rw [hφ₀1] at hc
  simp only [one_smul, one_mul] at hc
  refine ⟨fun ω => G ω + h ω ψ - circleAvg (h ω) ρ w,
    (hGm.add (GM.measurable_pair_fieldSigma h ψ hψV)).sub hcirc, ?_⟩
  filter_upwards [hc, hGe] with ω h1 h2
  have h3 : (∫ x, H ω x * φ₀ x) - h ω ψ = G ω := h1.symm.trans h2
  rw [integral_mul_unitBump hUo (hH.1 ω) _ hδU] at h3
  show H ω u - circleAvg (h ω) ρ w = G ω + h ω ψ - circleAvg (h ω) ρ w
  linarith

end HarmLoc
end LQGMetric
