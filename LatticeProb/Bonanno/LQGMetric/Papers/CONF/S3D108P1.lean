/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108P1 at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module and CONFZBMetricN. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreG
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLocal

/-!
# CONF Remark 1.2: the metric of the zero-boundary part (D108 packet P1)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, Remark 1.2 (C:324–338): "`D_{h̊^U} :=
e^{−ξ𝔥^U} D_{h|_U}` … is a.s. determined by `h̊^U` … since `h − g𝔥^U` is a whole-plane GFF plus a
continuous function, where `g` is a bump function equal to `1` on `V`, and the restrictions of
`h − g𝔥^U` and `h̊^U` to `V` agree" (C:335–337). We follow this proof verbatim:

* the random continuous function `g𝔥^U` is `DFGPS.L217.harmFn φ δ (recField − X)` (mean value
  property, `GM.pair_radBump_of_harmonic`; the same device as DFGPS Lemma 2.17, T:1224–1230), with
  `φ` from `DFGPS.L217.exists_bump_of_isCompact` (`φ = 1` near `cl V`);
* `Y := (h − h_ρ(w)) − g𝔥^U` is `IsGFFPlusCont`; Axiom II (`locality`) for `Y` on `V` gives `F`;
* `Y|_V = X|_V` (`DFGPS.L217.harmFn_sub_apply`); Axiom III (`weyl`, a.s. uniform in the continuous
  function) and the locality of Weyl scaling (`internal_weyl_eq_of_internal_eq`) identify
  `D_{(h − h_ρ(w)) − f}(·,·;V)` with `D_Y(·,·;V)` for every continuous `f = 𝔥^U` on `V`.

**The normalized field.** CONF's `h` is normalized (C:347, C:1187). The harmonic part `𝔥^U` is
that of the normalized field `recField h ρ w = h − h_ρ(w)`, and Remark 1.2 is stated for the metric
`D_{(h − h_ρ(w)) − f}(·,·;V)` of the normalized field: `CONFZBMetricN` below (proved,
`confZBMetricN`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **CONF Remark 1.2** (C:324–338) for the normalized field `h − h_ρ(w)` (see the module
docstring): for `V` open with `cl V ⊆ U` and every version `X` of
`h̊^U`, there is a measurable `F` with, a.s., `D_{(h − h_ρ(w)) − f}(·,·;V) = F(X|_V)` for every
continuous `f` equal to the harmonic part `𝔥^U` on `V`. -/
def CONFZBMetricN (D : DistC → ContMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (ρ : ℝ) (w : ℂ) (U : Set ℂ) (hU : IsOpen U),
      Bornology.IsBounded U → ∀ X : Ω → DistC, IsL33ZBPart P h ρ w U hU X →
      ∀ (V : TopologicalSpace.Opens ℂ), closure (V : Set ℂ) ⊆ U →
      ∃ F : DistOn V → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U →
          (∀ φ : TestOn (toOpens U hU),
            restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
          ∀ f : C(ℂ, ℝ), tsupport ⇑f ⊆ U → EqOn ⇑f 𝔥 (V : Set ℂ) →
          ∀ z ∈ V, ∀ y ∈ V,
            (D (addFun (recField h ρ w ω) (-f))).internal V z y = F (restrictTo V (X ω)) z y

/-- **The field `h − g𝔥^U` of CONF Remark 1.2** (C:335–337): for `V` open with `cl V ⊆ U` there
is a GFF plus a continuous function `Y` (namely `(h − h_ρ(w)) − g𝔥^U`, `g = 1` near `cl V`) with
`Y|_V = h̊^U|_V` a.s. and, a.s., `D_{(h − h_ρ(w)) − f}(·,·;W) = D_Y(·,·;W)` for every open
`W ⊆ V` and every continuous `f` equal to the harmonic part `𝔥^U` on `W`. -/
theorem exists_zbField {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ρ : ℝ} {w : ℂ}
    {U : Set ℂ} {hU : IsOpen U} (hUb : Bornology.IsBounded U) {X : Ω → DistC}
    (hX : IsL33ZBPart P h ρ w U hU X) (V : TopologicalSpace.Opens ℂ)
    (hVU : closure (V : Set ℂ) ⊆ U) :
    ∃ (Y : Ω → DistC) (fn : Ω → C(ℂ, ℝ)), (∀ ω, Y ω = addFun (recField h ρ w ω) (-(fn ω))) ∧
      (∀ ω, ∃ M, ∀ x, |fn ω x| ≤ M) ∧
      (∀ ω (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 U →
          (∀ φ : TestOn (toOpens U hU),
            restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
          EqOn ⇑(fn ω) 𝔥 (V : Set ℂ)) ∧
      IsGFFPlusCont Y P ∧
      (∀ᵐ ω ∂P, restrictTo V (Y ω) = restrictTo V (X ω)) ∧
      ∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U →
          (∀ φ : TestOn (toOpens U hU),
            restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
          ∀ W : Set ℂ, IsOpen W → W ⊆ V → ∀ f : C(ℂ, ℝ), EqOn ⇑f 𝔥 W → ∀ z y : ℂ,
            (D (addFun (recField h ρ w ω) (-f))).internal W z y = (D (Y ω)).internal W z y := by
  -- the bump `φ = 1` near `cl V`
  have hK : IsCompact (closure (V : Set ℂ)) :=
    (hUb.subset (subset_closure.trans hVU)).isCompact_closure
  obtain ⟨φ, U₁, δ, hφc, -, hKU₁, hφ1, hδ, hφU⟩ :=
    DFGPS.L217.exists_bump_of_isCompact hK hU hVU
  have hφU' : ∀ x, φ x ≠ 0 → closedBall x δ ⊆ (toOpens U hU : Set ℂ) := hφU
  have hVU₁ : (V : Set ℂ) ⊆ U₁ := subset_closure.trans hKU₁
  -- the random continuous function `g 𝔥^U`
  set g' : Ω → DistC := recField h ρ w with hg'
  have hg'G : IsWholePlaneGFF g' P := isWholePlaneGFF_recField hh ρ w
  set G₀ : Ω → DistC := fun ω => g' ω - X ω with hG₀
  have hG₀m : Measurable G₀ := by
    refine measurable_distOn_iff.2 fun ψ => ?_
    exact ((measurable_distOn_apply ψ).comp hg'G.measurable).sub
      ((measurable_distOn_apply ψ).comp hX.1)
  set fn : Ω → C(ℂ, ℝ) := fun ω => DFGPS.L217.harmFn φ δ hδ (G₀ ω) with hfn
  have hfnm : Measurable fn := (DFGPS.L217.measurable_harmFn φ δ hδ).comp hG₀m
  set Y : Ω → DistC := fun ω => g' ω - ofCont (fn ω) with hY
  have hYc : IsGFFPlusCont Y P := by
    obtain ⟨hm, f₀, hf₀, -, hw⟩ := DFGPS.L217.isGFFPlusBddCont_sub_ofCont hg'G hfnm
      (fun ω => DFGPS.L217.exists_bound_harmFn hφc δ hδ (G₀ ω))
    exact ⟨hm, f₀, hf₀, hw⟩
  -- `(h − h_ρ(w)) − g𝔥^U = h̊^U` on `V` (C:336), deterministic form
  have hresOf : ∀ ω (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 (toOpens U hU : Set ℂ) →
      (∀ φ : TestOn (toOpens U hU), restrictTo (toOpens U hU) (G₀ ω) φ = ∫ x, 𝔥 x * φ x) →
      restrictTo V (Y ω) = restrictTo V (X ω) := by
    intro ω 𝔥 h𝔥' hT
    ext ψ
    have e : (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) ψ : ℂ → ℝ) = ψ :=
      funext fun x => by simp [TestFunction.monoCLM_apply]
    have hψ : tsupport (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) ψ :
        ℂ → ℝ) ⊆ U₁ := by
      rw [e]; exact ψ.tsupport_subset.trans hVU₁
    exact DFGPS.L217.harmFn_sub_apply h𝔥' (hh := G₀ ω) (sub_add_cancel _ _).symm hT hδ hφU'
      hφ1 _ hψ
  have hYeq' : ∀ ω, Y ω = addFun (g' ω) (-(fn ω)) := fun ω => by
    simp only [hY, addFun, DFGPS.L217.ofCont_neg, sub_eq_add_neg]
  have hfnV : ∀ ω (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
      EqOn ⇑(fn ω) 𝔥 (V : Set ℂ) := by
    intro ω 𝔥 h𝔥 hT x hx
    have h𝔥' : InnerProductSpace.HarmonicOnNhd 𝔥 (toOpens U hU : Set ℂ) := h𝔥
    show DFGPS.L217.harmFn φ δ hδ (G₀ ω) x = 𝔥 x
    rw [DFGPS.L217.harmFn_eq_of_harmonic h𝔥' hT hδ hφU' x, hφ1 x (hVU₁ hx), one_mul]
  refine ⟨Y, fn, hYeq', fun ω => DFGPS.L217.exists_bound_harmFn hφc δ hδ (G₀ ω), hfnV, hYc,
    ?_, ?_⟩
  · obtain ⟨-, -, hh₀, hz, hdec, hXz, hharm, -, -⟩ := hX
    filter_upwards [hharm, hXz] with ω hg hXω
    obtain ⟨g, hg, hgT⟩ := hg
    refine hresOf ω g hg fun ψ => ?_
    have e : G₀ ω = hh₀ ω := by
      simp only [hG₀, hg', hdec ω, hXω, add_sub_cancel_right]
    rw [e]; exact hgT ψ
  · filter_upwards [hD.weyl P g' (GM.Tight.isGFFPlusCont_of_wp hg'G)] with ω hWω
    intro 𝔥 h𝔥 hT W hWo hWV f hfV z y
    have h𝔥' : InnerProductSpace.HarmonicOnNhd 𝔥 (toOpens U hU : Set ℂ) := h𝔥
    have hYeq : Y ω = addFun (g' ω) (-(fn ω)) := by
      simp only [hY, addFun, DFGPS.L217.ofCont_neg, sub_eq_add_neg]
    have hfeq : ∀ x ∈ W, xiGamma γ * (-f) x = xiGamma γ * (-(fn ω)) x := by
      intro x hx
      have h1 : fn ω x = φ x * 𝔥 x :=
        DFGPS.L217.harmFn_eq_of_harmonic h𝔥' hT hδ hφU' x
      simp only [ContinuousMap.neg_apply, h1, hφ1 x (hVU₁ (hWV hx)), one_mul, hfV hx]
    rw [hYeq]
    exact internal_weyl_eq_of_internal_eq hWo (fun a b => (hWω (-f) a b).symm)
      (fun a b => (hWω (-(fn ω)) a b).symm) (fun _ _ _ _ => rfl) hfeq z y

/-- **CONF Remark 1.2** (C:335–337), proved from Axioms II and III. -/
theorem confZBMetricN {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) : CONFZBMetricN D := by
  intro Ω _ P _ h hh ρ w U hU hUb X hX V hVU
  obtain ⟨Y, -, -, -, -, hYc, hres, hW⟩ := exists_zbField hD hh hUb hX V hVU
  obtain ⟨F, hFm, hF⟩ := hD.locality P Y hYc V
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hF, hres, hW] with ω hFω hrω hWω
  intro 𝔥 h𝔥 hT f _ hfV z hz y hy
  rw [hWω 𝔥 h𝔥 hT V V.isOpen subset_rfl f hfV z y, hFω z hz y hy, hrω]

end LQGMetric.CONF
