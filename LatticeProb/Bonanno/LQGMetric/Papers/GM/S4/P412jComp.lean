/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412jComp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodP412
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4Meas

/-!
# D70 completion transfer for GM Proposition 4.12 (`GMP4_12AtC → GMP4_12At`)

Source: decision D70 / DEC-47 (complete space, completion transfer); GM (arXiv:1905.00383v3)
Prop 4.12 (`prop-stab`, l. 2022–2024). The proof of Prop 4.12 (L4.15 Step 4, D98 §2) uses the
filtration `ℱ k = ⨆_{j ≤ k} gmAESigma σ(𝓑^•_{t_j}, h|) P`, which is a sub-σ-algebra only on a
complete space. `GMP4_12AtC` is `GMP4_12At` restricted to complete probability spaces;
`p412j_P4_12At_of_complete` removes the restriction.

The only dependence of `p412Bad` on the measure `P` is through the harmonic parts `harmPart P h U`
in the CONF events `E_r(z)` (`confE`, via `confRho` in conditions 6–7 of `ℰ_𝕣`). Conditional
expectations are unchanged by completion (`p412j_condExp_completion`, own routine argument:
`ae_eq_condExp_of_forall_setIntegral_eq` with the set integrals of `gm_integral_completion`), so
`IsHarmPart` and `harmPart` are unchanged (`p412j_harmPart_completion`), hence `confE`, `confRho`,
`regEvent`, `p412Bad` (`p412j_p412Bad_completion`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem p412j_le_null : mΩ ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
  fun s hs => (hs.nullMeasurableSet : NullMeasurableSet s P)

/-- set integrals over `mΩ`-measurable sets are unchanged by completion -/
theorem p412j_setIntegral_completion (g : Ω → ℝ) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g (gm_ofNull P x) ∂(P.completion) = ∫ x in s, g x ∂P := by
  have h1 : ∫ x in s, g (gm_ofNull P x) ∂(P.completion) =
      ∫ x, s.indicator g (gm_ofNull P x) ∂(P.completion) :=
    (integral_indicator (μ := P.completion) (f := fun x => g (gm_ofNull P x))
      (p412j_le_null s hs)).symm
  rw [h1, gm_integral_completion, integral_indicator hs]

/-- integrability is unchanged by completion -/
theorem p412j_integrable_completion (f : Ω → ℝ) :
    Integrable (f ∘ gm_ofNull P) P.completion ↔ Integrable f P := by
  constructor
  · intro hf
    have hm2 : Measurable (hf.1.mk _) := hf.1.stronglyMeasurable_mk.measurable
    have hfa : AEStronglyMeasurable f P :=
      ((NullMeasurable.aemeasurable (μ := P) hm2).congr hf.1.ae_eq_mk.symm).aestronglyMeasurable
    have := (integrable_map_measure (f := gm_ofNull P) (μ := P.completion) (g := f)
      (by rw [gm_map_ofNull]; exact hfa) gm_measurable_ofNull.aemeasurable).2 hf
    rwa [gm_map_ofNull] at this
  · intro hf
    rw [← gm_map_ofNull (P := P)] at hf
    exact hf.comp_measurable gm_measurable_ofNull

/-- `σ(h|_V mod const) ≤ mΩ` for a measurable field -/
theorem p412j_fieldSigma0On_le {h : Ω → DistC} (hmh : Measurable h) (V : Set ℂ) :
    fieldSigma0On h V ≤ mΩ := by
  have hf : Measurable fun ω (ψ : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ V}) => h ω ψ.1.1 :=
    measurable_pi_iff.2 fun ψ => (measurable_evalDist ψ.1.1).comp hmh
  exact hf.comap_le

/-- **conditional expectations given `σ(h|_K mod const)` are unchanged by completion** (D110) -/
theorem p412j_condExp_completion0 [IsProbabilityMeasure P] {h : Ω → DistC} (hmh : Measurable h)
    (K : Set ℂ) (f : Ω → ℝ) :
    (P.completion[f ∘ gm_ofNull P | fieldSigmaClosed0 h K] : Ω → ℝ) =ᵐ[P]
      P[f | fieldSigmaClosed0 h K] := by
  have hm : fieldSigmaClosed0 h K ≤ mΩ :=
    (iInf₂_le (1 : ℝ) one_pos).trans (p412j_fieldSigma0On_le hmh _)
  have hm' : fieldSigmaClosed0 h K ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
    hm.trans p412j_le_null
  haveI : IsFiniteMeasure (P.completion.trim hm') := isFiniteMeasure_trim (μ := P.completion) hm'
  have hsf : SigmaFinite (P.completion.trim hm') := IsFiniteMeasure.toSigmaFinite _
  by_cases hf : Integrable f P
  · have hf' := (p412j_integrable_completion (P := P) f).2 hf
    have key := ae_eq_condExp_of_forall_setIntegral_eq (μ := P.completion) hm' hf'
      (g := P[f | fieldSigmaClosed0 h K]) (fun s _ _ =>
        ((p412j_integrable_completion (P := P) (P[f | fieldSigmaClosed0 h K])).2
        integrable_condExp).integrableOn) (fun s hs _ =>
          (p412j_setIntegral_completion (P := P) (P[f | fieldSigmaClosed0 h K]) (hm s hs)).trans
            ((setIntegral_condExp hm hf hs).trans
              (p412j_setIntegral_completion (P := P) f (hm s hs)).symm))
      stronglyMeasurable_condExp.aestronglyMeasurable
    exact key.symm
  · have h1 := condExp_of_not_integrable (μ := P.completion)
      (m := fieldSigmaClosed0 h K)
      (mt (p412j_integrable_completion (P := P) f).1 hf)
    have h2 := condExp_of_not_integrable (μ := P) (m := fieldSigmaClosed0 h K) hf
    exact Eventually.of_forall fun ω => (congrFun h1 ω).trans (congrFun h2 ω).symm

variable [IsProbabilityMeasure P] {h : Ω → DistC}

theorem p412j_isHarmPart_completion (hm : Measurable h) (U : Set ℂ) (H : Ω → ℂ → ℝ) :
    IsHarmPart P.completion (h ∘ gm_ofNull P) U H ↔ IsHarmPart P h U H := by
  unfold IsHarmPart
  refine and_congr Iff.rfl (forall_congr' fun φ => forall_congr' fun ψ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_)
  have e := p412j_condExp_completion0 (P := P) hm Uᶜ (fun ω => h ω (φ - (∫ x, φ x) • ψ))
  exact ⟨fun h1 => e.symm.trans h1, fun h1 => e.trans h1⟩

open Classical in
theorem p412j_dite_choose {α : Type} {p q : α → Prop} (hpq : p = q) (d : α) :
    (if hp : ∃ x, p x then hp.choose else d) = (if hq : ∃ x, q x then hq.choose else d) := by
  subst hpq; rfl

theorem p412j_harmPart_completion (hm : Measurable h) (U : Set ℂ) :
    harmPart P.completion (h ∘ gm_ofNull P) U =
      @harmPart Ω mΩ P h U := by
  have e : IsHarmPart P.completion (h ∘ gm_ofNull P) U = IsHarmPart P h U :=
    funext fun H => propext (p412j_isHarmPart_completion hm U H)
  unfold harmPart
  exact p412j_dite_choose e _

theorem p412j_confE_completion (hm : Measurable h) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (p : CONFParams) (r : ℝ) (z : ℂ) :
    confE ξ cc D P.completion (h ∘ gm_ofNull P) p r z =
      @confE Ω mΩ ξ cc D P h p r z := by
  simp only [confE, confEU, p412j_harmPart_completion hm]
  rfl

theorem p412j_confRho_completion (hm : Measurable h) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (p : CONFParams) (R : ℝ) (z : ℂ) :
    ∀ n, confRho ξ cc D P.completion (h ∘ gm_ofNull P) p R z n =
      @confRho Ω mΩ ξ cc D P h p R z n
  | 0 => rfl
  | n + 1 => by
    funext ω
    simp only [confRho, p412j_confRho_completion hm ξ cc D p R z n, p412j_confE_completion hm]
    rfl

theorem p412j_regEvent_completion (hm : Measurable h) (D : DistC → ContMetric)
    (H : ℝ → ℂ → Ω → ℝ) (R : RegPar) (𝕣 a : ℝ) :
    regEvent D P.completion (h ∘ gm_ofNull P) H R 𝕣 a =
      @regEvent Ω mΩ D P h H R 𝕣 a := by
  simp only [regEvent, regC6, regC7, confRegH, p412j_confRho_completion hm]
  rfl

theorem p412j_p412Bad_completion (hm : Measurable h) (D : DistC → ContMetric)
    (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) (H : ℝ → ℂ → Ω → ℝ) (R : RegPar) (𝕫 𝕨 : ℂ)
    (𝕣 a ε β θ : ℝ) :
    p412Bad D sel P.completion (h ∘ gm_ofNull P) H R 𝕫 𝕨 𝕣 a ε β θ =
      @p412Bad Ω mΩ D sel P h H R 𝕫 𝕨 𝕣 a ε β θ := by
  simp only [p412Bad, p412j_regEvent_completion hm]
  rfl

/-- `GMP4_12At` restricted to complete probability spaces (D70) -/
def GMP4_12AtC (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (cp : CONFParams) (χ χ' : ℝ)
    (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) : Prop :=
  ∃ β θ : ℝ, β ∈ Ioo (0 : ℝ) 1 ∧ θ ∈ Ioo (0 : ℝ) 1 ∧ β < χ / χ' ∧
  ∀ R : RegPar, R.ξ = xiGamma γ → R.c = c → R.p = cp → R.χ = χ → R.χ' = χ' →
  0 < R.lam 0 → R.lam 0 < R.lam 1 → R.lam 1 ≤ R.lam 2 → R.lam 2 ≤ R.lam 3 → 1 < R.lam 3 →
  R.lam 3 < R.lam 4 → 0 < R.μ → R.μ < R.ν → R.ℓ ∈ Ioo (0 : ℝ) 1 → R.U ⊆ R.V →
  Bornology.IsBounded R.V →
  ∀ a ∈ Ioo (0 : ℝ) 1, a ≤ R.ℓ → ∀ M : ℝ, 0 < M → ∃ C ε₀ : ℝ, 0 < ε₀ ∧
  ∀ (E : ℝ → ℂ → Set DistC) (rr : ℝ → ℝ → ℕ → ℝ),
  (∀ 𝕣 > 0, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ k < ⌊R.μ * Real.logb 8 ε⁻¹⌋₊,
    rr 𝕣 ε k ∈ Icc (ε ^ (1 + R.ν) * 𝕣) (ε * 𝕣)) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (h : Ω → DistC), IsWholePlaneGFF h P →
    (∀ x y : ℂ, x ≠ y → ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) x y (sel x y (h ω))) →
    ∀ H : ℝ → ℂ → Ω → ℝ, DFGPS.IsCircleAvgVersion h P H →
    ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ 𝕫 ∈ rScale 𝕣 R.U, ∀ 𝕨 ∈ rScale 𝕣 R.U, 4 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
    ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₀ →
      P (p412Bad D sel P h H { R with E := E, rr := rr } 𝕫 𝕨 𝕣 a ((2 : ℝ)⁻¹ ^ n) β θ) ≤
        ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ n) ^ M)

/-- **D70 completion transfer**: Proposition 4.12 on complete spaces gives it on all spaces -/
theorem p412j_P4_12At_of_complete {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    {cp : CONFParams} {χ χ' : ℝ} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (Hc : GMP4_12AtC γ D c cp χ χ' sel) : GMP4_12At γ D c cp χ χ' sel := by
  obtain ⟨β, θ, hβ, hθ, hβχ, Hc⟩ := Hc
  refine ⟨β, θ, hβ, hθ, hβχ, fun R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 a ha haℓ
    M hM => ?_⟩
  obtain ⟨C, ε₀, hε₀, HC⟩ := Hc R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 a ha haℓ
    M hM
  refine ⟨C, ε₀, hε₀, fun E rr hrr Ω _ P _ h hh hgeo H hH 𝕣 h𝕣 𝕫 h𝕫 𝕨 h𝕨 hzw n hn => ?_⟩
  have hb := HC E rr hrr P.completion (h ∘ gm_ofNull P) (gm_isWholePlaneGFF_completion hh)
    (fun x y hxy => hgeo x y hxy) H ⟨hH.cont, fun r hr z => hH.ae_eq r hr z⟩ 𝕣 h𝕣 𝕫 h𝕫 𝕨 h𝕨
    hzw n hn
  rw [p412j_p412Bad_completion hh.measurable] at hb
  exact hb

end LQGMetric.GM
