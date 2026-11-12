/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bMeas

/-!
# GM Lemma 5.4 without a measurable choice of the bump function (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 5.4, l. 2805–2835. GM use one random `φ ∈ 𝓖_r`, determined by `h|_{ℂ∖B_{3r}}`
(the hitting points chosen measurably, footnote l. 3344), and the Cameron–Martin formula
conditionally on `h|_{ℂ∖B_{3r}}`.

**Deviation (own argument, proposed DV entry).** Here every deterministic `φ ∈ 𝓖_r` is used
separately (Cameron–Martin for a fixed shift, `condExp_le_of_invTarget` with a constant `φc`) and
the events are summed: if a.s. on `X` some `φ ∈ G` puts `h − φ` in the target `T`, then
`P[X | fieldSigmaClosed0 h K] ≤ Σ_φ P[X ∩ {h − φ ∈ T} | fieldSigmaClosed0 h K] ≤ #G · Λ · P[T | fieldSigmaClosed0 h K]`. No measurable choice of hitting points
is needed; the constant is `(#G + 1) Λ` instead of `Λ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the union-bound form of the conditional Cameron–Martin comparison -/
theorem condExp_le_of_invTarget_union (hh : IsWholePlaneGFF h P) (K : Set ℂ) (G : Finset TestC)
    (hG : ∀ φ ∈ G, ∃ ε > 0, Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K))
    {T : Set DistC} (hTm : MeasurableSet T)
    (hTinv : ∀ (g : DistC) (c : ℝ), addConst g c ∈ T ↔ g ∈ T)
    {Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : ∀ φ ∈ G, ∀ g ∈ T, cmDensity (-φ) (pair0 g) ≤ Λ)
    {X Y : Set Ω} (hXm : NullMeasurableSet X P) (hY : ∀ᵐ ω ∂P, ω ∈ Y ↔ h ω ∈ T)
    (hX : ∀ᵐ ω ∂P, ω ∈ X → ∃ φ ∈ G, subTest (h ω) φ ∈ T) :
    (fun ω => (((G.card : ℝ) + 1) * Λ)⁻¹ *
        (P[X.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω) ≤ᵐ[P]
      P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] := by
  have hXX' : X =ᵐ[P] toMeasurable P X := (NullMeasurableSet.toMeasurable_ae_eq hXm).symm
  let Xφ : TestC → Set Ω := fun φ => toMeasurable P X ∩ {ω | subTest (h ω) φ ∈ T}
  have hXφm : ∀ φ, MeasurableSet (Xφ φ) := fun φ =>
    (measurableSet_toMeasurable P X).inter
      (hTm.preimage ((measurable_addFun_left _).comp hh.measurable))
  -- each fixed shift
  have hone : ∀ φ ∈ G, (fun ω => Λ⁻¹ * (P[(Xφ φ).indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω) ≤ᵐ[P]
      P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K] := by
    intro φ hφ
    refine condExp_le_of_invTarget hh K {φ} (fun ψ hψ => hG ψ (by
        rw [Finset.mem_singleton.1 hψ]; exact hφ)) (fun _ => φ) (fun _ => Finset.mem_singleton_self φ)
      (fun ψ _ => ?_) hTm hTinv hΛ0 (fun ψ hψ => by rw [Finset.mem_singleton.1 hψ]; exact hΛ φ hφ)
      (hXφm φ).nullMeasurableSet hY (Filter.Eventually.of_forall fun ω hω => hω.2)
    by_cases e : φ = ψ
    · simp only [e, ofPred_true, MeasurableSet.univ]
    · simp only [e, ofPred_false, MeasurableSet.empty]
  have hall : ∀ᵐ ω ∂P, ∀ φ ∈ G,
      Λ⁻¹ * (P[(Xφ φ).indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω ≤
        (P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω :=
    (Filter.eventually_all_finset G).2 hone
  -- the indicator of `X` is at most the sum of the indicators of the `Xφ`
  have hint : ∀ φ ∈ G, Integrable ((Xφ φ).indicator (fun _ => (1 : ℝ))) P :=
    fun φ _ => (integrable_const (1 : ℝ)).indicator (hXφm φ)
  have hle : X.indicator (fun _ => (1 : ℝ)) ≤ᵐ[P]
      ∑ φ ∈ G, (Xφ φ).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hX, hXX'] with ω hω hωe
    by_cases hωX : ω ∈ X
    · obtain ⟨φ, hφG, hφ⟩ := hω hωX
      have hω' : ω ∈ toMeasurable P X := hωe ▸ hωX
      rw [indicator_of_mem hωX, Finset.sum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun ψ =>
        (Xφ ψ).indicator (fun _ => (1 : ℝ)) ω) (fun ψ _ => indicator_nonneg
          (fun _ _ => zero_le_one) ω) hφG)
      rw [indicator_of_mem (show ω ∈ Xφ φ from ⟨hω', hφ⟩)]
    · rw [indicator_of_notMem hωX, Finset.sum_apply]
      exact Finset.sum_nonneg fun ψ _ => indicator_nonneg (fun _ _ => zero_le_one) ω
  have hmono := condExp_mono (m := fieldSigmaClosed0 h K) ((integrable_const (1 : ℝ)).indicator
    (measurableSet_toMeasurable P X) |>.congr (indicator_ae_eq_of_ae_eq_set hXX'.symm))
    (integrable_finsetSum' G hint) hle
  have hsum := condExp_finsetSum hint (fieldSigmaClosed0 h K)
  have hnn := condExp_nonneg (m := fieldSigmaClosed0 h K) (μ := P)
    (f := Y.indicator (fun _ => (1 : ℝ)))
    (Filter.Eventually.of_forall fun ω => indicator_nonneg (fun _ _ => zero_le_one) ω)
  filter_upwards [hall, hmono, hsum, hnn] with ω h1 h2 h3 h4
  rw [h3, Finset.sum_apply] at h2
  have h4' : 0 ≤ (P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω := h4
  have hcard : (0 : ℝ) < ((G.card : ℝ) + 1) * Λ := by positivity
  rw [inv_mul_le_iff₀ hcard]
  have h5 : ∀ φ ∈ G, (P[(Xφ φ).indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω ≤
      Λ * (P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω := by
    intro φ hφ
    have := h1 φ hφ
    rwa [inv_mul_le_iff₀ hΛ0] at this
  have h6 := Finset.sum_le_sum h5
  rw [Finset.sum_const, nsmul_eq_mul] at h6
  have h7 : (G.card : ℝ) * (Λ * (P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω) ≤
      ((G.card : ℝ) + 1) * Λ * (P[Y.indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω := by
    nlinarith [mul_nonneg hΛ0.le h4']
  linarith

/-- (5.7) in the union-bound form: a.s. on `E ∩ {P ∩ B_{2r}(z) ≠ ∅}` some `φ ∈ G` puts `h − φ` in
`constCore 𝔈_r^{𝕫,𝕨}(z)` -/
theorem ae_exists_subTest_mem_constCore_frkE {γ : ℝ} {D D' : DistC → ContMetric}
    {c₀ c₀' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (hselm : ∀ a b : ℂ, Measurable (sel a b))
    (hgeo : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ a b : ℂ, a ≠ b →
        ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω)))
    {cs Cs c₂ b₀ Λ₀ r : ℝ} (G : Finset TestC) (z : ℂ) {a b : ℂ} (hab : a ≠ b) (E : Set DistC)
    (hB : ∀ g ∈ E, ∀ ψ ∈ G, |dirInner g ψ| + gradEnergy ψ / 2 ≤ Λ₀)
    (hh : IsWholePlaneGFF h P)
    (hC : ∀ᵐ ω ∂P, h ω ∈ E → (range (sel a b (h ω)) ∩ Metric.ball z (2 * r)).Nonempty →
      ∃ φ ∈ G, ∀ Qφ : C(unitInterval, ℂ), IsGeod01 (D (subTest (h ω) φ)) a b Qφ →
        frkDist D D' cs Cs c₂ b₀ r z (subTest (h ω) φ) Qφ) :
    ∀ᵐ ω ∂P, h ω ∈ E → (range (sel a b (h ω)) ∩ Metric.ball z (2 * r)).Nonempty →
      ∃ φ ∈ G, subTest (h ω) φ ∈
        constCore (frkE D D' sel cs Cs c₂ b₀ (Real.exp (3 * Λ₀)) r (G : Set TestC) z a b) := by
  have hgeoG : ∀ᵐ ω ∂P, ∀ φ ∈ G,
      IsGeod01 (D (subTest (h ω) φ)) a b (sel a b (subTest (h ω) φ)) := by
    refine (Filter.eventually_all_finset G).2 fun φ _ => ?_
    simpa only [subTest_eq_addFun_neg_cm] using
      ae_isGeod_sel_addFun hD hsel hselm hgeo hh (-φ) hab
  have hscD : ∀ᵐ ω ∂P, ∀ φ ∈ G, ∀ (c : ℝ) (u v : ℂ),
      (D (addConst (subTest (h ω) φ) c)).1 (u, v) =
        Real.exp (xiGamma γ * c) * (D (subTest (h ω) φ)).1 (u, v) := by
    refine (Filter.eventually_all_finset G).2 fun φ _ => ?_
    simpa only [subTest_eq_addFun_neg_cm] using
      hD.ae_dist_addConst (isGFFPlusCont_addFun_test hh (-φ))
  have hscD' : ∀ᵐ ω ∂P, ∀ φ ∈ G, ∀ (c : ℝ) (u v : ℂ),
      (D' (addConst (subTest (h ω) φ) c)).1 (u, v) =
        Real.exp (xiGamma γ * c) * (D' (subTest (h ω) φ)).1 (u, v) := by
    refine (Filter.eventually_all_finset G).2 fun φ _ => ?_
    simpa only [subTest_eq_addFun_neg_cm] using
      hD'.ae_dist_addConst (isGFFPlusCont_addFun_test hh (-φ))
  filter_upwards [hgeoG, hscD, hscD', hC] with ω hg h1 h2 hCω hE hhit
  obtain ⟨φ, hφ, hφC⟩ := hCω hE hhit
  refine ⟨φ, hφ, fun c => ?_⟩
  have hmem : subTest (h ω) φ ∈
      frkE D D' sel cs Cs c₂ b₀ (Real.exp (3 * Λ₀)) r (G : Set TestC) z a b :=
    ⟨hφC _ (hg _ hφ), fun _ hψ => exp_dir_subTest_le (fun ψ hψ => hB _ hE ψ hψ)
      (show φ ∈ (G : Set TestC) from hφ) hψ⟩
  exact (frkE_addConst_iff hsel (h1 _ hφ c) (h2 _ hφ c)).2 hmem

/-- **GM Lemma 5.4** (l. 2792–2835), union-bound form: condition (4) of `GeoIterateHyp` at
`(z, r, 𝕫, 𝕨)` (`λ₂ = 2`, `λ₃ = 3`) with `Λ = (#G + 1) e^{3Λ₀}` and
`𝔈 = constCore 𝔈_r^{𝕫,𝕨}(z)`. Inputs: Prop 5.2 (B) on `E`, measurability of `E`, and (C) in the
form "a.s. on `E ∩ {P ∩ B_{2r}(z) ≠ ∅}` some `φ ∈ G` forces (5.4) for every `D_{h−φ}`-geodesic". -/
theorem gm_L5_4_union_at {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (hselm : ∀ a b : ℂ, Measurable (sel a b))
    (hgeo : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ a b : ℂ, a ≠ b →
        ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω)))
    {cs Cs c₂ b₀ Λ₀ r : ℝ} (hr : 0 < r) (G : Finset TestC) (z : ℂ) {a b : ℂ} (hab : a ≠ b)
    (hGsupp : ∀ φ ∈ G, tsupport (φ : ℂ → ℝ) ⊆ Metric.ball z (3 * r)) (E : Set DistC)
    (hB : ∀ g ∈ E, ∀ ψ ∈ G, |dirInner g ψ| + gradEnergy ψ / 2 ≤ Λ₀)
    (hh : IsWholePlaneGFF h P) (hEm : NullMeasurableSet (h ⁻¹' E) P)
    (hC : ∀ᵐ ω ∂P, h ω ∈ E → (range (sel a b (h ω)) ∩ Metric.ball z (2 * r)).Nonempty →
      ∃ φ ∈ G, ∀ Qφ : C(unitInterval, ℂ), IsGeod01 (D (subTest (h ω) φ)) a b Qφ →
        frkDist D D' cs Cs c₂ b₀ r z (subTest (h ω) φ) Qφ) :
    (fun ω => (((G.card : ℝ) + 1) * Real.exp (3 * Λ₀))⁻¹ *
        (P[(h ⁻¹' E ∩ {ω | (range (sel a b (h ω)) ∩ Metric.ball z (2 * r)).Nonempty}).indicator
          (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (3 * r))ᶜ]) ω) ≤ᵐ[P]
      P[(h ⁻¹' constCore (frkE D D' sel cs Cs c₂ b₀ (Real.exp (3 * Λ₀)) r (G : Set TestC) z a b) ∩
          {ω | (range (sel a b (h ω)) ∩ Metric.ball z (2 * r)).Nonempty}).indicator
        (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (3 * r))ᶜ] := by
  set F := frkE D D' sel cs Cs c₂ b₀ (Real.exp (3 * Λ₀)) r (G : Set TestC) z a b with hFdef
  set H : Set DistC := {g | (range (sel a b g) ∩ Metric.ball z (2 * r)).Nonempty} with hHdef
  have hFm : MeasurableSet F :=
    measurableSet_frkE hD.measurable hD'.measurable (hselm a b) _ _ _ _ _ _ G z
  have hHinv : ∀ g c, addConst g c ∈ H ↔ g ∈ H := fun g c => by
    simp only [hHdef, mem_ofPred_eq, hsel]
  set T : Set DistC := normPsi ⁻¹' (F ∩ H) with hTdef
  have hTm : MeasurableSet T :=
    measurable_normPsi (hFm.inter (measurableSet_hitSet (hselm a b) _ _))
  have hTinv : ∀ (g : DistC) (c : ℝ), addConst g c ∈ T ↔ g ∈ T := fun g c => by
    simp only [hTdef, mem_preimage, normPsi_addConst]
  have hTΛ : ∀ φ ∈ G, ∀ g ∈ T, cmDensity (-φ) (pair0 g) ≤ Real.exp (3 * Λ₀) := by
    intro φ hφ g hg
    have h1 := cmDensity_neg_le_of_frkE hg.1 (show φ ∈ (G : Set TestC) from hφ)
    rw [cmDensity_neg_pair0] at h1 ⊢
    rwa [normPsi, dirInner_addConst] at h1
  have hG : ∀ φ ∈ G, ∃ ε > 0,
      Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε (Metric.ball z (3 * r))ᶜ) :=
    fun φ hφ => exists_disjoint_thickening_compl (φ.hasCompactSupport.isCompact)
      Metric.isOpen_ball (hGsupp φ hφ)
  have hXm : NullMeasurableSet (h ⁻¹' E ∩ h ⁻¹' H) P :=
    hEm.inter ((measurableSet_hitSet (hselm a b) z (2 * r)).preimage
      hh.measurable).nullMeasurableSet
  have hinvF := ae_frkE_addConst_iff hD hD' hsel cs Cs c₂ b₀ (Real.exp (3 * Λ₀)) r
    (G : Set TestC) z a b hh
  have hX := ae_exists_subTest_mem_constCore_frkE hD hD' hsel hselm hgeo G z hab E hB hh hC
  refine condExp_le_of_invTarget_union hh _ G hG hTm hTinv (Real.exp_pos _) hTΛ hXm ?_ ?_
  · filter_upwards [hinvF] with ω hω
    show h ω ∈ constCore F ∧ h ω ∈ H ↔ normPsi (h ω) ∈ F ∧ normPsi (h ω) ∈ H
    rw [constCore_eq_of_inv hω, normPsi, hω, hHinv]
  · filter_upwards [hX] with ω hω hωX
    obtain ⟨φ, hφ, hc⟩ := hω hωX.1 hωX.2
    have hF : normPsi (subTest (h ω) φ) ∈ F := hc _
    exact ⟨φ, hφ, hF, hit_of_frkDist hr hF.1⟩

end LQGMetric.GM
