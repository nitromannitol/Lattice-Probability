/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CaraExtCurve at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# EXT-CA C3 (curve part): continuous extension of finite-length curves; semicircle increments

Two elementary facts used in node C3 of `blueprint/EXT_CA_BLUEPRINT.md` (Carathéodory boundary
theory), together with Wolff's length–area lemma `exists_short_semicircle`
(`QuantumZipper/Proofs/Complex/CarLengthArea.lean`):

* `exists_extend_Icc_of_lintegral`: a curve on `(a,b)` whose increments are dominated by the
  integral of a density with finite total integral has a continuous extension to `[a,b]`, whose
  increments are bounded by the total integral. Own elementary proof (standard fact; cost rule of
  `AGENT_GUIDE.md`): the density measure `ν` has no atoms, so `ν (closedBall x τ) → 0`, the image
  filter `map c (𝓝[(a,b)] x)` is Cauchy, and `extendFrom` gives the extension.
* `enorm_sub_le_lintegral_semicircle`: the increment of a holomorphic `ψ` along the semicircle
  `x₀ + r e^{iθ}` is bounded by the length integral `∫⁻ ‖ψ'(x₀ + r e^{iθ})‖ r dθ`. Own elementary
  proof: fundamental theorem of calculus for `ψ ∘ γ`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

open scoped ENNReal NNReal Real

namespace QuantumZipper.CA.Car

/-- A curve on `(a,b)` whose increments are bounded by the integral of a density `g` with finite
total integral extends continuously to `[a,b]`, with all increments bounded by the total. -/
theorem exists_extend_Icc_of_lintegral {c : ℝ → ℂ} {g : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn c (Ioo a b))
    (hlen : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s ≤ t → ‖c t - c s‖ₑ ≤ ∫⁻ θ in Ioc s t, g θ)
    (hfin : ∫⁻ θ in Ioo a b, g θ < ⊤) :
    ∃ cb : ℝ → ℂ, ContinuousOn cb (Icc a b) ∧ EqOn cb c (Ioo a b) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖cb t - cb s‖ₑ ≤ ∫⁻ θ in Ioo a b, g θ := by
  set ν : Measure ℝ := (volume.restrict (Ioo a b)).withDensity g with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin.ne
  -- increments inside `(a,b)` are bounded by `ν` of any closed interval containing them
  have hinc : ∀ u ∈ Ioo a b, ∀ v ∈ Ioo a b, ∀ S : Set ℝ, MeasurableSet S →
      Icc u v ⊆ S → Icc v u ⊆ S → edist (c u) (c v) ≤ ν S := by
    intro u hu v hv S hS huv hvu
    have hνS : ν S = ∫⁻ θ in S ∩ Ioo a b, g θ := by
      rw [hν, withDensity_apply _ hS, Measure.restrict_restrict hS]
    rw [hνS, edist_eq_enorm_sub]
    rcases le_total u v with h | h
    · rw [← enorm_neg, neg_sub]
      refine (hlen u hu v hv h).trans (lintegral_mono_set ?_)
      exact subset_inter (Ioc_subset_Icc_self.trans huv)
        (fun θ hθ => ⟨hu.1.trans hθ.1, hθ.2.trans_lt hv.2⟩)
    · refine (hlen v hv u hu h).trans (lintegral_mono_set ?_)
      exact subset_inter (Ioc_subset_Icc_self.trans hvu)
        (fun θ hθ => ⟨hv.1.trans hθ.1, hθ.2.trans_lt hu.2⟩)
  -- limits exist at every point of `[a,b]`
  have hlim : ∀ x ∈ Icc a b, ∃ y, Tendsto c (𝓝[Ioo a b] x) (𝓝 y) := by
    intro x hx
    have : NeBot (𝓝[Ioo a b] x) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hab.ne]; exact hx
    have hx0 : ν {x} = 0 :=
      withDensity_absolutelyContinuous _ _ (by
        rw [Measure.restrict_apply (measurableSet_singleton x)]
        exact measure_mono_null inter_subset_left (measure_singleton x))
    have htend : Tendsto (fun τ => ν (cthickening τ {x})) (𝓝 0) (𝓝 (ν {x})) :=
      tendsto_measure_cthickening_of_isClosed ⟨1, one_pos, measure_ne_top _ _⟩ isClosed_singleton
    have hcau : Cauchy (map c (𝓝[Ioo a b] x)) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ν (cthickening τ {x}) < ENNReal.ofReal ε ∧ 0 < τ :=
        ((htend.mono_left nhdsWithin_le_nhds).eventually
          (gt_mem_nhds (by rw [hx0]; exact ENNReal.ofReal_pos.2 hε))).and self_mem_nhdsWithin
      obtain ⟨τ, hτ, hτ0⟩ := hev.exists
      rw [cthickening_singleton x hτ0.le] at hτ
      refine ⟨c '' (Ioo a b ∩ closedBall x τ), ?_, ?_⟩
      · rw [mem_map]
        refine mem_of_superset ?_ (subset_preimage_image c _)
        exact inter_mem_nhdsWithin _ (closedBall_mem_nhds x hτ0)
      · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
        rw [← edist_lt_ofReal]
        refine lt_of_le_of_lt (hinc u hu.1 v hv.1 _ measurableSet_closedBall ?_ ?_) hτ
        · exact (convex_closedBall x τ).ordConnected.out hu.2 hv.2
        · exact (convex_closedBall x τ).ordConnected.out hv.2 hu.2
    obtain ⟨y, hy⟩ := CompleteSpace.complete hcau
    exact ⟨y, hy⟩
  refine ⟨extendFrom (Ioo a b) c, continuousOn_extendFrom (closure_Ioo hab.ne).ge hlim,
    extendFrom_extends hc, ?_⟩
  have hcont : ContinuousOn (extendFrom (Ioo a b) c) (Icc a b) :=
    continuousOn_extendFrom (closure_Ioo hab.ne).ge hlim
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => edist (extendFrom (Ioo a b) c p.1) (extendFrom (Ioo a b) c p.2)
  have hclo : closure (Ioo a b ×ˢ Ioo a b) = Icc a b ×ˢ Icc a b := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
  have hF : ContinuousOn F (closure (Ioo a b ×ˢ Ioo a b)) := by
    rw [hclo]
    exact continuous_edist.comp_continuousOn
      ((hcont.comp continuousOn_fst (fun p (hp : p ∈ Icc a b ×ˢ Icc a b) => hp.1)).prodMk
        (hcont.comp continuousOn_snd (fun p (hp : p ∈ Icc a b ×ˢ Icc a b) => hp.2)))
  have himg : F '' (Ioo a b ×ˢ Ioo a b) ⊆ Iic (∫⁻ θ in Ioo a b, g θ) := by
    rintro _ ⟨p, hp, rfl⟩
    simp only [F, mem_Iic, extendFrom_extends hc _ hp.1, extendFrom_extends hc _ hp.2]
    have := hinc p.1 hp.1 p.2 hp.2 univ MeasurableSet.univ (subset_univ _) (subset_univ _)
    rwa [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  intro s hs t ht
  have hmem : F (t, s) ∈ Iic (∫⁻ θ in Ioo a b, g θ) :=
    (isClosed_Iic.closure_subset_iff.2 himg) (hF.image_closure (mem_image_of_mem F
      (by rw [hclo]; exact ⟨ht, hs⟩)))
  rw [← edist_eq_enorm_sub]
  exact hmem

theorem semicircle_mem_H (x₀ : ℝ) {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 π) :
    ((x₀ : ℂ) + r * Complex.exp (θ * Complex.I)) ∈ QuantumZipper.H := by
  show 0 < ((x₀ : ℂ) + r * Complex.exp (θ * Complex.I)).im
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, zero_add, add_zero]
  exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

/-- Increments of `ψ` along the semicircle `x₀ + r e^{iθ}` are bounded by its length. -/
theorem enorm_sub_le_lintegral_semicircle {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ QuantumZipper.H)
    (x₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ s ∈ Ioo 0 π, ∀ t ∈ Ioo 0 π, s ≤ t →
      ‖ψ (x₀ + r * Complex.exp (t * Complex.I)) - ψ (x₀ + r * Complex.exp (s * Complex.I))‖ₑ ≤
        ∫⁻ θ in Ioc s t, ‖deriv ψ (x₀ + r * Complex.exp (θ * Complex.I))‖ₑ * ENNReal.ofReal r := by
  intro s hs t ht hst
  set γ : ℝ → ℂ := fun θ => (x₀ : ℂ) + r * Complex.exp (θ * Complex.I) with hγdef
  set γ' : ℝ → ℂ := fun θ => (r : ℂ) * (Complex.exp (θ * Complex.I) * Complex.I) with hγ'def
  have hγ : ∀ θ : ℝ, HasDerivAt γ (γ' θ) θ := by
    intro θ
    have h1 := (((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp).comp_ofReal
    simp only [id, one_mul] at h1
    exact (h1.const_mul (r : ℂ)).const_add (x₀ : ℂ)
  have hsub : uIcc s t ⊆ Ioo 0 π := by
    rw [uIcc_of_le hst]; exact Icc_subset_Ioo hs.1 ht.2
  have hγH : ∀ θ ∈ uIcc s t, γ θ ∈ QuantumZipper.H := fun θ hθ =>
    semicircle_mem_H x₀ hr (hsub hθ)
  have hdcont : ContinuousOn (deriv ψ) QuantumZipper.H :=
    (hψ.analyticOnNhd QuantumZipper.isOpen_H).deriv.continuousOn
  have hderiv : ∀ θ ∈ uIcc s t, HasDerivAt (ψ ∘ γ) (deriv ψ (γ θ) * γ' θ) θ := fun θ hθ =>
    ((hψ.differentiableAt (QuantumZipper.isOpen_H.mem_nhds (hγH θ hθ))).hasDerivAt).comp θ (hγ θ)
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun θ => (hγ θ).continuousAt
  have hγ'c : Continuous γ' := by fun_prop
  have hint : IntervalIntegrable (fun θ => deriv ψ (γ θ) * γ' θ) volume s t :=
    ContinuousOn.intervalIntegrable
      ((hdcont.comp hγc.continuousOn hγH).mul hγ'c.continuousOn)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le hst] at hftc
  have hnorm : ∀ θ : ℝ, ‖deriv ψ (γ θ) * γ' θ‖ₑ = ‖deriv ψ (γ θ)‖ₑ * ENNReal.ofReal r := by
    intro θ
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm, hγ'def]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, mul_one]
  calc ‖ψ (γ t) - ψ (γ s)‖ₑ = ‖∫ θ in Ioc s t, deriv ψ (γ θ) * γ' θ‖ₑ := by
        rw [hftc]; rfl
    _ ≤ ∫⁻ θ in Ioc s t, ‖deriv ψ (γ θ) * γ' θ‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ θ in Ioc s t, ‖deriv ψ (γ θ)‖ₑ * ENNReal.ofReal r := by simp_rw [hnorm]

end QuantumZipper.CA.Car
