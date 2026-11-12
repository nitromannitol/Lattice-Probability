/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108P2C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2B
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine

/-!
# CONF Lemma 3.3, Step 2, uniformly over the scale (D108 packet P2)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, Step 2 of Lemma 3.3 (C:1226–1234): "Let
`U₀ := r⁻¹(U − z) ∈ 𝒰_1(0)` and let `g₀` be a smooth compactly supported bump function on `U₀` …
`g(·) = g₀(r⁻¹(· − z))`. Then the Dirichlet energy of `g` equals the Dirichlet energy of `g₀`,
which depends only on `U₀` … `P[G^U]` is bounded below by a constant depending only on
`U₀, δ, c, A`."

* `zsSub_affine` : `g = g₀ ∘ A⁻¹` is in `C_c^∞(rU₀ + z)` with the same Dirichlet energy (QZ
  `K3.dirichletEnergyOn_eq_of_eqOn_comp`, conformal invariance; `isConformalOnto_affFwd`);
* `zb_step2_uniform` : for unit-scale data `K₀ i ⊆ W₀ i ⊆ V₀ ⋐ U₀` and constants `C, s > 0`
  there is `𝔭 > 0` (depending only on these) such that for every scale `r`, centre `z`, field
  `h`, version `X` of `h̊^{rU₀+z}` and threshold `ℓ > 0`: if (3.12) holds in the form
  `P[∀ i, diam(rK₀ i + z; D_{h̊}(·,·; rW₀ i + z)) ≤ C ℓ] ≥ 1/2`, then
  `P[∀ i, diam(…) ≤ s ℓ] ≥ 𝔭` (with `D_{h̊}` realized by the field `Y` of `exists_zbField`).
  CONF uses `ℓ = 𝔠_r`, `s = (c/100) e^{−ξA}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **The scaled bump** (C:1227–1228): `g = g₀((· − z)/r)` is in `C_c^∞(rU₀ + z)` and has the
Dirichlet energy of `g₀`. -/
theorem zsSub_affine {r : ℝ} (hr : r ≠ 0) (z : ℂ) {U₀ : Opens ℂ}
    (f₀ : MarkovZB.zsSub (U₀ : Set ℂ)) :
    ∃ f : MarkovZB.zsSub (affOpens r z U₀ : Set ℂ), (∀ x, f.1 x = f₀.1 (affMap r z x)) ∧
      QuantumZipper.dirichletEnergyOn (affOpens r z U₀ : Set ℂ) f.1 =
        QuantumZipper.dirichletEnergyOn (U₀ : Set ℂ) f₀.1 := by
  have h0 : f₀.1 ∈ QuantumZipper.zeroSpace (U₀ : Set ℂ) := f₀.2
  have hmem : (f₀.1 ∘ affMap r z) ∈ QuantumZipper.zeroSpace (affOpens r z U₀ : Set ℂ) :=
    ⟨contDiff_comp_affMap r z h0.1, hasCompactSupport_comp_affMap r z hr h0.2.1,
      (tsupport_comp_subset_preimage _ (continuous_affMap r z)).trans (preimage_mono h0.2.2)⟩
  refine ⟨⟨_, hmem⟩, fun x => rfl, ?_⟩
  symm
  exact QuantumZipper.K3.dirichletEnergyOn_eq_of_eqOn_comp (isConformalOnto_affFwd hr U₀) h0.1
    hmem.1 (fun y _ => by show f₀.1 y = f₀.1 (affMap r z (affFwd r z y)); rw [affMap_affFwd hr])

/-- **CONF Lemma 3.3, Step 2, uniform form** (C:1226–1234): the lower bound for `P[G^U]` from
(3.12), with a constant depending only on the unit-scale configuration. -/
theorem zb_step2_uniform {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {U₀ V₀ : Opens ℂ} (hU₀b : Bornology.IsBounded (U₀ : Set ℂ))
    (hU₀ne : (U₀ : Set ℂ).Nonempty) (hV₀U₀ : closure (V₀ : Set ℂ) ⊆ U₀) {ι : Type} [Countable ι]
    {W₀ : ι → Opens ℂ} (hW₀V₀ : ∀ i, W₀ i ≤ V₀) {K₀ : ι → Set ℂ} (hK₀W₀ : ∀ i, K₀ i ⊆ W₀ i)
    {a₀ : ι → ℕ → ℂ} (ha₀ : ∀ i n, a₀ i n ∈ K₀ i) (hKa₀ : ∀ i, K₀ i ⊆ closure (range (a₀ i)))
    {C s : ℝ} (hC : 0 < C) (hs : 0 < s) :
    ∃ 𝔭 : ℝ, 0 < 𝔭 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (ρ : ℝ) (w : ℂ) (r : ℝ), 0 < r → ∀ (z : ℂ) (X : Ω → DistC),
        IsL33ZBPart P h ρ w (affOpens r z U₀) (affOpens r z U₀).isOpen X →
        ∃ (Y : Ω → DistC) (fn : Ω → C(ℂ, ℝ)),
          (∀ ω, Y ω = addFun (recField h ρ w ω) (-(fn ω))) ∧ (∀ ω, ∃ M, ∀ x, |fn ω x| ≤ M) ∧
          (∀ ω (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 (affOpens r z U₀) →
            (∀ φ : TestOn (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen),
              restrictTo (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen)
                (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
            EqOn ⇑(fn ω) 𝔥 (affOpens r z V₀ : Set ℂ)) ∧
          IsGFFPlusCont Y P ∧
          (∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (affOpens r z U₀) →
            (∀ φ : TestOn (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen),
              restrictTo (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen)
                (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
            ∀ W' : Set ℂ, IsOpen W' → W' ⊆ affOpens r z V₀ → ∀ f' : C(ℂ, ℝ), EqOn ⇑f' 𝔥 W' →
            ∀ u v : ℂ, (D (addFun (recField h ρ w ω) (-f'))).internal W' u v =
              (D (Y ω)).internal W' u v) ∧
          ∀ ℓ : ℝ, 0 < ℓ →
            ENNReal.ofReal (1 / 2) ≤ P {ω | ∀ i, internalDiam (D (Y ω))
              (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤ ENNReal.ofReal (C * ℓ)} →
            ENNReal.ofReal 𝔭 ≤ P {ω | ∀ i, internalDiam (D (Y ω))
              (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤ ENNReal.ofReal (s * ℓ)} := by
  set ξ := xiGamma γ
  have hξ : 0 < ξ := GM.xiGamma_pos hγ
  set L : ℝ := (Real.log s - Real.log C) / ξ with hL
  have hV₀c : IsCompact (closure (V₀ : Set ℂ)) :=
    (hU₀b.subset (subset_closure.trans hV₀U₀)).isCompact_closure
  obtain ⟨f₀, hf₀⟩ := exists_zsSub_eq_const hV₀c U₀.isOpen hV₀U₀ L
  set E := QuantumZipper.dirichletEnergyOn (U₀ : Set ℂ) f₀.1
  refine ⟨Real.exp (-E) / 4, by positivity, ?_⟩
  intro Ω _ P _ h hh ρ w r hr z X hX
  have hr0 : r ≠ 0 := hr.ne'
  -- the scaled configuration
  have hUb : Bornology.IsBounded (affOpens r z U₀ : Set ℂ) := by
    have e : (affOpens r z U₀ : Set ℂ) = affFwd r z '' U₀ := (image_affFwd_eq hr0 _).symm
    rw [e]
    exact (hU₀b.isCompact_closure.image (continuous_affFwd r z)).isBounded.subset
      (image_mono subset_closure)
  have hUne : (affOpens r z U₀ : Set ℂ).Nonempty := by
    obtain ⟨y, hy⟩ := hU₀ne
    exact ⟨affFwd r z y, show affMap r z (affFwd r z y) ∈ U₀ by rw [affMap_affFwd hr0]; exact hy⟩
  have hVU : closure (affOpens r z V₀ : Set ℂ) ⊆ affOpens r z U₀ :=
    ((continuous_affMap r z).closure_preimage_subset _).trans (preimage_mono hV₀U₀)
  have hWV : ∀ i, affOpens r z (W₀ i) ≤ affOpens r z V₀ := fun i x hx => hW₀V₀ i hx
  have hKW : ∀ i, affFwd r z '' K₀ i ⊆ affOpens r z (W₀ i) := by
    rintro i _ ⟨y, hy, rfl⟩
    show affMap r z (affFwd r z y) ∈ W₀ i
    rw [affMap_affFwd hr0]; exact hK₀W₀ i hy
  have haK : ∀ i n, affFwd r z (a₀ i n) ∈ affFwd r z '' K₀ i :=
    fun i n => mem_image_of_mem _ (ha₀ i n)
  have hKa : ∀ i, affFwd r z '' K₀ i ⊆ closure (range fun n => affFwd r z (a₀ i n)) := by
    intro i
    refine (image_mono (hKa₀ i)).trans ((image_closure_subset_closure_image
      (continuous_affFwd r z)).trans (closure_mono ?_))
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  obtain ⟨f, hff₀, hfE⟩ := zsSub_affine hr0 z f₀
  have hfL : ∀ x ∈ (affOpens r z V₀ : Set ℂ), f.1 x = L := fun x hx => by
    rw [hff₀]; exact hf₀ _ (subset_closure hx)
  obtain ⟨Y, fn, hYd, hfb, hfV, hYc, hres, hW⟩ := exists_zbField hD hh hUb hX (affOpens r z V₀) hVU
  refine ⟨Y, fn, hYd, hfb, hfV, hYc, hW, fun ℓ hℓ hhalf => ?_⟩
  have key := zb_step2_of_field hD hUb hUne hX (affOpens r z V₀) hVU hYc hres hWV f hfL hKW haK
    hKa (ENNReal.ofReal (s * ℓ))
  have e1 : ENNReal.ofReal (Real.exp (-(ξ * L))) * ENNReal.ofReal (s * ℓ) =
      ENNReal.ofReal (C * ℓ) := by
    have h1 : -(ξ * L) = Real.log C - Real.log s := by
      rw [hL]; field_simp; ring
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, h1, Real.exp_sub, Real.exp_log hC,
      Real.exp_log hs]
    congr 1; field_simp
  rw [e1, hfE] at key
  calc ENNReal.ofReal (Real.exp (-E) / 4)
      = ENNReal.ofReal (1 / 2) ^ 2 * ENNReal.ofReal (Real.exp (-E)) := by
        rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := mul_le_mul_left (pow_le_pow_left₀ zero_le hhalf 2) _
    _ ≤ _ := key

end LQGMetric.CONF
