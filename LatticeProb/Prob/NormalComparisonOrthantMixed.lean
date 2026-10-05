/-
# Li--Shao normal comparison: the mixed-derivative orthant integral (route item 4)

Continuing `LatticeProb/Prob/NormalComparisonOrthantDeriv.lean`.  There the orthant box-Fubini
(`integral_Iic_cons`, `integral_Iic_cons₂`) peels the coordinates `0` and `1` off the orthant
`Set.Iic b ⊆ (Fin (m+2) → ℝ)`, producing the nesting `∫ x₀ ∫ x₁ ∫ x''`, while the
two-dimensional fundamental theorem of calculus `integral_integral_mixed_deriv` is stated for
*one fixed tail* `x''`.  The two do not compose directly: the FTC needs the tail `x''`
*outermost*.  This file supplies the missing Fubini swap and closes the general-`m` form of
route item 4:

> `∫_{x ≤ b} ∂₀∂₁ p = ∫_{x'' ≤ (b 2, …, b (m+1))} p (b 0, b 1, x'')`.

## Route

* **`consConsEquiv`** — the measurable equivalence
  `((x₀, x₁), x'') ↦ Fin.cons x₀ (Fin.cons x₁ x'')` from `(ℝ × ℝ) × (Fin m → ℝ)` to
  `Fin (m+2) → ℝ`, built from `MeasurableEquiv.piFinSuccAbove` (twice) and
  `MeasurableEquiv.prodAssoc`; it is volume preserving
  (`volume_preserving_consConsEquiv`) and pulls the orthant `Set.Iic b` back to the box
  `(Iic (b 0) ×ˢ Iic (b 1)) ×ˢ Iic (b ∘ succ ∘ succ)` (`consConsEquiv_preimage_Iic`).
* **`setIntegral_prod_prod_symm`** — Fubini for a box `(s ×ˢ t) ×ˢ u` with the *third* factor
  outermost: `∫ x'' in u, ∫ x in s, ∫ y in t`.  It is `integral_prod_symm` followed, for
  almost every `x''`, by `integral_prod` on the slice (the slice integrability comes from
  `Integrable.prod_left_ae`).
* **`integral_Iic_mixed_deriv₂`** — the main theorem.  Integrability of the pushed integrand
  on the box comes from `IntegrableOn pxy (Set.Iic b)` through
  `MeasurePreserving.integrableOn_comp_preimage`; then the swap, and then for each tail
  `x''` the two-dimensional FTC `integral_integral_mixed_deriv`.

Compared with the route-note formulation, the slice-integrability hypothesis of
`integral_Iic_cons₂` (`∀ x₀, IntegrableOn (pxy ∘ cons x₀) …`) is *not* needed: the single
integrability `IntegrableOn pxy (Set.Iic b)` already yields almost-every slice integrability
through Fubini, and the swap is done on the box before any slice is taken.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonOrthantDeriv

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

/-! ### Fubini on a triple box with the third coordinate outermost -/

/-- **Fubini on a triple box, third factor outermost.**  For `f` integrable on the box
`(s ×ˢ t) ×ˢ u` of a triple product measure, the box integral is the iterated integral with the
third coordinate outermost: `∫ z in u, ∫ x in s, ∫ y in t, f ((x, y), z)`.  Only
`IntegrableOn f ((s ×ˢ t) ×ˢ u)` is assumed; the slice integrability needed for the inner
Fubini holds for almost every `z` by `Integrable.prod_left_ae`. -/
theorem setIntegral_prod_prod_symm {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite τ] (f : (α × β) × γ → ℝ) {s : Set α} {t : Set β}
    {u : Set γ} (hf : IntegrableOn f ((s ×ˢ t) ×ˢ u) ((μ.prod ν).prod τ)) :
    ∫ z in (s ×ˢ t) ×ˢ u, f z ∂((μ.prod ν).prod τ)
      = ∫ z in u, ∫ x in s, ∫ y in t, f ((x, y), z) ∂ν ∂μ ∂τ := by
  have hf' : Integrable f (((μ.restrict s).prod (ν.restrict t)).prod (τ.restrict u)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact hf
  have h1 : ∫ z in (s ×ˢ t) ×ˢ u, f z ∂((μ.prod ν).prod τ)
      = ∫ z, f z ∂(((μ.restrict s).prod (ν.restrict t)).prod (τ.restrict u)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
  rw [h1, integral_prod_symm f hf']
  refine integral_congr_ae ?_
  filter_upwards [hf'.prod_left_ae] with z hz
  rw [integral_prod _ hz]

/-! ### The measurable equivalence `((x₀, x₁), x'') ↦ Fin.cons x₀ (Fin.cons x₁ x'')` -/

/-- The inverse of `MeasurableEquiv.piFinSuccAbove` at index `0` is `Fin.cons`. -/
theorem piFinSuccAbove_symm_apply_zero {n : ℕ} (x₀ : ℝ) (x' : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (x₀, x')
      = (Fin.cons x₀ x' : Fin (n + 1) → ℝ) := by
  funext j
  rw [show ⇑((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm)
    = ⇑(Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) 0) from rfl]
  rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero]
  exact Fin.cases rfl (fun i => rfl) j

/-- **The two-coordinate `Fin.cons` equivalence.**  The measurable equivalence
`((x₀, x₁), x'') ↦ Fin.cons x₀ (Fin.cons x₁ x'')` from `(ℝ × ℝ) × (Fin m → ℝ)` to
`Fin (m+2) → ℝ`, peeling off coordinates `0` and `1` (see `consConsEquiv_apply`). -/
def consConsEquiv (m : ℕ) : (ℝ × ℝ) × (Fin m → ℝ) ≃ᵐ (Fin (m + 2) → ℝ) :=
  (MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0).symm

/-- `consConsEquiv` is `((x₀, x₁), x'') ↦ Fin.cons x₀ (Fin.cons x₁ x'')`. -/
theorem consConsEquiv_apply {m : ℕ} (x₀ x₁ : ℝ) (x'' : Fin m → ℝ) :
    consConsEquiv m ((x₀, x₁), x'')
      = (Fin.cons x₀ (Fin.cons x₁ x'') : Fin (m + 2) → ℝ) := by
  show (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0).symm
    (x₀, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm (x₁, x'')) = _
  rw [piFinSuccAbove_symm_apply_zero, piFinSuccAbove_symm_apply_zero]

/-- **`consConsEquiv` is volume preserving**, for the triple product measure
`(volume.prod volume).prod volume` on `(ℝ × ℝ) × (Fin m → ℝ)`. -/
theorem volume_preserving_consConsEquiv (m : ℕ) :
    MeasurePreserving (consConsEquiv m)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure (Fin m → ℝ)))
      (volume : Measure (Fin (m + 2) → ℝ)) := by
  have h1 := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure (Fin m → ℝ))
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))))
      ((volume : Measure ℝ).prod (volume : Measure (Fin (m + 1) → ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  have h3 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0).symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin (m + 1) → ℝ)))
      (volume : Measure (Fin (m + 2) → ℝ)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0).symm
  exact h3.comp (h2.comp h1)

/-- **The orthant pulls back to a box.**  Under `consConsEquiv`, the orthant `Set.Iic b` of
`Fin (m+2) → ℝ` is the box `(Iic (b 0) ×ˢ Iic (b 1)) ×ˢ Iic (b ∘ succ ∘ succ)`. -/
theorem consConsEquiv_preimage_Iic {m : ℕ} (b : Fin (m + 2) → ℝ) :
    consConsEquiv m ⁻¹' Set.Iic b
      = (Set.Iic (b 0) ×ˢ Set.Iic (b 1)) ×ˢ Set.Iic (fun j : Fin m => b j.succ.succ) := by
  ext ⟨⟨x₀, x₁⟩, x''⟩
  rw [Set.mem_preimage, consConsEquiv_apply]
  simp only [Set.mem_Iic, Pi.le_def, Set.mem_prod]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
    · simpa using h 0
    · simpa using h 1
    · simpa using h j.succ.succ
  · rintro ⟨⟨h0, h1⟩, h''⟩ i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h0
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using h1
      · simpa using h'' j

/-! ### The mixed-derivative orthant integral -/

/-- **The mixed-derivative orthant integral** (route item 4, general `m`).  Integrating the
mixed second derivative `∂₁ ∂₀ p = pxy` over the orthant `{x ≤ b} ⊆ (Fin (m+2) → ℝ)` leaves
`p` at the corner `(b 0, b 1)`, integrated over the orthant of the remaining `m` coordinates.
`px` is the derivative of `p` in coordinate `0` and `pxy` the derivative of `px` in
coordinate `1`; the remaining hypotheses are the integrability and decay side conditions of a
smooth rapidly decaying density.

The proof pulls the orthant back to the box `(Iic (b 0) ×ˢ Iic (b 1)) ×ˢ Iic tail` through the
volume-preserving `consConsEquiv`, swaps the tail outermost
(`setIntegral_prod_prod_symm`), and applies the two-dimensional FTC
`integral_integral_mixed_deriv` for each fixed tail `x''`.  No slice-integrability hypothesis
beyond `IntegrableOn pxy (Set.Iic b)` is needed. -/
theorem integral_Iic_mixed_deriv₂ {m : ℕ} (b : Fin (m + 2) → ℝ)
    (p px pxy : (Fin (m + 2) → ℝ) → ℝ)
    (hint : IntegrableOn pxy (Set.Iic b) volume)
    (hdy : ∀ (x₀ : ℝ) (x'' : Fin m → ℝ), ∀ y ∈ Set.Iic (b 1),
      HasDerivAt (fun y' => px (Fin.cons x₀ (Fin.cons y' x'')))
        (pxy (Fin.cons x₀ (Fin.cons y x''))) y)
    (hdy_int : ∀ (x₀ : ℝ) (x'' : Fin m → ℝ),
      IntegrableOn (fun y => pxy (Fin.cons x₀ (Fin.cons y x''))) (Set.Iic (b 1)))
    (hdy_lim : ∀ (x₀ : ℝ) (x'' : Fin m → ℝ),
      Filter.Tendsto (fun y => px (Fin.cons x₀ (Fin.cons y x''))) Filter.atBot (nhds 0))
    (hdx : ∀ (x'' : Fin m → ℝ), ∀ x ∈ Set.Iic (b 0),
      HasDerivAt (fun x' => p (Fin.cons x' (Fin.cons (b 1) x'')))
        (px (Fin.cons x (Fin.cons (b 1) x''))) x)
    (hdx_int : ∀ x'' : Fin m → ℝ,
      IntegrableOn (fun x => px (Fin.cons x (Fin.cons (b 1) x''))) (Set.Iic (b 0)))
    (hlim : ∀ x'' : Fin m → ℝ,
      Filter.Tendsto (fun x => p (Fin.cons x (Fin.cons (b 1) x''))) Filter.atBot (nhds 0)) :
    ∫ x in Set.Iic b, pxy x
      = ∫ x'' in Set.Iic (fun j : Fin m => b j.succ.succ),
          p (Fin.cons (b 0) (Fin.cons (b 1) x'')) := by
  have hmp := volume_preserving_consConsEquiv m
  have hemb := (consConsEquiv m).measurableEmbedding
  have hpre := consConsEquiv_preimage_Iic b
  have hint3 : IntegrableOn (fun q : (ℝ × ℝ) × (Fin m → ℝ) => pxy (consConsEquiv m q))
      ((Set.Iic (b 0) ×ˢ Set.Iic (b 1)) ×ˢ Set.Iic (fun j : Fin m => b j.succ.succ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (volume : Measure (Fin m → ℝ))) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hemb).mpr hint
  have h1 : ∫ x in Set.Iic b, pxy x
      = ∫ q in (Set.Iic (b 0) ×ˢ Set.Iic (b 1)) ×ˢ Set.Iic (fun j : Fin m => b j.succ.succ),
          pxy (consConsEquiv m q)
          ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
            (volume : Measure (Fin m → ℝ))) := by
    rw [← hpre]
    exact (hmp.setIntegral_preimage_emb hemb pxy (Set.Iic b)).symm
  rw [h1, setIntegral_prod_prod_symm _ hint3]
  refine integral_congr_ae ?_
  filter_upwards with x''
  simp only [consConsEquiv_apply]
  exact integral_integral_mixed_deriv (fun z : ℝ × ℝ => p (Fin.cons z.1 (Fin.cons z.2 x'')))
    (b 0) (b 1)
    (fun x y => px (Fin.cons x (Fin.cons y x'')))
    (fun x y => pxy (Fin.cons x (Fin.cons y x'')))
    (fun x y hy => hdy x x'' y hy) (fun x => hdy_int x x'') (fun x => hdy_lim x x'')
    (hdx x'') (hdx_int x'') (hlim x'')

end LatticeProb
