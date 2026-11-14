import Mathlib
import LatticeProb.Prob.UpcrossStrongMarkov

/-!
# Strong Markov property at an almost surely finite stopping functional

Let `W` be the law on `C(ℝ≥0, ℝ)` of a standard real Brownian motion and let `τ` be a measurable stopping
functional (`IsStopFun`) which is finite `W`-almost surely, for instance the first hitting time of a level.

* `LatticeProb.lintegral_stopAt_shiftPath_pathLaw`: for every measurable functional `F` of the pair (path stopped
  at `τ`, increments after `τ`), the increments after `τ` are integrated out against `W`. Since `τ < ∞` almost
  surely, no restriction to the event `{τ < ∞}` is needed.
* `LatticeProb.lintegral_stopAt_mul_shiftPath_pathLaw`: the product form: the stopped path and the increments
  after `τ` are independent, and the increments have law `W`.
* `LatticeProb.lintegral_pair_stopAt_shiftPath`: the same for a pair of independent Brownian paths (law
  `W.prod W'`), both stopped at a stopping functional `τ` of the first path. This is the strong Markov property of
  a planar Brownian motion with independent coordinates at a stopping time of its first coordinate. It follows
  from the one-dimensional statement by Tonelli: for a fixed first path, `τ` is a constant time for the second path.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- Stopping a path at a random time `σ z` is measurable in the parameter `z`. -/
theorem measurable_stopAt_of {Z : Type*} [MeasurableSpace Z] {σ : Z → ℝ≥0∞} {g : Z → C(ℝ≥0, ℝ)}
    (hσ : Measurable σ) (hg : Measurable g) : Measurable fun z => stopAt (σ z) (g z) := by
  refine measurable_pathValued_of_eval fun s => ?_
  exact (continuous_eval : Continuous fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2).measurable.comp
    (hg.prodMk (measurable_const.min hσ).ennreal_toNNReal)

/-- The increments of a path after a random time `σ z` are measurable in the parameter `z`. -/
theorem measurable_shiftPath_of {Z : Type*} [MeasurableSpace Z] {σ : Z → ℝ≥0} {g : Z → C(ℝ≥0, ℝ)}
    (hσ : Measurable σ) (hg : Measurable g) : Measurable fun z => shiftPath (σ z) (g z) := by
  have he : Measurable fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2 :=
    (continuous_eval : Continuous fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2).measurable
  refine measurable_pathValued_of_eval fun s => ?_
  exact (he.comp (hg.prodMk (hσ.add_const s))).sub (he.comp (hg.prodMk hσ))

/-- A stopping functional does not change when the path is stopped at its (finite) value. -/
theorem IsStopFun.apply_stopAt_self {τ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτ : IsStopFun τ) {w : C(ℝ≥0, ℝ)}
    (hw : τ w < ⊤) : τ (stopAt (τ w) w) = τ w := by
  have h := (hτ w (τ w).toNNReal).1 (ENNReal.coe_toNNReal hw.ne).ge
  rwa [ENNReal.coe_toNNReal hw.ne] at h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- With zero drift, `driftLaw` is the law of the Brownian path. -/
theorem driftLaw_zero_eq (hcont : ∀ ω, Continuous fun t => B t ω) :
    driftLaw P B hcont 0 = P.map (pathMap B hcont) := by
  have h : driftMap 0 = id := by
    funext w
    ext s
    simp
  rw [driftLaw, h, Measure.map_id]

variable [IsProbabilityMeasure P]

/-- **Strong Markov property at an almost surely finite stopping functional.** For the law `W` of a real
Brownian path, a measurable stopping functional `τ` with `τ < ∞` `W`-almost surely, and a measurable functional `F`
of the pair (path stopped at `τ`, increments after `τ`), the increments are integrated out against `W`. -/
theorem lintegral_stopAt_shiftPath_pathLaw (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {τ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτm : Measurable τ)
    (hτ : IsStopFun τ) (hfin : ∀ᵐ w ∂(P.map (pathMap B hcont)), τ w < ⊤)
    {F : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ w, F (stopAt (τ w) w, shiftPath (τ w).toNNReal w) ∂(P.map (pathMap B hcont)) =
      ∫⁻ w, ∫⁻ v, F (stopAt (τ w) w, v) ∂(P.map (pathMap B hcont)) ∂(P.map (pathMap B hcont)) := by
  have key := lintegral_stopAt_shift_driftLaw hB hm hcont 0 hτm hτ hF
  rw [driftLaw_zero_eq hcont,
    Measure.restrict_eq_self_of_ae_mem (s := {w | τ w < ⊤}) hfin] at key
  exact key

/-- **Product form of the strong Markov property.** Under the law `W` of a real Brownian path, the path stopped at
an almost surely finite stopping functional `τ` and the increments after `τ` are independent, and the increments
have law `W`. -/
theorem lintegral_stopAt_mul_shiftPath_pathLaw (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {τ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτm : Measurable τ)
    (hτ : IsStopFun τ) (hfin : ∀ᵐ w ∂(P.map (pathMap B hcont)), τ w < ⊤)
    {f g : C(ℝ≥0, ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ w, f (stopAt (τ w) w) * g (shiftPath (τ w).toNNReal w) ∂(P.map (pathMap B hcont)) =
      (∫⁻ w, f (stopAt (τ w) w) ∂(P.map (pathMap B hcont))) * ∫⁻ w, g w ∂(P.map (pathMap B hcont)) := by
  have key := lintegral_stopAt_shiftPath_pathLaw hB hm hcont hτm hτ hfin
    (F := fun p => f p.1 * g p.2) ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
  refine key.trans ?_
  simp only [lintegral_const_mul _ hg]
  exact lintegral_mul_const _ (hf.comp (measurable_stopAt_path hτm))

/-- **Strong Markov property of a pair of independent Brownian paths at a stopping functional of the first
path.** Let `W`, `W'` be the laws of two real Brownian paths and `τ` a measurable stopping functional with `τ < ∞`
`W`-almost surely. Under `W.prod W'`, for every measurable functional `F` of the pair (both paths stopped at the
time `τ` of the first path, the increments of both paths after that time), the increments are integrated out
against `W.prod W'`. -/
theorem lintegral_pair_stopAt_shiftPath (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {B' : ℝ≥0 → Ω' → ℝ}
    (hB' : IsBrownianReal B' P') (hm' : ∀ t, Measurable (B' t)) (hcont' : ∀ ω, Continuous fun t => B' t ω)
    {τ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτm : Measurable τ) (hτ : IsStopFun τ)
    (hfin : ∀ᵐ w ∂(P.map (pathMap B hcont)), τ w < ⊤)
    {F : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F ((stopAt (τ p.1) p.1, stopAt (τ p.1) p.2),
        (shiftPath (τ p.1).toNNReal p.1, shiftPath (τ p.1).toNNReal p.2))
        ∂((P.map (pathMap B hcont)).prod (P'.map (pathMap B' hcont'))) =
      ∫⁻ p, ∫⁻ q, F ((stopAt (τ p.1) p.1, stopAt (τ p.1) p.2), q)
        ∂((P.map (pathMap B hcont)).prod (P'.map (pathMap B' hcont')))
        ∂((P.map (pathMap B hcont)).prod (P'.map (pathMap B' hcont'))) := by
  set W := P.map (pathMap B hcont) with hW
  set W' := P'.map (pathMap B' hcont') with hW'
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2 inferInstance
  have : IsProbabilityMeasure W' :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B' hm' hcont').aemeasurable).2 inferInstance
  have hs1 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => stopAt (τ p.1) p.1 :=
    measurable_stopAt_of (hτm.comp measurable_fst) measurable_fst
  have hs2 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => stopAt (τ p.1) p.2 :=
    measurable_stopAt_of (hτm.comp measurable_fst) measurable_snd
  have hh1 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => shiftPath (τ p.1).toNNReal p.1 :=
    measurable_shiftPath_of (hτm.comp measurable_fst).ennreal_toNNReal measurable_fst
  have hh2 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => shiftPath (τ p.1).toNNReal p.2 :=
    measurable_shiftPath_of (hτm.comp measurable_fst).ennreal_toNNReal measurable_snd
  -- the second path integrated out for a fixed first path
  obtain ⟨G, hGdef⟩ : ∃ G : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) → ℝ≥0∞,
      G = fun z => ∫⁻ y, ∫⁻ v, F ((z.1, stopAt (τ z.1) y), (z.2, v)) ∂W' ∂W' := ⟨_, rfl⟩
  have hHm : Measurable fun r : ((C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × C(ℝ≥0, ℝ)) × C(ℝ≥0, ℝ) =>
      F ((r.1.1.1, stopAt (τ r.1.1.1) r.1.2), (r.1.1.2, r.2)) :=
    hF.comp (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_stopAt_of (hτm.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
        (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
  have hGm : Measurable G := by
    rw [hGdef]
    exact (hHm.lintegral_prod_right' (ν := W')).lintegral_prod_right' (ν := W')
  have hstep2 : ∀ x, τ x < ⊤ →
      ∫⁻ y, F ((stopAt (τ x) x, stopAt (τ x) y),
          (shiftPath (τ x).toNNReal x, shiftPath (τ x).toNNReal y)) ∂W' =
        G (stopAt (τ x) x, shiftPath (τ x).toNNReal x) := by
    intro x hx
    have key := lintegral_stopAt_shiftPath_pathLaw hB' hm' hcont' (τ := fun _ => τ x) measurable_const
      (fun _ _ => ⟨fun _ => rfl, fun h => h⟩) (ae_of_all _ fun _ => hx)
      (F := fun q => F ((stopAt (τ x) x, q.1), (shiftPath (τ x).toNNReal x, q.2)))
      (hF.comp ((measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)))
    refine key.trans ?_
    simp only [hGdef, hτ.apply_stopAt_self hx]
    rfl
  have hstep3 := lintegral_stopAt_shiftPath_pathLaw hB hm hcont hτm hτ hfin hGm
  have hK : Measurable fun r : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) =>
      F ((stopAt (τ r.1.1) r.1.1, stopAt (τ r.1.1) r.1.2), r.2) :=
    hF.comp (((hs1.prodMk hs2).comp measurable_fst).prodMk measurable_snd)
  have hOuter : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      ∫⁻ q, F ((stopAt (τ p.1) p.1, stopAt (τ p.1) p.2), q) ∂(W.prod W') :=
    hK.lintegral_prod_right'
  calc _ = ∫⁻ x, ∫⁻ y, F ((stopAt (τ x) x, stopAt (τ x) y),
          (shiftPath (τ x).toNNReal x, shiftPath (τ x).toNNReal y)) ∂W' ∂W :=
        lintegral_prod _ (hF.comp ((hs1.prodMk hs2).prodMk (hh1.prodMk hh2))).aemeasurable
    _ = ∫⁻ x, G (stopAt (τ x) x, shiftPath (τ x).toNNReal x) ∂W := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin] with x hx using hstep2 x hx
    _ = ∫⁻ x, ∫⁻ x', G (stopAt (τ x) x, x') ∂W ∂W := hstep3
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ x', ∫⁻ v, F ((stopAt (τ x) x, stopAt (τ x) y), (x', v)) ∂W' ∂W ∂W' ∂W := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin] with x hx
        simp only [hGdef, hτ.apply_stopAt_self hx]
        have hL : Measurable fun r : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × C(ℝ≥0, ℝ) =>
            F ((stopAt (τ x) x, stopAt (τ x) r.1.2), (r.1.1, r.2)) :=
          hF.comp ((measurable_const.prodMk
            (measurable_stopAt_of measurable_const (measurable_snd.comp measurable_fst))).prodMk
            ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        exact lintegral_lintegral_swap (hL.lintegral_prod_right' (ν := W')).aemeasurable
    _ = _ := by
        symm
        rw [lintegral_prod _ hOuter.aemeasurable]
        refine lintegral_congr fun x => lintegral_congr fun y => ?_
        exact lintegral_prod _ (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable

end LatticeProb
