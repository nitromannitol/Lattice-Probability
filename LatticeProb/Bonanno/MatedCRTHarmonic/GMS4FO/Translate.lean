/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.Translate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.LocalCurve
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTAffineReroot

/-!
# Translation covariance of the Lebesgue-time localized observables

Source: [18], proof of Proposition 4.10: the field is
recentred at the marked point `z₀` and the space-filling SLE is re-rooted at its first visit to `z₀`
(`MatedCRT.affineReroot z₀ 1 0`, `t ↦ c(τ_{z₀} + t) − z₀`). The localized quantities of §4.2 are invariant under
this operation: the swept masses of the translated measure along the re-rooted curve are those of the original
measure along the original curve.

* `sweep_shiftCurve`: the swept mass is unchanged (exact, for every measure and every curve);
* `locCurve_shiftCurve`: the local curve at `w − z₀` is the translate of the local curve at `w`;
* `localGood_shiftCurve_iff`: `LocalGood` for (translated measure, re-rooted curve) on `(D, f, R)` is `LocalGood` for
  (measure, curve) on `(D + z₀, f(· − z₀), R + z₀)`.
The only hypothesis is that every point is visited by `c` at a first time (true for a surjective transient
continuous curve, `exists_first_visit`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic

/-- The curve re-rooted at time `t₀` and translated by `−z₀`: `t ↦ c(t₀ + t) − z₀`. -/
def shiftCurve (c : ℝ → ℂ) (t₀ : ℝ) (z₀ : ℂ) : ℝ → ℂ := fun t => c (t₀ + t) - z₀

/-- The translation `w ↦ w − z₀` as a measurable equivalence. -/
def subEquiv (z₀ : ℂ) : ℂ ≃ᵐ ℂ := MeasurableEquiv.subRight z₀

@[simp] theorem subEquiv_apply (z₀ w : ℂ) : subEquiv z₀ w = w - z₀ := rfl

/-- `MatedCRT.affineReroot z₀ 1 0` is `shiftCurve` at the first visit to `z₀`. -/
theorem affineReroot_one_eq_shiftCurve (c : C(ℝ, ℂ)) (z₀ : ℂ) :
    (⇑(MatedCRT.affineReroot z₀ 1 0 c) : ℝ → ℂ) = shiftCurve c (GMS4b.hitTime c z₀) z₀ := by
  funext t
  simp [MatedCRT.affineReroot, shiftCurve, MatedCRT.firstHit, GMS4b.hitTime]

theorem image_shiftCurve_Icc (c : ℝ → ℂ) (t₀ : ℝ) (z₀ : ℂ) (a b : ℝ) :
    shiftCurve c t₀ z₀ '' Icc a b = subEquiv z₀ '' (c '' Icc (t₀ + a) (t₀ + b)) := by
  rw [image_image, ← image_const_add_Icc, image_image]
  rfl

/-- The translated measure of the translate of a set is the measure of the set. -/
theorem map_subEquiv_image (ν : Measure ℂ) (z₀ : ℂ) (K : Set ℂ) :
    ν.map (subEquiv z₀) (subEquiv z₀ '' K) = ν K := by
  rw [MeasurableEquiv.map_apply, (subEquiv z₀).preimage_image]

/-- **The swept mass is unchanged** by translating the measure and re-rooting the curve. -/
theorem sweep_shiftCurve (ν : Measure ℂ) (c : ℝ → ℂ) (t₀ : ℝ) (z₀ : ℂ) (σ u : ℝ) :
    sweep (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) σ u = sweep ν c (t₀ + σ) u := by
  unfold sweep
  split_ifs with hu
  · rw [image_shiftCurve_Icc, map_subEquiv_image, add_assoc]
  · rw [image_shiftCurve_Icc, map_subEquiv_image, add_assoc]

theorem relTime_shiftCurve (ν : Measure ℂ) (c : ℝ → ℂ) (t₀ : ℝ) (z₀ : ℂ) (σ s : ℝ) :
    relTime (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) σ s = relTime ν c (t₀ + σ) s := by
  have h : sweep (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) σ = sweep ν c (t₀ + σ) :=
    funext (sweep_shiftCurve ν c t₀ z₀ σ)
  simp only [relTime, sweepStart, sweepTop, sweepBot, h]

/-- The first visit of the re-rooted translated curve. -/
theorem hitTime_shiftCurve (c : ℝ → ℂ) (t₀ : ℝ) (z₀ w : ℂ) (hne : (c ⁻¹' {w}).Nonempty)
    (hbdd : BddBelow (c ⁻¹' {w})) :
    GMS4b.hitTime (shiftCurve c t₀ z₀) (w - z₀) = GMS4b.hitTime c w - t₀ := by
  have hset : {t : ℝ | shiftCurve c t₀ z₀ t = w - z₀} = (fun s => s - t₀) '' (c ⁻¹' {w}) := by
    ext t
    simp only [mem_ofPred_eq, shiftCurve, mem_image, mem_preimage, mem_singleton_iff,
      sub_left_inj]
    constructor
    · intro ht
      exact ⟨t₀ + t, ht, by ring⟩
    · rintro ⟨s, hs, rfl⟩
      rw [show t₀ + (s - t₀) = s by ring, hs]
  rw [GMS4b.hitTime, hset]
  have hmono : Monotone fun s : ℝ => s - t₀ := fun a b hab => by linarith
  rw [← hmono.map_csInf_of_continuousAt (continuous_sub_right t₀).continuousAt hne hbdd]
  rfl

/-- **The local curve at `w − z₀` is the translate of the local curve at `w`.** -/
theorem locCurve_shiftCurve (ν : Measure ℂ) (c : ℝ → ℂ) (t₀ : ℝ) (z₀ w : ℂ)
    (hne : (c ⁻¹' {w}).Nonempty) (hbdd : BddBelow (c ⁻¹' {w})) (s : ℝ) :
    locCurve (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) (w - z₀) s = locCurve ν c w s - z₀ := by
  simp only [locCurve, hitTime_shiftCurve c t₀ z₀ w hne hbdd, relTime_shiftCurve]
  simp only [shiftCurve]
  congr 2
  ring_nf

theorem simC_one_neg (z₀ : ℂ) :
    (⇑(GMS4b.simC 1 (-z₀) one_ne_zero) : ℂ → ℂ) = fun x => x - z₀ := by
  funext x
  simp [GMS4b.simC_apply, sub_eq_add_neg]

theorem locCurve_shiftCurve_eq_comp (ν : Measure ℂ) (c : ℝ → ℂ) (t₀ : ℝ) (z₀ w : ℂ)
    (hne : (c ⁻¹' {w}).Nonempty) (hbdd : BddBelow (c ⁻¹' {w})) :
    locCurve (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) (w - z₀) =
      GMS4b.simC 1 (-z₀) one_ne_zero ∘ locCurve ν c w := by
  funext s
  rw [locCurve_shiftCurve ν c t₀ z₀ w hne hbdd, Function.comp_apply, simC_one_neg]

/-- The localized density is translation invariant. -/
theorem locU_shiftCurve (ν : Measure ℂ) (c : ℝ → ℂ) (t₀ : ℝ) (z₀ w : ℂ)
    (hne : (c ⁻¹' {w}).Nonempty) (hbdd : BddBelow (c ⁻¹' {w})) (ε : ℝ) :
    locU (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) ε (w - z₀) = locU ν c ε w := by
  rw [locU, locU, locCurve_shiftCurve_eq_comp ν c t₀ z₀ w hne hbdd, GMS4b.locUStar,
    GMS4b.locUStar, GMS4b.locDA_simC, GMS4b.locDegIn_simC, GMS4b.locDegOut_simC]

/-- The localized window diameter is translation invariant. -/
theorem locWinDiam_shiftCurve (ν : Measure ℂ) (c : ℝ → ℂ) (t₀ : ℝ) (z₀ w : ℂ)
    (hne : (c ⁻¹' {w}).Nonempty) (hbdd : BddBelow (c ⁻¹' {w})) (ε : ℝ) :
    locWinDiam (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) ε (w - z₀) = locWinDiam ν c ε w := by
  rw [locWinDiam, locWinDiam, locCurve_shiftCurve_eq_comp ν c t₀ z₀ w hne hbdd,
    GMS4b.locWindow_simC, GMS4b.diam_simC_image, norm_one, one_mul]

/-- The translation `w ↦ w − z₀` preserves Lebesgue measure on `ℂ`. -/
theorem measurePreserving_subEquiv (z₀ : ℂ) :
    MeasurePreserving (subEquiv z₀) (volume : Measure ℂ) volume :=
  measurePreserving_sub_right volume z₀

/-- Change of variables `w = z + z₀` in a set lower integral. -/
theorem setLIntegral_translate (z₀ : ℂ) (D : Set ℂ) (g : ℂ → ℝ≥0∞) :
    (∫⁻ z in D, g z) = ∫⁻ w in (fun z => z + z₀) '' D, g (w - z₀) := by
  have hpre : (fun z => z + z₀) '' D = subEquiv z₀ ⁻¹' D := by
    ext w
    simp only [mem_image, mem_preimage, subEquiv_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hw
      exact ⟨w - z₀, hw, by ring⟩
  rw [hpre]
  exact ((measurePreserving_subEquiv z₀).setLIntegral_comp_preimage_emb
    (subEquiv z₀).measurableEmbedding g D).symm

/-- Every point with a first visit: the hypothesis of the covariance lemmas. -/
def HasFirstVisits (c : ℝ → ℂ) : Prop :=
  ∀ w : ℂ, (c ⁻¹' {w}).Nonempty ∧ BddBelow (c ⁻¹' {w})

/-- A surjective continuous curve tending to `∞` at `±∞` visits every point at a first time. -/
theorem hasFirstVisits_of_surjective {c : ℝ → ℂ}
    (hsurj : Function.Surjective c) (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) :
    HasFirstVisits c := by
  intro w
  refine ⟨hsurj w, ?_⟩
  have hmem : c ⁻¹' ({w}ᶜ) ∈ cocompact ℝ := htr isCompact_singleton.compl_mem_cocompact
  obtain ⟨t, ht, hts⟩ := mem_cocompact.1 hmem
  refine ht.bddBelow.mono fun x hx => ?_
  by_contra hxt
  exact hts hxt hx

/-- **Translation covariance of the localized good event.** -/
theorem localGood_shiftCurve_iff (ν : Measure ℂ) {c : ℝ → ℂ} (hc : HasFirstVisits c) (t₀ : ℝ)
    (z₀ : ℂ) (ε : ℝ) (D : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ) :
    LocalGood (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) ε D f A tol R r ↔
      LocalGood ν c ε ((fun z => z + z₀) '' D) (fun w => f (w - z₀)) A tol
        ((fun z => z + z₀) '' R) r := by
  have hU : ∀ w : ℂ, locU (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) ε (w - z₀) = locU ν c ε w :=
    fun w => locU_shiftCurve ν c t₀ z₀ w (hc w).1 (hc w).2 ε
  have hW : ∀ w : ℂ,
      locWinDiam (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) ε (w - z₀) = locWinDiam ν c ε w :=
    fun w => locWinDiam_shiftCurve ν c t₀ z₀ w (hc w).1 (hc w).2 ε
  have hint : (∫⁻ z in D, ENNReal.ofReal (f z) *
      locU (ν.map (subEquiv z₀)) (shiftCurve c t₀ z₀) ε z) =
      ∫⁻ w in (fun z => z + z₀) '' D, ENNReal.ofReal (f (w - z₀)) * locU ν c ε w := by
    rw [setLIntegral_translate z₀ D]
    simp only [hU]
  have hint' : (∫⁻ z in D, ENNReal.ofReal (f z)) =
      ∫⁻ w in (fun z => z + z₀) '' D, ENNReal.ofReal (f (w - z₀)) :=
    setLIntegral_translate z₀ D _
  unfold LocalGood
  rw [hint, hint']
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro h w ⟨z, hz, rfl⟩
    have := h z hz
    rwa [show z = (z + z₀) - z₀ by ring, hW] at this
  · intro h z hz
    have := h (z + z₀) ⟨z, hz, rfl⟩
    rwa [← hW, show z + z₀ - z₀ = z by ring] at this

end MatedCRTHarmonic.GMS4FO
