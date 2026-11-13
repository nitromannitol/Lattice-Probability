/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.ZeroConeLocality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.RootLocality
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Core
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionCoverage
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.MultiVisitNull

/-!
# (4.22) at every centre and scale for the 0-cone, from the area half of Lemma 4.3

Source: [18] Lemma 4.3 : "For each open set `V`, the measure `μ_h`
is determined by `h|_V`; indeed, this follows from the circle average construction of `μ_h` [DS11]. From this,
Lemma 2.4, and the definitions …, we obtain the statement of the lemma."

The proof splits into the **area half** (`μ_h|_V` is a Borel function of the field restricted to a neighbourhood, a
pure GMC statement) and the rest (Lemma 2.4 = the bundle's S7, plus the definitions). This file proves the rest at
The root, for the bundle's 0-cone and **all its recentrings** `h₀(z + r ·) − h₀,r(z)`:

* `L43O.ZeroConeAreaLocality D W V`: the named area half — one Borel map `M` of the field restricted to `W = 𝔻`
  returning, almost surely, the restricted GMC area `μ_h|_V` for the 0-cone field and for each recentred field;
* `L43O.zeroConeRescaledLocality_of_area`: the area half implies `ZeroConeRescaledLocality` for the masked `u_*`
  and the masked `DA` (`V = B_{3/4}(0)`, `θ = 1/2`).

Model facts used for the recentred sample: the bundle's IG coordinate change (via `affineReroot`), excursion
regularity transported by the affine map (the rational first-hit coverage), the area parametrization of the
rescaled curve by the recentred GMC (LR1's affine coordinate change for cone fields), and the a.s. unique visit of a
fixed point (the `ae_bundle_uniqueVisit_fixed`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.L43O

open GMS4b GMS4cP GMS4c

attribute [local instance] Classical.propDecidable

/-! ## Affine transport of excursion regularity -/

section affine

variable {c : C(ℝ, ℂ)} {z : ℂ} {r : ℝ}

theorem affineReroot_zero_apply' (z : ℂ) (s : ℝ) (c : C(ℝ, ℂ)) (t : ℝ) :
    affineReroot z s 0 c t = (s : ℂ)⁻¹ * (c (firstHit c z + s ^ 2 * t) - z) := by
  simp [affineReroot]

theorem lqgArea_bounded_lt_top' (γ : ℝ) (h : DistC) {A : Set ℂ}
    (hA : Bornology.IsBounded A) : CellScaling.lqgArea γ h A < ⊤ :=
  (measure_mono subset_closure).trans_lt
    (LQGCone.lqgArea_compact_lt_top γ h hA.isCompact_closure)

theorem affineReroot_eq_simC (hr : 0 < r) (t : ℝ) :
    affineReroot z r 0 c t =
      simC ((r : ℂ)⁻¹) (-((r : ℂ)⁻¹ * z)) (inv_ne_zero (by exact_mod_cast hr.ne'))
        (c (firstHit c z + r ^ 2 * t)) := by
  rw [affineReroot_zero_apply', simC_apply]
  ring

theorem image_affineReroot (hr : 0 < r) (a b : ℝ) :
    affineReroot z r 0 c '' Icc a b =
      simC ((r : ℂ)⁻¹) (-((r : ℂ)⁻¹ * z)) (inv_ne_zero (by exact_mod_cast hr.ne'))
        '' (c '' Icc (firstHit c z + r ^ 2 * a) (firstHit c z + r ^ 2 * b)) := by
  have hr2 : 0 < r ^ 2 := by positivity
  rw [← image_affine_Icc hr2, image_image, image_image]
  congr 1
  funext t
  exact affineReroot_eq_simC hr t

/-- The recentred Lebesgue-time curve is excursion regular. -/
theorem excursionRegular_affineReroot {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hr : 0 < r) (hsurj : Function.Surjective c) (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (c '' Icc s t) = ENNReal.ofReal (t - s))
    (hinter : ∀ a b : ℝ, a < b → (interior (c '' Icc a b)).Nonempty) :
    ExcursionRegular V (affineReroot z r 0 c) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hA : ((r : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hr.ne')
  set S := simC ((r : ℂ)⁻¹) (-((r : ℂ)⁻¹ * z)) hA with hSdef
  set τ := firstHit c z
  have hsurj' : Function.Surjective (affineReroot z r 0 c) := by
    intro w
    obtain ⟨t₀, ht₀⟩ := hsurj (S.symm w)
    refine ⟨(t₀ - τ) / r ^ 2, ?_⟩
    rw [affineReroot_eq_simC hr, show τ + r ^ 2 * ((t₀ - τ) / r ^ 2) = t₀ by field_simp; ring,
      ht₀, Homeomorph.apply_symm_apply]
  have htime : Tendsto (fun t : ℝ => τ + r ^ 2 * t) (cocompact ℝ) (cocompact ℝ) :=
    ((OrderIso.mulLeft₀ (r ^ 2) hr2).trans (OrderIso.addLeft τ)).toHomeomorph.map_cocompact.le
  have htr' : Tendsto (affineReroot z r 0 c) (cocompact ℝ) (cocompact ℂ) := by
    have h1 : Tendsto (fun t => c (τ + r ^ 2 * t)) (cocompact ℝ) (cocompact ℂ) := htr.comp htime
    have h2 : Tendsto S (cocompact ℂ) (cocompact ℂ) := S.map_cocompact.le
    have := h2.comp h1
    refine this.congr fun t => ?_
    exact (affineReroot_eq_simC hr t).symm
  have hvol' : ∀ s t : ℝ, s ≤ t →
      volume (affineReroot z r 0 c '' Icc s t) = ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [image_affineReroot hr, volume_simC_image, hvol _ _ (by nlinarith),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    field_simp
    ring
  have hinter' : ∀ a b : ℝ, a < b → (interior (affineReroot z r 0 c '' Icc a b)).Nonempty := by
    intro a b hab
    rw [image_affineReroot hr, ← S.image_interior]
    exact (hinter _ _ (by nlinarith)).image S
  exact ⟨hsurj', htr', ⟨volume, hvol'⟩, fun t ht =>
    exists_ratPt_firstHit_excursion hV hVb hsurj' htr' hvol' hinter' ht⟩

end affine

/-! ## The area half and the discharge -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The area half of [18] Lemma 4.3 for the 0-cone and its recentrings (named input).** One Borel map `M` of the
field restricted to `W` returns, almost surely, the GMC area restricted to `V`: for the 0-cone field, and for each
recentred field `h₀(z + r ·) − h₀,r(z)` with `B̄_r(z) ⊆ 𝔻`. Source: [18] ("the measure `μ_h` is
determined by `h|_V`; indeed, this follows from the circle average construction of `μ_h` [DS11]"). -/
def ZeroConeAreaLocality
    (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (W V : TopologicalSpace.Opens ℂ) : Prop :=
  ∃ Mₐ : DistOn W → Measure ℂ, Measurable Mₐ ∧
    (∀ᵐ ω ∂P, (Mₐ (restrictTo W (zeroConeField γ X₀ B₀ B₀' ω))).restrict V =
      (CellScaling.lqgArea γ (zeroConeField γ X₀ B₀ B₀' ω)).restrict V) ∧
    ∀ (z : ℂ) (r : ℝ), 0 < r → closedBall z r ⊆ ball (0 : ℂ) 1 → ∀ᵐ ω ∂P,
      (Mₐ (restrictTo W (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω)))).restrict V =
        (CellScaling.lqgArea γ (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))).restrict V

/-- The local reader assembled from the area half and the surrogate observables. -/
def zeroConeReader (Mₐ : DistOn fieldRegion → Measure ℂ) (obs : ℝ → SurrData → ℝ≥0∞) :
    ℝ × (DistOn fieldRegion × (ℚ × ℚ → ℝ → ℂ)) → ℝ≥0∞ :=
  fun p => obs p.1 (storeOf excursionRegion
    ((((Mₐ p.2.1).restrict excursionRegion), resDist excursionRegion fieldRegion p.2.1), p.2.2))

theorem measurable_zeroConeReader {Mₐ : DistOn fieldRegion → Measure ℂ} (hM : Measurable Mₐ)
    {obs : ℝ → SurrData → ℝ≥0∞} (hobs : Measurable fun p : ℝ × SurrData => obs p.1 p.2) :
    Measurable (zeroConeReader Mₐ obs) := by
  unfold zeroConeReader
  refine hobs.comp (measurable_fst.prodMk ((measurable_storeOf excursionRegion).comp ?_))
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) (measurable_snd.comp measurable_snd)
  · exact (GMS4c.measurable_measureRestrict excursionRegion).comp
      (hM.comp (measurable_fst.comp measurable_snd))
  · exact (measurable_resDist _ _).comp (measurable_fst.comp measurable_snd)

theorem excursionRegion_le_fieldRegion : excursionRegion ≤ fieldRegion := by
  intro w hw
  have : dist w 0 < 3 / 4 := hw
  change dist w 0 < 1
  linarith

/-- The reader returns the configuration of an actual sample. -/
theorem zeroConeReader_cfg {Mₐ : DistOn fieldRegion → Measure ℂ} {obs : ℝ → SurrData → ℝ≥0∞}
    {μ : Measure ℂ} {h : DistC} {cL : C(ℝ, ℂ)}
    (hM : (Mₐ (restrictTo fieldRegion h)).restrict excursionRegion = μ.restrict excursionRegion)
    (s : ℝ) :
    zeroConeReader Mₐ obs (s, (restrictTo fieldRegion h, excursionData excursionRegion cL)) =
      obs s (storeOf excursionRegion (localConfiguration excursionRegion μ h cL)) := by
  unfold zeroConeReader
  rw [hM, ← restrictTo_eq_resDist excursionRegion_le_fieldRegion]
  rfl

/-- A fixed point is visited at most once, as a curve statement. -/
theorem visit_unique_of_not_mem {c : ℝ → ℂ} {w : ℂ} (h : w ∉ multiVisitPoints c) {s t : ℝ}
    (hs : c s = w) (ht : c t = w) : s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h ⟨s, t, hlt, hs, ht⟩
  · exact h ⟨t, s, hlt, ht, hs⟩

theorem closedBall_three_quarter :
    closedBall (0 : ℂ) (1 / 2) ⊆ ball (0 : ℂ) (3 / 4) :=
  closedBall_subset_ball (by norm_num)

/-- **The base and recentred samples satisfy the root-locality hypotheses** — general form for an observable which
is read from a local configuration in the same way as `maskedLocUStar_eq_surrObs_cfg`. -/
theorem zeroConeRescaledLocality_of_reader
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hA : ZeroConeAreaLocality D fieldRegion excursionRegion)
    {obs : ℝ → (ℝ → ℂ) → ℝ≥0∞} {sobs : ℝ → SurrData → ℝ≥0∞}
    (hsobs : Measurable fun p : ℝ × SurrData => sobs p.1 p.2)
    (hread : ∀ (μ : Measure ℂ) (h : DistC) (cL : C(ℝ, ℂ)) (c : ℝ → ℂ) (φ : ℝ ≃o ℝ),
      μ (ballO (0 : ℂ) (3 / 4)) < ⊤ → ExcursionRegular (ballO (0 : ℂ) (3 / 4) : Set ℂ) cL →
      (∀ t, c t = cL (φ t)) →
      (∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) →
      c 0 = 0 → (∀ t, c t = 0 → t = 0) → ∀ s : ℝ, 0 < s →
      obs s c = sobs s (storeOf (ballO 0 (3 / 4)) (localConfiguration (ballO 0 (3 / 4)) μ h cL))) :
    ZeroConeRescaledLocality D obs fieldRegion excursionRegion := by
  have := D.isProbabilityMeasure
  obtain ⟨Mₐ, hMm, hbase, hresc⟩ := hA
  have hVb : Bornology.IsBounded ((excursionRegion : TopologicalSpace.Opens ℂ) : Set ℂ) :=
    isBounded_excursionRegion
  refine ⟨zeroConeReader Mₐ sobs, measurable_zeroConeReader hMm hsobs, ?_, ?_⟩
  · -- the base sample
    filter_upwards [hbase, D.areaParam₀, D.spaceFilling,
      (GMS4.prop48ZeroConeCellModel D hγ).ae_area_curve,
      ae_bundle_excursionRegular D excursionRegion hVb, ae_bundle_uniqueVisit_fixed D 0]
      with ω hMω harea hspace hparam hreg huv s hs
    obtain ⟨φ, hφ0, hcurve⟩ := harea.1
    rw [zeroConeReader_cfg hMω]
    refine hread _ _ (ηL ω) (η₀ ω) φ
      (lqgArea_bounded_lt_top' γ _ isBounded_ball) hreg hcurve hparam ?_ ?_ s hs
    · rw [hcurve, hφ0, hspace.2.2.1]
    · intro t ht
      rw [hcurve] at ht
      have h1 := visit_unique_of_not_mem huv ht hspace.2.2.1
      rw [← hφ0] at h1
      exact φ.injective h1
  · -- the recentred samples
    intro z r hr hzr
    have hLR1 := LQGCoord.ae_lqgArea_affine_coneField_holds (α := 0) hγ.1 hγ.2
      (LQGCoord.lqgQ_pos hγ.1) D.gff₀ D.bm_B₀ D.bm_B₀'
    filter_upwards [hresc z r hr hzr, D.areaParam₀, D.spaceFilling,
      (GMS4.prop48ZeroConeCellModel D hγ).ae_area_curve, GMS4c.ae_ηL_intervals_have_interior D,
      ae_bundle_uniqueVisit_fixed D z, ae_hitTime_spec D, hLR1]
      with ω hMω harea hspace hparam₀ hinter huv hhit hlr s hs
    obtain ⟨φ₀, hφ₀0, hcurve₀⟩ := harea.1
    obtain ⟨hsurj, htr, -, hvol⟩ := hspace
    set h₀ := zeroConeField γ X₀ B₀ B₀' ω with hh₀def
    set a₁ := circleAvg h₀ r z with ha₁def
    set lam := timeScale γ a₁ r with hlamdef
    have hlam : 0 < lam := timeScale_pos γ a₁ hr
    have hr2 : 0 < r ^ 2 := by positivity
    -- the first visits correspond
    set τ₀ := hitTime (η₀ ω) z with hτ₀def
    have hτ₀ : η₀ ω τ₀ = z := hhit z
    have hτ : firstHit (ηL ω) z = φ₀ τ₀ := by
      have hvis : ηL ω (φ₀ τ₀) = z := by rw [← hcurve₀, hτ₀]
      have hset : {t : ℝ | ηL ω t = z} = {φ₀ τ₀} := by
        ext t
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun ht => visit_unique_of_not_mem huv ht hvis, fun ht => ht ▸ hvis⟩
      unfold firstHit
      rw [hset, csInf_singleton]
    -- the time change
    set phiR : ℝ ≃o ℝ := ((OrderIso.mulLeft₀ lam hlam).trans (OrderIso.addLeft τ₀)).trans
      (φ₀.trans ((OrderIso.addRight (-φ₀ τ₀)).trans
        (OrderIso.mulLeft₀ (r ^ 2)⁻¹ (inv_pos.2 hr2)))) with hphiRdef
    have hphiR : ∀ t, phiR t = (r ^ 2)⁻¹ * (φ₀ (τ₀ + lam * t) + -φ₀ τ₀) := fun t => rfl
    have hcurve : ∀ t, rescaledCurve (η₀ ω) z r lam t = affineReroot z r 0 (ηL ω) (phiR t) := by
      intro t
      rw [rescaledCurve_apply, affineReroot_zero_apply', hτ, hphiR, hcurve₀]
      have harg : φ₀ τ₀ + r ^ 2 * ((r ^ 2)⁻¹ * (φ₀ (τ₀ + lam * t) + -φ₀ τ₀)) =
          φ₀ (τ₀ + lam * t) := by
        field_simp
        ring
      rw [harg]
    -- the area parametrization of the rescaled curve by the recentred GMC
    have hparam : ∀ s t : ℝ, s ≤ t →
        CellScaling.lqgArea γ (IGLaw.affField r 0 z h₀) (rescaledCurve (η₀ ω) z r lam '' Icc s t) =
          ENNReal.ofReal (t - s) := by
      intro s t hst
      have hfield : IGLaw.affField r 0 z h₀ =
          addConst (affineComp r z h₀) (CellScaling.lqgQ γ * Real.log r + (-a₁ - CellScaling.lqgQ γ * Real.log r)) := by
        rw [IGLaw.affField, rotateField_zero]
        congr 1
        ring
      have himg : (fun w : ℂ => (r : ℂ) * w + z) '' (rescaledCurve (η₀ ω) z r lam '' Icc s t) =
          η₀ ω '' Icc (τ₀ + lam * s) (τ₀ + lam * t) := by
        have hcomp : (fun w : ℂ => (r : ℂ) * w + z) ∘ rescaledCurve (η₀ ω) z r lam =
            (η₀ ω : ℝ → ℂ) ∘ (fun u : ℝ => τ₀ + lam * u) := by
          funext u
          have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
          simp only [Function.comp, rescaledCurve_apply]
          field_simp
          ring
        rw [← image_comp, hcomp, image_comp, image_affine_Icc hlam]
      have key : CellScaling.lqgArea γ (IGLaw.affField r 0 z h₀)
          (rescaledCurve (η₀ ω) z r lam '' Icc s t) =
          ENNReal.ofReal (Real.exp (γ * (-a₁ - CellScaling.lqgQ γ * Real.log r))) *
            CellScaling.lqgArea γ h₀ ((fun w : ℂ => (r : ℂ) * w + z) ''
              (rescaledCurve (η₀ ω) z r lam '' Icc s t)) := by
        rw [hfield]
        exact hlr r hr _ z _
      have hp : CellScaling.lqgArea γ h₀ (η₀ ω '' Icc (τ₀ + lam * s) (τ₀ + lam * t)) =
          ENNReal.ofReal (τ₀ + lam * t - (τ₀ + lam * s)) :=
        hparam₀ (τ₀ + lam * s) (τ₀ + lam * t) (by nlinarith)
      rw [key, himg, hp, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      have hrpow : r ^ (γ * CellScaling.lqgQ γ) = Real.exp (Real.log r * (γ * CellScaling.lqgQ γ)) :=
        Real.rpow_def_of_pos hr _
      rw [show τ₀ + lam * t - (τ₀ + lam * s) = lam * (t - s) by ring, ← mul_assoc, hlamdef,
        timeScale, hrpow, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      rw [show γ * (-a₁ - CellScaling.lqgQ γ * Real.log r) + γ * a₁ + Real.log r * (γ * CellScaling.lqgQ γ)
        = 0 by ring, Real.exp_zero, one_mul]
    -- excursion regularity and the root
    have hreg := excursionRegular_affineReroot (z := z) excursionRegion.isOpen hVb hr hsurj htr
      hvol hinter (c := ηL ω)
    have hroot : rescaledCurve (η₀ ω) z r lam 0 = 0 := by
      rw [rescaledCurve_apply, mul_zero, add_zero, ← hτ₀def, hτ₀, sub_self, mul_zero]
    have huniq : ∀ t, rescaledCurve (η₀ ω) z r lam t = 0 → t = 0 := by
      intro t ht
      rw [rescaledCurve_apply] at ht
      have hrne : ((r : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hr.ne')
      have h1 : η₀ ω (τ₀ + lam * t) = z := by
        have := (mul_eq_zero.1 ht).resolve_left hrne
        exact sub_eq_zero.1 this
      rw [hcurve₀] at h1
      have h2 : ηL ω (φ₀ τ₀) = z := by rw [← hcurve₀, hτ₀]
      have h3 := φ₀.injective (visit_unique_of_not_mem huv h1 h2)
      have : lam * t = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hlam.ne'
    rw [zeroConeReader_cfg hMω]
    exact hread _ _ _ _ phiR (lqgArea_bounded_lt_top' γ _ isBounded_ball) hreg hcurve hparam hroot
      huniq s hs

/-- **`ZeroConeRescaledLocality` for the masked `u_*` and the masked `DA`, from the area half.** -/
theorem zeroConeRescaledLocality_of_area
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hA : ZeroConeAreaLocality D fieldRegion excursionRegion) :
    ZeroConeRescaledLocality D (maskedLocUStar (1 / 2)) fieldRegion excursionRegion ∧
      ZeroConeRescaledLocality D (maskedLocDA (1 / 2)) fieldRegion excursionRegion := by
  refine ⟨zeroConeRescaledLocality_of_reader D hγ hA (measurable_surrObsU (1 / 2) (3 / 4))
    (fun μ h cL c φ hfin hreg hcurve hparam hroot huniq s hs =>
      maskedLocUStar_eq_surrObs_cfg (by norm_num) hfin hreg hcurve hparam hroot huniq
        closedBall_three_quarter hs),
    zeroConeRescaledLocality_of_reader D hγ hA (measurable_surrObsDA (1 / 2) (3 / 4))
    (fun μ h cL c φ hfin hreg hcurve hparam hroot huniq s hs =>
      maskedLocDA_eq_surrObs_cfg (by norm_num) hfin hreg hcurve hparam hroot huniq
        closedBall_three_quarter hs)⟩

end Bundle

end MatedCRTHarmonic.L43O
