/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.RootLocality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.SurrogateMatching
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Phase
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.SampleBridge

/-!
# Measurable root form of [18] Lemma 4.3 from a local configuration

Source: [18] Lemma 4.3 and (4.22).

`L43O.surrObsU θ R s ξ` (resp. `surrObsDA`) is the masked `u^s_*` (resp. `DA^s`) of the surrogate curve at its root
time, as a function of the stored data `ξ = (σ, M)`; it is jointly Borel in `(s, ξ)` (`measurable_surrObsU`). The
stored data of a local configuration `x` (the `GMS4c.LocalConfiguration`: restricted area, restricted field,
Lebesgue-time excursion segments) is `storeOf U x`: the Borel quantum-time segments `GMS4cP.l43pSegments U x`
and the local masses.

`L43O.maskedLocUStar_eq_surrObs_cfg`: for an excursion-regular Lebesgue curve `η_L`, its reparametrization `η` by the
mass of a measure `μ` finite on `U = B_R(0)`, a root `η 0 = 0` visited only at time `0`, and `B̄_θ(0) ⊆ U`,

`1{B^s_0 ⊆ B̄_θ(0)} u^s_*(η, 0) = surrObsU θ R s (storeOf U (localConfiguration U μ h η_L))` for every `s > 0`.

This is the deterministic content of (4.22) at the root: the masked local observable is a fixed Borel function of the
local configuration. (The local area itself must still be read from the field, the "area half" of Lemma 4.3.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.L43O

open GMS4b GMS4cP GMS4c
open LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT

attribute [local instance] Classical.propDecidable

/-! ## Rescaling the mesh to `1` -/

/-- `t ↦ c(t₀ + l t)` as a continuous curve. -/
def timeAffineC (c : C(ℝ, ℂ)) (t₀ l : ℝ) : C(ℝ, ℂ) := ⟨fun t => c (t₀ + l * t), by fun_prop⟩

theorem measurable_timeAffineC :
    Measurable fun p : (C(ℝ, ℂ) × ℝ) × ℝ => timeAffineC p.1.1 p.1.2 p.2 := by
  refine (GMS4c.measurableEmbedding_ratRestrict.measurable_comp_iff).1 ?_
  refine measurable_pi_iff.mpr fun t => ?_
  change Measurable fun p : (C(ℝ, ℂ) × ℝ) × ℝ => p.1.1 (p.1.2 + p.2 * (t : ℝ))
  exact continuous_eval.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).add (measurable_snd.mul measurable_const)))

theorem maskedLocUStarAt_eq_timeAffine {θ s : ℝ} (hs : 0 < s) (c : C(ℝ, ℂ)) (t₀ : ℝ) :
    maskedLocUStarAt θ s c t₀ = maskedLocUStar θ 1 (timeAffineC c t₀ s) := by
  have h1 : s / s = 1 := div_self hs.ne'
  have hball := locBall_timeAffine (c : ℝ → ℂ) (t₀ := t₀) hs s 0
  have hU := locUStar_affine 1 0 one_ne_zero (c : ℝ → ℂ) (t₀ := t₀) hs s 0
  rw [h1, mul_zero, add_zero] at hball hU
  have hc : (timeAffineC c t₀ s : ℝ → ℂ) = timeAffine (c : ℝ → ℂ) t₀ s := rfl
  have hc' : (timeAffineC c t₀ s : ℝ → ℂ) = affineCurve 1 0 (c : ℝ → ℂ) t₀ s := by
    funext t
    simp [timeAffineC, affineCurve]
  unfold maskedLocUStarAt maskedLocUStar
  rw [hc, hball, ← hc, hc', hU]

theorem maskedLocDAAt_eq_timeAffine {θ s : ℝ} (hs : 0 < s) (c : C(ℝ, ℂ)) (t₀ : ℝ) :
    maskedLocDAAt θ s c t₀ = maskedLocDA θ 1 (timeAffineC c t₀ s) := by
  have h1 : s / s = 1 := div_self hs.ne'
  have hball := locBall_timeAffine (c : ℝ → ℂ) (t₀ := t₀) hs s 0
  have hD := locDA_timeAffine (c : ℝ → ℂ) (t₀ := t₀) hs s 0
  rw [h1, mul_zero, add_zero] at hball hD
  have hc : (timeAffineC c t₀ s : ℝ → ℂ) = timeAffine (c : ℝ → ℂ) t₀ s := rfl
  unfold maskedLocDAAt maskedLocDA
  rw [hc, hball, hD]

/-! ## The surrogate observables -/

/-- The masked `u^s_*` of the surrogate at its root time. -/
def surrObsU (θ R s : ℝ) (ξ : SurrData) : ℝ≥0∞ :=
  if 0 < s then maskedLocUStar θ 1 (timeAffineC (surrogate R ξ.1 ξ.2) (rootTime R ξ.1 ξ.2) s)
  else 0

/-- The masked `DA^s` of the surrogate at its root time. -/
def surrObsDA (θ R s : ℝ) (ξ : SurrData) : ℝ≥0∞ :=
  if 0 < s then maskedLocDA θ 1 (timeAffineC (surrogate R ξ.1 ξ.2) (rootTime R ξ.1 ξ.2) s)
  else 0

theorem measurable_surrObsU (θ R : ℝ) :
    Measurable fun p : ℝ × SurrData => surrObsU θ R p.1 p.2 := by
  unfold surrObsU
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  have hm : Measurable fun p : ℝ × SurrData =>
      timeAffineC (surrogate R p.2.1 p.2.2) (rootTime R p.2.1 p.2.2) p.1 :=
    measurable_timeAffineC.comp (((measurable_surrogate.comp measurable_snd).prodMk
      (measurable_rootTime.comp measurable_snd)).prodMk measurable_fst)
  exact (measurable_maskedLocUStar θ zero_le_one).comp hm

theorem measurable_surrObsDA (θ R : ℝ) :
    Measurable fun p : ℝ × SurrData => surrObsDA θ R p.1 p.2 := by
  unfold surrObsDA
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  have hm : Measurable fun p : ℝ × SurrData =>
      timeAffineC (surrogate R p.2.1 p.2.2) (rootTime R p.2.1 p.2.2) p.1 :=
    measurable_timeAffineC.comp (((measurable_surrogate.comp measurable_snd).prodMk
      (measurable_rootTime.comp measurable_snd)).prodMk measurable_fst)
  exact (measurable_maskedLocDA θ 1).comp hm

/-! ## The stored data of a local configuration -/

/-- The stored data of a local configuration: quantum-time segments and local masses. -/
def storeOf (U : TopologicalSpace.Opens ℂ) (x : LocalConfiguration U) : SurrData :=
  (l43pSegments U x, fun q => localQuantumTotal q (l43pFinite U x))

theorem measurable_storeOf (U : TopologicalSpace.Opens ℂ) : Measurable (storeOf U) :=
  (measurable_l43pSegments U).prodMk (measurable_pi_iff.mpr fun q =>
    (measurable_localQuantumTotal U q).comp (measurable_l43pFinite U))

section cfg

variable {R : ℝ} {μ : Measure ℂ} {h : LQGMetric.DistC} {ηL : C(ℝ, ℂ)} {η : ℝ → ℂ}
  {φ : ℝ ≃o ℝ}

/-- The stored data of an actual sample is a `GoodStore`. -/
theorem goodStore_of_cfg (hR : 0 < R) (hfin : μ (ballO (0 : ℂ) R) < ⊤)
    (hreg : ExcursionRegular (ballO (0 : ℂ) R : Set ℂ) ηL) (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) :
    ∃ ηc : C(ℝ, ℂ), (ηc : ℝ → ℂ) = η ∧
      GoodStore R ηc
        (fun q => φ.symm (entryBefore ηL (ballO (0 : ℂ) R) (ratPt q)))
        (fun q => φ.symm (exitAfter ηL (ballO (0 : ℂ) R) (ratPt q)))
        (storeOf (ballO 0 R) (localConfiguration (ballO 0 R) μ h ηL)).1
        (storeOf (ballO 0 R) (localConfiguration (ballO 0 R) μ h ηL)).2 := by
  set U : TopologicalSpace.Opens ℂ := ballO (0 : ℂ) R with hUdef
  have hUb : Bornology.IsBounded (U : Set ℂ) := isBounded_ball
  have hfin' : IsFiniteMeasure (localConfiguration U μ h ηL).1.1 := by
    change IsFiniteMeasure (μ.restrict U)
    exact isFiniteMeasure_restrict.mpr hfin.ne
  let ηc : C(ℝ, ℂ) := ⟨η, by
    have : η = fun t => ηL (φ t) := funext hcurve
    rw [this]
    exact ηL.continuous.comp φ.continuous⟩
  have hD := isExcursionFamily_of_regular U.isOpen hUb hreg hcurve
  have hex : ∀ q, ratPt q ∈ (U : Set ℂ) →
      IsExcursion ηL U (entryBefore ηL U (ratPt q)) (exitAfter ηL U (ratPt q)) := fun q hq =>
    (isExcursion_entry_exit U.isOpen hUb hreg.surjective hreg.transient hq).1
  have hseg : ∀ q, ratPt q ∈ (U : Set ℂ) →
      ⇑((storeOf U (localConfiguration U μ h ηL)).1 q) =
        clampSeg η (φ.symm (entryBefore ηL U (ratPt q))) (φ.symm (exitAfter ηL U (ratPt q))) := by
    intro q hq
    change ⇑(l43pSegments U (localConfiguration U μ h ηL) q) = _
    unfold l43pSegments
    rw [l43pFinite_of_finite hfin']
    exact localQuantumCurve_cfg (η := ηc) hfin' hcurve hparam hq (hex q hq)
  refine ⟨ηc, rfl, ⟨hR, hD, hseg, fun q hq => ?_, fun q q' hq hq' hσ => ?_⟩⟩
  · change localQuantumTotal q (l43pFinite U (localConfiguration U μ h ηL)) = _
    rw [l43pFinite_of_finite hfin']
    exact localQuantumTotal_cfg (η := ηc) hfin' hcurve hparam hq (hex q hq)
  · have h1 := hseg q hq
    have h2 := hseg q' hq'
    rw [hσ] at h1
    exact hD.entry_eq_of_clampSeg_eq hparam hq hq' (h1.symm.trans h2)

/-- **Root locality from a local configuration.** -/
theorem maskedLocUStar_eq_surrObs_cfg (hR : 0 < R) (hfin : μ (ballO (0 : ℂ) R) < ⊤)
    (hreg : ExcursionRegular (ballO (0 : ℂ) R : Set ℂ) ηL) (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (hroot : η 0 = 0) (huniq : ∀ t, η t = 0 → t = 0) {θ : ℝ}
    (hθ : closedBall (0 : ℂ) θ ⊆ ball (0 : ℂ) R) {s : ℝ} (hs : 0 < s) :
    maskedLocUStar θ s η =
      surrObsU θ R s (storeOf (ballO 0 R) (localConfiguration (ballO 0 R) μ h ηL)) := by
  obtain ⟨ηc, hηc, hG⟩ := goodStore_of_cfg (h := h) hR hfin hreg hcurve hparam
  rw [surrObsU, if_pos hs, ← maskedLocUStarAt_eq_timeAffine hs, maskedLocUStar_eq_at, ← hηc]
  exact maskedLocUStarAt_surrogate hG (by rw [hηc]; exact hroot)
    (fun t ht => huniq t (by rw [← hηc]; exact ht)) hs.le hθ

theorem maskedLocDA_eq_surrObs_cfg (hR : 0 < R) (hfin : μ (ballO (0 : ℂ) R) < ⊤)
    (hreg : ExcursionRegular (ballO (0 : ℂ) R : Set ℂ) ηL) (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (hroot : η 0 = 0) (huniq : ∀ t, η t = 0 → t = 0) {θ : ℝ}
    (hθ : closedBall (0 : ℂ) θ ⊆ ball (0 : ℂ) R) {s : ℝ} (hs : 0 < s) :
    maskedLocDA θ s η =
      surrObsDA θ R s (storeOf (ballO 0 R) (localConfiguration (ballO 0 R) μ h ηL)) := by
  obtain ⟨ηc, hηc, hG⟩ := goodStore_of_cfg (h := h) hR hfin hreg hcurve hparam
  rw [surrObsDA, if_pos hs, ← maskedLocDAAt_eq_timeAffine hs, maskedLocDA_eq_at, ← hηc]
  exact maskedLocDAAt_surrogate hG (by rw [hηc]; exact hroot)
    (fun t ht => huniq t (by rw [← hηc]; exact ht)) hs.le hθ

end cfg

end MatedCRTHarmonic.L43O
