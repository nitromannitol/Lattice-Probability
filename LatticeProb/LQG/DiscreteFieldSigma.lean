import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Prob.UniformModShift

/-! # Local field observations modulo a discrete group of constants -/

set_option autoImplicit false
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint

namespace LatticeProb.LQG

/-- The local mean-zero pairings and the phase of an anchor pairing. -/
def discreteFieldSigma {Ω : Type} (h : Ω → DistC) (V : Set ℂ)
    (ψ : TestC) {p : ℝ} (hp : 0 < p) : MeasurableSpace Ω :=
  fieldSigma0On h V ⊔ MeasurableSpace.comap (fun ω => toIcoMod hp 0 (h ω ψ)) inferInstance

/-- For a measurable field, the discrete-period observation is measurable. -/
theorem discreteFieldSigma_le {Ω : Type} [MeasurableSpace Ω]
    {h : Ω → DistC} (hh : Measurable h) (V : Set ℂ) (ψ : TestC)
    {p : ℝ} (hp : 0 < p) : discreteFieldSigma h V ψ hp ≤ ‹MeasurableSpace Ω› := by
  apply sup_le
  · rw [fieldSigma0On, ← measurable_iff_comap_le]
    exact measurable_pi_iff.mpr fun φ => (LQGMetric.GFFInv.measurable_pair φ.1.1).comp hh
  · rw [← measurable_iff_comap_le]
    exact (LatticeProb.measurable_toIcoMod_zero hp).comp
      ((LQGMetric.GFFInv.measurable_pair ψ).comp hh)

private lemma measurable_meanZero_pair {Ω : Type} (h : Ω → DistC) {V : Set ℂ}
    (θ : TestC) (hθ : ∫ z, θ z = 0) (hθV : tsupport (θ : ℂ → ℝ) ⊆ V) :
    Measurable[fieldSigma0On h V] (fun ω => h ω θ) := by
  let F : Ω → ({φ : TestC0 // tsupport (φ.1 : ℂ → ℝ) ⊆ V} → ℝ) :=
    fun ω φ => h ω φ.1.1
  have hF : Measurable[MeasurableSpace.comap F MeasurableSpace.pi] F := comap_measurable F
  exact (measurable_pi_apply (⟨⟨θ, hθ⟩, hθV⟩ :
    {φ : TestC0 // tsupport (φ.1 : ℂ → ℝ) ⊆ V})).comp hF

/-- Changing between unit-integral local anchors leaves the observation unchanged. -/
theorem discreteFieldSigma_anchor_eq {Ω : Type} (h : Ω → DistC) {V : Set ℂ}
    {ψ θ : TestC} (hψV : tsupport (ψ : ℂ → ℝ) ⊆ V)
    (hθV : tsupport (θ : ℂ → ℝ) ⊆ V)
    (hψ : ∫ z, ψ z = 1) (hθ : ∫ z, θ z = 1)
    {p : ℝ} (hp : 0 < p) : discreteFieldSigma h V ψ hp = discreteFieldSigma h V θ hp := by
  suffices oneWay : ∀ {a b : TestC}, tsupport (a : ℂ → ℝ) ⊆ V →
      tsupport (b : ℂ → ℝ) ⊆ V → (∫ z, a z) = 1 → (∫ z, b z) = 1 →
      discreteFieldSigma h V b hp ≤ discreteFieldSigma h V a hp by
    exact le_antisymm (oneWay hθV hψV hθ hψ) (oneWay hψV hθV hψ hθ)
  intro a b ha hb hai hbi
  apply sup_le le_sup_left
  rw [← measurable_iff_comap_le]
  have hd : Measurable[discreteFieldSigma h V a hp] (fun ω => h ω (b - a)) := by
    apply (measurable_meanZero_pair h (b - a) ?_ ?_).mono le_sup_left le_rfl
    · simpa only [hbi, one_smul] using LQGMetric.GFFLaw.integral_sub_smul hai b
    · have he : ((b - a : TestC) : ℂ → ℝ) = fun z => b z - a z := by
        ext z
        simp
      rw [he]
      exact (tsupport_sub _ _).trans (union_subset hb ha)
  have hphase : Measurable[discreteFieldSigma h V a hp] (fun ω => toIcoMod hp 0 (h ω a)) :=
    (comap_measurable _).mono le_sup_right le_rfl
  have hm := (LatticeProb.measurable_toIcoMod_zero hp).comp (hphase.add hd)
  have heq : (fun ω => toIcoMod hp 0 (h ω b)) =
      (fun ω => toIcoMod hp 0 (toIcoMod hp 0 (h ω a) + h ω (b - a))) := by
    funext ω
    apply (toIcoMod_eq_toIcoMod hp).mpr
    refine ⟨-toIcoDiv hp 0 (h ω a), ?_⟩
    rw [map_sub, neg_zsmul]
    have hx := toIcoMod_add_toIcoDiv_zsmul hp 0 (h ω a)
    linarith
  rw [heq]
  exact hm

end LatticeProb.LQG
