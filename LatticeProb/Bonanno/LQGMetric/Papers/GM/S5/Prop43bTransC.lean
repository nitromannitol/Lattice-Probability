/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bTransC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bTrans

/-!
# Prop 5.2 (C) at centre `z` (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
l. 2846–2848: the events at `z` are those of Prop 5.2 for `h(· + z)`. From the clause (C) of
`P5_2` for the whole-plane GFF `h(· + z)` (`IsWholePlaneGFF.affineComp`) and the points `𝕫 − z`,
`𝕨 − z`, Axiom IV′ (translation invariance, at `h` and at `h − φ(· − z)`) gives the input `hC` of
`gm_L5_4_union_at` at centre `z` with the bumps `φ(· − z)`, `φ ∈ 𝓖_r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Classical

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the path `η − z` -/
def shiftPath43b (η : C(unitInterval, ℂ)) (z : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => η t - z, η.continuous.sub continuous_const⟩

@[simp] lemma shiftPath43b_apply (η : C(unitInterval, ℂ)) (z : ℂ) (t : unitInterval) :
    shiftPath43b η z t = η t - z := rfl

lemma isGeod01_shiftPath {D₁ D₂ : ContMetric} {z a b : ℂ}
    (hD : ∀ u v, D₂.1 (u, v) = D₁.1 (u + z, v + z)) {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 D₁ a b η) : IsGeod01 D₂ (a - z) (b - z) (shiftPath43b η z) := by
  refine ⟨by simp [hη.1], by simp [hη.2.1], fun s t => ?_⟩
  rw [hD, hD]
  simp only [shiftPath43b_apply, sub_add_cancel]
  exact hη.2.2 s t

lemma setDist_sphere_translate {d₁ d₂ : ContMetric} {z : ℂ}
    (hD : ∀ u v, d₂.1 (u, v) = d₁.1 (u + z, v + z)) (x : ℂ) (ρ : ℝ) :
    setDist d₂ {x - z} (Metric.sphere 0 ρ) = setDist d₁ {x} (Metric.sphere z ρ) := by
  simp only [setDist_eq_iInf, iInf_singleton, hD, sub_add_cancel]
  apply le_antisymm
  · refine le_iInf₂ fun y hy => ?_
    refine (iInf₂_le (y - z) ?_).trans_eq (by rw [sub_add_cancel])
    simpa [mem_sphere_iff_norm] using hy
  · refine le_iInf₂ fun y hy => iInf₂_le (y + z) ?_
    simpa [mem_sphere_iff_norm] using hy

/-- (5.3) at `0` for the translated field and path gives (5.4) at `z` -/
lemma frkDist_of_translate {D D' : DistC → ContMetric} {cs Cs c₂ b₀ r : ℝ} {z : ℂ}
    {g₁ g₂ : DistC} (hD : ∀ u v, (D g₂).1 (u, v) = (D g₁).1 (u + z, v + z))
    (hD' : ∀ u v, (D' g₂).1 (u, v) = (D' g₁).1 (u + z, v + z)) {Q : C(unitInterval, ℂ)}
    (hQ : ShortcutConcl D D' cs Cs c₂ b₀ r g₂ (shiftPath43b Q z)) :
    frkDist D D' cs Cs c₂ b₀ r z g₁ Q := by
  obtain ⟨s, t, h0, hst, h1, hs, ht, hb, hc, hd⟩ := hQ
  simp only [shiftPath43b_apply, hD, hD', sub_add_cancel, Metric.mem_ball, dist_zero_right,
    sub_sub_sub_cancel_right] at hs ht hb hc hd
  refine ⟨s, t, h0, hst, h1, ?_, ?_, hb, hc, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]; exact hs
  · rw [Metric.mem_ball, dist_eq_norm]; exact ht
  · rwa [setDist_sphere_translate hD'] at hd

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **Prop 5.2 (C) at centre `z`**: the input `hC` of `gm_L5_4_union_at` with the translated
bumps, from the clause (C) for `h(· + z)` at `𝕫 − z`, `𝕨 − z` -/
theorem ae_exists_bump_at {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hgeo : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ a b : ℂ, a ≠ b →
        ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω)))
    {cs Cs c₂ b₀ r : ℝ} (hr : 0 < r) (E : Set DistC) (Gs : Set TestC)
    (phi : ℂ → ℂ → TestC) (G : Finset TestC) (hGs : Gs ⊆ (G : Set TestC)) (z : ℂ)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∉ Metric.ball z (4 * r))
    (hb : b ∉ Metric.ball z (4 * r)) (hh : IsWholePlaneGFF h P)
    (hC : ∀ᵐ ω ∂P, ∀ x' y' : ℂ, IsHitPt (D (affineComp 1 z (h ω))) (a - z) x' r →
      IsHitPt (D (affineComp 1 z (h ω))) (b - z) y' r →
      phi x' y' ∈ Gs ∧
      ∀ Q Qφ : C(unitInterval, ℂ), IsGeod01 (D (affineComp 1 z (h ω))) (a - z) (b - z) Q →
        (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty → affineComp 1 z (h ω) ∈ E →
        IsGeod01 (D (subTest (affineComp 1 z (h ω)) (phi x' y'))) (a - z) (b - z) Qφ →
        ShortcutConcl D D' cs Cs c₂ b₀ r (subTest (affineComp 1 z (h ω)) (phi x' y')) Qφ) :
    ∀ᵐ ω ∂P, affineComp 1 z (h ω) ∈ E →
      (range (sel a b (h ω)) ∩ Metric.ball z (2 * r)).Nonempty →
      ∃ φ ∈ G.image (transTest z), ∀ Qφ : C(unitInterval, ℂ),
        IsGeod01 (D (subTest (h ω) φ)) a b Qφ → frkDist D D' cs Cs c₂ b₀ r z (subTest (h ω) φ) Qφ := by
  have hz := hh.affineComp one_pos z
  have hP := Tight.isGFFPlusCont_of_wp hh
  have hPφ : ∀ φ : TestC, IsGFFPlusCont (fun ω => subTest (h ω) φ) P := fun φ => by
    simpa only [subTest_eq_addFun_neg_cm] using isGFFPlusCont_addFun_test hh (-φ)
  have htrG : ∀ᵐ ω ∂P, ∀ ψ ∈ G, ∀ u v : ℂ,
      (D (affineComp 1 z (subTest (h ω) (transTest z ψ)))).1 (u, v) =
        (D (subTest (h ω) (transTest z ψ))).1 (u + z, v + z) ∧
      (D' (affineComp 1 z (subTest (h ω) (transTest z ψ)))).1 (u, v) =
        (D' (subTest (h ω) (transTest z ψ))).1 (u + z, v + z) := by
    refine (Filter.eventually_all_finset G).2 fun ψ _ => ?_
    filter_upwards [hD.translation P _ (hPφ (transTest z ψ)) z,
      hD'.translation P _ (hPφ (transTest z ψ)) z] with ω h1 h2 u v
    exact ⟨h1 u v, h2 u v⟩
  have ha' : 3 * r < ‖a - z‖ := by
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at ha; linarith
  have hb' : 3 * r < ‖b - z‖ := by
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hb; linarith
  filter_upwards [hC, hD.length P _ (Tight.isGFFPlusCont_of_wp hz), hgeo P h hh a b hab,
    hD.translation P h hP z, htrG] with ω hCω hL hg htr htrψ hE hhit
  obtain ⟨x', hx'⟩ := exists_isHitPt hL hr ha'
  obtain ⟨y', hy'⟩ := exists_isHitPt hL hr hb'
  obtain ⟨hφG, hsc⟩ := hCω x' y' hx' hy'
  set ψ := phi x' y'
  have hψG : ψ ∈ G := hGs hφG
  refine ⟨transTest z ψ, Finset.mem_image_of_mem _ hψG, fun Qφ hQφ => ?_⟩
  have hQ := isGeod01_shiftPath (D₂ := D (affineComp 1 z (h ω))) htr hg
  have hhit' : (range (shiftPath43b (sel a b (h ω)) z) ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty := by
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hhit
    refine ⟨_, ⟨t, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, shiftPath43b_apply]
    rwa [Metric.mem_ball, dist_eq_norm] at ht
  have hψtr := htrψ ψ hψG
  have hD1 : ∀ u v, (D (subTest (affineComp 1 z (h ω)) ψ)).1 (u, v) =
      (D (subTest (h ω) (transTest z ψ))).1 (u + z, v + z) := fun u v => by
    rw [← affineComp_subTest]; exact (hψtr u v).1
  have hD2 : ∀ u v, (D' (subTest (affineComp 1 z (h ω)) ψ)).1 (u, v) =
      (D' (subTest (h ω) (transTest z ψ))).1 (u + z, v + z) := fun u v => by
    rw [← affineComp_subTest]; exact (hψtr u v).2
  exact frkDist_of_translate hD1 hD2
    (hsc _ _ hQ hhit' hE (isGeod01_shiftPath hD1 hQφ))

end LQGMetric.GM
