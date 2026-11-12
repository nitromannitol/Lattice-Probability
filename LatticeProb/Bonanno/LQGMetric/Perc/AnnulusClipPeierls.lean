/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.AnnulusClipPeierls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusClipMain

/-!
# Peierls bound for good enclosures of a clipped square annulus

`perc_annulus_peierls_clip` (decision D72): `perc_annulus_peierls` for the annulus
`n ≤ ‖z‖_∞ ≤ N` clipped to the rectangle `R = annClip ext`, when in each axis `R` reaches past
the annulus on at least one side. The failure of a clipped good enclosure is contained in the
union over the active sides `d` (`N < ext d`) of the failure of a long-way good crossing of the
clipped side rectangle (`perc_annulus_enclosure_clip`), each bounded by `perc_clipRect_peierls`.
Only the sites of `R` in the annulus enter `hε` and `hind`. Compare DZZ (arXiv:1807.00422,
`LBM_LGDarXiv.tex` l. 1013).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LQGMetric

open PercClip in
/-- **Peierls bound for good enclosures** of a square annulus clipped to the rectangle
`annClip ext`. -/
theorem perc_annulus_peierls_clip {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n N : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (ext : PercDir → ℤ) (hext : ∀ d, -(n : ℤ) ≤ ext d)
    (hTB : (N : ℤ) < ext .T ∨ (N : ℤ) < ext .B) (hRL : (N : ℤ) < ext .R ∨ (N : ℤ) < ext .L)
    (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞}
    (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ z, annClip ext z → (∃ d, z ∈ annRect n N d) → μ (B z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, annClip ext z ∧ ∃ d, z ∈ annRect n N d) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)) :
    μ {ω | ¬ PercEnclosureClip n N ext {z | ω ∉ B z}} ≤
      4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) := by
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hnN' : (n : ℤ) ≤ N := by exact_mod_cast hnN
  set E : PercDir → Set Ω := fun d => {ω | (N : ℤ) < ext d ∧
    ¬ PercClipCross n N d (clipLo N ext d) (clipHi N ext d) {z | ω ∉ B z}} with hE
  have hd : ∀ d, μ (E d) ≤ (2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1) := by
    intro d
    by_cases hda : (N : ℤ) < ext d
    · have h1 := hext .T; have h2 := hext .B; have h3 := hext .R; have h4 := hext .L
      refine (measure_mono fun ω hω => hω.2).trans ?_
      refine perc_clipRect_peierls μ n N hnN d _ _ ?_ ?_ B r hθ hεθ
        (fun z hz => hε z (clipX_sub hn0 hnN' hext hda hz).1
          ⟨d, (clipX_sub hn0 hnN' hext hda hz).2⟩)
        (fun F hF hfar => hind F (fun z hz => ⟨(clipX_sub hn0 hnN' hext hda (hF z hz)).1,
          d, (clipX_sub hn0 hnN' hext hda (hF z hz)).2⟩) hfar)
      · cases d <;> simp only [clipLo, clipHi, clipLoDir, clipHiDir] <;> omega
      · cases d <;> simp only [clipLo, clipHi, clipLoDir, clipHiDir] <;> omega
    · have : E d = ∅ := Set.eq_empty_of_forall_notMem fun ω hω => hda hω.1
      rw [this, measure_empty]
      exact zero_le
  have hsub : {ω | ¬ PercEnclosureClip n N ext {z | ω ∉ B z}} ⊆
      (E .T ∪ E .B) ∪ (E .R ∪ E .L) := by
    intro ω hω
    by_contra hc
    simp only [hE, Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    apply hω
    exact perc_annulus_enclosure_clip n N (by exact_mod_cast hn) hnN' ext hext hTB hRL _
      (fun d => by cases d <;> tauto)
  calc μ {ω | ¬ PercEnclosureClip n N ext {z | ω ∉ B z}}
      ≤ (μ (E .T) + μ (E .B)) + (μ (E .R) + μ (E .L)) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
        gcongr <;> exact measure_union_le _ _
    _ ≤ 4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) := by
        have h4 := add_le_add (add_le_add (hd .T) (hd .B)) (add_le_add (hd .R) (hd .L))
        refine h4.trans (le_of_eq ?_)
        ring

end LQGMetric
