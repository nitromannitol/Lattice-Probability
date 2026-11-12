/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.AnnulusClipCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusClipPeierls

/-!
# Peierls bound for the four clipped long-way crossings of a square annulus

`perc_annulus_peierls_clip_cross` (decision D93, packet P-1): the crossing form of
`perc_annulus_peierls_clip`. Outside an event of probability `≤ 4 (2N+1) (8θ)^{N-n+1}`, every
active side rectangle (`N < ext d`) of the annulus `n ≤ ‖z‖_∞ ≤ N` clipped to `annClip ext` has a
long-way `4`-crossing of good sites. This is the union bound over the four sides from the proof
of `perc_annulus_peierls_clip` (each side bounded by `perc_clipRect_peierls`), stopping before
the gluing `perc_annulus_enclosure_clip`. Compare DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`
l. 1005–1013) and Grimmett, *Percolation* (2nd ed.), §11.7.

`percEnclosureClip_of_cross`: the gluing, i.e. `perc_annulus_enclosure_clip`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LQGMetric

open PercClip in
/-- **Peierls bound for the four clipped long-way crossings** of a square annulus clipped to
the rectangle `annClip ext` (crossing form of `perc_annulus_peierls_clip`). -/
theorem perc_annulus_peierls_clip_cross {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n N : ℕ) (_hn : 1 ≤ n) (hnN : n ≤ N) (ext : PercDir → ℤ) (hext : ∀ d, -(n : ℤ) ≤ ext d)
    (_hTB : (N : ℤ) < ext .T ∨ (N : ℤ) < ext .B) (_hRL : (N : ℤ) < ext .R ∨ (N : ℤ) < ext .L)
    (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞}
    (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ z, annClip ext z → (∃ d, z ∈ annRect n N d) → μ (B z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, annClip ext z ∧ ∃ d, z ∈ annRect n N d) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)) :
    μ {ω | ¬ ∀ d, (N : ℤ) < ext d →
        PercClipCross n N d (clipLo N ext d) (clipHi N ext d) {z | ω ∉ B z}} ≤
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
  have hsub : {ω | ¬ ∀ d, (N : ℤ) < ext d →
      PercClipCross n N d (clipLo N ext d) (clipHi N ext d) {z | ω ∉ B z}} ⊆
      (E .T ∪ E .B) ∪ (E .R ∪ E .L) := by
    intro ω hω
    by_contra hc
    simp only [hE, Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    exact hω fun d => by cases d <;> tauto
  calc μ {ω | ¬ ∀ d, (N : ℤ) < ext d →
        PercClipCross n N d (clipLo N ext d) (clipHi N ext d) {z | ω ∉ B z}}
      ≤ (μ (E .T) + μ (E .B)) + (μ (E .R) + μ (E .L)) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
        gcongr <;> exact measure_union_le _ _
    _ ≤ 4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) := by
        have h4 := add_le_add (add_le_add (hd .T) (hd .B)) (add_le_add (hd .R) (hd .L))
        refine h4.trans (le_of_eq ?_)
        ring

open PercClip in
/-- The four clipped long-way crossings glue to a clipped good enclosure
(`perc_annulus_enclosure_clip`). -/
theorem percEnclosureClip_of_cross (n N : ℤ) (hn : 1 ≤ n) (hnN : n ≤ N) (ext : PercDir → ℤ)
    (hext : ∀ d, -n ≤ ext d) (hTB : N < ext .T ∨ N < ext .B) (hRL : N < ext .R ∨ N < ext .L)
    (G : Set (ℤ × ℤ))
    (hcross : ∀ d, N < ext d → PercClipCross n N d (clipLo N ext d) (clipHi N ext d) G) :
    PercEnclosureClip n N ext G :=
  perc_annulus_enclosure_clip n N hn hnN ext hext hTB hRL G hcross

end LQGMetric
