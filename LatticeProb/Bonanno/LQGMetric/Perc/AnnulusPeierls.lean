/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.AnnulusPeierls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusMain
import LatticeProb.Bonanno.LQGMetric.Perc.Peierls

/-!
# Peierls bound for good enclosures of a square annulus

`perc_annulus_peierls`: in the annulus `n ≤ ‖z‖_∞ ≤ N` (`1 ≤ n ≤ N`), if each annulus box is
bad with probability `≤ ε`, badness of boxes pairwise at `ℓ^∞`-distance `> r` satisfies the
product bound, `ε ≤ θ^(r+1)²` and `8θ ≤ 1/2`, then the probability that there is no good
enclosure (`PercEnclosure`) is at most `4 (2N+1) (8θ)^(N-n+1)`. Compare DZZ
(arXiv:1807.00422, `LBM_LGDarXiv.tex` line 1013): `P(no open enclosure) ≤ 9K (8 p^{1/(2κ+1)})^K`
with `K` the width of the annulus.

Proof: `perc_annulus_enclosure` reduces the failure to the failure of a long-way good crossing
of one of the four rectangles; each is `perc_peierls` transported by the isometry `annFromStd`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LQGMetric

/-- A good enclosure of the annulus `n ≤ ‖z‖_∞ ≤ N`: a `4`-connected set of annulus sites of
`G` met by every `*`-path from the hole `‖z‖_∞ < n` to the outside `‖z‖_∞ > N`. -/
def PercEnclosure (n N : ℤ) (G : Set (ℤ × ℤ)) : Prop :=
  ∃ U : Set (ℤ × ℤ), (∀ z ∈ U, z ∈ G ∧ ∃ d, z ∈ annRect n N d) ∧ U.Nonempty ∧
    (∀ x ∈ U, ∀ y ∈ U, Relation.ReflTransGen (PercStepIn U PercAdj4) x y) ∧
    (∀ (Γ : Set (ℤ × ℤ)) (s e : ℤ × ℤ), (-n < s.1 ∧ s.1 < n ∧ -n < s.2 ∧ s.2 < n) →
      ¬ annBox N e → Relation.ReflTransGen (PercStepIn Γ PercAdjK) s e → ∃ z ∈ U, z ∈ Γ)

/-- The inverse of `annStd`. -/
def annFromStd (n N : ℤ) : PercDir → ℤ × ℤ → ℤ × ℤ
  | .T, x => (x.1 - N, x.2 + n)
  | .B, x => (x.1 - N, -(x.2 + n))
  | .R, x => (x.2 + n, x.1 - N)
  | .L, x => (-(x.2 + n), x.1 - N)

lemma annFromStd_inj (n N : ℤ) (d : PercDir) {x y : ℤ × ℤ}
    (h : annFromStd n N d x = annFromStd n N d y) : x = y := by
  rw [Prod.ext_iff] at h ⊢
  cases d <;> simp only [annFromStd] at h <;> omega

lemma annFromStd_mem (n N : ℤ) (hn : 0 ≤ n) (d : PercDir) {x : ℤ × ℤ}
    (hx : percInGrid (2 * N + 1) (N - n + 1) x) : annFromStd n N d x ∈ annRect n N d := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  cases d <;> simp only [annFromStd, annRect, annBox, annDir, Set.mem_ofPred_eq] <;> omega

lemma annFromStd_adj4 (n N : ℤ) (d : PercDir) {x y : ℤ × ℤ} (h : PercAdj4 x y) :
    PercAdj4 (annFromStd n N d x) (annFromStd n N d y) := by
  cases d <;> simp only [annFromStd, PercAdj4] at h ⊢ <;> omega

lemma annFromStd_far (n N : ℤ) (d : PercDir) (r : ℕ) {x y : ℤ × ℤ} (h : PercFar r x y) :
    PercFar r (annFromStd n N d x) (annFromStd n N d y) := by
  cases d <;> simp only [annFromStd, PercFar] at h ⊢ <;> omega

/-- The long-way crossing of a rectangle of the annulus by good boxes. -/
def PercAnnCross (n N : ℤ) (d : PercDir) (G : Set (ℤ × ℤ)) : Prop :=
  ∃ a b, annLong d a = -N ∧ annLong d b = N ∧ a ∈ annRect n N d ∧ a ∈ G ∧
    Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ G} PercAdj4) a b

lemma percAnnCross_of_std (n N : ℤ) (hn : 0 ≤ n) (d : PercDir) (G : Set (ℤ × ℤ))
    (h : PercGoodLR (2 * N + 1) (N - n + 1) (fun x => annFromStd n N d x ∈ G)) :
    PercAnnCross n N d G := by
  obtain ⟨a, b, ha, hb, hag, haG, hab⟩ := h
  refine ⟨annFromStd n N d a, annFromStd n N d b, ?_, ?_, annFromStd_mem n N hn d hag, haG,
    ?_⟩
  · cases d <;> simp only [annFromStd, annLong] <;> omega
  · cases d <;> simp only [annFromStd, annLong] <;> omega
  · refine Relation.ReflTransGen.lift (annFromStd n N d) (fun x y hxy => ?_) _ _ hab
    obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
    exact ⟨⟨annFromStd_mem n N hn d h1, h2⟩, ⟨annFromStd_mem n N hn d h3, h4⟩,
      annFromStd_adj4 n N d h5⟩

/-- Peierls bound for one rectangle of the annulus. -/
lemma perc_annRect_peierls {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n N : ℕ)
    (hnN : n ≤ N) (d : PercDir) (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞}
    (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ z, z ∈ annRect n N d → μ (B z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, z ∈ annRect n N d) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)) :
    μ {ω | ¬ PercAnnCross n N d {z | ω ∉ B z}} ≤ (2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1) := by
  classical
  set ψ := annFromStd (n : ℤ) (N : ℤ) d
  have hK : (((2 * N + 1 : ℕ) : ℤ)) = 2 * (N : ℤ) + 1 := by push_cast; ring
  have hL : (((N - n + 1 : ℕ) : ℤ)) = (N : ℤ) - n + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hnN]; simp
  have hgrid : ∀ x, percInGrid ((2 * N + 1 : ℕ) : ℤ) ((N - n + 1 : ℕ) : ℤ) x →
      ψ x ∈ annRect n N d := fun x hx =>
      annFromStd_mem n N (Int.natCast_nonneg n) d (by rwa [hK, hL] at hx)
  have key := perc_peierls μ (2 * N + 1) (N - n + 1) (by omega) (by omega) (fun x => B (ψ x)) r
    hθ hεθ (fun x hx => hε _ (hgrid x hx)) (fun F hF hfar => by
      have hinj : Set.InjOn ψ F := fun x _ y _ h => annFromStd_inj n N d h
      have e1 : (⋂ x ∈ F, B (ψ x)) = ⋂ z ∈ F.image ψ, B z := by
        rw [Finset.set_biInter_finset_image]
      rw [e1, ← Finset.prod_image (f := fun z => μ (B z)) hinj]
      refine hind _ (fun z hz => ?_) (fun x hx y hy hxy => ?_)
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        exact hgrid w (hF w hw)
      · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
        exact annFromStd_far n N d r (hfar x' hx' y' hy' fun h => hxy (h ▸ rfl)))
  refine le_trans (measure_mono fun ω hω => ?_) key
  intro hstd
  apply hω
  apply percAnnCross_of_std _ _ (Int.natCast_nonneg n)
  rwa [hK, hL] at hstd

/-- **Peierls bound for good enclosures** of a square annulus. -/
theorem perc_annulus_peierls {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n N : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞}
    (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ z, (∃ d, z ∈ annRect n N d) → μ (B z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, ∃ d, z ∈ annRect n N d) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)) :
    μ {ω | ¬ PercEnclosure n N {z | ω ∉ B z}} ≤
      4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) := by
  have hd : ∀ d, μ {ω | ¬ PercAnnCross n N d {z | ω ∉ B z}} ≤
      (2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1) := fun d =>
    perc_annRect_peierls μ n N hnN d B r hθ hεθ (fun z hz => hε z ⟨d, hz⟩)
      (fun F hF hfar => hind F (fun z hz => ⟨d, hF z hz⟩) hfar)
  have hsub : {ω | ¬ PercEnclosure n N {z | ω ∉ B z}} ⊆
      ({ω | ¬ PercAnnCross n N .T {z | ω ∉ B z}} ∪ {ω | ¬ PercAnnCross n N .B {z | ω ∉ B z}}) ∪
      ({ω | ¬ PercAnnCross n N .R {z | ω ∉ B z}} ∪
        {ω | ¬ PercAnnCross n N .L {z | ω ∉ B z}}) := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    apply hω
    exact perc_annulus_enclosure n N (by exact_mod_cast hn) (by exact_mod_cast hnN) _
      (fun d => by cases d <;> tauto)
  calc μ {ω | ¬ PercEnclosure n N {z | ω ∉ B z}}
      ≤ (μ {ω | ¬ PercAnnCross n N .T {z | ω ∉ B z}} +
          μ {ω | ¬ PercAnnCross n N .B {z | ω ∉ B z}}) +
        (μ {ω | ¬ PercAnnCross n N .R {z | ω ∉ B z}} +
          μ {ω | ¬ PercAnnCross n N .L {z | ω ∉ B z}}) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
        gcongr <;> exact measure_union_le _ _
    _ ≤ 4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) := by
        have h4 := add_le_add (add_le_add (hd .T) (hd .B)) (add_le_add (hd .R) (hd .L))
        refine h4.trans (le_of_eq ?_)
        ring

end LQGMetric
