/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.AnnulusClip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusPeierls

/-!
# Square annuli clipped to a rectangle: rectangles, crossings, Peierls bound, exits

Tools for `perc_annulus_peierls_clip` (`LQGMetric.Perc.AnnulusClipMain`, decision D72): the
Peierls bound for good enclosures of the annulus `n ≤ ‖z‖_∞ ≤ N` clipped to a rectangle
`R = annClip ext = {z | annDir d z ≤ ext d for every side d}`. Target statement (also in
`handoff/P2-PERCCLIP.md`):

```
theorem perc_annulus_peierls_clip {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n N : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (ext : PercDir → ℤ) (hext : ∀ d, -(n : ℤ) ≤ ext d)
    (hTB : (N : ℤ) < ext .T ∨ (N : ℤ) < ext .B) (hRL : (N : ℤ) < ext .R ∨ (N : ℤ) < ext .L)
    (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞}
    (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ z, annClip ext z → (∃ d, z ∈ annRect n N d) → μ (B z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, annClip ext z ∧ ∃ d, z ∈ annRect n N d) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)) :
    μ {ω | ¬ PercEnclosureClip n N ext {z | ω ∉ B z}} ≤
      4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1))
```

Context: Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1009–1016) take an open
enclosure "separating `B` from `𝕍 ∩ ∂B_large` in `𝕍`" for boxes `B` near `∂𝕍` without comment;
the clipped version of the rectangle-crossing construction of `perc_annulus_enclosure` (Grimmett,
*Percolation*, 2nd ed., §11.7; DDLGD Fig. 4) is the D72 route. Here: the clipped side rectangle
`clipRect n N d lo hi` (long coordinate in `[lo, hi]`), the meeting of long-way and short-way
crossings in it (`clipRect_meet`, transport of `percGoodLR_meets_percBadTB`), its Peierls bound
(`perc_clipRect_peierls`, transport of `perc_peierls`), and the exit lemma `ann_exit_clip`
(`PercAnn.ann_exit` remembering that the path leaves through a side `d` with `N < ext d`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LQGMetric

/-- The rectangle `R = {z | annDir d z ≤ ext d for every side d}`, i.e.
`-ext L ≤ z.1 ≤ ext R`, `-ext B ≤ z.2 ≤ ext T`. -/
def annClip (ext : PercDir → ℤ) (z : ℤ × ℤ) : Prop := ∀ d, annDir d z ≤ ext d

/-- A good enclosure of the annulus `n ≤ ‖z‖_∞ ≤ N` clipped to `R = annClip ext`: a
`4`-connected nonempty set of sites of `G ∩ R` in the annulus, met by every `*`-path inside `R`
from the hole `‖z‖_∞ < n` to the outside `‖z‖_∞ > N`. -/
def PercEnclosureClip (n N : ℤ) (ext : PercDir → ℤ) (G : Set (ℤ × ℤ)) : Prop :=
  ∃ U : Set (ℤ × ℤ), (∀ z ∈ U, z ∈ G ∧ annClip ext z ∧ ∃ d, z ∈ annRect n N d) ∧ U.Nonempty ∧
    (∀ x ∈ U, ∀ y ∈ U, Relation.ReflTransGen (PercStepIn U PercAdj4) x y) ∧
    (∀ (Γ : Set (ℤ × ℤ)) (s e : ℤ × ℤ), (∀ z ∈ Γ, annClip ext z) →
      (-n < s.1 ∧ s.1 < n ∧ -n < s.2 ∧ s.2 < n) → ¬ annBox N e →
      Relation.ReflTransGen (PercStepIn Γ PercAdjK) s e → ∃ z ∈ U, z ∈ Γ)

/-- The part `lo ≤ annLong d ≤ hi` of the side rectangle `n ≤ annDir d ≤ N`. -/
def clipRect (n N : ℤ) (d : PercDir) (lo hi : ℤ) : Set (ℤ × ℤ) :=
  {z | lo ≤ annLong d z ∧ annLong d z ≤ hi ∧ n ≤ annDir d z ∧ annDir d z ≤ N}

/-- The long-way crossing of `clipRect n N d lo hi` by good sites. -/
def PercClipCross (n N : ℤ) (d : PercDir) (lo hi : ℤ) (G : Set (ℤ × ℤ)) : Prop :=
  ∃ a b, annLong d a = lo ∧ annLong d b = hi ∧ a ∈ clipRect n N d lo hi ∧ a ∈ G ∧
    Relation.ReflTransGen (PercStepIn {z | z ∈ clipRect n N d lo hi ∧ z ∈ G} PercAdj4) a b

namespace PercClip

/-- The isometry carrying `clipRect n N d lo hi` onto `[0, hi - lo] × [0, N - n]`. -/
def clipStd (n lo : ℤ) (d : PercDir) (z : ℤ × ℤ) : ℤ × ℤ := (annLong d z - lo, annDir d z - n)

/-- The inverse of `clipStd`. -/
def clipFromStd (n lo : ℤ) : PercDir → ℤ × ℤ → ℤ × ℤ
  | .T, x => (x.1 + lo, x.2 + n)
  | .B, x => (x.1 + lo, -(x.2 + n))
  | .R, x => (x.2 + n, x.1 + lo)
  | .L, x => (-(x.2 + n), x.1 + lo)

lemma clipStd_adj4 (n lo : ℤ) (d : PercDir) {x y : ℤ × ℤ} (h : PercAdj4 x y) :
    PercAdj4 (clipStd n lo d x) (clipStd n lo d y) := by
  cases d <;> simp only [clipStd, annLong, annDir, PercAdj4] at h ⊢ <;> omega

lemma clipStd_adjK (n lo : ℤ) (d : PercDir) {x y : ℤ × ℤ} (h : PercAdjK x y) :
    PercAdjK (clipStd n lo d x) (clipStd n lo d y) := by
  cases d <;> simp only [clipStd, annLong, annDir, PercAdjK] at h ⊢ <;> omega

lemma clipStd_inj (n lo : ℤ) (d : PercDir) {x y : ℤ × ℤ}
    (h : clipStd n lo d x = clipStd n lo d y) : x = y := by
  rw [Prod.ext_iff] at h ⊢
  cases d <;> simp only [clipStd, annLong, annDir] at h <;> omega

lemma clipStd_grid (n N lo hi : ℤ) (d : PercDir) {z : ℤ × ℤ} (hz : z ∈ clipRect n N d lo hi) :
    percInGrid (hi - lo + 1) (N - n + 1) (clipStd n lo d z) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  simp only [clipStd, percInGrid]
  omega

lemma clipFromStd_inj (n lo : ℤ) (d : PercDir) {x y : ℤ × ℤ}
    (h : clipFromStd n lo d x = clipFromStd n lo d y) : x = y := by
  rw [Prod.ext_iff] at h ⊢
  cases d <;> simp only [clipFromStd] at h <;> omega

lemma clipFromStd_mem (n N lo hi : ℤ) (d : PercDir) {x : ℤ × ℤ}
    (hx : percInGrid (hi - lo + 1) (N - n + 1) x) : clipFromStd n lo d x ∈ clipRect n N d lo hi := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  cases d <;> simp only [clipFromStd, clipRect, annLong, annDir, Set.mem_ofPred_eq] <;> omega

lemma clipFromStd_adj4 (n lo : ℤ) (d : PercDir) {x y : ℤ × ℤ} (h : PercAdj4 x y) :
    PercAdj4 (clipFromStd n lo d x) (clipFromStd n lo d y) := by
  cases d <;> simp only [clipFromStd, PercAdj4] at h ⊢ <;> omega

lemma clipFromStd_far (n lo : ℤ) (d : PercDir) (r : ℕ) {x y : ℤ × ℤ} (h : PercFar r x y) :
    PercFar r (clipFromStd n lo d x) (clipFromStd n lo d y) := by
  cases d <;> simp only [clipFromStd, PercFar] at h ⊢ <;> omega

end PercClip

open PercClip

/-- In a clipped side rectangle, a long-way `4`-crossing of sites of `A` and a short-way
`*`-crossing of sites of `C` share a site (transport of `percGoodLR_meets_percBadTB`). -/
theorem clipRect_meet (n N : ℤ) (d : PercDir) (lo hi : ℤ) (A C : Set (ℤ × ℤ))
    (hA : PercClipCross n N d lo hi A)
    (hC : ∃ c e, annDir d c = N ∧ annDir d e = n ∧ c ∈ clipRect n N d lo hi ∧ c ∈ C ∧
      Relation.ReflTransGen (PercStepIn {z | z ∈ clipRect n N d lo hi ∧ z ∈ C} PercAdjK) c e) :
    ∃ z, z ∈ clipRect n N d lo hi ∧ z ∈ A ∧ z ∈ C := by
  classical
  set φ := clipStd n lo d
  obtain ⟨a, b, ha, hb, haX, haA, hab⟩ := hA
  obtain ⟨c, e, hc, he, hcX, hcC, hce⟩ := hC
  set A' : Set (ℤ × ℤ) := φ '' {z | z ∈ clipRect n N d lo hi ∧ z ∈ A}
  set C' : Set (ℤ × ℤ) := φ '' {z | z ∈ clipRect n N d lo hi ∧ z ∈ C}
  obtain ⟨z', hz'g, ⟨z1, ⟨hz1X, hz1A⟩, hz1⟩, ⟨z2, ⟨hz2X, hz2C⟩, hz2⟩⟩ :=
    percGoodLR_meets_percBadTB (K := hi - lo + 1) (L := N - n + 1) A' C' (by
      refine ⟨φ a, φ b, ?_, ?_, clipStd_grid n N lo hi d haX, ⟨a, ⟨haX, haA⟩, rfl⟩, ?_⟩
      · simp only [φ, clipStd, ha]; omega
      · simp only [φ, clipStd, hb]; omega
      · refine Relation.ReflTransGen.lift φ (fun x y hxy => ?_) _ _ hab
        obtain ⟨hx, hy, hxy⟩ := hxy
        exact ⟨clipStd_grid n N lo hi d hx.1, ⟨x, hx, rfl⟩, clipStd_grid n N lo hi d hy.1,
          ⟨y, hy, rfl⟩, clipStd_adj4 n lo d hxy⟩) (by
      refine ⟨φ c, φ e, ?_, ?_, clipStd_grid n N lo hi d hcX,
        not_not.mpr ⟨c, ⟨hcX, hcC⟩, rfl⟩, ?_⟩
      · simp only [φ, clipStd, hc]; omega
      · simp only [φ, clipStd, he]; omega
      · refine Relation.ReflTransGen.lift φ (fun x y hxy => ?_) _ _ hce
        obtain ⟨hx, hy, hxy⟩ := hxy
        exact ⟨clipStd_grid n N lo hi d hx.1, not_not.mpr ⟨x, hx, rfl⟩,
          clipStd_grid n N lo hi d hy.1, not_not.mpr ⟨y, hy, rfl⟩, clipStd_adjK n lo d hxy⟩)
  have : z1 = z2 := clipStd_inj n lo d (hz1.trans hz2.symm)
  subst this
  exact ⟨z1, hz1X, hz1A, hz2C⟩

/-- Peierls bound for one clipped side rectangle (long side `hi - lo + 1 ≤ 2N + 1`). -/
lemma perc_clipRect_peierls {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n N : ℕ)
    (hnN : n ≤ N) (d : PercDir) (lo hi : ℤ) (hlh : lo ≤ hi) (hlen : hi - lo ≤ 2 * (N : ℤ))
    (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞}
    (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ z, z ∈ clipRect n N d lo hi → μ (B z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, z ∈ clipRect n N d lo hi) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)) :
    μ {ω | ¬ PercClipCross n N d lo hi {z | ω ∉ B z}} ≤
      (2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1) := by
  classical
  set ψ := clipFromStd (n : ℤ) lo d
  set K : ℕ := (hi - lo + 1).toNat with hKdef
  have hK : ((K : ℕ) : ℤ) = hi - lo + 1 := by rw [hKdef]; omega
  have hL : (((N - n + 1 : ℕ) : ℤ)) = (N : ℤ) - n + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hnN]; simp
  have hK1 : 1 ≤ K := by omega
  have hK2 : K ≤ 2 * N + 1 := by omega
  have hgrid : ∀ x, percInGrid ((K : ℕ) : ℤ) ((N - n + 1 : ℕ) : ℤ) x →
      ψ x ∈ clipRect n N d lo hi := fun x hx =>
      clipFromStd_mem n N lo hi d (by rwa [hK, hL] at hx)
  have key := perc_peierls μ K (N - n + 1) hK1 (by omega) (fun x => B (ψ x)) r
    hθ hεθ (fun x hx => hε _ (hgrid x hx)) (fun F hF hfar => by
      have hinj : Set.InjOn ψ F := fun x _ y _ h => clipFromStd_inj n lo d h
      have e1 : (⋂ x ∈ F, B (ψ x)) = ⋂ z ∈ F.image ψ, B z := by
        rw [Finset.set_biInter_finset_image]
      rw [e1, ← Finset.prod_image (f := fun z => μ (B z)) hinj]
      refine hind _ (fun z hz => ?_) (fun x hx y hy hxy => ?_)
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        exact hgrid w (hF w hw)
      · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
        exact clipFromStd_far n lo d r (hfar x' hx' y' hy' fun h => hxy (h ▸ rfl)))
  refine le_trans (measure_mono fun ω hω => ?_) (key.trans ?_)
  · intro hstd
    apply hω
    rw [hK, hL] at hstd
    obtain ⟨a, b, ha, hb, hag, haG, hab⟩ := hstd
    refine ⟨ψ a, ψ b, ?_, ?_, clipFromStd_mem n N lo hi d hag, haG, ?_⟩
    · cases d <;> simp only [ψ, clipFromStd, annLong] <;> omega
    · cases d <;> simp only [ψ, clipFromStd, annLong] <;> omega
    · refine Relation.ReflTransGen.lift ψ (fun x y hxy => ?_) _ _ hab
      obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
      exact ⟨⟨clipFromStd_mem n N lo hi d h1, h2⟩, ⟨clipFromStd_mem n N lo hi d h3, h4⟩,
        clipFromStd_adj4 n lo d h5⟩
  · gcongr

namespace PercClip

open PercAnn in
/-- A `*`-path inside `R` from the hole to the outside contains a short-way crossing of the side
rectangle of a side `d` through which `R` reaches past the annulus (`N < ext d`). -/
lemma ann_exit_clip (n N : ℤ) (hnN : n ≤ N) (ext : PercDir → ℤ) (Γ : Set (ℤ × ℤ))
    (hΓ : ∀ z ∈ Γ, annClip ext z) {s e : ℤ × ℤ}
    (hs : -n < s.1 ∧ s.1 < n ∧ -n < s.2 ∧ s.2 < n) (he : ¬ annBox N e)
    (hse : Relation.ReflTransGen (PercStepIn Γ PercAdjK) s e) :
    ∃ d c e', N < ext d ∧ annDir d c = n ∧ annDir d e' = N ∧ c ∈ annRect n N d ∧ c ∈ Γ ∧
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ Γ} PercAdjK) c e' := by
  have key : (annBox N e ∧ ∀ d, annDir d e ≤ n ∨ ∃ c, annDir d c = n ∧ c ∈ annRect n N d ∧
      c ∈ Γ ∧ Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ Γ} PercAdjK) c e) ∨
      ∃ d c e', N < ext d ∧ annDir d c = n ∧ annDir d e' = N ∧ c ∈ annRect n N d ∧ c ∈ Γ ∧
        Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ Γ} PercAdjK) c e' := by
    clear he
    induction hse with
    | refl =>
      refine Or.inl ⟨⟨by omega, by omega, by omega, by omega⟩, fun d => Or.inl ?_⟩
      cases d <;> simp only [annDir] <;> omega
    | @tail z z' _ hst ih =>
      rcases ih with ⟨hbox, hd⟩ | hr
      · have hadj := hst.2.2
        by_cases hb' : annBox N z'
        · refine Or.inl ⟨hb', fun d => ?_⟩
          have hdd := annDir_adjK d hadj
          by_cases hz' : annDir d z' ≤ n
          · exact Or.inl hz'
          · have hz'X : z' ∈ annRect n N d := ⟨hb', by omega⟩
            rcases hd d with h | ⟨c, hc, hcX, hcΓ, hcz⟩
            · have hzX : z ∈ annRect n N d := ⟨hbox, by omega⟩
              exact Or.inr ⟨z, by omega, hzX, hst.1,
                Relation.ReflTransGen.single ⟨⟨hzX, hst.1⟩, ⟨hz'X, hst.2.1⟩, hadj⟩⟩
            · have hzX := rtg_end_mem hcz ⟨hcX, hcΓ⟩
              exact Or.inr ⟨c, hc, hcX, hcΓ, hcz.tail ⟨hzX, ⟨hz'X, hst.2.1⟩, hadj⟩⟩
        · obtain ⟨d, hd'⟩ := exists_dir_of_not_annBox hb'
          have hext : N < ext d := lt_of_lt_of_le hd' (hΓ z' hst.2.1 d)
          have hdd := annDir_adjK d hadj
          have hzN := annBox_dir hbox d
          rcases hd d with h | ⟨c, hc, hcX, hcΓ, hcz⟩
          · exact Or.inr ⟨d, z, z, hext, by omega, by omega, ⟨hbox, by omega⟩, hst.1, .refl⟩
          · exact Or.inr ⟨d, c, z, hext, hc, by omega, hcX, hcΓ, hcz⟩
      · exact Or.inr hr
  rcases key with ⟨hb, -⟩ | hr
  · exact absurd hb he
  · exact hr

end PercClip

end LQGMetric
