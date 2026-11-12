/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X4

/-!
# DZZ Lemma 3.12: consecutive crossings of the annulus meet (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1471–1477)
and Lemma 3.7 (l. 1005–1016, the enclosure "by duality"), in the ring form of DEC-93 §2: the
long-way crossings of a horizontal and a vertical side rectangle of the annulus share a site, so
the four crossings glue into a closed walk (the corner step of `perc_annulus_enclosure_clip`,
`clip_corner`, keeping the common site).

* `rtg_of_isChain_list`: a `4`-chain list is a `4`-path through its own sites;
* **`side_meet`**;
* `clipFromStd_clipStd`, **`side_slab_cut`**: `slab_cut` in the coordinates of a side rectangle.

Own elementary arguments (Grimmett, *Percolation*, 2nd ed., §11.7, as in `clip_corner`), DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open PercClip PercAnn

/-- A chain list is a path through its sites, from its head to its last element. -/
lemma rtg_of_isChain_list {adj : ℤ × ℤ → ℤ × ℤ → Prop} {S : Set (ℤ × ℤ)} :
    ∀ (a : ℤ × ℤ) (l : List (ℤ × ℤ)), (a :: l).IsChain adj → (∀ z ∈ a :: l, z ∈ S) →
      Relation.ReflTransGen (PercStepIn S adj) a ((a :: l).getLast (List.cons_ne_nil _ _))
  | a, [], _, _ => by simpa using Relation.ReflTransGen.refl
  | a, b :: l, h, hS => by
    rw [List.isChain_cons_cons] at h
    have ih := rtg_of_isChain_list b l h.2 (fun z hz => hS z (List.mem_cons_of_mem _ hz))
    rw [List.getLast_cons_cons]
    exact Relation.ReflTransGen.head ⟨hS a List.mem_cons_self,
      hS b (List.mem_cons_of_mem _ List.mem_cons_self), h.1⟩ ih

lemma annRect_sub_clipRect {n N : ℤ} {d : PercDir} {z : ℤ × ℤ} (hz : z ∈ annRect n N d) :
    z ∈ clipRect n N d (-N) N := by
  obtain ⟨⟨b1, b2, b3, b4⟩, h⟩ := hz
  cases d <;> simp only [clipRect, annLong, annDir, Set.mem_ofPred_eq] at h ⊢ <;> omega

/-- **The long-way crossings of a horizontal and a vertical side rectangle share a site.** -/
theorem side_meet {n N : ℤ} (hn : 0 ≤ n) (hnN : n ≤ N) {d e : PercDir} (hd : d = .T ∨ d = .B)
    (he : e = .R ∨ e = .L) {a₁ a₂ : ℤ × ℤ} {l₁ l₂ : List (ℤ × ℤ)}
    (h₁ : (a₁ :: l₁).IsChain PercAdj4) (h₂ : (a₂ :: l₂).IsChain PercAdj4)
    (hl₁ : ∀ z ∈ a₁ :: l₁, z ∈ annRect n N d) (hl₂ : ∀ z ∈ a₂ :: l₂, z ∈ annRect n N e)
    (ha₁ : annLong d a₁ = -N) (hb₁ : annLong d ((a₁ :: l₁).getLast (List.cons_ne_nil _ _)) = N)
    (ha₂ : annLong e a₂ = -N) (hb₂ : annLong e ((a₂ :: l₂).getLast (List.cons_ne_nil _ _)) = N) :
    ∃ m, m ∈ a₁ :: l₁ ∧ m ∈ a₂ :: l₂ := by
  set ext : PercDir → ℤ := fun _ => N + 1
  have hext : ∀ d, -n ≤ ext d := fun _ => by simp only [ext]; omega
  have hlo : ∀ d, clipLo N ext d = -N := fun d => by
    cases d <;> simp only [clipLo, ext] <;> omega
  have hhi : ∀ d, clipHi N ext d = N := fun d => by
    cases d <;> simp only [clipHi, ext] <;> omega
  have hX : ∀ d z, z ∈ annRect n N d → z ∈ clipX n N ext d := fun d z hz => by
    simp only [clipX, hlo, hhi]; exact annRect_sub_clipRect hz
  set S₂ : Set (ℤ × ℤ) := {z | z ∈ a₂ :: l₂}
  have hp₂ := rtg_of_isChain_list (S := S₂) a₂ l₂ h₂ (fun z hz => hz)
  obtain ⟨p, hpN, hap, c, hc, hpc⟩ := clip_corner_short hn hnN hext hd he
    (by simp only [ext]; omega) S₂ (by rw [hlo]; exact ha₂) (by rw [hhi]; exact hb₂) hp₂
  have hpS : p ∈ S₂ := rtg_end_mem hap List.mem_cons_self
  have hpX : p ∈ clipX n N ext d := clipX_corner_sub hn hnN hext hd he (by simp only [ext]; omega)
    (by simp only [ext]; omega) (hX e p (hl₂ p hpS)) (by omega)
  obtain ⟨z, -, hzA, hzC⟩ := clipRect_meet n N d (-N) N {z | z ∈ a₁ :: l₁} S₂
    ⟨a₁, _, ha₁, hb₁, annRect_sub_clipRect (hl₁ a₁ List.mem_cons_self), List.mem_cons_self,
      percStepIn_mono (S' := {z | z ∈ clipRect n N d (-N) N ∧ z ∈ {z | z ∈ a₁ :: l₁}})
        (fun z hz => ⟨annRect_sub_clipRect (hl₁ z hz), hz⟩) (fun _ _ h => h)
        (rtg_of_isChain_list (S := {z | z ∈ a₁ :: l₁}) a₁ l₁ h₁ (fun z hz => hz))⟩
    ⟨p, c, hpN, hc, by simpa [clipX, hlo, hhi] using hpX, hpS,
      percStepIn_mono (S' := {z | z ∈ clipRect n N d (-N) N ∧ z ∈ S₂})
        (fun z hz => ⟨by
          have := clipX_corner_sub hn hnN hext hd he (by simp only [ext]; omega)
            (by simp only [ext]; omega) (hX e z (hl₂ z hz.1)) hz.2
          simpa [clipX, hlo, hhi] using this, hz.1⟩)
        (fun _ _ h => percAdjK_of_adj4 h) hpc⟩
  exact ⟨z, hzA, hzC⟩

lemma clipRect_sub_annRect {n N : ℤ} (hn : 0 ≤ n) {d : PercDir} {z : ℤ × ℤ}
    (hz : z ∈ clipRect n N d (-N) N) : z ∈ annRect n N d := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  refine ⟨?_, z3⟩
  cases d <;> simp only [annBox, annLong, annDir] at z1 z2 z3 z4 ⊢ <;> omega

lemma annLong_clipFromStd (n lo : ℤ) (d : PercDir) (w : ℤ × ℤ) :
    annLong d (clipFromStd n lo d w) = w.1 + lo := by
  cases d <;> simp [clipFromStd, annLong]

lemma annDir_clipFromStd (n lo : ℤ) (d : PercDir) (w : ℤ × ℤ) :
    annDir d (clipFromStd n lo d w) = w.2 + n := by
  cases d <;> simp [clipFromStd, annDir] <;> ring

lemma clipFromStd_clipStd (n lo : ℤ) (d : PercDir) (z : ℤ × ℤ) :
    clipFromStd n lo d (clipStd n lo d z) = z := by
  cases d <;> ext <;> simp [clipFromStd, clipStd, annLong, annDir]

/-- **Slab cut of a side crossing** (site coordinates of side `d`, long coordinate `annLong d`):
straight through `{annLong < t₁}`, then the crossing in `{t₁ ≤ annLong < t₂}`, then straight
through `{annLong ≥ t₂}`. -/
theorem side_slab_cut {n N : ℤ} (hn : 0 ≤ n) (d : PercDir) {t₁ t₂ : ℤ} (ht₁ : -N ≤ t₁) (ht₂ : t₂ ≤ N + 1)
    {G : Set (ℤ × ℤ)} (hX : PercClipCross n N d (-N) N G) :
    ∃ A M B : List (ℤ × ℤ), (A ++ M ++ B) ≠ [] ∧ (A ++ M ++ B).IsChain PercAdj4 ∧
      (∀ a ∈ (A ++ M ++ B).head?, annLong d a = -N) ∧
      (∀ b ∈ (A ++ M ++ B).getLast?, annLong d b = N) ∧
      (∀ z ∈ A ++ M ++ B, z ∈ annRect n N d) ∧ (∀ z ∈ A, annLong d z < t₁) ∧
      (∀ z ∈ M, z ∈ G ∧ t₁ ≤ annLong d z ∧ annLong d z < t₂) ∧ (∀ z ∈ B, t₂ ≤ annLong d z) := by
  obtain ⟨a, b, ha, hb, haR, haG, hab⟩ := hX
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hab
  set S : Set (ℤ × ℤ) := {z | z ∈ clipRect n N d (-N) N ∧ z ∈ G}
  have hmem : ∀ z ∈ a :: l, z ∈ S := chain_mem_of_stepIn hl ⟨haR, haG⟩
  set φ := clipStd n (-N) d
  set ψ := clipFromStd n (-N) d
  have hφR : ∀ z ∈ a :: l, StdRect (2 * N) (N - n) (φ z) ∧ z ∈ G := by
    intro z hz
    obtain ⟨⟨z1, z2, z3, z4⟩, hzG⟩ := hmem z hz
    refine ⟨?_, hzG⟩
    simp only [StdRect, φ, clipStd]; omega
  obtain ⟨A', M', B', hc, hne, h0, hW, hA, hM, hB⟩ := slab_cut (W := 2 * N) (H := N - n)
    (s₁ := t₁ + N) (s₂ := t₂ + N) (G := {w | ψ w ∈ G}) (by omega) (by omega) ((a :: l).map φ)
    ((List.isChain_map φ).2 (hl.imp fun x y h => clipStd_adj4 n (-N) d h.2.2))
    (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hw
      have e : ψ (φ z) = z := clipFromStd_clipStd n (-N) d z
      exact ⟨(hφR z hz).1, show ψ (φ z) ∈ G by rw [e]; exact (hφR z hz).2⟩)
    (by intro w hw; simp only [List.map_cons, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hw; subst hw; simp only [φ, clipStd, ha]; ring)
    (by
      intro w hw
      rw [List.getLast?_map, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast] at hw
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hw
      subst hw; simp only [φ, clipStd, hb]; ring)
    (by simp)
  have hstd : ∀ w, StdRect (2 * N) (N - n) w → ψ w ∈ annRect n N d := by
    intro w ⟨w1, w2, w3, w4⟩
    apply clipRect_sub_annRect hn
    simp only [clipRect, Set.mem_ofPred_eq, ψ, annLong_clipFromStd, annDir_clipFromStd]
    omega
  have hall : ∀ w ∈ A' ++ M' ++ B', StdRect (2 * N) (N - n) w := by
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · exact (hA w hw).1
    · exact (hM w hw).1
    · exact (hB w hw).1
  refine ⟨A'.map ψ, M'.map ψ, B'.map ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [← List.map_append] using hne
  · rw [← List.map_append, ← List.map_append]
    exact (List.isChain_map ψ).2 (hc.imp fun x y h => clipFromStd_adj4 n (-N) d h)
  · intro x hx
    rw [← List.map_append, ← List.map_append, List.head?_map] at hx
    obtain ⟨w, hw, rfl⟩ := Option.mem_map.1 hx
    simp only [ψ, annLong_clipFromStd, h0 w hw]; ring
  · intro x hx
    rw [← List.map_append, ← List.map_append, List.getLast?_map] at hx
    obtain ⟨w, hw, rfl⟩ := Option.mem_map.1 hx
    simp only [ψ, annLong_clipFromStd, hW w hw]; ring
  · intro z hz
    rw [← List.map_append, ← List.map_append] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    exact hstd w (hall w hw)
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    simp only [ψ, annLong_clipFromStd]; have := (hA w hw).2; omega
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    obtain ⟨-, hwG, h1, h2⟩ := hM w hw
    exact ⟨hwG, by simp only [ψ, annLong_clipFromStd]; omega,
      by simp only [ψ, annLong_clipFromStd]; omega⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    simp only [ψ, annLong_clipFromStd]; have := (hB w hw).2; omega

end DZZ
end LQGMetric
