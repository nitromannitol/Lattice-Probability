/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X13 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X12

/-!
# DZZ Lemma 3.12: helpers for the four sides of the coarse ring (D93 §2, packet P-6a)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1461–1477),
ring form of DEC-93 §2.

* `side_meet'` (list form of `side_meet`), `spl_bounds`, `home_not_parent`, `cross_of_list`;
* `SideW`, **`coarseRing_of_sideW`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma side_meet' {n N : ℤ} (hn : 0 ≤ n) (hnN : n ≤ N) {d e : PercDir} (hd : d = .T ∨ d = .B)
    (he : e = .R ∨ e = .L) {X Y : List (ℤ × ℤ)} (hX0 : X ≠ []) (hY0 : Y ≠ [])
    (hX : X.IsChain PercAdj4) (hY : Y.IsChain PercAdj4)
    (hXR : ∀ z ∈ X, z ∈ annRect n N d) (hYR : ∀ z ∈ Y, z ∈ annRect n N e)
    (hXh : ∀ a ∈ X.head?, annLong d a = -N) (hXl : ∀ b ∈ X.getLast?, annLong d b = N)
    (hYh : ∀ a ∈ Y.head?, annLong e a = -N) (hYl : ∀ b ∈ Y.getLast?, annLong e b = N) :
    ∃ m, m ∈ X ∧ m ∈ Y := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hX0
  obtain ⟨a', l', rfl⟩ := List.exists_cons_of_ne_nil hY0
  exact side_meet hn hnN hd he hX hY hXR hYR (hXh a rfl)
    (hXl _ (List.getLast?_eq_some_getLast _)) (hYh a' rfl)
    (hYl _ (List.getLast?_eq_some_getLast _))

lemma spl_bounds (j h : ℕ) : -(h : ℤ) ≤ spl j h ∧ spl j h ≤ h := by
  unfold spl; split_ifs <;> omega

/-- The home region (`(near, near)`) lies in no parent cell. -/
lemma home_not_parent {C : DyBox} {k h : ℕ} (hC : IsCell m δ C) (hC1 : 1 ≤ C.n)
    (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h) {z : ℤ × ℤ} (hz : InGrid (C.n + k) (l37c C h) z)
    (hN : annBox (2 * (h : ℤ) - 2) z) (hx : farB C.j h z.1 = false)
    (hy : farB C.k h z.2 = false) (P : DyBox) (hP : IsParent m δ C P) :
    ¬ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox := by
  intro hs
  have hlt := n_lt_of_side_lt hP.2.1
  rw [sub_anc_iff (L := C.n - 1) (by omega) (by show C.n - 1 ≤ C.n + k; omega),
    anc_home hC1 hK hh hz hN hx hy] at hs
  exact not_isCell_of_sub hC hlt ((closedBox_sub_anc C (C.n - 1)).trans hs) hP.1

/-- A side list is a long-way crossing of its sites. -/
lemma cross_of_list {n N : ℤ} (hn : 0 ≤ n) {e : PercDir} {X : List (ℤ × ℤ)} {S : Set (ℤ × ℤ)}
    (hX0 : X ≠ []) (hX : X.IsChain PercAdj4) (hXR : ∀ z ∈ X, z ∈ annRect n N e)
    (hXS : ∀ z ∈ X, z ∈ S)
    (hXh : ∀ a ∈ X.head?, annLong e a = -N) (hXl : ∀ b ∈ X.getLast?, annLong e b = N) :
    PercClipCross n N e (-N) N S := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hX0
  refine ⟨a, (a :: l).getLast (List.cons_ne_nil _ _), hXh a rfl,
    hXl _ (List.getLast?_eq_some_getLast _),
    annRect_sub_clipRect (hXR a List.mem_cons_self), hXS a List.mem_cons_self, ?_⟩
  exact percStepIn_mono (S := {z | z ∈ a :: l}) (S' := {z | z ∈ clipRect n N e (-N) N ∧ z ∈ S})
    (fun z hz => ⟨annRect_sub_clipRect (hXR z hz), hXS z hz⟩) (fun _ _ h => h)
    (rtg_of_isChain_list a l hX fun z hz => hz)

/-- One side of the closed walk, in walk order, from corner `ci` (meeting point `mi`) to
corner `co` (meeting point `mo`). -/
def SideW (m : DyBox → ℝ) (δ : ℝ) (C : DyBox) (k h d : ℕ) (L F H : List (ℤ × ℤ))
    (ci co mi mo : ℤ × ℤ) : Prop :=
  (L ++ F ++ H).IsChain PercAdj4 ∧ (mi ∈ L ∨ (L = [] ∧ mi ∈ F)) ∧
    (mo ∈ H ∨ (H = [] ∧ mo ∈ F)) ∧
    (∀ z ∈ L ++ F ++ H, InGrid (C.n + k) (l37c C h) z ∧ annBox (2 * (h : ℤ) - 2) z ∧
      ∃ e, (h : ℤ) + 2 ≤ annDir e z) ∧
    (∀ z ∈ F, (∀ bt ∈ boxCollBdry (siteBox (C.n + k) (l37c C h) z) d, m bt < δ ^ 2) ∧
      ∀ P, IsParent m δ C P → ¬ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
    (∀ z ∈ L, (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
      ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
        (siteBox (C.n + k) (l37c C h) ci).closedBox ⊆ P.closedBox)) ∧
    (∀ z ∈ H, (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
      ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
        (siteBox (C.n + k) (l37c C h) co).closedBox ⊆ P.closedBox)) ∧
    ((∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) ci).closedBox ⊆ P.closedBox) →
      (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) co).closedBox ⊆ P.closedBox) →
      F = [])

/-- **The coarse ring from four walk sides** (wrapper of `coarseRing_of_sides`). -/
theorem coarseRing_of_sideW {C : DyBox} {k h d : ℕ} (hK : 2 ^ k = 2 * h)
    {L₁ F₁ H₁ L₂ F₂ H₂ L₃ F₃ H₃ L₄ F₄ H₄ : List (ℤ × ℤ)} {c₀ c₁ c₂ c₃ m₀ m₁ m₂ m₃ : ℤ × ℤ}
    (S₁ : SideW m δ C k h d L₁ F₁ H₁ c₀ c₁ m₀ m₁) (S₂ : SideW m δ C k h d L₂ F₂ H₂ c₁ c₂ m₁ m₂)
    (S₃ : SideW m δ C k h d L₃ F₃ H₃ c₂ c₃ m₂ m₃) (S₄ : SideW m δ C k h d L₄ F₄ H₄ c₃ c₀ m₃ m₀)
    (hhome : ∀ P, IsParent m δ C P →
      ¬ (siteBox (C.n + k) (l37c C h) c₀).closedBox ⊆ P.closedBox)
    (h13 : ∀ P, IsParent m δ C P →
      (siteBox (C.n + k) (l37c C h) c₁).closedBox ⊆ P.closedBox →
      (siteBox (C.n + k) (l37c C h) c₃).closedBox ⊆ P.closedBox → False)
    (hsep : ∀ M : Set DyBox, (∀ z ∈ L₁ ++ F₁ ++ H₁, siteBox (C.n + k) (l37c C h) z ∈ M) →
      (∀ z ∈ L₂ ++ F₂ ++ H₂, siteBox (C.n + k) (l37c C h) z ∈ M) →
      (∀ z ∈ L₃ ++ F₃ ++ H₃, siteBox (C.n + k) (l37c C h) z ∈ M) →
      (∀ z ∈ L₄ ++ F₄ ++ H₄, siteBox (C.n + k) (l37c C h) z ∈ M) → EnclosesBox C M)
    (hnt : ∃ z ∈ L₁ ++ F₁ ++ H₁, ∃ z' ∈ L₁ ++ F₁ ++ H₁,
      siteBox (C.n + k) (l37c C h) z ≠ siteBox (C.n + k) (l37c C h) z') :
    ∃ l, CoarseRing m δ C k d l := by
  obtain ⟨c1, u1, v1, s1, f1, l1, h1, -⟩ := S₁
  obtain ⟨c2, u2, v2, s2, f2, l2, h2, e2⟩ := S₂
  obtain ⟨c3, u3, v3, s3, f3, l3, h3, e3⟩ := S₃
  obtain ⟨c4, u4, v4, s4, f4, l4, h4, -⟩ := S₄
  refine coarseRing_of_sides hK c1 c2 c3 c4 u1 v1 u2 v2 u3 v3 u4 v4 ?_ ?_ ?_ hhome e2 e3 h13
    (fun M hM => hsep M (fun z hz => hM z (Or.inl hz)) (fun z hz => hM z (Or.inr (Or.inl hz)))
      (fun z hz => hM z (Or.inr (Or.inr (Or.inl hz))))
      (fun z hz => hM z (Or.inr (Or.inr (Or.inr hz))))) hnt
  · rintro z (hz | hz | hz | hz)
    · exact s1 z hz
    · exact s2 z hz
    · exact s3 z hz
    · exact s4 z hz
  · rintro z (hz | hz | hz | hz)
    · exact f1 z hz
    · exact f2 z hz
    · exact f3 z hz
    · exact f4 z hz
  · rintro z c (⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨hz, rfl⟩ |
      ⟨hz, rfl⟩ | ⟨hz, rfl⟩)
    · exact l1 z hz
    · exact h1 z hz
    · exact l2 z hz
    · exact h2 z hz
    · exact l3 z hz
    · exact h3 z hz
    · exact l4 z hz
    · exact h4 z hz

end DZZ
end LQGMetric
