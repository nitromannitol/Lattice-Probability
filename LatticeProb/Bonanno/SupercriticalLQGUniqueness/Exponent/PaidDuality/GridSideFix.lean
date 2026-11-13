/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.GridSideFix at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.Basic




 



set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set Metric
open scoped Convex

 
theorem good_chain_end_inGrid {A B : ℤ} {good : ℤ × ℤ → Prop}
    {a b : ℤ × ℤ} (ha : LQGMetric.percInGrid A B a)
    (hab : Relation.ReflTransGen (LQGMetric.PercGoodStep A B good) a b) :
    LQGMetric.percInGrid A B b := by
  induction hab with
  | refl => exact ha
  | tail _ hlast ih => exact hlast.2.2.1

 
theorem goodLR_near_one_component_grid {A B : ℤ} {good : ℤ × ℤ → Prop}
    (p : ℤ × ℤ → ℂ) {ι : Type*} (C : ι → Set ℂ)
    {δ ε : ℝ}
    (hnear : ∀ a, good a → ∃ i, ∃ x ∈ C i, dist (p a) x < δ)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j,
      2 * δ + ε ≤ dist x y)
    (hadj : ∀ a b, LQGMetric.PercAdj4 a b → dist (p a) (p b) < ε)
    (hgood : LQGMetric.PercGoodLR A B good) :
    ∃ a b : ℤ × ℤ, a.1 = 0 ∧ b.1 = A - 1 ∧
      LQGMetric.percInGrid A B a ∧ LQGMetric.percInGrid A B b ∧
      ∃ i, (∃ x ∈ C i, dist (p a) x < δ) ∧
        (∃ y ∈ C i, dist (p b) y < δ) := by
  obtain ⟨a, b, ha, hb, hgrid, hga, hab⟩ := hgood
  refine ⟨a, b, ha, hb, hgrid, good_chain_end_inGrid hgrid hab, ?_⟩
  apply Exponent.LatticePath.good_reflTransGen_component p C good hnear hsep
  · intro c d (hcd : LQGMetric.PercGoodStep A B good c d)
    exact ⟨hcd.2.1, hcd.2.2.2.1, hadj c d hcd.2.2.2.2⟩
  · exact hga
  · exact hab

 
theorem clipped_crossing_near_tangential_sides_grid {A B : ℤ}
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    {K R E F I J S T : Set ℂ} (hR : Convex ℝ R)
    (hdisconnect : LQGMetric.Disconnects K I J)
    (hE : E ⊆ I) (hF : F ⊆ J)
    {δ ε : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ → ℂ)
    (hin : ∀ a, LQGMetric.percInGrid A B a → p a ∈ R)
    (hadjK : ∀ a b, LQGMetric.PercAdjK a b → dist (p a) (p b) < δ)
    (hadj4 : ∀ a b, LQGMetric.PercAdj4 a b → dist (p a) (p b) < ε)
    (htop : ∀ a, LQGMetric.percInGrid A B a → a.2 = B - 1 → p a ∈ E)
    (hbottom : ∀ a, LQGMetric.percInGrid A B a → a.2 = 0 → p a ∈ F)
    (hleft : ∀ a, LQGMetric.percInGrid A B a → a.1 = 0 → p a ∈ S)
    (hright : ∀ a, LQGMetric.percInGrid A B a → a.1 = A - 1 → p a ∈ T)
    {ι : Type*} (C : ι → Set ℂ) (hcover : K ∩ R ⊆ ⋃ i, C i)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j,
      2 * δ + ε ≤ dist x y) :
    ∃ i, (∃ x ∈ C i, ∃ s ∈ S, dist x s < δ) ∧
      (∃ y ∈ C i, ∃ t ∈ T, dist y t < δ) := by
  have hgood := Exponent.LatticePath.near_clipped_goodLR_of_disconnects hA hB hR hdisconnect
    hE hF hδ p hin hadjK htop hbottom
  obtain ⟨a, b, ha, hb, hga, hgb, i, ⟨x, hxi, hax⟩, ⟨y, hyi, hby⟩⟩ :=
    goodLR_near_one_component_grid p C
      (good := fun a => ∃ z ∈ K ∩ R, dist (p a) z < δ)
      (by
        intro a ⟨z, hz, hdist⟩
        obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hcover hz)
        exact ⟨i, z, hzi, hdist⟩)
      hsep hadj4 hgood
  exact ⟨i, ⟨x, hxi, p a, hleft a hga ha, by simpa only [dist_comm] using hax⟩,
    ⟨y, hyi, p b, hright b hgb hb, by simpa only [dist_comm] using hby⟩⟩

end SupercriticalLQGUniqueness.Exponent.PaidDuality

