/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.Basic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.DualityMain
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected




 





set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.LatticePath

open Set Metric
open scoped Convex

theorem short_segment_avoids {O : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    {x y : ℂ} (hxy : dist x y < δ)
    (hx : ∀ z ∈ O, δ ≤ dist x z) :
    [x -[ℝ] y] ⊆ Oᶜ := by
  have hseg : [x -[ℝ] y] ⊆ ball x δ :=
    (convex_ball x δ).segment_subset (mem_ball_self hδ)
      (Metric.mem_ball.mpr (by simpa only [dist_comm] using hxy))
  intro z hz hO
  have hzball : dist z x < δ := hseg hz
  have hfar := hx z hO
  have : dist x z < δ := by simpa only [dist_comm] using hzball
  exact (not_lt_of_ge hfar) this

theorem short_step_joined {O : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    {x y : ℂ} (hxy : dist x y < δ)
    (hx : ∀ z ∈ O, δ ≤ dist x z) :
    JoinedIn Oᶜ x y :=
  JoinedIn.of_segment_subset (short_segment_avoids hδ hxy hx)

theorem white_reflTransGen_joined {α : Type*} {r : α → α → Prop}
    {O : Set ℂ} {δ : ℝ} (hδ : 0 < δ) (p : α → ℂ)
    (white : α → Prop)
    (hfar : ∀ a, white a → ∀ z ∈ O, δ ≤ dist (p a) z)
    (hstep : ∀ a b, r a b → white a ∧ white b ∧ dist (p a) (p b) < δ)
    {a b : α} (ha : white a) (hab : Relation.ReflTransGen r a b) :
    JoinedIn Oᶜ (p a) (p b) := by
  induction hab with
  | refl =>
      refine JoinedIn.refl ?_
      intro hO
      have h := hfar a ha (p a) hO
      have hzero : δ ≤ 0 := by simpa only [dist_self] using h
      exact (not_lt_of_ge hzero) hδ
  | @tail b c hab hbc ih =>
      obtain ⟨hb, _, hdist⟩ := hstep b c hbc
      exact ih.trans (short_step_joined hδ hdist (hfar b hb))

theorem badTB_joinedIn_compl {A B : ℤ} {good : ℤ × ℤ → Prop}
    {O : Set ℂ} {δ : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ → ℂ)
    (hfar : ∀ a, LQGMetric.percInGrid A B a → ¬ good a →
      ∀ z ∈ O, δ ≤ dist (p a) z)
    (hadj : ∀ a b, LQGMetric.PercAdjK a b → dist (p a) (p b) < δ)
    (hbad : LQGMetric.PercBadTB A B good) :
    ∃ a b : ℤ × ℤ, a.2 = B - 1 ∧ b.2 = 0 ∧
      LQGMetric.percInGrid A B a ∧ ¬ good a ∧
      JoinedIn Oᶜ (p a) (p b) := by
  obtain ⟨a, b, ha, hb, hgrid, hwhite, hab⟩ := hbad
  refine ⟨a, b, ha, hb, hgrid, hwhite, ?_⟩
  apply white_reflTransGen_joined (r := LQGMetric.PercBadStep A B good)
    hδ p (fun a => LQGMetric.percInGrid A B a ∧ ¬ good a)
  · intro c hc z hz
    exact hfar c hc.1 hc.2 z hz
  · intro c d (hcd : LQGMetric.PercBadStep A B good c d)
    exact ⟨⟨hcd.1, hcd.2.1⟩, ⟨hcd.2.2.1, hcd.2.2.2.1⟩,
      hadj c d hcd.2.2.2.2⟩
  · exact ⟨hgrid, hwhite⟩
  · exact hab

theorem short_step_joinedIn_diff {R O : Set ℂ} (hR : Convex ℝ R)
    {δ : ℝ} (hδ : 0 < δ) {x y : ℂ} (hxR : x ∈ R) (hyR : y ∈ R)
    (hxy : dist x y < δ) (hx : ∀ z ∈ O, δ ≤ dist x z) :
    JoinedIn (R \ O) x y := by
  apply JoinedIn.of_segment_subset
  intro z hz
  exact ⟨hR.segment_subset hxR hyR hz, short_segment_avoids hδ hxy hx hz⟩

theorem white_reflTransGen_joinedIn_diff {α : Type*} {r : α → α → Prop}
    {R O : Set ℂ} (hR : Convex ℝ R) {δ : ℝ} (hδ : 0 < δ)
    (p : α → ℂ) (white : α → Prop)
    (hin : ∀ a, white a → p a ∈ R)
    (hfar : ∀ a, white a → ∀ z ∈ O, δ ≤ dist (p a) z)
    (hstep : ∀ a b, r a b → white a ∧ white b ∧ dist (p a) (p b) < δ)
    {a b : α} (ha : white a) (hab : Relation.ReflTransGen r a b) :
    JoinedIn (R \ O) (p a) (p b) := by
  induction hab with
  | refl =>
      refine JoinedIn.refl ⟨hin a ha, ?_⟩
      intro hO
      have h := hfar a ha (p a) hO
      have hzero : δ ≤ 0 := by simpa only [dist_self] using h
      exact (not_lt_of_ge hzero) hδ
  | @tail b c hab hbc ih =>
      obtain ⟨hb, hc, hdist⟩ := hstep b c hbc
      exact ih.trans (short_step_joinedIn_diff hR hδ (hin b hb) (hin c hc)
        hdist (hfar b hb))

theorem badTB_joinedIn_diff {A B : ℤ} {good : ℤ × ℤ → Prop}
    {R O : Set ℂ} (hR : Convex ℝ R) {δ : ℝ} (hδ : 0 < δ)
    (p : ℤ × ℤ → ℂ)
    (hin : ∀ a, LQGMetric.percInGrid A B a → p a ∈ R)
    (hfar : ∀ a, LQGMetric.percInGrid A B a → ¬ good a →
      ∀ z ∈ O, δ ≤ dist (p a) z)
    (hadj : ∀ a b, LQGMetric.PercAdjK a b → dist (p a) (p b) < δ)
    (hbad : LQGMetric.PercBadTB A B good) :
    ∃ a b : ℤ × ℤ, a.2 = B - 1 ∧ b.2 = 0 ∧
      LQGMetric.percInGrid A B a ∧ ¬ good a ∧
      LQGMetric.percInGrid A B b ∧
      JoinedIn (R \ O) (p a) (p b) := by
  obtain ⟨a, b, ha, hb, hgrid, hwhite, hab⟩ := hbad
  have hbgrid : LQGMetric.percInGrid A B b := by
    induction hab with
    | refl => exact hgrid
    | tail hab hbc ih => exact hbc.2.2.1
  refine ⟨a, b, ha, hb, hgrid, hwhite, hbgrid, ?_⟩
  apply white_reflTransGen_joinedIn_diff (r := LQGMetric.PercBadStep A B good)
    hR hδ p (fun a => LQGMetric.percInGrid A B a ∧ ¬ good a)
  · intro c hc
    exact hin c hc.1
  · intro c hc z hz
    exact hfar c hc.1 hc.2 z hz
  · intro c d (hcd : LQGMetric.PercBadStep A B good c d)
    exact ⟨⟨hcd.1, hcd.2.1⟩, ⟨hcd.2.2.1, hcd.2.2.2.1⟩,
      hadj c d hcd.2.2.2.2⟩
  · exact ⟨hgrid, hwhite⟩
  · exact hab

theorem goodLR_of_relative_cut {A B : ℤ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (good : ℤ × ℤ → Prop) {R O E F : Set ℂ} (hR : Convex ℝ R)
    {δ : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ → ℂ)
    (hin : ∀ a, LQGMetric.percInGrid A B a → p a ∈ R)
    (hfar : ∀ a, LQGMetric.percInGrid A B a → ¬ good a →
      ∀ z ∈ O, δ ≤ dist (p a) z)
    (hadj : ∀ a b, LQGMetric.PercAdjK a b → dist (p a) (p b) < δ)
    (htop : ∀ a, LQGMetric.percInGrid A B a → a.2 = B - 1 → p a ∈ E)
    (hbottom : ∀ a, LQGMetric.percInGrid A B a → a.2 = 0 → p a ∈ F)
    (hcut : ∀ (x y : ℂ) (γ : Path x y), x ∈ E → y ∈ F →
      range γ ⊆ R → (range γ ∩ O).Nonempty) :
    LQGMetric.PercGoodLR A B good := by
  rcases LQGMetric.percGoodLR_or_percBadTB A B good hA hB with hgood | hbad
  · exact hgood
  · exfalso
    obtain ⟨a, b, ha, hb, hagrid, _, hbgrid, hj⟩ :=
      badTB_joinedIn_diff hR hδ p hin hfar hadj hbad
    have hγR : range hj.somePath ⊆ R := by
      intro z hz
      obtain ⟨t, ht⟩ := hz
      rw [← ht]
      exact (hj.somePath_mem t).1
    obtain ⟨z, hzγ, hzO⟩ :=
      hcut (p a) (p b) hj.somePath (htop a hagrid ha)
        (hbottom b hbgrid hb) hγR
    obtain ⟨t, ht⟩ := hzγ
    rw [← ht] at hzO
    exact (hj.somePath_mem t).2 hzO

theorem near_obstacle_goodLR_of_relative_cut {A B : ℤ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {R O E F : Set ℂ} (hR : Convex ℝ R)
    {δ : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ → ℂ)
    (hin : ∀ a, LQGMetric.percInGrid A B a → p a ∈ R)
    (hadj : ∀ a b, LQGMetric.PercAdjK a b → dist (p a) (p b) < δ)
    (htop : ∀ a, LQGMetric.percInGrid A B a → a.2 = B - 1 → p a ∈ E)
    (hbottom : ∀ a, LQGMetric.percInGrid A B a → a.2 = 0 → p a ∈ F)
    (hcut : ∀ (x y : ℂ) (γ : Path x y), x ∈ E → y ∈ F →
      range γ ⊆ R → (range γ ∩ O).Nonempty) :
    LQGMetric.PercGoodLR A B (fun a => ∃ z ∈ O, dist (p a) z < δ) := by
  apply goodLR_of_relative_cut hA hB _ hR hδ p hin
  · intro a _ hnot z hz
    exact le_of_not_gt (fun h => hnot ⟨z, hz, h⟩)
  · exact hadj
  · exact htop
  · exact hbottom
  · exact hcut

theorem relative_cut_of_disconnects {K R E F I J : Set ℂ}
    (hsep : LQGMetric.Disconnects K I J)
    (hE : E ⊆ I) (hF : F ⊆ J) :
    ∀ (x y : ℂ) (γ : Path x y), x ∈ E → y ∈ F →
      range γ ⊆ R → (range γ ∩ (K ∩ R)).Nonempty := by
  intro x y γ hx hy hγR
  obtain ⟨z, hzγ, hzK⟩ := hsep x y γ (hE hx) (hF hy)
  exact ⟨z, hzγ, hzK, hγR hzγ⟩

theorem near_clipped_goodLR_of_disconnects {A B : ℤ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {K R E F I J : Set ℂ} (hR : Convex ℝ R)
    (hsep : LQGMetric.Disconnects K I J)
    (hE : E ⊆ I) (hF : F ⊆ J)
    {δ : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ → ℂ)
    (hin : ∀ a, LQGMetric.percInGrid A B a → p a ∈ R)
    (hadj : ∀ a b, LQGMetric.PercAdjK a b → dist (p a) (p b) < δ)
    (htop : ∀ a, LQGMetric.percInGrid A B a → a.2 = B - 1 → p a ∈ E)
    (hbottom : ∀ a, LQGMetric.percInGrid A B a → a.2 = 0 → p a ∈ F) :
    LQGMetric.PercGoodLR A B
      (fun a => ∃ z ∈ K ∩ R, dist (p a) z < δ) := by
  exact near_obstacle_goodLR_of_relative_cut hA hB hR hδ p hin hadj
    htop hbottom (relative_cut_of_disconnects hsep hE hF)

theorem nearby_components_eq {ι : Type*} (C : ι → Set ℂ)
    {δ ε : ℝ} (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j,
      2 * δ + ε ≤ dist x y)
    {a b : ℂ} {i j : ι} (hab : dist a b < ε)
    (hi : ∃ x ∈ C i, dist a x < δ)
    (hj : ∃ y ∈ C j, dist b y < δ) : i = j := by
  by_contra hij
  obtain ⟨x, hxi, hax⟩ := hi
  obtain ⟨y, hyj, hby⟩ := hj
  have hxy := hsep i j hij x hxi y hyj
  have htri : dist x y ≤ dist x a + dist a b + dist b y := by
    calc
      dist x y ≤ dist x a + dist a y := dist_triangle x a y
      _ ≤ dist x a + (dist a b + dist b y) := by
        gcongr
        exact dist_triangle a b y
      _ = dist x a + dist a b + dist b y := by ring
  rw [dist_comm x a] at htri
  linarith

theorem good_reflTransGen_component {α ι : Type*} {r : α → α → Prop}
    (p : α → ℂ) (C : ι → Set ℂ) (good : α → Prop)
    {δ ε : ℝ}
    (hnear : ∀ a, good a → ∃ i, ∃ x ∈ C i, dist (p a) x < δ)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j,
      2 * δ + ε ≤ dist x y)
    (hstep : ∀ a b, r a b → good a ∧ good b ∧ dist (p a) (p b) < ε)
    {a b : α} (ha : good a) (hab : Relation.ReflTransGen r a b) :
    ∃ i, (∃ x ∈ C i, dist (p a) x < δ) ∧
      (∃ y ∈ C i, dist (p b) y < δ) := by
  induction hab with
  | refl =>
      obtain ⟨i, x, hx, hax⟩ := hnear a ha
      exact ⟨i, ⟨x, hx, hax⟩, ⟨x, hx, hax⟩⟩
  | @tail b c hab hbc ih =>
      obtain ⟨i, hia, hib⟩ := ih
      obtain ⟨_, hc, hdist⟩ := hstep b c hbc
      obtain ⟨j, hjc⟩ := hnear c hc
      have hij : i = j := nearby_components_eq C hsep hdist hib hjc
      subst j
      exact ⟨i, hia, hjc⟩

theorem goodLR_near_one_component {A B : ℤ} {good : ℤ × ℤ → Prop}
    (p : ℤ × ℤ → ℂ) {ι : Type*} (C : ι → Set ℂ)
    {δ ε : ℝ}
    (hnear : ∀ a, good a → ∃ i, ∃ x ∈ C i, dist (p a) x < δ)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j,
      2 * δ + ε ≤ dist x y)
    (hadj : ∀ a b, LQGMetric.PercAdj4 a b → dist (p a) (p b) < ε)
    (hgood : LQGMetric.PercGoodLR A B good) :
    ∃ a b : ℤ × ℤ, a.1 = 0 ∧ b.1 = A - 1 ∧
      ∃ i, (∃ x ∈ C i, dist (p a) x < δ) ∧
        (∃ y ∈ C i, dist (p b) y < δ) := by
  obtain ⟨a, b, ha, hb, _, hga, hab⟩ := hgood
  refine ⟨a, b, ha, hb, ?_⟩
  apply good_reflTransGen_component p C good hnear hsep
  · intro c d (hcd : LQGMetric.PercGoodStep A B good c d)
    exact ⟨hcd.2.1, hcd.2.2.2.1, hadj c d hcd.2.2.2.2⟩
  · exact hga
  · exact hab

theorem clipped_crossing_near_one_component {A B : ℤ}
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    {K R E F I J : Set ℂ} (hR : Convex ℝ R)
    (hdisconnect : LQGMetric.Disconnects K I J)
    (hE : E ⊆ I) (hF : F ⊆ J)
    {δ ε : ℝ} (hδ : 0 < δ) (p : ℤ × ℤ → ℂ)
    (hin : ∀ a, LQGMetric.percInGrid A B a → p a ∈ R)
    (hadjK : ∀ a b, LQGMetric.PercAdjK a b → dist (p a) (p b) < δ)
    (hadj4 : ∀ a b, LQGMetric.PercAdj4 a b → dist (p a) (p b) < ε)
    (htop : ∀ a, LQGMetric.percInGrid A B a → a.2 = B - 1 → p a ∈ E)
    (hbottom : ∀ a, LQGMetric.percInGrid A B a → a.2 = 0 → p a ∈ F)
    {ι : Type*} (C : ι → Set ℂ) (hcover : K ∩ R ⊆ ⋃ i, C i)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j,
      2 * δ + ε ≤ dist x y) :
    ∃ a b : ℤ × ℤ, a.1 = 0 ∧ b.1 = A - 1 ∧
      ∃ i, (∃ x ∈ C i, dist (p a) x < δ) ∧
        (∃ y ∈ C i, dist (p b) y < δ) := by
  have hgood := near_clipped_goodLR_of_disconnects hA hB hR hdisconnect
    hE hF hδ p hin hadjK htop hbottom
  apply goodLR_near_one_component p C
    (good := fun a => ∃ z ∈ K ∩ R, dist (p a) z < δ) ?_ hsep hadj4 hgood
  intro a ⟨z, hz, hdist⟩
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hcover hz)
  exact ⟨i, z, hzi, hdist⟩

theorem clipped_crossing_near_tangential_sides {A B : ℤ}
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
    (hleft : ∀ a, a.1 = 0 → p a ∈ S)
    (hright : ∀ a, a.1 = A - 1 → p a ∈ T)
    {ι : Type*} (C : ι → Set ℂ) (hcover : K ∩ R ⊆ ⋃ i, C i)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j,
      2 * δ + ε ≤ dist x y) :
    ∃ i, (∃ x ∈ C i, ∃ s ∈ S, dist x s < δ) ∧
      (∃ y ∈ C i, ∃ t ∈ T, dist y t < δ) := by
  obtain ⟨a, b, ha, hb, i, ⟨x, hxi, hax⟩, ⟨y, hyi, hby⟩⟩ :=
    clipped_crossing_near_one_component hA hB hR hdisconnect hE hF hδ p
      hin hadjK hadj4 htop hbottom C hcover hsep
  exact ⟨i, ⟨x, hxi, p a, hleft a ha, by simpa only [dist_comm] using hax⟩,
    ⟨y, hyi, p b, hright b hb, by simpa only [dist_comm] using hby⟩⟩

theorem compact_hits_closed_of_arbitrarily_near {C S : Set ℂ}
    (hC : IsCompact C) (hS : IsClosed S)
    (hnear : ∀ δ : ℝ, 0 < δ → ∃ x ∈ C, ∃ y ∈ S, dist x y < δ) :
    (C ∩ S).Nonempty := by
  by_contra hno
  have hdisj : Disjoint C S := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hno ⟨x, hx, hy⟩
  obtain ⟨r, hr, hfar⟩ := exists_pos_forall_lt_edist hC hS hdisj
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨x, hx, y, hy, hxy⟩ := hnear r hrR
  have hxy' : edist x y < (r : ENNReal) := by
    rw [edist_lt_coe]
    exact_mod_cast hxy
  exact (lt_asymm (hfar x hx y hy) hxy')

theorem finite_choice_arbitrarily_near {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ i {δ ε : ℝ}, δ ≤ ε → P i δ → P i ε)
    (h : ∀ δ : ℝ, 0 < δ → ∃ i ∈ s, P i δ) :
    ∃ i ∈ s, ∀ δ : ℝ, 0 < δ → P i δ := by
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨i, hi, _⟩ := h 1 (by norm_num)
      simp at hi
  | @insert a s ha ih =>
      by_cases haP : ∀ δ : ℝ, 0 < δ → P a δ
      · exact ⟨a, Finset.mem_insert_self a s, haP⟩
      · push Not at haP
        obtain ⟨δ₀, hδ₀, hnot⟩ := haP
        have hs : ∀ δ : ℝ, 0 < δ → ∃ i ∈ s, P i δ := by
          intro δ hδ
          let ε : ℝ := min δ δ₀ / 2
          have hε : 0 < ε := half_pos (lt_min hδ hδ₀)
          obtain ⟨i, hi, hPi⟩ := h ε hε
          have hieq : i ≠ a := by
            intro e
            subst i
            have hεδ₀ : ε ≤ δ₀ := by
              dsimp [ε]
              have hmin := min_le_right δ δ₀
              linarith
            exact hnot (hmono a hεδ₀ hPi)
          have hεmc : ε ≤ δ := by
            dsimp [ε]
            have hmin := min_le_left δ δ₀
            linarith
          exact ⟨i, (Finset.mem_insert.mp hi).resolve_left hieq,
            hmono i hεmc hPi⟩
        obtain ⟨i, hi, hPi⟩ := ih hs
        exact ⟨i, Finset.mem_insert_of_mem hi, hPi⟩

theorem finite_compact_component_touches_both {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ) {S T : Set ℂ}
    (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hS : IsClosed S) (hT : IsClosed T)
    (hnear : ∀ δ : ℝ, 0 < δ →
      ∃ i ∈ s, (∃ x ∈ C i, ∃ y ∈ S, dist x y < δ) ∧
        (∃ x ∈ C i, ∃ y ∈ T, dist x y < δ)) :
    ∃ i ∈ s, (C i ∩ S).Nonempty ∧ (C i ∩ T).Nonempty := by
  let P : ι → ℝ → Prop := fun i δ =>
    (∃ x ∈ C i, ∃ y ∈ S, dist x y < δ) ∧
      (∃ x ∈ C i, ∃ y ∈ T, dist x y < δ)
  have hmono : ∀ i {δ ε : ℝ}, δ ≤ ε → P i δ → P i ε := by
    intro i δ ε hδε ⟨⟨x, hx, y, hy, hxy⟩, ⟨u, hu, v, hv, huv⟩⟩
    exact ⟨⟨x, hx, y, hy, hxy.trans_le hδε⟩,
      ⟨u, hu, v, hv, huv.trans_le hδε⟩⟩
  obtain ⟨i, hi, hiNear⟩ := finite_choice_arbitrarily_near s P hmono hnear
  refine ⟨i, hi, ?_, ?_⟩
  · exact compact_hits_closed_of_arbitrarily_near (hcompact i hi) hS
      (fun δ hδ => (hiNear δ hδ).1)
  · exact compact_hits_closed_of_arbitrarily_near (hcompact i hi) hT
      (fun δ hδ => (hiNear δ hδ).2)

def gridPoint (h : ℝ) (a : ℤ × ℤ) : ℂ :=
  ⟨h * (a.1 : ℝ), h * (a.2 : ℝ)⟩

theorem gridPoint_adjK_dist_le (h : ℝ) (hh : 0 ≤ h)
    {a b : ℤ × ℤ} (hab : LQGMetric.PercAdjK a b) :
    dist (gridPoint h a) (gridPoint h b) ≤ 2 * h := by
  have h1 : |(a.1 : ℝ) - (b.1 : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast (show (-1 : ℤ) ≤ a.1 - b.1 by
        dsimp [LQGMetric.PercAdjK] at hab
        omega)
    · exact_mod_cast (show a.1 - b.1 ≤ (1 : ℤ) by
        dsimp [LQGMetric.PercAdjK] at hab
        omega)
  have h2 : |(a.2 : ℝ) - (b.2 : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast (show (-1 : ℤ) ≤ a.2 - b.2 by
        dsimp [LQGMetric.PercAdjK] at hab
        omega)
    · exact_mod_cast (show a.2 - b.2 ≤ (1 : ℤ) by
        dsimp [LQGMetric.PercAdjK] at hab
        omega)
  rw [dist_eq_norm]
  calc
    ‖gridPoint h a - gridPoint h b‖
        ≤ |(gridPoint h a - gridPoint h b).re| +
            |(gridPoint h a - gridPoint h b).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = h * |(a.1 : ℝ) - (b.1 : ℝ)| +
          h * |(a.2 : ℝ) - (b.2 : ℝ)| := by
      simp only [gridPoint, Complex.sub_re, Complex.sub_im,
        ← mul_sub, abs_mul, abs_of_nonneg hh]
    _ ≤ h * 1 + h * 1 := by gcongr
    _ = 2 * h := by ring

theorem adj4_imp_adjK {a b : ℤ × ℤ}
    (hab : LQGMetric.PercAdj4 a b) : LQGMetric.PercAdjK a b := by
  dsimp [LQGMetric.PercAdj4] at hab
  dsimp [LQGMetric.PercAdjK]
  rcases hab with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

theorem segPath_subPath_eq (a b : ℂ) {s t : ℝ} :
    LQGMetric.LFPP.subPath (LQGMetric.LFPP.segPath a b) s t =
      LQGMetric.LFPP.segPath (LQGMetric.LFPP.segPath a b s)
        (LQGMetric.LFPP.segPath a b t) := by
  funext u
  simp only [LQGMetric.LFPP.subPath, LQGMetric.LFPP.segPath]
  module

theorem segCost_subsegment_le (ξ : ℝ) (f : ℂ → ℝ) (a b : ℂ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    LQGMetric.LFPP.segCost ξ f (LQGMetric.LFPP.segPath a b s)
      (LQGMetric.LFPP.segPath a b t) ≤
        LQGMetric.LFPP.segCost ξ f a b := by
  open LQGMetric.LFPP in
    rw [segCost, ← segPath_subPath_eq, lfppLen_subPath (segPath a b) hst,
      segCost, lfppLen_eq]
  exact MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc hs ht)

theorem revPath_segPath_eq (a b : ℂ) :
    LQGMetric.LFPP.revPath (LQGMetric.LFPP.segPath a b) =
      LQGMetric.LFPP.segPath b a := by
  funext u
  simp only [LQGMetric.LFPP.revPath, LQGMetric.LFPP.segPath]
  module

theorem segCost_symm (ξ : ℝ) (f : ℂ → ℝ) (a b : ℂ) :
    LQGMetric.LFPP.segCost ξ f a b =
      LQGMetric.LFPP.segCost ξ f b a := by
  rw [LQGMetric.LFPP.segCost, ← revPath_segPath_eq,
    LQGMetric.LFPP.lfppLen_revPath, LQGMetric.LFPP.segCost]

theorem segCost_between_points_le (ξ : ℝ) (f : ℂ → ℝ) (a b : ℂ)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    LQGMetric.LFPP.segCost ξ f (LQGMetric.LFPP.segPath a b s)
      (LQGMetric.LFPP.segPath a b t) ≤ LQGMetric.LFPP.segCost ξ f a b := by
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact segCost_subsegment_le ξ f a b hs.1 hst ht.2
  · have hconst : LQGMetric.LFPP.segPath (LQGMetric.LFPP.segPath a b s)
        (LQGMetric.LFPP.segPath a b s) =
          fun _ => LQGMetric.LFPP.segPath a b s := by
      funext u
      simp [LQGMetric.LFPP.segPath]
    rw [LQGMetric.LFPP.segCost, hconst, LQGMetric.DDDF.lfppLen_const]
    exact bot_le
  · calc
      LQGMetric.LFPP.segCost ξ f (LQGMetric.LFPP.segPath a b s)
          (LQGMetric.LFPP.segPath a b t) =
          LQGMetric.LFPP.segCost ξ f (LQGMetric.LFPP.segPath a b t)
            (LQGMetric.LFPP.segPath a b s) :=
        segCost_symm ξ f _ _
      _ ≤ LQGMetric.LFPP.segCost ξ f a b :=
        segCost_subsegment_le ξ f a b ht.1 hts hs.2


end SupercriticalLQGUniqueness.Exponent.LatticePath

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set
open scoped Convex
open scoped ENNReal

 
theorem preconnected_subset_closed_cover {A U V : Set ℂ}
    (hA : IsPreconnected A) (hU : IsClosed U) (hV : IsClosed V)
    (hdisj : Disjoint U V) (hcover : A ⊆ U ∪ V)
    (hAU : (A ∩ U).Nonempty) : A ⊆ U := by
  by_contra hnot
  obtain ⟨y, hyA, hyU⟩ := Set.not_subset.mp hnot
  have hyV : y ∈ V := (hcover hyA).resolve_left hyU
  have hAV : (A ∩ V).Nonempty := ⟨y, hyA, hyV⟩
  have hAopen : A ⊆ Vᶜ ∪ Uᶜ := by
    intro z hz
    by_cases hzV : z ∈ V
    · exact Or.inr (by intro hzU; exact Set.disjoint_left.mp hdisj hzU hzV)
    · exact Or.inl hzV
  have hAU' : (A ∩ Vᶜ).Nonempty := by
    obtain ⟨x, hxA, hxU⟩ := hAU
    exact ⟨x, hxA, by intro hxV; exact Set.disjoint_left.mp hdisj hxU hxV⟩
  have hAV' : (A ∩ Uᶜ).Nonempty := ⟨y, hyA, hyU⟩
  obtain ⟨z, hzA, hzV, hzU⟩ := hA Vᶜ Uᶜ hV.isOpen_compl hU.isOpen_compl
    hAopen hAU' hAV'
  rcases hcover hzA with hzU' | hzV'
  · exact hzU hzU'
  · exact hzV hzV'

 
theorem overlap_reachable_of_preconnected_cover {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hclosed : ∀ k ∈ s, IsClosed (C k))
    {A : Set ℂ} (hA : IsPreconnected A)
    (hcover : A ⊆ ⋃ k ∈ s, C k)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hAi : (A ∩ C i).Nonempty) (hAj : (A ∩ C j).Nonempty) :
    Relation.ReflTransGen
      (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j := by
  classical
  let r : ι → ι → Prop := fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty
  let T : Finset ι := s.filter (fun k => Relation.ReflTransGen r i k)
  let U : Set ℂ := ⋃ k ∈ T, C k
  let V : Set ℂ := ⋃ k ∈ s \ T, C k
  have hU : IsClosed U := isClosed_biUnion_finset (s := T) (by
    intro k hk
    exact hclosed k (Finset.mem_filter.mp hk).1)
  have hV : IsClosed V := isClosed_biUnion_finset (s := s \ T) (by
    intro k hk
    exact hclosed k (Finset.mem_sdiff.mp hk).1)
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hxU hxV
    obtain ⟨k, hkT, hxk⟩ := Set.mem_iUnion₂.mp hxU
    obtain ⟨l, hlV, hxl⟩ := Set.mem_iUnion₂.mp hxV
    have hk : k ∈ s := (Finset.mem_filter.mp hkT).1
    have hl : l ∈ s := (Finset.mem_sdiff.mp hlV).1
    have hkl : r k l := ⟨hk, hl, ⟨x, hxk, hxl⟩⟩
    have hreach : Relation.ReflTransGen r i l :=
      (Finset.mem_filter.mp hkT).2.tail hkl
    exact (Finset.mem_sdiff.mp hlV).2 (Finset.mem_filter.mpr ⟨hl, hreach⟩)
  have hcov : A ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (hcover hx)
    by_cases hreach : Relation.ReflTransGen r i k
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hreach⟩, hxk⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr
        ⟨k, Finset.mem_sdiff.mpr ⟨hk, by
          intro hmem
          exact hreach (Finset.mem_filter.mp hmem).2⟩, hxk⟩)
  have hAU : (A ∩ U).Nonempty := by
    obtain ⟨x, hxA, hxi⟩ := hAi
    exact ⟨x, hxA, Set.mem_iUnion₂.mpr
      ⟨i, Finset.mem_filter.mpr ⟨hi, Relation.ReflTransGen.refl⟩, hxi⟩⟩
  have hAsubU := preconnected_subset_closed_cover hA hU hV hdisj hcov hAU
  by_contra hnot
  obtain ⟨y, hyA, hyj⟩ := hAj
  have hyV : y ∈ V := Set.mem_iUnion₂.mpr
    ⟨j, Finset.mem_sdiff.mpr ⟨hj, by
      intro hmem
      exact hnot (Finset.mem_filter.mp hmem).2⟩, hyj⟩
  exact Set.disjoint_left.mp hdisj (hAsubU hyA) hyV

 
theorem component_contains_of_overlap_reachable {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hpre : ∀ k ∈ s, IsPreconnected (C k))
    {i j : ι} (hi : i ∈ s) {x : ℂ} (hx : x ∈ C i)
    (hreach : Relation.ReflTransGen
      (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j) :
    C j ⊆ connectedComponentIn (⋃ k ∈ s, C k) x := by
  let K : Set ℂ := ⋃ k ∈ s, C k
  have hsubset : ∀ k ∈ s, C k ⊆ K := by
    intro k hk z hz
    exact Set.mem_iUnion₂.mpr ⟨k, hk, hz⟩
  induction hreach with
  | refl => exact (hpre i hi).subset_connectedComponentIn hx (hsubset i hi)
  | @tail k l hkl hstep ih =>
      obtain ⟨hk, hl, z, hzk, hzl⟩ := hstep
      have hzcomp : z ∈ connectedComponentIn K x := ih hzk
      have hCl : C l ⊆ connectedComponentIn K z :=
        (hpre l hl).subset_connectedComponentIn hzl (hsubset l hl)
      rwa [connectedComponentIn_eq hzcomp]

 
theorem overlap_reachable_of_component {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hclosed : ∀ k ∈ s, IsClosed (C k))
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    {x y : ℂ} (hx : x ∈ C i) (hy : y ∈ C j)
    (hcomp : y ∈ connectedComponentIn (⋃ k ∈ s, C k) x) :
    Relation.ReflTransGen
      (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j := by
  have hxK : x ∈ ⋃ k ∈ s, C k := Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
  exact overlap_reachable_of_preconnected_cover s C hclosed
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
    hi hj ⟨x, mem_connectedComponentIn hxK, hx⟩ ⟨y, hcomp, hy⟩

 
noncomputable def graphComponent {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ) (i : ι) : Set ℂ := by
  classical
  exact ⋃ j ∈ s.filter (fun j => Relation.ReflTransGen
    (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j), C j

 
theorem graphComponent_eq_connectedComponentIn {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hclosed : ∀ k ∈ s, IsClosed (C k))
    (hpre : ∀ k ∈ s, IsPreconnected (C k))
    {i : ι} (hi : i ∈ s) {x : ℂ} (hx : x ∈ C i) :
    graphComponent s C i = connectedComponentIn (⋃ k ∈ s, C k) x := by
  classical
  apply Set.Subset.antisymm
  · intro y hy
    change y ∈ ⋃ j ∈ s.filter (fun j => Relation.ReflTransGen
      (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j), C j at hy
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
    exact (component_contains_of_overlap_reachable s C hpre hi hx
      (Finset.mem_filter.mp hj).2) hyj
  · intro y hy
    have hyK : y ∈ ⋃ k ∈ s, C k := connectedComponentIn_subset _ _ hy
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hyK
    have hreach := overlap_reachable_of_component s C hclosed hi hj hx hyj hy
    change y ∈ ⋃ j ∈ s.filter (fun j => Relation.ReflTransGen
      (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j), C j
    exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hreach⟩, hyj⟩

 
theorem graphComponent_isCompact {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hcompact : ∀ k ∈ s, IsCompact (C k)) (i : ι) :
    IsCompact (graphComponent s C i) := by
  classical
  unfold graphComponent
  apply Finset.isCompact_biUnion
  intro j hj
  exact hcompact j (Finset.mem_filter.mp hj).1

 
theorem source_nonempty_of_overlap_reachable {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ) {i j : ι}
    (hreach : Relation.ReflTransGen
      (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j)
    (hj : (C j).Nonempty) : (C i).Nonempty := by
  induction hreach with
  | refl => exact hj
  | @tail k l hkl hstep ih =>
      obtain ⟨_, _, z, hzk, _⟩ := hstep
      exact ih ⟨z, hzk⟩

 
theorem graphComponent_disjoint_of_ne {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hclosed : ∀ k ∈ s, IsClosed (C k))
    (hpre : ∀ k ∈ s, IsPreconnected (C k))
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hneq : graphComponent s C i ≠ graphComponent s C j) :
    Disjoint (graphComponent s C i) (graphComponent s C j) := by
  classical
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hxi : (C i).Nonempty := by
    change z ∈ ⋃ k ∈ s.filter (fun k => Relation.ReflTransGen
      (fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty) i k), C k at hzi
    obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hzi
    exact source_nonempty_of_overlap_reachable s C (Finset.mem_filter.mp hk).2 ⟨z, hzk⟩
  obtain ⟨x, hx⟩ := hxi
  have hyi : z ∈ connectedComponentIn (⋃ k ∈ s, C k) x :=
    (graphComponent_eq_connectedComponentIn s C hclosed hpre hi hx) ▸ hzi
  have hzK : z ∈ ⋃ k ∈ s, C k := connectedComponentIn_subset _ _ hyi
  have hjnonempty : (C j).Nonempty := by
    change z ∈ ⋃ k ∈ s.filter (fun k => Relation.ReflTransGen
      (fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty) j k), C k at hzj
    obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hzj
    exact source_nonempty_of_overlap_reachable s C (Finset.mem_filter.mp hk).2 ⟨z, hzk⟩
  obtain ⟨y, hy⟩ := hjnonempty
  have hyj : z ∈ connectedComponentIn (⋃ k ∈ s, C k) y :=
    (graphComponent_eq_connectedComponentIn s C hclosed hpre hj hy) ▸ hzj
  have heq : connectedComponentIn (⋃ k ∈ s, C k) x =
      connectedComponentIn (⋃ k ∈ s, C k) y := by
    calc
      connectedComponentIn (⋃ k ∈ s, C k) x =
          connectedComponentIn (⋃ k ∈ s, C k) z := connectedComponentIn_eq hyi
      _ = connectedComponentIn (⋃ k ∈ s, C k) y := (connectedComponentIn_eq hyj).symm
  exact hneq ((graphComponent_eq_connectedComponentIn s C hclosed hpre hi hx).trans
    (heq.trans (graphComponent_eq_connectedComponentIn s C hclosed hpre hj hy).symm))

 

theorem clipped_segment_eq {R : Set ℂ} (hclosed : IsClosed R) (hconvex : Convex ℝ R)
    (a b : ℂ) (hne : ([a -[ℝ] b] ∩ R).Nonempty) :
    ∃ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧ s ≤ t ∧
      [a -[ℝ] b] ∩ R =
        [LQGMetric.LFPP.segPath a b s -[ℝ] LQGMetric.LFPP.segPath a b t] := by
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a b
  let D : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ f ⁻¹' R
  have hfcont : Continuous f := AffineMap.lineMap_continuous
  have hDcompact : IsCompact D :=
    (isCompact_Icc (a := (0 : ℝ)) (b := (1 : ℝ))).inter_right
      (hclosed.preimage hfcont)
  have hDconvex : Convex ℝ D := (convex_Icc (0 : ℝ) 1).inter (hconvex.affine_preimage f)
  have hDne : D.Nonempty := by
    rw [segment_eq_image_lineMap] at hne
    exact Set.image_inter_nonempty_iff.mp hne
  have hDeq : D = Set.Icc (sInf D) (sSup D) :=
    eq_Icc_of_connected_compact (hDconvex.isConnected hDne) hDcompact
  have hsD : sInf D ∈ D := hDcompact.isClosed.csInf_mem hDne hDcompact.bddBelow
  have htD : sSup D ∈ D := hDcompact.isClosed.csSup_mem hDne hDcompact.bddAbove
  have hst : sInf D ≤ sSup D := by
    exact ((le_of_eq hDeq) hsD).2
  refine ⟨sInf D, sSup D, hsD.1, htD.1, hst, ?_⟩
  calc
    [a -[ℝ] b] ∩ R = f '' D := by
      rw [segment_eq_image_lineMap, Set.image_inter_preimage]
    _ = f '' Set.Icc (sInf D) (sSup D) :=
      congrArg (fun E : Set ℝ => f '' E) hDeq
    _ = [f (sInf D) -[ℝ] f (sSup D)] := by
      rw [← segment_eq_Icc hst, image_segment]
    _ = [LQGMetric.LFPP.segPath a b (sInf D) -[ℝ]
          LQGMetric.LFPP.segPath a b (sSup D)] := by
      simp only [f, AffineMap.lineMap_apply_module, LQGMetric.LFPP.segPath]
      congr 1 <;> module

 
theorem clipped_segment_cost_le {R : Set ℂ} (hclosed : IsClosed R)
    (hconvex : Convex ℝ R) (a b : ℂ)
    (hne : ([a -[ℝ] b] ∩ R).Nonempty)
    (ξ : ℝ) (f : ℂ → ℝ) :
    ∃ p q : ℂ, [a -[ℝ] b] ∩ R = [p -[ℝ] q] ∧
      LQGMetric.LFPP.segCost ξ f p q ≤ LQGMetric.LFPP.segCost ξ f a b := by
  obtain ⟨s, t, hs, ht, _, heq⟩ := clipped_segment_eq hclosed hconvex a b hne
  exact ⟨LQGMetric.LFPP.segPath a b s, LQGMetric.LFPP.segPath a b t,
    heq, Exponent.LatticePath.segCost_between_points_le ξ f a b hs ht⟩

 
theorem simple_overlap_chain {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ) {i j : ι}
    (hreach : Relation.ReflTransGen
      (fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty) i j) :
    ∃ (l : List ι) (hne : l ≠ []),
      l.head hne = i ∧ l.getLast hne = j ∧ l.Nodup ∧
      l.IsChain (fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty) := by
  classical
  let r : ι → ι → Prop := fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty
  let G : SimpleGraph ι := SimpleGraph.fromRel r
  have hstep : ∀ u v : ι, r u v → G.Reachable u v := by
    intro u v huv
    by_cases hne : u = v
    · subst v
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (show G.Adj u v from ⟨hne, Or.inl huv⟩)
  have hpath : G.Reachable i j := by
    induction hreach with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hlast ih => exact ih.trans (hstep _ _ hlast)
  obtain ⟨w⟩ := hpath
  let p : G.Path i j := w.toPath
  refine ⟨(p : G.Walk i j).support, (p : G.Walk i j).support_ne_nil,
    ?_, ?_, p.nodup_support, ?_⟩
  · simpa only [List.head?_eq_some_head] using (p : G.Walk i j).head_support
  · exact (p : G.Walk i j).getLast_support
  · exact (p : G.Walk i j).isChain_adj_support.imp (by
      intro u v huv
      rcases huv.2 with hc | hc
      · exact hc
      · exact ⟨hc.2.1, hc.1, by simpa only [Set.inter_comm] using hc.2.2⟩)

 
theorem nodup_chain_charge_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (l : List ι) (w : ι → ℝ≥0∞)
    (hnodup : l.Nodup) (hsub : ∀ i ∈ l, i ∈ s) :
    (l.map w).sum ≤ ∑ i ∈ s, w i := by
  have hls : l.toFinset ⊆ s := by
    intro i hi
    exact hsub i (List.mem_toFinset.mp hi)
  rw [← List.sum_toFinset w hnodup]
  exact Finset.sum_le_sum_of_subset hls

 
theorem segCost_le_of_mem_segment (ξ : ℝ) (f : ℂ → ℝ)
    (a b z w : ℂ) (hz : z ∈ [a -[ℝ] b]) (hw : w ∈ [a -[ℝ] b]) :
    LQGMetric.LFPP.segCost ξ f z w ≤ LQGMetric.LFPP.segCost ξ f a b := by
  rw [segment_eq_image' ℝ a b] at hz hw
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := hw
  exact Exponent.LatticePath.segCost_between_points_le ξ f a b hs ht

 
theorem paid_path_of_overlap_chain {ι : Type*} (a b : ι → ℂ)
    {R : Set ℂ} (hR : Convex ℝ R) (ξ : ℝ) (f : ℂ → ℝ)
    (l : List ι) (hne : l ≠ [])
    (hchain : l.IsChain (fun i j =>
      (([a i -[ℝ] b i] ∩ R) ∩ ([a j -[ℝ] b j] ∩ R)).Nonempty))
    {z w : ℂ} (hz : z ∈ [a (l.head hne) -[ℝ] b (l.head hne)] ∩ R)
    (hw : w ∈ [a (l.getLast hne) -[ℝ] b (l.getLast hne)] ∩ R) :
    ∃ P : ℝ → ℂ, LQGMetric.IsPiecewiseC1Path P z w ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, P t ∈ R) ∧
      LQGMetric.lfppLen ξ f P ≤
        (l.map (fun i => LQGMetric.LFPP.segCost ξ f (a i) (b i))).sum := by
  induction l generalizing z with
  | nil => exact (hne rfl).elim
  | cons i tail ih =>
      cases tail with
      | nil =>
          refine ⟨LQGMetric.LFPP.segPath z w,
            LQGMetric.LFPP.isPiecewiseC1Path_segPath z w, ?_, ?_⟩
          · intro t ht
            exact LQGMetric.LFPP.segPath_mem hR hz.2 hw.2 ht
          · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
              LQGMetric.LFPP.segCost] using
                segCost_le_of_mem_segment ξ f (a i) (b i) z w hz.1 hw.1
      | cons j rest =>
          obtain ⟨hij, htail⟩ := List.isChain_cons_cons.mp hchain
          obtain ⟨q, hqi, hqj⟩ := hij
          have hneTail : j :: rest ≠ [] := by simp
          have hwTail : w ∈ [a ((j :: rest).getLast hneTail) -[ℝ]
              b ((j :: rest).getLast hneTail)] ∩ R := by
            simpa only [List.getLast_cons_cons] using hw
          obtain ⟨P, hP, hPin, hPlen⟩ := ih hneTail htail hqj hwTail
          let Q : ℝ → ℂ := LQGMetric.LFPP.concatPath (LQGMetric.LFPP.segPath z q) P
          have hjoin : LQGMetric.LFPP.segPath z q 1 = P 0 := by
            rw [hP.source]
            simp only [LQGMetric.LFPP.segPath, one_smul]
            abel
          refine ⟨Q, ?_, ?_, ?_⟩
          · exact LQGMetric.LFPP.isPiecewiseC1Path_concatPath
              (LQGMetric.LFPP.isPiecewiseC1Path_segPath z q) hP
          · intro t ht
            change LQGMetric.LFPP.concatPath (LQGMetric.LFPP.segPath z q) P t ∈ R
            unfold LQGMetric.LFPP.concatPath
            split_ifs with h
            · exact LQGMetric.LFPP.segPath_mem hR hz.2 hqi.2
                ⟨by linarith [ht.1], by linarith⟩
            · exact hPin (2 * t - 1) ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩
          · change LQGMetric.lfppLen ξ f
              (LQGMetric.LFPP.concatPath (LQGMetric.LFPP.segPath z q) P) ≤ _
            rw [LQGMetric.LFPP.lfppLen_concatPath hjoin]
            have hseg : LQGMetric.LFPP.segCost ξ f z q ≤
                LQGMetric.LFPP.segCost ξ f (a i) (b i) :=
              segCost_le_of_mem_segment ξ f (a i) (b i) z q hz.1 hqi.1
            simpa only [List.map_cons, List.sum_cons, LQGMetric.LFPP.segCost] using
              add_le_add hseg hPlen

 
theorem all_mem_of_overlap_chain {ι : Type*} (s : Finset ι)
    (C : ι → Set ℂ) (l : List ι) (hne : l ≠ [])
    (hfirst : l.head hne ∈ s)
    (hchain : l.IsChain (fun u v => u ∈ s ∧ v ∈ s ∧ (C u ∩ C v).Nonempty)) :
    ∀ k ∈ l, k ∈ s := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons i tail ih =>
      cases tail with
      | nil =>
          intro k hk
          have hki : k = i := by simpa only [List.mem_singleton] using hk
          subst k
          exact hfirst
      | cons j rest =>
          obtain ⟨hij, htail⟩ := List.isChain_cons_cons.mp hchain
          have hneTail : j :: rest ≠ [] := by simp
          have hallTail := ih hneTail hij.2.1 htail
          intro k hk
          rcases List.mem_cons.mp hk with rfl | hkt
          · exact hij.1
          · exact hallTail k hkt

 
theorem paid_admPath_of_overlap_reachable {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ)
    {R S T : Set ℂ} (hR : Convex ℝ R) (ξ : ℝ) (f : ℂ → ℝ)
    {i j : ι} (hi : i ∈ s) (_hj : j ∈ s)
    (hreach : Relation.ReflTransGen
      (fun u v => u ∈ s ∧ v ∈ s ∧
        (([a u -[ℝ] b u] ∩ R) ∩ ([a v -[ℝ] b v] ∩ R)).Nonempty) i j)
    {z w : ℂ} (hz : z ∈ [a i -[ℝ] b i] ∩ R) (hzS : z ∈ S)
    (hw : w ∈ [a j -[ℝ] b j] ∩ R) (hwT : w ∈ T) :
    ∃ P : ℝ → ℂ, LQGMetric.DDDF.AdmPath R S T P ∧
      LQGMetric.lfppLen ξ f P ≤
        ∑ k ∈ s, LQGMetric.LFPP.segCost ξ f (a k) (b k) := by
  classical
  let C : ι → Set ℂ := fun k => [a k -[ℝ] b k] ∩ R
  obtain ⟨l, hne, hhead, hlast, hnodup, hchain⟩ := simple_overlap_chain s C hreach
  have hchain' : l.IsChain (fun u v => (C u ∩ C v).Nonempty) :=
    hchain.imp (fun _ _ huv => huv.2.2)
  have hz' : z ∈ C (l.head hne) := by rw [hhead]; exact hz
  have hw' : w ∈ C (l.getLast hne) := by rw [hlast]; exact hw
  obtain ⟨P, hP, hPin, hlen⟩ :=
    paid_path_of_overlap_chain a b hR ξ f l hne hchain' hz' hw'
  have hfirst : l.head hne ∈ s := hhead ▸ hi
  have hall : ∀ k ∈ l, k ∈ s := all_mem_of_overlap_chain s C l hne hfirst hchain
  refine ⟨P, ⟨z, hzS, w, hwT, hP, hPin⟩, ?_⟩
  exact hlen.trans (nodup_chain_charge_le s l
    (fun k => LQGMetric.LFPP.segCost ξ f (a k) (b k)) hnodup hall)

end SupercriticalLQGUniqueness.Exponent.PaidDuality

