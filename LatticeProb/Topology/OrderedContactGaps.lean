import LatticeProb.Topology.CyclicContactGaps

/-! # Ordered contacts and accessible gaps -/

open Set Metric

namespace LatticeProb.Topology

/-- Three distinct values of a function on an interval can be represented in increasing order. -/
theorem exists_ordered_three_values {α : Type*} {f : ℝ → α} {s : Set ℝ}
    {x y z : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxy : f x ≠ f y) (hxz : f x ≠ f z) (hyz : f y ≠ f z) :
    ∃ a b c, c ∈ s ∧ a ∈ s ∧ b ∈ s ∧ a < b ∧ b < c ∧
      f a ≠ f b ∧ f a ≠ f c ∧ f b ≠ f c := by
  have hxy' : x ≠ y := fun h => hxy (congrArg f h)
  have hxz' : x ≠ z := fun h => hxz (congrArg f h)
  have hyz' : y ≠ z := fun h => hyz (congrArg f h)
  rcases lt_or_gt_of_ne hxy' with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hxz' with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hyz' with h₃ | h₃
  all_goals
    first
    | exact ⟨x, y, z, hz, hx, hy, by linarith, by linarith, hxy, hxz, hyz⟩
    | exact ⟨x, z, y, hy, hx, hz, by linarith, by linarith, hxz, hxy, hyz.symm⟩
    | exact ⟨y, x, z, hz, hy, hx, by linarith, by linarith, hxy.symm, hyz, hxz⟩
    | exact ⟨y, z, x, hx, hy, hz, by linarith, by linarith, hyz, hxy.symm, hxz.symm⟩
    | exact ⟨z, x, y, hy, hz, hx, by linarith, by linarith, hxz.symm, hyz.symm, hxy⟩
    | exact ⟨z, y, x, hx, hz, hy, by linarith, by linarith, hyz.symm, hxz.symm, hxy.symm⟩

/-- A periodic boundary parametrization selects accessible gaps between any three
contacts in distinct components of the intersection. -/
theorem exists_ordered_contacts_and_accessible_gaps {A B : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ A) (hB : IsClosed B)
    {f : ℝ → ℂ} {p : ℝ} (hf : Continuous f)
    (hfront : ∀ t, f t ∈ frontier A) (hperiod : Function.Periodic f p)
    (hcover : ∀ x ∈ A ∩ B, ∃ t ∈ Ico 0 p, f t = x)
    {x y z : ℂ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (hz : z ∈ A ∩ B)
    (hxy : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) y)
    (hxz : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) z)
    (hyz : connectedComponentIn (A ∩ B) y ≠ connectedComponentIn (A ∩ B) z) :
    ∃ a b c, a < b ∧ b < c ∧ c < a + p ∧
      f a ∈ A ∩ B ∧ f b ∈ A ∩ B ∧ f c ∈ A ∩ B ∧
      f b ∉ connectedComponentIn (A ∩ B) (f a) ∧
      f c ∉ connectedComponentIn (A ∩ B) (f b) ∧
      f a ∉ connectedComponentIn (A ∩ B) (f c) ∧
      ∃ t₁ ∈ Ioo a b, ∃ t₂ ∈ Ioo b c, ∃ t₃ ∈ Ioo c (a + p),
        ∀ t ∈ ({t₁, t₂, t₃} : Set ℝ),
          ∃ (q : ℂ) (P : Set ℂ), q ∈ (A ∪ B)ᶜ ∧ IsCompact P ∧ IsConnected P ∧
            f t ∈ P ∧ q ∈ P ∧ P ⊆ Bᶜ ∩ closure Aᶜ := by
  obtain ⟨tx, htx, hfx⟩ := hcover x hx
  obtain ⟨ty, hty, hfy⟩ := hcover y hy
  obtain ⟨tz, htz, hfz⟩ := hcover z hz
  let g : ℝ → Set ℂ := fun t => connectedComponentIn (A ∩ B) (f t)
  have hxy' : g tx ≠ g ty := by simpa only [g, hfx, hfy] using hxy
  have hxz' : g tx ≠ g tz := by simpa only [g, hfx, hfz] using hxz
  have hyz' : g ty ≠ g tz := by simpa only [g, hfy, hfz] using hyz
  have htx' : tx ∈ Ico (0 : ℝ) p ∩ {t | f t ∈ A ∩ B} := ⟨htx, by simpa only [mem_ofPred_eq, hfx] using hx⟩
  have hty' : ty ∈ Ico (0 : ℝ) p ∩ {t | f t ∈ A ∩ B} := ⟨hty, by simpa only [mem_ofPred_eq, hfy] using hy⟩
  have htz' : tz ∈ Ico (0 : ℝ) p ∩ {t | f t ∈ A ∩ B} := ⟨htz, by simpa only [mem_ofPred_eq, hfz] using hz⟩
  obtain ⟨a, b, c, hc, ha, hb, hab, hbc, habg, hacg, hbcg⟩ :=
    exists_ordered_three_values htx' hty' htz' hxy' hxz' hyz'
  have hca : c < a + p := by linarith [ha.1.1, hc.1.2]
  have habcomp : f b ∉ connectedComponentIn (A ∩ B) (f a) := by
    intro h
    exact habg (connectedComponentIn_eq h)
  have hbccomp : f c ∉ connectedComponentIn (A ∩ B) (f b) := by
    intro h
    exact hbcg (connectedComponentIn_eq h)
  have hcacomp : f a ∉ connectedComponentIn (A ∩ B) (f c) := by
    intro h
    exact hacg (connectedComponentIn_eq h).symm
  refine ⟨a, b, c, hab, hbc, hca, ha.2, hb.2, hc.2,
    habcomp, hbccomp, hcacomp, ?_⟩
  exact exists_three_accessible_cyclic_gaps e hB hab hbc hca hf.continuousOn
    (fun t _ => hfront t) (hperiod a) ha.2 hb.2 hc.2 habcomp hbccomp hcacomp

end LatticeProb.Topology
