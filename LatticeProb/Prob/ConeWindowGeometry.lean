import LatticeProb.Prob.ConeWindowWitness

/-! # Least starts of cone-window witnesses -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The rational witness formula is equivalent to a least starting time for
both endpoint-minimum inequalities. The least start may equal the window's
left endpoint. -/
theorem mem_coneWindowWitness_iff_least_start
    (z : C(ℝ, ℝ) × C(ℝ, ℝ)) (l r x t : ℝ) :
    ((z, x), t) ∈ coneWindowWitness l r ↔
      l < x ∧ x < t ∧ t ≤ r ∧
      ∃ a : ℝ, l ≤ a ∧ a < x ∧
        IsLeast {s : ℝ | s ≤ t ∧ ∀ v ∈ Icc s t,
          z.1 t ≤ z.1 v ∧ z.2 t ≤ z.2 v} a := by
  let S : Set ℝ := {s | s ≤ t ∧ ∀ v ∈ Icc s t,
    z.1 t ≤ z.1 v ∧ z.2 t ≤ z.2 v}
  have hmono {s q : ℝ} (hs : s ∈ S) (hsq : s ≤ q) (hqt : q ≤ t) : q ∈ S := by
    refine ⟨hqt, ?_⟩
    intro v hv
    exact hs.2 v ⟨le_trans hsq hv.1, hv.2⟩
  have hclosed : IsClosed S := by
    have h₁ : IsClosed {s : ℝ | s ≤ t ∧ ∀ v ∈ Icc s t, z.1 t ≤ z.1 v} :=
      isClosed_moving_endpoint_minimum.preimage
        (show Continuous (fun s : ℝ => ((z.1, s), t)) by fun_prop)
    have h₂ : IsClosed {s : ℝ | s ≤ t ∧ ∀ v ∈ Icc s t, z.2 t ≤ z.2 v} :=
      isClosed_moving_endpoint_minimum.preimage
        (show Continuous (fun s : ℝ => ((z.2, s), t)) by fun_prop)
    convert h₁.inter h₂ using 1
    ext s
    simp only [S, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hst, h⟩
      exact ⟨⟨hst, fun v hv => (h v hv).1⟩, hst, fun v hv => (h v hv).2⟩
    · rintro ⟨⟨hst, h₁⟩, _, h₂⟩
      exact ⟨hst, fun v hv => ⟨h₁ v hv, h₂ v hv⟩⟩
  constructor
  · intro h
    rcases h with ⟨hlx, hxt, htr, ⟨q, hqx, hqt, hq⟩, hall⟩
    have hqS : (q : ℝ) ∈ S := ⟨hqt.le, hq⟩
    have hlower : ∀ s ∈ S, l ≤ s := by
      intro s hs
      by_contra hn
      have hsl : s < l := lt_of_not_ge hn
      obtain ⟨p, hsp, hpl⟩ := exists_rat_btwn hsl
      have hpt : (p : ℝ) < t := lt_trans hpl (lt_trans hlx hxt)
      have hpS := hmono hs hsp.le hpt.le
      exact hall p hpl ⟨hpt, hpS.2⟩
    have hleast : IsLeast S (sInf S) := hclosed.isLeast_csInf ⟨q, hqS⟩ ⟨l, hlower⟩
    refine ⟨hlx, hxt, htr, sInf S, hlower _ hleast.1, ?_, hleast⟩
    exact lt_of_le_of_lt (hleast.2 hqS) hqx
  · rintro ⟨hlx, hxt, htr, a, hla, hax, ha⟩
    obtain ⟨q, haq, hqx⟩ := exists_rat_btwn hax
    have hqt : (q : ℝ) < t := lt_trans hqx hxt
    have hqS := hmono ha.1 haq.le hqt.le
    refine ⟨hlx, hxt, htr, ⟨q, hqx, hqt, hqS.2⟩, ?_⟩
    intro p hpl hp
    have hpS : (p : ℝ) ∈ S := ⟨hp.1.le, hp.2⟩
    exact (not_le_of_gt (lt_of_lt_of_le hpl hla)) (ha.2 hpS)

end LatticeProb
