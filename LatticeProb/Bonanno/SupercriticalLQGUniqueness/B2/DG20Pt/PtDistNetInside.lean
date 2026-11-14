/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNetInside at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNet

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem exists_pt_dist_net_inside (V : Set ℂ) (hV : Bornology.IsBounded V) :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, ∃ F : Finset ℂ,
      F.card ≤ C * 4 ^ k ∧ (∀ x ∈ F, x ∈ V) ∧
      ∀ z ∈ V, ∃ x ∈ F, dist z x < ((2 : ℝ)⁻¹) ^ (k + 2) := by
  classical
  obtain ⟨C, hC, hnet⟩ := exists_pt_dist_net V hV
  refine ⟨4 * C, by positivity, ?_⟩
  intro k
  by_cases hnon : V.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hnon
    obtain ⟨F₀, hcard₀, hcover₀⟩ := hnet (k + 1)
    let q : ℝ := ((2 : ℝ)⁻¹) ^ (k + 3)
    let G : Finset ℂ := F₀.filter (fun x => ∃ z ∈ V, dist z x < q)
    let rep (x : ℂ) : ℂ :=
      if h : ∃ z ∈ V, dist z x < q then Classical.choose h else z₀
    let F : Finset ℂ := G.image rep
    have hrep (x : ℂ) (hx : x ∈ G) : rep x ∈ V ∧ dist (rep x) x < q := by
      have h : ∃ z ∈ V, dist z x < q := (Finset.mem_filter.mp hx).2
      dsimp [rep]
      rw [dif_pos h]
      exact Classical.choose_spec h
    have hcard : F.card ≤ 4 * C * 4 ^ k := by
      calc
        F.card ≤ G.card := Finset.card_image_le
        _ ≤ F₀.card := Finset.card_filter_le _ _
        _ ≤ C * 4 ^ (k + 1) := hcard₀
        _ = 4 * C * 4 ^ k := by rw [pow_succ]; ring
    refine ⟨F, hcard, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (hrep y hy).1
    · intro z hz
      obtain ⟨x, hx, hzx⟩ := hcover₀ z hz
      have hqx : dist z x < q := by
        simpa only [q, show (k + 1) + 2 = k + 3 by omega] using hzx
      have hxG : x ∈ G := Finset.mem_filter.mpr ⟨hx, ⟨z, hz, hqx⟩⟩
      refine ⟨rep x, Finset.mem_image.mpr ⟨x, hxG, rfl⟩, ?_⟩
      have hr := (hrep x hxG).2
      have htri := dist_triangle z x (rep x)
      rw [dist_comm x (rep x)] at htri
      have hq : 2 * q = ((2 : ℝ)⁻¹) ^ (k + 2) := by
        dsimp [q]
        rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
        ring
      linarith
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro z hz
    exact False.elim (hnon ⟨z, hz⟩)

end SupercriticalLQGUniqueness.B2.DG20Pt
