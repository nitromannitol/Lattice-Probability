import LatticeProb.Prob.Percolation.Peierls.Animals

/-!
# Closed connected sets in Bernoulli site percolation

The union bound and selected counting constant from Exploding-Sandpiles,
`Exploding/Support/ExtMHProof9.lean` and `Exploding/Support/ExtMHProof10.lean`
(Apache-2.0).
-/
namespace LatticeProb.Percolation.Peierls

open LatticeProb MeasureTheory LatticeProb.Percolation.LSS
open scoped BigOperators

variable {d : ℕ}

/-- Peierls estimate with an explicit constant. -/
theorem xmh5_starconn_closed_prob (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : Site d) (m : ℕ) :
    sitePercolation d q {ω : Site d → Bool |
        ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧ xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, ω x = false}
      ≤ (K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m := by
  classical
  obtain ⟨T, hTcard, hTmem⟩ := hK p m
  set T' : Finset (Finset (Site d)) := T.filter (fun F => F.card = m) with hT'
  have hsub : {ω : Site d → Bool |
        ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧ xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, ω x = false}
      ⊆ {ω : Site d → Bool | ∃ F ∈ T', ∀ x ∈ F, ω x = false} := by
    rintro ω ⟨F, hp, hcard, hconn, hcl⟩
    exact ⟨F, Finset.mem_filter.mpr ⟨hTmem F hp hcard hconn, hcard⟩, hcl⟩
  have hbound : sitePercolation d q
        {ω : Site d → Bool | ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ (T'.card : ENNReal) * ENNReal.ofReal (1 - q) ^ m :=
    le_trans (measure_mono hsub)
      (xmh_peierls_union h0 h1 T' m fun F hF => (Finset.mem_filter.mp hF).2)
  refine le_trans hbound ?_
  gcongr
  exact_mod_cast le_trans (Finset.card_filter_le _ _) hTcard

/-- Peierls union bound with an explicit constant. -/
theorem xmh5_finset_closed_prob (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (S : Finset (Site d)) (m : ℕ) :
    sitePercolation d q {ω : Site d → Bool |
        ∃ p ∈ S, ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ (S.card : ENNReal) * ((K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m) := by
  classical
  have hsub : {ω : Site d → Bool |
        ∃ p ∈ S, ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      = ⋃ p ∈ S, {ω : Site d → Bool |
          ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
            xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [hsub]
  refine le_trans (measure_biUnion_finset_le S _) ?_
  calc ∑ p ∈ S, sitePercolation d q {ω : Site d → Bool |
          ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
            xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ ∑ _p ∈ S, (K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m :=
        Finset.sum_le_sum fun p _ => xmh5_starconn_closed_prob K hK h0 h1 p m
    _ = (S.card : ENNReal) * ((K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The constant of `xmh_starCount`, used in the summability threshold. -/
noncomputable def xmh6_K (d : ℕ) : ℕ := Classical.choose (xmh_starCount d)

theorem xmh6_K_spec (d : ℕ) :
    ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ xmh6_K d ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T :=
  Classical.choose_spec (xmh_starCount d)

end LatticeProb.Percolation.Peierls
