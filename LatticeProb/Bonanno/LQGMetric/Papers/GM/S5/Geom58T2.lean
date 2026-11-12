/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58T2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58T1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Data

/-!
# GM Lemma 5.8: (T5) for the tubes `U_r^{x,y}` of the construction (task P2-M2M4, D83 P5)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3086–3091). For the data `D : L58Data` (`U = int ⋃_G S`, GM (5.24)):
near an end point `x ∈ P_i` the squares of `U` are those meeting `P_i` (the other paths are `R`
away, the tubes `V_j` lie near the `z_j`), so if `P_i` is a straight segment `{x − te : t ∈ [0,M]}`
near `x`, (T5) holds at `x` (`t5_of_segment`). Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

namespace L58Data

variable (D : L58Data)

/-- **(T5) at an end point `x` of a path `P_i` which is straight near `x`** -/
theorem t5 {i : ℕ} (hi : i ≤ D.m) {x e : ℂ} {M : ℝ} (hM : 0 ≤ M) (he : ‖e‖ = 1)
    (hrad : ∀ t ∈ Icc (0 : ℝ) M, x - (t : ℂ) * e ∈ D.P i)
    (hnear : ∀ p ∈ D.P i, dist p x < D.R → ∃ t ∈ Icc (0 : ℝ) M, p = x - (t : ℂ) * e)
    (hfar : ∀ j < D.m, 3 * D.R ≤ dist x (D.zs j)) :
    D.U ∩ ball x (4 * D.s) ⊆ connectedComponentIn (D.U ∩ ball x (5 * D.s)) x := by
  have hs := D.hs
  have hsR := D.hsR
  have hx : x ∈ D.P i := by simpa using hrad 0 ⟨le_rfl, hM⟩
  refine t5_of_segment D.isOpen_U hs he (fun t ht => D.P_subset_U hi (hrad t ht)) ?_
  intro w hwU hwx
  obtain ⟨g, hgG, hwg⟩ := mem_iUnion₂.1 (interior_subset hwU)
  refine ⟨g, openSq_subset_interior hgG, hwg, ?_⟩
  rcases Finset.mem_union.1 hgG with hg | hg
  · exfalso
    obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.1 hg
    have hj' := Finset.mem_range.1 hj
    have h1 := D.dist_le_of_F hj' hgj hwg
    have h2 := hfar j hj'
    linarith [dist_triangle x w (D.zs j), dist_comm x w]
  · obtain ⟨i', hi', hgi'⟩ := Finset.mem_biUnion.1 hg
    have hi'' : i' ≤ D.m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi')
    obtain ⟨c, hcS, hcP⟩ := (D.hQ i' hi'' g).1 hgi'
    have hcw := dist_le_of_mem_sq hcS hwg
    have hcx : dist c x < D.R := by linarith [dist_triangle c w x]
    have hii : i' = i := by
      by_contra hne
      have := D.hPsep i' hi'' i hi hne c hcP x hx
      linarith
    subst hii
    obtain ⟨t, ht, rfl⟩ := hnear c hcP hcx
    exact ⟨t, ht, hcS⟩

end L58Data

end LQGMetric.GM
