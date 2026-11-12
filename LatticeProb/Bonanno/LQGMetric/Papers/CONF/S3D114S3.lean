/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114S3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S1

/-!
# CONF Lemma 3.6, Step 3: on `{Ũ = 𝔘}` the filled ball avoids `cl 𝔘`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Step 3 of Lemma 3.6 (C:1431–1437: "`Ũ^𝔯` is the
union of the squares … which do not intersect `𝓑^•_τ`", so `𝓑^•_τ ∩ 𝔘 = ∅` on `{Ũ = 𝔘}`, the
reason why the conditioning event is determined by `h|_{ℂ∖𝔘}`); decision D114 §4 C2 (ii).

* `conf36_mem_confSq_floor`: every point lies in its floor square;
* `conf36_closure_confU_subset`: `cl 𝔘` is covered by the squares of `𝒮^z_{δr}(𝔸_{3r,4r}(z))`
  not in `T`;
* `conf36T_eq_subset_compl_closure`: if `conf36T δ r z B = T` then `B ⊆ (cl 𝔘)ᶜ`,
  `𝔘 = confU r δ z T`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- the floor index of `u` in the grid `z + εℤ²` -/
def conf36Flr (ε : ℝ) (z u : ℂ) : ℤ × ℤ := (⌊(u.re - z.re) / ε⌋, ⌊(u.im - z.im) / ε⌋)

theorem conf36_mem_confSq_floor {ε : ℝ} (hε : 0 < ε) (z u : ℂ) :
    u ∈ confSq ε z (conf36Flr ε z u) := by
  have a1 := Int.floor_le ((u.re - z.re) / ε)
  have a2 := Int.lt_floor_add_one ((u.re - z.re) / ε)
  have b1 := Int.floor_le ((u.im - z.im) / ε)
  have b2 := Int.lt_floor_add_one ((u.im - z.im) / ε)
  rw [le_div_iff₀ hε] at a1 b1
  rw [div_lt_iff₀ hε] at a2 b2
  simp only [confSq, conf36Flr, mem_ofPred_eq]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem conf36_isClosed_confSq (ε : ℝ) (z : ℂ) (k : ℤ × ℤ) : IsClosed (confSq ε z k) := by
  have c1 : Continuous fun w : ℂ => w.re := Complex.continuous_re
  have c2 : Continuous fun w : ℂ => w.im := Complex.continuous_im
  have e : confSq ε z k = ({w : ℂ | z.re + k.1 * ε ≤ w.re} ∩ {w : ℂ | w.re ≤ z.re + (k.1 + 1) * ε})
      ∩ ({w : ℂ | z.im + k.2 * ε ≤ w.im} ∩ {w : ℂ | w.im ≤ z.im + (k.2 + 1) * ε}) := by
    ext w; simp only [confSq, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [e]
  exact ((isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)).inter
    ((isClosed_le continuous_const c2).inter (isClosed_le c2 continuous_const))

open Classical in
theorem conf36_closure_confU_subset {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (z : ℂ)
    (T : Finset (ℤ × ℤ)) :
    closure (confU r δ z T) ⊆ ⋃ k ∈ (conf36Box δ).filter
      (fun k => k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)) ∧ k ∉ T),
      confSq (δ * r) z k := by
  refine closure_minimal (fun u hu => ?_) (isClosed_biUnion_finset fun k _ =>
    conf36_isClosed_confSq _ _ _)
  have hk := conf36_mem_confSq_floor (mul_pos hδ hr) z u
  have hidx : conf36Flr (δ * r) z u ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)) :=
    ⟨u, hk, hu.1⟩
  refine mem_iUnion₂.2 ⟨conf36Flr (δ * r) z u, Finset.mem_filter.2
    ⟨conf36_mem_box hδ hr z hidx, hidx, fun hT => hu.2 (mem_iUnion₂.2 ⟨_, hT, hk⟩)⟩, hk⟩

open Classical in
theorem conf36T_eq_subset_compl_closure {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) {z : ℂ}
    {B : Set ℂ} {T : Finset (ℤ × ℤ)} (hT : conf36T δ r z B = T) :
    B ⊆ (closure (confU r δ z T))ᶜ := by
  intro u huB hu
  obtain ⟨k, hk, hu'⟩ := mem_iUnion₂.1 (conf36_closure_confU_subset hδ hr z T hu)
  obtain ⟨-, hkI, hkT⟩ := Finset.mem_filter.1 hk
  exact hkT (hT ▸ conf36T_cov hδ hr hkI ⟨u, hu', huB⟩)

end LQGMetric.CONF
