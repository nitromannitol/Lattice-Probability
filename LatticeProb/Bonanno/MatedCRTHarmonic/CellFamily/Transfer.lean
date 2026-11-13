/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.Transfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Core
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Exit
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RItinerary

/-!
# Transfer a template itinerary to the frozen annular event

This is the deterministic part of the waypoint construction: `TemplateSeparation` separates the two target circles, the itinerary
lies strictly before the annular exit, and the cell-diameter estimate controls the exit cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic

private theorem cellFamily_mem_annulus_iff {z w : ℂ} {a b : ℝ} :
    w ∈ annulus z a b ↔ a ≤ ‖w - z‖ ∧ ‖w - z‖ < b := by
  rw [annulus, Set.mem_sdiff, mem_ball, mem_ball, dist_eq_norm, not_lt]
  exact and_comm

theorem verticesMeeting_annulus_finite {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ}
    (H : CellularEmbedding G o) (z : ℂ) (r : ℝ) :
    (verticesMeeting H.cell (annulus z (r / 2) (3 * r / 2))).Finite := by
  apply (H.locallyFinite_cell.finite_nonempty_inter_compact (isCompact_closedBall z (3 * r / 2))).subset
  intro x hx
  obtain ⟨w, hwx, hwa⟩ := hx
  refine ⟨w, hwx, ?_⟩
  have hball : w ∈ ball z (3 * r / 2) := by
    rw [annulus, Set.mem_sdiff] at hwa
    exact hwa.1
  exact ball_subset_closedBall hball

private theorem norm_le_of_diam_le {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ}
    (H : CellularEmbedding G o) {v : ℤ} {d : ℝ}
    (hdiam : Metric.diam (H.cell v) ≤ d) {a b : ℂ} (ha : a ∈ H.cell v) (hb : b ∈ H.cell v) :
    ‖a - b‖ ≤ d := by
  have h := (Metric.dist_le_diam_of_mem (H.isCompact_cell v).isBounded ha hb).trans hdiam
  simpa [dist_eq_norm] using h

/-- A finite template itinerary yields the frozen `AnnularEvent` on paths whose graph is connected and whose walk
has valid graph steps. The exit-time finiteness is the GMS3 exit lemma; the waypoint construction supplies the same graph fact from the
mated-CRT connectedness anchor. -/
theorem annularEvent_of_polarTemplateItinerary
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (z : ℂ) (r ρ d : ℝ) (X : ℕ → ℤ)
    (hTS : H.TemplateSeparation z r)
    (hdiam : ∀ v, (H.cell v ∩ ball (0 : ℂ) ρ).Nonempty → Metric.diam (H.cell v) ≤ d)
    (hB : ball z (2 * r) ⊆ ball (0 : ℂ) ρ)
    (hsmall : 0 ≤ d ∧ d < r / 12)
    (hstart : X 0 ∈ verticesMeeting H.cell (sphere z r))
    (hstep : ∀ m, G.adj.Adj (X m) (X (m + 1)))
    (hExit : Markov.hitTime (verticesMeeting H.cell (annulus z (r / 2) (3 * r / 2)))ᶜ X ≠ ⊤)
    (hI : PolarTemplateItinerary H z r X) :
    G.AnnularEvent H.cell z r X := by
  classical
  obtain ⟨n, ϑ, α, β, hW, hConf, hstepI⟩ := hI
  let U : Set ℤ := verticesMeeting H.cell (annulus z (r / 2) (3 * r / 2))
  let τ : ℕ∞ := Markov.hitTime Uᶜ X
  have hUfinite : U.Finite := by
    simpa [U] using verticesMeeting_annulus_finite H z r
  have hStartU : X 0 ∈ U := by
    rcases hstart with ⟨w, hwcell, hwsphere⟩
    refine ⟨w, hwcell, ?_⟩
    rw [cellFamily_mem_annulus_iff]
    rw [mem_sphere, dist_eq_norm] at hwsphere
    constructor <;> nlinarith [hwsphere, hsmall.2]
  have hItinU : ∀ j ≤ n, X j ∈ U := by
    intro j hj
    rcases H.interior_cell_nonempty (X j) with ⟨w, hw⟩
    have hwcell : w ∈ H.cell (X j) := interior_subset hw
    have hwconf := hConf j hj hwcell
    refine ⟨w, hwcell, ?_⟩
    have hcoord := cellFamily_mem_annulus_iff.mp hwconf
    apply cellFamily_mem_annulus_iff.mpr
    constructor <;> nlinarith [hcoord.1, hcoord.2, hsmall.1]
  have hnlt : (n : ℕ∞) < τ := by
    rw [Markov.coe_lt_hitTime_iff]
    intro j hj
    exact fun hnot => hnot (hItinU j hj)
  have hτnot0 : τ ≠ 0 := by
    intro hτ0
    have hmem := Markov.hitTime_eq_zero_iff.mp hτ0
    exact hmem hStartU
  have hτpos : 0 < τ := lt_of_le_of_ne bot_le (Ne.symm hτnot0)
  have hdis := hTS ϑ n X α β hW.adj hW.α_zero hW.β_last hW.monotone_α hW.monotone_β
    hW.overlap hW.bounds hW.near
  have htpos : 0 < τ.toNat := by
    have hcoe : (τ.toNat : ℕ∞) = τ := Markov.coe_toNat_hitTime hExit
    have : (0 : ℕ∞) < (τ.toNat : ℕ∞) := by simpa [hcoe] using hτpos
    exact_mod_cast this
  have hnltNat : n < τ.toNat := by
    have hcoe : (τ.toNat : ℕ∞) = τ := Markov.coe_toNat_hitTime hExit
    rw [← hcoe] at hnlt
    exact_mod_cast hnlt
  have hbefore : ∀ m < τ.toNat, X m ∈ U := by
    intro m hm
    have hm' : (m : ℕ∞) < τ := by
      have hcoe : (τ.toNat : ℕ∞) = τ := Markov.coe_toNat_hitTime hExit
      rw [← hcoe]
      exact_mod_cast hm
    have hnot := Markov.notMem_of_lt_hitTime hm'
    simpa [U, τ] using hnot
  have htraceSub : {y | ∃ j ≤ n, X j = y} ⊆ {y | ∃ m < τ.toNat, X m = y} := by
    rintro y ⟨j, hj, rfl⟩
    exact ⟨j, lt_of_le_of_lt hj hnltNat, rfl⟩
  have hdis' := disconnects_mono htraceSub hdis
  have hcells : ∀ m ≤ τ.toNat, H.cell (X m) ⊆ annulus z (r / 3) (5 * r / 3) := by
    intro m hm w hw
    by_cases hmlt : m < τ.toNat
    · rcases hbefore m hmlt with ⟨q, hqcell, hqann⟩
      have hqcoord := cellFamily_mem_annulus_iff.mp hqann
      have hqball0 : q ∈ ball (0 : ℂ) ρ := hB (by
        rw [mem_ball, dist_eq_norm]
        nlinarith [hqcoord.2, hsmall.2])
      have hdm := hdiam (X m) ⟨q, hqcell, hqball0⟩
      have hdist := norm_le_of_diam_le H hdm hw hqcell
      have hqlo : r / 2 ≤ ‖q - z‖ := hqcoord.1
      have hqhi : ‖q - z‖ < 3 * r / 2 := hqcoord.2
      apply cellFamily_mem_annulus_iff.mpr
      constructor
      · have htri := norm_sub_le_norm_sub_add_norm_sub q w z
        have hdist' : ‖q - w‖ ≤ d := by simpa [norm_sub_rev] using hdist
        nlinarith [htri]
      · have htri := norm_sub_le_norm_sub_add_norm_sub w q z
        nlinarith [htri, hsmall.2]
    · have hmeq : m = τ.toNat := Nat.le_antisymm hm (Nat.le_of_not_lt hmlt)
      subst m
      have hprevMem : X (τ.toNat - 1) ∈ U := by
        apply hbefore
        omega
      rcases hprevMem with ⟨q, hqcell, hqann⟩
      have hqcoord := cellFamily_mem_annulus_iff.mp hqann
      have hqball0 : q ∈ ball (0 : ℂ) ρ := hB (by
        rw [mem_ball, dist_eq_norm]
        nlinarith [hqcoord.2, hsmall.2])
      have hprevDiam := hdiam (X (τ.toNat - 1)) ⟨q, hqcell, hqball0⟩
      have hprevBall : H.cell (X (τ.toNat - 1)) ⊆ ball z (2 * r) := by
        intro u hu
        have hdist := norm_le_of_diam_le H hprevDiam hu hqcell
        rw [mem_ball, dist_eq_norm]
        have htri := norm_sub_le_norm_sub_add_norm_sub u q z
        nlinarith [htri, hsmall.2, hqcoord.2]
      have hprevSucc : τ.toNat - 1 + 1 = τ.toNat := Nat.sub_add_cancel (by omega)
      have hAdjExit : G.adj.Adj (X (τ.toNat - 1)) (X (τ.toNat)) := by
        simpa [hprevSucc] using hstep (τ.toNat - 1)
      obtain ⟨q', hq'prev, hq'exit⟩ := H.inter_of_adj _ _ hAdjExit
      have hq'ball0 : q' ∈ ball (0 : ℂ) ρ := hB (hprevBall hq'prev)
      have hExitDiam := hdiam (X (τ.toNat)) ⟨q', hq'exit, hq'ball0⟩
      have hdist1 := norm_le_of_diam_le H hprevDiam hq'prev hqcell
      have hdist2 := norm_le_of_diam_le H hExitDiam hw hq'exit
      have hqlo : r / 2 ≤ ‖q - z‖ := hqcoord.1
      have hqhi : ‖q - z‖ < 3 * r / 2 := hqcoord.2
      apply cellFamily_mem_annulus_iff.mpr
      constructor
      ·
        have htri1 := norm_sub_le_norm_sub_add_norm_sub q q' z
        have htri2 := norm_sub_le_norm_sub_add_norm_sub q' w z
        have hdist1' : ‖q - q'‖ ≤ d := by simpa [norm_sub_rev] using hdist1
        have hdist2' : ‖q' - w‖ ≤ d := by simpa [norm_sub_rev] using hdist2
        nlinarith [htri1, htri2, hsmall.2]
      ·
        have htri1 := norm_sub_le_norm_sub_add_norm_sub w q' z
        have htri2 := norm_sub_le_norm_sub_add_norm_sub q' q z
        have hdist1' : ‖q' - q‖ ≤ d := by simpa [norm_sub_rev] using hdist1
        nlinarith [htri1, htri2, hsmall.2]
  have hτeq : τ = τ.toNat := (Markov.coe_toNat_hitTime hExit).symm
  refine ⟨τ.toNat, hτeq, hdis', hcells⟩

end MatedCRTHarmonic.CellFamily
