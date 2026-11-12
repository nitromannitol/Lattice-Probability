/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2Cross at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic

/-!
# A crossing lemma for GM Lemma 5.14

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

GM l. 3455–3457: "Each path from `B_{ζr}(U) ∪ 𝒲` to a point outside of `B_{2ζr}(U ∪ 𝒲)` has a
sub-path which is contained in `𝔸_{r/4,4r}(0) ∖ (B_{ζr}(U) ∪ 𝒲)` and has Euclidean diameter at
least `ζr`." `exists_cross_m2m2`: for a continuous `P : ℝ → ℂ` on `[a, b]` with
`dist(P a, K) ≤ d` and `dist(P b, K) ≥ 2d`, there are `a ≤ α ≤ β ≤ b` with
`d ≤ dist(P γ, K) ≤ 2d` on `[α, β]` and `|P α − P β| ≥ d` (own elementary proof: the last time
before `b` at distance `≤ d`, then the first later time at distance `≥ 2d`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology

namespace LQGMetric.GM

/-- the crossing lemma (GM l. 3455–3457) -/
lemma exists_cross_m2m2 {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    {K : Set ℂ} {d : ℝ} (hd : 0 < d) (ha : infDist (P a) K ≤ d) (hb : 2 * d ≤ infDist (P b) K) :
    ∃ α β : ℝ, a ≤ α ∧ α ≤ β ∧ β ≤ b ∧ d ≤ ‖P α - P β‖ ∧
      ∀ γ ∈ Icc α β, d ≤ infDist (P γ) K ∧ infDist (P γ) K ≤ 2 * d := by
  set F : ℝ → ℝ := fun γ => infDist (P γ) K with hF
  have hFc : ContinuousOn F (Icc a b) := (continuous_infDist_pt K).comp_continuousOn hP
  -- `α`: the last time in `[a, b]` with `F ≤ d`
  set A := Icc a b ∩ {γ | F γ ≤ d}
  have hAc : IsClosed A := hFc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hAne : A.Nonempty := ⟨a, ⟨le_rfl, hab⟩, ha⟩
  have hAb : BddAbove A := ⟨b, fun γ hγ => hγ.1.2⟩
  set α := sSup A
  have hαA : α ∈ A := hAc.csSup_mem hAne hAb
  have hαb : α < b := by
    rcases hαA.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h4 : F α ≤ d := hαA.2
      have h5 : 2 * d ≤ F b := hb
      rw [h] at h4; linarith
  have hafter : ∀ γ ∈ Ioc α b, d < F γ := fun γ hγ => by
    by_contra h; push_neg at h
    exact absurd (le_csSup hAb ⟨⟨hαA.1.1.trans hγ.1.le, hγ.2⟩, h⟩) (not_le.2 hγ.1)
  -- `β`: the first time in `[α, b]` with `F ≥ 2d`
  set B := Icc α b ∩ {γ | 2 * d ≤ F γ}
  have hBc : IsClosed B :=
    (hFc.mono (Icc_subset_Icc hαA.1.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Ici
  have hBne : B.Nonempty := ⟨b, ⟨hαb.le, le_rfl⟩, hb⟩
  have hBb : BddBelow B := ⟨α, fun γ hγ => hγ.1.1⟩
  set β := sInf B
  have hβB : β ∈ B := hBc.csInf_mem hBne hBb
  have hbefore : ∀ γ ∈ Ico α β, F γ < 2 * d := fun γ hγ => by
    by_contra h; push_neg at h
    exact absurd (csInf_le hBb ⟨⟨hγ.1, hγ.2.le.trans hβB.1.2⟩, h⟩) (not_le.2 hγ.2)
  have hαβ : α < β := by
    rcases hβB.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : 2 * d ≤ F β := hβB.2
      have h2 : F α ≤ d := hαA.2
      rw [← h] at h1; linarith
  -- `F α = d`: `F > d` just after `α`
  have hFα : d ≤ F α := by
    have hcont : ContinuousWithinAt F (Ioc α b) α :=
      (hFc.continuousWithinAt ⟨hαA.1.1, hαb.le⟩).mono (Ioc_subset_Icc_self.trans
        (Icc_subset_Icc hαA.1.1 le_rfl))
    have hne : (𝓝[Ioc α b] α).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hαb.ne]; exact ⟨le_rfl, hαb.le⟩
    exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun γ hγ => (hafter γ hγ).le)
  have hFβ : F β ≤ 2 * d := by
    have hcont : ContinuousWithinAt F (Ico α β) β :=
      (hFc.continuousWithinAt ⟨hαA.1.1.trans hβB.1.1, hβB.1.2⟩).mono
        (Ico_subset_Icc_self.trans (Icc_subset_Icc hαA.1.1 hβB.1.2))
    have hne : (𝓝[Ico α β] β).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hαβ.ne]; exact ⟨hαβ.le, le_rfl⟩
    exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun γ hγ => (hbefore γ hγ).le)
  refine ⟨α, β, hαA.1.1, hαβ.le, hβB.1.2, ?_, fun γ hγ => ⟨?_, ?_⟩⟩
  · have h1 : F β ≤ F α + dist (P β) (P α) := infDist_le_infDist_add_dist
    have h2 : 2 * d ≤ F β := hβB.2
    have h3 : F α ≤ d := hαA.2
    rw [dist_eq_norm, norm_sub_rev] at h1
    linarith
  · rcases hγ.1.lt_or_eq with h | h
    · exact (hafter γ ⟨h, hγ.2.trans hβB.1.2⟩).le
    · rw [← h]; exact hFα
  · rcases hγ.2.lt_or_eq with h | h
    · exact (hbefore γ ⟨hγ.1, h⟩).le
    · rw [h]; exact hFβ

end LQGMetric.GM
