/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CoreArc3e at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc3d
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoArcInterior
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.WeldingConsistency

/-!
# CORE_ARC, part 3e: the tip parameter is onto; `LoewnerSubhullsOfArc`

Plan nodes "No jump (left continuity)" (assembly) and the final statement of
`blueprint/CORE_ARC_PLAN.md`.

## Main results

* `Icc_subset_image_arcTime`: under the hypotheses of `LoewnerSubhullsOfArc`,
  `Icc 0 1 ⊆ arcTime A γ '' Icc 0 T`.
  Proof: for `u ∈ (0,1]` let `s` be the swallowing time of `γ u`. Then `arcTime A γ s' < u` for
  `s' < s` and `u ≤ arcTime A γ s =: b`. If `u < b`, the point `p = γ ((u+b)/2)` is the centre
  of a closed disc in `ℍ` missing `γ [0,u] ⊇ K_{s'}` (`s' < s`); `K_s ⊇ γ (u,b]` accumulates at
  `p`, and the disc contains a point off the arc (`CA.Topo.not_ball_subset_arc`), contradicting
  `no_jump`.
* `loewnerSubhullsOfArc : WeldingConsistency.LoewnerSubhullsOfArc`, with `τ = arcTime A γ`.

## Sources

Route of `blueprint/CORE_ARC_PLAN.md`, the project's own: no published proof of this direction
(Loewner hulls of an arc are its initial subarcs, with a continuous parametrisation, proved
without the Jordan curve theorem) was found (see `handoff/CORE-2.md`). Own proof.
-/

noncomputable section

open Set Filter Topology Metric

namespace QuantumZipper

namespace CoreArc

variable {A : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ}

/-- **Surjectivity of the tip parameter.** -/
theorem Icc_subset_image_arcTime (hA : Continuous A) (hA0 : A 0 = 0) (hT : 0 < T)
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) (hK : fwdHull A T = γ '' Ioc 0 1) :
    Icc (0 : ℝ) 1 ⊆ arcTime A γ '' Icc 0 T := by
  intro u hu
  rcases hu.1.eq_or_lt with hu0 | hu0
  · exact ⟨0, ⟨le_rfl, hT.le⟩, by rw [arcTime_zero hA, hu0]⟩
  have hKr : ∀ r ∈ Icc (0 : ℝ) T, fwdHull A r = γ '' Ioc 0 (arcTime A γ r) :=
    fun r hr => fwdHull_eq_image_Ioc_arcTime hA hγc hγi hK hr.1 hr.2
  have hτ1 : ∀ r, arcTime A γ r ∈ Icc (0 : ℝ) 1 := fun r => arcTime_mem_Icc
  -- membership in `K_r` through the parameter
  have hmemK : ∀ r ∈ Icc (0 : ℝ) T, ∀ v ∈ Icc (0 : ℝ) 1,
      γ v ∈ fwdHull A r ↔ v ∈ Ioc 0 (arcTime A γ r) := by
    intro r hr v hv
    rw [hKr r hr]
    constructor
    · rintro ⟨v', hv', hvv⟩
      have := hγi ⟨hv'.1.le, hv'.2.trans (hτ1 r).2⟩ hv hvv
      exact this ▸ hv'
    · exact fun h => ⟨v, h, rfl⟩
  set z := γ u with hz
  have hzT : z ∈ fwdHull A T := by rw [hK]; exact ⟨u, ⟨hu0, hu.2⟩, rfl⟩
  have hzH : 0 < z.im := hγH u ⟨hu0, hu.2⟩
  have hsw : swallowTime A z ≤ ENNReal.ofReal T := hzT.2
  have hne : swallowTime A z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsw
  set s := (swallowTime A z).toReal with hs
  have hs0 : 0 < s := ENNReal.toReal_pos (swallowTime_pos hA hzH).ne' hne
  have hsT : s ≤ T := ENNReal.toReal_le_of_le_ofReal hT.le hsw
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs0.le, hsT⟩
  have hzs : z ∈ fwdHull A s := ⟨hzH, by rw [hs, ENNReal.ofReal_toReal hne]⟩
  have hbefore : ∀ s' ∈ Ico (0 : ℝ) s, z ∉ fwdHull A s' := by
    intro s' hs' hz'
    have := ENNReal.toReal_le_of_le_ofReal hs'.1 hz'.2
    linarith [hs'.2]
  have huI : u ∈ Icc (0 : ℝ) 1 := hu
  have hub : u ≤ arcTime A γ s := ((hmemK s hsI u huI).1 hzs).2
  have hlt : ∀ s' ∈ Ico (0 : ℝ) s, arcTime A γ s' < u := by
    intro s' hs'
    by_contra hle
    exact hbefore s' hs'
      ((hmemK s' ⟨hs'.1, hs'.2.le.trans hsT⟩ u huI).2 ⟨hu0, not_lt.1 hle⟩)
  rcases hub.eq_or_lt with heq | hub'
  · exact ⟨s, hsI, heq.symm⟩
  exfalso
  set b := arcTime A γ s with hb
  have hb1 : b ≤ 1 := (hτ1 s).2
  set c := (u + b) / 2 with hc
  have hcu : u < c := by linarith
  have hcb : c < b := by linarith
  have hcI : c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set p := γ c with hp
  have hpH : p ∈ H := hγH c ⟨hcI.1, hcI.2.le⟩
  set L := γ '' Icc 0 u with hL
  have hLc : IsClosed L :=
    (isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc_right hu.2))).isClosed
  have hpL : p ∉ L := by
    rintro ⟨v, hv, hvp⟩
    have := hγi ⟨hv.1, hv.2.trans hu.2⟩ ⟨hcI.1.le, hcI.2.le⟩ hvp
    linarith [hv.2]
  obtain ⟨R₁, hR₁, hR₁L⟩ := Metric.isOpen_iff.1 hLc.isOpen_compl p hpL
  obtain ⟨R₂, hR₂, hR₂H⟩ := Metric.isOpen_iff.1 isOpen_H_coreArc p hpH
  set R := min R₁ R₂ / 2 with hR
  have hR0 : 0 < R := by positivity
  have hRlt : R < min R₁ R₂ := by linarith [lt_min hR₁ hR₂]
  have hball : closedBall p R ⊆ ball p R₁ ∩ ball p R₂ := fun y hy =>
    ⟨closedBall_subset_ball (hRlt.trans_le (min_le_left _ _)) hy,
      closedBall_subset_ball (hRlt.trans_le (min_le_right _ _)) hy⟩
  have hB : closedBall p R ⊆ H := fun y hy => hR₂H (hball hy).2
  have hdisj : ∀ s' ∈ Ico (0 : ℝ) s, ∀ y ∈ closedBall p R, y ∉ fwdHull A s' := by
    intro s' hs' y hy hyK
    rw [hKr s' ⟨hs'.1, hs'.2.le.trans hsT⟩] at hyK
    obtain ⟨v, hv, rfl⟩ := hyK
    exact hR₁L (hball hy).1 ⟨v, ⟨hv.1.le, hv.2.trans (hlt s' hs').le⟩, rfl⟩
  have hcont : ContinuousAt γ c := hγc.continuousAt (Icc_mem_nhds hcI.1 hcI.2)
  have hne' : ∀ᶠ t in 𝓝[>] c, γ t ∈ ({p}ᶜ : Set ℂ) := by
    filter_upwards [Ioc_mem_nhdsGT hcI.2] with t ht
    intro hpt
    have := hγi ⟨by linarith [ht.1, hcI.1], ht.2⟩ ⟨hcI.1.le, hcI.2.le⟩ hpt
    linarith [ht.1]
  have htend : Tendsto γ (𝓝[>] c) (𝓝[≠] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, hne'⟩
  have hacc : ∃ᶠ y in 𝓝[≠] p, y ∈ fwdHull A s := by
    refine htend.frequently (Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hcb] with t ht
    exact (hmemK s hsI t ⟨by linarith [ht.1, hcI.1], by linarith [ht.2]⟩).2
      ⟨by linarith [ht.1, hcI.1], ht.2.le⟩
  have hnot := CA.Topo.not_ball_subset_arc hγc hγi hcI hR0
  rw [Set.not_subset] at hnot
  obtain ⟨q, hq, hqγ⟩ := hnot
  have hqK : q ∉ fwdHull A s := by
    rw [hKr s hsI]
    rintro ⟨v, hv, rfl⟩
    exact hqγ ⟨v, ⟨hv.1.le, hv.2.trans hb1⟩, rfl⟩
  exact no_jump hA hA0 hs0 hR0 hB hdisj hacc hq hqK

/-- **`LoewnerSubhullsOfArc`** (CORE_ARC): if the forward hull at time `T` of a continuous
driver started at `0` is a simple arc `γ(0,1]`, the hulls at times `r ∈ [0,T]` are the initial
subarcs `γ(0, τ r]` for a continuous, strictly increasing `τ` with `τ 0 = 0`, `τ T = 1`, and the
forward map sends the tip to the driving point. -/
theorem loewnerSubhullsOfArc : WeldingConsistency.LoewnerSubhullsOfArc := by
  intro A hA hA0 T hT γ hγc hγi _hγ0 hγH hK
  have hmono := strictMonoOn_arcTime hA hA0 hγc hγi hK
  have hKr : ∀ r ∈ Icc (0 : ℝ) T, fwdHull A r = γ '' Ioc 0 (arcTime A γ r) :=
    fun r hr => fwdHull_eq_image_Ioc_arcTime hA hγc hγi hK hr.1 hr.2
  refine ⟨arcTime A γ, arcTime_zero hA, arcTime_eq_one_of_fwdHull_eq hK,
    continuousOn_Icc_of_monotoneOn_of_surj hT.le hmono.monotoneOn (arcTime_zero hA)
      (arcTime_eq_one_of_fwdHull_eq hK) (Icc_subset_image_arcTime hA hA0 hT hγc hγi hγH hK),
    hmono, hKr, fun r hr => ?_⟩
  exact tendsto_fwdMap_arc_tip hA hγi hmono (fun r _ => arcTime_mem_Icc) hKr hr

end CoreArc

end QuantumZipper
