/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasD2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD1

/-!
# GM Lemma 4.6 (b) from analyticity of the arc and avoiding-geodesic relations (task P2-E3c)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 4.6, first claim, proof l. 1705–1708, and GM.S4.1 (l. 1648–1654).

GM do not discuss measurability. The event `Stab_{k,r}(z)` (`gmStabSet`) has the quantifier shape
`∃ x₀ (analytic) ∀ geodesics (… ⊆ analytic)`, not covered by D30. On the a.s. event of GM.S4.1
(`gm_S4_1`: the arcs partition `∂𝓑^•_{t_k}`) it equals `gmStabSetN = {(z,r) ∈ 𝒵_k} ∖ Split`
(`gm_stabCond_iff_not_split`), and `Split` is an existential statement over the two relations
* `GMArcRelAn`: `{(d, s, t, x, y) : x ∈ Conf(s,t), y ∈ arcOf x}` and
* `GMAvoidRelAn`: `{(d, y) : y lies on a D(·,·;ℂ∖cl B_r(z))-geodesic from 𝕫}`,
so it is universally measurable on `lenSet` as soon as these are analytic there
(`gm_uMeasurableSet_split`, Lusin, D30). The locality of `gmStabSetN` is
`gm_stabSetN_of_internal_eq`; the glue is `gm_aeEventIn_of_local` (B2), applied to `gmStabSetN`
and transported to `Stab` by the a.s. equality (so no null-measurable variant of the glue is
needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- `A` agrees on `L` with the projection of a Borel subset of `α × β`, `β` standard Borel
(an analytic set, relative to `L`) -/
def GMAnalyticOn {α : Type} [MeasurableSpace α] (L A : Set α) : Prop :=
  ∃ (β : Type) (_ : MeasurableSpace β) (_ : StandardBorelSpace β) (S : Set (α × β)),
    MeasurableSet S ∧ ∀ a ∈ L, (a ∈ A ↔ ∃ b, (a, b) ∈ S)

/-- the relation `x ∈ Conf(s,t)`, `y ∈ arcOf x` (GM (4.7)) is analytic on `lenSet` -/
def GMArcRelAn (𝕫 : ℂ) : Prop :=
  GMAnalyticOn {p : (ContMetric × ℝ × ℝ) × ℂ × ℂ | p.1.1 ∈ lenSet}
    {p | p.2.1 ∈ confPts p.1.1 𝕫 p.1.2.1 p.1.2.2 ∧ p.2.2 ∈ arcOf p.1.1 𝕫 p.1.2.2 p.2.1}

/-- the relation "`y` lies on a `D(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫`" is analytic on `lenSet` -/
def GMAvoidRelAn (𝕫 z : ℂ) (r : ℝ) : Prop :=
  GMAnalyticOn {p : ContMetric × ℂ | p.1 ∈ lenSet} {p | gmOnAvoid p.1 𝕫 z r p.2}

/-- **`Split` is universally measurable on `lenSet`** -/
theorem gm_uMeasurableSet_split {𝕫 z : ℂ} {r : ℝ} (hA : GMArcRelAn 𝕫) (hV : GMAvoidRelAn 𝕫 z r)
    (R c₁ c : ℝ) :
    UMeasurableSet (lenSet ∩ {d | gmSplit d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c) z r}) := by
  obtain ⟨β₁, m₁, sb₁, SA, hSA, hA⟩ := hA
  obtain ⟨β₂, m₂, sb₂, SV, hSV, hV⟩ := hV
  let g : ContMetric → ContMetric × ℝ × ℝ := fun d => (d, gmTauB 𝕫 R d * c₁, gmTauB 𝕫 R d * c)
  have hg : Measurable g := measurable_id.prodMk
    (((gm_measurable_tauB 𝕫 R).mul_const c₁).prodMk ((gm_measurable_tauB 𝕫 R).mul_const c))
  let W := (ℂ × ℂ) × (ℂ × ℂ) × (β₁ × β₁) × (β₂ × β₂)
  let S : Set (ContMetric × W) := {q | q.1 ∈ lenSet ∧ q.2.1.1 ≠ q.2.1.2 ∧
    ((g q.1, (q.2.1.1, q.2.2.1.1)), q.2.2.2.1.1) ∈ SA ∧
    ((g q.1, (q.2.1.2, q.2.2.1.2)), q.2.2.2.1.2) ∈ SA ∧
    ((q.1, q.2.2.1.1), q.2.2.2.2.1) ∈ SV ∧ ((q.1, q.2.2.1.2), q.2.2.2.2.2) ∈ SV}
  have hS : MeasurableSet S := by
    have m1 : Measurable fun q : ContMetric × W => q.1 := measurable_fst
    have mw : Measurable fun q : ContMetric × W => q.2 := measurable_snd
    have mx₁ : Measurable fun q : ContMetric × W => q.2.1.1 := measurable_fst.comp (measurable_fst.comp mw)
    have mx₂ : Measurable fun q : ContMetric × W => q.2.1.2 := measurable_snd.comp (measurable_fst.comp mw)
    have my : Measurable fun q : ContMetric × W => q.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp mw)
    have ma : Measurable fun q : ContMetric × W => q.2.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp mw))
    have mb : Measurable fun q : ContMetric × W => q.2.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp mw))
    refine (measurableSet_lenSet.preimage m1).inter ((measurableSet_eq_fun mx₁ mx₂).compl.inter
      ((hSA.preimage ?_).inter ((hSA.preimage ?_).inter ((hSV.preimage ?_).inter
        (hSV.preimage ?_)))))
    · exact ((hg.comp m1).prodMk (mx₁.prodMk (measurable_fst.comp my))).prodMk
        (measurable_fst.comp ma)
    · exact ((hg.comp m1).prodMk (mx₂.prodMk (measurable_snd.comp my))).prodMk
        (measurable_snd.comp ma)
    · exact (m1.prodMk (measurable_fst.comp my)).prodMk (measurable_fst.comp mb)
    · exact (m1.prodMk (measurable_snd.comp my)).prodMk (measurable_snd.comp mb)
  have e : lenSet ∩ {d | gmSplit d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c) z r} =
      {d | ∃ w, (d, w) ∈ S} := by
    ext d
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hd, x₁, hx₁, x₂, hx₂, hne, ⟨y₁, hy₁, hv₁⟩, ⟨y₂, hy₂, hv₂⟩⟩
      rw [gm_tauD_eq_tauB hd] at hx₁ hx₂ hy₁ hy₂
      obtain ⟨a₁, ha₁⟩ := (hA ((g d), (x₁, y₁)) hd).1 ⟨hx₁, hy₁⟩
      obtain ⟨a₂, ha₂⟩ := (hA ((g d), (x₂, y₂)) hd).1 ⟨hx₂, hy₂⟩
      obtain ⟨b₁, hb₁⟩ := (hV (d, y₁) hd).1 hv₁
      obtain ⟨b₂, hb₂⟩ := (hV (d, y₂) hd).1 hv₂
      exact ⟨((x₁, x₂), (y₁, y₂), (a₁, a₂), (b₁, b₂)), hd, hne, ha₁, ha₂, hb₁, hb₂⟩
    · rintro ⟨⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩, ⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩, hd, hne, ha₁, ha₂, hb₁, hb₂⟩
      obtain ⟨hx₁, hy₁⟩ := (hA ((g d), (x₁, y₁)) hd).2 ⟨a₁, ha₁⟩
      obtain ⟨hx₂, hy₂⟩ := (hA ((g d), (x₂, y₂)) hd).2 ⟨a₂, ha₂⟩
      have hv₁ := (hV (d, y₁) hd).2 ⟨b₁, hb₁⟩
      have hv₂ := (hV (d, y₂) hd).2 ⟨b₂, hb₂⟩
      refine ⟨hd, ?_⟩
      rw [gm_tauD_eq_tauB hd]
      exact ⟨x₁, hx₁, x₂, hx₂, hne, ⟨y₁, hy₁, hv₁⟩, ⟨y₂, hy₂, hv₂⟩⟩
  rw [e]
  exact UMeasurableSet.setOf_exists hS

/-- `gmStabSetN` is universally measurable on `lenSet` -/
theorem gm_uMeasurableSet_stabSetN {𝕫 z : ℂ} {r : ℝ} (hA : GMArcRelAn 𝕫)
    (hV : GMAvoidRelAn 𝕫 z r) (R c₁ c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) :
    UMeasurableSet (lenSet ∩ gmStabSetN 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r) := by
  have e : lenSet ∩ gmStabSetN 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r =
      (lenSet ∩ {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r}) ∩
        (lenSet ∩ {d | gmSplit d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c) z r})ᶜ := by
    ext d
    simp only [gmStabSetN, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
    tauto
  rw [e]
  exact (gm_uMeasurableSet_candEvD 𝕫 _ _ _ _ _ _ _ _ z r).inter
    (gm_uMeasurableSet_split hA hV R c₁ c).compl

end LQGMetric.GM
