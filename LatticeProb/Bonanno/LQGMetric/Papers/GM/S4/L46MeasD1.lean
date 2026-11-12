/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasD1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB4

/-!
# GM Lemma 4.6 (b): `Stab_{k,r}(z)` without the nested quantifier (task P2-E3c)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
(4.11) (l. 1692) and GM.S4.1 (l. 1648–1654: `Conf_k` finite, the arcs `arcOf x`, `x ∈ Conf_k`,
disjoint and covering `∂𝓑^•_{t_k}`).

GM's event (4.11), "each `D_h(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to `∂B_r(z)` hits `∂𝓑^•_{t_k}`
in the same arc of `𝓘_k`", is formalized (`stabCond`) as `∃ x₀ ∈ Conf, ∀ avoiding geodesics …
⊆ arcOf x₀`. When the arcs partition `∂𝓑^•_t` (GM.S4.1, a.s.) this is the negation of
`gmSplit`: "two different arcs of `𝓘_k` are hit by avoiding geodesics" (`gm_stabCond_iff_not_split`,
own elementary argument; it is the literal meaning of "the same arc"). `gmSplit` is an existential
statement, hence analytic once its building blocks are (see `L46MeasD2.lean`).

* `gmHitArc`: the arc `arcOf x` contains a point of an avoiding geodesic;
* `gm_split_transfer`, `gm_stabSetN_of_internal_eq`: locality, as `gm_stab_of_internal_eq` (B3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `y` lies on a `D(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to `∂B_r(z)` (GM l. 1695–1696) -/
def gmOnAvoid (d : ContMetric) (𝕫 z : ℂ) (r : ℝ) (y : ℂ) : Prop :=
  ∃ (x : ℂ) (Q : ℝ → ℂ) (T : ℝ), IsAvoidGeod d 𝕫 z r x Q T ∧ y ∈ Q '' Icc 0 T

/-- the arc `arcOf x` of `𝓘` is hit by an avoiding geodesic -/
def gmHitArc (d : ContMetric) (𝕫 : ℂ) (t : ℝ) (z : ℂ) (r : ℝ) (x : ℂ) : Prop :=
  ∃ y ∈ arcOf d 𝕫 t x, gmOnAvoid d 𝕫 z r y

/-- two different arcs of `𝓘 = {arcOf x : x ∈ Conf(s,t)}` are hit by avoiding geodesics -/
def gmSplit (d : ContMetric) (𝕫 : ℂ) (s t : ℝ) (z : ℂ) (r : ℝ) : Prop :=
  ∃ x₁ ∈ confPts d 𝕫 s t, ∃ x₂ ∈ confPts d 𝕫 s t, x₁ ≠ x₂ ∧
    gmHitArc d 𝕫 t z r x₁ ∧ gmHitArc d 𝕫 t z r x₂

/-- **GM (4.11) as "no two arcs are hit"**, when the arcs partition `∂𝓑^•_t` (GM.S4.1) -/
theorem gm_stabCond_iff_not_split {d : ContMetric} {𝕫 : ℂ} {s t : ℝ} {z : ℂ} {r : ℝ}
    (hdisj : (confPts d 𝕫 s t).PairwiseDisjoint (arcOf d 𝕫 t))
    (hcov : ⋃ x ∈ confPts d 𝕫 s t, arcOf d 𝕫 t x = frontier (filledBall d 𝕫 t))
    (hne : (frontier (filledBall d 𝕫 t)).Nonempty) :
    stabCond d 𝕫 s t z r ↔ ¬ gmSplit d 𝕫 s t z r := by
  have hmem : ∀ y ∈ frontier (filledBall d 𝕫 t), ∃ x ∈ confPts d 𝕫 s t, y ∈ arcOf d 𝕫 t x := by
    intro y hy
    rw [← hcov] at hy
    simpa only [mem_iUnion, exists_prop] using hy
  constructor
  · rintro ⟨x₀, hx₀, hall⟩ ⟨x₁, hx₁, x₂, hx₂, hne12, ⟨y₁, hy₁, x', Q, T, hQ, hyQ⟩,
      ⟨y₂, hy₂, x'', Q', T', hQ', hyQ'⟩⟩
    have e1 : x₁ = x₀ := by
      by_contra hne'
      have h0 := hall x' Q T hQ ⟨hyQ, hy₁.1⟩
      exact (hdisj hx₁ hx₀ hne').ne_of_mem hy₁ h0 rfl
    have e2 : x₂ = x₀ := by
      by_contra hne'
      have h0 := hall x'' Q' T' hQ' ⟨hyQ', hy₂.1⟩
      exact (hdisj hx₂ hx₀ hne').ne_of_mem hy₂ h0 rfl
    exact hne12 (e1.trans e2.symm)
  · intro hns
    by_cases hex : ∃ x₁ ∈ confPts d 𝕫 s t, gmHitArc d 𝕫 t z r x₁
    · obtain ⟨x₁, hx₁, hh₁⟩ := hex
      refine ⟨x₁, hx₁, fun x Q T hQ y hy => ?_⟩
      obtain ⟨x₂, hx₂, hy₂⟩ := hmem y hy.2
      by_cases e : x₂ = x₁
      · rw [← e]; exact hy₂
      · exact absurd ⟨x₂, hx₂, x₁, hx₁, e, ⟨y, hy₂, x, Q, T, hQ, hy.1⟩, hh₁⟩ hns
    · push Not at hex
      obtain ⟨y₀, hy₀⟩ := hne
      obtain ⟨x₀, hx₀, -⟩ := hmem y₀ hy₀
      refine ⟨x₀, hx₀, fun x Q T hQ y hy => ?_⟩
      obtain ⟨x₂, hx₂, hy₂⟩ := hmem y hy.2
      exact absurd ⟨y, hy₂, x, Q, T, hQ, hy.1⟩ (hex x₂ hx₂)

theorem gm_onAvoid_transfer {d₁ d₂ : ContMetric} {U : Set ℂ}
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y) {𝕫 z : ℂ} {r : ℝ}
    (hUr : (ball z r)ᶜ ⊆ U) {y : ℂ} (h : gmOnAvoid d₁ 𝕫 z r y) : gmOnAvoid d₂ 𝕫 z r y := by
  obtain ⟨x, Q, T, hQ, hy⟩ := h
  exact ⟨x, Q, T, gm_avoidGeod_transfer heq hUr hQ, hy⟩

theorem gm_hitArc_transfer {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ}
    (H : GMAgree d₁ d₂ U 𝕫 T) {z : ℂ} {r : ℝ} (hUr : (ball z r)ᶜ ⊆ U) {t : ℝ} (ht : t ≤ T)
    {x : ℂ} (h : gmHitArc d₁ 𝕫 t z r x) : gmHitArc d₂ 𝕫 t z r x := by
  obtain ⟨y, hy, hav⟩ := h
  exact ⟨y, gm_arcOf_transfer H ht hy, gm_onAvoid_transfer H.int hUr hav⟩

theorem gm_split_transfer {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ}
    (H : GMAgree d₁ d₂ U 𝕫 T) {z : ℂ} {r : ℝ} (hUr : (ball z r)ᶜ ⊆ U) {s t : ℝ} (hs : s ≤ T)
    (ht : t ≤ T) (h : gmSplit d₁ 𝕫 s t z r) : gmSplit d₂ 𝕫 s t z r := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hne, h₁, h₂⟩ := h
  exact ⟨x₁, gm_hitSet_transfer H hs ht hx₁, x₂, gm_hitSet_transfer H hs ht hx₂, hne,
    gm_hitArc_transfer H hUr ht h₁, gm_hitArc_transfer H hUr ht h₂⟩

/-- the metric event `{(z,r) ∈ 𝒵_k} ∖ Split`, a.s. equal to `Stab_{k,r}(z)` -/
def gmStabSetN (𝕫 : ℂ) (R c₁ c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) (z : ℂ) (r : ℝ) :
    Set ContMetric :=
  {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r ∧
    ¬ gmSplit d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c) z r}

/-- locality of `gmStabSetN` (as `gm_stab_of_internal_eq`) -/
theorem gm_stabSetN_of_internal_eq {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {𝕫 : ℂ} {R c₁ c lam1 lam4 ε ν 𝕣 : ℝ} {Rads : Set ℝ} {z : ℂ} {r ρ : ℝ} (hc : 1 < c)
    (hc₁ : c₁ ≤ c) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) (hρr : ρ ≤ r) {U : Set ℂ}
    (hU : IsOpen U) (hUρ : (Metric.ball z ρ)ᶜ ⊆ U)
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y)
    (H : d₁ ∈ gmStabSetN 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r) :
    d₂ ∈ gmStabSetN 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r := by
  obtain ⟨hA, hτ⟩ := gm_agree_of_candEvD h₁ h₂ hc ha hρ hU hUρ heq H.1
  refine ⟨gm_candEvD_of_internal_eq h₁ h₂ hc ha hρ hU hUρ heq H.1, ?_⟩
  rw [hτ]
  have hτ0 : 0 ≤ tauD d₁ 𝕫 R := by
    by_contra hneg
    have := hA.pos
    nlinarith [not_le.1 hneg]
  have hUr : (ball z r)ᶜ ⊆ U :=
    (compl_subset_compl.2 (ball_subset_ball hρr)).trans hUρ
  have hA' : GMAgree d₂ d₁ U 𝕫 (tauD d₁ 𝕫 R * c) := hA.symm
  exact fun hs => H.2 (gm_split_transfer hA' hUr (mul_le_mul_of_nonneg_left hc₁ hτ0) le_rfl hs)

end LQGMetric.GM
