/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.RightContinuityAtInfty at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.PathProperties

/-!
# Right continuity at `∞` of the constructed process, and Lemma 3.10 for it
(Gwynne–Sung, arXiv:2506.18827; Lemma 3.11.1, p. 26–27, deterministic core)

`Theorem16.RightContinuousAtInfty` (`Theorem16Statement.lean`) is the half of right continuity
that the printed property (ii) does not state — a.s., at every time `t` with `X_t = ∞` and
for every vertex `y`, `X ≠ y` on some `(t, t + ε)` — and which `IsReflectedWalk` therefore
carries as a conjunct of its own (the `∞`-side of (ii), an approved modification of the
printed statement); it is also the hypothesis under which `StrongMarkov.lean` proves
Lemma 3.10.  This file proves that clause for the process `X` of (3.26).

## The argument

The paper proves the corresponding statement (its Lemma 3.11.1, "`X⁻¹(A) ∩ [0,t)` is a finite
union of intervals") from the strong Markov property.  For the *constructed* process this is
unnecessary: the visits to a vertex `y ∈ VG_m` are the holding intervals `[τ_ξ, τ_ξ̂)` with
`Y_ξ = y`, and by (3.14) every such `ξ` has a representative `(m, j)` at level `m`.  Those
with `ξ < [(0,K)] = [(m, J^{0,m}_K)]` have `j < J^{0,m}_K`, so there are **finitely many**
of them (`finite_visits`).  Since `τ_{[(0,K)]} → ∞` (the first clause (3.16) of Lemma 3.5),
every bounded time interval sees only finitely many visits to `y`; hence if `X_t = ∞` the
visits to `y` cannot accumulate at `t` from the right (`X_rightContinuousAtInfty`).  The only
probabilistic inputs are the a.s. coupling identity (3.12) and (3.16).

## Consequences

`PathProperties.rightContinuousAtInfty`: the hypothesis of Lemma 3.10 holds for
`PathProperties.process` under any law for which (3.12) and the first clause of (3.16) hold
a.s.  The specialisation to the process family of `Existence.lean` is
`Existence.rightContinuousAtInfty` in that file, where it supplies the corresponding conjunct
of `Existence.isReflectedWalk` (with (3.16) discharged by Lemma 3.5:
`Existence.rightContinuousAtInfty_of_rateFunction`); Lemma 3.10 for that family is in
`ExistenceStrongMarkov.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

universe u

namespace ReflectedWalk

open IndexSet

variable {V : Type u}

/-! ### The deterministic core -/

section deterministic

variable (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (E : (ℕ →₀ ℕ) → ℝ)

/-- `X_t = x ∈ VG` forces `t ∈ [τ_η, τ_η̂)` with `Y_η = x` for some `η ∈ Ξ` (from (3.26)). -/
lemma exists_inInterval_of_X_eq_some {t : ℝ≥0} {x : V} (h : X Gs Y w E t = some x) :
    ∃ η, InInterval Gs Y w E η t ∧ Yxi Gs Y η = x := by
  by_cases hx : ∃ η, InInterval Gs Y w E η t
  · rw [X, dite_eq_left hx] at h
    exact ⟨Classical.choose hx, Classical.choose_spec hx, Option.some_injective V h⟩
  · rw [X, dite_eq_right hx] at h
    exact absurd h (by simp)

/-- **Finitely many visits to a vertex before a level-`0` time.**  Every `ξ ∈ Ξ` with `Y_ξ = y`
and `ξ < [(0,K)]` is `[(m, j)]` with `y ∈ VG_m` and `j < J^{0,m}_K` ((3.14) and the order
comparison at level `m`). -/
lemma finite_visits (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (K : ℕ) (y : V) :
    {a | a ∈ below Gs Y (addr Gs Y 0 K) ∧ Yxi Gs Y a = y}.Finite := by
  obtain ⟨m, hm⟩ := hcov y
  have hK : addr Gs Y 0 K = addr Gs Y m (J Gs Y 0 m K) := by
    have := addr_J Gs Y 0 m K
    rw [Nat.zero_add] at this
    exact this.symm
  refine ((Set.finite_Iio (J Gs Y 0 m K)).image (addr Gs Y m)).subset ?_
  rintro a ⟨⟨ha, hlt⟩, hay⟩
  obtain ⟨j, hj⟩ := h.exists_addr_eq_of_mem Gs Y hG ha (by rw [hay]; exact hm)
  refine ⟨j, ?_, hj⟩
  rw [Set.mem_Iio, ← addr_lt_addr_iff Gs Y, hj, ← hK]
  exact hlt

/-- **Right continuity at `∞`, deterministic core** (the content of Lemma 3.11.1 for the
process (3.26)).  If `X_t = ∞` then, for every vertex `y`, `X ≠ y` on a right neighbourhood of
`t`: a visit to `y` at `s ∈ (t, t + 1)` is a holding interval `[τ_η, τ_η̂)` with `Y_η = y` that
starts after `t` (it cannot contain `t`) and before `τ_{[(0,K)]}` for a level-`0` time `K` with
`τ_{[(0,K)]} > t + 1`; there are finitely many such `η`, so their starting times stay away from
`t`. -/
theorem X_rightContinuousAtInfty (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (htot : totalTime Gs Y w E = ⊤)
    (t : ℝ≥0) (ht : X Gs Y w E t = none) (y : V) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X Gs Y w E s ≠ some y := by
  classical
  obtain ⟨K, hK⟩ := PathProperties.exists_lt_tau_addr_zero Gs Y w E htot
    (s := ((t + 1 : ℝ≥0) : ℝ≥0∞)) ENNReal.coe_ne_top
  -- the visits to `y` before `[(0,K)]` that start after `t`
  set S : Set (ℕ →₀ ℕ) := {a | (a ∈ below Gs Y (addr Gs Y 0 K) ∧ Yxi Gs Y a = y) ∧
    (t : ℝ≥0∞) < tau Gs Y w E a} with hS
  have hSfin : S.Finite := (finite_visits Gs Y h hG hcov K y).subset fun a ha => ha.1
  -- every visit to `y` in `(t, t + 1)` is one of them
  have hmem : ∀ s : ℝ≥0, t < s → s < t + 1 → X Gs Y w E s = some y →
      ∃ η ∈ S, tau Gs Y w E η ≤ (s : ℝ≥0∞) := by
    intro s hts hs1 hXs
    obtain ⟨η, hη, hηy⟩ := exists_inInterval_of_X_eq_some Gs Y w E hXs
    have hτs : tau Gs Y w E η ≤ (s : ℝ≥0∞) := hη.2.1
    have htτ : (t : ℝ≥0∞) < tau Gs Y w E η := by
      by_contra hle'
      have hle : tau Gs Y w E η ≤ (t : ℝ≥0∞) := not_lt.1 hle'
      rw [X_eq_none_iff] at ht
      exact ht ⟨η, hη.1, hle, lt_trans (ENNReal.coe_lt_coe.2 hts) hη.2.2⟩
    have hlt : toLex η < toLex (addr Gs Y 0 K) := by
      by_contra hge'
      have hge : toLex (addr Gs Y 0 K) ≤ toLex η := not_lt.1 hge'
      have h1 := tau_mono Gs Y w E hge
      have h2 : tau Gs Y w E η < ((t + 1 : ℝ≥0) : ℝ≥0∞) :=
        lt_of_le_of_lt hτs (ENNReal.coe_lt_coe.2 hs1)
      exact absurd (lt_of_le_of_lt h1 h2) (not_lt.2 hK.le)
    exact ⟨η, ⟨⟨⟨hη.1, hlt⟩, hηy⟩, htτ⟩, hτs⟩
  by_cases hne : S.Nonempty
  · obtain ⟨a₀, ha₀, hmin⟩ := Set.exists_min_image S (tau Gs Y w E) hSfin hne
    have hta₀ : (t : ℝ≥0∞) < tau Gs Y w E a₀ := ha₀.2
    obtain ⟨ε, hε, hε1, hεle⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ ε ≤ 1 ∧
        ((t + ε : ℝ≥0) : ℝ≥0∞) ≤ tau Gs Y w E a₀ := by
      cases hτ : tau Gs Y w E a₀ with
      | top => exact ⟨1, one_pos, le_rfl, le_top⟩
      | coe c =>
        rw [hτ] at hta₀
        have htc : t < c := ENNReal.coe_lt_coe.1 hta₀
        refine ⟨min (c - t) 1, lt_min (tsub_pos_of_lt htc) one_pos, min_le_right _ _, ?_⟩
        rw [ENNReal.coe_le_coe]
        calc t + min (c - t) 1 ≤ t + (c - t) := by gcongr; exact min_le_left _ _
          _ = c := add_tsub_cancel_of_le htc.le
    refine ⟨ε, hε, fun s hs hXs => ?_⟩
    obtain ⟨η, hηS, hτη⟩ := hmem s hs.1 (lt_of_lt_of_le hs.2 (by gcongr)) hXs
    have h1 : tau Gs Y w E a₀ ≤ tau Gs Y w E η := hmin η hηS
    have h2 : tau Gs Y w E η < ((t + ε : ℝ≥0) : ℝ≥0∞) :=
      lt_of_le_of_lt hτη (ENNReal.coe_lt_coe.2 hs.2)
    exact absurd (lt_of_le_of_lt (hεle.trans h1) h2) (lt_irrefl _)
  · refine ⟨1, one_pos, fun s hs hXs => ?_⟩
    obtain ⟨η, hηS, -⟩ := hmem s hs.1 hs.2 hXs
    exact hne ⟨η, hηS⟩

end deterministic

/-! ### The process of `PathProperties.lean` -/

section probabilistic

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
  (Gs : ℕ → Set V) (w : V → ℝ) (Y : Ω → ℕ → ℕ → V) (E : Ω → (ℕ →₀ ℕ) → ℝ)

/-- **Right continuity at `∞`** for `PathProperties.process`: the probabilistic inputs are the
a.s. coupling identity (3.12) and the a.s. divergence `∑_{ξ ∈ Ξ} T_ξ = ∞` of (3.16). -/
theorem PathProperties.rightContinuousAtInfty (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω))
    (htot : ∀ᵐ ω ∂P, totalTime Gs (Y ω) w (E ω) = ⊤) :
    Theorem16.RightContinuousAtInfty P (PathProperties.process Gs w Y E) := by
  filter_upwards [hcons, htot] with ω hω hωt
  intro t ht y
  simp only [PathProperties.process_of_consistent Gs w Y E hω] at ht ⊢
  exact X_rightContinuousAtInfty Gs (Y ω) w (E ω) hω hG hcov hωt t ht y

end probabilistic

end ReflectedWalk
