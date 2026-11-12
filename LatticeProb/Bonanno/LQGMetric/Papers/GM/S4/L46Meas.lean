/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasDet
import LatticeProb.Bonanno.LQGMetric.Meas.Internal
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# GM Lemma 4.6 (a): `{(z,r) ∈ 𝒵_k}` is a.s. determined by `h|_{ℂ∖B_ρ(z)}` (task P2-E3a)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 4.6 and its proof, l. 1701–1706 ("Since `𝓑^•_{t_k}` is a local set for `h` and since balls
`B_r(z)` for `(z,r) ∈ 𝒵_k` are disjoint from `𝓑^•_{t_k}`, we find that `{(z,r) ∈ 𝒵_k}` is
determined by `h|_{ℂ∖B_r(z)}`"), in the form `gm_L4_7_pair` (`Conditional.lean`) consumes:
`AEEventIn P (fieldSigmaClosed h (ball z ρ)ᶜ) {(z,r) ∈ 𝒵_k}` with `ρ = λ₃ r ≤ λ₄ε𝕣`.

Route (decision DEC-E §3, E3a). For each `n`, `U = B_{1/(n+1)}(ℂ∖B_ρ(z))`:
* Axiom II gives a measurable `Φ` with `D_h(·,·;U) = Φ(h|_U)` a.s.;
* on a Borel set `W` of fields carrying the law of `h` (length metrics, and `Φ` = internal metric
  at the points of a countable dense subset `q` of `U`), two fields with the same values
  `R(g) = (Φ(g|_U)(q_i, q_j))_{i,j}` have the same internal metric on `U` (LM Lemma 1.1,
  continuity), hence the same event (deterministic part `gm_candEvD_of_internal_eq`);
* the images under `R` of the event and of its complement (in `W`) are disjoint analytic sets,
  so a Borel set separates them (Lusin separation, mathlib `AnalyticSet.measurablySeparable`;
  Kechris, *Classical Descriptive Set Theory*, Thm 14.7): the event is a.s. `{R(h) ∈ S}`.
Finally the `σ(h|_{U_n})`-events are combined by a `liminf` into one event of
`fieldSigmaClosed`.

The measurability inputs are explicit hypotheses of `gm_L4_6a`: a Borel set `L` of length metrics
carrying the law of `D_h`, and Borel measurability of the event on `L` (see the handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint TopologicalSpace

namespace LQGMetric.GM

/-- an event a.s. equal, for every `n`, to an event of `σ(h|_{B_{1/(n+1)}(K)})` is a.s. an event
of `σ(h|_K) = ⋂_ε σ(h|_{B_ε(K)})` -/
theorem gm_aeEventIn_fieldSigmaClosed {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h : Ω → DistC) (K : Set ℂ) {E : Set Ω}
    (hE : ∀ n : ℕ, ∃ F, MeasurableSet[fieldSigma h (nbhdO (1 / ((n : ℝ) + 1)) K)] F ∧
      E =ᵐ[P] F) :
    AEEventIn P (fieldSigmaClosed h K) E := by
  choose F hFm hEF using hE
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      fieldSigma h (nbhdO (1 / ((n : ℝ) + 1)) K) ≤ fieldSigma h (nbhdO (1 / ((m : ℝ) + 1)) K) := by
    intro m n hmn
    refine fieldSigma_mono h (fun x hx => thickening_mono ?_ K hx)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  refine ⟨⋃ N, ⋂ n, ⋂ (_ : N ≤ n), F n, ?_, ?_⟩
  · rw [fieldSigmaClosed, MeasurableSpace.measurableSet_iInf]
    intro ε
    rw [MeasurableSpace.measurableSet_iInf]
    intro hε
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    have hle : fieldSigma h (nbhdO (1 / ((M : ℝ) + 1)) K) ≤ fieldSigma h (nbhdO ε K) :=
      fieldSigma_mono h (fun x hx => thickening_mono hM.le K hx)
    have heq : (⋃ N, ⋂ n, ⋂ (_ : N ≤ n), F n) = ⋃ N, ⋂ n, ⋂ (_ : max N M ≤ n), F n := by
      ext ω
      simp only [mem_iUnion, mem_iInter]
      constructor
      · rintro ⟨N, hN⟩
        exact ⟨N, fun n hn => hN n ((le_max_left N M).trans hn)⟩
      · rintro ⟨N, hN⟩
        exact ⟨max N M, hN⟩
    rw [heq]
    refine hle _ (MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun hn => hmono ((le_max_right N M).trans hn) _ (hFm n))
  · have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ E ↔ ω ∈ F n) := by
      rw [ae_all_iff]
      intro n
      filter_upwards [hEF n] with ω hω
      exact Iff.of_eq hω
    filter_upwards [hall] with ω hω
    refine propext ⟨fun hωE => ?_, fun hωF => ?_⟩
    · exact mem_iUnion.2 ⟨0, mem_iInter.2 fun n => mem_iInter.2 fun _ => (hω n).1 hωE⟩
    · obtain ⟨N, hN⟩ := mem_iUnion.1 hωF
      exact (hω N).2 (mem_iInter.1 (mem_iInter.1 hN N) le_rfl)

/-- `ℂ ∖ B_ρ(z)` is nonempty -/
theorem gm_compl_ball_nonempty (z : ℂ) (ρ : ℝ) : (Metric.ball z ρ)ᶜ.Nonempty := by
  by_contra hemp
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
  exact NormedSpace.unbounded_univ ℝ ℂ (hemp ▸ isBounded_ball)

end LQGMetric.GM
