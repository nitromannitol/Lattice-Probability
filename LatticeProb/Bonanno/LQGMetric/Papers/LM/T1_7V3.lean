/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V1
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V2
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E4
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E5

/-!
# LM Theorem 1.7, packet P-VAR (c): Efron–Stein over the grid squares with `D^S`, per `g`

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, Steps 1–2 (l. 1011–1036), for one probability
measure `ν` on metrics (later `ν = κ_g`) and one grid `(ε, θ)`:

* `t17v_internal_eq_of_enc`: two length metrics with the same chain encoding `t17eEnc S` (the
  coordinate `D(·,·;S)` of L5.3/L5.4) have the same internal metric on the open set `S`
  (LM Lemma 1.1, continuity of internal metrics, `ContMetric.continuousOn_internal`).
* `T17Compat`: the properties of the resampled metric `D^S` used in Step 2: length, the
  bi-Lipschitz bound (5.11) `C⁻² D ≤ D^S ≤ C² D`, and `D^S(·,·;S') = D(·,·;S')` for `S' ≠ S`.
* `t17v_es_grid` (LM (5.4) + l. 1013–1016 + (5.11)): `Var_ν(F) ≤ ∫ ES dν` for the explicit
  measurable Efron–Stein integrand `ES`, and for `ν`-a.e. `d`, `ES(d) ≤ ∑_S b_S` whenever
  `(F(D^S) − F(d))_+² ≤ b_S` for every `D^S` compatible with `d` at `S`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

/-- equal chain encodings on an open set give equal internal metrics (length metrics) -/
theorem t17v_internal_eq_of_enc {d d'' : ContMetric} (hd : d.IsLength) (hd'' : d''.IsLength)
    {S : Set ℂ} (hS : IsOpen S) (henc : t17eEnc S d'' = t17eEnc S d) :
    ∀ u ∈ S, ∀ v ∈ S, d.internal S u v = d''.internal S u v := by
  set p := TopologicalSpace.denseSeq (ℂ × ℂ)
  have hEq : EqOn (fun q : ℂ × ℂ => d.internal S q.1 q.2) (fun q => d''.internal S q.1 q.2)
      (S ×ˢ S ∩ range p) := by
    rintro _ ⟨-, n, rfl⟩
    have := congrFun henc n
    simp only [t17eEnc] at this
    simp only [d.internal_eq_chainInf hd hS, d''.internal_eq_chainInf hd'' hS]
    exact this.symm
  have h := hEq.of_subset_closure (d.continuousOn_internal hd hS)
    (d''.continuousOn_internal hd'' hS) inter_subset_left
    ((TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)).open_subset_closure_inter (hS.prod hS))
  exact fun u hu v hv => @h (u, v) ⟨hu, hv⟩

/-- the properties of the resampled metric `D^S` (`S = S_k`) relative to `d` -/
def T17Compat (C ε : ℝ) (θ : ℝ × ℝ) (s : Finset (ℤ × ℤ)) (d d'' : ContMetric) (k : ℤ × ℤ) :
    Prop :=
  d''.IsLength ∧ (∀ x y : ℂ, d''.1 (x, y) ≤ C ^ 2 * d.1 (x, y)) ∧
    (∀ x y : ℂ, d.1 (x, y) ≤ C ^ 2 * d''.1 (x, y)) ∧
    ∀ j ∈ s, j ≠ k → ∀ u ∈ t17Square ε θ j, ∀ v ∈ t17Square ε θ j,
      d.internal (t17Square ε θ j) u v = d''.internal (t17Square ε θ j) u v

/-- the square coordinates `Y_θ d = (D(·,·;S))_{S ∈ s}` -/
def t17Y (ε : ℝ) (θ : ℝ × ℝ) (s : Finset (ℤ × ℤ)) (d : ContMetric) : s → ℕ → ℝ≥0∞ :=
  fun k => t17eEnc (t17Square ε θ k) d

lemma measurable_t17Y (ε : ℝ) (θ : ℝ × ℝ) (s : Finset (ℤ × ℤ)) : Measurable (t17Y ε θ s) :=
  measurable_pi_iff.2 fun _ => measurable_t17eEnc _

end LQGMetric.LM
