/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgGauss at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Mollified circle averages of a whole-plane GFF: Gaussian structure

`mollAvg g n z r := (1/2π) ∫ g(ψ_{n, z + r e^{iθ}}) dθ` is the `n`-th term of the sequence whose
limit defines `circleAvg g r z`. For a whole-plane GFF `h` (any additive constant), the
differences `mollAvg h n z r − mollAvg h m w s` are pairings of `h` with the mean-zero test
function `circDiff = circBump n z r − circBump m w s` (`CircleAvgPairing`), hence form a
centered Gaussian process with covariance `logCov` (`isGaussianProcess_mollAvg_sub`,
`integral_mollAvg_sub`, `covariance_mollAvg_sub`). This is the finite-`n` part of
Duplantier–Sheffield, arXiv:0808.1560, §3.1 (the circle average process `h_ε(z) = (h, ρ_ε^z)`
is Gaussian with the covariance of the Green function).

Also: `circleAvg_addConst_of_tendsto` — adding a constant `c` shifts `h_r(z)` by `c` wherever the
defining limit exists.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace CircleAvg

/-- the `n`-th mollified circle average `(1/2π) ∫ g(ψ_{n, z + r e^{iθ}}) dθ` -/
def mollAvg (g : DistC) (n : ℕ) (z : ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun x => g (bumpTest n x)) z r

lemma circleAvg_eq_limUnder (g : DistC) (r : ℝ) (z : ℂ) :
    circleAvg g r z = limUnder atTop fun n => mollAvg g n z r := rfl

lemma mollAvg_eq (g : DistC) (n : ℕ) (z : ℂ) (r : ℝ) :
    mollAvg g n z r = g (circBump n z r) :=
  circleAverage_pairing g n z r

lemma integrable_testC (φ : TestC) : Integrable (fun x => φ x) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- `circBump n z r − circBump m w s`, a mean-zero test function -/
def circDiff (n : ℕ) (z : ℂ) (r : ℝ) (m : ℕ) (w : ℂ) (s : ℝ) : TestC0 :=
  ⟨circBump n z r - circBump m w s, by
    show ∫ x, (circBump n z r x - circBump m w s x) = 0
    rw [integral_sub (integrable_testC _) (integrable_testC _), integral_circBump,
      integral_circBump, sub_self]⟩

lemma mollAvg_sub_eq (g : DistC) (n : ℕ) (z : ℂ) (r : ℝ) (m : ℕ) (w : ℂ) (s : ℝ) :
    mollAvg g n z r - mollAvg g m w s = g (circDiff n z r m w s).1 := by
  rw [mollAvg_eq, mollAvg_eq, circDiff, map_sub]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **Gaussianity.** For a whole-plane GFF, the increments of the mollified circle averages
(indexed by `(n, z, r)` and `(m, w, s)`) form a Gaussian process. -/
theorem isGaussianProcess_mollAvg_sub (hh : IsWholePlaneGFF h P) :
    IsGaussianProcess (fun (p : (ℕ × ℂ × ℝ) × (ℕ × ℂ × ℝ)) (ω : Ω) =>
      mollAvg (h ω) p.1.1 p.1.2.1 p.1.2.2 - mollAvg (h ω) p.2.1 p.2.2.1 p.2.2.2) P := by
  have := hh.gaussian.comp_right
    (fun p : (ℕ × ℂ × ℝ) × (ℕ × ℂ × ℝ) =>
      circDiff p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2)
  refine this.congr fun p => Eventually.of_forall fun ω => ?_
  simp only [Function.comp_apply]
  rw [mollAvg_sub_eq]

theorem hasGaussianLaw_mollAvg_sub (hh : IsWholePlaneGFF h P) (n : ℕ) (z : ℂ) (r : ℝ)
    (m : ℕ) (w : ℂ) (s : ℝ) :
    HasGaussianLaw (fun ω => mollAvg (h ω) n z r - mollAvg (h ω) m w s) P :=
  (isGaussianProcess_mollAvg_sub hh).hasGaussianLaw_eval ((n, z, r), (m, w, s))

theorem integral_mollAvg_sub (hh : IsWholePlaneGFF h P) (n : ℕ) (z : ℂ) (r : ℝ)
    (m : ℕ) (w : ℂ) (s : ℝ) :
    ∫ ω, (mollAvg (h ω) n z r - mollAvg (h ω) m w s) ∂P = 0 := by
  simp_rw [mollAvg_sub_eq]
  exact hh.centered _

theorem covariance_mollAvg_sub (hh : IsWholePlaneGFF h P) (n : ℕ) (z : ℂ) (r : ℝ)
    (m : ℕ) (w : ℂ) (s : ℝ) (n' : ℕ) (z' : ℂ) (r' : ℝ) (m' : ℕ) (w' : ℂ) (s' : ℝ) :
    cov[fun ω => mollAvg (h ω) n z r - mollAvg (h ω) m w s,
        fun ω => mollAvg (h ω) n' z' r' - mollAvg (h ω) m' w' s'; P] =
      logCov (circDiff n z r m w s).1 (circDiff n' z' r' m' w' s').1 := by
  simp_rw [mollAvg_sub_eq]
  exact hh.covariance_eq _ _

/-- adding a constant shifts every mollified circle average by that constant -/
lemma mollAvg_addConst (g : DistC) (c : ℝ) (n : ℕ) (z : ℂ) (r : ℝ) :
    mollAvg (addConst g c) n z r = mollAvg g n z r + c :=
  circleAverage_addConst g c n z r

/-- `circleAvg` is the limit wherever the mollified averages converge -/
lemma circleAvg_eq_of_tendsto {g : DistC} {r : ℝ} {z : ℂ} {a : ℝ}
    (ha : Tendsto (fun n => mollAvg g n z r) atTop (𝓝 a)) : circleAvg g r z = a :=
  ha.limUnder_eq

/-- `(g + c)_r(z) = g_r(z) + c` wherever the defining limit for `g` exists -/
lemma circleAvg_addConst_of_tendsto {g : DistC} {r : ℝ} {z : ℂ} {a : ℝ}
    (ha : Tendsto (fun n => mollAvg g n z r) atTop (𝓝 a)) (c : ℝ) :
    circleAvg (addConst g c) r z = circleAvg g r z + c := by
  rw [circleAvg_eq_of_tendsto ha]
  apply circleAvg_eq_of_tendsto
  simp_rw [mollAvg_addConst]
  exact ha.add_const c

end CircleAvg
end LQGMetric
