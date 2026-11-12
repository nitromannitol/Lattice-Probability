/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P2G at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P2F
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P1B

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2: the glued metric from the truncated local limits (P-1a/P-2, amended)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2:
Step 1 (T:1349, "a measurable function `h ↦ D_h` from distributions to continuous metrics"),
Step 2 (T:1358–1374, the internal metrics `D(·,·;O)` are determined by the truncated values
`D(u,v) 1{D(u,v) < D(u,∂O')}`, which are limits of the localized LFPP), Step 3 (T:1376–1385,
patching over bounded open sets; "Euclidean otherwise"). Amendment of D90 Q2.2 (see the handoff
of P2-DFT12b): the local limits `locLim` of the untruncated localized LFPP on `W̄` need not
converge (their limits `d_W` are not determined by `D_h` on `∂W`), so the glued metric is built
from the truncated limits.

* `truncLim` — `lim_k truncW(𝔞⁻¹D̂^{ε_k}_g(·,·;W̄))` (junk if no limit); `measurable_truncLim`.
* `patchT` — `D_g(z,w) := lim_n D(z,w; sqW n)` with `D(·,·;sqW n)` the chain formula of
  `truncLim (sqW n) g`, made continuous by `contQ`, then a continuous metric by `toContMetric`;
  `measurable_patchT`.
* `patchT_eq` — if `truncLim (sqW n) g = truncD (sqW n) D` for all `n`, `D` a length metric,
  then `patchT g = D`.
* `exists_subseq_patchT_ae` — **P-2**: along a deterministic subsequence, `patchT ∘ h = D_h`
  a.s.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- `lim_k truncW(𝔞_{ε_k}⁻¹ D̂^{ε_k}_g(·,·;W̄))` (junk if the limit does not exist) -/
def truncLim (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k) (W : dyadicDomainsC) (g : DistC) :
    C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) :=
  limUnder atTop fun k => truncW W (L217.locSqC ξ (εs k) (hεs k) g (closure W))

theorem measurable_truncLim {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k} (W : dyadicDomainsC) :
    Measurable (truncLim ξ εs hεs W) := by
  have := compactSpace_closure_dy W
  have : PolishSpace C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) :=
    polishSpace_continuousMap _ _
  exact (StronglyMeasurable.limUnder fun k => ((continuous_truncW W).measurable.comp
    (L217.measurable_locSqC ξ (εs k) (hεs k) W.2.1 W.2.2)).stronglyMeasurable).measurable

theorem continuous_infFr_left (W : dyadicDomainsC) (a : closure (W : Set ℂ)) :
    Continuous fun T : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) => infFr W T a := by
  refine (LipschitzWith.of_dist_le_mul fun T T' => ?_).continuous (K := 1)
  rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_le]
  have h1 := infFr_le_add W T T' a
  have h2 := infFr_le_add W T' T a
  rw [dist_comm] at h2
  constructor <;> linarith

theorem measurable_tStep (W : dyadicDomainsC) (x y : ℂ) :
    Measurable fun T : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) => tStep W T x y := by
  classical
  by_cases h : x ∈ (W : Set ℂ) ∧ y ∈ closure (W : Set ℂ)
  · simp only [tStep, h, and_self, ↓reduceDIte]
    refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp
      (continuous_eval_const _).measurable) measurable_const
    exact measurableSet_lt (continuous_eval_const _).measurable
      (continuous_infFr_left W _).measurable
  · simp only [tStep, h, ↓reduceDIte]
    exact measurable_const

theorem measurable_tChainVal (W : dyadicDomainsC) :
    ∀ (l : List ℂ) (x y : ℂ), Measurable fun T : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) =>
      tChainVal W T x l y
  | [], x, y => by simpa only [tChainVal] using measurable_tStep W x y
  | q :: l, x, y => by
    simp only [tChainVal]
    exact (measurable_tStep W x q).add (measurable_tChainVal W l q y)

theorem measurable_tChainInf (W : dyadicDomainsC) (z w : ℂ) :
    Measurable fun T : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) => tChainInf W T z w :=
  Measurable.iInf fun _ => measurable_tChainVal W _ z w

/-- the squares as dyadic domains -/
def sqWd (n : ℕ) : dyadicDomainsC := ⟨sqW n, sqW_mem n⟩

/-- the pointwise glued function `lim_n D(z,w; sqW n)` -/
def patchF (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k) (g : DistC) (p : ℂ × ℂ) : ℝ :=
  limUnder atTop fun n => (tChainInf (sqWd n) (truncLim ξ εs hεs (sqWd n) g) p.1 p.2).toReal

/-- **the glued metric** (T:1349, T:1376–1385): `patchF` made continuous on the dense
sequence, then a continuous metric (Euclidean otherwise) -/
def patchT (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k) (g : DistC) : ContMetric :=
  toContMetric (contQ fun a => patchF ξ εs hεs g (Qd a))

theorem measurable_patchT {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k} :
    Measurable (patchT ξ εs hεs) := by
  refine measurable_toContMetric.comp (measurable_contQ fun a => ?_)
  exact (StronglyMeasurable.limUnder (l := atTop) fun n =>
    (ENNReal.measurable_toReal.comp ((measurable_tChainInf (sqWd n) _ _).comp
      (measurable_truncLim (sqWd n)))).stronglyMeasurable).measurable

/-- **`patchT` recovers a length metric from its truncated internal limits** -/
theorem patchT_eq {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k} (D : ContMetric) (hD : D.IsLength)
    (g : DistC) (h : ∀ n, truncLim ξ εs hεs (sqWd n) g = truncD (sqWd n) D.1) :
    patchT ξ εs hεs g = D := by
  have hF : ∀ p, patchF ξ εs hεs g p = D.1 p := fun p => by
    refine Tendsto.limUnder_eq ?_
    refine (tendsto_internal_sqW_toReal D hD p.1 p.2).congr fun n => ?_
    rw [h n, ← internal_eq_tChainInf D hD (sqWd n)]
    rfl
  have e : (fun a => patchF ξ εs hεs g (Qd a)) = D.1 ∘ Qd := funext fun a => hF (Qd a)
  rw [patchT, e, contQ_comp, toContMetric_coe]

end LQGMetric.DFGPS.T12
