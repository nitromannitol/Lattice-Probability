/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeat at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
(task P2-KILLED, decision D-KHK1, `decisions/DEC-KHK.md`)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 467–469) write the killed heat kernel
of a domain `A` as `p_A(t; u, v) = (2πt)⁻¹ e^{−|u−v|²/(2t)} q(t; u, v)` with
`q(t; u, v) = P(B_s − (s/t)B_t + u + (s/t)(v − u) ∈ A for all s ≤ t)`.
Here `B_s − (s/t) B_t` is a planar Brownian bridge of length `t`, i.e. a continuous centred
Gaussian process whose coordinates are independent with covariance `min(s,r) − sr/t`
(`IsPlanarBridge`). Main result:

* `KilledHeat.measure_bridgeEvent_eq`: for open `A` the probability that `z + (s/t)(w − z) + X_s`
  stays in `A` on `[0, t]` is the same for every planar bridge `X` of length `t` on every
  probability space. (Law of a continuous Gaussian process; `KilledHeatLaw.lean`.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}

/-- The two real coordinates of a planar process, as one real process indexed by
`Bool × ℝ≥0` (`false` ↦ real part, `true` ↦ imaginary part). -/
def coordProc (X : ℝ≥0 → Ω → ℂ) : Bool × ℝ≥0 → Ω → ℝ :=
  fun p ω ↦ if p.1 then (X p.2 ω).im else (X p.2 ω).re

/-- Covariance of the planar Brownian bridge of length `t`: independent coordinates, each with
covariance `min(s, r) − s r / t`. -/
def bridgeCov (t : ℝ≥0) (p q : Bool × ℝ≥0) : ℝ :=
  if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) - (p.2 : ℝ) * q.2 / t else 0

/-- `X` is a planar Brownian bridge of length `t` (on `[0, t]`) under `P`: a.s. continuous paths,
jointly Gaussian centred coordinates with the bridge covariance. -/
structure IsPlanarBridge (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) (P : Measure Ω) : Prop where
  cont : ∀ᵐ ω ∂P, Continuous (fun s ↦ X s ω)
  gauss : IsGaussianProcess (coordProc X) P
  mean : ∀ p, P[coordProc X p] = 0
  cov : ∀ p q, p.2 ≤ t → q.2 ≤ t → cov[coordProc X p, coordProc X q; P] = bridgeCov t p q

/-- The bridge from `z` to `w` in time `t` built from the centred bridge `X`:
`z + (s/t)(w − z) + X_s`. -/
def bridgePath (t : ℝ≥0) (z w : ℂ) (X : ℝ≥0 → Ω → ℂ) (s : ℝ≥0) (ω : Ω) : ℂ :=
  z + (((s : ℝ) / t : ℝ) : ℂ) * (w - z) + X s ω

/-- The event that the bridge from `z` to `w` stays in `A` during `[0, t]`. -/
def bridgeEvent (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) (X : ℝ≥0 → Ω → ℂ) : Set Ω :=
  {ω | ∀ s : ℝ≥0, s ≤ t → bridgePath t z w X s ω ∈ A}

/-- A point of `ℂ` from the two real coordinates of `g` at index `q`. -/
def cpt (g : Bool × ℚ → ℝ) (q : ℚ) : ℂ := (g (false, q) : ℂ) + (g (true, q) : ℂ) * Complex.I

/-- The countable version of `bridgeEvent`, a measurable subset of `Bool × ℚ → ℝ`. -/
def cEvent (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) : Set (Bool × ℚ → ℝ) :=
  ⋃ n : ℕ, ⋂ q : ℚ,
    {g | z + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (w - z) + cpt g q ∈ innerSet A n}

/-- The coordinates of `X` sampled at the times `clampT t q`. -/
def sampled (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) : Bool × ℚ → Ω → ℝ :=
  fun p ω ↦ coordProc X (p.1, clampT t p.2) ω

lemma cpt_sampled (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) (ω : Ω) (q : ℚ) :
    cpt (fun p ↦ sampled t X p ω) q = X (clampT t q) ω := by
  simp [cpt, sampled, coordProc, Complex.re_add_im]

lemma measurableSet_cEvent (A : Set ℂ) (t : ℝ≥0) (z w : ℂ) : MeasurableSet (cEvent A t z w) := by
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.iInter fun q ↦ ?_
  have hm : Measurable fun g : Bool × ℚ → ℝ ↦
      z + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (w - z) + cpt g q := by
    unfold cpt
    fun_prop
  exact hm (isClosed_innerSet A n).measurableSet

lemma mem_bridgeEvent_iff (A : Set ℂ) (hA : IsOpen A) (t : ℝ≥0) (z w : ℂ)
    (X : ℝ≥0 → Ω → ℂ) {ω : Ω} (hω : Continuous fun s ↦ X s ω) :
    ω ∈ bridgeEvent A t z w X ↔ (fun p ↦ sampled t X p ω) ∈ cEvent A t z w := by
  have hF : Continuous fun s ↦ bridgePath t z w X s ω := by
    unfold bridgePath
    fun_prop
  simp only [bridgeEvent, Set.mem_ofPred_eq, cEvent, Set.mem_iUnion, Set.mem_iInter,
    cpt_sampled]
  exact forall_mem_iff_exists_clamp hF hA t

lemma sampled_isGaussianProcess {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) : IsGaussianProcess (sampled t X) P :=
  hX.gauss.comp_right (fun p : Bool × ℚ ↦ (p.1, clampT t p.2))

lemma measure_bridgeEvent_eq_map {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) {A : Set ℂ} (hA : IsOpen A) (z w : ℂ) :
    P (bridgeEvent A t z w X) =
      (P.map (fun ω p ↦ sampled t X p ω)) (cEvent A t z w) := by
  have hm : AEMeasurable (fun ω p ↦ sampled t X p ω) P :=
    .of_eval fun p ↦ (sampled_isGaussianProcess hX).aemeasurable p
  rw [Measure.map_apply_of_aemeasurable hm (measurableSet_cEvent A t z w)]
  refine measure_congr ?_
  filter_upwards [hX.cont] with ω hω
  exact propext (mem_bridgeEvent_iff A hA t z w X hω)

/-- **Law invariance.** The probability that the bridge from `z` to `w` stays in an open set `A`
on `[0, t]` does not depend on the planar bridge used. -/
theorem measure_bridgeEvent_eq {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {Y : ℝ≥0 → Ω' → ℂ}
    {P : Measure Ω} {P' : Measure Ω'} (hX : IsPlanarBridge t X P) (hY : IsPlanarBridge t Y P')
    {A : Set ℂ} (hA : IsOpen A) (z w : ℂ) :
    P (bridgeEvent A t z w X) = P' (bridgeEvent A t z w Y) := by
  rw [measure_bridgeEvent_eq_map hX hA, measure_bridgeEvent_eq_map hY hA,
    map_eq_of_gaussian (sampled_isGaussianProcess hX) (sampled_isGaussianProcess hY)]
  · intro p
    exact (hX.mean _).trans (hY.mean _).symm
  · intro p q
    show cov[coordProc X _, coordProc X _; P] = cov[coordProc Y _, coordProc Y _; P']
    rw [hX.cov _ _ (clampT_le t _) (clampT_le t _), hY.cov _ _ (clampT_le t _) (clampT_le t _)]


/-! ### Planar Brownian motion and its bridge -/

/-- `W` is a standard planar Brownian motion started at `0` under `P` (as a centred Gaussian
process with independent coordinates of covariance `min(s, r)` and a.s. continuous paths). -/
structure IsPlanarBM (W : ℝ≥0 → Ω → ℂ) (P : Measure Ω) : Prop where
  cont : ∀ᵐ ω ∂P, Continuous (fun s ↦ W s ω)
  gauss : IsGaussianProcess (coordProc W) P
  mean : ∀ p, P[coordProc W p] = 0
  cov : ∀ p q, cov[coordProc W p, coordProc W q; P] =
    if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0

/-- The centred bridge `W_s − (s/t) W_t` of a planar process `W`. -/
def bridgeOf (t : ℝ≥0) (W : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ :=
  fun s ω ↦ W s ω - (((s : ℝ) / t : ℝ) : ℂ) * W t ω

lemma coordProc_bridgeOf (t : ℝ≥0) (W : ℝ≥0 → Ω → ℂ) (p : Bool × ℝ≥0) :
    coordProc (bridgeOf t W) p =
      fun ω ↦ coordProc W p ω - ((p.2 : ℝ) / t) * coordProc W (p.1, t) ω := by
  ext ω
  rcases p with ⟨b, s⟩
  cases b <;> simp [coordProc, bridgeOf]

/-- `W_s − (s/t) W_t` is a planar Brownian bridge of length `t`. -/
theorem IsPlanarBM.isPlanarBridge {W : ℝ≥0 → Ω → ℂ} {P : Measure Ω} (hW : IsPlanarBM W P)
    (t : ℝ≥0) (ht : t ≠ 0) : IsPlanarBridge t (bridgeOf t W) P := by
  have := hW.gauss.isProbabilityMeasure
  have hL2 : ∀ p, MemLp (coordProc W p) 2 P := fun p ↦ (hW.gauss.hasGaussianLaw_eval p).memLp_two
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hW.cont] with ω hω
    unfold bridgeOf
    fun_prop
  · refine hW.gauss.of_isGaussianProcess fun p ↦ ?_
    classical
    refine ⟨{p, (p.1, t)}, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({p, (p.1, t)} :
      Finset (Bool × ℝ≥0)) ↦ ℝ) ⟨p, by simp⟩) - ((p.2 : ℝ) / t) •
      (ContinuousLinearMap.proj ⟨(p.1, t), by simp⟩), fun ω ↦ ?_⟩
    rw [coordProc_bridgeOf]
    simp
  · intro p
    rw [coordProc_bridgeOf, integral_sub ((hL2 p).integrable (by norm_num))
      (((hL2 _).integrable (by norm_num)).const_mul _),
      integral_const_mul, hW.mean, hW.mean]
    simp
  · intro p q hp hq
    have hb : ∀ p : Bool × ℝ≥0, MemLp (fun ω ↦ coordProc W p ω -
        ((p.2 : ℝ) / t) * coordProc W (p.1, t) ω) 2 P := fun p ↦
      (hL2 p).sub ((hL2 _).const_mul _)
    rw [coordProc_bridgeOf, coordProc_bridgeOf, covariance_fun_sub_left (hL2 p)
      ((hL2 _).const_mul _) (hb q),
      covariance_fun_sub_right (hL2 p) (hL2 q) ((hL2 _).const_mul _),
      covariance_fun_sub_right ((hL2 _).const_mul _) (hL2 q) ((hL2 _).const_mul _),
      covariance_const_mul_right, covariance_const_mul_left, covariance_const_mul_left,
      covariance_const_mul_right, hW.cov, hW.cov, hW.cov, hW.cov]
    rcases p with ⟨b, s⟩
    rcases q with ⟨b', r⟩
    simp only at hp hq ⊢
    unfold bridgeCov
    by_cases hb : b = b'
    · subst hb
      simp only [ite_true, min_eq_left hp, min_eq_right hq, min_self, NNReal.coe_min]
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      field_simp
      ring
    · simp [hb]

end KilledHeat
end LQGMetric
