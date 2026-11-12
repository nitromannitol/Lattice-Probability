/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSInputsLM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Prob.CondLaw

/-!
# Blueprint: the LM and DF results DFGPS §2 cites (task P2-BP-DF)

Sources:
* LM = Gwynne–Miller, *Local metrics of the Gaussian free field*, arXiv:1905.00379,
  `literature/src/1905.00379/local-metrics-final.tex` (cited `LM:`): Def 1.5 (`n = 1`, LM:284–287),
  Lemma 2.3 (`lem-local-equiv`, LM:523–531), Corollary 1.8 (`cor-bilip-msrble`, LM:317–329).
  Consumers: DFGPS (arXiv:1905.00380, cited `T:`) Def 2.15/2.16 (T:1132–1146: "equivalent to
  [LM, Definition 1.2] by [LM, Lemma 2.3]"), Lemma 2.17 (T:1150–1155) and Theorem 2.21 = special
  case of LM Cor 1.8 (T:1305–1316), used in the proof of Lemma 2.20 (T:1316–1331).
* DF = Dubédat–Falconet, *Liouville metric of star-scale invariant fields: tails and Weyl
  scaling*, arXiv:1809.02607, `literature/src/1809.02607/LiouvilleMetricStarScale.tex` (cited
  `DF:`): Lemma 7.1 (`StabMetric`, DF:1280–1285) and the remark after its proof (DF:1344). Consumer:
  DFGPS Lemma 2.12 (T:1026–1051: "apply an argument as in the proof of [DF, Lemma 7.1] … That
  lemma only applies for metrics defined on squares, so we need to localize … the lemma now follows
  from the same proof as in [DF, Lemma 7.1]").

Reused, not restated: GMSh Lemma 2.2 = `LMLem2_1` (DFGPS L2.18 is used only with `V ∩ ∂B_r(z) = ∅`,
T:1221; the normalization `h_r(z) = 0` is reached from `LMLem2_1` by translation and scaling,
a DFGPS-side lemma of `blueprint/DF.md`); LM Lemma 3.1 = `LMLem3_1a`, `LMLem3_1b` (DFGPS L3.3);
LM Def 1.2 = `IsLocalMetric`.

Readings (proposed DEVIATIONS entries BP-DF-5…7, see the P2-BP-DF report):
* LM Cor 1.8 and Lemma 2.3 are stated for `U = ℂ` (decision D21; DFGPS uses only this case), the
  conditionally i.i.d. pair `(D, D̃)` given `h` is the canonical copy `condCopyMeasure` on
  `Ω × ContMetric` (`Prob/CondCopies.lean`, the law of `(h, D, D̃)` is determined by that of
  `(h, D)`), and "`D` is a.s. determined by `h`" is `AEDeterminedBy D h P`.
* LM Def 1.5 with `n = 1` is `IsXiAdditive2 ξ P h D D` (for one metric the joint σ-algebras of
  `IsJointlyLocalFam` coincide with the single ones).
* DF Lemma 7.1 is stated in the **adapted** form DFGPS use (DEV-DFGPS-6): metrics on `ℂ`, GM's
  Weyl scaling `weylScale` (GM (1.6)) instead of DF's Riemann-sum `e^f · d`, local uniform
  convergence on `ℂ` instead of pointwise convergence on `[0,1]²`, and DFGPS's localization
  (T:1036–1048, with Euclidean balls instead of squares and the factor `e^{2|ξ|M}` that the
  argument at T:1046 needs, `M` a bound for `|f^n|`, `|f|`) as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-- **LM Definition 1.5** with `n = 1`, `U = ℂ` (LM:284–287; DFGPS Def 2.16, T:1143–1146):
`D` is a ξ-additive local metric for `h` — `D` is local for `h` and for each `z ∈ ℂ`, `r > 0`,
`e^{−ξh_r(z)} D` is local for `h − h_r(z)`. -/
def IsXiAdditive1 (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D : Ω → ContMetric) : Prop :=
  IsXiAdditive2 ξ P h D D

/-- **LM Corollary 1.8** (`cor-bilip-msrble`, LM:317–329), `U = ℂ`: "There is a universal
constant `p ∈ (0,1)` such that the following is true. Let `U ⊂ ℂ` be a domain which contains the
unit disk, let `h` be a whole-plane GFF normalized so that `h_1(0) = 0`, and let `(h, D)` be a
coupling of `h` with a random continuous length metric on `U` which is local for `h|_U` and
satisfies the following hypotheses. (1) `D` is ξ-additive for `h|_U` for some `ξ ∈ ℝ`. (2)
Condition on `h` and let `D` and `D̃` be conditionally i.i.d. samples from the conditional law of
`D` given `h`. There is a deterministic constant `C > 0` such that for each compact set `K ⊂ U`,
there exists `r_K > 0` such that (1.3) holds for this choice of `D` and `D̃`. Then `D` is a.s.
determined by `h`." (1.3) (LM:295–297): `P[sup_{u,v∈∂B_r(z)} D̃(u,v; 𝔸_{r/2,2r}(z)) ≤
C D(∂B_{r/2}(z), ∂B_r(z))] ≥ p` for `z ∈ K`, `r ∈ (0, r_K]`. -/
def LMCor1_8 : Prop :=
  ∃ p : ℝ, 0 < p ∧ p < 1 ∧
    ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC) (D : Ω → ContMetric) (hh : IsNormalizedWPGFF h P),
      IsXiAdditive1 ξ P h D → ∀ C : ℝ, 0 < C →
      (∀ K : Set ℂ, IsCompact K → ∃ rK : ℝ, 0 < rK ∧ ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) rK,
        ENNReal.ofReal p ≤ condCopyMeasure D h P hh.1.measurable
          {q | internalDiam q.2 (Metric.sphere z r) (annulus z (r / 2) (2 * r)) ≤
            ENNReal.ofReal C * setDist (D q.1) (Metric.sphere z (r / 2)) (Metric.sphere z r)}) →
      AEDeterminedBy D h P

/-- `sup_{u,v ∈ A} D(u, v)` in `[0, ∞]` -/
def supDist (D : ContMetric) (A : Set ℂ) : ℝ≥0∞ :=
  ⨆ u ∈ A, ⨆ v ∈ A, ENNReal.ofReal (D.1 (u, v))

/-- **DF Lemma 7.1** (`StabMetric`, DF:1280–1285, with the remark DF:1344 "the same result holds
if instead of `f`, we assume that a sequence of continuous functions `(f_n)` converges uniformly to
`f`"), **adapted as DFGPS use it** (T:1036–1051, DEV-DFGPS-6): let `D_n`, `D` be continuous length
metrics on `ℂ` with `D_n → D` locally uniformly, and `f_n`, `f` continuous with `|f_n|, |f| ≤ M`
and `f_n → f` locally uniformly; assume the localization of T:1040–1048: for every `r > 0` there is
`r' > r` with `e^{2|ξ|M} sup_{u,v∈B̄_r(0)} D(u,v) < D(B̄_r(0), ∂B_{r'}(0))`. Then
`e^{ξ f_n} · D_n → e^{ξ f} · D` locally uniformly (all values finite). DF's literal lemma
(pointwise convergence of `e^f · d_n` on `[0,1]²` for intrinsic metrics `d_n` with uniform moduli
`r(|x−y|) ≤ d_n(x,y) ≤ R(|x−y|)`) is the special case DFGPS reduce to by localization. -/
def DFLem7_1 : Prop :=
  ∀ (ξ M : ℝ) (Dn : ℕ → ContMetric) (D : ContMetric) (fn : ℕ → C(ℂ, ℝ)) (f : C(ℂ, ℝ)),
    (∀ n, (Dn n).IsLength) → D.IsLength →
    (∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R)) →
    (∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (Metric.closedBall (0 : ℂ) R)) →
    (∀ n z, |fn n z| ≤ M) → (∀ z, |f z| ≤ M) →
    (∀ r : ℝ, 0 < r → ∃ r' : ℝ, r < r' ∧
      ENNReal.ofReal (Real.exp (2 * |ξ| * M)) * supDist D (Metric.closedBall 0 r) <
        setDist D (Metric.closedBall 0 r) (Metric.sphere 0 r')) →
    (∀ z w, weylScale ξ f D z w ≠ ⊤) ∧ (∀ n z w, weylScale ξ (fn n) (Dn n) z w ≠ ⊤) ∧
    ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n (p : ℂ × ℂ) => (weylScale ξ (fn n) (Dn n) p.1 p.2).toReal)
        (fun p => (weylScale ξ f D p.1 p.2).toReal) atTop
        (Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R)

end LQGMetric.Blueprint
