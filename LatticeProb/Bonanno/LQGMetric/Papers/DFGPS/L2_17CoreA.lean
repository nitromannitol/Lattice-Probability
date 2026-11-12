/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreFM
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: coordinates and transfer (packet P-A of D80)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17
(T:1218–1282); decision D80 (`decisions/DEC-80.md` §2–3, packet P-A).

D80 replaces the `h`-coordinate of the convergence in law of `Lem2_17Core` (which lives on
`DistC` with mathlib's compact-convergence topology) by the countable coordinates
`pairJ ⊤ ∘ h : Ω → (CoordJ → ℝ)` (a Polish space), and transports only `Indep` statements
between couplings. This file supplies the bookkeeping:

* `continuous_pairJ` — `pairJ ⊤` is continuous (each coordinate is an evaluation).
* `hconv_pairJ` — the convergence in law of `Lem2_17Core` in the coordinates `pairJ ⊤`.
* `indep_comap_of_map_eq` — independence of pulled-back σ-algebras only depends on the law.
* `indep_of_le_aeClosure` — independence passes to σ-algebras a.s. contained in the given ones.
* `fieldSigmaClosed_le_comap_pairJ` — `σ(h|_K) ≤ σ(pairJ ∘ h)`.

All standard (own elementary arguments, DV-D80).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip

/-- independence of σ-algebras pulled back by a random variable only depends on its law -/
theorem indep_comap_of_map_eq {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [mS : MeasurableSpace S] {P : Measure Ω} {P' : Measure Ω'} {X : Ω → S} {X' : Ω' → S}
    (hX : Measurable X) (hX' : Measurable X') (hlaw : P.map X = P'.map X')
    {A B : MeasurableSpace S} (hA : A ≤ mS) (hB : B ≤ mS)
    (h : Indep (A.comap X') (B.comap X') P') : Indep (A.comap X) (B.comap X) P := by
  rw [Indep_iff] at h ⊢
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have hs' := hA s hs
  have ht' := hB t ht
  have e : ∀ u, MeasurableSet[mS] u → P (X ⁻¹' u) = P' (X' ⁻¹' u) := fun u hu => by
    rw [← Measure.map_apply hX hu, hlaw, Measure.map_apply hX' hu]
  rw [← preimage_inter, e _ (hs'.inter ht'), e _ hs', e _ ht', preimage_inter]
  exact h _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩

/-- independence passes to σ-algebras whose events are a.s. events of the given ones -/
theorem indep_of_le_aeClosure {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {A B A' B' : MeasurableSpace Ω} (h : Indep A B μ) (hA' : A' ≤ aeClosure μ A)
    (hB' : B' ≤ aeClosure μ B) : Indep A' B' μ := by
  rw [Indep_iff] at h ⊢
  intro t1 t2 h1 h2
  obtain ⟨s1, hs1, e1⟩ := hA' t1 h1
  obtain ⟨s2, hs2, e2⟩ := hB' t2 h2
  rw [measure_congr (e1.inter e2), measure_congr e1, measure_congr e2]
  exact h _ _ hs1 hs2

/-- `σ(g|_K) ≤ σ(pairJ ⊤ ∘ g)` -/
theorem fieldSigmaClosed_le_comap_pairJ {Ω : Type} [MeasurableSpace Ω] (g : Ω → DistC)
    (K : Set ℂ) :
    fieldSigmaClosed g K ≤ MeasurableSpace.comap (fun ω => pairJ ⊤ (g ω)) inferInstance := by
  refine (iInf₂_le (1 : ℝ) one_pos).trans ?_
  have e : MeasurableSpace.comap (fun ω => pairJ ⊤ (g ω)) MeasurableSpace.pi =
      MeasurableSpace.comap g (DistOn.measurableSpace ⊤) := by
    rw [distOn_measurableSpace_eq_comap_pairJ, MeasurableSpace.comap_comp]; rfl
  show fieldSigma g (nbhdO 1 K) ≤ _
  rw [e, fieldSigma]
  exact ((measurable_restrictTo _).comp (comap_measurable g)).comap_le

end LQGMetric.DFGPS.L217
