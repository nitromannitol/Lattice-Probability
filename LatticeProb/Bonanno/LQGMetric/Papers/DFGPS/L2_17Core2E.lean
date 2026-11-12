/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core2E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2D
import LatticeProb.Bonanno.LQGMetric.Meas.Internal
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the internal metrics of a dyadic limit are determined by `d_W`

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3–4 (T:1248–1278): Lemma 2.5 B identifies, on `W`, the internal metric of the limit `D` with
that of the limit `d_W` of `𝔞⁻¹D^ε(·,·;W̄)`, so `D(·,·;W)` is determined by `d_W`; this is how the
independence of the `d_W`'s (eqn-limit-metric-ind) becomes the independence of the internal
metrics of `D`. The measurability statement needed for that is not in the paper ("clearly"); we
prove it by Lusin's separation theorem (as in `comap_le_fieldSigma_of_local`): own argument.

* `comap_le_aeClosure_of_fiber` — on a standard Borel space, if a measurable `F` is constant on
  the fibres of a measurable `R` (into a second-countable Borel space) on a conull measurable
  set, then `σ(F) ⊆ σ(R)` up to null sets.
* `intFn W d` — `D(·,·;W)` as a Borel function of `d = D ∈ C(ℂ × ℂ, ℝ)` (the countable chain
  formula `ContMetric.chainInf` of `Meas/Internal.lean`; `0` off continuous metrics);
  `internal_eq_intFn` for length metrics, `measurable_intFn`.
* `intFn_eq_of_isDyadicLimit` — for dyadic limits `x, x'` with `x.2 W = x'.2 W`, the internal
  metrics on `W` of `x.1` and `x'.1` agree (Lemma 2.5 B, `IsDyadicLimit`).
* `comap_intFn_le_aeClosure` — under a law carried by dyadic limits,
  `σ(D(·,·;W)) ⊆ σ(d_W)` up to null sets.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

open Blueprint LFPP MetricGeometry GM.Bilip

/-- **Lusin separation, fibre form**: a measurable `F` constant on the fibres of a measurable `R`
on a conull measurable set is `σ(R)`-measurable up to null sets. -/
theorem comap_le_aeClosure_of_fiber {X Y β : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [T2Space Y] [mβ : MeasurableSpace β] {μ : Measure X} {F : X → β} (hF : Measurable F)
    {R : X → Y} (hR : Measurable R) {L : Set X} (hL : MeasurableSet L) (hμL : μ Lᶜ = 0)
    (hfib : ∀ x ∈ L, ∀ x' ∈ L, R x = R x' → F x = F x') :
    MeasurableSpace.comap F mβ ≤ aeClosure μ (MeasurableSpace.comap R inferInstance) := by
  rintro _ ⟨s, hs, rfl⟩
  have hA : MeasurableSet (F ⁻¹' s ∩ L) := (hF hs).inter hL
  have hA' : MeasurableSet (F ⁻¹' sᶜ ∩ L) := (hF hs.compl).inter hL
  have h1 := hA.analyticSet_image hR
  have h2 := hA'.analyticSet_image hR
  have hdisj : Disjoint (R '' (F ⁻¹' s ∩ L)) (R '' (F ⁻¹' sᶜ ∩ L)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, ⟨hx, hxL⟩, rfl⟩ ⟨x', ⟨hx', hx'L⟩, he⟩
    exact hx' (show F x' ∈ s by rw [hfib x' hx'L x hxL he]; exact hx)
  obtain ⟨u, hAu, hdu, hu⟩ := h1.measurablySeparable h2 hdisj
  refine ⟨R ⁻¹' u, ⟨u, hu, rfl⟩, ?_⟩
  have hLae : ∀ᵐ x ∂μ, x ∈ L := ae_iff.2 (by simpa [compl_def] using hμL)
  filter_upwards [hLae] with x hxL
  change (x ∈ F ⁻¹' s) = (x ∈ R ⁻¹' u)
  refine propext ⟨fun h => hAu ⟨x, ⟨h, hxL⟩, rfl⟩, fun h => ?_⟩
  by_contra hn
  exact Set.disjoint_left.1 hdu ⟨x, ⟨hn, hxL⟩, rfl⟩ h

/-- `D(·,·;W)` as a Borel function of `D ∈ C(ℂ × ℂ, ℝ)` (chain formula; `0` off metrics) -/
def intFn (W : Set ℂ) (d : C(ℂ × ℂ, ℝ)) : ℂ → ℂ → ℝ≥0∞ := by
  classical
  exact fun u v => if hd : IsContinuousMetric d then ContMetric.chainInf ⟨d, hd⟩ W u v else 0

theorem measurable_intFn (W : Set ℂ) : Measurable (intFn W) := by
  classical
  refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
  set s : Set C(ℂ × ℂ, ℝ) := {d | IsContinuousMetric d}
  have hf : Measurable fun D : s => ContMetric.chainInf ⟨D.1, D.2⟩ W u v :=
    (ContMetric.measurable_chainInf W).comp (f := fun D : s => ((⟨D.1, D.2⟩ : ContMetric), u, v))
      (measurable_subtype_coe.subtype_mk.prodMk measurable_const)
  have e : (fun d => intFn W d u v) = fun d => if hd : d ∈ s then
      (fun D : s => ContMetric.chainInf ⟨D.1, D.2⟩ W u v) ⟨d, hd⟩
      else (fun _ : (sᶜ : Set C(ℂ × ℂ, ℝ)) => (0 : ℝ≥0∞)) ⟨d, hd⟩ := by
    funext d
    simp only [intFn]
    by_cases hd : IsContinuousMetric d
    · rw [dif_pos hd, dif_pos (show d ∈ s from hd)]
    · rw [dif_neg hd, dif_neg (show d ∉ s from hd)]
  rw [e]
  exact Measurable.dite hf measurable_const measurableSet_isContinuousMetric

theorem internal_eq_intFn (D : ContMetric) (hD : D.IsLength) {W : Set ℂ} (hW : IsOpen W) :
    D.internal W = intFn W D.1 := by
  funext u v
  simp only [intFn, dif_pos D.2]
  exact D.internal_eq_chainInf hD hW u v

theorem internalEDist_metricFun_congr {K : Set ℂ} {d d' : C(K × K, ℝ)} (h : d = d')
    (hd : IsMetricFun ⇑d) (hd' : IsMetricFun ⇑d') (W : Set ℂ) (u v : K) :
    internalEDist {y : MetricFunSpace _ hd | (metricFunSpaceVal _ hd y).1 ∈ W}
        (MetricFunSpace.pt _ hd u) (MetricFunSpace.pt _ hd v) =
      internalEDist {y : MetricFunSpace _ hd' | (metricFunSpaceVal _ hd' y).1 ∈ W}
        (MetricFunSpace.pt _ hd' u) (MetricFunSpace.pt _ hd' v) := by
  subst h; rfl

theorem internal_eq_top_of_notMem (D : ContMetric) {W : Set ℂ} {u v : ℂ} (h : u ∉ W ∨ v ∉ W) :
    D.internal W u v = ⊤ := by
  rcases h with hu | hv
  · refine MetricGeometry.internalEDist_eq_top_of_notMem_left ?_
    rintro ⟨y, hy, hyu⟩
    exact hu (by rw [← show y = u from hyu]; exact hy)
  · refine MetricGeometry.internalEDist_eq_top_of_notMem_right ?_
    rintro ⟨y, hy, hyv⟩
    exact hv (by rw [← show y = v from hyv]; exact hy)

theorem isOpen_of_dyadicDomainsC (W : dyadicDomainsC) : IsOpen (W : Set ℂ) := by
  obtain ⟨𝒮, -, he⟩ := W.2.1
  rw [he]; exact isOpen_interior

/-- **internal metrics of a dyadic limit on `W` are determined by `d_W`** (Lemma 2.5 B) -/
theorem intFn_eq_of_isDyadicLimit {x x' : DyProd} (hx : IsDyadicLimit x)
    (hx' : IsDyadicLimit x') (W : dyadicDomainsC) (he : x.2 W = x'.2 W) :
    intFn W x.1 = intFn W x'.1 := by
  obtain ⟨⟨hc, hl⟩, hW⟩ := hx
  obtain ⟨⟨hc', hl'⟩, hW'⟩ := hx'
  have hWo := isOpen_of_dyadicDomainsC W
  rw [← internal_eq_intFn ⟨x.1, hc⟩ hl hWo, ← internal_eq_intFn ⟨x'.1, hc'⟩ hl' hWo]
  funext u v
  by_cases hu : u ∈ (W : Set ℂ)
  · by_cases hv : v ∈ (W : Set ℂ)
    · obtain ⟨hd, -, -, -, hI⟩ := hW W
      obtain ⟨hd', -, -, -, hI'⟩ := hW' W
      exact (hI hc ⟨u, subset_closure hu⟩ ⟨v, subset_closure hv⟩ hu hv).trans
        ((internalEDist_metricFun_congr he hd hd' _ _ _).trans
          (hI' hc' ⟨u, subset_closure hu⟩ ⟨v, subset_closure hv⟩ hu hv).symm)
    · exact (internal_eq_top_of_notMem _ (Or.inr hv)).trans
        (internal_eq_top_of_notMem _ (Or.inr hv)).symm
  · exact (internal_eq_top_of_notMem _ (Or.inl hu)).trans
      (internal_eq_top_of_notMem _ (Or.inl hu)).symm

/-- **`σ(D(·,·;W)) ⊆ σ(d_W)` up to null sets** under a law carried by dyadic limits -/
theorem comap_intFn_le_aeClosure {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {μ : Measure X} {Pm : X → DyProd} (hPm : Measurable Pm)
    (hdy : ∀ᵐ x ∂μ, IsDyadicLimit (Pm x)) (W : dyadicDomainsC) :
    MeasurableSpace.comap (fun x => intFn W (Pm x).1) inferInstance ≤
      aeClosure μ (MeasurableSpace.comap (fun x => (Pm x).2 W) inferInstance) := by
  obtain ⟨M, hMsup, hMm, hM0⟩ := exists_measurable_superset_of_null (ae_iff.1 hdy)
  refine comap_le_aeClosure_of_fiber ((measurable_intFn W).comp
    (continuous_dyProd_fst.measurable.comp hPm)) ((continuous_dyProd_snd W).measurable.comp hPm)
    hMm.compl (by rwa [compl_compl]) fun x hx x' hx' he => ?_
  have k : ∀ y ∈ Mᶜ, IsDyadicLimit (Pm y) := fun y hy => by
    by_contra hn; exact hy (hMsup hn)
  exact intFn_eq_of_isDyadicLimit (k x hx) (k x' hx') W he

/-- **(eqn-limit-metric-ind) for the internal metrics of `D₁`** (T:1260–1264): in the limit
coupling of `indep_stage_limit`, the `d_W` (`W ∈ 𝒲`) may be replaced by the internal metrics
`D₁(·,·;W)` of the first limit metric (`comap_intFn_le_aeClosure`). -/
theorem indep_stage_intFn {S : Type*} [TopologicalSpace S] [mS : MeasurableSpace S]
    [BorelSpace S] [PolishSpace S] {ρ : Measure (S × (DyProd × DyProd))}
    (hdy : ∀ᵐ p ∂ρ, IsDyadicLimit p.2.1) (𝒲 𝒲' : Finset dyadicDomainsC)
    (𝒢 ℋ : {m : MeasurableSpace S // m ≤ mS})
    (hind : Indep (𝒢.1.comap Prod.fst ⊔ MeasurableSpace.comap
          (fun p : S × (DyProd × DyProd) => famProj 𝒲 p.2.1.2) inferInstance)
        (ℋ.1.comap Prod.fst ⊔ MeasurableSpace.comap
          (fun p : S × (DyProd × DyProd) => famProj 𝒲' p.2.2.2) inferInstance) ρ) :
    Indep (𝒢.1.comap Prod.fst ⊔ ⨆ W ∈ 𝒲, MeasurableSpace.comap
          (fun p : S × (DyProd × DyProd) => intFn W p.2.1.1) inferInstance)
        (ℋ.1.comap Prod.fst ⊔ MeasurableSpace.comap
          (fun p : S × (DyProd × DyProd) => famProj 𝒲' p.2.2.2) inferInstance) ρ := by
  refine indep_of_le_aeClosure hind (sup_le ((le_sup_left).trans (le_aeClosure _))
    (iSup₂_le fun W hW => ?_)) (le_aeClosure _)
  refine (comap_intFn_le_aeClosure (Pm := fun p : S × (DyProd × DyProd) => p.2.1)
    (measurable_fst.comp measurable_snd) hdy W).trans (aeClosure_mono ?_)
  refine le_sup_of_le_right ?_
  have e : (fun p : S × (DyProd × DyProd) => p.2.1.2 W) =
      (fun f : FamT 𝒲 => f ⟨W, hW⟩) ∘ fun p : S × (DyProd × DyProd) => famProj 𝒲 p.2.1.2 := rfl
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.1 (measurable_pi_apply _))

end L217

end LQGMetric.DFGPS
