/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.CoordApprox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13Scale
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelDistOn
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange

/-!
# Pairings of the field as limits of coordinates of `pairJ ⊤` (D90)

D90 (decisions/DEC-90.md) states the joint convergence in law of DFGPS Lemmas 2.13, 2.17, 2.20
(`Lem2_13`, `Lem2_17Core`, `Lem2_17`, `Lem2_20`) in the coordinates `pairJ ⊤ ∘ h` of the field
(the Polish space `CoordJ → ℝ` on which Prokhorov's theorem produces the subsequential limits of
DFGPS T:1342). The proofs of these lemmas push the convergence through the circle average `h_r(z)`,
which they approximate a.s. by continuous functions of the coordinates:

* `exists_coord_seq`: every pairing `g ↦ ⟨g, φ⟩` is a pointwise limit of coordinate projections
  `g ↦ pairJ ⊤ g c_k` (density of the generators `distGen`, as in
  `distOn_measurableSpace_eq_comap`);
* `exists_coord_approx`: an a.s. limit of pairings `⟨h, φ_m⟩` is an a.s. limit of coordinate
  projections (diagonal choice, convergence in measure and Borel–Cantelli);
* `exists_coord_circ`: the circle average `h_r(z)` of a whole-plane GFF is an a.s. limit of
  continuous functions of `pairJ ⊤ h` (pairings with mollified circle measures,
  `CircleAvg.ae_tendsto_mollAvg`).

Own elementary argument (the paper works with the weak topology of `𝒟'` and does not need it);
DEVIATIONS DV-D90.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal Distributions

namespace LQGMetric.DFGPS.CoordApprox

/-- every pairing with a test function is a pointwise limit of coordinates of `pairJ ⊤` -/
theorem exists_coord_seq (φ : TestC) : ∃ c : ℕ → CoordJ, ∀ g : DistC,
    Tendsto (fun k => pairJ ⊤ g (c k)) atTop (𝓝 (g φ)) := by
  obtain ⟨n, hn⟩ := exists_exhaustK_superset (⊤ : Opens ℂ) φ.hasCompactSupport.isCompact
    φ.tsupport_subset
  let ψ : 𝓓^{⊤}_{exhaustK (⊤ : Opens ℂ) n}(ℂ, ℝ) :=
    ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hn h)⟩
  have hψ : TestFunction.ofSupportedIn (exhaustK_subset (⊤ : Opens ℂ) n) ψ = φ := by ext; rfl
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 ((denseRange_denseSeqK (⊤ : Opens ℂ) n) ψ)
  choose k hk using hs
  refine ⟨fun i => Finsupp.single (n, k i) 1, fun g => ?_⟩
  have hc : Continuous fun χ : 𝓓^{⊤}_{exhaustK (⊤ : Opens ℂ) n}(ℂ, ℝ) =>
      g (TestFunction.ofSupportedIn (exhaustK_subset (⊤ : Opens ℂ) n) χ) :=
    (map_continuous g).comp
      (TestFunction.ofSupportedInCLM ℝ (exhaustK_subset (⊤ : Opens ℂ) n)).continuous
  have := (hc.tendsto ψ).comp hlim
  rw [hψ] at this
  refine this.congr fun i => ?_
  simp only [Function.comp_apply, pairJ, comb_single, distGen, ← hk i]

/-- an a.s. limit of pairings `⟨h, φ_m⟩` is an a.s. limit of coordinates of `pairJ ⊤ h` -/
theorem exists_coord_approx {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {h : Ω → DistC} (hh : Measurable h) (φ : ℕ → TestC) (A : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, Tendsto (fun m => h ω (φ m)) atTop (𝓝 (A ω))) :
    ∃ c : ℕ → CoordJ, ∀ᵐ ω ∂P, Tendsto (fun m => pairJ ⊤ (h ω) (c m)) atTop (𝓝 (A ω)) := by
  choose c hc using fun m => exists_coord_seq (φ m)
  have hmeas : ∀ m k, Measurable fun ω => pairJ ⊤ (h ω) (c m k) := fun m k =>
    (measurable_distOn_apply _).comp hh
  have hk : ∀ m : ℕ, ∃ k, P {ω | ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ≤
      edist (pairJ ⊤ (h ω) (c m k)) (h ω (φ m))} ≤ (2⁻¹ : ℝ≥0∞) ^ m := by
    intro m
    have hT : TendstoInMeasure P (fun k ω => pairJ ⊤ (h ω) (c m k)) atTop
        (fun ω => h ω (φ m)) :=
      tendstoInMeasure_of_tendsto_ae (fun k => (hmeas m k).aestronglyMeasurable)
        (Eventually.of_forall fun ω => hc m (h ω))
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ m) :=
      ENNReal.ofReal_pos.2 (by positivity)
    have h2 : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ m :=
      ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) m
    exact ((hT _ hpos).eventually (ge_mem_nhds h2)).exists
  choose k hk using hk
  refine ⟨fun m => c m (k m), ?_⟩
  have hsum : (∑' m, P {ω | ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ≤
      edist (pairJ ⊤ (h ω) (c m (k m))) (h ω (φ m))}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hk)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_eventually_notMem hsum, hA] with ω h1 h2
  have hd : Tendsto (fun m => dist (pairJ ⊤ (h ω) (c m (k m))) (h ω (φ m))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) (h1.mono fun m hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
    simp only [not_le] at hm
    exact (edist_lt_ofReal.1 hm).le
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
    (fun m => dist_triangle _ (h ω (φ m)) _) ?_)
  simpa using hd.add (tendsto_iff_dist_tendsto_zero.1 h2)

/-- the circle average `h_r(z)` of a whole-plane GFF is an a.s. limit of continuous (coordinate)
functions of `pairJ ⊤ h` -/
theorem exists_coord_circ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∃ g : ℕ → (CoordJ → ℝ) → ℝ, (∀ m, Continuous (g m)) ∧ (∀ m, Measurable (g m)) ∧
      ∀ᵐ ω ∂P, Tendsto (fun m => g m (pairJ ⊤ (h ω))) atTop (𝓝 (circleAvg (h ω) r z)) := by
  have hA : ∀ᵐ ω ∂P, Tendsto (fun m => h ω (CircleAvg.circBump m z r)) atTop
      (𝓝 (circleAvg (h ω) r z)) := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hh z hr] with ω hω
    have e : ∀ m, h ω (CircleAvg.circBump m z r) = CircleAvg.mollAvg (h ω) m z r := fun m =>
      (CircleAvg.circleAverage_pairing (h ω) m z r).symm
    simp only [e]
    rw [CircleAvg.circleAvg_eq_limUnder]
    exact tendsto_nhds_limUnder hω
  obtain ⟨c, hc⟩ := exists_coord_approx hh.measurable (fun m => CircleAvg.circBump m z r) _ hA
  exact ⟨fun m x => x (c m), fun m => continuous_apply _, fun m => measurable_pi_apply _, hc⟩

end LQGMetric.DFGPS.CoordApprox
