/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightC at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightChain
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
GM (arXiv:1905.00383v3) l. 449–452 / DFGPS (1.4), T:370–374: the laws of
`𝔠_r⁻¹ e^{−ξ h_r(0)} sup_{u,v ∈ rK} D_h(u, v; rU)` are tight. No proof in either paper.
Decision D-A3 (`decisions/DEC-A.md` (c), S2.4c) reads `U` as a bounded **connected** open set
(for disconnected `U` and `K` meeting two components the internal diameter is `∞`) and proves:

`gm_S2_4c`: for every `ε > 0` there is `S > 0` such that, uniformly over whole-plane GFFs `h`,
scales `r > 0` and centres `z`,
`P[∃ u, v ∈ K, D_h(ru + z, rv + z; rU + z) > S 𝔠_r e^{ξ h_r(z)}] < ε`.

Proof (D-A3): take the compact `L ⊇ K` of `exists_chain_compact`; on the event of S2.4a for
`(L, ∂U)` at level `s` and S2.4b on `L` at level `s` (probability `≥ 1 − ε`), and on the a.s. event
that `D_h` is a length metric (Axiom I), every chain step `x, y ∈ L`, `|x − y| ≤ b` has
`D_h(x′, y′) < s𝔞 < D_h(x′, ∂(rU + z))`, hence `D_h(x′, y′; rU + z) = D_h(x′, y′)` (length-space
fact, DFGPS L2.11 proof T:978–989, `ContMetric.internal_eq_of_lt_infEDist_frontier`), and the
triangle inequality along the `N`-step chain gives `D_h(u′, v′; rU + z) ≤ N s 𝔞`.
Own argument (no source); DEVIATIONS DA5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

/-- the homeomorphism `w ↦ r w + z` -/
def affHomeo (r : ℝ) (hr : r ≠ 0) (z : ℂ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (r : ℂ) (Complex.ofReal_ne_zero.2 hr)).trans (Homeomorph.addRight z)

/-- Deterministic chaining step of S2.4c. -/
theorem internal_le_of_chain {D : ContMetric} (hlen : D.IsLength) {U L : Set ℂ} (hU : IsOpen U)
    (hLU : L ⊆ U) (e : ℂ ≃ₜ ℂ) {a b : ℝ} (ha : 0 < a)
    (hA : ∀ x ∈ L, ∀ w ∈ frontier U, a < D.1 (e x, e w))
    (hB : ∀ x ∈ L, ∀ y ∈ L, ‖x - y‖ ≤ b → D.1 (e x, e y) < a) {N : ℕ} {u v : ℂ}
    (hc : ChainJoined L b N u v) :
    D.internal (e '' U) (e u) (e v) ≤ ENNReal.ofReal (N * a) := by
  obtain ⟨x, hx0, hxL, hxs, hxe⟩ := hc
  have hV : IsOpen (e '' U) := e.isOpenMap U hU
  have hstep : ∀ i, D.internal (e '' U) (e (x i)) (e (x (i + 1))) ≤ ENNReal.ofReal a := by
    intro i
    have hlt : edist (D.pt (e (x i))) (D.pt (e (x (i + 1)))) <
        Metric.infEDist (D.pt (e (x i))) (D.pt '' frontier (e '' U)) := by
      refine lt_of_lt_of_le (b := ENNReal.ofReal a) ?_ (Metric.le_infEDist.2 ?_)
      · exact (show edist (D.pt (e (x i))) (D.pt (e (x (i + 1)))) =
          ENNReal.ofReal (D.1 (e (x i), e (x (i + 1)))) from edist_dist _ _).trans_lt
          ((ENNReal.ofReal_lt_ofReal_iff ha).2 (hB _ (hxL i) _ (hxL (i + 1)) (hxs i)))
      · rintro _ ⟨y, hy, rfl⟩
        rw [← e.image_frontier] at hy
        obtain ⟨w, hw, rfl⟩ := hy
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hA _ (hxL i) _ hw).le
    rw [(ContMetric.internal_eq_of_lt_infEDist_frontier hlen hV ⟨_, hLU (hxL i), rfl⟩ hlt).2,
      edist_dist]
    exact ENNReal.ofReal_le_ofReal (hB _ (hxL i) _ (hxL (i + 1)) (hxs i)).le
  have hk : ∀ k : ℕ, D.internal (e '' U) (e u) (e (x k)) ≤ ENNReal.ofReal (k * a) := by
    intro k
    induction k with
    | zero =>
      rw [hx0]
      simp only [ContMetric.internal]
      rw [MetricGeometry.internalEDist_self (show D.pt (e u) ∈ D.pt '' (e '' U) from
        ⟨e u, ⟨u, hx0 ▸ hLU (hxL 0), rfl⟩, rfl⟩)]
      exact zero_le
    | succ k ih =>
      calc D.internal (e '' U) (e u) (e (x (k + 1)))
          ≤ D.internal (e '' U) (e u) (e (x k)) + D.internal (e '' U) (e (x k)) (e (x (k + 1))) :=
            MetricGeometry.internalEDist_triangle _ _ _ _
        _ ≤ ENNReal.ofReal (k * a) + ENNReal.ofReal a := add_le_add ih (hstep k)
        _ = ENNReal.ofReal ((k + 1 : ℕ) * a) := by
            rw [← ENNReal.ofReal_add (by positivity) ha.le]; push_cast; ring_nf
  have := hk N
  rwa [hxe N le_rfl] at this

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **GM.S2.4c** (D-A3): tightness of the rescaled internal diameter of `rK + z` in `rU + z`,
for `U` bounded, open and connected and `K ⊆ U` compact, uniformly in the field, the scale and the
centre. -/
theorem gm_S2_4c (hD : IsWeakLQGMetric γ D c) {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsConnected U) (hUb : Bornology.IsBounded U) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ S : ℝ, 0 < S ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K,
        (D (h ω)).internal ((fun w => (r : ℂ) * w + z) '' U) ((r : ℂ) * u + z) ((r : ℂ) * v + z)
          ≤ ENNReal.ofReal (S * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z))} < ε := by
  obtain ⟨L, hLc, hKL, hLU, hchain⟩ := exists_chain_compact hU hUc hK hKU
  have hfc : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hdisj : Disjoint L (frontier U) :=
    (Set.disjoint_iff_inter_eq_empty.2 hU.inter_frontier_eq).mono_left hLU
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨s, hs, HA⟩ := gm_S2_4a hD hLc hfc hdisj hε2
  obtain ⟨b, hb, HB⟩ := gm_S2_4b hD hLc hs hε2
  obtain ⟨N, hN⟩ := hchain b hb
  refine ⟨N * s + s, by positivity, fun P _ h hh r hr z => ?_⟩
  have hcr := hD.tightness.1 r hr
  have hgood : ∀ ω, (D (h ω)).IsLength →
      (∀ u ∈ L, ∀ v ∈ frontier U, s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
        (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)) →
      (∀ u ∈ L, ∀ v ∈ L, ‖u - v‖ ≤ b → (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z) <
        s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)) →
      ∀ u ∈ K, ∀ v ∈ K, (D (h ω)).internal ((fun w => (r : ℂ) * w + z) '' U)
        ((r : ℂ) * u + z) ((r : ℂ) * v + z) ≤
        ENNReal.ofReal ((N * s + s) * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)) := by
    intro ω hlen h1 h2 u hu v hv
    have ha : 0 < s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) := by positivity
    have := internal_le_of_chain hlen hU hLU (affHomeo r hr.ne' z) ha h1 h2
      (hN u hu v hv)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have e : (N * s + s) * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) =
        N * (s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)) +
          s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) := by ring
    rw [e]; linarith
  have hlenae := hD.length P h (isGFFPlusCont_of_wp hh)
  calc _ ≤ P ({ω | ¬ ∀ u ∈ L, ∀ v ∈ frontier U,
          s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
            (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)} ∪
        {ω | ¬ ∀ u ∈ L, ∀ v ∈ L, ‖u - v‖ ≤ b →
          (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z) <
            s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)}) := by
        refine measure_mono_ae ?_
        filter_upwards [hlenae] with ω hlen hbad
        by_contra hcon
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
        exact hbad (hgood ω hlen hcon.1 hcon.2)
    _ ≤ _ := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (HA P h hh r hr z) (HB P h hh r hr z)
    _ = ε := ENNReal.add_halves ε

end Tight
end GM
end LQGMetric
