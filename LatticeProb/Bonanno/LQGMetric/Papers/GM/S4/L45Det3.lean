/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Det3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic

/-!
# GM Lemma 4.5: local events of `𝓑^•_{t_k}` (task P2-E2R)

GM, arXiv:1905.00383, `uniqueness-final.tex` l. 1654 ("by Axiom II (locality), `𝓘_k` is
determined by `𝓑^•_{t_k}` and `h|_{𝓑^•_{t_k}}`"). With `t_k = τ_R c` (`gm_s4T_eq`) and
`𝓑^•_{t_k} = gmKt D 𝕫 R c (h)`:

* `gm_hullSat_Kt`: on `{(𝓑^•_{t_k})^{(n)} = S}`, equal internal metrics on `int S` give the
  locality data `GMLocData` (`𝓑^•_{t_k} ⊆ int S`, `LocalEvent.subset_interior_dyadicHull`) and the
  same hull;
* `gm_aeEventIn_Kt`: an event of the field which is invariant under `GMLocData` (and
  null-measurable on each hull piece) is a.s. a `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`-event
  (`LocalEvent.aeEventIn_localSigma_of_saturated`);
* `gm_arcHit_aeEventIn`, `gm_confMem_aeEventIn`: the hit events of the arcs `arcOf x` and the
  events `{x ∈ Conf_k}` (fixed `x`), given their null-measurability;
* `GMLocData.isGeod01`: geodesics from `𝕫` to the points of `𝓑^•_T` are local.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `𝓑^•_{t_k}` as a function of the field, `t_k = τ_R c` -/
def gmKt (D : DistC → ContMetric) (𝕫 : ℂ) (R c : ℝ) (g : DistC) : Set ℂ :=
  filledBall (D g) 𝕫 (tauD (D g) 𝕫 R * c)

theorem gm_filledBall_isBounded_of_lenSet {d : ContMetric} (hd : d ∈ LocalEvent.lenSet)
    (𝕫 : ℂ) (s : ℝ) : Bornology.IsBounded (filledBall d 𝕫 s) := by
  have hb := LocalEvent.bcpt_of_mem_lenSet hd
  have hc : IsCompact (closure (ballM d 𝕫 s)) := by
    refine hb _ isClosed_closure ⟨2 * s, fun u hu v hv => ?_⟩
    have h1 := gm_dist_le_of_mem_closure d 𝕫 hu
    have h2 := gm_dist_le_of_mem_closure d 𝕫 hv
    have := d.2.triangle u 𝕫 v
    rw [d.2.symm u 𝕫] at this
    linarith
  exact (jb_isCompact_filledBall (hc.isBounded.subset subset_closure)).isBounded

/-- **geodesics from `𝕫` to points of `𝓑^•_T` are local** (GM l. 1665–1668) -/
theorem GMLocData.isGeod01 {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {x : ℂ} (hx : x ∈ filledBall d₁ 𝕫 T)
    {η₂ : C(unitInterval, ℂ)} (hη₂ : IsGeod01 d₂ 𝕫 x η₂) {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 d₁ 𝕫 x η) : IsGeod01 d₂ 𝕫 x η := by
  have hr₁ : range η ⊆ U := (gm_range_geod_subset_filledBall hη hx).trans H.sub
  have hx₂ : x ∈ filledBall d₂ 𝕫 T := by rw [H.filledBall_eq le_rfl]; exact hx
  have hr₂ : range η₂ ⊆ U := (gm_range_geod_subset_filledBall hη₂ hx₂).trans
    (by rw [H.filledBall_eq le_rfl]; exact H.sub)
  refine gm_isGeod01_congr H.int hη hr₁ ?_
  have h1 := gm_internal_le_of_isGeod01' hη₂ hr₂
  have h2 : ENNReal.ofReal (d₁.1 (𝕫, x)) ≤ d₁.internal U 𝕫 x := by
    rw [← ContMetric.edist_pt]
    exact MetricGeometry.edist_le_internalEDist _ _ _
  rw [H.int] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (gm_D_nonneg d₂ 𝕫 x)).1 (h2.trans h1)

/-- a filled ball whose closed ball part lies in `cl B_r(𝕫)` lies in `cl B_r(𝕫)` (the outside of
`cl B_r(𝕫)` is connected and unbounded) -/
theorem gm_filledBall_subset_closedBall {d : ContMetric} {𝕫 : ℂ} {s r : ℝ}
    (hX : closure (ballM d 𝕫 s) ⊆ closedBall 𝕫 r) : filledBall d 𝕫 s ⊆ closedBall 𝕫 r := by
  intro x hx
  by_contra hxr
  rw [mem_closedBall, not_le] at hxr
  set X := closure (ballM d 𝕫 s)
  set O : Set ℂ := {w | r < dist w 𝕫}
  have hO : IsPreconnected O := by
    have e : O = (fun w => w + 𝕫) '' {w : ℂ | r < ‖w‖} := by
      ext w
      simp only [O, mem_ofPred_eq, mem_image, dist_eq_norm]
      exact ⟨fun h => ⟨w - 𝕫, h, by ring⟩, fun ⟨v, hv, he⟩ => by rw [← he]; simpa using hv⟩
    rw [e]
    exact (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm r).image _
      (continuous_id.add continuous_const).continuousOn
  have hOX : O ⊆ Xᶜ := fun w hw hwX => absurd (hX hwX) (by
    rw [mem_closedBall, not_le]; exact hw)
  have hxX : x ∉ X := hOX hxr
  have hxb : Bornology.IsBounded (connectedComponentIn Xᶜ x) := by
    rcases hx with hx | ⟨_, hb⟩
    · exact absurd hx hxX
    · exact hb
  have hOb := hxb.subset (hO.subset_connectedComponentIn hxr hOX)
  obtain ⟨M, hM⟩ := (isBounded_iff_subset_closedBall 𝕫).1 hOb
  have hw : 𝕫 + ((max r M + 1 : ℝ) : ℂ) ∈ O := by
    show r < dist _ 𝕫
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le (by linarith [le_max_left r M]) (le_abs_self _)
  have := hM hw
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
    Real.norm_eq_abs] at this
  linarith [le_max_right r M, le_abs_self (max r M + 1)]

/-- **`τ_R > 0` surely** (`R > 0`): small metric balls are Euclidean-small, and some metric ball
leaves `B_R(𝕫)` -/
theorem gm_tauD_pos (d : ContMetric) (𝕫 : ℂ) {R : ℝ} (hR : 0 < R) : 0 < tauD d 𝕫 R := by
  obtain ⟨δ, hδ, hδE⟩ := d.2.euclidean_of_small 𝕫 (R / 2) (by linarith)
  have hsmall : ∀ s, s ≤ δ → filledBall d 𝕫 s ⊆ Metric.ball 𝕫 R := by
    intro s hs
    have h1 : ballM d 𝕫 s ⊆ Metric.ball 𝕫 (R / 2) := fun y hy => by
      rw [mem_ball, dist_comm, dist_eq_norm]
      exact hδE y (lt_of_lt_of_le hy hs)
    have h2 := gm_filledBall_subset_closedBall
      ((closure_mono h1).trans closure_ball_subset_closedBall)
    exact h2.trans (closedBall_subset_ball (by linarith))
  set w : ℂ := 𝕫 + (R : ℂ)
  have hne : {s | 0 < s ∧ ¬ filledBall d 𝕫 s ⊆ Metric.ball 𝕫 R}.Nonempty := by
    refine ⟨d.1 (𝕫, w) + 1, by linarith [gm_D_nonneg d 𝕫 w], fun hsub => ?_⟩
    have hw : w ∈ filledBall d 𝕫 (d.1 (𝕫, w) + 1) :=
      Or.inl (subset_closure (show d.1 (𝕫, w) < d.1 (𝕫, w) + 1 by linarith))
    have := hsub hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR] at this
    exact lt_irrefl _ this
  refine lt_of_lt_of_le hδ (le_csInf hne fun s ⟨_, hs⟩ => ?_)
  by_contra hlt
  exact hs (hsmall s (not_le.1 hlt).le)

/-- **saturation on a hull piece** -/
theorem gm_hullSat_Kt {D : DistC → ContMetric} {𝕫 : ℂ} {R c : ℝ} (hc : 1 < c) {n : ℕ}
    {S : Set ℂ} {g₁ g₂ : DistC} (h₁ : D g₁ ∈ LocalEvent.lenSet) (h₂ : D g₂ ∈ LocalEvent.lenSet)
    (heq : (D g₁).internal (interior S) = (D g₂).internal (interior S))
    (hS : dyadicHull n (gmKt D 𝕫 R c g₁) = S) (hτ : 0 < tauD (D g₁) 𝕫 R) :
    tauD (D g₂) 𝕫 R = tauD (D g₁) 𝕫 R ∧
      GMLocData (D g₁) (D g₂) 𝕫 (tauD (D g₁) 𝕫 R * c) (interior S) ∧
      dyadicHull n (gmKt D 𝕫 R c g₂) = S := by
  have hKU : gmKt D 𝕫 R c g₁ ⊆ interior S := hS ▸ LocalEvent.subset_interior_dyadicHull n _
  obtain ⟨hτe, H⟩ := gm_locData_tk (LocalEvent.isLength_of_mem_lenSet h₁)
    (LocalEvent.isLength_of_mem_lenSet h₂) hc isOpen_interior heq hτ hKU
  refine ⟨hτe, H, ?_⟩
  have : gmKt D 𝕫 R c g₂ = gmKt D 𝕫 R c g₁ := by
    simp only [gmKt]
    rw [hτe]
    exact H.filledBall_eq le_rfl
  rw [this, hS]

/-- **events of the field invariant under the locality data at `t_k` are
`σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`-events** (GM l. 1654, Axiom II) -/
theorem gm_aeEventIn_Kt {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hgp : IsGFFPlusCont h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ LocalEvent.lenSet) (𝕫 : ℂ) {R c : ℝ} (hR : 0 < R) (hc : 1 < c)
    {B : Set DistC}
    (hnull : ∀ (n : ℕ) (s : Finset (ℤ × ℤ)), NullMeasurableSet
      (B ∩ {g | dyadicHull n (gmKt D 𝕫 R c g) = LocalEvent.hullFin n s}) (P.map h))
    (hsat : ∀ (g₁ g₂ : DistC) (U : Set ℂ), D g₁ ∈ LocalEvent.lenSet →
      D g₂ ∈ LocalEvent.lenSet → tauD (D g₂) 𝕫 R = tauD (D g₁) 𝕫 R →
      GMLocData (D g₁) (D g₂) 𝕫 (tauD (D g₁) 𝕫 R * c) U → g₁ ∈ B → g₂ ∈ B) :
    AEEventIn P (localSigma h (fun ω => gmKt D 𝕫 R c (h ω))) (h ⁻¹' B) := by
  have hb : ∀ᵐ ω ∂P, Bornology.IsBounded (gmKt D 𝕫 R c (h ω)) := by
    filter_upwards [hlen] with ω hω using gm_filledBall_isBounded_of_lenSet hω _ _
  exact LocalEvent.aeEventIn_localSigma_of_saturated hD P h hgp hlen
    (gmKt D 𝕫 R c) (fun g => gm_filledBall_isClosed _ _ _) hb hnull (by
      rintro n s g₁ g₂ h1 h2 heq hS hB
      obtain ⟨hτe, H, hS₂⟩ := gm_hullSat_Kt hc h1 h2 heq hS (gm_tauD_pos _ 𝕫 hR)
      exact ⟨hS₂, hsat g₁ g₂ _ h1 h2 hτe H hB⟩)

end LQGMetric.GM
