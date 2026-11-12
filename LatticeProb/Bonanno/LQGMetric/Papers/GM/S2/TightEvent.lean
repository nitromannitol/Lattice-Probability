/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# GM S2.4e, the annulus events for LM Lemma 3.1 (task P2-TIGHT)

Decision D-A3 (`decisions/DEC-A.md` (c), S2.4e): "Each crossing is `≥ a 𝔠_{8^k r} e^{ξ h_{8^k r}(z)}`
with probability `≥ p` (S2.4a). The events are determined by `(h − h_{8^k r}(z))` on
`𝔸_{8^k r/8, 8^k r/2}(z)`, via S3.1, locality and Weyl for constants." LM Lemma 3.1
(`Blueprint.LMLem3_1a`, hypothesis `AnnulusIterHyp`) needs events that are *measurable* w.r.t.
`σ((h − h_ρ(0))|_{𝔸_{ρ/8, ρ/2}(0)})`.

`exists_crossing_event`: for every `ε > 0` there is `s > 0` such that for every whole-plane GFF
`h` and `ρ > 0` there is an event `E`, measurable w.r.t. that σ-algebra, with `P[Eᶜ] < ε`, on
which a.s. `D_h(u, v; 𝔸_{ρ/8, ρ/2}(0)) ≥ s 𝔠_ρ e^{ξ h_ρ(0)}` for all `u ∈ ∂B_{ρ/4}(0)`,
`v ∈ ∂B_{3ρ/8}(0)`.

Construction: `E = {F((h − h_ρ(0))|_U)(u, v) ≥ s 𝔠_ρ for u, v in countable dense subsets of the
two circles}`, `F` the locality functional of Axiom II for the field `h − h_ρ(0)`; Weyl scaling
for constants (`IsWeakLQGMetric.ae_internal_addFun_of_eq_const`) converts to `D_h`; continuity
of internal metrics (LM Lemma 1.1, `ContMetric.continuousOn_internal`) passes from the dense sets
to the circles; `P[Eᶜ] < ε` from S2.4a (`gm_S2_4a`) and `D ≤ D(·,·;U)`. Own argument (D-A3;
DEVIATIONS DA5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

open Blueprint

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

lemma exists_countable_dense_sphere (R : ℝ) :
    ∃ C : Set ℂ, C.Countable ∧ C ⊆ sphere 0 R ∧ sphere 0 R ⊆ closure C := by
  obtain ⟨C', hC'c, hC'd⟩ := TopologicalSpace.exists_countable_dense (sphere (0 : ℂ) R)
  refine ⟨Subtype.val '' C', hC'c.image _, fun _ ⟨u, _, hu⟩ => hu ▸ u.2, fun u hu => ?_⟩
  have : (⟨u, hu⟩ : sphere (0 : ℂ) R) ∈ closure C' := by rw [hC'd.closure_eq]; trivial
  exact image_closure_subset_closure_image continuous_subtype_val ⟨_, this, rfl⟩

/-- **Measurable annulus-crossing events** for LM Lemma 3.1 (S2.4e input). -/
theorem exists_crossing_event (hD : IsWeakLQGMetric γ D c) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ ρ : ℝ, 0 < ρ → ∃ E : Set Ω,
      MeasurableSet[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ 0))
        (annulus 0 (1 / 8 * ρ) (1 / 2 * ρ))] E ∧ P Eᶜ < ε ∧
      ∀ᵐ ω ∂P, ω ∈ E → ∀ u ∈ sphere (0 : ℂ) (ρ / 4), ∀ v ∈ sphere (0 : ℂ) (3 * ρ / 8),
        ENNReal.ofReal (s * c ρ * Real.exp (xiGamma γ * circleAvg (h ω) ρ 0)) ≤
          (D (h ω)).internal (annulus 0 (1 / 8 * ρ) (1 / 2 * ρ)) u v := by
  have hdisj : Disjoint (sphere (0 : ℂ) (1 / 4)) (sphere (0 : ℂ) (3 / 8)) :=
    disjoint_left.2 fun u h1 h2 => by
      rw [mem_sphere] at h1 h2
      linarith
  obtain ⟨s, hs, HA⟩ := gm_S2_4a hD (isCompact_sphere 0 (1 / 4)) (isCompact_sphere 0 (3 / 8))
    hdisj hε
  refine ⟨s, hs, ?_⟩
  intro Ω _ P _ h hh ρ hρ
  set U : TopologicalSpace.Opens ℂ := annulus 0 (1 / 8 * ρ) (1 / 2 * ρ) with hU
  have hmeasA := measurable_circleAvg_left ρ 0
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) ρ 0) with hgdef
  have hg : IsWholePlaneGFF g P := hh.addConst (hmeasA.comp hh.measurable).neg
  obtain ⟨F, hFm, hF⟩ := hD.locality P g (isGFFPlusCont_of_wp hg) U
  obtain ⟨C₁, hC₁c, hC₁s, hC₁d⟩ := exists_countable_dense_sphere (ρ / 4)
  obtain ⟨C₂, hC₂c, hC₂s, hC₂d⟩ := exists_countable_dense_sphere (3 * ρ / 8)
  have hsU₁ : sphere (0 : ℂ) (ρ / 4) ⊆ U := fun u hu => by
    have := mem_sphere.1 hu
    rw [dist_zero_right] at this
    show 1 / 8 * ρ < ‖u - 0‖ ∧ ‖u - 0‖ < 1 / 2 * ρ
    rw [sub_zero, this]; constructor <;> linarith
  have hsU₂ : sphere (0 : ℂ) (3 * ρ / 8) ⊆ U := fun u hu => by
    have := mem_sphere.1 hu
    rw [dist_zero_right] at this
    show 1 / 8 * ρ < ‖u - 0‖ ∧ ‖u - 0‖ < 1 / 2 * ρ
    rw [sub_zero, this]; constructor <;> linarith
  set T : Set (DistOn U) :=
    {T | ∀ u ∈ C₁, ∀ v ∈ C₂, ENNReal.ofReal (s * c ρ) ≤ F T u v} with hT
  have hTm : MeasurableSet T := by
    have : T = ⋂ u ∈ C₁, ⋂ v ∈ C₂, {T | ENNReal.ofReal (s * c ρ) ≤ F T u v} := by
      ext; simp [hT]
    rw [this]
    exact MeasurableSet.biInter hC₁c fun u _ => MeasurableSet.biInter hC₂c fun v _ =>
      measurableSet_le measurable_const ((measurable_pi_apply v).comp
        ((measurable_pi_apply u).comp hFm))
  have hW := hD.ae_internal_addFun_of_eq_const (isGFFPlusCont_of_wp hh)
  have hlen := hD.length P h (isGFFPlusCont_of_wp hh)
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hscale : ∀ {R : ℝ} {u : ℂ}, u ∈ sphere (0 : ℂ) (ρ * R) → u / ρ ∈ sphere (0 : ℂ) R ∧
      (ρ : ℂ) * (u / ρ) + 0 = u := fun {R u} hu => by
    refine ⟨?_, by field_simp; ring⟩
    rw [mem_sphere, dist_zero_right] at hu ⊢
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hu]
    field_simp
  have hs4 : ∀ u, u ∈ sphere (0 : ℂ) (ρ / 4) → u ∈ sphere (0 : ℂ) (ρ * (1 / 4)) := fun u hu => by
    rwa [show ρ * (1 / 4) = ρ / 4 by ring]
  have hs8 : ∀ u, u ∈ sphere (0 : ℂ) (3 * ρ / 8) → u ∈ sphere (0 : ℂ) (ρ * (3 / 8)) :=
    fun u hu => by rwa [show ρ * (3 / 8) = 3 * ρ / 8 by ring]
  have hexp : ∀ a : ℝ, Real.exp (xiGamma γ * a) * Real.exp (xiGamma γ * -a) = 1 := fun a => by
    rw [← Real.exp_add]; simp
  refine ⟨(fun ω => restrictTo U (g ω)) ⁻¹' T, MeasurableSpace.measurableSet_comap.2
    ⟨T, hTm, rfl⟩, ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_mono_ae ?_) (HA P h hh ρ hρ 0)
    filter_upwards [hF, hW] with ω hFω hWω hω hgood
    apply hω
    intro u hu v hv
    set a := circleAvg (h ω) ρ 0 with ha
    rw [← hFω u (hsU₁ (hC₁s hu)) v (hsU₂ (hC₂s hv)),
      show g ω = addFun (h ω) (ContinuousMap.const ℂ (-a)) from rfl,
      hWω (ContinuousMap.const ℂ (-a)) U (xiGamma γ * -a) U.isOpen (fun x _ => rfl) u v]
    obtain ⟨hu', hu''⟩ := hscale (hs4 u (hC₁s hu))
    obtain ⟨hv', hv''⟩ := hscale (hs8 v (hC₂s hv))
    have h1 := hgood (u / ρ) hu' (v / ρ) hv'
    rw [hu'', hv''] at h1
    have h2 : ENNReal.ofReal ((D (h ω)).1 (u, v)) ≤ (D (h ω)).internal U u v := by
      have := MetricGeometry.edist_le_internalEDist ((D (h ω)).pt '' (U : Set ℂ))
        ((D (h ω)).pt u) ((D (h ω)).pt v)
      rwa [edist_dist] at this
    calc ENNReal.ofReal (s * c ρ)
        = ENNReal.ofReal (Real.exp (xiGamma γ * -a)) *
            ENNReal.ofReal (s * c ρ * Real.exp (xiGamma γ * a)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [show Real.exp (xiGamma γ * -a) * (s * c ρ * Real.exp (xiGamma γ * a)) =
            s * c ρ * (Real.exp (xiGamma γ * a) * Real.exp (xiGamma γ * -a)) by ring, hexp, mul_one]
      _ ≤ ENNReal.ofReal (Real.exp (xiGamma γ * -a)) * (D (h ω)).internal U u v :=
          by gcongr; exact (ENNReal.ofReal_le_ofReal h1.le).trans h2
  · filter_upwards [hF, hW, hlen] with ω hFω hWω hlω hE u hu v hv
    set a := circleAvg (h ω) ρ 0 with ha
    have hdense : ∀ p ∈ C₁ ×ˢ C₂,
        ENNReal.ofReal (s * c ρ * Real.exp (xiGamma γ * a)) ≤
          (D (h ω)).internal U p.1 p.2 := by
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      have := hE u hu v hv
      rw [← hFω u (hsU₁ (hC₁s hu)) v (hsU₂ (hC₂s hv)),
        show g ω = addFun (h ω) (ContinuousMap.const ℂ (-a)) from rfl,
        hWω (ContinuousMap.const ℂ (-a)) U (xiGamma γ * -a) U.isOpen (fun x _ => rfl) u v] at this
      calc ENNReal.ofReal (s * c ρ * Real.exp (xiGamma γ * a))
          = ENNReal.ofReal (Real.exp (xiGamma γ * a)) * ENNReal.ofReal (s * c ρ) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; ring_nf
        _ ≤ ENNReal.ofReal (Real.exp (xiGamma γ * a)) *
            (ENNReal.ofReal (Real.exp (xiGamma γ * -a)) * (D (h ω)).internal U u v) :=
            by gcongr
        _ = (D (h ω)).internal U u v := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hexp,
              ENNReal.ofReal_one, one_mul]
    have hcl : closure (C₁ ×ˢ C₂) ⊆ (U : Set ℂ) ×ˢ (U : Set ℂ) := by
      rw [closure_prod_eq]
      exact prod_mono ((closure_minimal hC₁s isClosed_sphere).trans hsU₁)
        ((closure_minimal hC₂s isClosed_sphere).trans hsU₂)
    exact le_on_closure (f := fun _ => ENNReal.ofReal (s * c ρ * Real.exp (xiGamma γ * a)))
      (g := fun p : ℂ × ℂ => (D (h ω)).internal U p.1 p.2) hdense continuousOn_const
      ((ContMetric.continuousOn_internal _ hlω U.isOpen).mono hcl)
      (x := (u, v)) (by rw [closure_prod_eq]; exact ⟨hC₁d hu, hC₂d hv⟩)

end Tight
end GM
end LQGMetric
