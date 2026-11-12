/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.LocEquiv at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocCI
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsLM

/-!
# LM Lemma 2.3 (`lem-local-equiv`): the three forms of locality (task P2-LMLOC)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 2.3, l. 523–531, proof l. 532–549. Forms, for every open `V`:
(1) `D(·,·;V) ⟂ (h|_{ℂ∖V}, D(·,·;ℂ∖V̄)) | h|_V` (Def 1.2, `IsLocalMetric`);
(2) `D(·,·;V) ⟂ (h, D(·,·;ℂ∖V̄)) | h|_V` (`LocForm2`);
(3) `D(·,·;V) ⟂ (h, D(·,·;ℂ∖V̄)) | h|_{V̄}` (`LocForm3`).

Proved here, following LM's proof:
* `isLocalMetric_of_form2` — (2) ⟹ (1) (`σ(h|_{ℂ∖V}) ⊆ σ(h)`).
* `locForm3_of_form2` — (2) ⟹ (3), LM l. 535–536 (the probability fact there is weak union,
  `DFGPS.L219.condIndepEv_transfer`, since `σ(h|_V) ⊆ σ(h|_{V̄}) ⊆ σ(h)`).
* `locForm2_of_isLocal` — (1) ⟹ (2), LM l. 534 ("since `h` is determined by `h|_V` and
  `h|_{U∖V}`"), from that fact, stated as `LocGermSplit`.
* `locForm2_of_form3` — (3) ⟹ (2), LM l. 538–548: for `W_n = {z : d(z, ℂ∖V) > 1/(n+1)}` (so
  `W̄_n ⊆ V`), (3) at `W_n` gives `D(·,·;W_n) ⟂ (h, D(·,·;ℂ∖V̄)) | h|_V`, using LM l. 545 ("the
  metric `D(·,·;U∖V̄)` … is determined by `D(·,·;U∖W̄)`"), stated as `LocInternalNest`; then
  "letting `W` increase to all of `V`" (`condIndepEv_iSup_of_monotone`, with
  `D(u,v;V) = inf_n D(u,v;W_n)`, `internal_eq_iInf_exhaust`).
* `lmLem2_3_of` — `Blueprint.LMLem2_3` from `LocGermSplit` and `LocInternalNest`.

The two inputs are the facts LM use without proof (l. 534 and l. 545); both are reported as
open nodes (handoff/P2-LMLOC.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

/-- **LM l. 545** ("`D(·,·;U∖V̄)` is equal to the internal metric of `D(·,·;U∖W̄)` on `U∖V̄`, so is
determined by `D(·,·;U∖W̄)`"), up to null events: for `W₁ ⊆ W₂` open and an a.s. length metric,
`σ(D(·,·;W₁)) ⊆ σ(D(·,·;W₂))` modulo null events. (The identity of metrics is
`MetricGeometry.internalEDist_internalSpace`; the missing part is measurability.) -/
def LocInternalNest : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ContMetric), Measurable D →
    (∀ᵐ ω ∂P, (D ω).IsLength) → ∀ W₁ W₂ : Set ℂ, IsOpen W₁ → IsOpen W₂ → W₁ ⊆ W₂ →
      famSigma (internalFam D) W₁ ≤ aeClosure P (famSigma (internalFam D) W₂)

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- LM Lemma 2.3, form (2) at `V` -/
def LocForm2 (P : Measure Ω) (h : Ω → DistC) (D : Ω → ContMetric)
    (V : TopologicalSpace.Opens ℂ) : Prop :=
  CondIndepEv (fieldSigma h V) (famSigma (internalFam D) V)
    (MeasurableSpace.comap h inferInstance ⊔ famSigma (internalFam D) (closure (V : Set ℂ))ᶜ) P

/-- LM Lemma 2.3, form (3) at `V` -/
def LocForm3 (P : Measure Ω) (h : Ω → DistC) (D : Ω → ContMetric)
    (V : TopologicalSpace.Opens ℂ) : Prop :=
  CondIndepEv (fieldSigmaClosed h (closure (V : Set ℂ))) (famSigma (internalFam D) V)
    (MeasurableSpace.comap h inferInstance ⊔ famSigma (internalFam D) (closure (V : Set ℂ))ᶜ) P

omit mΩ in
theorem fieldSigma_le_comapH (h : Ω → DistC) (V : TopologicalSpace.Opens ℂ) :
    fieldSigma h V ≤ MeasurableSpace.comap h inferInstance :=
  ((measurable_restrictTo V).comp (comap_measurable h)).comap_le

omit mΩ in
theorem fieldSigmaClosed_le_comapH (h : Ω → DistC) (K : Set ℂ) :
    fieldSigmaClosed h K ≤ MeasurableSpace.comap h inferInstance :=
  (iInf₂_le (1 : ℝ) one_pos).trans (fieldSigma_le_comapH h _)

theorem le_aeClosure_trans {X Y Z : MeasurableSpace Ω} (h1 : X ≤ aeClosure P Y)
    (h2 : Y ≤ aeClosure P Z) : X ≤ aeClosure P Z :=
  h1.trans ((aeClosure_mono h2).trans (aeClosure_aeClosure_le Z))

/-- **(2) ⟹ (1)** -/
theorem isLocalMetric_of_form2 {h : Ω → DistC} {D : Ω → ContMetric} (hD : Measurable D)
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (h2 : ∀ V, LocForm2 P h D V) : IsLocalMetric P h D :=
  ⟨hD, hlen, fun V => (h2 V).mono le_rfl (sup_le_sup_right (fieldSigmaClosed_le_comapH h _) _)⟩

variable [IsProbabilityMeasure P]

/-- **(2) ⟹ (3)** (LM l. 535–536) -/
theorem locForm3_of_form2 {h : Ω → DistC} {D : Ω → ContMetric} (hm : Measurable h)
    (hD : Measurable D) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (V : TopologicalSpace.Opens ℂ)
    (h2 : LocForm2 P h D V) : LocForm3 P h D V := by
  have hV := V.isOpen
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have h2' : CondIndepEv (fieldSigma h V) (chainSigma D V)
      (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ) P :=
    GM.Bilip.CondIndepEv.of_le_aeClosure h2 (chainSigma_le_famSigma hlen hV)
      (sup_le (le_sup_left.trans (le_aeClosure _))
        ((chainSigma_le_famSigma hlen hW).trans (aeClosure_mono le_sup_right)))
  refine condIndepEv_transfer (fieldSigma_le hm V) (chainSigma_le hD _)
    (sup_le hm.comap_le (chainSigma_le hD _)) (fieldSigmaClosed_le hm _) h2' ?_ ?_ ?_ ?_
  · exact (le_iInf₂ fun δ hδ => GM.fieldSigma_mono h
      (fun x hx => self_subset_thickening hδ _ (subset_closure hx))).trans (le_aeClosure _)
  · exact ((fieldSigmaClosed_le_comapH h _).trans (le_sup_left.trans le_sup_left)).trans
      (le_aeClosure _)
  · exact (famSigma_le_chainSigma hlen hV).trans (aeClosure_mono le_sup_left)
  · exact sup_le ((le_sup_left.trans le_sup_left).trans (le_aeClosure _))
      ((famSigma_le_chainSigma hlen hW).trans (aeClosure_mono (le_sup_right.trans le_sup_left)))

/-! ### (3) ⟹ (2): the exhaustion `W_n ↑ V` -/

/-- `W_n = {z : d(z, ℂ∖V) > 1/(n+1)}` -/
def exhaustO (V : Set ℂ) (n : ℕ) : TopologicalSpace.Opens ℂ :=
  ⟨{z | 1 / ((n : ℝ) + 1) < infDist z Vᶜ}, isOpen_lt continuous_const (continuous_infDist_pt _)⟩

theorem exhaustO_subset (V : Set ℂ) (n : ℕ) : (exhaustO V n : Set ℂ) ⊆ V := by
  intro z hz
  by_contra hzV
  have h0 : infDist z Vᶜ = 0 := infDist_zero_of_mem hzV
  have hz' : 1 / ((n : ℝ) + 1) < infDist z Vᶜ := hz
  rw [h0] at hz'
  exact absurd hz' (not_lt.2 (by positivity))

theorem exhaustO_mono (V : Set ℂ) {m n : ℕ} (hmn : m ≤ n) :
    (exhaustO V m : Set ℂ) ⊆ exhaustO V n := by
  intro z hz
  have hz' : 1 / ((m : ℝ) + 1) < infDist z Vᶜ := hz
  show 1 / ((n : ℝ) + 1) < infDist z Vᶜ
  refine lt_of_le_of_lt ?_ hz'
  gcongr

theorem thickening_closure_exhaustO_subset (V : Set ℂ) (n : ℕ) :
    thickening (1 / (2 * ((n : ℝ) + 1))) (closure (exhaustO V n : Set ℂ)) ⊆ V := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  have hcl : closure (exhaustO V n : Set ℂ) ⊆ {z | 1 / ((n : ℝ) + 1) ≤ infDist z Vᶜ} :=
    closure_minimal (fun z (hz : 1 / ((n : ℝ) + 1) < infDist z Vᶜ) => (le_of_lt hz : _))
      (isClosed_le continuous_const (continuous_infDist_pt _))
  have hz1 : 1 / ((n : ℝ) + 1) ≤ infDist z Vᶜ := hcl hz
  have htri : infDist z Vᶜ ≤ infDist y Vᶜ + dist z y := infDist_le_infDist_add_dist
  by_contra hyV
  have h0 : infDist y Vᶜ = 0 := infDist_zero_of_mem hyV
  rw [dist_comm] at htri
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have e : 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1))) := by field_simp
  have hε : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  linarith

/-- `D(u,v;V) = inf_n D(u,v;W_n)`: every path in `V` has compact range, hence lies in some
`W_n` (as in `DFGPS.L217.internal_eq_iInf_dyadicC`) -/
theorem internal_eq_iInf_exhaust (D : ContMetric) {V : Set ℂ} (hV : IsOpen V) (hne : Vᶜ.Nonempty)
    (u v : ℂ) : D.internal V u v = ⨅ n : ℕ, D.internal (exhaustO V n) u v := by
  refine le_antisymm (le_iInf fun n =>
    MetricGeometry.internalEDist_anti (image_mono (exhaustO_subset V n)) _ _) ?_
  unfold ContMetric.internal MetricGeometry.internalEDist
  refine le_iInf fun γ => ?_
  set K : Set ℂ := range (D.unpt ∘ γ.1)
  have hKc : IsCompact K := isCompact_range (D.continuous_unpt.comp γ.1.continuous)
  have hKV : K ⊆ V := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy, hyt⟩ := γ.2 t
    simp only [Function.comp_apply, ← hyt, ContMetric.unpt_pt]
    exact hy
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_thickening_subset_open hV hKV
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hKW : K ⊆ exhaustO V n := by
    intro z hz
    show 1 / ((n : ℝ) + 1) < infDist z Vᶜ
    refine hn.trans_le ((le_infDist hne).2 fun y hy => le_of_not_gt fun hlt => hy ?_)
    exact hδV (mem_thickening_iff.2 ⟨z, hz, by rw [dist_comm]; exact hlt⟩)
  refine iInf_le_of_le n (iInf_le_of_le ⟨γ.1, fun t => ⟨D.unpt (γ.1 t),
    hKW ⟨t, rfl⟩, ContMetric.pt_unpt _ _⟩⟩ le_rfl)

omit mΩ in
theorem measurable_of_eq_iInf {Ω' : Type} [MeasurableSpace Ω'] (f : Ω' → ℂ → ℂ → ℝ≥0∞)
    (g : ℕ → Ω' → ℂ → ℂ → ℝ≥0∞) (hg : ∀ n, Measurable (g n))
    (hfg : ∀ ω u v, f ω u v = ⨅ n, g n ω u v) : Measurable f := by
  refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
  have e : (fun ω => f ω u v) = fun ω => ⨅ n, g n ω u v := funext fun ω => hfg ω u v
  rw [e]
  exact Measurable.iInf fun n => (measurable_pi_apply v).comp ((measurable_pi_apply u).comp (hg n))

theorem famSigma_le_iSup_exhaust (D : Ω → ContMetric) {V : Set ℂ} (hV : IsOpen V)
    (hne : Vᶜ.Nonempty) :
    famSigma (internalFam D) V ≤ ⨆ n : ℕ, famSigma (internalFam D) (exhaustO V n) :=
  Measurable.comap_le (@measurable_of_eq_iInf Ω (⨆ n : ℕ, famSigma (internalFam D) (exhaustO V n))
    (fun ω => internalFam D ω V) (fun n ω => internalFam D ω (exhaustO V n))
    (fun n => (comap_measurable (fun ω => internalFam D ω (exhaustO V n))).mono
      (le_iSup (fun m => famSigma (internalFam D) (exhaustO V m)) n) le_rfl)
    (fun ω u v => internal_eq_iInf_exhaust (D ω) hV hne u v))

/-- `⋁_{k ≤ n} σ(D(·,·;W_k))` (Borel versions) -/
def exhaustSigma (D : Ω → ContMetric) (V : Set ℂ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ (k : ℕ) (_ : k ≤ n), chainSigma D (exhaustO V k)

/-- **(3) ⟹ (2)** (LM l. 538–548), from `LocInternalNest` -/
theorem locForm2_of_form3 (hnest : LocInternalNest) {h : Ω → DistC} {D : Ω → ContMetric}
    (hm : Measurable h) (hD : Measurable D) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (h3 : ∀ V, LocForm3 P h D V) (V : TopologicalSpace.Opens ℂ) : LocForm2 P h D V := by
  have hV := V.isOpen
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have hB'le : MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ ≤ mΩ :=
    sup_le hm.comap_le (chainSigma_le hD _)
  have hBB' : MeasurableSpace.comap h inferInstance ⊔ famSigma (internalFam D) (closure (V : Set ℂ))ᶜ ≤
      aeClosure P (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ) :=
    sup_le (le_sup_left.trans (le_aeClosure _))
      ((famSigma_le_chainSigma hlen hW).trans (aeClosure_mono le_sup_right))
  -- the chain form of (3) at an open set `U`
  have h3c : ∀ U : TopologicalSpace.Opens ℂ, CondIndepEv (fieldSigmaClosed h (closure (U : Set ℂ)))
      (chainSigma D U)
      (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (U : Set ℂ))ᶜ) P := fun U =>
    GM.Bilip.CondIndepEv.of_le_aeClosure (h3 U) (chainSigma_le_famSigma hlen U.isOpen)
      (sup_le (le_sup_left.trans (le_aeClosure _))
        ((chainSigma_le_famSigma hlen isClosed_closure.isOpen_compl).trans
          (aeClosure_mono le_sup_right)))
  by_cases hVu : (V : Set ℂ) = univ
  · -- `V = ℂ`: `σ(h|_{V̄}) ⊆ σ(h|_V)`
    refine GM.Bilip.CondIndepEv.of_le_aeClosure (condIndepEv_transfer (fieldSigmaClosed_le hm _)
      (chainSigma_le hD _) hB'le (fieldSigma_le hm V) (h3c V) ?_ ?_ ?_ (le_sup_left.trans
        (le_aeClosure _))) (famSigma_le_chainSigma hlen hV |>.trans (aeClosure_mono le_rfl)) hBB'
    · refine ((iInf₂_le (1 : ℝ) one_pos).trans (GM.fieldSigma_mono h fun x _ => ?_)).trans
        (le_aeClosure _)
      show x ∈ (V : Set ℂ)
      rw [hVu]; trivial
    · exact ((fieldSigma_le_comapH h V).trans (le_sup_left.trans le_sup_left)).trans
        (le_aeClosure _)
    · exact (le_sup_left).trans (le_aeClosure _)
  have hne : (V : Set ℂ)ᶜ.Nonempty := by
    rw [nonempty_compl]; exact hVu
  -- (3) at `W_n`, transferred to conditioning on `h|_V`
  have hstep : ∀ n, CondIndepEv (fieldSigma h V) (chainSigma D (exhaustO V n))
      (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ) P := by
    intro n
    have hsub : (closure (V : Set ℂ))ᶜ ⊆ (closure (exhaustO V n : Set ℂ))ᶜ :=
      compl_subset_compl.2 (closure_mono (exhaustO_subset V n))
    have hε : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    refine condIndepEv_transfer (fieldSigmaClosed_le hm _) (chainSigma_le hD _)
      (sup_le hm.comap_le (chainSigma_le hD _)) (fieldSigma_le hm V) (h3c (exhaustO V n)) ?_ ?_
      (le_sup_left.trans (le_aeClosure _)) ?_
    · exact ((iInf₂_le _ hε).trans (GM.fieldSigma_mono h
        (thickening_closure_exhaustO_subset V n))).trans (le_aeClosure _)
    · exact ((fieldSigma_le_comapH h V).trans (le_sup_left.trans le_sup_left)).trans
        (le_aeClosure _)
    · refine sup_le ((le_sup_left.trans le_sup_left).trans (le_aeClosure _)) ?_
      refine le_aeClosure_trans (chainSigma_le_famSigma hlen hW) (le_aeClosure_trans
        (hnest P D hD hlen _ _ hW isClosed_closure.isOpen_compl hsub) ?_)
      exact (famSigma_le_chainSigma hlen isClosed_closure.isOpen_compl).trans
        (aeClosure_mono (le_sup_right.trans le_sup_left))
  -- the increasing family `A_n = ⋁_{k ≤ n} σ(D(·,·;W_k))`
  have hAle : ∀ n, exhaustSigma D V n ≤ mΩ := fun n => iSup₂_le fun k _ => chainSigma_le hD _
  have hAmono : Monotone (exhaustSigma D V) := fun m n hmn =>
    iSup₂_le fun k hk => le_iSup₂_of_le (f := fun k (_ : k ≤ n) => chainSigma D (exhaustO V k)) k
      (hk.trans hmn) le_rfl
  have hAae : ∀ n, exhaustSigma D V n ≤ aeClosure P (chainSigma D (exhaustO V n)) := fun n =>
    iSup₂_le fun k hk => le_aeClosure_trans (chainSigma_le_famSigma hlen (exhaustO V k).isOpen)
      (le_aeClosure_trans (hnest P D hD hlen _ _ (exhaustO V k).isOpen (exhaustO V n).isOpen
        (exhaustO_mono V hk)) (famSigma_le_chainSigma hlen (exhaustO V n).isOpen))
  have hAci : ∀ n, CondIndepEv (fieldSigma h V) (exhaustSigma D V n)
      (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ) P := fun n =>
    GM.Bilip.CondIndepEv.of_le_aeClosure (hstep n) (hAae n) (le_aeClosure _)
  have hlim := condIndepEv_iSup_of_monotone (fieldSigma_le hm V) hAle hB'le hAmono hAci
  refine GM.Bilip.CondIndepEv.of_le_aeClosure hlim ?_ hBB'
  refine (famSigma_le_iSup_exhaust D hV hne).trans (iSup_le fun n => ?_)
  exact (famSigma_le_chainSigma hlen (exhaustO V n).isOpen).trans (aeClosure_mono
    ((le_iSup₂ (f := fun k (_ : k ≤ n) => chainSigma D (exhaustO V k)) n le_rfl).trans (le_iSup (exhaustSigma D V) n)))

end LQGMetric.LM
