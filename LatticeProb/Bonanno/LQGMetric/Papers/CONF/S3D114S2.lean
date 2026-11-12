/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114S2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114S1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114NA
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3EMeas
import LatticeProb.Bonanno.LQGMetric.Field.HarmLocD

/-!
# CONF Lemma 3.6, Step 3: `Conf36StepNodeD` from (3.25)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Step 3 of Lemma 3.6 (C:1425–1447); decision D114
§4 packet C2.

* `conf36Conn_of_preconnected`, `conf36_ae_conn`: the connectivity conjunct of `G̃^{n+1}` holds
  a.s. (DEC-114 §1(d), CONF C:1393: `𝓑^•_τ` is connected for a length metric,
  `jp_isPreconnected_filledBall`, and contains `x` with `|x − z| < ε𝕣/2`);
* `conf36_confEU_nullMeas`: `E^U_r(z)` is null-measurable (`GM.p412j_confEU`, Axiom II and the
  locality of the harmonic part `HarmLoc.p412jHarmLoc`);
* `Conf36Eq325`: CONF (3.25) (C:1433–1437): on each piece `{ε𝕣 = 𝔢, z = 𝔷, ρ̃^{n+1} = 𝔯, T = 𝔗}`
  of Step 3, the event `A ∩ ⋂_{m ≤ n'} (G̃^m)ᶜ` (`n' ≤ n`) is a.s. `B' ∩ E^𝔘_𝔯(𝔷)` with
  `B' ∈ σ((h − h_𝔯(𝔷))|_{ℂ∖𝔘})`;
* `conf36StepNodeD_of_eq325`: `Conf36StepNodeD γ D c p Fat` from `Conf36Eq325 γ D c p Fat`
  (summation `conf36_step_of_pieces`, S3D114S1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- a preconnected set with a closure point in `B_{3r}(z)` meets `𝔸_{3r,4r}(z)` or lies in
`cl B_{3r}(z)` -/
theorem conf36Conn_of_preconnected {B : Set ℂ} (hB : IsPreconnected B) {x z : ℂ} {r : ℝ}
    (hx : x ∈ closure B) (hxz : ‖x - z‖ < 3 * r) : conf36Conn B r z := by
  by_cases hsub : B ⊆ closedBall z (3 * r)
  · exact Or.inr hsub
  left
  obtain ⟨y, hyB, hy⟩ := not_subset.1 hsub
  rw [mem_closedBall, dist_eq_norm, not_le] at hy
  obtain ⟨w, hwB, hw⟩ := Metric.mem_closure_iff.1 hx (3 * r - ‖x - z‖) (by linarith)
  rw [dist_eq_norm] at hw
  have hwz : ‖w - z‖ < 3 * r := by
    have : ‖w - z‖ ≤ ‖x - w‖ + ‖x - z‖ := by
      calc ‖w - z‖ = ‖(x - z) - (x - w)‖ := by congr 1; ring
        _ ≤ ‖x - z‖ + ‖x - w‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  have hr : 0 < r := by linarith [norm_nonneg (w - z)]
  set f : ℂ → ℝ := fun u => ‖u - z‖
  have hf : Continuous f := (continuous_id.sub continuous_const).norm
  have hI := (hB.image f hf.continuousOn).Icc_subset (mem_image_of_mem f hwB)
    (mem_image_of_mem f hyB)
  set t := (3 * r + min (f y) (4 * r)) / 2
  have hm : 3 * r < min (f y) (4 * r) := lt_min hy (by linarith)
  have ht : t = (3 * r + min (f y) (4 * r)) / 2 := rfl
  have hfw : f w < 3 * r := hwz
  obtain ⟨u, huB, hu⟩ := hI ⟨by linarith [min_le_left (f y) (4 * r)],
    by linarith [min_le_left (f y) (4 * r)]⟩
  refine ⟨u, huB, ?_⟩
  show 3 * r < ‖u - z‖ ∧ ‖u - z‖ < 4 * r
  have : ‖u - z‖ = t := hu
  rw [this]
  constructor <;> linarith [min_le_right (f y) (4 * r)]

section Random
variable {Ω : Type} [MeasurableSpace Ω]

/-- the connectivity conjunct holds a.s. for every radius `r ≥ ε𝕣` -/
theorem conf36_ae_conn {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {z₀ : ℂ} {τ : Ω → ℝ} {x : Ω → ℂ} {e : Ω → ℝ} (he : ∀ ω, 0 < e ω)
    (hx : ∀ᵐ ω ∂P, x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω))) :
    ∀ᵐ ω ∂P, ∀ r, e ω ≤ r →
      conf36Conn (filledBall (D (h ω)) z₀ (τ ω)) r (conf36Grid (e ω / 4) (x ω)) := by
  filter_upwards [hx, hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh)] with ω hxω hL r hr
  have hcl : x ω ∈ closure (filledBall (D (h ω)) z₀ (τ ω)) :=
    subset_closure (subset_union_left (conf36_frontier_filledBall_subset _ _ _ hxω))
  have hτ : 0 < τ ω :=
    conf36_pos_of_mem_filledBall (subset_union_left (conf36_frontier_filledBall_subset _ _ _ hxω))
  refine conf36Conn_of_preconnected (GM.jp_isPreconnected_filledBall hτ hL) hcl ?_
  have := conf36Grid_norm_lt (by linarith [he ω] : 0 < e ω / 4) (x ω)
  linarith [he ω]

omit [MeasurableSpace Ω] in
theorem conf36_range_grid_countable {m : Ω → ℝ} (hm : (range m).Countable) (x : Ω → ℂ) :
    (range fun ω => conf36Grid (m ω) (x ω)).Countable := by
  have hsub : (range fun ω => conf36Grid (m ω) (x ω)) ⊆
      (fun q : ℝ × ℤ × ℤ => (⟨q.2.1 * q.1, q.2.2 * q.1⟩ : ℂ)) '' (range m ×ˢ univ) := by
    rintro _ ⟨ω, rfl⟩
    exact ⟨(m ω, ⌊(x ω).re / m ω⌋, ⌊(x ω).im / m ω⌋), ⟨mem_range_self ω, mem_univ _⟩, rfl⟩
  exact ((hm.prod countable_univ).image _).mono hsub

/-- `σ((h − h_ρ(w))|_K) ≤ mΩ` -/
theorem conf36_recSigma_le {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (ρ : ℝ) (w : ℂ) (K : Set ℂ) :
    recSigma h ρ w K ≤ ‹MeasurableSpace Ω› := by
  have hm : Measurable fun ω => -circleAvg (h ω) ρ w :=
    ((measurable_circleAvg_left ρ w).comp hh.measurable).neg
  exact (iInf₂_le (1 : ℝ) one_pos).trans
    ((measurable_restrictTo _).comp (hh.addConst hm).measurable).comap_le

/-- `E^U_r(z)` is null-measurable (Axiom II, locality of the harmonic part) -/
theorem conf36_confEU_nullMeas {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (p : CONFParams) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (T : Finset (ℤ × ℤ)) : NullMeasurableSet (confEU (xiGamma γ) c D P h p r z T) P := by
  obtain ⟨F, hF, hae⟩ := GM.p412j_confEU HarmLoc.p412jHarmLoc hD P h hh (xiGamma γ) c p hr z
    (ball z (6 * r)) isOpen_ball (closedBall_subset_ball (by linarith)) T
  have hF' : MeasurableSet F :=
    ((measurable_restrictTo _).comp hh.measurable).comap_le F hF
  exact hF'.nullMeasurableSet.congr hae.symm

end Random

/-- **CONF (3.25)** (C:1433–1437, "`{ε = 𝔢, z = 𝔷, ρ̃ⁿ = 𝔯, Ũ = 𝔘} ∩ ⋂_{m<n} (G̃^m)ᶜ ∩ A` is a.s.
determined by `h|_{ℂ∖𝔘}` and `E^𝔘_𝔯(𝔷)`"; DEC-114 §4 C2 (ii)): on each piece of Step 3, for
`A ∈ σ(𝓑^•_τ, h|_{𝓑^•_τ})` mod constants and `n' ≤ n`, the event `A ∩ ⋂_{1 ≤ m ≤ n'} (G̃^m)ᶜ ∩
{ε𝕣 = 𝔢, z = 𝔷, ρ̃^{n+1} = 𝔯, T = 𝔗} ∩ E^𝔘_𝔯(𝔷)` is a.s. `B' ∩ E^𝔘_𝔯(𝔷)` with
`B' ∈ σ((h − h_𝔯(𝔷))|_{ℂ∖𝔘})`, `𝔯 = 2^k𝔢`, `𝔘 = confU 𝔯 δ 𝔷 𝔗` -/
def Conf36Eq325 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams)
    (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) : Prop :=
  IsWeakLQGMetric γ D c →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ ‹MeasurableSpace Ω› →
      ∀ (x : Ω → ℂ) (ε : Ω → ℝ),
      @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x →
      @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε →
      (∀ ω, ε ω ∈ Ioo 0 1) → (Set.range ε).Countable →
      ∀ n : ℕ, ∀ n' ≤ n, ∀ A : Set Ω,
        MeasurableSet[localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))] A →
        ∀ i ∈ conf36Idx (fun ω => ε ω * R) (fun ω => conf36Grid (ε ω * R / 4) (x ω)),
          ∃ B' : Set Ω, MeasurableSet[recSigma h ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1
              (confU ((2 : ℝ) ^ i.2.2.1 * i.1) p.δ i.2.1 i.2.2.2)ᶜ] B' ∧
            conf36Avoid (conf36Gt Fat (xiGamma γ) c D P h p (fun ω => ε ω * R)
                (fun ω => conf36Grid (ε ω * R / 4) (x ω))
                (fun ω => filledBall (D (h ω)) z₀ (τ ω))) A n' ∩
              conf36Pc (xiGamma γ) c D P h p (fun ω => ε ω * R)
                (fun ω => conf36Grid (ε ω * R / 4) (x ω))
                (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n i =ᵐ[P]
              B' ∩ confEU (xiGamma γ) c D P h p ((2 : ℝ) ^ i.2.2.1 * i.1) i.2.1 i.2.2.2

/-- **Step 3 node** `Conf36StepNodeAE` (D120 form) from CONF (3.25) -/
theorem conf36StepNodeAE_of_eq325 {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop} (H : Conf36Eq325 γ D c p Fat) :
    Conf36StepNodeAE γ D c p Fat := by
  intro 𝔭 _ h𝔭1 H33 hD Ω _ P _ h hh z₀ R hR τ _ hloc hle x ε hx hε hxf hε1 hεc j n _ A hA _
  have he : ∀ ω, 0 < ε ω * R := fun ω => mul_pos (hε1 ω).1 hR
  have hec : (range fun ω => ε ω * R).Countable :=
    (hεc.image (· * R)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨ε ω, mem_range_self ω, rfl⟩)
  have hzc := conf36_range_grid_countable (m := fun ω => ε ω * R / 4)
    ((hεc.image (· * R / 4)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨ε ω, mem_range_self ω, rfl⟩)) x
  have H' := H hD P h hh z₀ R hR τ hloc hle x ε hx hε hε1 hεc
  refine conf36_step_of_pieces H33 h𝔭1.le hh he hec hzc (conf36_ae_conn hD hh he hxf) ?_
    (H' n n le_rfl A hA)
  intro i hi
  obtain ⟨B', hB', hae⟩ := H' n 0 (Nat.zero_le _) univ MeasurableSet.univ i hi
  have hi1 : 0 < i.1 := by
    obtain ⟨⟨ω, hω⟩, -⟩ := hi
    rw [← hω]; exact he ω
  have e0 : ∀ F : ℕ → Set Ω, conf36Avoid F univ 0 = univ := by
    intro F; ext ω
    simp only [conf36Avoid, univ_inter, mem_ofPred_eq, mem_univ, iff_true]
    intro m h1 h2; omega
  rw [e0, univ_inter] at hae
  exact (((conf36_recSigma_le hh _ _ _) _ hB').nullMeasurableSet.inter
    (conf36_confEU_nullMeas hD hh p (by positivity) _ _)).congr hae.symm

end LQGMetric.CONF
