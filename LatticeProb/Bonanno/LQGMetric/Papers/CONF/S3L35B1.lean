/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HarmLocD
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3EMeas

/-!
# CONF Lemma 3.5, leaf `CONFHarmLocN` under the D110 `IsHarmPart` (task P2-CONF35b)

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex` C:1150–1154 (condition 3 of `E^U_r(z)` is determined by `h|_W` viewed
modulo additive constants) and C:1187 (normalize `h` away from `U`, Markov property).

Under decision D110 (`Blueprint.IsHarmPart` conditions on `σ(h|_{ℂ∖U})` modulo constants) the
leaf `CONF.CONFHarmLocN` (S3EMeas.lean) is true as stated, **given the existence of a harmonic
part** (`CONFHarmExists`, the exact statement of `HarmExist.exists_isHarmPart`, DEC-110 packet P3,
proved by P2-D110c in Field/HarmExistB.lean, plugged in as `confHarmExists` in S3L35B9; without it the junk value `harmPart = 0` makes
the leaf false). Proof:

* `harmLoc_of_isHarmPart`: the argument of `HarmLoc.p412jHarmLoc` (Field/HarmLocD.lean; the
  locality argument of Sheffield math/0312099 §2.6 Thm 2.17 / Berestycki–Powell arXiv:2404.16642
  Thm 1.52 in `HarmLoc.p412jHarmLoc_raw`) for an arbitrary version `H` of the harmonic part;
* `confHarmLocN_of_exists`: apply it to `h' := h − h_ρ(w)` (whose harmonic part is
  `𝔥^U − h_ρ(w)`, `CONF.isHarmPart0_addConst_iff`) with an auxiliary circle `∂B_{ρ'}(u) ⊆ U`,
  and add back the `σ(h'|_W)`-measurable circle average `h'_{ρ'}(u)`.

Own routine glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.CONF

open Blueprint

/-- **existence of the harmonic part** for every whole-plane GFF and bounded open `U` (DEC-110
packet P3; exact statement of `HarmExist.exists_isHarmPart`, Field/HarmExistB.lean, P2-D110c). -/
def CONFHarmExists : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → ∃ H, IsHarmPart P h U H

theorem measurable_circleAvg_of_sphere_subset {Ω : Type} (h : Ω → DistC) {V : Set ℂ}
    (hV : IsOpen V) {ρ : ℝ} {w : ℂ} (hρ : 0 < ρ) (hS : sphere w ρ ⊆ V) :
    Measurable[fieldSigma h (toOpens V hV)] fun ω => circleAvg (h ω) ρ w := by
  obtain ⟨ε, hε, hεV⟩ := (isCompact_sphere w ρ).exists_thickening_subset_open hV hS
  have hεV' : thickening ε (sphere w |ρ|) ⊆ V := by rwa [abs_of_pos hρ]
  exact (GM.measurable_circleAvg_fieldSigma h ρ w hε).mono
    (GM.fieldSigma_mono h (V := nbhdO ε (sphere w |ρ|)) (W := toOpens V hV) hεV') le_rfl

/-- `HarmLoc.p412jHarmLoc` for an arbitrary version `H` of the harmonic part (same proof). -/
theorem harmLoc_of_isHarmPart {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (U V : Set ℂ)
    (hV : IsOpen V) (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUV : closure U ⊆ V)
    (ρ : ℝ) (w : ℂ) (hρ : 0 < ρ) (hS : sphere w ρ ⊆ V) (u : ℂ) (hu : u ∈ U)
    {H : Ω → ℂ → ℝ} (hH : IsHarmPart P h U H) :
    ∃ G : Ω → ℝ, Measurable[fieldSigma h (toOpens V hV)] G ∧
      (fun ω => H ω u - circleAvg (h ω) ρ w) =ᵐ[P] G := by
  have hWne : (V ∩ (closure U)ᶜ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, ← Set.sdiff_eq, Set.sdiff_eq_empty] at hne
    have hcl : closure U = V := le_antisymm hUV hne
    have hclopen : IsClopen (closure U) := ⟨isClosed_closure, hcl ▸ hV⟩
    rcases isClopen_iff.1 hclopen with h0 | h1
    · rw [closure_empty_iff] at h0
      exact (h0 ▸ hu : u ∈ (∅ : Set ℂ))
    · exact NormedSpace.unbounded_univ ℝ ℂ (h1 ▸ hUb.closure)
  obtain ⟨ψ₀, hψW, hψ1⟩ := HarmLoc.exists_unit_test (hV.inter isClosed_closure.isOpen_compl) hWne
  have hψV : tsupport (ψ₀ : ℂ → ℝ) ⊆ V := hψW.trans inter_subset_left
  have hψU : tsupport (ψ₀ : ℂ → ℝ) ⊆ Uᶜ :=
    hψW.trans (inter_subset_right.trans (compl_subset_compl.2 subset_closure))
  set h' := normIn h ψ₀
  have hH' : IsHarmPart0 P (fun ω => addConst (h ω) (-(h ω ψ₀))) U
      (fun ω x => H ω x + -(h ω ψ₀)) :=
    (isHarmPart0_addConst_iff h (fun ω => -(h ω ψ₀)) U H).2 hH
  have eσ : fieldSigmaClosed h' Uᶜ = fieldSigmaClosed0 h' Uᶜ :=
    (fieldSigmaClosed_normIn_eq h hψ1 hψU).trans (fieldSigmaClosed0_addConst h _ Uᶜ).symm
  have hraw : HarmLoc.IsHarmPartRaw P h' U (fun ω x => H ω x + -(h ω ψ₀)) := by
    unfold HarmLoc.IsHarmPartRaw
    rw [eσ]
    exact hH'
  obtain ⟨G, hGm, hGe⟩ := HarmLoc.p412jHarmLoc_raw (isWholePlaneGFF_normIn hh ψ₀) U V hV hUo hUb
    hUV ρ w hρ hS u hu hraw
  have hle : fieldSigma h' (toOpens V hV) ≤ fieldSigma h (toOpens V hV) := by
    rw [GM.gm_fieldSigma_eq_fieldSigma0On (V := toOpens V hV) hψ1 (normIn_apply_psi h hψ1) hψV,
      fieldSigma0On_normIn]
    exact fieldSigma0On_le_fieldSigma h hV
  refine ⟨G, hGm.mono hle le_rfl, ?_⟩
  filter_upwards [hGe, CircleAvg.ae_circleAvg_addConst hh w hρ] with ω h1 h2
  have h3 : circleAvg (h' ω) ρ w = circleAvg (h ω) ρ w + -(h ω ψ₀) := h2 _
  rw [← h1]
  show H ω u - circleAvg (h ω) ρ w = H ω u + -(h ω ψ₀) - circleAvg (h' ω) ρ w
  rw [h3]
  ring

/-- **`CONFHarmLocN`** (CONF C:1150–1154, condition 3) under the D110 `IsHarmPart`, from the
existence of harmonic parts. -/
theorem confHarmLocN_of_exists (hEx : CONFHarmExists) : CONFHarmLocN := by
  intro Ω _ P _ h hh U W hUo hUb hUW ρ w hρ u hu
  have hm : Measurable fun ω => -circleAvg (h ω) ρ w :=
    ((measurable_circleAvg_left ρ w).comp hh.measurable).neg
  set hc : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) ρ w) with hc_def
  have hhc : IsWholePlaneGFF hc P := hh.addConst hm
  have hH : IsHarmPart P h U (harmPart P h U) :=
    isHarmPart0_harmPart0 (hEx P h hh U hUo hUb)
  have hHc : IsHarmPart P hc U (fun ω x => harmPart P h U ω x + -circleAvg (h ω) ρ w) :=
    (isHarmPart0_addConst_iff h (fun ω => -circleAvg (h ω) ρ w) U (harmPart P h U)).2 hH
  obtain ⟨ρ', hρ', hB⟩ := Metric.isOpen_iff.1 hUo u hu
  have hS : sphere u (ρ' / 2) ⊆ (W : Set ℂ) := fun x hx =>
    hUW (subset_closure (hB (by rw [mem_sphere] at hx; rw [mem_ball]; linarith)))
  obtain ⟨G, hGm, hGe⟩ := harmLoc_of_isHarmPart hhc U W W.isOpen hUo hUb hUW (ρ' / 2) u
    (by linarith) hS u hu hHc
  have hcm := measurable_circleAvg_of_sphere_subset hc W.isOpen (by linarith : 0 < ρ' / 2) hS
  refine ⟨fun ω => G ω + circleAvg (hc ω) (ρ' / 2) u, hGm.add hcm, ?_⟩
  filter_upwards [hGe] with ω hω
  rw [← hω]
  ring

end LQGMetric.CONF
