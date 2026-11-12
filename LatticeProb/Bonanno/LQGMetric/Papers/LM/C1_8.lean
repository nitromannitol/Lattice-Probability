/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Copy

/-!
# LM Corollary 1.8 (`cor-bilip-msrble`) from LM Theorems 1.6, 1.7 and Lemma 1.4 (task P2-LMC18)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Corollary 1.8 (l. 317–329) and its proof (l. 323–332): "We first
claim that `(D, D̃)` is a pair of ξ-additive local metrics for `h|_U` [… Lemma 1.4 …]. Theorem 1.6
tells us that if (1.3) holds for a large enough universal `p ∈ (0,1)`, then a.s.
`D̃(z,w) ≤ C D(z,w)` for each `z, w ∈ U`. Therefore, Theorem 1.7 implies that `D` is a.s.
determined by `h`."

Main results:
* `c18_xiAdditive_copy`: the copy pair `(D, D̃)` on `condCopyMeasure D h P` is ξ-additive for
  `h` (LM l. 323–328), from `Blueprint.LMLem1_4` and `CopyAeLength`;
* `lmCor1_8_core`: the statement of `LMCor1_8` with the extra hypothesis "the copy `D̃` is a.s.
  a length metric", from `LMThm1_6`, `LMLem1_4`, `LMThm1_7`;
* `lmCor1_8_of : LMThm1_6 → LMLem1_4 → LMThm1_7 → CopyAeLength → LMCor1_8`;
* `lmCor1_8L_of : LMThm1_6 → LMLem1_4 → LMThm1_7 → LMCor1_8L`, where `LMCor1_8L` reads "random
  length metric" on the law (`∀ᵐ d ∂ law(D), d.IsLength`), which transfers to the copy
  (`c18_copy_ae_length`);
* `copyAeLength_of_nullMeasurable`: `CopyAeLength` holds once the set of length metrics is
  null-measurable for every probability measure on `ContMetric`.

Open inputs stated here:
* `LMThm1_7` — LM Theorem 1.7 (`thm-msrble-general`, l. 306–311), `U = ℂ`, verbatim (cited
  result; LM §4, l. 885–1110, proves it with the Efron–Stein inequality);
* `CopyAeLength` — the conditionally independent copy `D̃` is a.s. a length metric when `D` is.
  LM take this for granted ("conditionally i.i.d. samples from the conditional law of `D`"); in
  Lean it needs measurability of `{d | d.IsLength}` (see the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip

/-- **LM Theorem 1.7** (`thm-msrble-general`, l. 306–311), `U = ℂ`: "Let `h` be a GFF on `U`, and
let `(h, D)` be a coupling of `h` with a random continuous length metric which is local for `h`.
Assume that `D` is determined by `h` up to bi-Lipschitz equivalence in the following sense.
Suppose we condition on `h` and let `D, D̃` be conditionally i.i.d. samples from the conditional
law of `D` given `h`. There is a random constant `C = C_h > 1`, depending only on `h`, such that
a.s. `D̃(z,w) ≤ C D(z,w)` for each `z, w ∈ U`. Then `D` is a.s. determined by `h`." The pair
`(D, D̃)` is the canonical copy `condCopyMeasure` (as in `Blueprint.LMCor1_8`), and `C_h` is
`C ∘ h` for a measurable `C`. -/
def LMThm1_7 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D : Ω → ContMetric) (hh : IsWholePlaneGFF h P), IsLocalMetric P h D →
    ∀ C : DistC → ℝ, Measurable C → (∀ g, 1 < C g) →
      (∀ᵐ q ∂condCopyMeasure D h P hh.measurable, ∀ z w : ℂ,
        q.2.1 (z, w) ≤ C (h q.1) * (D q.1).1 (z, w)) →
      AEDeterminedBy D h P

/-- the conditionally independent copy of an a.s. length metric is a.s. a length metric -/
def CopyAeLength : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D : Ω → ContMetric) (hm : Measurable h), Measurable D → (∀ᵐ ω ∂P, (D ω).IsLength) →
    ∀ᵐ q ∂condCopyMeasure D h P hm, q.2.IsLength

section Copy

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {D : Ω → ContMetric}

lemma c18_law_fst (hm : Measurable h) (hD : Measurable D) :
    (condCopyMeasure D h P hm).map (fun q => (h q.1, D q.1)) = P.map (fun ω => (h ω, D ω)) := by
  rw [show (fun q : Ω × ContMetric => (h q.1, D q.1)) = (fun ω => (h ω, D ω)) ∘ Prod.fst from rfl,
    ← Measure.map_map (hm.prodMk hD) measurable_fst, condCopyMeasure_fst]

lemma c18_ae_fst (hm : Measurable h) {p : Ω → Prop} (H : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ q ∂condCopyMeasure D h P hm, p q.1 := by
  have : ∀ᵐ ω ∂(condCopyMeasure D h P hm).map Prod.fst, p ω := by
    rw [condCopyMeasure_fst]; exact H
  exact ae_of_ae_map measurable_fst.aemeasurable this

lemma c18_isNormalized_copy (hh : IsNormalizedWPGFF h P) :
    IsNormalizedWPGFF (fun q => h q.1) (condCopyMeasure D h P hh.1.measurable) := by
  have hm := hh.1.measurable
  refine ⟨DFGPS.L217.isWholePlaneGFF_of_map_eq (hm.comp measurable_fst) hh.1 ?_, c18_ae_fst hm hh.2⟩
  rw [show (fun q : Ω × ContMetric => h q.1) = h ∘ Prod.fst from rfl,
    ← Measure.map_map hm measurable_fst, condCopyMeasure_fst]

/-- **LM l. 323–328**: the copy pair `(D, D̃)` is ξ-additive for `h` -/
theorem c18_xiAdditive_copy (h14 : LMLem1_4) {ξ : ℝ} (hh : IsNormalizedWPGFF h P)
    (hxi : IsXiAdditive1 ξ P h D)
    (hlen : ∀ᵐ q ∂condCopyMeasure D h P hh.1.measurable, q.2.IsLength) :
    IsXiAdditive2 ξ (condCopyMeasure D h P hh.1.measurable) (fun q => h q.1) (fun q => D q.1)
      Prod.snd := by
  obtain ⟨⟨hD, -, hlD', hJL⟩, hadd⟩ := hxi
  have hm := hh.1.measurable
  set P' := condCopyMeasure D h P hm with hP'
  have hlD : ∀ᵐ ω ∂P, (D ω).IsLength := hlD'.mono fun _ h => h.1
  have hn' := c18_isNormalized_copy (D := D) hh
  have hh' := hn'.1
  have hm' : Measurable fun q : Ω × ContMetric => h q.1 := hm.comp measurable_fst
  have hD1 : Measurable fun q : Ω × ContMetric => D q.1 := hD.comp measurable_fst
  have hl1 : ∀ᵐ q ∂P', (D q.1).IsLength := c18_ae_fst hm hlD
  have law1 := c18_law_fst (P := P) hm hD
  have law2 := condCopyMeasure_map_snd (μ := P) hm hD
  have hci := condIndepEv_condCopy (μ := P) hm hD
  have loc1 : IsLocalMetric P' (fun q => h q.1) (fun q => D q.1) :=
    c18_isLocalMetric_of_jl hD1 hl1
      (c18_jl_transfer_plain hm hD hm' hD1 law1.symm hlD hl1 hJL)
  have loc2 : IsLocalMetric P' (fun q => h q.1) Prod.snd :=
    c18_isLocalMetric_of_jl measurable_snd hlen
      (c18_jl_transfer_plain hm hD hm' measurable_snd law2.symm hlD hlen hJL)
  refine ⟨h14 P' _ _ _ hh' loc1 loc2 hci, fun z r hr => ?_⟩
  -- the rescaled metrics and the recentred field
  have hc : Measurable fun g : DistC => circleAvg g r z := measurable_circleAvg_left r z
  have hc' : Measurable fun q : Ω × ContMetric => circleAvg (h q.1) r z := hc.comp hm'
  have hf : Measurable fun g : DistC => addConst g (-circleAvg g r z) :=
    DFGPS.L219.measurable_addConst_of measurable_id hc.neg
  have hs : Measurable fun g : DistC => Real.exp (-ξ * circleAvg g r z) :=
    (hc.const_mul (-ξ)).exp
  let g' : Ω × ContMetric → DistC := fun q => addConst (h q.1) (-circleAvg (h q.1) r z)
  let D₁ : Ω × ContMetric → ContMetric := fun q =>
    (D q.1).smulPos (Real.exp (-ξ * circleAvg (h q.1) r z)) (Real.exp_pos _)
  let D₂ : Ω × ContMetric → ContMetric := fun q =>
    q.2.smulPos (Real.exp (-ξ * circleAvg (h q.1) r z)) (Real.exp_pos _)
  have hg' : Measurable g' := hf.comp hm'
  have hD₁ : Measurable D₁ := DFGPS.L217.measurable_smulPos_rand hD1 (hc'.const_mul (-ξ))
  have hD₂ : Measurable D₂ := DFGPS.L217.measurable_smulPos_rand measurable_snd (hc'.const_mul (-ξ))
  have hint : ∀ (F : Ω × ContMetric → ContMetric), ∀ᵐ q ∂P', ∀ V : Set ℂ, IsOpen V →
      (fun u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (h q.1) r z)) * (F q).internal V u v) =
        internalFam (fun q => (F q).smulPos (Real.exp (-ξ * circleAvg (h q.1) r z))
          (Real.exp_pos _)) q V :=
    fun F => Eventually.of_forall fun q V _ => by
      funext u v
      exact (ContMetric.internal_smulPos _ _ _ _ _).symm
  have hint' : ∀ (F : Ω × ContMetric → ContMetric), ∀ᵐ q ∂P', ∀ V : Set ℂ, IsOpen V →
      internalFam (fun q => (F q).smulPos (Real.exp (-ξ * circleAvg (h q.1) r z))
          (Real.exp_pos _)) q V =
        (fun u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (h q.1) r z)) * (F q).internal V u v) :=
    fun F => (hint F).mono fun q hq V hV => (hq V hV).symm
  have T1 := c18_jl_transfer hm hD hm' hD1 law1.symm hlD hl1 hf hs (hadd z r hr)
  have T2 := c18_jl_transfer hm hD hm' measurable_snd law2.symm hlD hlen hf hs (hadd z r hr)
  have loc1s : IsLocalMetric P' g' D₁ :=
    c18_isLocalMetric_of_jl hD₁ (hl1.mono fun q hq => ContMetric.isLength_smulPos _ hq)
      (isJointlyLocalFam_congr T1 (hint' fun q => D q.1) (hint' fun q => D q.1))
  have loc2s : IsLocalMetric P' g' D₂ :=
    c18_isLocalMetric_of_jl hD₂ (hlen.mono fun q hq => ContMetric.isLength_smulPos _ hq)
      (isJointlyLocalFam_congr T2 (hint' Prod.snd) (hint' Prod.snd))
  -- conditional independence given `h − h_r(z)` (LM l. 326–327)
  have hH : MeasurableSpace.comap (fun q : Ω × ContMetric => h q.1) inferInstance ≤
      (inferInstance : MeasurableSpace (Ω × ContMetric)) := hm'.comap_le
  have hci' := c18_condIndepEv_sup_cond hH hD1.comap_le measurable_snd.comap_le hci
  have hGH : MeasurableSpace.comap g' inferInstance ≤
      MeasurableSpace.comap (fun q : Ω × ContMetric => h q.1) inferInstance := by
    rw [show g' = (fun g : DistC => addConst g (-circleAvg g r z)) ∘ fun q => h q.1 from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hf.comap_le
  have hHG : MeasurableSpace.comap (fun q : Ω × ContMetric => h q.1) inferInstance ≤
      aeClosure P' (MeasurableSpace.comap g' inferInstance) := by
    have hN : Measurable fun g : DistC => addConst g (-circleAvg g 1 0) :=
      DFGPS.L219.measurable_addConst_of measurable_id (measurable_circleAvg_left 1 0).neg
    refine DFGPS.L219.comap_le_aeClosure_of_ae_eq
      (Y := fun q => addConst (g' q) (-circleAvg (g' q) 1 0)) (hN.comp (comap_measurable g')) ?_
    filter_upwards [hn'.2, CircleAvg.ae_circleAvg_addConst_one_zero hh'] with q h0 hq
    show h q.1 = addConst (addConst (h q.1) (-circleAvg (h q.1) r z))
      (-circleAvg (addConst (h q.1) (-circleAvg (h q.1) r z)) 1 0)
    rw [hq, h0, zero_add, neg_neg, GFFLaw.addConst_addConst, neg_add_cancel, GFFLaw.addConst_zero']
  have hA : MeasurableSpace.comap (fun q : Ω × ContMetric => D q.1) inferInstance ⊔
      MeasurableSpace.comap (fun q : Ω × ContMetric => h q.1) inferInstance ≤
      (inferInstance : MeasurableSpace (Ω × ContMetric)) := sup_le hD1.comap_le hH
  have hB : MeasurableSpace.comap (Prod.snd : Ω × ContMetric → ContMetric) inferInstance ⊔
      MeasurableSpace.comap (fun q : Ω × ContMetric => h q.1) inferInstance ≤
      (inferInstance : MeasurableSpace (Ω × ContMetric)) := sup_le measurable_snd.comap_le hH
  have hci2 := DFGPS.L217.condIndepEv_congr_cond hH (hg'.comap_le) hHG
    (hGH.trans (le_aeClosure _)) (hA.trans (le_aeClosure _)) (hB.trans (le_aeClosure _)) hci'
  have hcis : CondIndepEv (MeasurableSpace.comap g' inferInstance)
      (MeasurableSpace.comap D₁ inferInstance) (MeasurableSpace.comap D₂ inferInstance) P' := by
    refine hci2.mono ?_ ?_
    · exact c18_comap_le_of_factor (fun q : Ω × ContMetric => h q.1) (fun q => D q.1)
        (F := fun t : DistC × ContMetric => t.2.smulPos (Real.exp (-ξ * circleAvg t.1 r z))
          (Real.exp_pos _))
        (DFGPS.L217.measurable_smulPos_rand measurable_snd ((hc.comp measurable_fst).const_mul (-ξ)))
    · exact c18_comap_le_of_factor (fun q : Ω × ContMetric => h q.1) Prod.snd
        (F := fun t : DistC × ContMetric => t.2.smulPos (Real.exp (-ξ * circleAvg t.1 r z))
          (Real.exp_pos _))
        (DFGPS.L217.measurable_smulPos_rand measurable_snd ((hc.comp measurable_fst).const_mul (-ξ)))
  have hJ := (h14 P' g' D₁ D₂ (hh'.addConst hc'.neg) loc1s loc2s hcis).2.2.2
  exact isJointlyLocalFam_congr hJ (hint fun q => D q.1) (hint Prod.snd)

end Copy

/-- **LM Corollary 1.8, core** (l. 323–332): the statement of `LMCor1_8` with the extra
hypothesis that the copy `D̃` is a.s. a length metric -/
theorem lmCor1_8_core (h16 : LMThm1_6) (h14 : LMLem1_4) (h17 : LMThm1_7) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (D : Ω → ContMetric) (hh : IsNormalizedWPGFF h P),
        IsXiAdditive1 ξ P h D →
        (∀ᵐ q ∂condCopyMeasure D h P hh.1.measurable, q.2.IsLength) → ∀ C : ℝ, 0 < C →
        (∀ K : Set ℂ, IsCompact K → ∃ rK : ℝ, 0 < rK ∧ ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) rK,
          ENNReal.ofReal p ≤ condCopyMeasure D h P hh.1.measurable
            {q | internalDiam q.2 (Metric.sphere z r) (annulus z (r / 2) (2 * r)) ≤
              ENNReal.ofReal C * setDist (D q.1) (Metric.sphere z (r / 2)) (Metric.sphere z r)}) →
        AEDeterminedBy D h P := by
  obtain ⟨p, hp0, hp1, H16⟩ := h16
  refine ⟨p, hp0, hp1, fun ξ Ω _ P _ h D hh hxi hl C hC hK => ?_⟩
  have hm := hh.1.measurable
  obtain ⟨⟨hD, -, hlD', hJL⟩, -⟩ := id hxi
  have hlD : ∀ᵐ ω ∂P, (D ω).IsLength := hlD'.mono fun _ h => h.1
  have hxi' := c18_xiAdditive_copy h14 hh hxi hl
  have hbound := H16 ξ (condCopyMeasure D h P hm) (fun q => h q.1) (fun q => D q.1) Prod.snd
    (c18_isNormalized_copy hh) hxi' C hC hK
  refine h17 P h D hh.1 (c18_isLocalMetric_of_jl hD hlD hJL) (fun _ => max C 2) measurable_const
    (fun _ => lt_max_of_lt_right one_lt_two) ?_
  filter_upwards [hbound] with q hq z w
  exact (hq z w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (dist_nonneg : 0 ≤ dist ((D q.1).pt z) ((D q.1).pt w)))

/-- **LM Corollary 1.8** (`cor-bilip-msrble`, l. 317–332) from LM Theorem 1.6, LM Lemma 1.4,
LM Theorem 1.7 and `CopyAeLength`, following LM's proof (l. 323–332). -/
theorem lmCor1_8_of (h16 : LMThm1_6) (h14 : LMLem1_4) (h17 : LMThm1_7) (hlen : CopyAeLength) :
    LMCor1_8 := by
  obtain ⟨p, hp0, hp1, H⟩ := lmCor1_8_core h16 h14 h17
  refine ⟨p, hp0, hp1, fun ξ Ω _ P _ h D hh hxi C hC hK => ?_⟩
  obtain ⟨⟨hD, -, hlD', -⟩, -⟩ := id hxi
  exact H ξ P h D hh hxi (hlen P h D hh.1.measurable hD (hlD'.mono fun _ h => h.1)) C hC hK

/-- `CopyAeLength` from null-measurability of the set of length metrics -/
theorem copyAeLength_of_nullMeasurable
    (hL : ∀ μ : Measure ContMetric, IsProbabilityMeasure μ →
      NullMeasurableSet {d : ContMetric | d.IsLength} μ) : CopyAeLength := by
  intro Ω _ P _ h D hm hD hlD
  have hlaw : (condCopyMeasure D h P hm).map Prod.snd = P.map D := by
    have e := congrArg (fun μ => μ.map Prod.snd) (condCopyMeasure_map_snd (μ := P) hm hD)
    rw [Measure.map_map measurable_snd (hm.prodMk hD), Measure.map_map measurable_snd
      (show Measurable fun p : Ω × ContMetric => (h p.1, p.2) from
        (hm.comp measurable_fst).prodMk measurable_snd)] at e
    exact e
  have : IsProbabilityMeasure (P.map D) :=
    (Measure.isProbabilityMeasure_map_iff hD.aemeasurable).2 inferInstance
  obtain ⟨M, hMS, hM, hMae⟩ := (hL (P.map D) this).exists_measurable_subset_ae_eq
  obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null
    (show (P.map D) ({d : ContMetric | d.IsLength} \ M) = 0 from
      ae_le_set.1 hMae.symm.le)
  have hDM : ∀ᵐ ω ∂P, D ω ∈ M := by
    have hN' : ∀ᵐ ω ∂P, D ω ∉ N := by
      rw [Measure.map_apply hD hN] at hN0
      exact measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hlD, hN'] with ω h1 h2
    by_contra h3
    exact h2 (hSN ⟨h1, h3⟩)
  have h1 : ∀ᵐ d ∂(condCopyMeasure D h P hm).map Prod.snd, d ∈ M := by
    rw [hlaw]; exact (ae_map_iff hD.aemeasurable hM).2 hDM
  exact (ae_of_ae_map measurable_snd.aemeasurable h1).mono fun q hq => hMS hq

end LQGMetric.LM
