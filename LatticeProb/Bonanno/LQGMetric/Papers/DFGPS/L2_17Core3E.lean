/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3D

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: `σ(D₁(·,·;W)) ⊆ σ(Fb, d₂_W)` in the limit coupling (R1 + R2)

Source and proof: see L2_17Core3D.lean (T:1240–1273).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint MetricGeometry LFPP GM.Bilip

/-- **Step 4, the `h̊` side, in the limit coupling** (T:1248–1251, T:1270–1273) -/
theorem comap_intFn_le_aeClosure_coupling (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [PolishSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {N : S → DistC} (hN : IsGFFPlusBddCont N μ)
    {Fb : S → C(ℂ, ℝ)} (hFb : Measurable Fb) {K : Set ℂ} (hK : IsCompact K)
    (hFK : ∀ x, ∀ z ∉ K, Fb x z = 0)
    (hN₂ : IsGFFPlusBddCont (fun x => N x - ofCont (Fb x)) μ)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n) (hεs0 : Tendsto εs atTop (𝓝 0))
    {ρ : ProbabilityMeasure (S × (DyProd × DyProd))}
    (hconv : ∀ f : S × (DyProd × DyProd) →ᵇ ℝ, Tendsto (fun n => ∫ x, f (x,
        (lfppJoint (xiGamma γ) (εs n) (N x), lfppJoint (xiGamma γ) (εs n) (N x - ofCont (Fb x))))
          ∂μ) atTop (𝓝 (∫ p, f p ∂(ρ : Measure (S × (DyProd × DyProd))))))
    (hmarg : (ρ : Measure (S × (DyProd × DyProd))).map Prod.fst = μ) (W : dyadicDomainsC) :
    MeasurableSpace.comap (fun p : S × (DyProd × DyProd) => intFn W p.2.1.1) inferInstance ≤
      aeClosure (ρ : Measure (S × (DyProd × DyProd))) (MeasurableSpace.comap
        (fun p : S × (DyProd × DyProd) => (Fb p.1, p.2.2.2 W)) inferInstance) := by
  set ξ := xiGamma γ
  set N₂ : S → DistC := fun x => N x - ofCont (Fb x)
  have hA₁ : ∀ n, AEMeasurable (fun x => lfppJoint ξ (εs n) (N x)) μ := fun n =>
    aemeasurable_lfppJoint hN (hεs n).ne'
  have hA₂ : ∀ n, AEMeasurable (fun x => lfppJoint ξ (εs n) (N₂ x)) μ := fun n =>
    aemeasurable_lfppJoint hN₂ (hεs n).ne'
  set L : ℕ → S → DyProd × DyProd := fun n x => ((hA₁ n).mk _ x, (hA₂ n).mk _ x)
  have hLm : ∀ n, Measurable (L n) := fun n =>
    (hA₁ n).measurable_mk.prodMk (hA₂ n).measurable_mk
  have hLe : ∀ n, ∀ᵐ x ∂μ, L n x = (lfppJoint ξ (εs n) (N x), lfppJoint ξ (εs n) (N₂ x)) :=
    fun n => by
      filter_upwards [(hA₁ n).ae_eq_mk, (hA₂ n).ae_eq_mk] with x h1 h2
      simp only [L, ← h1, ← h2]
  -- stable convergence: add `Fb x`
  have hΦ : Measurable fun x : S => (x, Fb x) := measurable_id.prodMk hFb
  have hst := tendsto_law_of_fixed_marginal (P := μ) (P' := (ρ : Measure _)) (X := id)
    measurable_id (X' := Prod.fst) measurable_fst (by rw [hmarg, Measure.map_id]) (Yn := L) hLm
    (Y := Prod.snd) measurable_snd (fun φ hφ ⟨C, hC⟩ => by
      have H := hconv (BoundedContinuousFunction.mkOfBound ⟨φ, hφ⟩ (2 * C) fun a b => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have := abs_sub (φ a) (φ b)
        linarith [hC a, hC b])
      simp only [BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk] at H
      refine H.congr fun n => integral_congr_ae ?_
      filter_upwards [hLe n] with x hx
      simp only [id, hx]; rfl) hΦ
  -- Skorokhod
  obtain ⟨Ω', mΩ', hsb, P', hP', Z, Z₀, hZm, hZ₀m, hZlaw, hZ₀law, hZc⟩ :=
    exists_skorokhod_representation_sb hst
  simp only [ProbabilityMeasure.coe_mk] at hZlaw hZ₀law
  -- the field coordinate of `Z n` has law `μ`
  have hΦn : ∀ n, Measurable fun x : S => ((x, Fb x), L n x) := fun n => hΦ.prodMk (hLm n)
  have hlawx : ∀ n, P'.map (fun ω => (Z n ω).1.1) = μ := fun n => by
    calc P'.map (fun ω => (Z n ω).1.1)
        = (P'.map (Z n)).map (fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => e.1.1) :=
          (Measure.map_map (measurable_fst.comp measurable_fst) (hZm n)).symm
      _ = (μ.map fun x : S => ((x, Fb x), L n x)).map
            (fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => e.1.1) := by rw [hZlaw n]; rfl
      _ = μ.map fun x : S => x := Measure.map_map (measurable_fst.comp measurable_fst) (hΦn n)
      _ = μ := Measure.map_id
  have hx : ∀ n, ∀ Q : S → Prop, (∀ᵐ x ∂μ, Q x) → ∀ᵐ ω ∂P', Q (Z n ω).1.1 := fun n Q hQ =>
    ae_of_ae_map ((measurable_fst.comp measurable_fst).comp (hZm n)).aemeasurable
      (by rw [hlawx n]; exact hQ : ∀ᵐ x ∂(P'.map (fun ω => (Z n ω).1.1)), Q x)
  -- `Z n` lies on the graph of `x ↦ ((x, Fb x), L n x)`
  have hgraph : ∀ n, ∀ᵐ ω ∂P', (Z n ω).1.2 = Fb (Z n ω).1.1 ∧ (Z n ω).2 = L n (Z n ω).1.1 :=
    fun n => by
      have hAm : MeasurableSet {e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) |
          e.1.2 = Fb e.1.1 ∧ e.2 = L n e.1.1} :=
        (measurableSet_eq_fun (measurable_snd.comp measurable_fst)
          (hFb.comp (measurable_fst.comp measurable_fst))).inter
          (measurableSet_eq_fun measurable_snd ((hLm n).comp (measurable_fst.comp measurable_fst)))
      have : ∀ᵐ e ∂(P'.map (Z n)), e ∈ {e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) |
          e.1.2 = Fb e.1.1 ∧ e.2 = L n e.1.1} := by
        rw [hZlaw n]
        exact (ae_map_iff (hΦ.comp measurable_id |>.prodMk (hLm n)).aemeasurable hAm).2
          (Eventually.of_forall fun x => ⟨rfl, rfl⟩)
      exact ae_of_ae_map (hZm n).aemeasurable this
  -- regularity of the fields along the sequence
  have hF1 : ∀ᵐ ω ∂P', ∀ n, L n (Z n ω).1.1 =
      (lfppJoint ξ (εs n) (N (Z n ω).1.1), lfppJoint ξ (εs n) (N₂ (Z n ω).1.1)) :=
    ae_all_iff.2 fun n => hx n _ (hLe n)
  have hF2 : ∀ᵐ ω ∂P', ∀ n, Continuous (heatMollify (εs n) (N (Z n ω).1.1)) :=
    ae_all_iff.2 fun n => hx n _ ((hN.ae_tendstoLocallyUniformly_heatMollify _
      (hεs n).ne').mono fun x hx => hx.2)
  have hF3 : ∀ᵐ ω ∂P', ∀ n, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => N₂ (Z n ω).1.1 (heatTrunc (εs n ^ 2 / 2) z k))
        (heatMollify (εs n) (N₂ (Z n ω).1.1)) atTop ∧
        Continuous (heatMollify (εs n) (N₂ (Z n ω).1.1)) :=
    ae_all_iff.2 fun n => hx n _ (hN₂.ae_tendstoLocallyUniformly_heatMollify _ (hεs n).ne')
  -- the laws of the two LFPP coordinates converge to those of the limit
  have hlaw₁ : ∀ n, P'.map (fun ω => (Z n ω).2.1) =
      μ.map fun x => lfppJoint ξ (εs n) (N x) := fun n => by
    calc P'.map (fun ω => (Z n ω).2.1)
        = (P'.map (Z n)).map (fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => e.2.1) :=
          (Measure.map_map (measurable_fst.comp measurable_snd) (hZm n)).symm
      _ = (μ.map fun x : S => ((x, Fb x), L n x)).map
            (fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => e.2.1) := by rw [hZlaw n]; rfl
      _ = μ.map fun x : S => (L n x).1 :=
          Measure.map_map (measurable_fst.comp measurable_snd) (hΦn n)
      _ = _ := Measure.map_congr ((hLe n).mono fun x hx => by simp only [hx])
  have hlaw₂ : ∀ n, P'.map (fun ω => (Z n ω).2.2) =
      μ.map fun x => lfppJoint ξ (εs n) (N₂ x) := fun n => by
    calc P'.map (fun ω => (Z n ω).2.2)
        = (P'.map (Z n)).map (fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => e.2.2) :=
          (Measure.map_map (measurable_snd.comp measurable_snd) (hZm n)).symm
      _ = (μ.map fun x : S => ((x, Fb x), L n x)).map
            (fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => e.2.2) := by rw [hZlaw n]; rfl
      _ = μ.map fun x : S => (L n x).2 :=
          Measure.map_map (measurable_snd.comp measurable_snd) (hΦn n)
      _ = _ := Measure.map_congr ((hLe n).mono fun x hx => by simp only [hx])
  have hc₁ := tendsto_map_of_forall_tendsto (P := P') (fun n => (measurable_fst.comp
    measurable_snd).comp (hZm n)) ((measurable_fst.comp measurable_snd).comp hZ₀m)
    fun ω => ((continuous_fst.comp continuous_snd).tendsto _).comp (hZc ω)
  have hc₂ := tendsto_map_of_forall_tendsto (P := P') (fun n => (measurable_snd.comp
    measurable_snd).comp (hZm n)) ((measurable_snd.comp measurable_snd).comp hZ₀m)
    fun ω => ((continuous_snd.comp continuous_snd).tendsto _).comp (hZc ω)
  have hD₁ : ∀ᵐ ω ∂P', IsDyadicLimit (Z₀ ω).2.1 := by
    refine ae_of_ae_map ((measurable_fst.comp measurable_snd).comp hZ₀m).aemeasurable
      (ae_isDyadicLimit_of_tendsto h28 hγ hγ2 hN hεs hεs0 (hc₁.congr fun n => ?_))
    exact Subtype.ext (hlaw₁ n)
  have hD₂ : ∀ᵐ ω ∂P', IsDyadicLimit (Z₀ ω).2.2 := by
    refine ae_of_ae_map ((measurable_snd.comp measurable_snd).comp hZ₀m).aemeasurable
      (ae_isDyadicLimit_of_tendsto h28 hγ hγ2 hN₂ hεs hεs0 (hc₂.congr fun n => ?_))
    exact Subtype.ext (hlaw₂ n)
  have hAg : ∀ᵐ ω ∂P', ∀ k r : ℕ, ∃ s : ℕ,
      (Z₀ ω).2.2.1 ∈ agreeSetK ((k : ℝ) + 1) ((r : ℝ) + 1) s := by
    refine ae_of_ae_map ((measurable_snd.comp measurable_snd).comp hZ₀m).aemeasurable
      (ae_agreeSetK_of_tendsto h28 hγ hγ2 hN₂ hεs hεs0 (E := DyProd)
        (ρ := ⟨P'.map fun ω => (Z₀ ω).2.2, (Measure.isProbabilityMeasure_map_iff
          ((measurable_snd.comp measurable_snd).comp hZ₀m).aemeasurable).2 inferInstance⟩)
        continuous_fst fun f => ?_)
    have H := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hc₂)
      (f.compContinuous ⟨Prod.fst, continuous_fst⟩)
    simp only [ProbabilityMeasure.coe_mk, BoundedContinuousFunction.compContinuous_apply] at H
    refine H.congr fun n => ?_
    rw [show Measure.map ((Prod.snd ∘ Prod.snd : (S × C(ℂ, ℝ)) × (DyProd × DyProd) → DyProd) ∘
        Z n) P' = _ from hlaw₂ n]
    exact integral_map (hA₂ n) (f.continuous.comp continuous_dyProd_fst).aestronglyMeasurable
  -- the good event on the Skorokhod space
  have hgood : ∀ᵐ ω ∂P', IsDyadicLimit (Z₀ ω).2.1 ∧ IsDyadicLimit (Z₀ ω).2.2 ∧
      ∀ hc : IsContinuousMetric (Z₀ ω).2.2.1, ∀ u v : ℂ,
        ENNReal.ofReal ((Z₀ ω).2.1.1 (u, v)) = weylScale ξ (Z₀ ω).1.2 ⟨(Z₀ ω).2.2.1, hc⟩ u v := by
    filter_upwards [hD₁, hD₂, hAg, ae_all_iff.2 hgraph, hF1, hF2, hF3] with ω d1 d2 ag g0 f1 f2 f3
    refine ⟨d1, d2, fun hc u v => ?_⟩
    have e1 : ∀ n, (Z n ω).1.2 = Fb (Z n ω).1.1 := fun n => (g0 n).1
    have e2 : ∀ n, (Z n ω).2 = (lfppJoint ξ (εs n) (N (Z n ω).1.1),
        lfppJoint ξ (εs n) (N₂ (Z n ω).1.1)) := fun n => (g0 n).2.trans (f1 n)
    have hadd : ∀ n, addFun (N₂ (Z n ω).1.1) ((Z n ω).1.2) = N (Z n ω).1.1 := fun n => by
      rw [e1 n]; simp only [addFun, N₂, sub_add_cancel]
    obtain ⟨hc', hl⟩ := d2.1
    refine weyl_of_sample ξ hεs hεs0 (g := fun n => N₂ (Z n ω).1.1) f3
      (f := fun n => (Z n ω).1.2) (F := (Z₀ ω).1.2)
      (((continuous_snd.comp continuous_fst).tendsto _).comp (hZc ω)) hK
      (fun n z hz => by rw [e1 n]; exact hFK _ z hz) (fun n => by rw [hadd n]; exact f2 n)
      ?_ (D := ⟨(Z₀ ω).2.2.1, hc⟩) hl ag ?_ u v
    · have e : (fun n => lfppC ξ (εs n) (addFun (N₂ (Z n ω).1.1) ((Z n ω).1.2))) =
          fun n => (Z n ω).2.1.1 := funext fun n => by rw [hadd n, e2 n]; rfl
      rw [e]
      exact ((continuous_fst.comp (continuous_fst.comp continuous_snd)).tendsto _).comp (hZc ω)
    · have e : (fun n => lfppC ξ (εs n) (N₂ (Z n ω).1.1)) = fun n => (Z n ω).2.2.1 :=
        funext fun n => by rw [e2 n]; rfl
      rw [e]
      exact ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).comp (hZc ω)
  -- Lusin on the Skorokhod space, then back to `ρ`
  have Hrep := comap_le_aeClosure_of_rep (P' := P') hZ₀m
    (G := fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => intFn W e.2.1.1)
    ((measurable_intFn W).comp (continuous_dyProd_fst.measurable.comp
      (measurable_fst.comp measurable_snd)))
    (R := fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => (e.1.2, e.2.2.2 W))
    ((measurable_snd.comp measurable_fst).prodMk
      ((continuous_dyProd_snd W).measurable.comp (measurable_snd.comp measurable_snd)))
    (Good := fun e : (S × C(ℂ, ℝ)) × (DyProd × DyProd) => IsDyadicLimit e.2.1 ∧
      IsDyadicLimit e.2.2 ∧ ∀ hc : IsContinuousMetric e.2.2.1, ∀ u v : ℂ,
        ENNReal.ofReal (e.2.1.1 (u, v)) = weylScale ξ e.1.2 ⟨e.2.2.1, hc⟩ u v)
    hgood fun e he e' he' hR => by
      have hF : e.1.2 = e'.1.2 := congrArg Prod.fst hR
      have h3' := he'.2.2
      rw [← hF] at h3'
      exact intFn_eq_of_weyl he.1 he'.1 he.2.1 he'.2.1 he.2.2 h3' W (congrArg Prod.snd hR)
  rw [hZ₀law] at Hrep
  exact comap_comp_le_aeClosure (ι := fun p : S × (DyProd × DyProd) => ((p.1, Fb p.1), p.2))
    ((hΦ.comp measurable_fst).prodMk measurable_snd) Hrep

end L217

end LQGMetric.DFGPS
