import LatticeProb.Prob.AkcogluKrengelAE.BoxTiling
import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxErgodicProved
import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxMean

/-!
# The anchored-box and rectangle pointwise ergodic theorems

For a measure-preserving additive `ℤᵈ`-action `σ` on an ergodic probability space and a bounded
measurable `h`, the anchored-box averages `N⁻ᵈ ∑_{x ∈ ∏ᵢ [0, ⌈N cᵢ⌉)} h (σ x ω)` converge a.e.
to `(∏ᵢ cᵢ) ∫h`.

The box iteration `exists_ae_tendsto_boxAvg` produces a bounded measurable limit `G` invariant under
the unit shifts.  For `d ≥ 1` such a function is invariant under the whole action, since the
elements leaving it invariant form an additive subgroup containing the generators.  On an ergodic
space a measurable function that is a.e. invariant under every element of the action is a.e.
constant: its sublevel sets agree a.e. with the strictly invariant sets
`⋂_z σ_z⁻¹ {G ∈ U}`.  The integral identifies the constant.

## Main results

* `ergodicConstantLimit_holds`, `anchoredBoxLimitExists_holds`, `anchoredBoxLimitInvariant_holds`:
  the three steps of `anchoredBoxErgodic_of_steps`;
* `anchoredBoxErgodic_holds`, `rectangleErgodic_holds`: the anchored-box and rectangle theorems;
* `anchoredBoxDensityUpgradeCentred_holds`, `anchoredBoxDenseClass_holds`, `anchoredBoxMean_holds`:
  the corresponding inputs of `AnchoredBoxErgodic_of_MaximalMeanCentred`, the last one being the
  `Lᵖ` box mean ergodic theorem for `0 < p`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

omit [MeasurableSpace Ω] in
/-- For `d ≥ 1`, a function invariant under the unit shifts of an additive `ℤᵈ`-action is
invariant under every element of the action. -/
theorem comp_eq_of_comp_unit_eq {σ : Site d → Ω → Ω} (hd : 0 < d)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) {G : Ω → ℝ}
    (hG : ∀ j, G ∘ σ (unit j) = G) (z : Site d) : G ∘ σ z = G := by
  have h0 : G ∘ σ 0 = G := by
    funext ω
    have h1 := congrFun (hG ⟨0, hd⟩) (σ 0 ω)
    have h2 := congrFun (hG ⟨0, hd⟩) ω
    simp only [Function.comp_apply] at h1 h2 ⊢
    rw [← hσadd, add_zero] at h1
    rw [← h1]
    exact h2
  let H : AddSubgroup (Site d) :=
    { carrier := {z | G ∘ σ z = G}
      zero_mem' := h0
      add_mem' := by
        intro a b ha hb
        show G ∘ σ (a + b) = G
        funext ω
        simp only [Set.mem_ofPred_eq] at ha hb
        simp only [Function.comp_apply]
        rw [hσadd]
        exact (congrFun ha (σ b ω)).trans (congrFun hb ω)
      neg_mem' := by
        intro a ha
        show G ∘ σ (-a) = G
        funext ω
        simp only [Set.mem_ofPred_eq] at ha
        simp only [Function.comp_apply]
        rw [← congrFun ha (σ (-a) ω)]
        show G (σ a (σ (-a) ω)) = G ω
        rw [← hσadd, add_neg_cancel]
        exact congrFun h0 ω }
  have hz : z = ∑ j, z j • unit j := by
    ext k
    simp [unit, Finset.sum_apply, Pi.single_apply]
  have key : (∑ j, z j • unit j) ∈ H :=
    AddSubgroup.sum_mem H fun j _ => AddSubgroup.zsmul_mem H (hG j) (z j)
  rw [← hz] at key
  exact key

/-- On an ergodic probability space, a measurable function that is a.e. invariant under every
element of an additive `ℤᵈ`-action is a.e. constant. -/
theorem exists_ae_eq_const_of_ae_invariant {μ : Measure Ω} [IsProbabilityMeasure μ]
    {σ : Site d → Ω → Ω} (hσm : ∀ z, Measurable (σ z))
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    (herg : ∀ A : Set Ω, MeasurableSet A → (∀ z, σ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1)
    {G : Ω → ℝ} (hGm : Measurable G) (hinv : ∀ᵐ ω ∂μ, ∀ z : Site d, G (σ z ω) = G ω) :
    ∃ a : ℝ, G =ᵐ[μ] fun _ => a := by
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU => ?_
  set A : Set Ω := ⋂ z : Site d, σ z ⁻¹' (G ⁻¹' U) with hA
  have hAm : MeasurableSet A := MeasurableSet.iInter fun z => (hσm z) (hGm hU)
  have hAinv : ∀ w, σ w ⁻¹' A = A := by
    intro w
    ext ω
    simp only [hA, Set.mem_preimage, Set.mem_iInter]
    constructor
    · intro h z
      have := h (z - w)
      rwa [← hσadd, sub_add_cancel] at this
    · intro h z
      rw [← hσadd]
      exact h (z + w)
  have hAeq : A =ᵐ[μ] G ⁻¹' U := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hinv] with ω hω
    simp only [hA, Set.mem_preimage, Set.mem_iInter, hω, forall_const]
  rcases herg A hAm hAinv with h0 | h1
  · right
    have : μ (G ⁻¹' U) = 0 := (measure_congr hAeq).symm.trans h0
    exact measure_eq_zero_iff_ae_notMem.1 this
  · left
    have : μ (G ⁻¹' U) = 1 := (measure_congr hAeq).symm.trans h1
    exact ae_iff.2 ((prob_compl_eq_zero_iff (hGm hU)).2 this)

/-- **The constant-limit step holds.** -/
theorem ergodicConstantLimit_holds (d : ℕ) : ErgodicConstantLimit d := by
  intro Ω _ μ _ σ hσ hσadd herg h _hh M _hM _hb c _hc G hGm hGint hinv
  obtain ⟨a, ha⟩ :=
    exists_ae_eq_const_of_ae_invariant (fun z => (hσ z).measurable) hσadd herg hGm hinv
  have hai : a = ∫ ω, h ω ∂μ := by
    rw [← hGint, integral_congr_ae ha]
    simp
  filter_upwards [ha] with ω hω
  rw [hω, hai]

/-- **The box-iteration statement holds**: it is `exists_ae_tendsto_anchoredBox_with_integral`. -/
theorem anchoredBoxLimitExists_holds (d : ℕ) : AnchoredBoxLimitExists d := by
  intro Ω _ μ _ σ hσ hσadd h hh M hM hb c hc
  exact exists_ae_tendsto_anchoredBox_with_integral hσ hσadd hh hM hb hc

/-- For positive sides, the anchored-box averages of a bounded measurable `h` converge a.e. to
`(∏ᵢ cᵢ) · G` for a measurable `G` invariant under the unit shifts. -/
theorem exists_ae_tendsto_anchoredBox_unit_invariant {μ : Measure Ω} [IsProbabilityMeasure μ]
    {σ : Site d → Ω → Ω} (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    {c : Fin d → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ j, G ∘ σ (unit j) = G) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ anchoredBox c N, h (σ x ω)) atTop (𝓝 ((∏ i, c i) * G ω)) := by
  obtain ⟨G, hGm, _hGb, hGconv, hinv⟩ :=
    exists_ae_tendsto_boxAvg hσ hσadd hh hM hb Finset.univ
  refine ⟨G, hGm, fun j => hinv j (Finset.mem_univ j), ?_⟩
  have hc0 : ∀ i, 0 ≤ c i := fun i => (hc i).le
  have hmi : ∀ i, Tendsto (fun N : ℕ => ⌈(N : ℝ) * c i⌉.toNat) atTop atTop :=
    fun i => tendsto_ceil_toNat_atTop (hc i)
  have hconv := hGconv (fun N i => ⌈(N : ℝ) * c i⌉.toNat) (fun i _ => hmi i)
  have hscale : Tendsto (fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) *
      ((N : ℝ) ^ (-(d : ℝ)))) atTop (𝓝 (∏ i, c i)) := by
    have hlim := tendsto_prod_ceil_toNat_div_pow hc0
    have heq : (fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) *
        ((N : ℝ) ^ (-(d : ℝ)))) =
        fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) / (N : ℝ) ^ d := by
      funext N
      rw [Real.rpow_neg (Nat.cast_nonneg N) (d : ℝ), Real.rpow_natCast (N : ℝ) d,
        div_eq_mul_inv]
    rw [heq]
    exact hlim
  filter_upwards [hconv] with ω hω
  have heq : (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (σ x ω)) =
      fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) * ((N : ℝ) ^ (-(d : ℝ))) *
          boxAvg σ h Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω := by
    funext N
    rw [anchoredBox_eq_intBox hc0 N,
      ← sum_boxGridSet_eq_sum_intBox Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat)
          (fun x => h (σ x ω)),
      sum_boxGridSet_eq_boxAvg_mul σ h Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω]
    ring
  rw [heq]
  exact hscale.mul hω

/-- **The invariance step holds**: for positive sides, an a.e. limit `G` of the normalised
anchored-box averages is a.e. invariant under the action. -/
theorem anchoredBoxLimitInvariant_holds (d : ℕ) : AnchoredBoxLimitInvariant d := by
  intro Ω _ μ _ σ hσ hσadd h hh M hM hb c hc G _hGm _hGint hGconv
  obtain ⟨G₀, hG₀inv, hGG₀⟩ : ∃ G₀ : Ω → ℝ, (∀ z, G₀ ∘ σ z = G₀) ∧ G =ᵐ[μ] G₀ := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨fun ω => h (σ 0 ω), fun z => ?_, ?_⟩
      · funext ω
        simp only [Function.comp_apply]
        rw [Subsingleton.elim z 0, ← hσadd, add_zero]
      · have hbox : ∀ N : ℕ, ∀ ω, (N : ℝ) ^ (-((0 : ℕ) : ℝ)) *
            ∑ x ∈ anchoredBox c N, h (σ x ω) = h (σ 0 ω) := by
          intro N ω
          have hone : anchoredBox c N = {0} :=
            Finset.eq_singleton_iff_unique_mem.2
              ⟨mem_anchoredBox.2 fun i => i.elim0, fun x _ => Subsingleton.elim x 0⟩
          rw [hone, Finset.sum_singleton, Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul]
        filter_upwards [hGconv] with ω hω
        simp only [hbox, Finset.univ_eq_empty, Finset.prod_empty, one_mul] at hω
        exact tendsto_nhds_unique hω tendsto_const_nhds
    · obtain ⟨G₀, _, hG₀u, hG₀conv⟩ :=
        exists_ae_tendsto_anchoredBox_unit_invariant hσ hσadd hh hM hb hc
      refine ⟨G₀, comp_eq_of_comp_unit_eq hd hσadd hG₀u, ?_⟩
      have hprod : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hc i).ne'
      filter_upwards [hGconv, hG₀conv] with ω h1 h2
      exact mul_left_cancel₀ hprod (tendsto_nhds_unique h1 h2)
  rw [ae_all_iff]
  intro z
  have h1 : G ∘ σ z =ᵐ[μ] G₀ ∘ σ z := (hσ z).quasiMeasurePreserving.ae_eq_comp hGG₀
  filter_upwards [h1, hGG₀] with ω hω1 hω2
  calc G (σ z ω) = (G₀ ∘ σ z) ω := hω1
    _ = G₀ ω := congrFun (hG₀inv z) ω
    _ = G ω := hω2.symm

/-- **The anchored-box pointwise ergodic theorem.** -/
theorem anchoredBoxErgodic_holds (d : ℕ) : AnchoredBoxErgodic d :=
  anchoredBoxErgodic_of_steps (anchoredBoxLimitExists_holds d) (anchoredBoxLimitInvariant_holds d)
    (ergodicConstantLimit_holds d)

/-- **The rectangle pointwise ergodic theorem.** -/
theorem rectangleErgodic_holds (d : ℕ) : RectangleErgodic d :=
  RectangleErgodic_of_AnchoredBox (anchoredBoxErgodic_holds d)

/-- The density upgrade holds: its conclusion is the anchored-box ergodic theorem. -/
theorem anchoredBoxDensityUpgradeCentred_holds (c : Fin d → ℝ) (p : ℝ) :
    AnchoredBoxDensityUpgradeCentred d c p := by
  intro hc _hp Ω _ μ _ τ hτ hadd herg _Hmax _Hdense h hh hb
  exact anchoredBoxErgodic_holds d μ τ hτ hadd herg h hh hb c hc

/-- The dense class holds for `0 < p`, with the class of all bounded measurable functions. -/
theorem anchoredBoxDenseClass_holds (c : Fin d → ℝ) {p : ℝ} (hp : 0 < p) :
    AnchoredBoxDenseClass d c p := by
  intro hc Ω _ μ _ τ hτ hadd herg
  refine ⟨{g | Measurable g ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |g x| ≤ M}, fun g hg => hg.1, ?_, ?_⟩
  · intro g hg
    filter_upwards [anchoredBoxErgodic_holds d μ τ hτ hadd herg g hg.1 hg.2 c hc] with ω hω
    have hs := hω.sub_const ((∏ i, c i) * ∫ ω, g ω ∂μ)
    rw [sub_self] at hs
    exact hs
  · intro h hh hb ε hε
    refine ⟨h, ⟨hh, hb⟩, ?_⟩
    simp [ENNReal.zero_rpow_of_pos hp, hε]

/-- The cardinality of the anchored box is `∏ᵢ ⌈N cᵢ⌉₊`. -/
theorem card_anchoredBox (c : Fin d → ℝ) (N : ℕ) :
    ((anchoredBox c N).card : ℝ) = ∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ) := by
  simp [anchoredBox, Fintype.card_piFinset, Int.card_Ico]

/-- **The `Lᵖ` box mean ergodic theorem** for `0 < p`, by dominated convergence from the
pointwise theorem. -/
theorem anchoredBoxMean_holds (c : Fin d → ℝ) {p : ℝ} (hp : 0 < p) : AnchoredBoxMean d c p := by
  intro hc Ω _ μ _ τ hτ hadd herg h hh hb
  obtain ⟨M, hM, hMb⟩ := hb
  have hae := anchoredBoxErgodic_holds d μ τ hτ hadd herg h hh ⟨M, hM, hMb⟩ c hc
  set m : ℝ := (∏ i, c i) * ∫ ω, h ω ∂μ with hm
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) * ((anchoredBox c N).card : ℝ))
      atTop (𝓝 (∏ i, c i)) := by
    have hlim := tendsto_prod_ceil_toNat_div_pow hc
    refine hlim.congr fun N => ?_
    rw [card_anchoredBox, Real.rpow_neg (Nat.cast_nonneg N) (d : ℝ), Real.rpow_natCast (N : ℝ) d,
      div_eq_mul_inv, mul_comm]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hscale.eventually (ge_mem_nhds (lt_add_one _)))
  set K : ℝ := M * ((∏ i, c i) + 1) + |m| with hK
  have hbound : ∀ N, N₀ ≤ N → ∀ ω, |anchoredBoxAvgMean h τ c N ω - m| ≤ K := by
    intro N hN ω
    have hA : |anchoredBoxAvgMean h τ c N ω| ≤ M * ((∏ i, c i) + 1) := by
      unfold anchoredBoxAvgMean
      have hpow : 0 ≤ (N : ℝ) ^ (-(d : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hsum : |∑ x ∈ anchoredBox c N, h (τ x ω)| ≤ ((anchoredBox c N).card : ℝ) * M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun x _ => hMb (τ x ω)).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [abs_mul, abs_of_nonneg hpow]
      calc (N : ℝ) ^ (-(d : ℝ)) * |∑ x ∈ anchoredBox c N, h (τ x ω)|
          ≤ (N : ℝ) ^ (-(d : ℝ)) * (((anchoredBox c N).card : ℝ) * M) :=
            mul_le_mul_of_nonneg_left hsum hpow
        _ = M * ((N : ℝ) ^ (-(d : ℝ)) * ((anchoredBox c N).card : ℝ)) := by ring
        _ ≤ M * ((∏ i, c i) + 1) := mul_le_mul_of_nonneg_left (hN₀ N hN) hM
    calc |anchoredBoxAvgMean h τ c N ω - m| ≤ |anchoredBoxAvgMean h τ c N ω| + |m| :=
          abs_sub _ _
      _ ≤ K := by rw [hK]; linarith
  have hmeas : ∀ N, Measurable fun ω =>
      (ENNReal.ofReal |anchoredBoxAvgMean h τ c (N + N₀) ω - m|) ^ p := fun N =>
    ((((measurable_anchoredBoxAvgMean hh (fun z => (hτ z).measurable) c (N + N₀)).sub_const
      m).abs).ennreal_ofReal).pow_const p
  have hshift : Tendsto (fun N : ℕ => ∫⁻ ω, (ENNReal.ofReal
      |anchoredBoxAvgMean h τ c (N + N₀) ω - m|) ^ p ∂μ) atTop (𝓝 0) := by
    have hdom := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (fun _ => (ENNReal.ofReal K) ^ p) hmeas
      (fun N => Eventually.of_forall fun ω =>
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hbound (N + N₀) (by omega) ω)) hp.le)
      (by
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      (f := fun _ => 0)
      (by
        filter_upwards [hae] with ω hω
        have h1 : Tendsto (fun N : ℕ => anchoredBoxAvgMean h τ c (N + N₀) ω - m) atTop
            (𝓝 0) := by
          have hs := ((tendsto_add_atTop_iff_nat N₀).2 hω).sub_const m
          rw [sub_self] at hs
          exact hs
        have h2 := ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
          ((ENNReal.continuous_ofReal.tendsto _).comp (h1.abs))
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp] using h2)
    simpa using hdom
  exact (tendsto_add_atTop_iff_nat N₀).1 hshift

end LatticeProb
