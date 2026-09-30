import LatticeProb.Prob.Strassen.LevelCoupling

/-!
# F. Passage to the limit

`ProbabilityMeasure ((S → Bool)²)` is compact (Mathlib `instCompactSpaceProbabilityMeasure`,
Prokhorov), so the level-`F_N` couplings of stage E, along an exhausting sequence `F_N ↑ S` with
`D_N = (N+1) |P_{F_N}|`, have a limit point `P₀` along an ultrafilter refining `atTop`. The closed
support set `couplingSupport S` passes to the limit by portmanteau
(`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), clopen cylinder masses pass by
`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`, and cylinders form a generating
π-system (`generateFrom_measurableCylinders`, `isPiSystem_measurableCylinders`) that pins down
both marginals of `P₀`. This assembles into **Strassen's theorem**
(`exists_coupling_of_domination`, restated as `exists_monotone_coupling`).
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- A countable `S` has an exhausting sequence of finsets `F : ℕ → Finset S`: every finset `G` is
contained in `F N` for all large `N`. -/
private theorem exists_finset_forall_subset_of_countable {S : Type} [Countable S] :
    ∃ F : ℕ → Finset S, ∀ G : Finset S, ∃ N0, ∀ N, N0 ≤ N → G ⊆ F N := by
  classical
  letI := Encodable.ofCountable S
  refine ⟨fun N => (Finset.range N).preimage Encodable.encode
      (Encodable.encode_injective.injOn), ?_⟩
  intro G
  refine ⟨G.sup Encodable.encode + 1, fun N hN => ?_⟩
  intro x hx
  rw [Finset.mem_preimage, Finset.mem_range]
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup hx)) hN


/-- `couplingSupport S` is the intersection, over `s`, of the preimages of `{(a, b) | b = true → a =
true}` under the `s`-coordinate maps. -/
private theorem couplingSupport_eq_iInter_preimage (S : Type) :
    couplingSupport S = ⋂ s : S,
      (fun p : (S → Bool) × (S → Bool) => (p.1 s, p.2 s)) ⁻¹'
        {q : Bool × Bool | q.2 = true → q.1 = true} := by
  ext p
  simp [couplingSupport]

/-- `couplingSupport S` is closed. -/
private theorem isClosed_couplingSupport (S : Type) : IsClosed (couplingSupport S) := by
  rw [couplingSupport_eq_iInter_preimage S]
  exact isClosed_iInter fun s =>
    IsClosed.preimage
      (Continuous.prodMk ((continuous_apply s).comp continuous_fst)
        ((continuous_apply s).comp continuous_snd)) (isClosed_discrete _)


/-- Every measurable cylinder set is clopen. -/
private theorem isClopen_of_mem_measurableCylinders {S : Type} (C : Set (S → Bool))
    (hC : C ∈ measurableCylinders (fun _ : S => Bool)) : IsClopen C := by
  obtain ⟨s, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hC
  haveI : DiscreteTopology (↥s → Bool) := Pi.discreteTopology
  exact IsClopen.preimage (isClopen_discrete T) (Finset.continuous_restrict s)


/-- By compactness of the space of probability measures, every sequence `Ps` has a subsequential
limit along some ultrafilter refining `atTop`. -/
private theorem exists_ultrafilter_tendsto_of_compactSpace_probabilityMeasure {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] [CompactSpace (ProbabilityMeasure Y)]
    (Ps : ℕ → ProbabilityMeasure Y) :
    ∃ (U : Ultrafilter ℕ) (P₀ : ProbabilityMeasure Y),
      (U : Filter ℕ) ≤ atTop ∧ Tendsto Ps (U : Filter ℕ) (𝓝 P₀) := by
  obtain ⟨P₀, -, hP₀⟩ := isCompact_univ.ultrafilter_le_nhds
    (Ultrafilter.map Ps (Ultrafilter.of atTop)) (by rw [le_principal_iff]; exact Filter.univ_mem)
  refine ⟨Ultrafilter.of atTop, P₀, Ultrafilter.of_le atTop, ?_⟩
  rw [Ultrafilter.coe_map] at hP₀
  exact hP₀


/-- If `Ps n K = 1` for every `n` and `Ps` tends to `P₀` along an ultrafilter, on a closed set `K`,
then `P₀ K = 1`. -/
private theorem apply_eq_one_of_tendsto_of_forall_apply_eq_one {Y : Type*} [MeasurableSpace Y]
    [TopologicalSpace Y]
    [OpensMeasurableSpace Y] [HasOuterApproxClosed Y] (U : Ultrafilter ℕ)
    (Ps : ℕ → ProbabilityMeasure Y) (P₀ : ProbabilityMeasure Y)
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀)) (K : Set Y) (hK : IsClosed K)
    (h1 : ∀ n, Ps n K = 1) : P₀ K = 1 := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hK
  have hfn : (fun i : ℕ => ((Ps i : ProbabilityMeasure Y) : Measure Y) K)
      = (fun _ : ℕ => (1 : ENNReal)) :=
    funext (fun n =>
      ((ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (Ps n) K).symm).trans
        ((congrArg (fun r : NNReal => (r : ENNReal)) (h1 n)).trans ENNReal.coe_one))
  rw [hfn, limsup_const] at h
  exact le_antisymm (ProbabilityMeasure.apply_le_one P₀ K)
    (ENNReal.coe_le_coe.mp (by simpa using h))


/-- If `Ps n E → c` along `atTop` and `Ps` tends to `P₀` along a finer ultrafilter, on a clopen set
`E`, then `P₀ E = c`. -/
private theorem apply_eq_of_isClopen_of_tendsto {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] [HasOuterApproxClosed Y] (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop)
    (Ps : ℕ → ProbabilityMeasure Y) (P₀ : ProbabilityMeasure Y)
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀)) (E : Set Y) (hE : IsClopen E) (c : NNReal)
    (hc : Tendsto (fun n => Ps n E) atTop (𝓝 c)) : P₀ E = c := by
  exact tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hlim hE) (hc.mono_left hU)


/-- If `π (C ×ˢ univ) = μ C` for every measurable cylinder `C`, then the first marginal of `π` is
`μ`. -/
private theorem map_fst_eq_of_forall_apply_prod_univ_eq {S : Type}
    (π : Measure ((S → Bool) × (S → Bool)))
    [IsProbabilityMeasure π] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (h : ∀ C ∈ measurableCylinders (fun _ : S => Bool), π (C ×ˢ Set.univ) = μ C) :
    π.map Prod.fst = μ := by
  haveI : IsFiniteMeasure (π.map Prod.fst) := inferInstance
  refine ext_of_generate_finite (measurableCylinders (fun _ : S => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    rw [Measure.map_apply measurable_fst (MeasurableSet.of_mem_measurableCylinders hC),
      ← Set.prod_univ]
    exact h C hC
  · rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    simp


/-- If `π (univ ×ˢ C) = ν C` for every measurable cylinder `C`, then the second marginal of `π` is
`ν`. -/
private theorem map_snd_eq_of_forall_apply_univ_prod_eq {S : Type}
    (π : Measure ((S → Bool) × (S → Bool)))
    [IsProbabilityMeasure π] (ν : Measure (S → Bool)) [IsProbabilityMeasure ν]
    (h : ∀ C ∈ measurableCylinders (fun _ : S => Bool), π (Set.univ ×ˢ C) = ν C) :
    π.map Prod.snd = ν := by
  refine ext_of_generate_finite (measurableCylinders (fun _ : S => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    rw [Measure.map_apply measurable_snd (MeasurableSet.of_mem_measurableCylinders hC),
      ← Set.univ_prod]
    exact h C hC
  · rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ,
      measure_univ, measure_univ]


/-- An NNReal sequence within `e N` of `c`, with `e → 0`, tends to `c`. -/
private theorem tendsto_of_forall_abs_sub_le_of_tendsto_zero (x : ℕ → NNReal) (c : NNReal)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hx : ∀ᶠ N in atTop, |(x N : ℝ) - c| ≤ e N) : Tendsto x atTop (𝓝 c) := by
  rw [← NNReal.tendsto_coe]
  refine (tendsto_iff_norm_sub_tendsto_zero).mpr ?_
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      (hx.mono fun N hN => le_trans hN (le_abs_self _)) (by simpa using he.abs)


/-- The error sequence `card P_N / ((N + 1) * card P_N)` tends to `0`. -/
private theorem tendsto_div_card_mul_add_one_atTop_zero (c : ℕ → ℕ) (hc : ∀ N, 0 < c N) :
    Tendsto (fun N => (c N : ℝ) / ((N + 1) * c N : ℕ)) atTop (𝓝 0) := by
  have hcN : ∀ N : ℕ, (c N : ℝ) ≠ 0 := fun N => Nat.cast_ne_zero.mpr (ne_of_gt (hc N))
  have hfun : ∀ N : ℕ, (c N : ℝ) / ((N + 1) * c N : ℕ) = 1 / ((N : ℝ) + 1) := fun N => by
    have h1 : (↑(c N) : ℝ) ≠ 0 := hcN N
    push_cast
    field_simp
  simp only [hfun]
  exact tendsto_one_div_add_atTop_nhds_zero_nat


/-- Restates a probability measure's value `P A = r` as the value `(P : Measure Ω) A = r` of its
underlying measure. -/
private theorem coe_apply_eq_of_apply_eq {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (A : Set Ω) (r : NNReal) (h : P A = r) : (P : Measure Ω) A = (r : ENNReal) := by
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P A, h]

/-- In the limit along the ultrafilter, the first-coordinate mass of `P₀` on `cylinder G T ×ˢ univ`
equals `μ (cylinder G T)`, from clopenness and convergence of the approximating marginals. -/
private theorem apply_cylinder_prod_univ_eq_measure_of_tendsto {S : Type} [Countable S]
    (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (P₀ : ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀))
    (hfst : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (C ×ˢ Set.univ)) atTop (𝓝 (μ C).toNNReal))
    (G : Finset S) (T : Set (G → Bool)) (hT : MeasurableSet T) :
    (↑P₀ : Measure ((S → Bool) × (S → Bool)))
        ((cylinder (α := fun _ : S => Bool) G T) ×ˢ (Set.univ : Set (S → Bool)))
      = μ (cylinder (α := fun _ : S => Bool) G T) := by
  have hmem : (cylinder (α := fun _ : S => Bool) G T) ∈ measurableCylinders (fun _ : S => Bool) :=
    (mem_measurableCylinders _).mpr ⟨G, T, hT, rfl⟩
  have hE : IsClopen ((cylinder (α := fun _ : S => Bool) G T) ×ˢ (Set.univ : Set (S → Bool))) :=
    IsClopen.prod (isClopen_of_mem_measurableCylinders _ hmem) isClopen_univ
  have hfront : P₀
      (frontier ((cylinder (α := fun _ : S => Bool) G T) ×ˢ (Set.univ : Set (S → Bool)))) = 0 := by
    rw [hE.frontier_eq]
    simp
  have h1 : Tendsto (fun N => Ps N ((cylinder (α := fun _ : S => Bool) G T) ×ˢ Set.univ))
      (U : Filter ℕ)
      (𝓝 ((μ (cylinder (α := fun _ : S => Bool) G T)).toNNReal)) :=
    (hfst _ hmem).mono_left hU
  have h2 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hlim hfront
  have h3 : P₀ ((cylinder (α := fun _ : S => Bool) G T) ×ˢ Set.univ)
      = (μ (cylinder (α := fun _ : S => Bool) G T)).toNNReal := tendsto_nhds_unique h2 h1
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P₀
      ((cylinder (α := fun _ : S => Bool) G T) ×ˢ Set.univ), h3,
    ENNReal.coe_toNNReal (measure_ne_top μ _)]

/-- In the limit along the ultrafilter, the second-coordinate mass of `P₀` on `univ ×ˢ cylinder G T`
equals `ν (cylinder G T)`. -/
private theorem apply_univ_prod_cylinder_eq_measure_of_tendsto {S : Type} [Countable S]
    (ν : Measure (S → Bool)) [IsProbabilityMeasure ν]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (P₀ : ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀))
    (hsnd : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (Set.univ ×ˢ C)) atTop (𝓝 (ν C).toNNReal))
    (G : Finset S) (T : Set (G → Bool)) (hT : MeasurableSet T) :
    (↑P₀ : Measure ((S → Bool) × (S → Bool)))
        ((Set.univ : Set (S → Bool)) ×ˢ (cylinder (α := fun _ : S => Bool) G T))
      = ν (cylinder (α := fun _ : S => Bool) G T) := by
  have hmem : (cylinder (α := fun _ : S => Bool) G T) ∈ measurableCylinders (fun _ : S => Bool) :=
    (mem_measurableCylinders _).mpr ⟨G, T, hT, rfl⟩
  have hE : IsClopen ((Set.univ : Set (S → Bool)) ×ˢ (cylinder (α := fun _ : S => Bool) G T)) :=
    IsClopen.prod isClopen_univ (isClopen_of_mem_measurableCylinders _ hmem)
  have hfront : P₀
      (frontier ((Set.univ : Set (S → Bool)) ×ˢ (cylinder (α := fun _ : S => Bool) G T))) = 0 := by
    rw [hE.frontier_eq]
    simp
  have h1 : Tendsto (fun N => Ps N (Set.univ ×ˢ (cylinder (α := fun _ : S => Bool) G T)))
      (U : Filter ℕ)
      (𝓝 ((ν (cylinder (α := fun _ : S => Bool) G T)).toNNReal)) :=
    (hsnd _ hmem).mono_left hU
  have h2 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hlim hfront
  have h3 : P₀ (Set.univ ×ˢ (cylinder (α := fun _ : S => Bool) G T))
      = (ν (cylinder (α := fun _ : S => Bool) G T)).toNNReal := tendsto_nhds_unique h2 h1
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P₀
      (Set.univ ×ˢ (cylinder (α := fun _ : S => Bool) G T)), h3,
    ENNReal.coe_toNNReal (measure_ne_top ν _)]

/-- The limit measure `P₀` puts full mass on the closed set `couplingSupport S`, since every
approximating `Ps N` does. -/
private theorem apply_couplingSupport_eq_one_of_tendsto {S : Type} [Countable S]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hK : IsClosed (couplingSupport S))
    (hsupp : ∀ N, (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)ᶜ = 0)
    (U : Ultrafilter ℕ) (P₀ : ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀)) :
    (↑P₀ : Measure ((S → Bool) × (S → Bool))) (couplingSupport S) = 1 := by
  have hPsK : ∀ N, (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S) =
      (1 : ENNReal) :=
    fun N =>
        (prob_compl_eq_zero_iff (μ := (↑(Ps N) : Measure ((S → Bool) × (S → Bool))))
          hK.measurableSet).mp (hsupp N)
  have hlimsup : limsup
      (fun N => (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)) (U : Filter ℕ) =
          (1 : ENNReal) := by
    rw [show (fun N => (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S))
        = fun _ => (1 : ENNReal) from funext hPsK,
      limsup_const]
  have hle : (1 : ENNReal) ≤ (↑P₀ : Measure ((S → Bool) × (S → Bool))) (couplingSupport S) := by
    have hmain := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hK
    rwa [hlimsup] at hmain
  refine le_antisymm ?_ hle
  calc (↑P₀ : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)
      = ((P₀ (couplingSupport S) : NNReal) : ENNReal) :=
          (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P₀ _).symm
    _ ≤ ((1 : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr (ProbabilityMeasure.apply_le_one P₀ _)
    _ = 1 := by norm_num

/-- Assembling the ultrafilter limit: if the `Ps N` all avoid the complement of `couplingSupport S`
and the marginals converge cylinder-by-cylinder to `μ` and `ν`, there is a probability measure `π`
with marginals `μ`, `ν`, supported a.e. on `couplingSupport S`. -/
private theorem exists_coupling_of_tendsto_marginals {S : Type} [Countable S]
    (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hsupp : ∀ N, (Ps N : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)ᶜ = 0)
    (hfst : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (C ×ˢ Set.univ)) atTop (𝓝 (μ C).toNNReal))
    (hsnd : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (Set.univ ×ˢ C)) atTop (𝓝 (ν C).toNNReal)) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true := by
  classical
  obtain ⟨U, P₀, hU, hlim⟩ := exists_ultrafilter_tendsto_of_compactSpace_probabilityMeasure Ps
  have hK : IsClosed (couplingSupport S) := isClosed_couplingSupport S
  refine ⟨(↑P₀ : Measure ((S → Bool) × (S → Bool))), inferInstance, ?_, ?_, ?_⟩
  · refine map_fst_eq_of_forall_apply_prod_univ_eq _ μ ?_
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    exact apply_cylinder_prod_univ_eq_measure_of_tendsto μ Ps U hU P₀ hlim hfst G T hT
  · refine map_snd_eq_of_forall_apply_univ_prod_eq _ ν ?_
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    exact apply_univ_prod_cylinder_eq_measure_of_tendsto ν Ps U hU P₀ hlim hsnd G T hT
  · rw [ae_iff]
    exact
        (prob_compl_eq_zero_iff (μ := (↑P₀ : Measure ((S → Bool) × (S → Bool))))
          hK.measurableSet).mpr
      (apply_couplingSupport_eq_one_of_tendsto Ps hK hsupp U P₀ hlim)


/-- **Strassen's theorem** for `{0,1}`-valued fields on a countable set, in the domination form of
the Exploding externals: if every measurable increasing event is at least as likely under `μ` as
under `ν`, then there is a coupling whose first coordinate (law `μ`) dominates its second (law `ν`)
pointwise almost surely. -/
theorem exists_coupling_of_domination {S : Type} [Countable S] (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true := by
  obtain ⟨F, hF⟩ := exists_finset_forall_subset_of_countable (S := S)
  choose π hπprob hπsupp hπcyl using fun N : ℕ =>
    exists_cplMeasure_of_domination (μ := μ) (ν := ν) hdom (F N)
        ((N + 1) * Fintype.card (F N → Bool))
      (Nat.pos_iff_ne_zero.mp (by positivity))
  let Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)) := fun N => ⟨π N, hπprob N⟩
  have hfst : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (C ×ˢ Set.univ)) atTop (𝓝 (μ C).toNNReal) := by
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    obtain ⟨N0, hN0⟩ := hF G
    refine tendsto_of_forall_abs_sub_le_of_tendsto_zero _ _ _
      (tendsto_div_card_mul_add_one_atTop_zero (fun N => Fintype.card (F N → Bool))
        fun N => Fintype.card_pos) ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    have hb := (hπcyl N G (hN0 N hN) T hT).1
    have h1 : ((Ps N) (cylinder G T ×ˢ Set.univ) : ℝ)
        = ((π N) (cylinder G T ×ˢ Set.univ)).toReal := rfl
    have h2 : ((μ (cylinder G T)).toNNReal : ℝ) = (μ (cylinder G T)).toReal := rfl
    rw [h1, h2]
    exact hb
  have hsnd : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (Set.univ ×ˢ C)) atTop (𝓝 (ν C).toNNReal) := by
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    obtain ⟨N0, hN0⟩ := hF G
    refine tendsto_of_forall_abs_sub_le_of_tendsto_zero _ _ _
      (tendsto_div_card_mul_add_one_atTop_zero (fun N => Fintype.card (F N → Bool))
        fun N => Fintype.card_pos) ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    have hb := (hπcyl N G (hN0 N hN) T hT).2
    have h1 : ((Ps N) (Set.univ ×ˢ cylinder G T) : ℝ)
        = ((π N) (Set.univ ×ˢ cylinder G T)).toReal := rfl
    have h2 : ((ν (cylinder G T)).toNNReal : ℝ) = (ν (cylinder G T)).toReal := rfl
    rw [h1, h2]
    exact hb
  exact exists_coupling_of_tendsto_marginals μ ν Ps (fun N => hπsupp N) hfst hsnd

/-- Restates `exists_coupling_of_domination` under the name used by the percolation literature. -/
theorem exists_monotone_coupling {S : Type} [Countable S] (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true := by
  exact exists_coupling_of_domination μ ν hdom

end StrassenAux

end LatticeProb
