import LatticeProb.Prob.Percolation.LSS.Thin

/-!
# Finite-coordinate domination and projective limits of Bernoulli fields

The finite-coordinate form of the product law: on a finite set of coordinates the product
measure of a finite set is the sum of the weights of its elements. This is the building block
for the finite-coordinate domination step of the bounded-degree theorem.

Compactness of the cylinder content: on `ι → Bool` the measurable cylinders are clopen, so a
decreasing sequence of them with empty intersection is eventually empty. This is the
continuity-at-empty step that makes the projective family content sigma-subadditive, and hence
gives the projective limit measure through Carathéodory's extension theorem.

Ported from the Exploding-Sandpiles formalization, `Support/ExtLSSProofDom.lean` and
`Support/ExtLSSProofContent.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb.Percolation.LSS

variable {S : Type}


/-- The finite product of probability measures on `ι → Bool`, evaluated on a finite set, as the
sum of the weights of its elements. -/
theorem xlss_pi_eq_sum {ι : Type*} [Fintype ι] (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (B : Finset (ι → Bool)) :
    Measure.pi μ ((B : Set (ι → Bool))) = ∑ x ∈ B, ∏ i, μ i {x i} := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    rw [Finset.coe_insert, Finset.sum_insert ha]
    have hins : (insert a (↑B : Set (ι → Bool))) = ({a} : Set (ι → Bool)) ∪ (↑B : Set _) :=
      Set.insert_eq a (↑B : Set (ι → Bool))
    rw [hins, measure_union (by rw [Set.disjoint_singleton_left]; exact ha)
      B.finite_toSet.measurableSet, Measure.pi_singleton, ih]

/-- The `ENNReal` form of the thinning's normalisation. -/
theorem xlss_thin_norm_ofReal [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (T : Finset S) (w : S → Bool → Finset S → ℝ) (hw : XlssThin μ ρ γ T w)
    (x : S → Bool) :
    ∑ V ∈ T.powerset, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) = 1 := by
  rw [← ENNReal.ofReal_one, ← hw.norm x]
  rw [ENNReal.ofReal_sum_of_nonneg]
  exact fun V hV => Finset.prod_nonneg fun l hl => (hw.bd l hl V (Finset.mem_powerset.mp hV) _).1

/-- The `ENNReal` form of the thinning's marginal law. -/
theorem xlss_thin_marg_ofReal [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (T : Finset S) (w : S → Bool → Finset S → ℝ) (hw : XlssThin μ ρ γ T w)
    (V : Finset S) (hV : V ⊆ T) :
    ∫⁻ x, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ =
      ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (xlss_integrable_prod μ T (fun l b => w l b V) (fun l hl => hw.bd l hl V hV))
    (Filter.Eventually.of_forall fun x =>
      Finset.prod_nonneg fun l hl => (hw.bd l hl V hV _).1)]
  rw [hw.marg V hV]

/-- The subset of `T` carved out by a `T`-indexed bit configuration. -/
def xlss_Vof (T : Finset S) (v : T → Bool) : Finset S :=
  (Finset.univ.filter (fun t : T => v t = true)).map
    (Function.Embedding.subtype (fun s : S => s ∈ T))

theorem xlss_Vof_subset (T : Finset S) (v : T → Bool) : xlss_Vof T v ⊆ T := by
  intro s hs
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hs
  exact t.2

theorem xlss_mem_Vof (T : Finset S) (v : T → Bool) (s : S) :
    s ∈ xlss_Vof T v ↔ ∃ hs : s ∈ T, v ⟨s, hs⟩ = true := by
  rw [xlss_Vof, Finset.mem_map]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [Finset.mem_filter] at ht
    refine ⟨hts ▸ t.2, ?_⟩
    have ht' : (⟨s, hts ▸ t.2⟩ : T) = t := Subtype.ext hts.symm
    rw [ht']
    exact ht.2
  · rintro ⟨hs, hv⟩
    exact ⟨⟨s, hs⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv⟩, rfl⟩

theorem xlss_Vof_injective (T : Finset S) : Function.Injective (xlss_Vof T) := by
  intro v v' h
  funext t
  have h1 : v t = true ↔ (t : S) ∈ xlss_Vof T v := by
    rw [xlss_mem_Vof]
    exact ⟨fun hv => ⟨t.2, hv⟩, fun ⟨hs, hv⟩ => by
      have : (⟨(t : S), hs⟩ : T) = t := Subtype.ext rfl
      rwa [this] at hv⟩
  have h2 : v' t = true ↔ (t : S) ∈ xlss_Vof T v' := by
    rw [xlss_mem_Vof]
    exact ⟨fun hv => ⟨t.2, hv⟩, fun ⟨hs, hv⟩ => by
      have : (⟨(t : S), hs⟩ : T) = t := Subtype.ext rfl
      rwa [this] at hv⟩
  have hmem : (t : S) ∈ xlss_Vof T v ↔ (t : S) ∈ xlss_Vof T v' := by rw [h]
  have hiff : (v t = true) ↔ (v' t = true) := h1.trans (hmem.trans h2.symm)
  cases hvt : v t <;> cases hv't : v' t <;> simp_all

theorem xlss_Vof_surjective (T : Finset S) :
    ∀ V ∈ T.powerset, ∃ v : T → Bool, xlss_Vof T v = V := by
  classical
  intro V hV
  refine ⟨fun t => decide ((t : S) ∈ V), ?_⟩
  ext s
  rw [xlss_mem_Vof]
  constructor
  · rintro ⟨_, hv⟩
    simpa using hv
  · intro hsV
    exact ⟨Finset.mem_powerset.mp hV hsV, by rw [decide_eq_true_iff]; exact hsV⟩

/-- A bit configuration on `T` is equivalent to the subset of `T` that it occupies. -/
noncomputable def xlss_VofEquiv (T : Finset S) :
    (T → Bool) ≃ {V : Finset S // V ∈ T.powerset} where
  toFun v := ⟨xlss_Vof T v, Finset.mem_powerset.mpr (xlss_Vof_subset T v)⟩
  invFun V := Classical.choose (xlss_Vof_surjective T V.1 V.2)
  left_inv v := xlss_Vof_injective T (Classical.choose_spec
    (xlss_Vof_surjective T (xlss_Vof T v) (Finset.mem_powerset.mpr (xlss_Vof_subset T v))))
  right_inv V := Subtype.ext (Classical.choose_spec (xlss_Vof_surjective T V.1 V.2))

/-- Reindexing a sum over the powerset of `T` as a sum over `T`-bit configurations. -/
theorem xlss_sum_Vof [DecidableEq S] (T : Finset S) (g : Finset S → ENNReal) :
    ∑ v : T → Bool, g (xlss_Vof T v) = ∑ V ∈ T.powerset, g V := by
  classical
  rw [← Finset.sum_attach T.powerset g]
  exact (xlss_VofEquiv T).sum_comp (fun V : {V : Finset S // V ∈ T.powerset} => g V.1)

/-- The cardinality of the occupied subset. -/
theorem xlss_card_Vof [DecidableEq S] (T : Finset S) (v : T → Bool) :
    (xlss_Vof T v).card = (Finset.univ.filter (fun t : T => v t = true)).card := by
  rw [xlss_Vof, Finset.card_map]

/-- The product of one-site Bernoulli masses of a bit configuration. -/
theorem xlss_bitLaw_prod [DecidableEq S] (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : Finset S) (v : T → Bool) :
    ∏ t : T, bitLaw ρ {v t} =
      ENNReal.ofReal (ρ ^ (xlss_Vof T v).card *
        (1 - ρ) ^ (T.card - (xlss_Vof T v).card)) := by
  classical
  have hbit : ∀ b : Bool,
      bitLaw ρ {b} = if b then ENNReal.ofReal ρ else ENNReal.ofReal (1 - ρ) := by
    intro b
    cases b <;> simp [bitLaw]
  simp only [hbit]
  have hite : ∀ t : T, (if v t then ENNReal.ofReal ρ else ENNReal.ofReal (1 - ρ)) =
      ENNReal.ofReal (if v t then ρ else 1 - ρ) := by
    intro t
    split_ifs <;> rfl
  simp_rw [hite]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [xlss_card_Vof, Finset.prod_ite,
      Finset.prod_eq_pow_card (fun _ _ => rfl),
      Finset.prod_eq_pow_card (fun _ _ => rfl)]
    have hcard : (Finset.univ.filter (fun t : T => v t = true)).card +
        (Finset.univ.filter (fun t : T => ¬ (v t = true))).card = T.card := by
      rw [Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun t : T => v t = true), Finset.card_univ, Fintype.card_coe]
    have hsub : (Finset.univ.filter (fun t : T => ¬ (v t = true))).card =
        T.card - (Finset.univ.filter (fun t : T => v t = true)).card := by omega
    rw [hsub]
  · intro t _
    split_ifs
    · exact hρ0
    · linarith

/-- The indicator of the occupied subset restricts back to the configuration. -/
theorem xlss_rest_ind_Vof [DecidableEq S] (T : Finset S) (v : T → Bool) :
    T.restrict (fun s => decide (s ∈ xlss_Vof T v)) = v := by
  funext t
  have h : ((t : S) ∈ xlss_Vof T v) ↔ v t = true := by
    rw [xlss_mem_Vof]
    constructor
    · rintro ⟨hs, hv⟩
      have : (⟨(t : S), hs⟩ : T) = t := Subtype.ext rfl
      rwa [this] at hv
    · intro hv
      exact ⟨t.2, hv⟩
  show decide ((t : S) ∈ xlss_Vof T v) = v t
  by_cases hv : v t = true
  · have ht : (t : S) ∈ xlss_Vof T v := h.mpr hv
    simp [hv, ht]
  · have ht : ¬ ((t : S) ∈ xlss_Vof T v) := fun hc => hv (h.mp hc)
    have hv' : v t = false := by cases h' : v t <;> simp_all
    simp [hv', ht]

/-- The projection of a `T`-determined set is the set of configurations whose occupied subset
belongs to the set. -/
theorem xlss_mem_proj [DecidableEq S] (T : Finset S) (A : Set (S → Bool))
    (hdet : ∀ x y, (∀ t ∈ T, x t = y t) → (x ∈ A ↔ y ∈ A)) (v : T → Bool) :
    v ∈ T.restrict '' A ↔ (fun s => decide (s ∈ xlss_Vof T v)) ∈ A := by
  constructor
  · rintro ⟨x, hxA, hxv⟩
    refine (hdet x (fun s => decide (s ∈ xlss_Vof T v)) ?_).mp hxA
    intro t ht
    calc x t = T.restrict x ⟨t, ht⟩ := rfl
      _ = v ⟨t, ht⟩ := congrFun hxv ⟨t, ht⟩
      _ = T.restrict (fun s => decide (s ∈ xlss_Vof T v)) ⟨t, ht⟩ :=
          (congrFun (xlss_rest_ind_Vof T v) ⟨t, ht⟩).symm
      _ = (fun s => decide (s ∈ xlss_Vof T v)) t := rfl
  · rintro hv
    exact ⟨fun s => decide (s ∈ xlss_Vof T v), hv, xlss_rest_ind_Vof T v⟩

/-- The occupied subset of the indicator configuration of a subset of `T`. -/
theorem xlss_Vof_ind [DecidableEq S] (T : Finset S) (V : Finset S) (hV : V ⊆ T) :
    xlss_Vof T (fun t => decide ((t : S) ∈ V)) = V := by
  ext s
  rw [xlss_mem_Vof]
  constructor
  · rintro ⟨_, hv⟩
    simpa using hv
  · intro hsV
    exact ⟨hV hsV, by simp [hsV]⟩

/-- The map sending a `T`-configuration to the indicator of its occupied subset is measurable. -/
theorem xlss_meas_Phi [DecidableEq S] (T : Finset S) :
    Measurable (fun v : T → Bool => fun s : S => decide (s ∈ xlss_Vof T v)) := by
  refine Measurable.of_eval fun s => ?_
  by_cases hs : s ∈ T
  · have hcoord : (fun v : T → Bool => decide (s ∈ xlss_Vof T v)) =
        fun v => v ⟨s, hs⟩ := by
      funext v
      have hmem : s ∈ xlss_Vof T v ↔ v ⟨s, hs⟩ = true := by
        rw [xlss_mem_Vof]
        exact ⟨fun ⟨_, hv⟩ => hv, fun hv => ⟨hs, hv⟩⟩
      by_cases hv : v ⟨s, hs⟩ = true
      · have : s ∈ xlss_Vof T v := hmem.mpr hv
        simp [hv, this]
      · have hv' : v ⟨s, hs⟩ = false := by cases h : v ⟨s, hs⟩ <;> simp_all
        have : ¬ (s ∈ xlss_Vof T v) := fun hc => hv (hmem.mp hc)
        simp [hv', this]
    simpa only [hcoord] using (show Measurable (fun v : T → Bool => v ⟨s, hs⟩) from by fun_prop)
  · have hconst : (fun v : T → Bool => decide (s ∈ xlss_Vof T v)) = fun _ => false := by
      funext v
      have : s ∉ xlss_Vof T v := fun h => hs (xlss_Vof_subset T v h)
      simp [this]
    simpa only [hconst] using (measurable_const : Measurable fun _ : T → Bool => false)

section

open MeasureTheory Set Filter
open scoped Topology


/-- A decreasing sequence of measurable cylinders in `ι → Bool` with empty intersection is
eventually empty. -/
theorem xlss_antitone_cylinder_eventually_empty {ι : Type*} (A : ℕ → Set (ι → Bool))
    (hA : ∀ n, A n ∈ measurableCylinders (fun _ : ι => Bool)) (hanti : Antitone A)
    (hinter : (⋂ n, A n) = ∅) : ∃ N, A N = ∅ := by
  by_contra h
  push Not at h
  have hne : ∀ n, (A n).Nonempty := h
  have hclosed : ∀ n, IsClosed (A n) := by
    intro n
    obtain ⟨I, S, _, hEq⟩ := (mem_measurableCylinders (A n)).mp (hA n)
    rw [hEq]
    exact IsClosed.cylinder I (isClosed_discrete S)
  have htd : ∀ n, A (n + 1) ⊆ A n := fun n => hanti (Nat.le_succ n)
  have hcomp : IsCompact (A 0) := (hclosed 0).isCompact
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    A htd hne hcomp hclosed
  rw [hinter] at hx
  exact hx

/-- The projective family content is continuous at the empty set, by compactness. -/
theorem xlss_projectiveFamilyContent_tendsto_zero {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool)) (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P)
    [∀ J, IsFiniteMeasure (P J)] :
    ∀ ⦃s : ℕ → Set (ι → Bool)⦄,
      (∀ n, s n ∈ measurableCylinders (fun _ : ι => Bool)) → Antitone s →
      (⋂ n, s n) = ∅ → Tendsto (fun n => projectiveFamilyContent (α := fun _ : ι => Bool) hP (s n)) atTop (𝓝 0) := by
  intro s hs hanti hinter
  obtain ⟨N, hN⟩ := xlss_antitone_cylinder_eventually_empty s hs hanti hinter
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  have hsub : s n ⊆ s N := hanti hn
  rw [hN] at hsub
  rw [Set.subset_empty_iff.mp hsub, projectiveFamilyContent_eq, projectiveFamilyFun_empty hP]

/-- The projective family content on `ι → Bool` is σ-subadditive. -/
theorem xlss_projectiveFamilyContent_isSigmaSubadditive {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool)) (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P)
    [∀ J, IsFiniteMeasure (P J)] :
    (projectiveFamilyContent (α := fun _ : ι => Bool) hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    (C := measurableCylinders (fun _ : ι => Bool)) isSetRing_measurableCylinders
    (m := projectiveFamilyContent (α := fun _ : ι => Bool) hP) fun f hf hf_Union hf' => ?_
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent (α := fun _ : ι => Bool) hP) (fun s _ => projectiveFamilyContent_ne_top hP)
    (fun s hs hanti hinter => xlss_projectiveFamilyContent_tendsto_zero P hP hs hanti hinter)
    hf hf_Union hf'

/-- The projective limit measure of a projective family of probability measures on `ι → Bool`,
built from the σ-subadditive projective family content by Carathéodory's extension theorem. -/
noncomputable def xlss_projectiveLimit {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool))
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P)
    [∀ J, IsProbabilityMeasure (P J)] : Measure (ι → Bool) :=
  (projectiveFamilyContent (α := fun _ : ι => Bool) hP).measure
    isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    (xlss_projectiveFamilyContent_isSigmaSubadditive P hP)

/-- The measure `xlss_projectiveLimit` is the projective limit of the family. -/
theorem xlss_isProjectiveLimit_projectiveLimit {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool))
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P)
    [∀ J, IsProbabilityMeasure (P J)] :
    IsProjectiveLimit (xlss_projectiveLimit P hP) P := by
  intro I
  refine Measure.ext fun S hS => ?_
  have hmeas : Measurable (Finset.restrict I : (ι → Bool) → (I → Bool)) :=
    Measurable.of_eval fun i => measurable_pi_apply (i : ι)
  rw [Measure.map_apply hmeas hS]
  change xlss_projectiveLimit P hP (cylinder I S) = P I S
  rw [show xlss_projectiveLimit P hP (cylinder I S) =
      projectiveFamilyContent (α := fun _ : ι => Bool) hP (cylinder I S) from
    AddContent.measure_eq _ isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.symm
      (xlss_projectiveFamilyContent_isSigmaSubadditive P hP)
      ((mem_measurableCylinders _).mpr ⟨I, S, hS, rfl⟩)]
  exact projectiveFamilyContent_cylinder hP hS

end

end LatticeProb.Percolation.LSS
