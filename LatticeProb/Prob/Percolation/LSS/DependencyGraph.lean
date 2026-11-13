import Mathlib
import LatticeProb.Prob.Percolation.LSS.Defs

/-!
# Dependence graphs of fields of bits

Fields of bits with a dependence graph: the line graph of the bonds of `ℤ^d` and the
lattice graph itself as dependence graphs, their degree bounds, and the domination
of Bernoulli percolation obtained from `LiggettSchonmannStaceyBoundedDegree`.
The product Bernoulli law on a countable index set is a probability measure and is
inner regular by closed sets.
-/

open MeasureTheory ProbabilityTheory LatticeProb

namespace LatticeProb.Percolation.LSS

theorem rn_dependence_graph {Ω A : Type*} {S : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : A → Ω → Bool) (hX : ∀ a, Measurable (X a)) (hind : iIndepFun X P)
    (G : SimpleGraph S) (vs : S → Finset A) (Φ : S → (A → Bool) → Bool)
    (hΦ : ∀ s a a', (∀ t ∈ vs s, a t = a' t) → Φ s a = Φ s a')
    (hloc : ∀ s t, s ≠ t → ¬ G.Adj s t → Disjoint (vs s) (vs t)) :
    Measurable (fun (ω : Ω) (s : S) => Φ s (fun a => X a ω)) ∧
      HasDependenceGraph G (P.map (fun (ω : Ω) (s : S) => Φ s (fun a => X a ω))) := by
  classical
  have hmeasF : Measurable (fun (ω : Ω) (s : S) => Φ s (fun a => X a ω)) := by
    refine measurable_pi_iff.mpr (fun s => ?_)
    have h1 : (fun ω => Φ s (fun a => X a ω)) =
        (fun v : (vs s → Bool) => Φ s (fun a => if h : a ∈ vs s then v ⟨a, h⟩ else false)) ∘
          (fun ω (t : vs s) => X t ω) := by
      funext ω
      simp only [Function.comp]
      refine hΦ s _ _ (fun t ht => ?_)
      simp [ht]
    rw [h1]
    exact (measurable_of_countable _).comp (Measurable.of_eval (fun t => hX t))
  refine ⟨hmeasF, ?_⟩
  intro I J hIJ hadj
  have hdisj : Disjoint (I.biUnion vs) (J.biUnion vs) := by
    rw [Finset.disjoint_left]
    intro a haI haJ
    obtain ⟨s, hs, has⟩ := Finset.mem_biUnion.mp haI
    obtain ⟨t, ht, hat⟩ := Finset.mem_biUnion.mp haJ
    have hst : s ≠ t := fun h => (Finset.disjoint_left.mp hIJ) hs (h ▸ ht)
    exact Finset.disjoint_left.mp (hloc s t hst (hadj s hs t ht)) has hat
  have hind2 := hind.indepFun_finset (I.biUnion vs) (J.biUnion vs) hdisj hX
  -- the restriction maps
  let ΨI : (I.biUnion vs → Bool) → (I → Bool) := fun v i =>
    Φ i (fun a => if h : a ∈ I.biUnion vs then v ⟨a, h⟩ else false)
  let ΨJ : (J.biUnion vs → Bool) → (J → Bool) := fun v i =>
    Φ i (fun a => if h : a ∈ J.biUnion vs then v ⟨a, h⟩ else false)
  have hΨI : Measurable ΨI := measurable_of_countable _
  have hΨJ : Measurable ΨJ := measurable_of_countable _
  have hcomp := hind2.comp hΨI hΨJ
  set F := (fun (ω : Ω) (s : S) => Φ s (fun a => X a ω)) with hF
  have huI : (fun ω (i : I) => F ω i) = ΨI ∘ (fun ω (a : I.biUnion vs) => X a ω) := by
    funext ω i
    simp only [Function.comp, hF, ΨI]
    refine hΦ i _ _ (fun t ht => ?_)
    have : t ∈ I.biUnion vs := Finset.mem_biUnion.mpr ⟨i, i.2, ht⟩
    simp [this]
  have huJ : (fun ω (j : J) => F ω j) = ΨJ ∘ (fun ω (a : J.biUnion vs) => X a ω) := by
    funext ω i
    simp only [Function.comp, hF, ΨJ]
    refine hΦ i _ _ (fun t ht => ?_)
    have : t ∈ J.biUnion vs := Finset.mem_biUnion.mpr ⟨i, i.2, ht⟩
    simp [this]
  -- transfer to the image measure
  have hmI : Measurable (fun (ω' : S → Bool) (i : I) => ω' i) := Measurable.of_eval (fun i => measurable_pi_apply _)
  have hmJ : Measurable (fun (ω' : S → Bool) (j : J) => ω' j) := Measurable.of_eval (fun i => measurable_pi_apply _)
  haveI : IsProbabilityMeasure (P.map F) := (Measure.isProbabilityMeasure_map_iff hmeasF.aemeasurable).mpr inferInstance
  rw [indepFun_iff_map_prod_eq_prod_map_map hmI.aemeasurable hmJ.aemeasurable]
  have hPI : (fun ω (i : I) => F ω i) = (fun (ω' : S → Bool) (i : I) => ω' i) ∘ F := rfl
  have hPJ : (fun ω (j : J) => F ω j) = (fun (ω' : S → Bool) (j : J) => ω' j) ∘ F := rfl
  rw [huI] at hPI
  rw [huJ] at hPJ
  have hc2 : IndepFun ((fun (ω' : S → Bool) (i : I) => ω' i) ∘ F) ((fun (ω' : S → Bool) (j : J) => ω' j) ∘ F) P := by
    rw [← hPI, ← hPJ]
    exact hcomp
  rw [indepFun_iff_map_prod_eq_prod_map_map (hmI.comp hmeasF).aemeasurable (hmJ.comp hmeasF).aemeasurable] at hc2
  rw [Measure.map_map (hmI.prodMk hmJ) hmeasF, Measure.map_map hmI hmeasF, Measure.map_map hmJ hmeasF]
  exact hc2


variable {d : ℕ}

/-- The bonds of `ℤ^d` are indexed by `(x, i)`, the bond joining `x` and `x + e_i`. -/
abbrev RnBond (d : ℕ) : Type := Site d × Fin d

/-- The two endpoints of a bond. -/
def rn_ends (e : RnBond d) : Finset (Site d) := {e.1, e.1 + unit e.2}

/-- The `≤ 2d` bonds with endpoint `v`. -/
def rn_incident (d : ℕ) (v : Site d) : Finset (RnBond d) :=
  Finset.univ.image (fun j : Fin d => (v, j)) ∪ Finset.univ.image (fun j : Fin d => (v - unit j, j))

theorem rn_card_incident_le (v : Site d) : (rn_incident d v).card ≤ 2 * d := by
  unfold rn_incident
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (Finset.univ.image (fun j : Fin d => (v, j))).card ≤ d :=
    (Finset.card_image_le).trans (by simp)
  have h2 : (Finset.univ.image (fun j : Fin d => (v - unit j, j))).card ≤ d :=
    (Finset.card_image_le).trans (by simp)
  omega

/-- The line graph: two distinct bonds are adjacent when they share an endpoint. -/
def rn_lineGraph (d : ℕ) : SimpleGraph (RnBond d) where
  Adj e e' := e ≠ e' ∧ (rn_ends e ∩ rn_ends e').Nonempty
  symm := ⟨fun e e' h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem rn_mem_incident_of_mem_ends {e' : RnBond d} {v : Site d} (hv : v ∈ rn_ends e') :
    e' ∈ rn_incident d v := by
  simp only [rn_ends, Finset.mem_insert, Finset.mem_singleton] at hv
  simp only [rn_incident, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  rcases hv with rfl | rfl
  · exact Or.inl ⟨e'.2, rfl⟩
  · exact Or.inr ⟨e'.2, by simp⟩

theorem rn_lineGraph_degree (e : RnBond d) :
    ((rn_lineGraph d).neighborSet e).Finite ∧ ((rn_lineGraph d).neighborSet e).ncard ≤ 4 * d := by
  have hsub : (rn_lineGraph d).neighborSet e ⊆
      ↑(rn_incident d e.1 ∪ rn_incident d (e.1 + unit e.2)) := by
    intro e' he'
    have hadj : (rn_lineGraph d).Adj e e' := he'
    obtain ⟨v, hv⟩ := hadj.2
    rw [Finset.mem_inter] at hv
    have hv' : v ∈ rn_ends e := hv.1
    have : e' ∈ rn_incident d v := rn_mem_incident_of_mem_ends hv.2
    simp only [rn_ends, Finset.mem_insert, Finset.mem_singleton] at hv'
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    rcases hv' with rfl | rfl
    · exact Or.inl this
    · exact Or.inr this
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  refine (Finset.card_union_le _ _).trans ?_
  have := rn_card_incident_le (d := d) e.1
  have := rn_card_incident_le (d := d) (e.1 + unit e.2)
  omega

theorem rn_lattice_degree (x : Site d) :
    ((lattice d).neighborSet x).Finite ∧ ((lattice d).neighborSet x).ncard ≤ 2 * d := by
  have hsub : (lattice d).neighborSet x ⊆ ↑(nbrFinset x) := by
    intro y hy
    obtain ⟨i, hi | hi⟩ := hy
    · rw [Finset.mem_coe, nbrFinset, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, by simp [hi]⟩
    · rw [Finset.mem_coe, nbrFinset, Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have : y = x - unit i := by rw [hi]; abel
      simp [this]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  unfold nbrFinset
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ i : Fin d, ({x + unit i, x - unit i} : Finset (Site d)).card ≤ ∑ i : Fin d, 2 :=
        Finset.sum_le_sum (fun i _ => Finset.card_le_two)
    _ = 2 * d := by simp [mul_comm]

theorem rn_incident_disjoint {x y : Site d} (hne : x ≠ y) (hadj : ¬ (lattice d).Adj x y) :
    Disjoint (rn_incident d x) (rn_incident d y) := by
  rw [Finset.disjoint_left]
  intro b hbx hby
  simp only [rn_incident, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hbx hby
  rcases hbx with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rcases hby with ⟨j', hj'⟩ | ⟨j', hj'⟩
  · exact hne (Prod.ext_iff.mp (hj.trans hj'.symm)).1
  · obtain ⟨h1, h2⟩ := Prod.ext_iff.mp (hj.trans hj'.symm)
    simp only at h1 h2
    subst h2
    exact hadj ⟨j, Or.inl (by rw [h1]; abel)⟩
  · obtain ⟨h1, h2⟩ := Prod.ext_iff.mp (hj.trans hj'.symm)
    simp only at h1 h2
    subst h2
    exact hadj ⟨j, Or.inr (by rw [← h1]; abel)⟩
  · obtain ⟨h1, h2⟩ := Prod.ext_iff.mp (hj.trans hj'.symm)
    simp only at h1 h2
    subst h2
    exact hne (sub_left_injective h1)

theorem rn_bitLaw_isProb {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsProbabilityMeasure (bitLaw q) := by
  refine ⟨?_⟩
  unfold bitLaw
  simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  norm_num

theorem rn_bitLaw_true (q : ℝ) : bitLaw q {true} = ENNReal.ofReal q := by
  unfold bitLaw
  simp [Measure.dirac_apply']

theorem rn_infinitePi_isProb {ι : Type*} {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsProbabilityMeasure (Measure.infinitePi fun _ : ι => bitLaw q) := by
  haveI := rn_bitLaw_isProb h0 h1
  infer_instance

/-- The coordinates of Bernoulli product measure are independent. -/
theorem rn_bernoulli_iIndep {ι : Type*} {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    iIndepFun (fun (i : ι) (ω : ι → Bool) => ω i) (Measure.infinitePi fun _ : ι => bitLaw q) := by
  haveI := rn_bitLaw_isProb h0 h1
  exact iIndepFun_infinitePi (P := fun _ : ι => bitLaw q) (X := fun _ => id) (fun _ => measurable_id)

theorem rn_bernoulli_marg {ι : Type*} {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (i : ι) :
    (Measure.infinitePi fun _ : ι => bitLaw q) {ω | ω i = true} = ENNReal.ofReal q := by
  haveI := rn_bitLaw_isProb h0 h1
  have : {ω : ι → Bool | ω i = true} = (fun ω : ι → Bool => ω i) ⁻¹' {true} := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton true),
    Measure.infinitePi_map_eval, rn_bitLaw_true]

theorem rn_lssb_apply (hLSSB : LiggettSchonmannStaceyBoundedDegree)
    {S : Type} [Countable S] (G : SimpleGraph S) (D : ℕ)
    (hdeg : ∀ s : S, (G.neighborSet s).Finite ∧ (G.neighborSet s).ncard ≤ D)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ μ : Measure (S → Bool), IsProbabilityMeasure μ →
      HasDependenceGraph G μ → (∀ s, ENNReal.ofReal p ≤ μ {ω | ω s = true}) →
      ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A →
        bernoulliProduct S ρ A ≤ μ A := by
  obtain ⟨p, hp1, hp⟩ := hLSSB S G (D + 1) (by omega)
    (fun s => ⟨(hdeg s).1, (hdeg s).2.trans (Nat.le_succ D)⟩)
    (fun s _ => ⟨s, by simp, Nat.lt_succ_of_le (hdeg s).2⟩) ρ hρ0 hρ1
  refine ⟨max p 0, le_max_right _ _, max_lt hp1 zero_lt_one, fun μ hμ hdep hmarg A hA hinc => ?_⟩
  refine hp μ hμ hdep (fun s => ?_) A hA hinc
  refine le_trans ?_ (hmarg s)
  exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

theorem rn_lineGraph_loc (e e' : RnBond d) (hne : e ≠ e') (hadj : ¬ (rn_lineGraph d).Adj e e') :
    Disjoint (rn_ends e) (rn_ends e') := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact fun h => hadj ⟨hne, h⟩

/-- **Domination of Bernoulli bond percolation by the good-edge field.**  If the bits `X x` are
independent with marginals at least `q`, the bond field `e ↦ X e.1 ∧ X (e.1 + e_{e.2})` dominates,
on measurable increasing events, Bernoulli bond percolation of any prescribed density `ρ < 1`,
provided `q` is close enough to `1`. -/
theorem rn_edge_dom (hLSSB : LiggettSchonmannStaceyBoundedDegree)
    (d : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ q : ℝ, q < 1 ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Site d → Ω → Bool), (∀ x, Measurable (X x)) → iIndepFun X P →
      (∀ x, ENNReal.ofReal q ≤ P {ω | X x ω = true}) →
      ∀ A : Set (RnBond d → Bool), MeasurableSet A → IsIncreasingSet A →
        bernoulliProduct (RnBond d) ρ A ≤
          P {ω | (fun e : RnBond d => X e.1 ω && X (e.1 + unit e.2) ω) ∈ A} := by
  obtain ⟨p, hp0, hp1, hp⟩ := rn_lssb_apply hLSSB (rn_lineGraph d) (4 * d) rn_lineGraph_degree ρ hρ0 hρ1
  refine ⟨Real.sqrt p, ?_, ?_⟩
  · rw [Real.sqrt_lt' one_pos]; linarith
  intro Ω _ P _ X hX hind hmarg A hA hinc
  obtain ⟨hFm, hdep⟩ := rn_dependence_graph P X hX hind (rn_lineGraph d) rn_ends
    (fun e a => a e.1 && a (e.1 + unit e.2))
    (fun e a a' h => by
      have h1 : a e.1 = a' e.1 := h _ (by simp [rn_ends])
      have h2 : a (e.1 + unit e.2) = a' (e.1 + unit e.2) := h _ (by simp [rn_ends])
      simp [h1, h2])
    rn_lineGraph_loc
  set F := (fun (ω : Ω) (e : RnBond d) => X e.1 ω && X (e.1 + unit e.2) ω) with hF
  haveI : IsProbabilityMeasure (P.map F) := (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).mpr inferInstance
  have hmarg' : ∀ e : RnBond d, ENNReal.ofReal p ≤ (P.map F) {ω' | ω' e = true} := by
    intro e
    have hm : MeasurableSet {ω' : RnBond d → Bool | ω' e = true} := by
      exact measurableSet_eq_fun (measurable_pi_apply e) measurable_const
    rw [Measure.map_apply hFm hm]
    have hne : e.1 ≠ e.1 + unit e.2 := by
      intro h
      have : unit e.2 = (0 : Site d) := by
        have h' : e.1 + 0 = e.1 + unit e.2 := by simpa using h
        exact (add_left_cancel h').symm
      exact unit_ne_zero e.2 this
    have hset : F ⁻¹' {ω' | ω' e = true} = (X e.1 ⁻¹' {true}) ∩ (X (e.1 + unit e.2) ⁻¹' {true}) := by
      ext ω; simp [hF]
    rw [hset]
    have hi := (hind.indepFun hne).measure_inter_preimage_eq_mul {true} {true}
      (measurableSet_singleton true) (measurableSet_singleton true)
    rw [hi]
    have h1 : ENNReal.ofReal (Real.sqrt p) ≤ P (X e.1 ⁻¹' {true}) := hmarg e.1
    have h2 : ENNReal.ofReal (Real.sqrt p) ≤ P (X (e.1 + unit e.2) ⁻¹' {true}) :=
      hmarg (e.1 + unit e.2)
    calc ENNReal.ofReal p = ENNReal.ofReal (Real.sqrt p) * ENNReal.ofReal (Real.sqrt p) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg p), Real.mul_self_sqrt hp0]
      _ ≤ _ := mul_le_mul' h1 h2
  have := hp (P.map F) inferInstance hdep hmarg' A hA hinc
  rwa [Measure.map_apply hFm hA] at this

theorem rn_site_dom (hLSSB : LiggettSchonmannStaceyBoundedDegree)
    (d : ℕ) (hd : 1 ≤ d) (ρ₂ : ℝ) (hρ0 : 0 ≤ ρ₂) (hρ1 : ρ₂ < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ ρ₁ : ℝ, r ≤ ρ₁ → ρ₁ ≤ 1 →
      ∀ A : Set (Site d → Bool), MeasurableSet A → IsIncreasingSet A →
        bernoulliProduct (Site d) ρ₂ A ≤
          bondPercolation d ρ₁
            {ζ | (fun x : Site d => decide (∀ b ∈ rn_incident d x, ζ b = true)) ∈ A} := by
  obtain ⟨p, hp0, hp1, hp⟩ := rn_lssb_apply hLSSB (lattice d) (2 * d) rn_lattice_degree ρ₂ hρ0 hρ1
  have h2d : (0 : ℝ) < 1 / (2 * (d : ℝ)) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hr0 : 0 ≤ p ^ (1 / (2 * (d : ℝ))) := Real.rpow_nonneg hp0 _
  refine ⟨p ^ (1 / (2 * (d : ℝ))), hr0, Real.rpow_lt_one hp0 hp1 h2d, ?_⟩
  intro ρ₁ hr h1 A hA hinc
  have hρ₁0 : 0 ≤ ρ₁ := hr0.trans hr
  have hpow : p ≤ ρ₁ ^ (2 * d) := by
    calc p = (p ^ (1 / (2 * (d : ℝ)))) ^ (2 * d) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
          have : (1 / (2 * (d : ℝ))) * ((2 * d : ℕ) : ℝ) = 1 := by
            have : (0 : ℝ) < d := by exact_mod_cast hd
            push_cast; field_simp
          rw [this, Real.rpow_one]
      _ ≤ ρ₁ ^ (2 * d) := pow_le_pow_left₀ hr0 hr _
  set P : Measure (RnBond d → Bool) := bondPercolation d ρ₁ with hP
  haveI : IsProbabilityMeasure P := rn_infinitePi_isProb (ι := RnBond d) hρ₁0 h1
  have hind : iIndepFun (fun (b : RnBond d) (ω : RnBond d → Bool) => ω b) P :=
    rn_bernoulli_iIndep hρ₁0 h1
  obtain ⟨hFm, hdep⟩ := rn_dependence_graph P (fun (b : RnBond d) (ω : RnBond d → Bool) => ω b)
    (fun b => measurable_pi_apply b) hind (lattice d) (rn_incident d)
    (fun x a => decide (∀ b ∈ rn_incident d x, a b = true))
    (fun x a a' h => by
      have : (∀ b ∈ rn_incident d x, a b = true) ↔ (∀ b ∈ rn_incident d x, a' b = true) :=
        forall₂_congr (fun b hb => by rw [h b hb])
      simp only [decide_eq_decide]; exact this)
    (fun x y hne hadj => rn_incident_disjoint hne hadj)
  set F := (fun (ω : RnBond d → Bool) (x : Site d) =>
    decide (∀ b ∈ rn_incident d x, ω b = true)) with hF
  haveI : IsProbabilityMeasure (P.map F) := (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).mpr inferInstance
  have hmarg' : ∀ x : Site d, ENNReal.ofReal p ≤ (P.map F) {ω' | ω' x = true} := by
    intro x
    have hm : MeasurableSet {ω' : Site d → Bool | ω' x = true} := by
      exact measurableSet_eq_fun (measurable_pi_apply x) measurable_const
    rw [Measure.map_apply hFm hm]
    have hset : F ⁻¹' {ω' | ω' x = true} =
        ⋂ b ∈ rn_incident d x, (fun ω : RnBond d → Bool => ω b) ⁻¹' {true} := by
      ext ω; simp [hF]
    rw [hset, hind.measure_inter_preimage_eq_mul (rn_incident d x)
      (sets := fun _ => {true}) (fun _ _ => measurableSet_singleton true)]
    have hb : ∀ b ∈ rn_incident d x, P ((fun ω : RnBond d → Bool => ω b) ⁻¹' {true}) =
        ENNReal.ofReal ρ₁ := fun b _ => rn_bernoulli_marg hρ₁0 h1 b
    rw [Finset.prod_congr rfl hb, Finset.prod_const, ← ENNReal.ofReal_pow hρ₁0]
    refine ENNReal.ofReal_le_ofReal (hpow.trans ?_)
    exact pow_le_pow_of_le_one hρ₁0 h1 (by simpa using rn_card_incident_le x)
  have := hp (P.map F) inferInstance hdep hmarg' A hA hinc
  rwa [Measure.map_apply hFm hA] at this


section

open MeasureTheory Set Filter
open scoped Topology ENNReal
variable {S : Type}

/-- The product Bernoulli law is a probability measure for a density in `[0, 1]`. -/
theorem xlsd_isProbabilityMeasure (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    IsProbabilityMeasure (bernoulliProduct S ρ) := by
  unfold bernoulliProduct
  exact rn_infinitePi_isProb hρ0 hρ1

/-- Inner regularity of the product Bernoulli law by closed sets, on a countable index set. -/
theorem xlsd_measure_eq_iSup_isClosed [Countable S] (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {A : Set (S → Bool)} (hA : MeasurableSet A) :
    bernoulliProduct S ρ A =
      ⨆ (F : Set (S → Bool)) (_ : F ⊆ A) (_ : IsClosed F), bernoulliProduct S ρ F := by
  haveI := xlsd_isProbabilityMeasure (S := S) ρ hρ0 hρ1
  exact hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top _ _)

end

end LatticeProb.Percolation.LSS
