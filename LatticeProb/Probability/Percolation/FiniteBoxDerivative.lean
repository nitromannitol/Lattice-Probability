import LatticeProb.Prob.Percolation.FiniteProductPivotal
import LatticeProb.Vendor.FormalMathPercolation.Literature.SharpnessDCTProofs

/-!
# Finite-box connectivity and pivotal coordinates

A pivotal event does not depend on the state of its pivotal coordinate. This
identifies the probability of a closed pivotal coordinate with its pivotal
probability times the probability that the coordinate is closed. A path from
the origin remains in the set of vertices not connected to the box boundary
when the origin belongs to that set.
-/

open Finset Classical

namespace LatticeProb.Percolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In a finite product model, a pivotal coordinate is closed with probability
`1 - par i`, independently of its pivotality. -/
theorem fpr_pivot_and_closed (par : ι → ℝ) (i : ι) (A : Set (ι → _)) :
    fpr par {ω | ω ∈ Pivot i A ∧ ω i = false} =
      (1 - par i) * fpr par (Pivot i A) := by
  rw [fpr_affine par i {ω | ω ∈ Pivot i A ∧ ω i = false},
    fpr_affine par i (Pivot i A)]
  have hpiv : ∀ (b : _) τ,
      (Equiv.piSplitAt i (fun _ => _)).symm (b, τ) ∈ Pivot i A ↔
      (Equiv.piSplitAt i (fun _ => _)).symm (false, τ) ∈ Pivot i A := by
    intro b τ
    simp only [Pivot, Set.mem_ofPred_eq, update_symm]
  simp only [Set.mem_ofPred_eq, Equiv.piSplitAt_symm_apply, ne_eq,
    ↓reduceDIte, reduceCtorEq, and_false, ite_false, Finset.sum_const_zero,
    mul_zero, zero_add, and_true]
  simp only [hpiv true]
  ring

end LatticeProb.Percolation

namespace Percolation.Literature.DCT16

open LatticeModels MeasureTheory

variable {d n : ℕ}

/-- If the origin is not connected to the boundary, every connection from the
origin inside the box stays inside the set of vertices disconnected from the
boundary. -/
theorem openConnIn_blockSet_of_openConnIn_box {ω : BondConfig (Site d)} {x : Site d}
    (h0 : (0 : Site d) ∈ blockSet n ω)
    (h : ω ∈ openConnIn (↑(box d n) : Set (Site d)) 0 x) :
    ω ∈ openConnIn (↑(blockSet n ω) : Set (Site d)) 0 x := by
  apply mem_openConnIn_of_pathIn
  apply (pathIn_restrict_cluster (pathIn_of_mem_openConnIn h)).mono
  intro z hz
  rw [Finset.mem_coe, mem_blockSet_iff]
  refine ⟨hz.1, ?_⟩
  intro hzbdry
  have h0bdry : BdryConn n ω 0 := by
    obtain ⟨w, hw, hp⟩ := bdryConn_iff.mp hzbdry
    exact bdryConn_iff.mpr ⟨w, hw, hz.2.trans hp⟩
  exact (mem_blockSet_iff.mp h0).2 h0bdry

/-- A closed pivotal edge leaves the blocking set at a vertex connected to the origin. -/
theorem closed_pivotal_boundary_witness {ω : BondConfig (Site d)} {e : Sym2 (Site d)}
    (he : e ∈ (zdGraph d).edgeSet) (hp : IsPivotal (siteToBoundary d n) e ω)
    (hc : e ∉ ω) :
    ∃ x ∈ blockSet n ω, ∃ y ∈ (zdGraph d).neighborFinset x,
      y ∉ blockSet n ω ∧ s(x, y) = e ∧
      ω ∈ openConnIn (↑(blockSet n ω) : Set (Site d)) 0 x := by
  have hp' := (Russo.isPivotal_iff_of_notMem (isUpperSet_siteToBoundary d n) hc).1 hp
  have h0 : (0 : Site d) ∈ blockSet n ω := zero_mem_blockSet_iff.2 hp'.2
  rw [mem_siteToBoundary_iff] at hp'
  obtain ⟨z, hz, hpath⟩ := hp'.1
  have hzout : z ∉ blockSet n ω := by
    intro h
    exact (mem_blockSet_iff.1 h).2 (bdryConn_of_mem_innerBoundary hz)
  obtain ⟨x, y, hx, hy, hybox, hxy, hprefix⟩ := hpath.exit h0 hzout
  have hyconn : BdryConn n ω y := by
    have h : y ∉ blockSet n ω := hy
    rw [mem_blockSet_iff] at h
    by_contra hh
    exact h ⟨hybox, hh⟩
  have hclosed : s(x, y) ∉ ω := by
    intro h
    have hxb := (mem_blockSet_iff.1 hx)
    exact hxb.2 (hyconn.of_adj hxb.1 ((openGraph_adj ω x y).2
      ⟨h, (openGraph_adj _ x y).1 hxy |>.2⟩))
  have hedge : s(x, y) = e := by
    have h := (openGraph_adj _ x y).1 hxy
    exact (Set.mem_insert_iff.mp h.1).resolve_right hclosed
  have hne : ∀ a b, a ∈ (↑(blockSet n ω) : Set (Site d)) ∩ ↑(box d n) →
      b ∈ (↑(blockSet n ω) : Set (Site d)) ∩ ↑(box d n) → s(a, b) ≠ e := by
    intro a b ha hb hab
    have hs : s(a, b) = s(x, y) := hab.trans hedge.symm
    rcases Sym2.eq_iff.mp hs with ⟨hax, hby⟩ | ⟨hay, hbx⟩
    · exact hy (hby ▸ hb.1)
    · exact hy (hay ▸ ha.1)
  have horig : PathIn (openGraph ω)
      ((↑(blockSet n ω) : Set (Site d)) ∩ ↑(box d n)) 0 x := by
    apply pathIn_congrGraph (G := openGraph (insert e ω))
    · intro a b ha hb hab
      have hab' := (openGraph_adj _ a b).1 hab
      exact (openGraph_adj ω a b).2
        ⟨(Set.mem_insert_iff.mp hab'.1).resolve_left (hne a b ha hb), hab'.2⟩
    · exact hprefix
  refine ⟨x, hx, y, ?_, hy, hedge, ?_⟩
  · rw [SimpleGraph.mem_neighborFinset]
    rw [← hedge] at he
    exact he
  · exact mem_openConnIn_of_pathIn (horig.mono Set.inter_subset_left)

/-- Closed pivotality is equivalent to the oriented blocking-set boundary event. -/
theorem closed_pivotal_iff_boundary_witness {ω : BondConfig (Site d)} {e : Sym2 (Site d)} :
    (e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω) ↔
      ∃ S ∈ originSets d n, ∃ x ∈ S, ∃ y ∈ (zdGraph d).neighborFinset x,
        y ∉ S ∧ s(x, y) = e ∧
        ω ∈ openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S := by
  constructor
  · rintro ⟨he, hp, hc⟩
    have hp' := (Russo.isPivotal_iff_of_notMem (isUpperSet_siteToBoundary d n) hc).1 hp
    have h0 : (0 : Site d) ∈ blockSet n ω := zero_mem_blockSet_iff.2 hp'.2
    obtain ⟨x, hx, y, hy, hyS, heq, hconn⟩ := closed_pivotal_boundary_witness he hp hc
    exact ⟨blockSet n ω, mem_originSets.2 ⟨blockSet_subset ω, h0⟩,
      x, hx, y, hy, hyS, heq, hconn, rfl⟩
  · rintro ⟨S, hS, x, hx, y, hy, hyS, heq, hω⟩
    rw [← heq]
    exact subset_pivotal hS hx hy hyS hω

/-- The sum over oriented boundary events equals the sum of closed pivotal probabilities.
The finite regrouping follows the proof of `sum_le_sum_pivotal` in the vendored
FormalMathPercolation library. -/
theorem sum_eq_sum_pivotal (p : unitInterval) (n : ℕ) :
    ∑ S ∈ originSets d n, ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
        (bondPercolation (zdGraph d) p).real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) =
      ∑ e ∈ (box d n).sym2, (bondPercolation (zdGraph d) p).real
        {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω} := by
  classical
  set μ := bondPercolation (zdGraph d) p with hμ
  set T : Finset ((Σ _ : Finset (Site d), Σ _ : Site d, Site d)) :=
    (originSets d n).sigma fun S => S.sigma fun x =>
      ((zdGraph d).neighborFinset x).filter (· ∉ S) with hT
  set f : (Σ _ : Finset (Site d), Σ _ : Site d, Site d) → ℝ :=
    fun t => μ.real (openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1) with hf
  set g : (Σ _ : Finset (Site d), Σ _ : Site d, Site d) → Sym2 (Site d) := fun t => s(t.2.1, t.2.2) with hg
  have hmemT : ∀ t ∈ T, t.1 ∈ originSets d n ∧ t.2.1 ∈ t.1 ∧
      t.2.2 ∈ (zdGraph d).neighborFinset t.2.1 ∧ t.2.2 ∉ t.1 := by
    rintro ⟨S, x, y⟩ ht
    simp only [hT, Finset.mem_sigma, Finset.mem_filter] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
  have hsum : ∑ S ∈ originSets d n, ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
      μ.real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) = ∑ t ∈ T, f t := by
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_sigma]
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not T (fun t => g t ∈ (box d n).sym2)]
  have hzero : ∑ t ∈ T with ¬g t ∈ (box d n).sym2, f t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_filter] at ht
    obtain ⟨hS, hx, hy, hyS⟩ := hmemT t ht.1
    have hyn : t.2.2 ∉ box d n := by
      intro hyn
      exact ht.2 (Finset.mk_mem_sym2_iff.2 ⟨(mem_originSets.1 hS).1 hx, hyn⟩)
    have hempty : openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1 = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => hyn ?_
      obtain ⟨-, hblock⟩ := hω
      simp only [blockEvent, Set.mem_ofPred_eq] at hblock
      have hxb : t.2.1 ∈ box d n ∧ ¬BdryConn n ω t.2.1 := by
        rw [← mem_blockSet_iff, hblock]; exact hx
      by_contra hyn
      exact hxb.2 (bdryConn_of_mem_innerBoundary (mem_innerBoundary_iff.2
        ⟨hxb.1, t.2.2, hyn, (SimpleGraph.mem_neighborFinset _ _ _).1 hy⟩))
    simp only [hf, hempty, measureReal_empty]
  rw [hzero, add_zero, ← Finset.sum_fiberwise_of_maps_to (g := g) (t := (box d n).sym2)
    (fun t ht => (Finset.mem_filter.1 ht).2)]
  refine Finset.sum_congr rfl fun e he => ?_
  set Te := (T.filter fun t => g t ∈ (box d n).sym2).filter fun t => g t = e with hTe
  have hTe_mem : ∀ t ∈ Te, t ∈ T ∧ g t = e := fun t ht => by
    simp only [hTe, Finset.mem_filter] at ht
    exact ⟨ht.1.1, ht.2⟩
  have hdisj : Set.PairwiseDisjoint (↑Te : Set ((Σ _ : Finset (Site d), Σ _ : Site d, Site d)))
      (fun t : (Σ _ : Finset (Site d), Σ _ : Site d, Site d) => openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1) := by
    rintro t ht t' ht' hne
    obtain ⟨htT, hte⟩ := hTe_mem t ht
    obtain ⟨ht'T, ht'e⟩ := hTe_mem t' ht'
    obtain ⟨-, hx, -, hyS⟩ := hmemT t htT
    obtain ⟨-, hx', -, hyS'⟩ := hmemT t' ht'T
    refine Set.disjoint_left.2 fun ω hω hω' => hne ?_
    have hSS : t.1 = t'.1 := hω.2.symm.trans hω'.2
    have hg' : s(t.2.1, t.2.2) = s(t'.2.1, t'.2.2) := hte.trans ht'e.symm
    rcases Sym2.eq_iff.1 hg' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases t with ⟨S, x, y⟩
      rcases t' with ⟨S', x', y'⟩
      simp only at hSS h1 h2
      subst hSS h1 h2
      rfl
    · exact absurd (h1 ▸ hx) (hSS ▸ hyS')
  calc ∑ t ∈ Te, f t = μ.real (⋃ t ∈ Te, openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1) := by
        rw [measureReal_biUnion_finset hdisj]
        intro t ht
        obtain ⟨htT, -⟩ := hTe_mem t ht
        obtain ⟨hS, -, -, -⟩ := hmemT t htT
        exact (measurableSet_openConnIn _ _ _).inter (measurableSet_blockEvent n _)
    _ = μ.real {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω} := by
        congr 1
        ext ω
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨t, ht, hω⟩
          obtain ⟨htT, hte⟩ := hTe_mem t ht
          obtain ⟨hS, hx, hy, hyS⟩ := hmemT t htT
          rw [← hte]
          exact subset_pivotal hS hx hy hyS hω
        · intro hω
          obtain ⟨S, hS, x, hx, y, hy, hyS, heq, hω⟩ :=
            closed_pivotal_iff_boundary_witness.mp hω
          let t : (Σ _ : Finset (Site d), Σ _ : Site d, Site d) := ⟨S, x, y⟩
          have htT : t ∈ T := by
            simp only [hT, Finset.mem_sigma, Finset.mem_filter]
            exact ⟨hS, hx, hy, hyS⟩
          have hte : g t = e := heq
          have ht : t ∈ Te := by
            simp only [hTe, Finset.mem_filter]
            exact ⟨⟨htT, hte ▸ he⟩, hte⟩
          exact ⟨t, ht, hω⟩

/-- The finite-box derivative as the weighted sum of blocking-set boundary terms. -/
theorem hasDerivAt_thetaN_weighted_phi (d n : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 1) :
    HasDerivAt (thetaN d n)
      ((∑ S ∈ originSets d n,
        phi (Set.projIcc 0 1 zero_le_one p) S *
          (bondPercolation (zdGraph d) (Set.projIcc 0 1 zero_le_one p)).real (blockEvent n S)) /
        (p * (1 - p))) p := by
  classical
  set q : unitInterval := Set.projIcc 0 1 zero_le_one p with hqdef
  have hqp : (q : ℝ) = p := by rw [hqdef, Set.projIcc_of_mem _ ⟨hp.1.le, hp.2.le⟩]
  set μ := bondPercolation (zdGraph d) q with hμ
  set A := siteToBoundary d n with hA
  set F : Finset (Sym2 (Site d)) := (box d n).sym2 with hF
  have hderiv := russo_formula_sum_holds (zdGraph d) (isUpperSet_siteToBoundary d n) F
    (determinedBy_siteToBoundary d n) p hp
  set D := ∑ e ∈ F, μ.real {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal A e ω} with hD
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : 1 - p ≠ 0 := by linarith [hp.2]
  have h1 : ∑ e ∈ F, μ.real {ω | e ∈ (zdGraph d).edgeSet ∧
      IsPivotal A e ω ∧ e ∉ ω} = (1 - p) * D := by
    rw [hD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hμ, hA, real_pivotal_closed q n e, hqp]
  have h3 : ∀ S ∈ originSets d n,
      ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
        μ.real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) =
        μ.real (blockEvent n S) * (phi q S / p) := by
    intro S hS
    have hind : ∀ x ∈ S, μ.real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) =
        μ.real (openConnIn (↑S : Set (Site d)) 0 x) * μ.real (blockEvent n S) := by
      intro x _
      refine real_inter_of_determinedBy_disjoint (zdGraph d) q
        (determinedBy_openConnIn (↑S : Set (Site d)) 0 x (K := ↑S.sym2) (by rw [Finset.coe_sym2]))
        (determinedBy_blockEvent n S) Finset.disjoint_sdiff
    rw [phi_def, hqp, mul_div_cancel_left₀ _ hp0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hind x hx, mul_comm]
  have h2 := sum_eq_sum_pivotal (d := d) q n
  change (∑ S ∈ originSets d n, ∑ x ∈ S,
      ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
        μ.real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S)) =
      ∑ e ∈ F, μ.real {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal A e ω ∧ e ∉ ω} at h2
  rw [Finset.sum_congr rfl h3, h1] at h2
  have h4 : (∑ S ∈ originSets d n, μ.real (blockEvent n S) * (phi q S / p)) =
      (∑ S ∈ originSets d n, phi q S * μ.real (blockEvent n S)) / p := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  rw [h4] at h2
  have hD' : D = (∑ S ∈ originSets d n, phi q S * μ.real (blockEvent n S)) /
      (p * (1 - p)) := by
    apply (eq_div_iff (mul_ne_zero hp0 hp1)).2
    have h := (div_eq_iff hp0).1 h2
    nlinarith
  change HasDerivAt (thetaN d n) D p at hderiv
  rw [hD'] at hderiv
  exact hderiv

/-- The boundary sum vanishes when the set does not contain the origin. -/
theorem phi_eq_zero_of_not_mem (p : unitInterval) {S : Finset (Site d)}
    (h0 : (0 : Site d) ∉ S) : phi p S = 0 := by
  rw [phi_def]
  have hempty : ∀ x, openConnIn (↑S : Set (Site d)) 0 x = ∅ := by
    intro x
    apply Set.eq_empty_of_forall_notMem
    intro ω hω
    exact h0 (pathIn_of_mem_openConnIn hω).left_mem
  simp only [hempty, measureReal_empty, Finset.sum_const_zero, mul_zero]

/-- The expectation of the boundary sum is a finite sum over blocking sets. -/
theorem integral_phi_blockSet (p : unitInterval) (n : ℕ) :
    (∫ ω, phi p (blockSet n ω) ∂(bondPercolation (zdGraph d) p)) =
      ∑ S ∈ originSets d n, phi p S *
        (bondPercolation (zdGraph d) p).real (blockEvent n S) := by
  classical
  set μ := bondPercolation (zdGraph d) p
  have hpoint : ∀ ω : BondConfig (Site d), phi p (blockSet n ω) =
      ∑ S ∈ originSets d n, (blockEvent n S).indicator (fun _ => phi p S) ω := by
    intro ω
    by_cases h0 : (0 : Site d) ∈ blockSet n ω
    · have hS : blockSet n ω ∈ originSets d n :=
        mem_originSets.2 ⟨blockSet_subset ω, h0⟩
      rw [Finset.sum_eq_single_of_mem (blockSet n ω) hS]
      · simp [blockEvent]
      · intro S hS' hne
        have hω : ω ∉ blockEvent n S := by
          intro h
          exact hne h.symm
        simp [hω]
    · rw [phi_eq_zero_of_not_mem p h0]
      symm
      apply Finset.sum_eq_zero
      intro S hS
      have hω : ω ∉ blockEvent n S := by
        intro h
        exact h0 (h ▸ (mem_originSets.1 hS).2)
      simp [hω]
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun S hS => ?_
    rw [integral_indicator_const _ (measurableSet_blockEvent n S)]
    simp only [smul_eq_mul, measureReal_def]
    ring
  · intro S _
    exact (integrable_const (phi p S)).indicator (measurableSet_blockEvent n S)

/-- The finite-box derivative is the expected blocking-set boundary sum divided by `p(1-p)`. -/
theorem hasDerivAt_thetaN_expected_phi (d n : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 1) :
    HasDerivAt (thetaN d n)
      ((∫ ω, phi (Set.projIcc 0 1 zero_le_one p) (blockSet n ω)
        ∂(bondPercolation (zdGraph d) (Set.projIcc 0 1 zero_le_one p))) /
        (p * (1 - p))) p := by
  rw [integral_phi_blockSet]
  exact hasDerivAt_thetaN_weighted_phi d n p hp

end Percolation.Literature.DCT16
