import Mathlib

/-!
# Removing a convex compact set from a connected plane domain keeps it preconnected

General plane topology, no Harnack or LQG input. The statement below was used as a hypothesis in the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795]; it asserts: for open connected `V ⊆ ℂ`, compact convex `K ⊆ V`, the set `V \ K` is preconnected.

Main theorem `LatticeProb.Topology.isPreconnected_diff_of_convex_compact`. Route (all steps in Mathlib):

* `isPreconnected_collar_of_convex`: for `K ⊆ interior L`, `K` nonempty convex, `L` compact convex, the collar
  `L \ K` is preconnected. Gauge `P = (c + ·)⁻¹' L` of the translated set `L` at a point `c ∈ K`; the radial map
  `R z = c + (gauge P (z - c))⁻¹ • (z - c)` sends `ℂ \ {c}` (connected) continuously onto a subset of `L \ K`; each
  `z ∈ L \ K` is joined inside `L \ K` to `R z` by the segment `{c + l • (z - c) : 1 ≤ l ≤ (gauge P (z - c))⁻¹}`.
* `isPreconnected_diff_of_convex_compact`: take `δ > 0` with `cthickening δ K ⊆ V` and `L = cthickening δ K`
  (convex, compact, `K ⊆ interior L`). A connected component `C` of `V \ K` that misses the collar `L \ K` is
  clopen in `V` (its closure misses `K`), hence equals `V`, which contradicts `K ≠ ∅`. So every component meets the
  collar, and `V \ K` is preconnected.

Names and terminology: gauge (Minkowski functional) and radial projection as in Armitage-Gardiner's potential-theory
conventions; no new hypothesis is introduced.
-/

open Set Filter Topology Metric

namespace LatticeProb.Topology

/-- Collar lemma: for a nonempty convex `K` and a compact convex `L` with `K ⊆ interior L`, the set `L \ K` is
preconnected (radial projection from a point of `K` through the gauge of `L`). -/
theorem isPreconnected_collar_of_convex {K L : Set ℂ} (hKcv : Convex ℝ K) (hKne : K.Nonempty)
    (hLcv : Convex ℝ L) (hLc : IsCompact L) (hKL : K ⊆ interior L) :
    IsPreconnected (L \ K) := by
  obtain ⟨c, hcK⟩ := hKne
  obtain ⟨P, hPdef⟩ : ∃ P : Set ℂ, P = (fun x => c + x) ⁻¹' L := ⟨_, rfl⟩
  have hmemP : ∀ x, x ∈ P ↔ c + x ∈ L := fun x => by rw [hPdef]; rfl
  have hLn : L ∈ 𝓝 c := mem_interior_iff_mem_nhds.1 (hKL hcK)
  have hPcv : Convex ℝ P := by rw [hPdef]; exact hLcv.translate_preimage_right c
  have hPeq : P = (fun x => -c + x) '' L := by
    rw [hPdef, Set.image_add_left, neg_neg]
  have hPc : IsCompact P := by rw [hPeq]; exact hLc.image (continuous_const_add (-c))
  have hP0 : P ∈ 𝓝 (0 : ℂ) := by
    rw [hPdef]
    exact (continuous_const_add c).continuousAt.preimage_mem_nhds (by simpa using hLn)
  have hgcont : Continuous (gauge P) := continuous_gauge hPcv hP0
  have hgle : ∀ x, gauge P x ≤ 1 ↔ c + x ∈ L := by
    intro x
    rw [gauge_le_one_iff_mem_closure hPcv hP0, hPc.isClosed.closure_eq, hmemP]
  have hgpos : ∀ x, x ≠ 0 → 0 < gauge P x := fun x hx =>
    (gauge_pos (absorbent_nhds_zero hP0) (hPc.isVonNBounded ℝ)).2 hx
  have hgsmul : ∀ t : ℝ, 0 ≤ t → ∀ x, gauge P (t • x) = t * gauge P x := by
    intro t ht x
    rw [gauge_smul_of_nonneg ht x, smul_eq_mul]
  -- points of `K` have gauge `< 1`
  have hgK : ∀ w ∈ K, gauge P (w - c) < 1 := by
    intro w hw
    rw [gauge_lt_one_iff_mem_interior hPcv hP0]
    apply mem_interior_iff_mem_nhds.2
    have hLw : L ∈ 𝓝 (c + (w - c)) := by
      rw [add_sub_cancel]; exact mem_interior_iff_mem_nhds.1 (hKL hw)
    rw [hPdef]
    exact (continuous_const_add c).continuousAt.preimage_mem_nhds hLw
  -- the radial projection
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ → ℂ, R = fun z => c + (gauge P (z - c))⁻¹ • (z - c) := ⟨_, rfl⟩
  have hRapply : ∀ z, R z = c + (gauge P (z - c))⁻¹ • (z - c) := fun z => by rw [hRdef]
  -- segments from `c` through points of the collar stay in the collar
  have hseg : ∀ z ∈ L \ K, ∀ l ∈ Icc (1 : ℝ) (gauge P (z - c))⁻¹,
      c + l • (z - c) ∈ L \ K := by
    rintro z ⟨hzL, hzK⟩ l hl
    have hzc : z ≠ c := fun h => hzK (by rw [h]; exact hcK)
    have hg0 : 0 < gauge P (z - c) := hgpos _ (sub_ne_zero.2 hzc)
    have hl0 : 0 < l := lt_of_lt_of_le one_pos hl.1
    have hlg : l * gauge P (z - c) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hl.2 hg0.le
      rwa [inv_mul_cancel₀ hg0.ne'] at this
    refine ⟨(hgle _).1 ?_, fun hy => hzK ?_⟩
    · rw [hgsmul l hl0.le]; exact hlg
    · have h1 : 0 ≤ 1 - l⁻¹ := by
        rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hl.1
      have h2 : 0 ≤ l⁻¹ := inv_nonneg.2 hl0.le
      have key := hKcv hcK hy h1 h2 (by ring)
      have heq : (1 - l⁻¹) • c + l⁻¹ • (c + l • (z - c)) = z := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hl0.ne']
        module
      rwa [heq] at key
  -- the radial projection maps `ℂ \ {c}` into the collar
  have hRin : ∀ z ∈ ({c} : Set ℂ)ᶜ, R z ∈ L \ K := by
    intro z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.2 hz
    have hg0 : 0 < gauge P (z - c) := hgpos _ hzc
    have hg : gauge P (R z - c) = 1 := by
      rw [hRapply, add_sub_cancel_left, hgsmul _ (inv_nonneg.2 hg0.le), inv_mul_cancel₀ hg0.ne']
    refine ⟨?_, fun hRK => ?_⟩
    · have := (hgle (R z - c)).1 hg.le
      simpa using this
    · have := hgK _ hRK
      rw [hg] at this
      exact lt_irrefl _ this
  -- `R` is continuous on `ℂ \ {c}`
  have hRcont : ContinuousOn R ({c} : Set ℂ)ᶜ := by
    rw [hRdef]
    apply ContinuousOn.add continuousOn_const
    have h1 : ContinuousOn (fun z : ℂ => (gauge P (z - c))⁻¹) ({c} : Set ℂ)ᶜ :=
      ContinuousOn.inv₀ (hgcont.comp (continuous_id.sub continuous_const)).continuousOn
        (fun z hz => (hgpos _ (sub_ne_zero.2 hz)).ne')
    have h2 : ContinuousOn (fun z : ℂ => z - c) ({c} : Set ℂ)ᶜ :=
      (continuous_id.sub continuous_const).continuousOn
    exact ContinuousOn.smul h1 h2
  have hFpre : IsPreconnected (R '' ({c} : Set ℂ)ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) c).isPreconnected.image
      R hRcont
  -- every collar point is joined to `R z` inside the collar
  have hSpre : ∀ z : ℂ, IsPreconnected ((fun l : ℝ => c + l • (z - c)) '' Icc (1 : ℝ) (gauge P (z - c))⁻¹) :=
    fun z => isPreconnected_Icc.image _
      ((by fun_prop : Continuous fun l : ℝ => c + l • (z - c)).continuousOn)
  have hne1 : (({c} : Set ℂ)ᶜ).Nonempty := ⟨c + 1, by simp⟩
  have hFne : (R '' ({c} : Set ℂ)ᶜ).Nonempty := hne1.image R
  obtain ⟨x0, hx0⟩ := hFne
  refine isPreconnected_of_forall x0 (fun y hy => ?_)
  obtain ⟨hyL, hyK⟩ := hy
  have hyc : y ≠ c := fun h => hyK (by rw [h]; exact hcK)
  have hg0 : 0 < gauge P (y - c) := hgpos _ (sub_ne_zero.2 hyc)
  have hg1 : gauge P (y - c) ≤ 1 := (hgle _).2 (by simpa using hyL)
  have hginv : (1 : ℝ) ≤ (gauge P (y - c))⁻¹ := (one_le_inv₀ hg0).2 hg1
  refine ⟨(fun l : ℝ => c + l • (y - c)) '' Icc (1 : ℝ) (gauge P (y - c))⁻¹ ∪ R '' ({c} : Set ℂ)ᶜ,
    ?_, Or.inr hx0, Or.inl ⟨1, ⟨le_rfl, hginv⟩, by simp⟩, ?_⟩
  · rintro w (⟨l, hl, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact hseg y ⟨hyL, hyK⟩ l hl
    · exact hRin z hz
  · refine IsPreconnected.union' ⟨R y, ⟨(gauge P (y - c))⁻¹, ⟨hginv, le_rfl⟩, by rw [hRapply]⟩,
      ⟨y, hyc, rfl⟩⟩ (hSpre y) hFpre

/-- Preconnectedness of `V \ K` for an open connected `V ⊆ ℂ` and a compact convex `K ⊆ V`
(plane domain minus a convex compact set). -/
theorem isPreconnected_diff_of_convex_compact {V K : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V)
    (hKc : IsCompact K) (hKcv : Convex ℝ K) (hKV : K ⊆ V) : IsPreconnected (V \ K) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simpa using hVc.isPreconnected
  obtain ⟨δ, hδ, hLV⟩ := hKc.exists_cthickening_subset_open hVo hKV
  obtain ⟨L, hLdef⟩ : ∃ L : Set ℂ, L = cthickening δ K := ⟨_, rfl⟩
  have hLcv : Convex ℝ L := by rw [hLdef]; exact hKcv.cthickening δ
  have hLc : IsCompact L := by rw [hLdef]; exact hKc.cthickening
  have hLV' : L ⊆ V := by rw [hLdef]; exact hLV
  have hKL : K ⊆ interior L := by
    rw [hLdef]
    exact (self_subset_thickening hδ K).trans (thickening_subset_interior_cthickening δ K)
  have hMpre : IsPreconnected (L \ K) := isPreconnected_collar_of_convex hKcv hKne hLcv hLc hKL
  have hMX : L \ K ⊆ V \ K := sdiff_subset_sdiff_left hLV'
  have hXo : IsOpen (V \ K) := hVo.sdiff hKc.isClosed
  -- every component of `V \ K` meets the collar
  have hcomp : ∀ y ∈ V \ K, (connectedComponentIn (V \ K) y ∩ (L \ K)).Nonempty := by
    intro y hy
    by_contra hne
    obtain ⟨C, hCdef⟩ : ∃ C : Set ℂ, C = connectedComponentIn (V \ K) y := ⟨_, rfl⟩
    rw [← hCdef] at hne
    have hCX : C ⊆ V \ K := by rw [hCdef]; exact connectedComponentIn_subset _ _
    have hCo : IsOpen C := by rw [hCdef]; exact hXo.connectedComponentIn
    have hyC : y ∈ C := by rw [hCdef]; exact mem_connectedComponentIn hy
    have hCL : ∀ z ∈ C, z ∉ L := fun z hz hzL => hne ⟨z, hz, hzL, (hCX hz).2⟩
    -- the closure of `C` misses `K`
    have hclK : ∀ z ∈ closure C, z ∉ K := by
      intro z hz hzK
      obtain ⟨w, hwint, hwC⟩ := mem_closure_iff.1 hz (interior L) isOpen_interior (hKL hzK)
      exact hCL w hwC (interior_subset hwint)
    -- `C` is closed in `V`
    have hclV : ∀ z ∈ closure C, z ∈ V → z ∈ C := by
      intro z hz hzV
      have hzX : z ∈ V \ K := ⟨hzV, hclK z hz⟩
      have hCpre : IsPreconnected C := by rw [hCdef]; exact isPreconnected_connectedComponentIn
      have hpc : IsPreconnected (insert z C) :=
        hCpre.subset_closure (subset_insert z C) (insert_subset_iff.2 ⟨hz, subset_closure⟩)
      have hsub : insert z C ⊆ V \ K := insert_subset hzX hCX
      have hsub2 := hpc.subset_connectedComponentIn (Or.inr hyC) hsub
      rw [← hCdef] at hsub2
      exact hsub2 (mem_insert z C)
    -- `V` is connected, so the clopen piece `C` of `V` must be all of `V`
    have hVconn := hVc.isPreconnected
    rw [isPreconnected_iff_subset_of_disjoint] at hVconn
    have hcover : V ⊆ C ∪ (closure C)ᶜ := by
      intro z hzV
      by_cases hz : z ∈ closure C
      · exact Or.inl (hclV z hz hzV)
      · exact Or.inr hz
    have hdisj : V ∩ (C ∩ (closure C)ᶜ) = ∅ := by
      ext z
      constructor
      · rintro ⟨_, hzC, hzcl⟩
        exact (hzcl (subset_closure hzC)).elim
      · intro h; simp at h
    rcases hVconn C (closure C)ᶜ hCo isClosed_closure.isOpen_compl hcover hdisj with hVC | hVcl
    · obtain ⟨k, hkK⟩ := hKne
      have hkV : k ∈ V := hKV hkK
      exact (hCX (hVC hkV)).2 hkK
    · exact (hVcl hy.1) (subset_closure hyC)
  rcases (V \ K).eq_empty_or_nonempty with hX | ⟨y0, hy0⟩
  · rw [hX]; exact isPreconnected_empty
  · obtain ⟨m0, -, hm0M⟩ := hcomp y0 hy0
    refine isPreconnected_of_forall m0 (fun y hy => ?_)
    refine ⟨connectedComponentIn (V \ K) y ∪ (L \ K), ?_, Or.inr hm0M,
      Or.inl (mem_connectedComponentIn hy), ?_⟩
    · exact union_subset (connectedComponentIn_subset _ _) hMX
    · exact IsPreconnected.union' (hcomp y hy) isPreconnected_connectedComponentIn hMpre

end LatticeProb.Topology
