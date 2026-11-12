/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Exh at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofBSp
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, end of Step 4: letting `W ↑ V`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1279–1280: "Letting `W` increase to
`V` and `W'` increase to `ℂ ∖ cl V` now concludes the proof." The deterministic input: the internal
metric on an open `V` is the infimum of the internal metrics on the dyadic domains `W` (with
connected closure, the class of `Lem2_5B`) with `cl W ⊆ V`, because every path in `V` has compact
connected range and so lies in such a `W`.

* `exists_dyadicC_of_compact`: a compact connected `K ⊆ V` lies in some `W ∈ dyadicDomainsC` with
  `cl W ⊆ V` (the squares of a fine dyadic grid meeting a thin neighbourhood of `K`).
* `internal_eq_iInf_dyadicC`: `D(u, v; V) = inf_{W ∈ 𝒲, cl W ⊆ V} D(u, v; W)`.

Own elementary proofs (DEVIATIONS entry DFB9-3).
-/

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

open LFPP

lemma convex_dfDyadicSq (k : ℤ) (j : ℤ × ℤ) : Convex ℝ (dfDyadicSq k j) := by
  have e : dfDyadicSq k j = (Complex.reLm ⁻¹' Icc ((j.1 : ℝ) * 2 ^ k) (((j.1 : ℝ) + 1) * 2 ^ k)) ∩
      (Complex.imLm ⁻¹' Icc ((j.2 : ℝ) * 2 ^ k) (((j.2 : ℝ) + 1) * 2 ^ k)) := by
    ext x; simp [dfDyadicSq, and_assoc]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

lemma closure_interior_dfDyadicSq (k : ℤ) (j : ℤ × ℤ) :
    closure (interior (dfDyadicSq k j)) = dfDyadicSq k j := by
  have hpos : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) k
  set O : Set ℂ := {x | (j.1 : ℝ) * 2 ^ k < x.re ∧ x.re < ((j.1 : ℝ) + 1) * 2 ^ k ∧
    (j.2 : ℝ) * 2 ^ k < x.im ∧ x.im < ((j.2 : ℝ) + 1) * 2 ^ k}
  have hO : IsOpen O := by
    refine ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const))))
  have hOS : O ⊆ dfDyadicSq k j := fun x hx =>
    ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩
  have hne : (interior (dfDyadicSq k j)).Nonempty := by
    refine ⟨⟨((j.1 : ℝ) + 1 / 2) * 2 ^ k, ((j.2 : ℝ) + 1 / 2) * 2 ^ k⟩,
      interior_maximal hOS hO ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp <;> nlinarith
  have hcl : IsClosed (dfDyadicSq k j) := by
    refine ((isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const))))
  rw [(convex_dfDyadicSq k j).closure_interior_eq_closure_of_nonempty_interior hne,
    hcl.closure_eq]

lemma mem_dfDyadicSq_floor (k : ℤ) (y : ℂ) :
    y ∈ dfDyadicSq k (⌊y.re / 2 ^ k⌋, ⌊y.im / 2 ^ k⌋) := by
  have hpos : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_div_iff₀ hpos).1 (Int.floor_le _)
  · exact ((div_le_iff₀ hpos).1 (Int.lt_floor_add_one _).le)
  · exact (le_div_iff₀ hpos).1 (Int.floor_le _)
  · exact ((div_le_iff₀ hpos).1 (Int.lt_floor_add_one _).le)

lemma dist_le_of_mem_dfDyadicSq {k : ℤ} {j : ℤ × ℤ} {x y : ℂ} (hx : x ∈ dfDyadicSq k j)
    (hy : y ∈ dfDyadicSq k j) : dist x y ≤ 2 * 2 ^ k := by
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 : |x.re - y.re| ≤ 2 ^ k := abs_sub_le_iff.2 ⟨by linarith [hx.2.1, hy.1],
    by linarith [hx.1, hy.2.1]⟩
  have h2 : |x.im - y.im| ≤ 2 ^ k := abs_sub_le_iff.2 ⟨by linarith [hx.2.2.2, hy.2.2.1],
    by linarith [hx.2.2.1, hy.2.2.2]⟩
  linarith

/-- a compact connected `K ⊆ V`, `V` open, lies in a dyadic domain `W` with connected closure and
`cl W ⊆ V` -/
theorem exists_dyadicC_of_compact {K V : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ W ∈ dyadicDomainsC, K ⊆ W ∧ closure W ⊆ V := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (2 : ℝ) ^ k < δ / 4 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / 4)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨-(n : ℤ), by simpa [zpow_neg, zpow_natCast, one_div, inv_pow] using hn⟩
  have hpos : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) k
  set ρ := δ / 4 with hρ
  set Kρ := thickening ρ K
  set J : Set (ℤ × ℤ) := {j | (dfDyadicSq k j ∩ Kρ).Nonempty}
  obtain ⟨R, hR⟩ := (hK.isBounded.thickening (δ := ρ)).subset_closedBall 0
  have hJfin : J.Finite := by
    set N : ℤ := ⌈R / 2 ^ k⌉ + 1
    refine ((finite_Icc (-N) N).prod (finite_Icc (-N) N)).subset ?_
    rintro j ⟨x, hxS, hxK⟩
    have hxR := mem_closedBall_zero_iff.1 (hR hxK)
    have hre : |x.re| ≤ R := (Complex.abs_re_le_norm x).trans hxR
    have him : |x.im| ≤ R := (Complex.abs_im_le_norm x).trans hxR
    have hN : R / 2 ^ k ≤ ⌈R / 2 ^ k⌉ := Int.le_ceil _
    have hNr : ((N : ℤ) : ℝ) = (⌈R / 2 ^ k⌉ : ℝ) + 1 := by simp [N]
    have key : ∀ (a : ℤ) (t : ℝ), (a : ℝ) * 2 ^ k ≤ t → t ≤ ((a : ℝ) + 1) * 2 ^ k →
        |t| ≤ R → -N ≤ a ∧ a ≤ N := by
      intro a t h1 h2 h3
      have h4 : (a : ℝ) ≤ R / 2 ^ k := by
        rw [le_div_iff₀ hpos]; linarith [(abs_le.1 h3).2]
      have h5 : -(R / 2 ^ k) - 1 ≤ (a : ℝ) := by
        have : -R ≤ ((a : ℝ) + 1) * 2 ^ k := by linarith [(abs_le.1 h3).1]
        have : -R / 2 ^ k ≤ (a : ℝ) + 1 := by rw [div_le_iff₀ hpos]; linarith
        rw [neg_div] at this; linarith
      constructor
      · have : ((-N : ℤ) : ℝ) ≤ a := by rw [Int.cast_neg, hNr]; linarith
        exact_mod_cast this
      · have : (a : ℝ) ≤ ((N : ℤ) : ℝ) := by rw [hNr]; linarith
        exact_mod_cast this
    obtain ⟨a1, a2⟩ := key j.1 x.re hxS.1 hxS.2.1 hre
    obtain ⟨b1, b2⟩ := key j.2 x.im hxS.2.2.1 hxS.2.2.2 him
    exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  set U₀ : Set ℂ := ⋃ j ∈ J, dfDyadicSq k j
  set F : Finset (ℤ × ℤ × ℤ) := hJfin.toFinset.image fun j => (k, j)
  have hU₀ : (⋃ p ∈ F, dfDyadicSq p.1 p.2) = U₀ := by
    ext x
    simp only [F, U₀, mem_iUnion, Finset.mem_image, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨p, ⟨j, hj, rfl⟩, hx⟩; exact ⟨j, hj, hx⟩
    · rintro ⟨j, hj, hx⟩; exact ⟨(k, j), ⟨j, hj, rfl⟩, hx⟩
  have hKρU : Kρ ⊆ U₀ := fun y hy =>
    mem_biUnion (x := (⌊y.re / 2 ^ k⌋, ⌊y.im / 2 ^ k⌋)) ⟨y, mem_dfDyadicSq_floor k y, hy⟩
      (mem_dfDyadicSq_floor k y)
  have hU₀cl : IsClosed U₀ := hJfin.isClosed_biUnion fun j _ =>
    (closure_interior_dfDyadicSq k j) ▸ isClosed_closure
  have hclW : closure (interior U₀) = U₀ := by
    refine subset_antisymm ((closure_mono interior_subset).trans hU₀cl.closure_eq.le) ?_
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
    rw [← closure_interior_dfDyadicSq k j] at hxj
    exact closure_mono (interior_mono (subset_biUnion_of_mem (u := fun j => dfDyadicSq k j) hj))
      hxj
  refine ⟨interior U₀, ⟨isDyadicDomain_iff.2 ⟨F, by rw [dyadicDomainOf, hU₀]⟩, ?_⟩,
    (self_subset_thickening (by positivity) K).trans (interior_maximal hKρU isOpen_thickening),
    ?_⟩
  · -- connected closure
    rw [hclW]
    obtain ⟨x₀, hx₀⟩ := hKc.nonempty
    refine ⟨⟨x₀, hKρU (self_subset_thickening (by positivity) K hx₀)⟩,
      isPreconnected_of_forall x₀ fun y hy => ?_⟩
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 hy
    obtain ⟨p, hpS, hpK⟩ := hj
    obtain ⟨x, hxK, hpx⟩ := mem_thickening_iff.1 hpK
    refine ⟨(K ∪ ball x ρ) ∪ dfDyadicSq k j, ?_, Or.inl (Or.inl hx₀), Or.inr hyj, ?_⟩
    · refine union_subset (union_subset ((self_subset_thickening (by positivity) K).trans hKρU)
        ((ball_subset_thickening hxK ρ).trans hKρU)) (subset_biUnion_of_mem
          (u := fun j => dfDyadicSq k j) ⟨p, hpS, hpK⟩)
    · refine (hKc.isPreconnected.union x hxK (mem_ball_self (by positivity))
        (convex_ball x ρ).isPreconnected).union p (Or.inr (mem_ball.2 hpx)) hpS
        (convex_dfDyadicSq k j).isPreconnected
  · -- `cl W ⊆ V`
    rw [hclW]
    refine (iUnion₂_subset fun j hj => ?_).trans hδV
    obtain ⟨p, hpS, hpK⟩ := hj
    intro y hy
    obtain ⟨x, hxK, hpx⟩ := mem_thickening_iff.1 hpK
    refine mem_cthickening_of_dist_le y x δ K hxK ?_
    calc dist y x ≤ dist y p + dist p x := dist_triangle _ _ _
      _ ≤ 2 * 2 ^ k + ρ := add_le_add (dist_le_of_mem_dfDyadicSq hy hpS) hpx.le
      _ ≤ δ := by linarith

/-- **the internal metric on `V` is the infimum over dyadic subdomains** (DFGPS T:1279–1280) -/
theorem internal_eq_iInf_dyadicC (D : ContMetric) {V : Set ℂ} (hV : IsOpen V) (u v : ℂ) :
    D.internal V u v =
      ⨅ (W : dyadicDomainsC) (_ : closure (W : Set ℂ) ⊆ V), D.internal W u v := by
  refine le_antisymm (le_iInf₂ fun W hW =>
    MetricGeometry.internalEDist_anti (image_mono (subset_closure.trans hW)) _ _) ?_
  unfold ContMetric.internal MetricGeometry.internalEDist
  refine le_iInf fun γ => ?_
  set K : Set ℂ := range (D.unpt ∘ γ.1)
  have hKc : IsConnected K := isConnected_range (D.continuous_unpt.comp γ.1.continuous)
  have hKV : K ⊆ V := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy, hyt⟩ := γ.2 t
    simp only [Function.comp_apply, ← hyt, ContMetric.unpt_pt]
    exact hy
  obtain ⟨W, hW, hKW, hWV⟩ := exists_dyadicC_of_compact
    (isCompact_range (D.continuous_unpt.comp γ.1.continuous)) hKc hV hKV
  refine iInf₂_le_of_le ⟨W, hW⟩ hWV (iInf_le_of_le ⟨γ.1, fun t => ⟨D.unpt (γ.1 t),
    hKW ⟨t, rfl⟩, ContMetric.pt_unpt _ _⟩⟩ le_rfl)

/-- `σ(D(·,·;V)) ≤ ⋁_{W ∈ 𝒲, cl W ⊆ V} σ(D(·,·;W))` for a random metric `D` -/
theorem famSigma_le_iSup_dyadicC {Ω : Type} (D : Ω → ContMetric) {V : Set ℂ} (hV : IsOpen V) :
    Blueprint.famSigma (Blueprint.internalFam D) V ≤
      ⨆ (W : dyadicDomainsC) (_ : closure (W : Set ℂ) ⊆ V),
        Blueprint.famSigma (Blueprint.internalFam D) W := by
  set M := ⨆ (W : dyadicDomainsC) (_ : closure (W : Set ℂ) ⊆ V),
    Blueprint.famSigma (Blueprint.internalFam D) W
  have hW : ∀ W : dyadicDomainsC, closure (W : Set ℂ) ⊆ V →
      Measurable[M] fun ω => Blueprint.internalFam D ω W := fun W hW' =>
    (comap_measurable _).mono (le_iSup₂_of_le W hW' le_rfl) le_rfl
  have e : (fun ω => Blueprint.internalFam D ω V) = fun ω u v =>
      ⨅ (W : dyadicDomainsC) (_ : closure (W : Set ℂ) ⊆ V), Blueprint.internalFam D ω W u v := by
    funext ω u v
    exact internal_eq_iInf_dyadicC (D ω) hV u v
  have hm : Measurable[M] fun ω => Blueprint.internalFam D ω V := by
    rw [e]
    refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
    refine Measurable.iInf fun W => Measurable.iInf fun hW' => ?_
    exact (measurable_pi_apply v).comp ((measurable_pi_apply u).comp (hW W hW'))
  exact hm.comap_le

end LQGMetric.DFGPS.L217
