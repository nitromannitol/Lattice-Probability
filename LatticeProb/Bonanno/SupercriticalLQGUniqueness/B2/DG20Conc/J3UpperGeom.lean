/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J3UpperGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J3LowerGeom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteExitMeet
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue2

 













set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 

theorem j3_connected_meets {K C : Set ℂ} (hK : IsConnected K) (hC : IsClosed C) {z y : ℂ}
    (hz : z ∈ K) (hy : y ∈ K)
    (hsep : ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → γ 0 = z → γ 1 = y →
      ∃ r ∈ Icc (0 : ℝ) 1, γ r ∈ C) :
    (K ∩ C).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hKC : K ⊆ Cᶜ := fun x hx hxC => (eq_empty_iff_forall_notMem.mp hne) x ⟨hx, hxC⟩
  set O := connectedComponentIn Cᶜ z with hO
  have hKO : K ⊆ O := hK.isPreconnected.subset_connectedComponentIn hz hKC
  have hOopen : IsOpen O := hC.isOpen_compl.connectedComponentIn
  have hOconn : IsConnected O := isConnected_connectedComponentIn_iff.mpr (hKC hz)
  have hOpc : IsPathConnected O := (hOopen.isConnected_iff_isPathConnected).mp hOconn
  obtain ⟨γ, hγ⟩ := hOpc.joinedIn z (hKO hz) y (hKO hy)
  obtain ⟨r, -, hr⟩ := hsep γ.extend γ.continuous_extend.continuousOn (by simp) (by simp)
  have hrO : γ.extend r ∈ O := by
    rw [Path.extend]
    exact hγ _
  exact (connectedComponentIn_subset _ _ hrO) hr

 

theorem j3_visited_reach {q : ℝ → ℂ} (hq : ContinuousOn q (Icc 0 1)) (S : Finset (ℤ × ℤ))
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b, q t ∈ T20.dyBlock 0 b → b ∈ S) {u v : ℤ × ℤ}
    (hu : q 0 ∈ T20.dyBlock 0 u) (hv : q 1 ∈ T20.dyBlock 0 v) :
    (S6.blkGraph S).Reachable u v := by
  classical
  set R := S.filter fun b => (S6.blkGraph S).Reachable u b
  set A : Set ℂ := ⋃ b ∈ R, T20.dyBlock 0 b
  set B : Set ℂ := ⋃ b ∈ S \ R, T20.dyBlock 0 b
  have hcl : ∀ b, IsClosed (T20.dyBlock 0 b) := fun b =>
    (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  have hA : IsClosed A := isClosed_biUnion_finset fun b _ => hcl b
  have hB : IsClosed B := isClosed_biUnion_finset fun b _ => hcl b
  have hI : IsPreconnected (q '' Icc 0 1) := isPreconnected_Icc.image _ hq
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hcov : q '' Icc 0 1 ⊆ A ∪ B := by
    rintro _ ⟨t, ht, rfl⟩
    have hbt := j3_mem_dyBlock_floor 0 (q t)
    have hbS := hS t ht _ hbt
    by_cases hbR : (⌊(q t).re * 2 ^ 0⌋, ⌊(q t).im * 2 ^ 0⌋) ∈ R
    · exact Or.inl (mem_biUnion hbR hbt)
    · exact Or.inr (mem_biUnion (Finset.mem_sdiff.2 ⟨hbS, hbR⟩) hbt)
  have hdisj : q '' Icc 0 1 ∩ (A ∩ B) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨_, hyA, hyB⟩ => ?_
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.1 hyA
    obtain ⟨b', hb', hyb'⟩ := mem_iUnion₂.1 hyB
    obtain ⟨hb'S, hb'R⟩ := Finset.mem_sdiff.1 hb'
    obtain ⟨hbS, hreach⟩ := Finset.mem_filter.1 hb
    apply hb'R
    refine Finset.mem_filter.2 ⟨hb'S, ?_⟩
    by_cases e : b = b'
    · exact e ▸ hreach
    · exact hreach.trans (SimpleGraph.Adj.reachable ⟨e, hbS, hb'S, S6.close_of_inter hyb hyb'⟩)
  have huS : u ∈ S := hS 0 h0 u hu
  have hvS : v ∈ S := hS 1 h1 v hv
  have huR : u ∈ R := Finset.mem_filter.2 ⟨huS, SimpleGraph.Reachable.refl u⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hI) A B hA hB hcov hdisj with h | h
  · obtain ⟨b, hb, hb1⟩ := mem_iUnion₂.1 (h ⟨1, h1, rfl⟩)
    obtain ⟨hbS, hreach⟩ := Finset.mem_filter.1 hb
    by_cases e : b = v
    · exact e ▸ hreach
    · exact hreach.trans (SimpleGraph.Adj.reachable ⟨e, hbS, hvS, S6.close_of_inter hb1 hv⟩)
  · exfalso
    have hq0 : q 0 ∈ q '' Icc 0 1 := ⟨0, h0, rfl⟩
    have : q 0 ∈ q '' Icc 0 1 ∩ (A ∩ B) := ⟨hq0, mem_biUnion huR hu, h hq0⟩
    rw [hdisj] at this; exact this

 
theorem j3_siteCirc_on_closed {ξ : ℝ} {f : ℂ → ℝ} {b : ℤ × ℤ} {c : ℝ≥0∞} (C : SiteCirc ξ f b c) :
    IsClosed {x | C.On x} := by
  have hc : ∀ {R : MarkedRect} {γ : ℝ → ℂ}, AdmPath R.toSet R.side₁ R.side₂ γ →
      IsCompact (γ '' Icc 0 1) := by
    intro R γ hγ
    obtain ⟨_, _, _, _, hp, _⟩ := hγ
    exact isCompact_Icc.image_of_continuousOn hp.continuousOn
  have hset : {x | C.On x} = C.B '' Icc 0 1 ∪ C.T '' Icc 0 1 ∪ C.L '' Icc 0 1 ∪
      C.R '' Icc 0 1 := by
    ext x
    simp only [SiteCirc.On, mem_setOf_eq, mem_union, mem_image, or_assoc]
  rw [hset]
  exact ((((hc C.hB).union (hc C.hT)).union (hc C.hL)).union (hc C.hR)).isClosed

 

theorem j3_connected_meets_siteCirc {ξ : ℝ} {f : ℂ → ℝ} {b : ℤ × ℤ} {c : ℝ≥0∞}
    (C : SiteCirc ξ f b c) {K : Set ℂ} (hK : IsConnected K) {z y : ℂ} (hz : z ∈ K)
    (hy : y ∈ K) (hzb : z ∈ T20.dyBlock 0 b) (hy5 : 5 ≤ dist z y) :
    ∃ a ∈ K, C.On a := by
  obtain ⟨a, haK, haC⟩ := j3_connected_meets hK (j3_siteCirc_on_closed C) hz hy
    (fun γ hγ h0 h1 => by
      refine laneB_siteCirc_meets_exit C zero_le_one hγ (by rw [h0]; exact hzb) ?_
      rw [h1]
      intro hbox
      rw [Complex.mem_reProdIm] at hbox
      obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := hbox
      obtain ⟨z1, z2, z3, z4⟩ := S6.mem_dyBlock hzb
      simp only [pow_zero, mul_one] at z1 z2 z3 z4
      have hre : |y.re - z.re| < 2 := by rw [abs_lt]; constructor <;> linarith
      have him : |y.im - z.im| < 2 := by rw [abs_lt]; constructor <;> linarith
      have hd : dist z y < 4 := by
        rw [dist_comm, dist_eq_norm]
        calc ‖y - z‖ ≤ |(y - z).re| + |(y - z).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = |y.re - z.re| + |y.im - z.im| := by simp
          _ < 4 := by linarith
      linarith)
  exact ⟨a, haK, haC⟩

 
theorem j3_site_sub {U' : Set ℂ} {q : ℝ → ℂ}
    (htube : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (q t) 5 ⊆ U') {b : ℤ × ℤ}
    (hb : ∃ t ∈ Icc (0 : ℝ) 1, q t ∈ T20.dyBlock 0 b) : SiteCirc.Sub U' b := by
  obtain ⟨t, ht, hqt⟩ := hb
  obtain ⟨z1, z2, z3, z4⟩ := S6.mem_dyBlock hqt
  simp only [pow_zero, mul_one] at z1 z2 z3 z4
  have key : ∀ x : ℂ, x.re ∈ Icc ((b.1 : ℝ) - 1) ((b.1 : ℝ) + 2) →
      x.im ∈ Icc ((b.2 : ℝ) - 1) ((b.2 : ℝ) + 2) → x ∈ U' := by
    intro x hre him
    apply htube t ht
    rw [mem_closedBall, dist_eq_norm]
    have h1 : |(x - q t).re| ≤ 2 := by
      rw [Complex.sub_re, abs_le]; constructor <;> linarith [hre.1, hre.2]
    have h2 : |(x - q t).im| ≤ 2 := by
      rw [Complex.sub_im, abs_le]; constructor <;> linarith [him.1, him.2]
    calc ‖x - q t‖ ≤ |(x - q t).re| + |(x - q t).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 := by linarith
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rw [mem_toSet_iff] at hx <;> obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hx <;>
    simp only [sB, sT, sL, sR] at a1 a2 a3 a4 <;>
    exact key x ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

 



theorem j3_upper_geometry_unit {U' K₁ K₂ : Set ℂ} {q : ℝ → ℂ} (hq : ContinuousOn q (Icc 0 1))
    (htube : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (q t) 5 ⊆ U')
    (hc₁ : IsConnected K₁) (hq0 : q 0 ∈ K₁) {y₁ : ℂ} (hy₁ : y₁ ∈ K₁) (h5₁ : 5 ≤ dist (q 0) y₁)
    (hc₂ : IsConnected K₂) (hq1 : q 1 ∈ K₂) {y₂ : ℂ} (hy₂ : y₂ ∈ K₂) (h5₂ : 5 ≤ dist (q 1) y₂)
    (S : Finset (ℤ × ℤ)) (hS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b, q t ∈ T20.dyBlock 0 b → b ∈ S)
    (hSv : ∀ b ∈ S, ∃ t ∈ Icc (0 : ℝ) 1, q t ∈ T20.dyBlock 0 b)
    {ξ : ℝ} {g : ℂ → ℝ} {ℓ : ℝ≥0∞} (hℓ : ℓ ≠ ⊤) (hℓ0 : 0 < ℓ)
    (hR : ∀ b ∈ S, ∀ i : Fin 4, rectLen ξ g (S6U.siteR b i) ≤ ℓ) :
    crossLenIn ξ g U' K₁ K₂ ≤ (2 * S.card + 1) * (8 * ℓ) := by
  classical
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hsub : ∀ b ∈ S, SiteCirc.Sub U' b := fun b hb => j3_site_sub htube (hSv b hb)
  have hcirc : ∀ b ∈ S, Nonempty (SiteCirc ξ g b (4 * (ℓ + ℓ))) := fun b hb =>
    siteCirc_of_good hℓ0 hℓ (hR b hb 0) (hR b hb 1) (hR b hb 2) (hR b hb 3)
  let Cf : ∀ b, b ∈ S → SiteCirc ξ g b (4 * (ℓ + ℓ)) := fun b hb => Classical.choice (hcirc b hb)
  let On : ℤ × ℤ → ℂ → Prop := fun b a => ∃ hb : b ∈ S, (Cf b hb).On a
  let m : ℤ × ℤ → ℂ := fun b =>
    if hb : b ∈ S then Classical.choose ((Cf b hb).hub (hsub b hb)) else 0
  have hhub : ∀ x a, On x a → lfppDOn ξ g U' a (m x) ≤ 4 * (ℓ + ℓ) := by
    rintro x a ⟨hx, ha⟩
    have := Classical.choose_spec ((Cf x hx).hub (hsub x hx)) a ha
    simpa only [m, dif_pos hx] using this
  have hmeet : ∀ x y, (S6.blkGraph S).Adj x y → ∃ q, On x q ∧ On y q := by
    rintro x y ⟨hne, hx, hy, hd1, hd2⟩
    have hadj : PercAdjK x y := by
      rw [abs_le] at hd1 hd2
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      by_contra hc
      push_neg at hc
      exact hne (Prod.ext hc.1 hc.2)
    obtain ⟨q', hq1', hq2'⟩ := SiteCirc.meet_adjK (Cf x hx) (Cf y hy) hadj
    exact ⟨q', ⟨hx, hq1'⟩, ⟨hy, hq2'⟩⟩
  
  set b₁ := (⌊(q 0).re * 2 ^ 0⌋, ⌊(q 0).im * 2 ^ 0⌋) with hb₁
  set b₂ := (⌊(q 1).re * 2 ^ 0⌋, ⌊(q 1).im * 2 ^ 0⌋) with hb₂
  have hq0b : q 0 ∈ T20.dyBlock 0 b₁ := j3_mem_dyBlock_floor 0 (q 0)
  have hq1b : q 1 ∈ T20.dyBlock 0 b₂ := j3_mem_dyBlock_floor 0 (q 1)
  have hb₁S : b₁ ∈ S := hS 0 h0 b₁ hq0b
  have hb₂S : b₂ ∈ S := hS 1 h1 b₂ hq1b
  obtain ⟨p⟩ := j3_visited_reach hq S hS hq0b hq1b
  have hsupp : ∀ x ∈ p.support, x ∈ S := by
    have key : ∀ {u v : ℤ × ℤ} (w : (S6.blkGraph S).Walk u v), u ∈ S → ∀ x ∈ w.support, x ∈ S := by
      intro u v w
      induction w with
      | nil => intro hu x hx; simp at hx; exact hx ▸ hu
      | cons hadj w ih =>
        intro hu x hx
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hu
        · exact ih hadj.2.2.1 x hx
    exact key p hb₁S
  have hchain := chain_dOn_finset On m (fun _ => 4 * (ℓ + ℓ)) hhub hmeet S p hsupp
  
  obtain ⟨a, haK, haC⟩ := j3_connected_meets_siteCirc (Cf b₁ hb₁S) hc₁ hq0 hy₁ hq0b h5₁
  obtain ⟨a', ha'K, ha'C⟩ := j3_connected_meets_siteCirc (Cf b₂ hb₂S) hc₂ hq1 hy₂ hq1b h5₂
  have hfirst := hchain a ⟨hb₁S, haC⟩
  have hlast : lfppDOn ξ g U' (m b₂) a' ≤ 4 * (ℓ + ℓ) := by
    rw [lfppDOn_comm]; exact hhub b₂ a' ⟨hb₂S, ha'C⟩
  have hcross : crossLenIn ξ g U' K₁ K₂ ≤ lfppDOn ξ g U' a a' :=
    (iInf₂_le a haK).trans (iInf₂_le a' ha'K)
  have hsum : ∑ _x ∈ S, 4 * (ℓ + ℓ) = (S.card : ℝ≥0∞) * (8 * ℓ) := by
    rw [Finset.sum_const, nsmul_eq_mul]; congr 1; rw [← two_mul, ← mul_assoc]; norm_num
  calc crossLenIn ξ g U' K₁ K₂ ≤ lfppDOn ξ g U' a a' := hcross
    _ ≤ lfppDOn ξ g U' a (m b₂) + lfppDOn ξ g U' (m b₂) a' := lfppDOn_triangle _ _ _
    _ ≤ 2 * ∑ _x ∈ S, 4 * (ℓ + ℓ) + 4 * (ℓ + ℓ) := add_le_add hfirst hlast
    _ = (2 * S.card + 1) * (8 * ℓ) := by
        rw [hsum, show 4 * (ℓ + ℓ) = 8 * ℓ by rw [← two_mul, ← mul_assoc]; norm_num]
        ring

end SupercriticalLQGUniqueness.B2.DG20Conc
