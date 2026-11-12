/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.JordanPunct at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

/-!
# The punctured filled ball `𝓑^•_s ∖ {z}` is connected (DEC-B node J1d, first half)

Needed to see that, after the inversion `x ↦ 1/(x − z)`, the complement of the image of
`U = ℂ ∖ 𝓑^•_s` is connected and unbounded, so that the image (plus `0`) is a bounded simply
connected domain (QuantumZipper `hasHoloSqrt_of_unbounded_compl`). Own elementary arguments
(standard plane topology, no source needed: removing a point from an open connected plane set;
the closure of a component of `ℂ ∖ X` meets `X`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- A punctured disc is preconnected (image of `(0, r) × S¹` under polar coordinates). -/
theorem jp_isPreconnected_ball_diff (z : ℂ) (r : ℝ) : IsPreconnected (ball z r \ {z}) := by
  have he : ball z r \ {z} =
      (fun p : ℝ × ℂ => z + (p.1 : ℂ) * p.2) '' (Ioo 0 r ×ˢ sphere (0 : ℂ) 1) := by
    ext w
    constructor
    · rintro ⟨hw, hwz⟩
      have hpos : 0 < ‖w - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hwz)
      refine ⟨(‖w - z‖, (w - z) / (‖w - z‖ : ℂ)), ⟨⟨hpos, ?_⟩, ?_⟩, ?_⟩
      · rwa [mem_ball, dist_eq_norm] at hw
      · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpos, div_self hpos.ne']
      · have : (‖w - z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
        simp only
        field_simp
        ring
    · rintro ⟨⟨ρ, u⟩, ⟨⟨hρ0, hρr⟩, hu⟩, rfl⟩
      have hun : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
      have hn : ‖z + (ρ : ℂ) * u - z‖ = ρ := by
        rw [add_sub_cancel_left, norm_mul, hun, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hρ0]
      refine ⟨by rw [mem_ball, dist_eq_norm, hn]; exact hρr, fun h => ?_⟩
      rw [mem_singleton_iff] at h
      have h' : z + (ρ : ℂ) * u = z := h
      rw [h', sub_self, norm_zero] at hn
      exact hρ0.ne' hn.symm
  rw [he]
  exact (isPreconnected_Ioo.prod LQGMetric.JordanMap.jm_isPreconnected_sphere).image _
    (by fun_prop)

/-- Removing a point from an open preconnected plane set leaves it preconnected. -/
theorem jp_isPreconnected_diff_singleton {V : Set ℂ} (hVo : IsOpen V) (hV : IsPreconnected V)
    (z : ℂ) : IsPreconnected (V \ {z}) := by
  by_cases hz : z ∈ V
  swap
  · rwa [diff_singleton_eq_self hz]
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo z hz
  have key : ∀ u' v' : Set ℂ, IsOpen u' → IsOpen v' → Disjoint u' v' → v' ⊆ V \ {z} →
      V \ {z} ⊆ u' ∪ v' → ball z r \ {z} ⊆ u' → v'.Nonempty → False := by
    intro u' v' hu' hv' hd hv'S hcov' hBu ⟨y, hy⟩
    have hd2 : Disjoint (u' ∪ ball z r) v' := by
      refine disjoint_union_left.2 ⟨hd, disjoint_left.2 fun x hxB hxv => ?_⟩
      have hxz : x ≠ z := fun h => (hv'S hxv).2 h
      exact disjoint_left.1 hd (hBu ⟨hxB, hxz⟩) hxv
    have hVsub : V ⊆ (u' ∪ ball z r) ∪ v' := fun x hx => by
      by_cases hxz : x = z
      · exact Or.inl (Or.inr (hxz ▸ mem_ball_self hr))
      · rcases hcov' ⟨hx, hxz⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    rcases hV.subset_or_subset (hu'.union isOpen_ball) hv' hd2 hVsub with h | h
    · exact disjoint_left.1 hd2 (h (hv'S hy).1) hy
    · exact (hv'S (h hz)).2 rfl
  intro u v hu hv hcov ⟨a, haS, hau⟩ ⟨b, hbS, hbv⟩
  by_contra hne
  have hVz : IsOpen (V \ {z}) := hVo.sdiff isClosed_singleton
  have hdisj : Disjoint (u ∩ (V \ {z})) (v ∩ (V \ {z})) :=
    disjoint_left.2 fun x hxu hxv => hne ⟨x, hxu.2, hxu.1, hxv.1⟩
  have hcov' : V \ {z} ⊆ (u ∩ (V \ {z})) ∪ (v ∩ (V \ {z})) := fun x hx => by
    rcases hcov hx with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hx⟩
  have hBsub : ball z r \ {z} ⊆ (u ∩ (V \ {z})) ∪ (v ∩ (V \ {z})) := fun x hx =>
    hcov' ⟨hrV hx.1, hx.2⟩
  rcases (jp_isPreconnected_ball_diff z r).subset_or_subset (hu.inter hVz) (hv.inter hVz) hdisj
      hBsub with h | h
  · exact key _ _ (hu.inter hVz) (hv.inter hVz) hdisj inter_subset_right hcov' h
      ⟨b, hbv, hbS⟩
  · exact key _ _ (hv.inter hVz) (hu.inter hVz) hdisj.symm inter_subset_right
      (fun x hx => (hcov' hx).symm) h ⟨a, hau, haS⟩

variable {D : ContMetric} {z : ℂ} {s : ℝ}

/-- The frontier of a component `C` of `ℂ ∖ X` (`X = cl 𝓑_s`) lies in `X`. -/
theorem jp_frontier_cc_subset (y : ℂ) :
    frontier (connectedComponentIn (closure (ballM D z s))ᶜ y) ⊆ closure (ballM D z s) := by
  intro p hp
  by_contra hpX
  have hpo : IsOpen (connectedComponentIn (closure (ballM D z s))ᶜ p) := jb_isOpen_cc p
  obtain ⟨c, hcp, hcC⟩ := mem_closure_iff.1 hp.1 _ hpo (mem_connectedComponentIn hpX)
  have h1 := connectedComponentIn_eq hcp
  have h2 := connectedComponentIn_eq hcC
  have hpC : p ∈ connectedComponentIn (closure (ballM D z s))ᶜ y := by
    rw [h2, ← h1]
    exact mem_connectedComponentIn hpX
  exact hp.2 ((jb_isOpen_cc y).interior_eq.symm ▸ hpC)

/-- **J1d (first half).** `𝓑^•_s ∖ {z}` is preconnected. -/
theorem jp_isPreconnected_filledBall_diff (hs : 0 < s) (hL : D.IsLength) :
    IsPreconnected (filledBall D z s \ {z}) := by
  set X := closure (ballM D z s) with hX
  have hBo := jb_isOpen_ballM D z s
  have hBz : IsPreconnected (ballM D z s \ {z}) :=
    jp_isPreconnected_diff_singleton hBo (jb_isPreconnected_ballM D z s hL) z
  have hXz : IsPreconnected (X \ {z}) := by
    refine hBz.subset_closure (diff_subset_diff_left subset_closure) ?_
    intro x hx
    have h1 : ballM D z s ⊆ closure (ballM D z s ∩ {z}ᶜ) :=
      (dense_compl_singleton z).open_subset_closure_inter hBo
    rw [← diff_eq] at h1
    exact closure_minimal h1 isClosed_closure hx.1
  -- a base point of `𝓑_s ∖ {z}`
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 hBo z (jb_mem_ballM D z s hs)
  set x₀ : ℂ := z + ((r / 2 : ℝ) : ℂ) with hx₀
  have hx₀B : x₀ ∈ ballM D z s \ {z} := by
    have hn : ‖x₀ - z‖ = r / 2 := by
      rw [hx₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    refine ⟨hrB (by rw [mem_ball, dist_eq_norm, hn]; linarith), fun h => ?_⟩
    rw [mem_singleton_iff] at h
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hx₀X : x₀ ∈ X \ {z} := ⟨subset_closure hx₀B.1, hx₀B.2⟩
  have hXK : X \ {z} ⊆ filledBall D z s \ {z} := diff_subset_diff_left subset_union_left
  refine isPreconnected_of_forall x₀ fun y hy => ?_
  by_cases hyX : y ∈ X
  · exact ⟨X \ {z}, hXK, hx₀X, ⟨hyX, hy.2⟩, hXz⟩
  -- `y` lies in a bounded component `C` of `ℂ ∖ X`
  set C := connectedComponentIn Xᶜ y with hC
  have hyC : y ∈ C := mem_connectedComponentIn hyX
  have hCb : Bornology.IsBounded C := by
    rcases hy.1 with h | ⟨_, h⟩
    · exact absurd h hyX
    · exact h
  have hCK : C ⊆ filledBall D z s := jb_cc_subset y hyX hCb
  have hzC : z ∉ closure C := by
    intro h
    obtain ⟨c, hcB, hcC⟩ := mem_closure_iff.1 h _ hBo (jb_mem_ballM D z s hs)
    exact connectedComponentIn_subset _ _ hcC (subset_closure hcB)
  have hfr : (frontier C).Nonempty := by
    refine nonempty_frontier_iff.2 ⟨⟨y, hyC⟩, fun h => ?_⟩
    exact jb_not_isBounded_lt_norm 0 (hCb.subset (h ▸ subset_univ _))
  obtain ⟨p, hp⟩ := hfr
  have hpX : p ∈ X := jp_frontier_cc_subset y hp
  have hclK : closure C ⊆ filledBall D z s \ {z} := by
    intro c hc
    refine ⟨?_, fun h => hzC (mem_singleton_iff.1 h ▸ hc)⟩
    by_cases hcC : c ∈ C
    · exact hCK hcC
    · exact Or.inl (jp_frontier_cc_subset y ⟨hc, fun h => hcC (interior_subset h)⟩)
  refine ⟨X \ {z} ∪ closure C, union_subset hXK hclK, Or.inl hx₀X, Or.inr (subset_closure hyC),
    IsPreconnected.union' ⟨p, ⟨hpX, fun h => hzC (mem_singleton_iff.1 h ▸ hp.1)⟩, hp.1⟩ hXz
      isPreconnected_connectedComponentIn.closure⟩

/-- **J0**: `𝓑^•_s` is preconnected. -/
theorem jp_isPreconnected_filledBall (hs : 0 < s) (hL : D.IsLength) :
    IsPreconnected (filledBall D z s) := by
  refine (jp_isPreconnected_filledBall_diff hs hL).subset_closure diff_subset fun x hx => ?_
  by_cases hxz : x = z
  · rw [hxz]
    have h1 : ballM D z s ⊆ closure (ballM D z s ∩ {z}ᶜ) :=
      (dense_compl_singleton _).open_subset_closure_inter (jb_isOpen_ballM D z s)
    rw [← diff_eq] at h1
    exact closure_mono (diff_subset_diff_left (subset_closure.trans subset_union_left))
      (h1 (jb_mem_ballM D z s hs))
  · exact subset_closure ⟨hx, hxz⟩

/-- **J0**: every point of `∂𝓑^•_s` is at `D`-distance exactly `s` from `z`. -/
theorem jp_frontier_subset_sphere (hbd : Bornology.IsBounded (ballM D z s)) :
    frontier (filledBall D z s) ⊆ {x | D.1 (z, x) = s} := by
  intro x hx
  have hcl : closure (ballM D z s) ⊆ {x | D.1 (z, x) ≤ s} :=
    closure_minimal (fun y (hy : D.1 (z, y) < s) => show D.1 (z, y) ≤ s from hy.le)
      (isClosed_le (D.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const)
  refine le_antisymm (hcl (jb_frontier_subset_closure hbd hx)) (not_lt.1 fun h => ?_)
  exact disjoint_left.1 jb_disjoint_ballM_frontier h hx

end LQGMetric.GM
