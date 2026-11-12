/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrdCara at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.Lift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Jordan
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

/-!
# TOPO-ORD, step 2a: Carathéodory maps of inverted exteriors (generic compact sets)

Setting of `TopoOrd` (`Lift.lean`, DEC-D (b)): `K` compact, `z ∈ int K`, `ℂ ∖ K` connected,
`∂K` the range of a positive Jordan lift. With `ι(x) = 1/(x − z)`,
`Ω(K) := ι(ℂ ∖ K) ∪ {0}` (`toOmega`) is a bounded Jordan domain containing `0` all of whose
complementary components are unbounded, so Carathéodory's theorem
(`JordanMap.jm_jordan_closedDisc_extension'`, Pommerenke 1992 Thm 2.6) gives `f : 𝔻̄ → Ω̄`
continuous, injective, holomorphic inside, `f 0 = 0`, `f(∂𝔻) = ι(∂K)`.

This is the generic form of GM `jo_disc_map` (`Papers/GM/S4/Jordan*.lean`, task P2-M2I), whose
proofs are copied here with `filledBall D z s` replaced by `K`. The only new inputs: `K` is
connected (each component of `int K` is bounded, hence has frontier points, which lie on the
connected curve `∂K`), hence `K ∖ {z}` is connected (`z ∈ int K`); and `∂K` is a Jordan curve in
the sense of `IsJordanCurve` (parametrize the circle by `arg`). Own elementary arguments
(standard plane topology), recorded in DEVIATIONS (DV-CONF-TO1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF.DD

/-- `Ω(K) = ι(ℂ ∖ K) ∪ {0}`, `ι(x) = 1/(x − z)` -/
def toOmega (K : Set ℂ) (z : ℂ) : Set ℂ := {w | z + w⁻¹ ∉ K} ∪ {0}

section Omega

variable {K : Set ℂ} {z : ℂ}

theorem to_far (hK : IsCompact K) : ∃ δ > 0, ∀ w : ℂ, w ≠ 0 → ‖w‖ < δ → z + w⁻¹ ∉ K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set A := |R| + ‖z‖ + 1 with hA
  have hApos : 0 < A := by positivity
  refine ⟨1 / A, by positivity, fun w hw0 hw hwK => ?_⟩
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have h1 : A < ‖w⁻¹‖ := by
    rw [norm_inv, lt_inv_comm₀ hApos hwpos, ← one_div]
    exact hw
  have h2 := hR hwK
  rw [mem_closedBall, dist_zero_right] at h2
  have h3 : ‖w⁻¹‖ ≤ ‖z + w⁻¹‖ + ‖z‖ := by
    calc ‖w⁻¹‖ = ‖(z + w⁻¹) - z‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖z + w⁻¹‖ + ‖z‖ := norm_sub_le _ _
  linarith [le_abs_self R]

theorem to_near (hz : z ∈ interior K) :
    ∃ r > 0, ∀ w : ℂ, z + w⁻¹ ∉ K → w ≠ 0 ∧ r ≤ ‖w⁻¹‖ := by
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  refine ⟨r, hr, fun w hw => ⟨fun h => ?_, ?_⟩⟩
  · apply hw
    rw [h, inv_zero, add_zero]
    exact interior_subset hz
  by_contra h
  apply hw
  refine interior_subset (hrB ?_)
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
  exact not_le.1 h

theorem to_omega_eq (hz : z ∈ interior K) :
    toOmega K z = (fun x => (x - z)⁻¹) '' Kᶜ ∪ {0} := by
  ext w
  simp only [toOmega, mem_union, mem_setOf_eq, mem_image, mem_compl_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨z + w⁻¹, h, GM.jo_inv_right⟩
    · exact Or.inr h
  · rintro (⟨x, hx, rfl⟩ | h)
    · left
      have hxz : x ≠ z := fun e => hx (e ▸ interior_subset hz)
      rwa [GM.jo_inv_left hxz]
    · exact Or.inr h

theorem to_isOpen_omega (hK : IsCompact K) (hz : z ∈ interior K) : IsOpen (toOmega K z) := by
  obtain ⟨δ, hδ, hfar⟩ := to_far (z := z) hK
  have he : toOmega K z = ({0}ᶜ ∩ (fun w => z + w⁻¹) ⁻¹' Kᶜ) ∪ ball 0 δ := by
    ext w
    simp only [toOmega, mem_union, mem_setOf_eq, mem_inter_iff, mem_compl_iff,
      mem_singleton_iff, mem_preimage, mem_ball_zero_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨fun e => h (by rw [e, inv_zero, add_zero]; exact interior_subset hz), h⟩
      · exact Or.inr (by rw [h, norm_zero]; exact hδ)
    · rintro (⟨-, h⟩ | h)
      · exact Or.inl h
      · by_cases hw : w = 0
        · exact Or.inr hw
        · exact Or.inl (hfar w hw h)
  rw [he]
  refine (ContinuousOn.isOpen_inter_preimage ?_ isOpen_compl_singleton
    hK.isClosed.isOpen_compl).union isOpen_ball
  exact continuousOn_const.add continuousOn_inv₀

theorem to_omega_subset (hz : z ∈ interior K) :
    ∃ r > 0, toOmega K z ⊆ closedBall 0 (1 / r) := by
  obtain ⟨r, hr, hnear⟩ := to_near hz
  refine ⟨r, hr, fun w hw => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  rcases hw with hw | hw
  · obtain ⟨hw0, hwr⟩ := hnear w hw
    rw [norm_inv] at hwr
    rw [le_div_iff₀ hr]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    calc ‖w‖ * r ≤ ‖w‖ * ‖w‖⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hwpos.ne'
  · rw [mem_singleton_iff.1 hw, norm_zero]
    positivity

theorem to_isPreconnected_omega (hK : IsCompact K) (hz : z ∈ interior K)
    (hKc : IsPreconnected Kᶜ) : IsPreconnected (toOmega K z) := by
  obtain ⟨δ, hδ, hfar⟩ := to_far (z := z) hK
  have hzU : z ∉ Kᶜ := fun h => h (interior_subset hz)
  have hI : IsPreconnected ((fun x => (x - z)⁻¹) '' Kᶜ) :=
    hKc.image _ (GM.jo_continuousOn_iota _ hzU)
  have he : toOmega K z = (fun x => (x - z)⁻¹) '' Kᶜ ∪ ball 0 δ := by
    rw [to_omega_eq hz]
    apply subset_antisymm
    · exact union_subset_union subset_rfl (singleton_subset_iff.2 (mem_ball_self hδ))
    · refine union_subset subset_union_left fun w hw => ?_
      by_cases hw0 : w = 0
      · exact Or.inr hw0
      · exact Or.inl ⟨z + w⁻¹, hfar w hw0 (mem_ball_zero_iff.1 hw), GM.jo_inv_right⟩
  set w₀ : ℂ := ((δ / 2 : ℝ) : ℂ)
  have hw₀ : w₀ ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hw₀n : ‖w₀‖ < δ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  rw [he]
  exact hI.union' ⟨w₀, ⟨z + w₀⁻¹, hfar w₀ hw₀ hw₀n, GM.jo_inv_right⟩, mem_ball_zero_iff.2 hw₀n⟩
    isPreconnected_ball

theorem to_compl_omega :
    (toOmega K z)ᶜ = (fun x => (x - z)⁻¹) '' (K \ {z}) := by
  ext w
  simp only [toOmega, mem_compl_iff, mem_union, mem_setOf_eq, mem_singleton_iff, not_or,
    not_not, mem_image, mem_diff]
  constructor
  · rintro ⟨hK, hw0⟩
    refine ⟨z + w⁻¹, ⟨hK, fun e => hw0 ?_⟩, GM.jo_inv_right⟩
    have : w⁻¹ = 0 := by
      have := congrArg (· - z) e
      simpa using this
    exact inv_eq_zero.1 this
  · rintro ⟨x, ⟨hxK, hxz⟩, rfl⟩
    refine ⟨by rwa [GM.jo_inv_left hxz], inv_ne_zero (sub_ne_zero.2 hxz)⟩

theorem to_frontier_omega (hK : IsCompact K) (hz : z ∈ interior K) :
    frontier (toOmega K z) = (fun x => (x - z)⁻¹) '' frontier K := by
  have hΩo := to_isOpen_omega hK hz
  have hKc := hK.isClosed
  have hzF : z ∉ frontier K := fun h => h.2 hz
  rw [hΩo.frontier_eq]
  apply subset_antisymm
  · rintro w ⟨hwcl, hwΩ⟩
    have hwK : z + w⁻¹ ∈ K := by
      by_contra h
      exact hwΩ (Or.inl h)
    have hw0 : w ≠ 0 := fun h => hwΩ (Or.inr h)
    have hcont : ContinuousAt (fun w : ℂ => z + w⁻¹) w :=
      continuousAt_const.add (continuousAt_inv₀ hw0)
    have h1 := mem_closure_image hcont hwcl
    have himg : (fun w : ℂ => z + w⁻¹) '' toOmega K z ⊆ Kᶜ ∪ {z} := by
      rintro _ ⟨v, hv | hv, rfl⟩
      · exact Or.inl hv
      · rw [mem_singleton_iff.1 hv]
        show z + (0 : ℂ)⁻¹ ∈ _
        rw [inv_zero, add_zero]
        exact Or.inr rfl
    have h2 := closure_mono himg h1
    rw [closure_union, closure_singleton] at h2
    have hne : z + w⁻¹ ≠ z := fun e => hw0 (inv_eq_zero.1 (by simpa using congrArg (· - z) e))
    have h3 : z + w⁻¹ ∈ closure Kᶜ := h2.resolve_right hne
    refine ⟨z + w⁻¹, ?_, GM.jo_inv_right⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hwK, h3⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxz : x ≠ z := fun e => hzF (e ▸ hx)
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun x : ℂ => (x - z)⁻¹) x :=
        (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hxz)
      have hxU : x ∈ closure Kᶜ := by
        rw [← frontier_compl] at hx
        exact frontier_subset_closure hx
      refine closure_mono ?_ (mem_closure_image (f := fun x : ℂ => (x - z)⁻¹) hcont hxU)
      rw [to_omega_eq hz]
      exact subset_union_left
    · rintro (h | h)
      · exact h (by rw [GM.jo_inv_left hxz]; exact hKc.frontier_subset hx)
      · exact inv_ne_zero (sub_ne_zero.2 hxz) (mem_singleton_iff.1 h)

/-- `K` is connected when `∂K` is connected (components of `int K` reach `∂K`) -/
theorem to_isPreconnected_K (hK : IsCompact K) (hJ : IsPreconnected (frontier K))
    (hJne : (frontier K).Nonempty) : IsPreconnected K := by
  obtain ⟨x₀, hx₀⟩ := hJne
  have hJK : frontier K ⊆ K := hK.isClosed.frontier_subset
  refine isPreconnected_of_forall x₀ fun y hy => ?_
  by_cases hyJ : y ∈ frontier K
  · exact ⟨frontier K, hJK, hx₀, hyJ, hJ⟩
  have hyi : y ∈ interior K := by
    by_contra h
    exact hyJ ⟨subset_closure hy, h⟩
  set C := connectedComponentIn (interior K) y with hC
  have hCK : closure C ⊆ K := by
    rw [← hK.isClosed.closure_eq]
    exact closure_mono ((connectedComponentIn_subset _ _).trans interior_subset)
  have hCpc : IsPreconnected (closure C) := isPreconnected_connectedComponentIn.closure
  have hmeet : (frontier K ∩ closure C).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hsub : closure C ⊆ interior K := by
      intro x hx
      by_contra h
      have : x ∈ frontier K := ⟨subset_closure (hCK hx), h⟩
      exact (eq_empty_iff_forall_notMem.1 hne) x ⟨this, hx⟩
    have hcl : closure C ⊆ C :=
      hCpc.subset_connectedComponentIn (subset_closure (mem_connectedComponentIn hyi)) hsub
    have hclo : IsClopen C :=
      ⟨closure_subset_iff_isClosed.1 hcl, isOpen_interior.connectedComponentIn⟩
    have hU := hclo.eq_univ ⟨y, mem_connectedComponentIn hyi⟩
    have hb : Bornology.IsBounded (univ : Set ℂ) :=
      hU ▸ hK.isBounded.subset ((connectedComponentIn_subset _ _).trans interior_subset)
    exact GM.jb_not_isBounded_lt_norm 0 (hb.subset (subset_univ _))
  exact ⟨frontier K ∪ closure C, union_subset hJK hCK, Or.inl hx₀,
    Or.inr (subset_closure (mem_connectedComponentIn hyi)), hJ.union' hmeet hCpc⟩

theorem to_isPreconnected_punct (r : ℝ) : IsPreconnected (ball z r \ {z}) := by
  have he : ball z r \ {z} = (fun p : ℝ × ℝ => z + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) *
      Complex.I)) '' (Ioo 0 r ×ˢ univ) := by
    ext x
    simp only [mem_diff, mem_ball, mem_singleton_iff, mem_image, mem_prod, mem_Ioo, mem_univ,
      and_true, Prod.exists, dist_eq_norm]
    constructor
    · rintro ⟨hx, hxz⟩
      refine ⟨‖x - z‖, Complex.arg (x - z), ⟨norm_pos_iff.2 (sub_ne_zero.2 hxz), hx⟩, ?_⟩
      rw [Complex.norm_mul_exp_arg_mul_I]; ring
    · rintro ⟨ρ, t, ⟨hρ, hρr⟩, rfl⟩
      have hn : ‖(ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ = ρ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hρ]
      refine ⟨by rw [add_sub_cancel_left, hn]; exact hρr, fun h => ?_⟩
      have : (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) = 0 := by
        have := congrArg (· - z) h; simpa using this
      rw [← hn, this, norm_zero] at hρ
      exact lt_irrefl _ hρ
  rw [he]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ (by fun_prop)

/-- removing an interior point keeps `K` connected -/
theorem to_isPreconnected_diff (hKp : IsPreconnected K) (hz : z ∈ interior K) :
    IsPreconnected (K \ {z}) := by
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hB : ball z r \ {z} ⊆ K \ {z} := sdiff_subset_sdiff_left (hrB.trans interior_subset)
  have hBp := to_isPreconnected_punct (z := z) r
  -- if the punctured ball misses `v`, `K` is disconnected
  have key : ∀ u v : Set ℂ, IsOpen u → IsOpen v → K \ {z} ⊆ u ∪ v → (K \ {z} ∩ u).Nonempty →
      (K \ {z} ∩ v).Nonempty → (K \ {z} ∩ (u ∩ v)) = ∅ → (ball z r \ {z}) ∩ v = ∅ → False := by
    intro u v hu hv hcov hnu hnv hdis hBv
    have hcov' : K ⊆ (u ∪ ball z r) ∪ (v \ {z}) := by
      intro x hx
      by_cases hxz : x = z
      · exact Or.inl (Or.inr (hxz ▸ mem_ball_self hr))
      · rcases hcov ⟨hx, hxz⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hxz⟩
    obtain ⟨x, hxK, hxu, hxv⟩ := hKp _ _ (hu.union isOpen_ball) (hv.sdiff isClosed_singleton)
      hcov' (let ⟨x, hx, hxu⟩ := hnu; ⟨x, hx.1, Or.inl hxu⟩)
      (let ⟨x, hx, hxv⟩ := hnv; ⟨x, hx.1, hxv, hx.2⟩)
    rcases hxu with h | h
    · exact (eq_empty_iff_forall_notMem.1 hdis) x ⟨⟨hxK, hxv.2⟩, h, hxv.1⟩
    · exact (eq_empty_iff_forall_notMem.1 hBv) x ⟨⟨h, hxv.2⟩, hxv.1⟩
  intro u v hu hv hcov hnu hnv
  by_contra hdis
  rw [not_nonempty_iff_eq_empty] at hdis
  have hBne : (ball z r \ {z}).Nonempty := by
    refine ⟨z + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]; linarith
    · intro h
      have : ((r / 2 : ℝ) : ℂ) = 0 := by have := congrArg (· - z) h; simpa using this
      exact (show (r / 2 : ℝ) ≠ 0 by positivity) (by exact_mod_cast this)
  by_cases hBv : (ball z r \ {z}) ∩ v = ∅
  · exact key u v hu hv hcov hnu hnv hdis hBv
  by_cases hBu : (ball z r \ {z}) ∩ u = ∅
  · exact key v u hv hu (by rw [union_comm]; exact hcov) hnv hnu
      (by rw [inter_comm v u]; exact hdis) hBu
  obtain ⟨x, hxB, hxu, hxv⟩ := hBp u v hu hv (hB.trans hcov) (nonempty_iff_ne_empty.2 hBu)
    (nonempty_iff_ne_empty.2 hBv)
  exact (eq_empty_iff_forall_notMem.1 hdis) x ⟨hB hxB, hxu, hxv⟩

end Omega

end LQGMetric.CONF.DD
