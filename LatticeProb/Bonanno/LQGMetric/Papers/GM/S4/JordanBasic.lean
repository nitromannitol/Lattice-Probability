/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.JordanBasic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.Analysis.Normed.Module.Connected
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep

/-!
# Filled metric balls: elementary plane topology (DEC-B J0, J1a, J1c)

Setting of `decisions/DEC-B.md` question (b): `D` a continuous metric on `ℂ` (inducing the
Euclidean topology), a length metric, with bounded balls around the centre `z`
(GPS arXiv:2010.07889 Lemma 2.4: `D(w, x) → ∞` as `x → ∞`); `X := cl 𝓑_s(z; D)`,
`K := 𝓑^•_s(z; D)` (`Blueprint.filledBall`), `U := ℂ ∖ K`, `Γ := ∂K = ∂U`.

* **J0** (elementary): `K` is closed and bounded (compact), `U` is the unbounded component of
  `ℂ ∖ X` (hence open, connected), `𝓑_s ⊆ int K`, `Γ ⊆ cl 𝓑_s`, and `𝓑_s` is connected
  (length metric: paths of length `< s` from `z` stay in `𝓑_s`).
* **J1a** (Miller–Sheffield arXiv:1506.03806, proof of Prop 2.1, first paragraph,
  `mapmaking_final.tex` l. 566–570): every point of `Γ` is a limit of points of `U` and of
  `𝓑_s ⊆ Ũ`, and `Γ` separates `U` from `z` (`jb_not_mem_cc`).
* **J1c** (own argument, DV-B13): `Γ ∖ {q}` is preconnected for every `q ∈ ℂ` (for `q ∉ Γ`
  this says `Γ` is connected). Proof from Janiszewski's theorem (QuantumZipper
  `CA.Topo.janiszewski`, Burckel Ex. 4.37(ii)): if `Γ ∖ {q} = A ⊔ B`, one of the compact sets
  `A ∪ T`, `B ∪ T` (`T = Γ ∩ {q}`) separates a point of `U` from `z`; a small disk around a
  point of the other part misses it and meets `U` and `𝓑_s`, so `U ∪ disk ∪ 𝓑_s` joins them.
  This replaces MS's "two loops touch only at one point" argument (tex l. 610), which needs the
  Jordan curve theorem (absent from mathlib and QuantumZipper).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable (D : ContMetric) (z : ℂ) (s : ℝ)

theorem jb_isOpen_ballM : IsOpen (ballM D z s) :=
  isOpen_lt (D.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const

theorem jb_mem_ballM (hs : 0 < s) : z ∈ ballM D z s := by
  show D.1 (z, z) < s
  rw [D.2.self_eq_zero]
  exact hs

/-- **J0**: for a length metric, `𝓑_s(z; D)` is preconnected (paths of `D`-length `< s` from
`z` stay in it). -/
theorem jb_isPreconnected_ballM (hL : D.IsLength) : IsPreconnected (ballM D z s) := by
  refine isPreconnected_of_forall z fun w hw => ?_
  have hw' : D.1 (z, w) < s := hw
  set ε := (s - D.1 (z, w)) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨γ, hγ⟩ := hL (D.pt z) (D.pt w) ε hεpos
  have hpt : ∀ t, D.1 (z, D.unpt (γ t)) < s := by
    intro t
    have h1 : edist (D.pt z) (γ t) ≤ MetricGeometry.pathLength γ := by
      have h := MetricGeometry.edist_le_curveLength γ.extend t.2.1
      rw [Path.extend_zero, Path.extend_extends'] at h
      exact h.trans (MetricGeometry.curveLength_mono _ le_rfl t.2.2)
    have h2 := h1.trans hγ
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg hεpos.le,
      ENNReal.ofReal_le_ofReal_iff (add_nonneg dist_nonneg hεpos.le)] at h2
    have h3 : dist (D.pt z) (γ t) = D.1 (z, D.unpt (γ t)) := rfl
    have h4 : dist (D.pt z) (D.pt w) = D.1 (z, w) := rfl
    rw [h3, h4] at h2
    linarith
  refine ⟨range fun t => D.unpt (γ t), ?_, ⟨0, by simp⟩, ⟨1, by simp⟩,
    isPreconnected_range (D.continuous_unpt.comp γ.continuous)⟩
  rintro _ ⟨t, rfl⟩
  exact hpt t

/-! ## J0: the filled ball -/

section Filled

variable {D z s}

/-- A point of `X := cl 𝓑_s` outside `X` whose component of `ℂ ∖ X` is bounded has an open
neighbourhood (that component) inside `𝓑^•_s`. -/
theorem jb_cc_subset (x : ℂ) (hx : x ∉ closure (ballM D z s))
    (hb : Bornology.IsBounded (connectedComponentIn (closure (ballM D z s))ᶜ x)) :
    connectedComponentIn (closure (ballM D z s))ᶜ x ⊆ filledBall D z s := by
  intro y hy
  refine Or.inr ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  rwa [← connectedComponentIn_eq hy]

theorem jb_isOpen_cc (x : ℂ) : IsOpen (connectedComponentIn (closure (ballM D z s))ᶜ x) :=
  isClosed_closure.isOpen_compl.connectedComponentIn

/-- **J0**: `ℂ ∖ 𝓑^•_s` is the (unbounded) component of `ℂ ∖ cl 𝓑_s` containing any point `p`
far out. -/
theorem jb_not_isBounded_lt_norm (R : ℝ) : ¬ Bornology.IsBounded {w : ℂ | R < ‖w‖} := by
  intro hb
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  have hmem : ((max R r + 1 : ℝ) : ℂ) ∈ {w : ℂ | R < ‖w‖} := by
    show R < ‖((max R r + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le (by linarith [le_max_left R r]) (le_abs_self _)
  have h := hr hmem
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [le_max_right R r, le_abs_self (max R r + 1)]

/-- **J0**: `ℂ ∖ 𝓑^•_s` is the (unbounded) component of `ℂ ∖ cl 𝓑_s` containing any point `p`
far out. -/
theorem jb_compl_filledBall_eq {R : ℝ} (hR : closure (ballM D z s) ⊆ ball 0 R) {p : ℂ}
    (hp : R < ‖p‖) : (filledBall D z s)ᶜ = connectedComponentIn (closure (ballM D z s))ᶜ p := by
  have hfar := QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
    (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R) (jb_not_isBounded_lt_norm R)
    (Set.disjoint_left.2 fun _ ha hb => QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR ha hb)
    hp
  ext x
  simp only [filledBall, mem_compl_iff, mem_union, mem_setOf_eq, not_or, not_and]
  constructor
  · rintro ⟨hxX, hxb⟩
    have hsub := QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
      isPreconnected_connectedComponentIn (hxb hxX)
      (Set.disjoint_left.2 fun _ ha hb => connectedComponentIn_subset _ _ ha hb) hp
    exact hsub (mem_connectedComponentIn hxX)
  · intro hx
    have hxX : x ∉ closure (ballM D z s) := connectedComponentIn_subset _ _ hx
    refine ⟨hxX, fun _ hb => ?_⟩
    rw [← connectedComponentIn_eq hx] at hb
    exact jb_not_isBounded_lt_norm R (hb.subset hfar)


theorem jb_exists_far (hbd : Bornology.IsBounded (ballM D z s)) :
    ∃ R : ℝ, ∃ p : ℂ, closure (ballM D z s) ⊆ ball 0 R ∧ R < ‖p‖ := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hbd.closure
  refine ⟨R, ((|R| + 1 : ℝ) : ℂ), hR, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact lt_of_lt_of_le (by linarith [le_abs_self R]) (le_abs_self _)

theorem jb_far_subset_compl {R : ℝ} (hR : closure (ballM D z s) ⊆ ball 0 R) :
    {w : ℂ | R < ‖w‖} ⊆ (filledBall D z s)ᶜ := fun w hw => by
  rw [jb_compl_filledBall_eq hR hw]
  exact mem_connectedComponentIn fun h => lt_asymm (mem_ball_zero_iff.1 (hR h)) hw

theorem jb_isClosed_filledBall (hbd : Bornology.IsBounded (ballM D z s)) :
    IsClosed (filledBall D z s) := by
  obtain ⟨R, p, hR, hp⟩ := jb_exists_far hbd
  rw [← isOpen_compl_iff, jb_compl_filledBall_eq hR hp]
  exact jb_isOpen_cc p

theorem jb_filledBall_subset_closedBall {R : ℝ} (hR : closure (ballM D z s) ⊆ ball 0 R) :
    filledBall D z s ⊆ closedBall 0 R := fun x hx => by
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact jb_far_subset_compl hR (not_le.1 h) hx

/-- **J0**: `𝓑^•_s` is compact. -/
theorem jb_isCompact_filledBall (hbd : Bornology.IsBounded (ballM D z s)) :
    IsCompact (filledBall D z s) := by
  obtain ⟨R, p, hR, hp⟩ := jb_exists_far hbd
  exact Metric.isCompact_of_isClosed_isBounded (jb_isClosed_filledBall hbd)
    (isBounded_closedBall.subset (jb_filledBall_subset_closedBall hR))

/-- **J0**: `U = ℂ ∖ 𝓑^•_s` is preconnected. -/
theorem jb_isPreconnected_compl (hbd : Bornology.IsBounded (ballM D z s)) :
    IsPreconnected (filledBall D z s)ᶜ := by
  obtain ⟨R, p, hR, hp⟩ := jb_exists_far hbd
  rw [jb_compl_filledBall_eq hR hp]
  exact isPreconnected_connectedComponentIn

theorem jb_ballM_subset_interior : ballM D z s ⊆ interior (filledBall D z s) :=
  interior_maximal (subset_closure.trans subset_union_left) (jb_isOpen_ballM D z s)

theorem jb_disjoint_ballM_frontier : Disjoint (ballM D z s) (frontier (filledBall D z s)) :=
  disjoint_left.2 fun _ hx hf => hf.2 (jb_ballM_subset_interior hx)

/-- **J0**: `Γ = ∂𝓑^•_s ⊆ cl 𝓑_s`. -/
theorem jb_frontier_subset_closure (hbd : Bornology.IsBounded (ballM D z s)) :
    frontier (filledBall D z s) ⊆ closure (ballM D z s) := by
  intro x hx
  by_contra hxX
  have hxK : x ∈ filledBall D z s := (jb_isClosed_filledBall hbd).frontier_subset hx
  have hb : Bornology.IsBounded (connectedComponentIn (closure (ballM D z s))ᶜ x) := by
    rcases hxK with h | ⟨_, h⟩
    · exact absurd h hxX
    · exact h
  exact hx.2 (mem_interior.2 ⟨_, jb_cc_subset x hxX hb, jb_isOpen_cc x,
    mem_connectedComponentIn hxX⟩)

/-- A preconnected set meeting a closed set `K` and its complement meets `∂K`. -/
theorem jb_inter_frontier_nonempty {K C : Set ℂ} (hK : IsClosed K) (hC : IsPreconnected C)
    {a b : ℂ} (ha : a ∈ C) (haK : a ∉ K) (hb : b ∈ C) (hbK : b ∈ K) :
    (C ∩ frontier K).Nonempty := by
  by_contra hne
  have hsub : C ⊆ interior K ∪ Kᶜ := fun x hx => by
    by_cases hxK : x ∈ K
    · left
      by_contra hi
      exact hne ⟨x, hx, subset_closure hxK, hi⟩
    · exact Or.inr hxK
  rcases hC.subset_or_subset isOpen_interior hK.isOpen_compl
      ((disjoint_compl_right (a := K)).mono_left interior_subset) hsub with h | h
  · exact haK (interior_subset (h ha))
  · exact h hb hbK

/-- **J1a** (MS Prop 2.1 proof, tex l. 566–570): with `F ⊆ Γ` closed and `p ∈ Γ ∖ F`, a point
`a ∈ U` and `z` are joined in `ℂ ∖ F` by `U ∪ B_r(p) ∪ 𝓑_s` (every point of `Γ` is a limit of
points of `U` and of `𝓑_s`). -/
theorem jb_mem_cc_of_off (hs : 0 < s) (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D z s))
    {F : Set ℂ} (hFc : IsClosed F) (hF : F ⊆ frontier (filledBall D z s)) {p : ℂ}
    (hp : p ∈ frontier (filledBall D z s)) (hpF : p ∉ F) {a : ℂ} (ha : a ∉ filledBall D z s) :
    z ∈ connectedComponentIn Fᶜ a := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl p hpF
  have hpU : p ∈ closure (filledBall D z s)ᶜ := by
    rw [← frontier_compl] at hp
    exact frontier_subset_closure hp
  have hpB : p ∈ closure (ballM D z s) := jb_frontier_subset_closure hbd hp
  obtain ⟨a', ha'U, ha'p⟩ := Metric.mem_closure_iff.1 hpU r hr
  obtain ⟨b', hb'B, hb'p⟩ := Metric.mem_closure_iff.1 hpB r hr
  have hW : IsPreconnected ((filledBall D z s)ᶜ ∪ ball p r ∪ ballM D z s) :=
    (IsPreconnected.union a' ha'U (mem_ball.2 (by rwa [dist_comm])) (jb_isPreconnected_compl hbd)
      isPreconnected_ball).union b' (Or.inr (mem_ball.2 (by rwa [dist_comm]))) hb'B
      (jb_isPreconnected_ballM D z s hL)
  have hWF : (filledBall D z s)ᶜ ∪ ball p r ∪ ballM D z s ⊆ Fᶜ := by
    rintro x ((hx | hx) | hx) hxF
    · exact hx ((jb_isClosed_filledBall hbd).frontier_subset (hF hxF))
    · exact hball hx hxF
    · exact disjoint_left.1 jb_disjoint_ballM_frontier hx (hF hxF)
  exact hW.subset_connectedComponentIn (Or.inl (Or.inl ha)) hWF (Or.inr (jb_mem_ballM D z s hs))

/-- **J1c** (own argument, DV-B13; Janiszewski's theorem): `∂𝓑^•_s ∖ {q}` is preconnected for
every `q ∈ ℂ` (so `∂𝓑^•_s` is connected and has no cut points). -/
theorem jb_isPreconnected_frontier_diff (hs : 0 < s) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D z s)) (q : ℂ) :
    IsPreconnected (frontier (filledBall D z s) \ {q}) := by
  set Γ := frontier (filledBall D z s) with hΓ
  have hKc := jb_isClosed_filledBall hbd
  have hΓK : Γ ⊆ filledBall D z s := hKc.frontier_subset
  have hΓcpt : IsCompact Γ :=
    (jb_isCompact_filledBall hbd).of_isClosed_subset isClosed_frontier hΓK
  intro u v hu hv hcov ⟨p, hpS, hpu⟩ ⟨p', hp'S, hp'v⟩
  by_contra hne
  have huv : ∀ x ∈ Γ \ {q}, x ∈ u → x ∈ v → False := fun x hx hxu hxv => hne ⟨x, hx, hxu, hxv⟩
  set T := Γ ∩ {q} with hT
  set A := (Γ ∩ vᶜ) ∪ T with hAdef
  set B := (Γ ∩ uᶜ) ∪ T with hBdef
  have hTc : IsClosed T := isClosed_frontier.inter isClosed_singleton
  have hAΓ : A ⊆ Γ := union_subset inter_subset_left inter_subset_left
  have hBΓ : B ⊆ Γ := union_subset inter_subset_left inter_subset_left
  have hA : IsCompact A := hΓcpt.of_isClosed_subset
    ((isClosed_frontier.inter hv.isClosed_compl).union hTc) hAΓ
  have hB : IsCompact B := hΓcpt.of_isClosed_subset
    ((isClosed_frontier.inter hu.isClosed_compl).union hTc) hBΓ
  have hAB : IsPreconnected (A ∩ B) := by
    refine Set.Subsingleton.isPreconnected
      (Set.Subsingleton.anti (Set.subsingleton_singleton (a := q)) (s := A ∩ B) ?_)
    rintro x ⟨hxA, hxB⟩
    by_contra hxq
    have hxT : x ∉ T := fun h => hxq h.2
    have hxA' : x ∈ Γ ∩ vᶜ := hxA.resolve_right hxT
    have hxB' : x ∈ Γ ∩ uᶜ := hxB.resolve_right hxT
    rcases hcov ⟨hxA'.1, hxq⟩ with h | h
    · exact hxB'.2 h
    · exact hxA'.2 h
  have hΓAB : Γ ⊆ A ∪ B := by
    intro x hx
    by_cases hxq : x = q
    · exact Or.inl (Or.inr ⟨hx, hxq⟩)
    · by_cases hxv : x ∈ v
      · exact Or.inr (Or.inl ⟨hx, fun hxu => huv x ⟨hx, hxq⟩ hxu hxv⟩)
      · exact Or.inl (Or.inl ⟨hx, hxv⟩)
  obtain ⟨R, p0, hR, hp0⟩ := jb_exists_far hbd
  have ha : p0 ∉ filledBall D z s := jb_far_subset_compl hR hp0
  have hzK : z ∈ filledBall D z s := Or.inl (subset_closure (jb_mem_ballM D z s hs))
  have hzΓ : z ∉ Γ := disjoint_left.1 jb_disjoint_ballM_frontier (jb_mem_ballM D z s hs)
  have hnA : p0 ∉ A ∪ B := fun h => ha (hΓK ((union_subset hAΓ hBΓ) h))
  have hnB : z ∉ A ∪ B := fun h => hzΓ ((union_subset hAΓ hBΓ) h)
  have hsep : z ∉ connectedComponentIn (A ∪ B)ᶜ p0 := by
    intro hz
    obtain ⟨y, hyC, hyΓ⟩ := jb_inter_frontier_nonempty hKc isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hnA) ha hz hzK
    exact connectedComponentIn_subset _ _ hyC (hΓAB hyΓ)
  by_cases h1 : z ∈ connectedComponentIn Aᶜ p0
  · by_cases h2 : z ∈ connectedComponentIn Bᶜ p0
    · exact hsep (QuantumZipper.CA.Topo.janiszewski hA hB hAB hnA hnB h1 h2)
    · refine h2 (jb_mem_cc_of_off hs hL hbd hB.isClosed hBΓ hpS.1 ?_ ha)
      rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact h hpu
      · exact hpS.2 h
  · refine h1 (jb_mem_cc_of_off hs hL hbd hA.isClosed hAΓ hp'S.1 ?_ ha)
    rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h hp'v
    · exact hp'S.2 h

end Filled

end LQGMetric.GM
