/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.ArcNonSep at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Crossing

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: an arc does not separate the plane; components have the curve as frontier

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 386–691.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- `unitInterval` is a Tietze extension space, as a retract of `ℝ` (via `Set.projIcc`).
Added in the port: the original relied on an instance available in its mathlib pin (`import
Mathlib`) that our pin does not provide. -/
instance instTietzeExtensionUnitInterval : TietzeExtension unitInterval :=
  TietzeExtension.of_retract ⟨Subtype.val, continuous_subtype_val⟩
    ⟨Set.projIcc 0 1 zero_le_one, continuous_projIcc⟩ (by
      ext x; simp [Set.projIcc_of_mem _ x.2])

/-- **Maehara's Lemma 1 core: "an arc does not separate the plane".** If `A ⊆ ℝ²`
is an arc (homeomorphic to the unit interval `[0,1]`) then its complement `Aᶜ` is
connected.

Proof (Brouwer + Tietze). If `Aᶜ` were disconnected it would have a bounded
component (there is a unique unbounded one, containing the cobounded exterior of a
disc through `A`); pick a point `o` in it. Since `A ≃ₜ [0,1]` and `[0,1]` is an
absolute retract (`TietzeExtension`), the identity `A → A` extends to a retraction
`ρ : ℝ² → A`. Glue `ρ` on the component `K ∋ o` with the identity elsewhere: the two
pieces agree on `frontier K ⊆ A` where `ρ = id`, giving a continuous
`Q : ℝ² → ℝ²∖{o}` that is the identity outside `K`. On a large disc `D = closedBall o R`
containing `A` and `K`, the map `z ↦ o - R·(Q z - o)/‖Q z - o‖` (antipodal radial
projection about `o`) is a fixed-point-free continuous self-map of `D`, contradicting
Brouwer. -/
theorem arc_not_separates (hbr : BrouwerFPT) {A : Set Plane}
    (φ : A ≃ₜ unitInterval) : IsConnected Aᶜ := by
  classical
  -- `A` is compact, hence closed, bounded, and `Aᶜ` is open.
  have : CompactSpace ↥unitInterval := inferInstance
  have hcsA : CompactSpace ↥A := φ.symm.compactSpace
  have hAcpt : IsCompact A := isCompact_iff_compactSpace.mpr hcsA
  have hAcl : IsClosed A := hAcpt.isClosed
  have hAbd : IsBounded A := hAcpt.isBounded
  have hAopen : IsOpen Aᶜ := hAcl.isOpen_compl
  -- Tietze retraction `ρ : ℝ² → ℝ²`, `range ρ ⊆ A`, `ρ = id` on `A`.
  have : TietzeExtension ↥A := TietzeExtension.of_homeo φ
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hAcl (ContinuousMap.id ↥A)
  set ρ : Plane → Plane := fun x => (g x : Plane) with hρdef
  have hρcont : Continuous ρ := continuous_subtype_val.comp g.continuous
  have hρmem : ∀ x, ρ x ∈ A := fun x => (g x).2
  have hρid : ∀ a ∈ A, ρ a = a := by
    intro a ha
    have h1 := DFunLike.congr_fun hg ⟨a, ha⟩
    simp only [ContinuousMap.restrict_apply, ContinuousMap.id_apply] at h1
    show (g a : Plane) = a
    exact congrArg Subtype.val h1
  -- A radius `R0 ≥ 0` with `A ⊆ closedBall 0 R0`; the cobounded exterior `E`.
  obtain ⟨R0, hR0, hAsub⟩ : ∃ R0 : ℝ, 0 ≤ R0 ∧ A ⊆ closedBall (0 : Plane) R0 := by
    obtain ⟨R, hR⟩ := hAbd.subset_closedBall (0 : Plane)
    exact ⟨max R 0, le_max_right R 0,
      hR.trans (closedBall_subset_closedBall (le_max_left R 0))⟩
  set E : Set Plane := {z : Plane | R0 < ‖z‖} with hEdef
  have hEconn : IsConnected E := isConnected_compl_closedBall hR0
  have hEsub : E ⊆ Aᶜ := by
    intro z hz hzA
    have := hAsub hzA
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  obtain ⟨p, hpE⟩ := hEconn.nonempty
  have hpAc : p ∈ Aᶜ := hEsub hpE
  have hEcomp : E ⊆ connectedComponentIn Aᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpE hEsub
  -- An unbounded component meets `E`.
  have meetsE : ∀ z, z ∈ Aᶜ → ¬ IsBounded (connectedComponentIn Aᶜ z) →
      ∃ w ∈ E, w ∈ connectedComponentIn Aᶜ z := by
    intro z _ hzu
    by_contra hcon
    push Not at hcon
    apply hzu
    have hsubBall : connectedComponentIn Aᶜ z ⊆ closedBall (0 : Plane) R0 := by
      intro w hw
      rw [mem_closedBall_zero_iff]
      by_contra hwn
      exact hcon w (not_le.1 hwn) hw
    exact isBounded_closedBall.subset hsubBall
  refine ⟨⟨p, hpAc⟩, ?_⟩
  -- `IsPreconnected Aᶜ`: either every component is unbounded (⇒ connected), or a
  -- bounded one exists (⇒ Brouwer contradiction).
  by_cases hbdd : ∃ o ∈ Aᶜ, IsBounded (connectedComponentIn Aᶜ o)
  · -- Bounded component: derive a contradiction via Brouwer.
    exfalso
    obtain ⟨o, hoAc, hKbd⟩ := hbdd
    set K : Set Plane := connectedComponentIn Aᶜ o with hKdef
    have hoK : o ∈ K := mem_connectedComponentIn hoAc
    have hKopen : IsOpen K := hAopen.connectedComponentIn
    have hoA : o ∉ A := hoAc
    -- `frontier K ⊆ A`.
    have hfrontier : frontier K ⊆ A := by
      intro x hx
      by_contra hxA
      have hxAc : x ∈ Aᶜ := hxA
      have hxcl : x ∈ closure K := frontier_subset_closure hx
      have hxnK : x ∉ K := by
        intro hxK
        have : x ∈ K ∩ frontier K := ⟨hxK, hx⟩
        rw [hKopen.inter_frontier_eq] at this
        exact absurd this (Set.notMem_empty x)
      have hCxopen : IsOpen (connectedComponentIn Aᶜ x) := hAopen.connectedComponentIn
      have hxCx : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hxAc
      rw [_root_.mem_closure_iff] at hxcl
      obtain ⟨w, hwCx, hwK⟩ := hxcl _ hCxopen hxCx
      have e1 : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwCx
      rw [hKdef] at hwK
      have e2 : connectedComponentIn Aᶜ o = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwK
      rw [e1, ← e2] at hxCx
      rw [← hKdef] at hxCx
      exact hxnK hxCx
    -- A radius `R > 0` with `A ⊆ ball o R` and `K ⊆ ball o R`.
    obtain ⟨R, hRpos, hAR, hKR⟩ :
        ∃ R : ℝ, 0 < R ∧ A ⊆ ball o R ∧ K ⊆ ball o R := by
      obtain ⟨rA, hrA⟩ := hAbd.subset_closedBall o
      obtain ⟨rK, hrK⟩ := hKbd.subset_closedBall o
      refine ⟨max (max rA rK) 0 + 1, by positivity, ?_, ?_⟩
      · exact hrA.trans (closedBall_subset_ball
          (lt_of_le_of_lt ((le_max_left rA rK).trans (le_max_left _ 0)) (lt_add_one _)))
      · exact hrK.trans (closedBall_subset_ball
          (lt_of_le_of_lt ((le_max_right rA rK).trans (le_max_left _ 0)) (lt_add_one _)))
    -- The glued map `Q` and its properties.
    set Q : Plane → Plane := K.piecewise ρ id with hQdef
    have hQcont : Continuous Q := by
      refine Continuous.piecewise ?_ hρcont continuous_id
      intro a ha
      show ρ a = id a
      simpa using hρid a (hfrontier ha)
    have hQA : ∀ z ∈ K, Q z = ρ z := fun z hz => by
      rw [hQdef]; exact Set.piecewise_eq_of_mem _ _ _ hz
    have hQid : ∀ z, z ∉ K → Q z = z := fun z hz => by
      rw [hQdef]; exact Set.piecewise_eq_of_notMem _ _ _ hz
    have hQne : ∀ z, Q z ≠ o := by
      intro z
      by_cases hz : z ∈ K
      · rw [hQA z hz]; intro h; exact hoA (h ▸ hρmem z)
      · rw [hQid z hz]; intro h; apply hz; rw [h]; exact hoK
    -- The antipodal radial projection about `o`.
    set Φ : Plane → Plane := fun z => o - R • (‖Q z - o‖⁻¹ • (Q z - o)) with hΦdef
    have hΦcont : Continuous Φ := by
      have h1 : Continuous (fun z => Q z - o) := hQcont.sub continuous_const
      have h2 : Continuous (fun z => (‖Q z - o‖)⁻¹) :=
        h1.norm.inv₀ (fun z => by
          simp only [ne_eq, norm_eq_zero, sub_eq_zero]; exact hQne z)
      -- Each step is ascribed explicitly, and the scalar is passed to `const_smul`
      -- rather than inferred: since Mathlib `905b9581`, `continuous_const.smul _`
      -- leaves the scalar an undetermined metavariable, because unifying the `Pi`-level
      -- `f • g` of `Continuous.smul` against `fun z ↦ R • …` no longer solves for it.
      have h3 : Continuous (fun z => (‖Q z - o‖)⁻¹ • (Q z - o)) := h2.smul h1
      have h4 : Continuous (fun z => R • ((‖Q z - o‖)⁻¹ • (Q z - o))) := h3.const_smul R
      exact continuous_const.sub h4
    have hΦsphere : ∀ z, ‖Φ z - o‖ = R := by
      intro z
      have hne : Q z - o ≠ 0 := sub_ne_zero.mpr (hQne z)
      have hw1 : ‖‖Q z - o‖⁻¹ • (Q z - o)‖ = 1 := norm_smul_inv_norm hne
      have he : Φ z - o = -(R • (‖Q z - o‖⁻¹ • (Q z - o))) := by
        simp only [hΦdef]; abel
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hRpos.le, hw1,
        mul_one]
    -- `Φ` maps `D = closedBall o R` into `D`.
    set D : Set Plane := closedBall o R with hDdef
    have hΦD : ∀ z ∈ D, Φ z ∈ D := by
      intro z _
      rw [hDdef, mem_closedBall]
      exact le_of_eq (by rw [dist_eq_norm]; exact hΦsphere z)
    have hDconv : Convex ℝ D := convex_closedBall o R
    have hDcomp : IsCompact D := isCompact_closedBall o R
    have hDne : D.Nonempty := ⟨o, by rw [hDdef]; exact mem_closedBall_self hRpos.le⟩
    -- Package as a self-map of `D` and apply Brouwer.
    let F : C(↥D, ↥D) :=
      ⟨fun z => ⟨Φ z.1, hΦD z.1 z.2⟩,
        Continuous.subtype_mk (hΦcont.comp continuous_subtype_val) _⟩
    obtain ⟨x, hx⟩ := hbr D hDconv hDcomp hDne F
    set x0 : Plane := (x : Plane) with hx0
    have hfix : Φ x0 = x0 := congrArg Subtype.val hx
    have hx0R : ‖x0 - o‖ = R := by rw [← hfix]; exact hΦsphere x0
    have hx0nK : x0 ∉ K := by
      intro hk
      have hin := hKR hk
      rw [mem_ball, dist_eq_norm, hx0R] at hin
      exact lt_irrefl R hin
    have hQx0 : Q x0 = x0 := hQid x0 hx0nK
    have hcompute : Φ x0 = o - (x0 - o) := by
      simp only [hΦdef]
      rw [hQx0, hx0R, smul_smul, mul_inv_cancel₀ hRpos.ne', one_smul]
    rw [hcompute] at hfix
    have hz : x0 - o = 0 := by
      have e : (2 : ℝ) • (x0 - o) = x0 - (o - (x0 - o)) := by rw [two_smul]; abel
      have h20 : (2 : ℝ) • (x0 - o) = 0 := by rw [e, hfix]; abel
      exact (smul_eq_zero.mp h20).resolve_left (by norm_num)
    rw [hz, norm_zero] at hx0R
    exact absurd hx0R.symm hRpos.ne'
  · -- No bounded component: every point's component equals that of `p`.
    push Not at hbdd
    have hAeq : Aᶜ ⊆ connectedComponentIn Aᶜ p := by
      intro x hx
      obtain ⟨w, hwE, hwx⟩ := meetsE x hx (hbdd x hx)
      have e1 : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwx
      have e2 : connectedComponentIn Aᶜ p = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq (hEcomp hwE)
      have hxc : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hx
      rw [e1, ← e2] at hxc
      exact hxc
    have hsup : connectedComponentIn Aᶜ p ⊆ Aᶜ := connectedComponentIn_subset Aᶜ p
    rw [Set.Subset.antisymm hAeq hsup]
    exact (isConnected_connectedComponentIn_iff.mpr hpAc).isPreconnected

/-- **Maehara's Lemma 1.** If `ℝ²∖J` is disconnected, each component has the whole
Jordan curve `J = range r` as its boundary. We state (and prove) the sharper
unconditional form: for any `x` in the complement, the frontier of its connected
component equals `range r`.

Proof (arc argument, via `arc_not_separates`). Write `U` for the component of `x`.
Always `frontier U ⊆ range r` (a boundary point outside the curve would lie in some
component of the open complement, forcing it into `U` — impossible for a frontier
point). If `frontier U ⊊ range r`, transport the proper closed set
`C = r⁻¹(frontier U) ⊊ S¹` to a proper closed arc `A₀` (via `exists_proper_arc`) and
push forward to `A = r '' A₀`, a proper arc with `frontier U ⊆ A ⊊ range r`. Then
`Aᶜ` is connected (`arc_not_separates`), yet `U` and `(closure U)ᶜ` split it into two
nonempty relatively open pieces (`x ∈ U`; a point of `range r ∖ A` lies in
`(closure U)ᶜ`) — contradicting connectedness. -/
theorem component_boundary_eq (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    {x : Plane} (hx : x ∈ (range r)ᶜ)
    (_hy : ∃ y ∈ (range r)ᶜ,
      connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ x) :
    frontier (connectedComponentIn (range r)ᶜ x) = range r := by
  classical
  set U := connectedComponentIn (range r)ᶜ x with hUdef
  have hUopen : IsOpen U := isOpen_component r hcont x
  have hxU : x ∈ U := mem_connectedComponentIn hx
  -- **Step 1: `frontier U ⊆ range r`.**
  have hsub : frontier U ⊆ range r := by
    intro w hw
    by_contra hwr
    have hwc : w ∈ (range r)ᶜ := hwr
    have hwcl : w ∈ closure U := frontier_subset_closure hw
    have hWopen : IsOpen (connectedComponentIn (range r)ᶜ w) :=
      isOpen_component r hcont w
    have hwW : w ∈ connectedComponentIn (range r)ᶜ w := mem_connectedComponentIn hwc
    rw [_root_.mem_closure_iff] at hwcl
    obtain ⟨v, hvW, hvU⟩ := hwcl _ hWopen hwW
    have e1 : connectedComponentIn (range r)ᶜ w = connectedComponentIn (range r)ᶜ v :=
      connectedComponentIn_eq hvW
    have e2 : U = connectedComponentIn (range r)ᶜ v := connectedComponentIn_eq hvU
    have hwU : w ∈ U := by rw [e2, ← e1]; exact hwW
    have : w ∈ U ∩ frontier U := ⟨hwU, hw⟩
    rw [hUopen.inter_frontier_eq] at this
    exact absurd this (Set.notMem_empty w)
  -- **Step 2: `frontier U = range r`.**
  by_contra hne
  have hssub : frontier U ⊂ range r := hsub.ssubset_of_ne hne
  -- Pull `frontier U` back to a proper closed subset `C ⊊ S¹`.
  set C : Set (sphere (0 : Plane) 1) := r ⁻¹' frontier U with hCdef
  have hCclosed : IsClosed C := isClosed_frontier.preimage hcont
  have hCne : C ≠ univ := by
    intro h
    apply hne
    refine Set.Subset.antisymm hsub ?_
    intro w hw
    obtain ⟨s, rfl⟩ := hw
    have hsC : s ∈ C := h.symm ▸ mem_univ s
    exact hsC
  obtain ⟨A₀, hCA0, hA0ne, hA0closed, ⟨e0⟩⟩ :=
    Arcs.exists_proper_arc hCclosed hCne
  set A : Set Plane := r '' A₀ with hAdef
  -- Compactness of the sphere subtype ⇒ of `A₀`, giving `A ≃ₜ unitInterval`.
  have hcsSphere : CompactSpace (sphere (0 : Plane) 1) :=
    Arcs.circleHomeoSphere.compactSpace
  have hcsA0 : CompactSpace ↥A₀ := isCompact_iff_compactSpace.mp hA0closed.isCompact
  have eImg : (↥A₀) ≃ₜ (↥A) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.image r A₀ hinj)
      (continuous_induced_rng.2 (hcont.comp continuous_subtype_val))
  have eA : A ≃ₜ unitInterval := eImg.symm.trans e0
  -- `A ⊆ range r`, `frontier U ⊆ A`, and a point of `range r ∖ A`.
  have hAr : A ⊆ range r := by
    rw [hAdef]; rintro _ ⟨s, _, rfl⟩; exact ⟨s, rfl⟩
  have hfrA : frontier U ⊆ A := by
    rw [hAdef]
    intro w hw
    obtain ⟨s, rfl⟩ := hsub hw
    exact ⟨s, hCA0 hw, rfl⟩
  obtain ⟨s₀, hs₀⟩ := (Set.ne_univ_iff_exists_notMem A₀).1 hA0ne
  have hq'r : r s₀ ∈ range r := ⟨s₀, rfl⟩
  have hq'A : r s₀ ∉ A := by
    rw [hAdef]
    rintro ⟨s, hsA, hss⟩
    exact hs₀ (hinj hss ▸ hsA)
  -- `Aᶜ` is connected (an arc does not separate the plane).
  have hAconn : IsConnected Aᶜ := arc_not_separates hbr eA
  -- The clopen (preconnectedness) contradiction.
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset (range r)ᶜ x
  have hUAc : U ⊆ Aᶜ := hUsub.trans (compl_subset_compl.mpr hAr)
  have hxAc : x ∈ Aᶜ := hUAc hxU
  have hVopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have hcover : Aᶜ ⊆ U ∪ (closure U)ᶜ := by
    intro w hwAc
    by_cases hwcl : w ∈ closure U
    · left
      by_contra hwU
      have hfr : w ∈ frontier U := by
        refine ⟨hwcl, ?_⟩
        rw [hUopen.interior_eq]; exact hwU
      exact hwAc (hfrA hfr)
    · right; exact hwcl
  have hqV : r s₀ ∈ (closure U)ᶜ := by
    intro hcl
    have hnU : r s₀ ∉ U := fun h => (hUsub h) hq'r
    have hfr : r s₀ ∈ frontier U := by
      refine ⟨hcl, ?_⟩
      rw [hUopen.interior_eq]; exact hnU
    exact hq'A (hfrA hfr)
  obtain ⟨w, _, hwU, hwV⟩ :=
    hAconn.isPreconnected U (closure U)ᶜ hUopen hVopen hcover
      ⟨x, hxAc, hxU⟩ ⟨r s₀, hq'A, hqV⟩
  exact hwV (subset_closure hwU)

end MatedCRTHarmonic.Planar.Jordan
