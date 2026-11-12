/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.Paths at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Normalize

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: path concatenation and interior points

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 1044–1437.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-! ### Path-concatenation infrastructure and Maehara's interior points

The tools below package repeated use of the `crossing` lemma: any bottom-to-top
path in the normalized rectangle meets each arc (`vertical_meets_arc`), together with
the plumbing (`concatPath2`, `concatPath3`) that glues path pieces into one
continuous path on `[-1,1]` whose image is the union of the pieces. -/

/-- An arc `J ⊆ Plane` homeomorphic to `unitInterval` is path-connected. -/
theorem arc_isPathConnected {J : Set Plane} (e : ↥J ≃ₜ unitInterval) :
    IsPathConnected J := by
  have : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0:ℝ) 1).isPathConnected (Set.nonempty_Icc.mpr (by norm_num)))
  have h1 : IsPathConnected (univ : Set unitInterval) := isPathConnected_univ
  have h2 := h1.image
    (show Continuous (fun x : unitInterval => ((e.symm x : ↥J) : Plane)) from
      continuous_subtype_val.comp e.symm.continuous)
  rw [Set.image_univ] at h2
  have hrange : (Set.range fun x : unitInterval => ((e.symm x : ↥J) : Plane)) = J := by
    ext p
    simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩; exact (e.symm x).2
    · intro hp; exact ⟨e ⟨p, hp⟩, by simp⟩
  rwa [hrange] at h2

/-- An arc `J ≃ₜ unitInterval` joins any two of its points inside `J`. -/
theorem arc_joinedIn {J : Set Plane} (e : ↥J ≃ₜ unitInterval)
    {a b : Plane} (ha : a ∈ J) (hb : b ∈ J) : JoinedIn J a b :=
  (arc_isPathConnected e).joinedIn a ha b hb

/-- **Key reusable tool.** Any path `v` running from the bottom edge (`v (-1) 1 = -2`)
to the top edge (`v 1 1 = 2`) of the normalized rectangle `[-1,1]×[-2,2]` must meet an
arc `J` that joins the left point `a = !₂[-1,0]` to the right point `b = !₂[1,0]` inside
the rectangle. Immediate from `crossing`, using `arc_path` for the horizontal path. -/
theorem vertical_meets_arc (hbr : BrouwerFPT) {J : Set Plane}
    (hJsub : J ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2})
    (hJoin : JoinedIn J (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]))
    {v : ℝ → Plane} (hvcont : ContinuousOn v (Icc (-1:ℝ) 1))
    (hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2)
    (hv1 : v (-1) 1 = -2) (hv2 : v 1 1 = 2) :
    ∃ t ∈ Icc (-1:ℝ) 1, v t ∈ J := by
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := arc_path hJoin
  have hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc (-1:ℝ) 1 ∧ h t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hJsub (hhmem t ht)
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1)
    (by norm_num : (-2:ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1 hv2
  exact ⟨t, ht, heq ▸ hhmem s hs⟩

/-- A path piece `f : ℝ → Plane`, continuous on `[-1,1]`, as a `Path (f (-1)) (f 1)`
over `unitInterval` (reparametrized by `s ↦ 2s-1`). -/
noncomputable def pathOfPiece {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) : Path (f (-1)) (f 1) :=
  Path.mk ⟨fun s : unitInterval => f (2 * (s : ℝ) - 1), by
      refine hf.comp_continuous (by fun_prop) (fun s => ?_)
      have hs := s.2; rw [Set.mem_Icc] at hs ⊢
      constructor <;> [linarith [hs.1]; linarith [hs.2]]⟩
    (by norm_num [Set.Icc.coe_zero]) (by norm_num [Set.Icc.coe_one])

lemma pathOfPiece_range {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) :
    Set.range (pathOfPiece hf) = f '' Icc (-1:ℝ) 1 := by
  ext p
  simp only [Set.mem_range, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨s, rfl⟩
    have hs := s.2; rw [Set.mem_Icc] at hs
    exact ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨⟨(y + 1) / 2, by rw [Set.mem_Icc]; constructor <;> linarith⟩, ?_⟩
    show f (2 * ((y + 1) / 2) - 1) = f y
    congr 1; ring

/-- **Path concatenation (2 pieces).** Two path pieces on `[-1,1]` that chain up
(`f 1 = g (-1)`) glue to one path `c` on `[-1,1]` from `f (-1)` to `g 1`, whose image
is contained in the union of the pieces' images. -/
theorem concatPath2 {f g : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) (hg : ContinuousOn g (Icc (-1:ℝ) 1))
    (hchain : f 1 = g (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = g 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1, c t ∈ f '' Icc (-1:ℝ) 1 ∪ g '' Icc (-1:ℝ) 1 := by
  set P : Path (f (-1)) (g 1) :=
    (pathOfPiece hf).trans ((pathOfPiece hg).cast hchain rfl) with hP
  refine ⟨fun t => P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)), ?_, ?_, ?_, ?_⟩
  · exact (P.continuous.comp (continuous_projIcc.comp (by fun_prop))).continuousOn
  · show P _ = f (-1)
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((-1:ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.source
  · show P _ = g 1
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((1:ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.target
  · intro t _
    have hmem : P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)) ∈ Set.range P := ⟨_, rfl⟩
    rw [hP, Path.trans_range] at hmem
    have hr1 : Set.range (pathOfPiece hf) = f '' Icc (-1:ℝ) 1 := pathOfPiece_range hf
    have hr2 : Set.range ((pathOfPiece hg).cast hchain rfl) = g '' Icc (-1:ℝ) 1 := by
      simp only [Path.cast_coe]; exact pathOfPiece_range hg
    rw [hr1, hr2] at hmem
    exact hmem

/-- **Path concatenation (3 pieces).** Three chained path pieces on `[-1,1]` glue to
one path `c` on `[-1,1]` from `f (-1)` to `h 1`, with image in the union of the three
pieces' images. -/
theorem concatPath3 {f g h : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) (hg : ContinuousOn g (Icc (-1:ℝ) 1))
    (hh : ContinuousOn h (Icc (-1:ℝ) 1))
    (hfg : f 1 = g (-1)) (hgh : g 1 = h (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = h 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1,
        c t ∈ f '' Icc (-1:ℝ) 1 ∪ g '' Icc (-1:ℝ) 1 ∪ h '' Icc (-1:ℝ) 1 := by
  obtain ⟨c2, hc2cont, hc2a, hc2b, hc2mem⟩ := concatPath2 hf hg hfg
  obtain ⟨c3, hc3cont, hc3a, hc3b, hc3mem⟩ :=
    concatPath2 hc2cont hh (by rw [hc2b]; exact hgh)
  refine ⟨c3, hc3cont, by rw [hc3a, hc2a], hc3b, fun t ht => ?_⟩
  rcases hc3mem t ht with hin | hin
  · obtain ⟨u, hu, huc⟩ := hin
    exact Set.mem_union_left _ (huc ▸ hc2mem u hu)
  · exact Set.mem_union_right _ hin

/-- **Path concatenation (5 pieces).** Five chained path pieces on `[-1,1]` glue to one
path `c` on `[-1,1]` from `f1 (-1)` to `f5 1`, with image in the union of the five
pieces' images. -/
theorem concatPath5 {f1 f2 f3 f4 f5 : ℝ → Plane}
    (h1 : ContinuousOn f1 (Icc (-1:ℝ) 1)) (h2 : ContinuousOn f2 (Icc (-1:ℝ) 1))
    (h3 : ContinuousOn f3 (Icc (-1:ℝ) 1)) (h4 : ContinuousOn f4 (Icc (-1:ℝ) 1))
    (h5 : ContinuousOn f5 (Icc (-1:ℝ) 1))
    (c12 : f1 1 = f2 (-1)) (c23 : f2 1 = f3 (-1)) (c34 : f3 1 = f4 (-1))
    (c45 : f4 1 = f5 (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f1 (-1) ∧ c 1 = f5 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1,
        c t ∈ ((((f1 '' Icc (-1:ℝ) 1 ∪ f2 '' Icc (-1:ℝ) 1) ∪ f3 '' Icc (-1:ℝ) 1)
          ∪ f4 '' Icc (-1:ℝ) 1) ∪ f5 '' Icc (-1:ℝ) 1) := by
  obtain ⟨c123, hc123cont, hc123a, hc123b, hc123mem⟩ := concatPath3 h1 h2 h3 c12 c23
  obtain ⟨c45, hc45cont, hc45a, hc45b, hc45mem⟩ := concatPath2 h4 h5 c45
  obtain ⟨c, hccont, hca, hcb, hcmem⟩ :=
    concatPath2 hc123cont hc45cont (by rw [hc123b, hc45a]; exact c34)
  refine ⟨c, hccont, by rw [hca, hc123a], by rw [hcb, hc45b], fun t ht => ?_⟩
  rcases hcmem t ht with hin | hin
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc123mem u hu
    rw [hue] at hmem
    exact Or.inl (Or.inl hmem)
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc45mem u hu
    rw [hue] at hmem
    rcases hmem with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- **Interior point `m`.** The intersection `J_n ∩ axis` (`axis = {p | p 0 = 0}`) is
compact and nonempty (it contains `l`), hence attains its `y`-minimum at a point `m`. -/
theorem exists_ymin_Jn_axis {J_n : Set Plane} (hJncl : IsClosed J_n)
    (hcpt : IsCompact J_n) {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0) :
    ∃ m ∈ J_n, m 0 = 0 ∧ ∀ p ∈ J_n, p 0 = 0 → m 1 ≤ p 1 := by
  set Jm : Set Plane := {p ∈ J_n | p 0 = 0} with hJm
  have hsub : Jm ⊆ J_n := fun p hp => hp.1
  have hcl : IsClosed Jm :=
    hJncl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hJmcpt : IsCompact Jm := hcpt.of_isClosed_subset hcl hsub
  have hne : Jm.Nonempty := ⟨l, hlJn, hl0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨m, hmJm, hmmin⟩ :=
    hJmcpt.exists_isMinOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  exact ⟨m, hmJm.1, hmJm.2, fun p hpJn hp0 => hmmin (show p ∈ Jm from ⟨hpJn, hp0⟩)⟩

/-- **The vertical segment `m → s` meets `J_s`.** With `s = !₂[0,-2]` (below the
rectangle's bottom edge), the axis segment from the interior point `m ∈ J_n` down to
`s` must cross the southern arc `J_s`. Proof by contradiction: were it disjoint from
`J_s`, the concatenation `s → m` (axis), `m → l` (a path inside `J_n \ {a,b}`),
`l → n` (axis, `n = !₂[0,2]`) would give a bottom-to-top path in the rectangle
avoiding `J_s`, contradicting `vertical_meets_arc` (`J_s` joins `a` to `b`). The
crossing point lies on the segment, so it sits on the axis at height `≤ m 1`. -/
theorem ms_meets_Js (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (_hcont : Continuous r) (_hinj : Injective r)
    (hmr : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hpr : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane}
    (hUnion : J_n ∪ J_s = range r)
    (hInter : J_n ∩ J_s = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]})
    (eJs : ↥J_s ≃ₜ unitInterval)
    (hpcJn : IsPathConnected (J_n \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}))
    {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0)
    (hlmax : ∀ q ∈ range r, q 0 = 0 → q 1 ≤ l 1)
    {m : Plane} (hmJn : m ∈ J_n) (hm0 : m 0 = 0) :
    ∃ w ∈ J_s, w 0 = 0 ∧ w 1 ≤ m 1 := by
  set a : Plane := !₂[(-1:ℝ), 0] with ha_def
  set b : Plane := !₂[(1:ℝ), 0] with hb_def
  -- opaque bottom / top axis points (avoid unfolding `!₂` in later arithmetic)
  obtain ⟨s, hs0, hs1⟩ : ∃ s : Plane, s 0 = 0 ∧ s 1 = -2 :=
    ⟨!₂[(0:ℝ), -2], by simp, by simp⟩
  obtain ⟨nn, hn0, hn1⟩ : ∃ nn : Plane, nn 0 = 0 ∧ nn 1 = 2 :=
    ⟨!₂[(0:ℝ), 2], by simp, by simp⟩
  have ha0 : a 0 = -1 := by simp [ha_def]
  have hb0 : b 0 = 1 := by simp [hb_def]
  -- basic containments and the rectangle bound
  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hrect := normalized_subset_rectangle hmr hpr hfar
  have hmrange : m ∈ range r := hJnr hmJn
  have hlrange : l ∈ range r := hJnr hlJn
  have hm1lb : (-2 : ℝ) ≤ m 1 := (hrect hmrange).2.1
  have hm1ub : m 1 ≤ 2 := (hrect hmrange).2.2
  have hl1lb : (-2 : ℝ) ≤ l 1 := (hrect hlrange).2.1
  have hl1ub : l 1 ≤ 2 := (hrect hlrange).2.2
  -- `a, b ∈ J_s`; `J_s` joins them
  have haJs : a ∈ J_s := by
    have : a ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert _ _
    exact this.2
  have hbJs : b ∈ J_s := by
    have : b ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJs : JoinedIn J_s a b := arc_joinedIn eJs haJs hbJs
  have hJsrect : J_s ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} :=
    hJsr.trans hrect
  -- `m, l ∉ {a,b}` (they are on the axis `x = 0`, while `a 0 = -1`, `b 0 = 1`)
  have hmab : m ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hm0, ha0, hb0] at hc; norm_num at hc)
  have hlab : l ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hl0, ha0, hb0] at hc; norm_num at hc)
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ w ∈ J_s, w 0 = 0 → m 1 < w 1`
  -- three path pieces on `[-1,1]`
  set f1 : ℝ → Plane := fun t => s + ((t + 1) / 2) • (m - s) with hf1def
  set f3 : ℝ → Plane := fun t => l + ((t + 1) / 2) • (nn - l) with hf3def
  obtain ⟨f2, hf2cont, hf2m, hf2l, hf2mem⟩ :=
    arc_path (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
  have hf1cont : ContinuousOn f1 (Icc (-1:ℝ) 1) := (by fun_prop : Continuous f1).continuousOn
  have hf3cont : ContinuousOn f3 (Icc (-1:ℝ) 1) := (by fun_prop : Continuous f3).continuousOn
  have hf1_1 : f1 1 = m := by simp [hf1def]
  have hf1_m1 : f1 (-1) = s := by simp [hf1def]
  have hf3_1 : f3 1 = nn := by simp [hf3def]
  have hf3_m1 : f3 (-1) = l := by simp [hf3def]
  have hf1f2 : f1 1 = f2 (-1) := by rw [hf1_1, hf2m]
  have hf2f3 : f2 1 = f3 (-1) := by rw [hf2l, hf3_m1]
  obtain ⟨c, hccont, hcs, hcn, hcmem⟩ := concatPath3 hf1cont hf2cont hf3cont hf1f2 hf2f3
  -- endpoints of the concatenation are on the bottom / top edges
  have hcm1 : c (-1) 1 = -2 := by rw [hcs, hf1_m1]; exact hs1
  have hcn1 : c 1 1 = 2 := by rw [hcn, hf3_1]; exact hn1
  -- the three pieces stay in the rectangle
  have hf1x : ∀ t, f1 t 0 = 0 := fun t => by simp [hf1def, hs0, hm0]
  have hf3x : ∀ t, f3 t 0 = 0 := fun t => by simp [hf3def, hl0, hn0]
  have hf1y_le : ∀ t ∈ Icc (-1:ℝ) 1, f1 t 1 ≤ m 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf1y_ge : ∀ t ∈ Icc (-1:ℝ) 1, (-2:ℝ) ≤ f1 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf3y_ge : ∀ t ∈ Icc (-1:ℝ) 1, l 1 ≤ f3 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1ub]
  have hf3y_le : ∀ t ∈ Icc (-1:ℝ) 1, f3 t 1 ≤ 2 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1lb, hl1ub]
  have hbound : ∀ z ∈ (f1 '' Icc (-1:ℝ) 1 ∪ f2 '' Icc (-1:ℝ) 1) ∪ f3 '' Icc (-1:ℝ) 1,
      z 0 ∈ Icc (-1:ℝ) 1 ∧ z 1 ∈ Icc (-2:ℝ) 2 := by
    rintro z ((⟨t1, ht1, rfl⟩ | ⟨t2, ht2, rfl⟩) | ⟨t3, ht3, rfl⟩)
    · exact ⟨by rw [hf1x]; norm_num,
        mem_Icc.2 ⟨hf1y_ge t1 ht1, le_trans (hf1y_le t1 ht1) hm1ub⟩⟩
    · exact hrect (hJnr (hf2mem t2 ht2).1)
    · exact ⟨by rw [hf3x]; norm_num,
        mem_Icc.2 ⟨le_trans hl1lb (hf3y_ge t3 ht3), hf3y_le t3 ht3⟩⟩
  have hcE : ∀ t ∈ Icc (-1:ℝ) 1, c t 0 ∈ Icc (-1:ℝ) 1 ∧ c t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hbound (c t) (hcmem t ht)
  -- the concatenation is a bottom-to-top path, so it must meet `J_s`
  obtain ⟨t, ht, hctJs⟩ :=
    vertical_meets_arc hbr hJsrect hJoinJs hccont hcE hcm1 hcn1
  rcases hcmem t ht with (⟨t1, ht1, ht1e⟩ | ⟨t2, ht2, ht2e⟩) | ⟨t3, ht3, ht3e⟩
  · -- on the lower axis segment: contradicts `hcon` (height `≤ m 1`)
    have hct0 : c t 0 = 0 := by rw [← ht1e]; exact hf1x t1
    have hcty : c t 1 ≤ m 1 := by rw [← ht1e]; exact hf1y_le t1 ht1
    exact absurd (hcon (c t) hctJs hct0) (not_lt.2 hcty)
  · -- on the middle piece: lands in `J_n \ {a,b}`, disjoint from `J_s`
    have hctJn : c t ∈ J_n := ht2e ▸ (hf2mem t2 ht2).1
    have hctnab : c t ∉ ({a, b} : Set Plane) := ht2e ▸ (hf2mem t2 ht2).2
    have : c t ∈ J_n ∩ J_s := ⟨hctJn, hctJs⟩
    rw [hInter] at this
    exact hctnab this
  · -- on the upper axis segment: forced to equal `l`, but `l ∉ J_s`
    have hct0 : c t 0 = 0 := by rw [← ht3e]; exact hf3x t3
    have hcty_ge : l 1 ≤ c t 1 := by rw [← ht3e]; exact hf3y_ge t3 ht3
    have hcty_le : c t 1 ≤ l 1 := hlmax (c t) (hJsr hctJs) hct0
    have hcty : c t 1 = l 1 := le_antisymm hcty_le hcty_ge
    have hctl : c t = l := by ext i; fin_cases i <;> simp [hct0, hl0, hcty]
    have hlnJs : l ∉ J_s := by
      intro h
      have : l ∈ J_n ∩ J_s := ⟨hlJn, h⟩
      rw [hInter] at this; exact hlab this
    exact hlnJs (hctl ▸ hctJs)

/-- **Maehara's construction points.** Bundles the five points of Maehara's figure
on the vertical axis `x = 0`:
* `l` — the topmost intersection of the axis with the curve (in `J_n`);
* `m` — the lowest point of `J_n` on the axis;
* `p` — the highest point of `J_s` on the axis lying at or below `m` (the top of the
  southern arc on the segment `m → s`, via `ms_meets_Js`);
* `q` — the lowest point of `J_s` on the axis;
* `z₀` — the midpoint `!₂[0,(m 1 + p 1)/2]` of `m` and `p`.

The established `y`-ordering is `q 1 ≤ p 1 ≤ z₀ 1 ≤ m 1 ≤ l 1`. (Note `p` is the
`J_s`-max **restricted to heights `≤ m 1`**; this is what makes `p 1 ≤ m 1` — hence
the placement of `z₀` between `p` and `m` — provable at this stage.) -/
theorem exists_construction_points (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ (J_n J_s : Set Plane) (l m p q z₀ : Plane),
      J_n ∪ J_s = range r ∧
      J_n ∩ J_s = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} ∧
      IsPathConnected (J_n \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      (l ∈ J_n ∧ l 0 = 0 ∧ ∀ w ∈ range r, w 0 = 0 → w 1 ≤ l 1) ∧
      (m ∈ J_n ∧ m 0 = 0 ∧ ∀ w ∈ J_n, w 0 = 0 → m 1 ≤ w 1) ∧
      (p ∈ J_s ∧ p 0 = 0 ∧ p 1 ≤ m 1 ∧ ∀ w ∈ J_s, w 0 = 0 → w 1 ≤ m 1 → w 1 ≤ p 1) ∧
      (q ∈ J_s ∧ q 0 = 0 ∧ ∀ w ∈ J_s, w 0 = 0 → q 1 ≤ w 1) ∧
      z₀ = !₂[(0:ℝ), (m 1 + p 1) / 2] ∧
      m 1 ≤ l 1 ∧ q 1 ≤ p 1 ∧ p 1 ≤ z₀ 1 ∧ z₀ 1 ≤ m 1 ∧
      IsPathConnected (J_s \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      JoinedIn J_n (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) ∧
      JoinedIn J_s (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) := by
  obtain ⟨J_n, J_s, hJncl, hJscl, hUnion, hInter, ⟨eJn⟩, ⟨eJs⟩, hpcJn, hpcJs,
    l, hlr, hl0, hlmax, hlJn⟩ := jordan_arcs hbr hcont hinj hm hp hfar
  have hcptr : IsCompact (range r) := jordanCurve_isCompact r hcont
  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hJncpt : IsCompact J_n := hcptr.of_isClosed_subset hJncl hJnr
  have hJscpt : IsCompact J_s := hcptr.of_isClosed_subset hJscl hJsr
  -- `m` : lowest point of `J_n` on the axis
  obtain ⟨m, hmJn, hm0, hmmin⟩ := exists_ymin_Jn_axis hJncl hJncpt hlJn hl0
  -- `J_s` meets the axis below `m`
  obtain ⟨w₀, hw₀Js, hw₀0, hw₀m⟩ :=
    ms_meets_Js hbr hcont hinj hm hp hfar hUnion hInter eJs hpcJn hlJn hl0 hlmax hmJn hm0
  -- `p` : highest point of `J_s` on the axis at or below `m`
  set Sp : Set Plane := {w ∈ J_s | w 0 = 0 ∧ w 1 ≤ m 1} with hSpdef
  have hSpcl : IsClosed Sp := by
    have hEq : Sp = (J_s ∩ {w : Plane | w 0 = 0}) ∩ {w : Plane | w 1 ≤ m 1} := by
      ext w
      constructor
      · rintro ⟨hJ, h0, hle⟩; exact ⟨⟨hJ, h0⟩, hle⟩
      · rintro ⟨⟨hJ, h0⟩, hle⟩; exact ⟨hJ, h0, hle⟩
    rw [hEq]
    exact (hJscl.inter (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hSpcpt : IsCompact Sp := hJscpt.of_isClosed_subset hSpcl (fun w hw => hw.1)
  obtain ⟨p, hpSp, hpmax⟩ := hSpcpt.exists_isMaxOn ⟨w₀, hw₀Js, hw₀0, hw₀m⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn
  -- `q` : lowest point of `J_s` on the axis
  set Sq : Set Plane := {w ∈ J_s | w 0 = 0} with hSqdef
  have hSqcl : IsClosed Sq :=
    hJscl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hSqcpt : IsCompact Sq := hJscpt.of_isClosed_subset hSqcl (fun w hw => hw.1)
  obtain ⟨q, hqSq, hqmin⟩ := hSqcpt.exists_isMinOn ⟨w₀, hw₀Js, hw₀0⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn
  -- extract the packaged facts
  have hpm : p 1 ≤ m 1 := hpSp.2.2
  have hml : m 1 ≤ l 1 := hlmax m (hJnr hmJn) hm0
  have hqp : q 1 ≤ p 1 := hqmin ⟨hpSp.1, hpSp.2.1⟩
  have haJn : (!₂[(-1:ℝ), 0] : Plane) ∈ J_n := by
    have : (!₂[(-1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.1
  have hbJn : (!₂[(1:ℝ), 0] : Plane) ∈ J_n := by
    have : (!₂[(1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.1
  have haJs : (!₂[(-1:ℝ), 0] : Plane) ∈ J_s := by
    have : (!₂[(-1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.2
  have hbJs : (!₂[(1:ℝ), 0] : Plane) ∈ J_s := by
    have : (!₂[(1:ℝ), 0] : Plane) ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJn : JoinedIn J_n (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) := arc_joinedIn eJn haJn hbJn
  have hJoinJs : JoinedIn J_s (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) := arc_joinedIn eJs haJs hbJs
  refine ⟨J_n, J_s, l, m, p, q, !₂[(0:ℝ), (m 1 + p 1) / 2], hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩,
    ⟨hpSp.1, hpSp.2.1, hpm, fun w hwJs hw0 hwm => hpmax ⟨hwJs, hw0, hwm⟩⟩,
    ⟨hqSq.1, hqSq.2, fun w hwJs hw0 => hqmin ⟨hwJs, hw0⟩⟩, rfl, hml, hqp, ?_, ?_,
    hpcJs, hJoinJn, hJoinJs⟩
  · rw [show (!₂[(0:ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]
  · rw [show (!₂[(0:ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]

end MatedCRTHarmonic.Planar.Jordan
