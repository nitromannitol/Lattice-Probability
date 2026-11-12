/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5Chain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Disc
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.5, Step 2: chaining crossings along a graph path (deterministic part)

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Theorem 1.5, Step 2 (T:1677–1690): along a path `π` of the graph `(𝕣𝕊) ∩ (δ𝕣ℤ²)` from
`∂_L` to `∂_R`, short `D_h`-paths attached to the vertices `π(j)` meet consecutively, so their
union connects the left and right sides of `𝕣𝕊` and
`D_h(𝕣∂_L𝕊, 𝕣∂_R𝕊) ≤ Σ_j (D_h-length of the paths at π(j))` (eqn-lfpp-lower).

The paper uses loops around the square annuli `B_{δ𝕣}(S_z) ∖ S_z` ((eqn-square-around), node
DFGPS.S9 of `blueprint/DFGPS.md`). We use instead, at each vertex `z` (`s = δ𝕣`), a horizontal
crossing `H_z` of the rectangle `z + s((-3,3) × (-1/2,1/2))` between its short sides and a
vertical crossing `V_z` of `z + s((-1/2,1/2) × (-3,3))` (both given by DFGPS Prop 3.1 with
`K₁, K₂` = the short sides, `U` = the rectangle). For `8`-neighbours `z, z'` the horizontal
crossing at `z` meets the vertical one at `z'`, and `V_{z'}` meets `H_{z'}`, by the crossing lemma
for rectangles (`RectMeet.rect_crossings_meet`, Poincaré–Miranda in dimension two). This is the
blueprint's own argument for S9 (four overlapping rectangles), with two rectangles per vertex
(proposed DEVIATIONS entry in the report).
-/

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

/-- a path realizing `D(A, B; V) < X` -/
lemma exists_path_of_setDistIn_lt (D : ContMetric) {A B V : Set ℂ} {X : ℝ≥0∞}
    (h : setDistIn D A B V < X) :
    ∃ P : ℝ → ℂ, ContinuousOn P (Icc 0 1) ∧ P 0 ∈ A ∧ P 1 ∈ B ∧ MapsTo P (Icc 0 1) V ∧
      D.len P 0 1 < X := by
  unfold setDistIn at h
  simp only [iInf_lt_iff] at h
  obtain ⟨u, hu, v, hv, h⟩ := h
  unfold ContMetric.internal internalEDist at h
  rw [iInf_lt_iff] at h
  obtain ⟨⟨γ, hγ⟩, hlen⟩ := h
  refine ⟨fun t => D.unpt (γ.extend t), (D.continuous_unpt.comp γ.continuous_extend).continuousOn,
    by simpa using hu, by simpa using hv, fun t ht => ?_, hlen⟩
  have h1 := hγ ⟨t, ht⟩
  show D.unpt (γ.extend t) ∈ V
  rw [Path.extend_apply γ ht]
  obtain ⟨w, hw, hweq⟩ := h1
  rw [← hweq]; exact hw

/-- two points of one path in `Y` are at internal distance at most its length -/
lemma internal_le_len_of_path (D : ContMetric) {Y : Set ℂ} {P : ℝ → ℂ}
    (hP : ContinuousOn P (Icc 0 1)) (hY : MapsTo P (Icc 0 1) Y) {t₁ t₂ : ℝ}
    (h₁ : t₁ ∈ Icc (0 : ℝ) 1) (h₂ : t₂ ∈ Icc (0 : ℝ) 1) :
    D.internal Y (P t₁) (P t₂) ≤ D.len P 0 1 := by
  have key : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a ≤ b →
      D.internal Y (P a) (P b) ≤ D.len P 0 1 := by
    intro a b ha hb hab
    have hsub : Icc a b ⊆ Icc 0 1 := Icc_subset_Icc ha.1 hb.2
    calc D.internal Y (P a) (P b) ≤ curveLength (D.pt ∘ P) a b :=
          internalEDist_le_curveLength hab (D.continuous_pt.comp_continuousOn (hP.mono hsub))
            fun u hu => ⟨P u, hY (hsub hu), rfl⟩
      _ ≤ D.len P 0 1 := curveLength_mono _ ha.1 hb.2
  rcases le_total t₁ t₂ with h | h
  · exact key _ _ h₁ h₂ h
  · unfold ContMetric.internal; rw [internalEDist_comm]; exact key _ _ h₂ h₁ h

lemma affine_mem_Icc {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Icc a b := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩

lemma affine_mem_Icc' {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Icc (0 : ℝ) 1) :
    b - u * (b - a) ∈ Icc a b := ⟨by nlinarith [hu.2], by nlinarith [hu.1]⟩

/-- **A horizontal crossing at `z` meets a vertical crossing at a neighbour `z'`**
(crossing lemma for the rectangle `[z.re ± 5s/2] × [z'.im ± 5s/2]`). -/
lemma HV_meet {s : ℝ} (hs : 0 < s) {z z' : ℂ} (hre : |z'.re - z.re| ≤ s)
    (him : |z'.im - z.im| ≤ s) {H V : ℝ → ℂ} (hH : ContinuousOn H (Icc 0 1))
    (hV : ContinuousOn V (Icc 0 1)) (hH0 : (H 0).re = z.re - 5 / 2 * s)
    (hH1 : (H 1).re = z.re + 5 / 2 * s) (hHm : ∀ t ∈ Icc (0 : ℝ) 1, |(H t).im - z.im| ≤ s / 2)
    (hV0 : (V 0).im = z'.im - 5 / 2 * s) (hV1 : (V 1).im = z'.im + 5 / 2 * s)
    (hVm : ∀ t ∈ Icc (0 : ℝ) 1, |(V t).re - z'.re| ≤ s / 2) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ t' ∈ Icc (0 : ℝ) 1, H t = V t' := by
  obtain ⟨a, b, ha, hab, hb, hHa, hHb, hHab⟩ := RectCross.exists_sub_crossing (f := fun t => (H t).re)
    zero_le_one (Complex.continuous_re.comp_continuousOn hH) (by linarith) hH0.le hH1.ge
  obtain ⟨a', b', ha', hab', hb', hVa, hVb, hVab⟩ :=
    RectCross.exists_sub_crossing (f := fun t => (V t).im)
    zero_le_one (Complex.continuous_im.comp_continuousOn hV) (by linarith) hV0.le hV1.ge
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha hb
  have hsub' : Icc a' b' ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha' hb'
  rw [abs_le] at hre him
  obtain ⟨u, hu, w, hw, huw⟩ := RectMeet.rect_crossings_meet (z.re - 5 / 2 * s) (z.re + 5 / 2 * s)
    (z'.im - 5 / 2 * s) (z'.im + 5 / 2 * s) (fun u => H (a + u * (b - a)))
    (fun u => V (b' - u * (b' - a')))
    (hH.comp (by fun_prop) fun u hu => hsub (affine_mem_Icc hab hu))
    (hV.comp (by fun_prop) fun u hu => hsub' (affine_mem_Icc' hab' hu))
    (fun u hu => by
      have h1 := hHab _ (affine_mem_Icc hab hu)
      have h2 := hHm _ (hsub (affine_mem_Icc hab hu))
      rw [abs_le] at h2
      exact ⟨h1, by constructor <;> linarith [h2.1, h2.2]⟩)
    (fun u hu => by
      have h1 := hVab _ (affine_mem_Icc' hab' hu)
      have h2 := hVm _ (hsub' (affine_mem_Icc' hab' hu))
      rw [abs_le] at h2
      exact ⟨by constructor <;> linarith [h2.1, h2.2], h1⟩)
    (by simpa using hHa) (by simpa using hHb) (by simpa using hVb) (by simpa using hVa)
  exact ⟨_, hsub (affine_mem_Icc hab hu), _, hsub' (affine_mem_Icc' hab' hw), huw⟩

lemma internal_triangle (D : ContMetric) (Y : Set ℂ) (u v w : ℂ) :
    D.internal Y u w ≤ D.internal Y u v + D.internal Y v w :=
  internalEDist_triangle _ _ _ _

/-- grid neighbours differ by at most one step in each coordinate -/
lemma abs_sub_le_of_adj {s : ℝ} (hs : 0 < s) {z z' : ℂ} (hz : z ∈ gridPts s)
    (hz' : z' ∈ gridPts s) (hadj : ‖z - z'‖ = s ∨ ‖z - z'‖ = Real.sqrt 2 * s) :
    |z'.re - z.re| ≤ s ∧ |z'.im - z.im| ≤ s := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨a', b', rfl⟩ := hz'
  have hn : ‖(⟨a * s, b * s⟩ : ℂ) - ⟨a' * s, b' * s⟩‖ < 2 * s := by
    have h2 : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    rcases hadj with h | h <;> rw [h] <;> nlinarith
  have key : ∀ k : ℤ, |(k : ℝ) * s| < 2 * s → |(k : ℝ) * s| ≤ s := by
    intro k hk
    rw [abs_mul, abs_of_pos hs] at hk ⊢
    have h1 : |(k : ℝ)| < 2 := by nlinarith
    have h2 : |k| < 2 := by exact_mod_cast (Int.cast_abs (R := ℝ) ▸ h1)
    have h3 : |k| ≤ 1 := by omega
    have h4 : |(k : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast h3
    nlinarith
  constructor
  · have h := (Complex.abs_re_le_norm _).trans_lt hn
    simp only [Complex.sub_re] at h
    have := key (a' - a) (by
      push_cast; rw [show ((a' : ℝ) - a) * s = -(a * s - a' * s) by ring, abs_neg]; exact h)
    push_cast at this; convert this using 2; ring
  · have h := (Complex.abs_im_le_norm _).trans_lt hn
    simp only [Complex.sub_im] at h
    have := key (b' - b) (by
      push_cast; rw [show ((b' : ℝ) - b) * s = -(b * s - b' * s) by ring, abs_neg]; exact h)
    push_cast at this; convert this using 2; ring

lemma le_re_add_of_mem_rightVerts {s 𝕣 : ℝ} (hs : 0 < s) (h𝕣 : 0 < 𝕣) {z : ℂ}
    (hz : z ∈ rightVerts s 𝕣) : 𝕣 ≤ z.re + s := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨hzS, a, b, rfl⟩, hmax⟩ := hz
  have hS := (mem_rS_iff h𝕣).1 hzS
  simp only at hS hc
  have hw : (⟨((a + 1 : ℤ) : ℝ) * s, b * s⟩ : ℂ) ∈ rS 𝕣 ∩ gridPts s := by
    refine ⟨(mem_rS_iff h𝕣).2 ⟨?_, ?_, hS.2.2.1, hS.2.2.2⟩, _, _, rfl⟩ <;> push_cast <;> nlinarith
  have := hmax _ hw
  simp only at this; push_cast at this; nlinarith

lemma re_le_of_mem_leftVerts {s 𝕣 : ℝ} (hs : 0 < s) (hs𝕣 : s < 𝕣) {z : ℂ}
    (hz : z ∈ leftVerts s 𝕣) : z.re ≤ s := by
  have h𝕣 : 0 < 𝕣 := hs.trans hs𝕣
  obtain ⟨⟨hzS, a, b, rfl⟩, hmin⟩ := hz
  have hS := (mem_rS_iff h𝕣).1 hzS
  have hw : (⟨((1 : ℤ) : ℝ) * s, b * s⟩ : ℂ) ∈ rS 𝕣 ∩ gridPts s :=
    ⟨(mem_rS_iff h𝕣).2 ⟨by push_cast; linarith, by push_cast; linarith, hS.2.2.1, hS.2.2.2⟩,
      _, _, rfl⟩
  have := hmin _ hw
  simpa using this

section Chain
variable (D : ContMetric) {s 𝕣 : ℝ} {Y : Set ℂ} (b : ℂ → ℝ) (H V : ℂ → ℝ → ℂ)

/-- the properties of the horizontal crossing `H z` at a vertex `z` -/
def HCross (s : ℝ) (Y : Set ℂ) (z : ℂ) (P : ℝ → ℂ) (B : ℝ) : Prop :=
  ContinuousOn P (Icc 0 1) ∧ (P 0).re = z.re - 5 / 2 * s ∧ (P 1).re = z.re + 5 / 2 * s ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |(P t).im - z.im| ≤ s / 2) ∧ MapsTo P (Icc 0 1) Y ∧
    D.len P 0 1 ≤ ENNReal.ofReal B

/-- the properties of the vertical crossing `V z` at a vertex `z` -/
def VCross (s : ℝ) (Y : Set ℂ) (z : ℂ) (P : ℝ → ℂ) (B : ℝ) : Prop :=
  ContinuousOn P (Icc 0 1) ∧ (P 0).im = z.im - 5 / 2 * s ∧ (P 1).im = z.im + 5 / 2 * s ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |(P t).re - z.re| ≤ s / 2) ∧ MapsTo P (Icc 0 1) Y ∧
    D.len P 0 1 ≤ ENNReal.ofReal B

lemma chain_aux (hs : 0 < s) (h𝕣 : 0 < 𝕣) (hb : ∀ z, 0 ≤ b z)
    (hH : ∀ z ∈ rS 𝕣 ∩ gridPts s, HCross D s Y z (H z) (b z))
    (hV : ∀ z ∈ rS 𝕣 ∩ gridPts s, VCross D s Y z (V z) (b z)) :
    ∀ (rest : List ℂ) (z : ℂ), IsGraphPath s (rS 𝕣) (z :: rest) →
      (∃ y ∈ (z :: rest).getLast?, y ∈ rightVerts s 𝕣) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∃ e : ℂ, e.re = 𝕣 ∧ (∃ y ∈ rS 𝕣, |e.im - y.im| ≤ s / 2) ∧
        D.internal Y (H z t) e ≤ ENNReal.ofReal (b z + (rest.map fun x => 2 * b x).sum) := by
  intro rest
  induction rest with
  | nil =>
    intro z hL hlast t ht
    obtain ⟨y, hy, hyR⟩ := hlast
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hy
    subst hy
    have hzg := hL.2.1 z (by simp)
    obtain ⟨hc, h0, h1, hm, hY, hlen⟩ := hH z ⟨hzg.1, hzg.2⟩
    have hR := le_re_add_of_mem_rightVerts hs h𝕣 hyR
    have hzS := (mem_rS_iff h𝕣).1 hzg.1
    obtain ⟨te, hte, hre⟩ := intermediate_value_Icc zero_le_one
      (Complex.continuous_re.comp_continuousOn hc) ⟨by show (H z 0).re ≤ 𝕣; linarith,
        by show 𝕣 ≤ (H z 1).re; linarith⟩
    refine ⟨H z te, hre, ⟨z, hzg.1, hm te hte⟩, ?_⟩
    simpa using (internal_le_len_of_path D hc hY ht hte).trans hlen
  | cons z' rest ih =>
    intro z hL hlast t ht
    have hz := hL.2.1 z (by simp)
    have hz' := hL.2.1 z' (by simp)
    obtain ⟨hadj, hchain⟩ := List.isChain_cons_cons.1 hL.2.2
    have hL' : IsGraphPath s (rS 𝕣) (z' :: rest) :=
      ⟨by simp, fun x hx => hL.2.1 x (List.mem_cons_of_mem _ hx), hchain⟩
    have hlast' : ∃ y ∈ (z' :: rest).getLast?, y ∈ rightVerts s 𝕣 := by
      simpa [List.getLast?_cons_cons] using hlast
    obtain ⟨hHc, hH0, hH1, hHm, hHY, hHl⟩ := hH z ⟨hz.1, hz.2⟩
    obtain ⟨hHc', hH0', hH1', hHm', hHY', hHl'⟩ := hH z' ⟨hz'.1, hz'.2⟩
    obtain ⟨hVc', hV0', hV1', hVm', hVY', hVl'⟩ := hV z' ⟨hz'.1, hz'.2⟩
    obtain ⟨hdre, hdim⟩ := abs_sub_le_of_adj hs hz.2 hz'.2 hadj
    obtain ⟨t₁, ht₁, t₁', ht₁', e₁⟩ :=
      HV_meet hs hdre hdim hHc hVc' hH0 hH1 hHm hV0' hV1' hVm'
    obtain ⟨t₂, ht₂, t₂', ht₂', e₂⟩ :=
      HV_meet hs (by simp [hs.le]) (by simp [hs.le]) hHc' hVc' hH0' hH1' hHm' hV0' hV1' hVm'
    obtain ⟨e, he, hey, hint⟩ := ih z' hL' hlast' t₂ ht₂
    refine ⟨e, he, hey, ?_⟩
    have hS : 0 ≤ (rest.map fun x => 2 * b x).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; linarith [hb y]
    calc D.internal Y (H z t) e
        ≤ D.internal Y (H z t) (H z t₁) + (D.internal Y (V z' t₁') (V z' t₂') +
            D.internal Y (H z' t₂) e) := by
          refine (internal_triangle D Y _ (H z t₁) _).trans (add_le_add le_rfl ?_)
          rw [e₁]
          refine (internal_triangle D Y _ (V z' t₂') _).trans (le_of_eq ?_)
          rw [e₂]
      _ ≤ ENNReal.ofReal (b z) + (ENNReal.ofReal (b z') +
            ENNReal.ofReal (b z' + (rest.map fun x => 2 * b x).sum)) :=
          add_le_add ((internal_le_len_of_path D hHc hHY ht ht₁).trans hHl)
            (add_le_add ((internal_le_len_of_path D hVc' hVY' ht₁' ht₂').trans hVl') hint)
      _ = ENNReal.ofReal (b z + ((z' :: rest).map fun x => 2 * b x).sum) := by
          rw [← ENNReal.ofReal_add (hb z') (add_nonneg (hb z') hS),
            ← ENNReal.ofReal_add (hb z) (by linarith [hb z'])]
          congr 1
          simp only [List.map_cons, List.sum_cons]; ring

/-- **DFGPS Thm 1.5, Step 2, deterministic part** ((eqn-lfpp-lower), T:1677–1690): if every
vertex `z` of `(𝕣𝕊) ∩ sℤ²` carries a horizontal and a vertical crossing in `Y` of lengths at most
`b z`, then for every graph path `L` from `∂^s_L` to `∂^s_R`,
`D(K₁, K₂; Y) ≤ Σ_{z ∈ L} 2 b(z)`, where `K₁ ⊇` the points of `Re = 0` near `𝕣𝕊` and `K₂ ⊇` the
points of `Re = 𝕣` near `𝕣𝕊`. -/
theorem setDistIn_le_of_graphPath (hs : 0 < s) (hs𝕣 : s < 𝕣) (hb : ∀ z, 0 ≤ b z)
    (hH : ∀ z ∈ rS 𝕣 ∩ gridPts s, HCross D s Y z (H z) (b z))
    (hV : ∀ z ∈ rS 𝕣 ∩ gridPts s, VCross D s Y z (V z) (b z)) {K₁ K₂ : Set ℂ}
    (hK₁ : ∀ w : ℂ, w.re = 0 → (∃ y ∈ rS 𝕣, |w.im - y.im| ≤ s / 2) → w ∈ K₁)
    (hK₂ : ∀ w : ℂ, w.re = 𝕣 → (∃ y ∈ rS 𝕣, |w.im - y.im| ≤ s / 2) → w ∈ K₂)
    {L : List ℂ} (hL : IsGraphPath s (rS 𝕣) L) (hhead : ∃ x ∈ L.head?, x ∈ leftVerts s 𝕣)
    (hlast : ∃ y ∈ L.getLast?, y ∈ rightVerts s 𝕣) :
    setDistIn D K₁ K₂ Y ≤ ENNReal.ofReal ((L.map fun x => 2 * b x).sum) := by
  have h𝕣 : 0 < 𝕣 := hs.trans hs𝕣
  obtain ⟨z₀, rest, rfl⟩ : ∃ z₀ rest, L = z₀ :: rest := by
    cases L with
    | nil => exact absurd rfl hL.1
    | cons x rest => exact ⟨x, rest, rfl⟩
  obtain ⟨x, hx, hxL⟩ := hhead
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  rw [← hx] at hxL
  have hz := hL.2.1 z₀ (by simp)
  have hzS := (mem_rS_iff h𝕣).1 hz.1
  have hle := re_le_of_mem_leftVerts hs hs𝕣 hxL
  obtain ⟨hc, h0, h1, hm, -, -⟩ := hH z₀ ⟨hz.1, hz.2⟩
  obtain ⟨t₀, ht₀, hre⟩ := intermediate_value_Icc zero_le_one
    (Complex.continuous_re.comp_continuousOn hc) ⟨by show (H z₀ 0).re ≤ 0; linarith,
      by show 0 ≤ (H z₀ 1).re; linarith⟩
  obtain ⟨e, he, hey, hint⟩ := chain_aux D b H V hs h𝕣 hb hH hV rest z₀ hL hlast t₀ ht₀
  have hS : 0 ≤ (rest.map fun x => 2 * b x).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; linarith [hb y]
  calc setDistIn D K₁ K₂ Y ≤ D.internal Y (H z₀ t₀) e :=
        iInf₂_le_of_le _ (hK₁ _ hre ⟨z₀, hz.1, hm t₀ ht₀⟩) (iInf₂_le_of_le _ (hK₂ _ he hey) le_rfl)
    _ ≤ _ := hint.trans (ENNReal.ofReal_le_ofReal (by
        simp only [List.map_cons, List.sum_cons]; linarith [hb z₀]))

end Chain

end LQGMetric.DFGPS
