/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5f at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H3
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom2

/-!
# CONF Theorem 3.9, packet J6d: saturated events of the normalized field and extra local data

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1559–1561 with `h` viewed modulo additive constants (C:1154): on a hull piece the arcs are
functions of the internal metric of `D_h` near `𝓑^•_{s_k}` (up to the factor `e^{ξc}`) and of
further local data (the sets `𝓑^•_{s_k}`, `𝓑^•_τ`).

**`t39k5_piece_sat`**: for the normalized field `g = h − h_r(z)` (`∂B_r(z) ⊆ A`), a random
variable `Z` (standard Borel values) measurable for a σ-algebra `G`, and a null-measurable `B`
saturated for the internal metric of `D_g` on `A`, the event `{(g, Z) ∈ B}` is a.s. an event of
`σ(h|_A mod const) ⊔ G`. Copy-and-adapt of `LocalEvent.exists_fieldSigma_piece`
(Meas/LocalEventRandom2: chain codes of the internal metric on a dense sequence, Axiom II
`hD.locality`, `LocalEvent.aeEventIn_of_saturated`) with the extra coordinate `Z`, followed by
the normalization `conf36_aeEventIn_fieldSigma0On_of_norm` (S3D114U1) in the a.s. σ-algebra
`t39hAESig` (S3T39H3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint LocalEvent

/-- **saturated events of `(h − h_r(z), Z)` are a.s. events of `σ(h|_A mod const) ⊔ G`** -/
theorem t39k5_piece_sat {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} (G : MeasurableSpace Ω) [MeasurableSpace Ω]
    {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r)
    {z : ℂ} {A : Opens ℂ} (hsph : sphere z r ⊆ A)
    {𝒵 : Type} [MeasurableSpace 𝒵] [StandardBorelSpace 𝒵]
    {Z : Ω → 𝒵} (hZG : Measurable[G] Z) (hZ : Measurable Z)
    (hlen : ∀ᵐ ω ∂P, D (addConst (h ω) (-circleAvg (h ω) r z)) ∈ lenSet)
    {B : Set (DistC × 𝒵)}
    (hB : NullMeasurableSet B (P.map fun ω => (addConst (h ω) (-circleAvg (h ω) r z), Z ω)))
    (hsat : ∀ g₁ g₂ : DistC, D g₁ ∈ lenSet → D g₂ ∈ lenSet →
      (D g₁).internal A = (D g₂).internal A → ∀ ζ, (g₁, ζ) ∈ B → (g₂, ζ) ∈ B) :
    AEEventIn P (fieldSigma0On h A ⊔ G)
      {ω | (addConst (h ω) (-circleAvg (h ω) r z), Z ω) ∈ B} := by
  classical
  let := upgradeStandardBorel 𝒵
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) r z) with hg_def
  have hm : Measurable fun ω => -circleAvg (h ω) r z :=
    ((measurable_circleAvg_left r z).comp hh.measurable).neg
  have hgp := GM.Tight.isGFFPlusCont_of_wp (hh.addConst hm)
  have hgm : Measurable g := hgp.1
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P g hgp A
  have hAne : (A : Set ℂ).Nonempty := ⟨z + (r : ℂ), hsph (by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr])⟩
  have : Nonempty (A : Set ℂ) := hAne.to_subtype
  set q : ℕ → ℂ := fun n => (TopologicalSpace.denseSeq (A : Set ℂ) n : ℂ) with hq
  have hqU : ∀ n, q n ∈ (A : Set ℂ) := fun n => (TopologicalSpace.denseSeq (A : Set ℂ) n).2
  have hqd : (A : Set ℂ) ⊆ closure (range q) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro o ho hxo
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (A : Set ℂ)).exists_mem_open
      (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
    exact ⟨q n, hn, n, rfl⟩
  let R : DistC × 𝒵 → (ℕ × ℕ → ℝ≥0∞) × 𝒵 :=
    fun y => (fun p => (D y.1).chainInf A (q p.1) (q p.2), y.2)
  let Gf : DistOn A → (ℕ × ℕ → ℝ≥0∞) := fun x p => Φ x (q p.1) (q p.2)
  have hR : Measurable R := (measurable_pi_iff.2 fun p =>
    GM.measurable_chainInf_comp (hD.measurable.comp measurable_fst) measurable_const
      measurable_const _).prodMk measurable_snd
  have hG : Measurable Gf := measurable_pi_iff.2 fun p =>
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
  have hV : Measurable[fieldSigma g A ⊔ G] fun ω => (Gf (restrictTo A (g ω)), Z ω) :=
    Measurable.prodMk (m := fieldSigma g A ⊔ G)
      ((hG.comp (Measurable.of_comap_le le_rfl)).mono le_sup_left le_rfl)
      (hZG.mono le_sup_right le_rfl)
  have hVR : ∀ᵐ ω ∂P, (Gf (restrictTo A (g ω)), Z ω) = R (g ω, Z ω) := by
    filter_upwards [hΦae, hlen] with ω h1 h3
    refine Prod.ext (funext fun p => ?_) rfl
    show Φ _ (q p.1) (q p.2) = (D (g ω)).chainInf A (q p.1) (q p.2)
    rw [← h1 _ (hqU _) _ (hqU _)]
    exact (D (g ω)).internal_eq_chainInf (isLength_of_mem_lenSet h3) A.isOpen _ _
  have hW : MeasurableSet ((D ⁻¹' lenSet) ×ˢ (univ : Set 𝒵)) :=
    (measurableSet_lenSet.preimage hD.measurable).prod MeasurableSet.univ
  have hYW : ∀ᵐ ω ∂P, (g ω, Z ω) ∈ (D ⁻¹' lenSet) ×ˢ (univ : Set 𝒵) :=
    hlen.mono fun ω hω => ⟨hω, trivial⟩
  have hs : ∀ y₁ ∈ (D ⁻¹' lenSet) ×ˢ (univ : Set 𝒵), ∀ y₂ ∈ (D ⁻¹' lenSet) ×ˢ (univ : Set 𝒵),
      R y₁ = R y₂ → y₁ ∈ B → y₂ ∈ B := by
    rintro ⟨g₁, ζ₁⟩ ⟨h1, -⟩ ⟨g₂, ζ₂⟩ ⟨h2, -⟩ he hB₁
    have l1 := isLength_of_mem_lenSet h1
    have l2 := isLength_of_mem_lenSet h2
    obtain ⟨he1, he2⟩ := Prod.ext_iff.1 he
    change ζ₁ = ζ₂ at he2
    subst he2
    refine hsat g₁ g₂ h1 h2 ?_ ζ₁ hB₁
    refine GM.internal_eq_of_dense l1 l2 A.isOpen hqU hqd fun i j => ?_
    rw [(D g₁).internal_eq_chainInf l1 A.isOpen, (D g₂).internal_eq_chainInf l2 A.isOpen]
    exact congrFun he1 (i, j)
  obtain ⟨F, hF, hEF⟩ := LocalEvent.aeEventIn_of_saturated (Y := fun ω => (g ω, Z ω))
    (hgm.prodMk hZ) hR hV hVR hW hB hYW hs
  have hle : fieldSigma g A ⊔ G ≤ t39hAESig P (fieldSigma0On h A ⊔ G) := by
    refine sup_le (fun F' hF' => ?_) (fun F' hF' => ⟨F', (le_sup_right : G ≤ _) _ hF',
      Filter.EventuallyEq.rfl⟩)
    obtain ⟨F'', hF'', hE''⟩ :=
      conf36_aeEventIn_fieldSigma0On_of_norm hh hr (le_refl A) hsph
        ⟨F', hF', Filter.EventuallyEq.rfl⟩
    exact ⟨F'', (le_sup_left : fieldSigma0On h A ≤ _) _ hF'', hE''⟩
  obtain ⟨F', hF', hFF'⟩ := hle F hF
  exact ⟨F', hF', hEF.trans hFF'⟩

end LQGMetric.CONF
