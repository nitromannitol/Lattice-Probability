/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.ArcDeterminesDriver at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardFlow
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardHolo
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Convex

/-!
# A simple arc determines its driver

Sheffield, *Conformal weldings of random surfaces*, §1.4 (proof of Theorem 1.4); blueprint node
A3, the lemma "a simple arc determines its driver".

Main result, `eqOn_of_revMap_eq`: let `W, W'` be continuous drivers from `0`, `T > 0`, and
suppose that for both, the forward hulls of the time-reversed increment on `[0,T]` are the
initial arcs of one simple chord. If `revMap W' T = revMap W T` on `ℍ`, then `W = W'` on
`[0,T]`.

Proof:
1. (`exists_reparam`) equal final arcs let one chord be reparametrized along the other, so each
   forward hull of one driver is a forward hull of the other.
2. (`fwdHull_eq_imp`) equal simple forward hulls give equal times and centred forward maps that
   differ by the difference of the terminal driver values. `χ = f_a ∘ g_b'` is a holomorphic
   bijection of `ℍ` with `χ(z) - z` bounded, so Phragmén–Lindelöf gives `Im χ ≥ Im z` and, by
   symmetry, `χ(z) = z + c` (`exists_translation`); the far-field expansion then gives equal
   times (`drive_and_time_eq_of_revMap_eq`).
3. (`eqOn_of_fwdMap_rel`) the ODE step: the integral equations force `c ≡ 0`.
-/

noncomputable section

open Set Filter Topology Complex Bornology
open scoped ComplexConjugate

namespace QuantumZipper

namespace ArcDriver

/-! ### Phragmén–Lindelöf: holomorphic self-maps of `ℍ` at bounded distance from the identity -/

theorem norm_exp_I_mul (a : ℂ) : ‖Complex.exp (I * a)‖ = Real.exp (-a.im) := by
  rw [Complex.norm_exp]
  simp

theorem affine_im (w : ℂ) (δ : ℝ) : (I * w + I * δ).im = w.re + δ := by simp

theorem im_le_im_of_bounded {χ : ℂ → ℂ} (hd : DifferentiableOn ℂ χ H) (hmaps : MapsTo χ H H)
    {C : ℝ} (hC : ∀ z ∈ H, ‖χ z - z‖ ≤ C) {z : ℂ} (hz : z ∈ H) : z.im ≤ (χ z).im := by
  have hz' : (0 : ℝ) < z.im := hz
  have key : ∀ δ : ℝ, 0 < δ → δ < z.im → z.im - (χ z).im ≤ δ := by
    intro δ hδ hδz
    set L : ℂ → ℂ := fun w => I * w + I * δ with hL
    have hLH : ∀ w : ℂ, -δ < w.re → L w ∈ H := fun w hw => by
      show (0 : ℝ) < (L w).im
      simp only [hL, affine_im]
      linarith
    set f : ℂ → ℂ := fun w => Complex.exp (I * (χ (L w) - L w)) with hf
    have hnorm : ∀ w, ‖f w‖ = Real.exp ((L w).im - (χ (L w)).im) := fun w => by
      simp only [hf, norm_exp_I_mul, Complex.sub_im, neg_sub]
    have hdL : DifferentiableOn ℂ f {w : ℂ | -δ < w.re} := by
      have h1 : DifferentiableOn ℂ L {w : ℂ | -δ < w.re} :=
        (by fun_prop : Differentiable ℂ L).differentiableOn
      have h2 : DifferentiableOn ℂ (fun w => χ (L w)) {w : ℂ | -δ < w.re} :=
        hd.comp h1 fun w hw => hLH w hw
      exact ((h2.sub h1).const_mul I).cexp
    have hcl : DiffContOnCl ℂ f {w : ℂ | 0 < w.re} := by
      refine DifferentiableOn.diffContOnCl (hdL.mono ?_)
      rw [Complex.closure_setOfPred_lt_re]
      intro w hw
      have : (0 : ℝ) ≤ w.re := hw
      show -δ < w.re
      linarith
    have hbound : ∀ w : ℂ, 0 ≤ w.re → ‖f w‖ ≤ Real.exp C := fun w hw => by
      rw [hnorm]
      apply Real.exp_le_exp.2
      have h := hC (L w) (hLH w (by linarith))
      have : (L w).im - (χ (L w)).im = -(χ (L w) - L w).im := by simp
      rw [this]
      exact (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans h)
    have hexp : ∃ c < (2 : ℝ), ∃ B,
        f =O[cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}] fun z => Real.exp (B * ‖z‖ ^ c) := by
      refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (Real.exp C) ?_⟩
      refine Filter.eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
      simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
      exact hbound w (le_of_lt hw)
    have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖ :=
      ⟨Real.exp C, Filter.eventually_map.2 ((eventually_ge_atTop (0 : ℝ)).mono
        fun x hx => hbound x (by simpa using hx))⟩
    have him : ∀ x : ℝ, ‖f (x * I)‖ ≤ Real.exp δ := fun x => by
      rw [hnorm]
      apply Real.exp_le_exp.2
      have hLx : (L (x * I)).im = δ := by simp [hL]
      have hpos : (0 : ℝ) < (χ (L (x * I))).im := hmaps (hLH _ (by simp; linarith))
      linarith
    set w₀ : ℂ := -I * (z - I * δ) with hw₀def
    have hw₀re : w₀.re = z.im - δ := by simp [hw₀def]
    have hw₀ : 0 ≤ w₀.re := by rw [hw₀re]; linarith
    have hLw₀ : L w₀ = z := by
      simp only [hL, hw₀def]
      linear_combination (I * δ - z) * Complex.I_sq
    have := PhragmenLindelof.right_half_plane_of_bounded_on_real hcl hexp hre him hw₀
    rw [hnorm, hLw₀] at this
    exact Real.exp_le_exp.1 this
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h := key (min ε (z.im / 2)) (lt_min hε (by linarith))
    (by have := min_le_right ε (z.im / 2); linarith)
  have := min_le_left ε (z.im / 2)
  linarith

theorem mem_H_I : I ∈ H := by
  show (0 : ℝ) < I.im
  simp

theorem exists_const_of_im_eq_zero {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h H)
    (him : ∀ z ∈ H, (h z).im = 0) : ∃ c : ℝ, ∀ z ∈ H, h z = c := by
  have hopen : IsOpen H := WeldingUniqueness.wu_isOpen_H
  have hderiv : EqOn (deriv h) 0 H := by
    intro z hz
    have hdz : HasDerivAt h (deriv h z) z := (hd.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hloc : ∀ v : ℂ, (fun t : ℝ => (h (z + t * v)).im) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      intro v
      have hc : Continuous fun t : ℝ => z + t * v := by fun_prop
      have hH : H ∈ 𝓝 (z + ((0 : ℝ) : ℂ) * v) := by simpa using hopen.mem_nhds hz
      have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), z + (t : ℂ) * v ∈ H :=
        hc.continuousAt.preimage_mem_nhds hH
      filter_upwards [hmem] with t ht using him _ ht
    have hder : ∀ v : ℂ, HasDerivAt (fun t : ℝ => (h (z + t * v)).im) (deriv h z * v).im 0 := by
      intro v
      have h1 : HasDerivAt (fun t : ℝ => z + t * v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v).const_add z
      have h0 : HasDerivAt h (deriv h z) (z + ((0 : ℝ) : ℂ) * v) := by simpa using hdz
      have h2 : HasDerivAt (fun t : ℝ => h (z + t * v)) (deriv h z * v) 0 := h0.comp (0 : ℝ) h1
      have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      exact h3
    have hzero : ∀ v : ℂ, (deriv h z * v).im = 0 := fun v =>
      (hder v).unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq (hloc v))
    have e1 := hzero 1
    have e2 := hzero I
    simp only [mul_one, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, add_zero] at e1 e2
    apply Complex.ext <;> simp [e1, e2]
  obtain ⟨a, ha⟩ := hopen.exists_is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
    hd hderiv
  have ha0 : a.im = 0 := by rw [← ha I mem_H_I]; exact him I mem_H_I
  exact ⟨a.re, fun z hz => by rw [ha z hz]; exact Complex.ext (by simp) (by simp [ha0])⟩

/-- A holomorphic self-map of `ℍ` at bounded distance from the identity, with a left inverse of
the same kind, is a real translation. -/
theorem exists_translation {χ χ' : ℂ → ℂ} (hd : DifferentiableOn ℂ χ H)
    (hd' : DifferentiableOn ℂ χ' H) (hm : MapsTo χ H H) (hm' : MapsTo χ' H H) {C C' : ℝ}
    (hC : ∀ z ∈ H, ‖χ z - z‖ ≤ C) (hC' : ∀ z ∈ H, ‖χ' z - z‖ ≤ C')
    (hinv : ∀ z ∈ H, χ' (χ z) = z) : ∃ c : ℝ, ∀ z ∈ H, χ z = z + c := by
  have him : ∀ z ∈ H, (χ z - z).im = 0 := fun z hz => by
    have h1 := im_le_im_of_bounded hd hm hC hz
    have h2 := im_le_im_of_bounded hd' hm' hC' (hm hz)
    rw [hinv z hz] at h2
    simp only [Complex.sub_im]
    linarith
  obtain ⟨c, hc⟩ := exists_const_of_im_eq_zero (h := fun z => χ z - z)
    (hd.sub differentiableOn_id) him
  exact ⟨c, fun z hz => by linear_combination hc z hz⟩

/-! ### Time reversal on `[0,a]` -/

/-- The time reversal of `A` on `[0,a]`: `r ↦ A(a - r) - A(a)`. -/
def trev (A : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := fun r => A (a - r) - A a

theorem continuous_trev {A : ℝ → ℝ} (hA : Continuous A) (a : ℝ) : Continuous (trev A a) := by
  unfold trev
  fun_prop

theorem trev_zero (A : ℝ → ℝ) (a : ℝ) : trev A a 0 = 0 := by simp [trev]

theorem trev_trev {A : ℝ → ℝ} (hA0 : A 0 = 0) (a : ℝ) :
    (fun s => trev A a (a - s) - trev A a a) = A := by
  funext s
  simp only [trev, sub_sub_cancel, sub_self, hA0]
  ring

section Trev

variable {A : ℝ → ℝ} (hA : Continuous A) (hA0 : A 0 = 0) {a : ℝ} (ha : 0 < a)
include hA hA0 ha

theorem revHull_trev : revHull (trev A a) a = fwdHull A a := by
  rw [LoewnerAlgebra.revHull_eq_fwdHull_timeRev _ (continuous_trev hA a) (trev_zero A a) ha,
    trev_trev hA0]

theorem revMap_trev_spec {z : ℂ} (hz : z ∈ H) :
    revMap (trev A a) a z ∈ H \ fwdHull A a ∧ fwdMap A a (revMap (trev A a) a z) = z := by
  have h := LoewnerAlgebra.fwdMap_revMap_timeRev (trev A a) (continuous_trev hA a)
    (trev_zero A a) ha hz
  rw [trev_trev hA0] at h
  exact ⟨⟨lt_of_lt_of_le hz (im_le_im_revMap _ (continuous_trev hA a) z hz ha.le), h.1⟩, h.2⟩

theorem fwdMap_trev_spec {w : ℂ} (hw : w ∈ H \ fwdHull A a) :
    fwdMap A a w ∈ H ∧ revMap (trev A a) a (fwdMap A a w) = w := by
  have hwim : w ∈ revMap (trev A a) a '' H := by
    by_contra hcon
    apply hw.2
    rw [← revHull_trev hA hA0 ha]
    exact ⟨hw.1, hcon⟩
  obtain ⟨z, hz, rfl⟩ := hwim
  rw [(revMap_trev_spec hA hA0 ha hz).2]
  exact ⟨hz, rfl⟩

theorem exists_bound_revMap_trev (hCar : Blueprint.RevMapCaratheodory)
    (hK : IsSimpleCurveHull (fwdHull A a)) :
    ∃ C : ℝ, ∀ z ∈ H, ‖revMap (trev A a) a z - z‖ ≤ C := by
  rw [← revHull_trev hA hA0 ha] at hK
  obtain ⟨F, hF⟩ := hCar _ (continuous_trev hA a) (trev_zero A a) a ha hK
  obtain ⟨C, hC⟩ := (WeldingUniqueness.glueData_of_caratheodory (continuous_trev hA a) ha hF).bound
  exact ⟨C, fun z hz => by rw [← hF.1 hz]; exact hC z (WeldingUniqueness.wu_H_subset_Hbar hz)⟩

end Trev

theorem revMap_add_ofReal {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : 0 < z.im) (c : ℝ) : revMap W T (z + c) = revMap (fun r => W r - c) T z := by
  have hzc : 0 < (z + c).im := by simpa using hz
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW (z + c) hzc T hT
  have hu' : IsReverseSol (fun r => W r - c) z T u :=
    ⟨hu.1, fun t ht => ⟨(hu.2 t ht).1, by
      rw [(hu.2 t ht).2]
      simp only [Complex.ofReal_sub]
      ring⟩⟩
  rw [revMap_eq W hW _ hT le_rfl hu, revMap_eq (fun r => W r - c) (hW.sub continuous_const) z hT le_rfl hu']

/-! ### Step 2: equal simple forward hulls -/

/-- **Equal simple forward hulls** give equal times, and the centred forward maps differ by the
difference of the terminal driver values. -/
theorem fwdHull_eq_imp (hCar : Blueprint.RevMapCaratheodory) {A A' : ℝ → ℝ} (hA : Continuous A)
    (hA' : Continuous A') (hA0 : A 0 = 0) (hA'0 : A' 0 = 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hK : IsSimpleCurveHull (fwdHull A a)) (heq : fwdHull A' b = fwdHull A a) :
    a = b ∧ ∀ w ∈ H \ fwdHull A a, fwdMap A' b w + A' b = fwdMap A a w + A a := by
  have hK' : IsSimpleCurveHull (fwdHull A' b) := heq ▸ hK
  obtain ⟨C, hC⟩ := exists_bound_revMap_trev hA hA0 ha hCar hK
  obtain ⟨C', hC'⟩ := exists_bound_revMap_trev hA' hA'0 hb hCar hK'
  set g := revMap (trev A a) a with hg
  set g' := revMap (trev A' b) b with hg'
  have hgs := fun {z : ℂ} (hz : z ∈ H) => revMap_trev_spec hA hA0 ha hz
  have hgs' := fun {z : ℂ} (hz : z ∈ H) => revMap_trev_spec hA' hA'0 hb hz
  have hfs := fun {w : ℂ} (hw : w ∈ H \ fwdHull A a) => fwdMap_trev_spec hA hA0 ha hw
  have hfs' := fun {w : ℂ} (hw : w ∈ H \ fwdHull A' b) => fwdMap_trev_spec hA' hA'0 hb hw
  set χ : ℂ → ℂ := fun z => fwdMap A a (g' z) with hχ
  set χ' : ℂ → ℂ := fun z => fwdMap A' b (g z) with hχ'
  have hg'K : ∀ {z}, z ∈ H → g' z ∈ H \ fwdHull A a := fun hz => heq ▸ (hgs' hz).1
  have hgK' : ∀ {z}, z ∈ H → g z ∈ H \ fwdHull A' b := fun hz => heq.symm ▸ (hgs hz).1
  have hd : DifferentiableOn ℂ χ H :=
    (FwdHolo.differentiableOn_fwdMap hA ha.le).comp
      (differentiableOn_revMap _ (continuous_trev hA' b) hb.le) fun z hz => hg'K hz
  have hd' : DifferentiableOn ℂ χ' H :=
    (FwdHolo.differentiableOn_fwdMap hA' hb.le).comp
      (differentiableOn_revMap _ (continuous_trev hA a) ha.le) fun z hz => hgK' hz
  have hm : MapsTo χ H H := fun z hz => (hfs (hg'K hz)).1
  have hm' : MapsTo χ' H H := fun z hz => (hfs' (hgK' hz)).1
  have hbd : ∀ z ∈ H, ‖χ z - z‖ ≤ C + C' := fun z hz => by
    obtain ⟨hy, hgy⟩ := hfs (hg'K hz)
    have e : χ z - z = -(g (χ z) - χ z) + (g' z - z) := by
      rw [show g (χ z) = g' z from hgy]
      ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (by rw [norm_neg]; exact hC _ hy) (hC' z hz))
  have hbd' : ∀ z ∈ H, ‖χ' z - z‖ ≤ C' + C := fun z hz => by
    obtain ⟨hy, hgy⟩ := hfs' (hgK' hz)
    have e : χ' z - z = -(g' (χ' z) - χ' z) + (g z - z) := by
      rw [show g' (χ' z) = g z from hgy]
      ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (by rw [norm_neg]; exact hC' _ hy) (hC z hz))
  have hinv : ∀ z ∈ H, χ' (χ z) = z := fun z hz => by
    show fwdMap A' b (g (fwdMap A a (g' z))) = z
    rw [show g (fwdMap A a (g' z)) = g' z from (hfs (hg'K hz)).2]
    exact (hgs' hz).2
  obtain ⟨c, hc⟩ := exists_translation hd hd' hm hm' hbd hbd' hinv
  -- `g' z = g (z + c)`
  have hgg : ∀ z ∈ H, g' z = g (z + c) := fun z hz => by
    rw [← hc z hz]
    exact ((hfs (hg'K hz)).2).symm
  have hrev : EqOn (revMap (trev A' b) b) (revMap (fun r => trev A a r - c) a) H := fun z hz => by
    show g' z = _
    rw [hgg z hz, hg, revMap_add_ofReal (continuous_trev hA a) ha.le hz]
  obtain ⟨h1, h2⟩ := WeldingUniqueness.drive_and_time_eq_of_revMap_eq
    ((continuous_trev hA a).sub continuous_const) (continuous_trev hA' b) ha.le hb.le hrev
  subst h2
  simp only [trev, Pi.sub_apply, sub_self, hA0, hA'0] at h1
  have hc' : ((A' a : ℝ) : ℂ) = (A a : ℂ) + c := by
    exact_mod_cast (by linarith : A' a = A a + c)
  refine ⟨rfl, fun w hw => ?_⟩
  have hw' : w ∈ H \ fwdHull A' a := heq.symm ▸ hw
  obtain ⟨hz, hgz⟩ := hfs' hw'
  have := hc _ hz
  simp only [hχ] at this
  rw [show g' (fwdMap A' a w) = w from hgz] at this
  rw [this, hc']
  ring

/-! ### Step 1: reparametrization of simple chords -/

theorem exists_reparam {η η' : ℝ → ℂ} (hη : IsSimpleChord η) (hη' : IsSimpleChord η') {T : ℝ}
    (hT : 0 < T) (heq : η' '' Ioc 0 T = η '' Ioc 0 T) {s : ℝ} (hs : s ∈ Ioc 0 T) :
    ∃ t ∈ Ioc 0 T, η' '' Ioc 0 s = η '' Ioc 0 t := by
  obtain ⟨h0, hc, hinj, -, -⟩ := hη
  obtain ⟨h0', hc', hinj', -, -⟩ := hη'
  have hIcc : η' '' Icc 0 T = η '' Icc 0 T := by
    rw [← Ioc_insert_left hT.le, image_insert_eq, image_insert_eq, heq, h0, h0']
  -- the embedding of `[0,T]` by `η`
  let e : Icc (0 : ℝ) T → ℂ := fun x => η x
  have hec : Continuous e := (hc.mono Icc_subset_Ici_self).restrict
  have hei : Function.Injective e := fun x y hxy =>
    Subtype.ext (hinj (Icc_subset_Ici_self x.2) (Icc_subset_Ici_self y.2) hxy)
  have hemb := hec.isClosedEmbedding hei
  have hpre : ∀ x : Icc (0 : ℝ) T, ∃ y : Icc (0 : ℝ) T, e y = η' x := fun x => by
    have : η' x ∈ η '' Icc 0 T := hIcc ▸ mem_image_of_mem η' x.2
    obtain ⟨y, hy, hye⟩ := this
    exact ⟨⟨y, hy⟩, hye⟩
  choose σ hσ using hpre
  have hσc : Continuous σ := by
    rw [hemb.isInducing.continuous_iff]
    have : e ∘ σ = fun x : Icc (0 : ℝ) T => η' x := funext hσ
    rw [this]
    exact (hc'.mono Icc_subset_Ici_self).restrict
  have hσi : Function.Injective σ := fun x y hxy => Subtype.ext
    (hinj' (Icc_subset_Ici_self x.2) (Icc_subset_Ici_self y.2) (by rw [← hσ, ← hσ, hxy]))
  let σr : ℝ → ℝ := fun x => σ (projIcc 0 T hT.le x)
  have hσr_eq : ∀ x ∈ Icc (0 : ℝ) T, η' x = η (σr x) := fun x hx => by
    simp only [σr, projIcc_of_mem hT.le hx]
    exact (hσ ⟨x, hx⟩).symm
  have hσr0 : σr 0 = 0 := by
    have h := hσr_eq 0 ⟨le_rfl, hT.le⟩
    rw [h0', ← h0] at h
    exact (hinj (mem_Ici.2 le_rfl) (mem_Ici.2 (σ _).2.1) h).symm
  have hσrc : ContinuousOn σr (Icc 0 T) :=
    (continuous_subtype_val.comp (hσc.comp continuous_projIcc)).continuousOn
  have hσri : InjOn σr (Icc 0 T) := fun x hx y hy hxy => by
    have := congrArg Subtype.val (hσi (Subtype.ext hxy : σ (projIcc 0 T hT.le x) = _))
    simpa [projIcc_of_mem hT.le hx, projIcc_of_mem hT.le hy] using this
  have hσr_mem : ∀ x, σr x ∈ Icc (0 : ℝ) T := fun x => (σ _).2
  have hmono : StrictMonoOn σr (Icc 0 T) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc hT.le (by rw [hσr0]; exact (hσr_mem T).1) hσrc hσri
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hts : 0 < σr s := hσr0 ▸ hmono ⟨le_rfl, hT.le⟩ hsI hs.1
  refine ⟨σr s, ⟨hts, (hσr_mem s).2⟩, ?_⟩
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxI : x ∈ Icc (0 : ℝ) T := ⟨hx.1.le, hx.2.trans hs.2⟩
    refine ⟨σr x, ⟨?_, ?_⟩, (hσr_eq x hxI).symm⟩
    · exact hσr0 ▸ hmono ⟨le_rfl, hT.le⟩ hxI hx.1
    · exact hmono.monotoneOn hxI hsI hx.2
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hs.1.le (hσrc.mono (Icc_subset_Icc_right hs.2))
      (show y ∈ Icc (σr 0) (σr s) from ⟨hσr0.symm ▸ hy.1.le, hy.2⟩)
    have hx0 : x ≠ 0 := fun h => by rw [h, hσr0] at hxy; exact hy.1.ne' hxy.symm
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩, ?_⟩
    rw [hσr_eq x ⟨hx.1, hx.2.trans hs.2⟩, hxy]

/-! ### Step 3: the ODE step -/

theorem exists_mem_compl_fwdHull {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {T : ℝ}
    (hT : 0 < T) : ∃ w, w ∈ H \ fwdHull V T :=
  ⟨_, (revMap_trev_spec hV hV0 hT mem_H_I).1⟩

theorem eqOn_of_fwdMap_rel {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V')
    (hV0 : V 0 = 0) (hV'0 : V' 0 = 0) {T : ℝ} (hT : 0 < T)
    (hsame : fwdHull V' T = fwdHull V T)
    (hrel : ∀ s ∈ Ioc 0 T, ∀ w ∈ H \ fwdHull V s, fwdMap V' s w + V' s = fwdMap V s w + V s) :
    EqOn V V' (Icc 0 T) := by
  obtain ⟨w, hwH, hwK⟩ := exists_mem_compl_fwdHull hV hV0 hT
  have hwK' : w ∉ fwdHull V' T := hsame ▸ hwK
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT.le hwH hwK
  obtain ⟨u', hu'⟩ := exists_isForwardSol_of_not_mem_fwdHull hT.le hwH hwK'
  have hwim : 0 < w.im := hwH
  -- the relation along the solutions
  have hd : ∀ s ∈ Icc (0 : ℝ) T, u' s + V' s = u s + V s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h
      rw [(hu.2 0 hs).2, (hu'.2 0 hs).2, hV0, hV'0]
      simp
    · have hws : w ∈ H \ fwdHull V s := ⟨hwH, fun h' => hwK ((fwdHull_mono.1 hs.2) h')⟩
      rw [← fwdMap_eq hV hwim hu hs, ← fwdMap_eq hV' hwim hu' hs]
      exact hrel s ⟨h, hs.2⟩ w hws
  set k : ℝ → ℂ := fun r => 2 / u' r - 2 / u r with hk
  have hkc : ContinuousOn k (Icc 0 T) :=
    (continuousOn_const.div hu'.1 fun r hr => (hu'.2 r hr).1).sub
      (continuousOn_const.div hu.1 fun r hr => (hu.2 r hr).1)
  have hint : ∀ s ∈ Icc (0 : ℝ) T, ∫ r in (0 : ℝ)..s, k r = 0 := by
    intro s hs
    have hsub : Icc (0 : ℝ) s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
    have i1 : IntervalIntegrable (fun r => 2 / u' r) MeasureTheory.volume 0 s :=
      ((continuousOn_const.div hu'.1 fun r hr => (hu'.2 r hr).1).mono hsub).intervalIntegrable_of_Icc
        hs.1
    have i2 : IntervalIntegrable (fun r => 2 / u r) MeasureTheory.volume 0 s :=
      ((continuousOn_const.div hu.1 fun r hr => (hu.2 r hr).1).mono hsub).intervalIntegrable_of_Icc
        hs.1
    rw [hk, intervalIntegral.integral_sub i1 i2]
    have e := hd s hs
    rw [(hu.2 s hs).2, (hu'.2 s hs).2] at e
    linear_combination e
  have hk0 : ∀ s ∈ Ioo (0 : ℝ) T, k s = 0 := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
    have hcont : ContinuousAt k s := hkc.continuousAt (Icc_mem_nhds hs.1 hs.2)
    have hF := intervalIntegral.integral_hasDerivAt_right
      ((hkc.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hkc.mono Ioo_subset_Icc_self) s hs)
      hcont
    have hF0 : HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, k r) 0 s := by
      refine (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
      exact hint x (Ioo_subset_Icc_self hx)
    exact hF.unique hF0
  have hEq : EqOn V V' (Ioo 0 T) := by
    intro s hs
    have h1 := hk0 s hs
    have hsI : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
    have hu0 := (hu.2 s hsI).1
    have hu'0 := (hu'.2 s hsI).1
    simp only [hk, sub_eq_zero] at h1
    have huu : u' s = u s := by
      field_simp at h1
      exact h1.symm
    have e := hd s hsI
    rw [huu] at e
    exact_mod_cast (add_left_cancel e).symm
  refine hEq.of_subset_closure hV.continuousOn hV'.continuousOn Ioo_subset_Icc_self ?_
  rw [closure_Ioo hT.ne]

/-! ### The main theorem -/

/-- The forward hulls of the time-reversed increment on `[0,T]` are initial arcs of one simple
chord. -/
def HasChordHulls (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ η : ℝ → ℂ, IsSimpleChord η ∧
    ∀ s ∈ Icc (0 : ℝ) T, fwdHull (fun r => W (T - r) - W T) s = η '' Ioc 0 s

/-- **A simple arc determines its driver.** -/
theorem eqOn_of_revMap_eq (hCar : Blueprint.RevMapCaratheodory) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T : ℝ}
    (hT : 0 < T) (hc : HasChordHulls W T) (hc' : HasChordHulls W' T)
    (h : EqOn (revMap W' T) (revMap W T) H) : EqOn W W' (Icc 0 T) := by
  obtain ⟨η, hη, hhull⟩ := hc
  obtain ⟨η', hη', hhull'⟩ := hc'
  set V : ℝ → ℝ := fun r => W (T - r) - W T with hVdef
  set V' : ℝ → ℝ := fun r => W' (T - r) - W' T with hV'def
  have hV : Continuous V := by fun_prop
  have hV' : Continuous V' := by fun_prop
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hV'0 : V' 0 = 0 := by simp [hV'def]
  have hTI : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hrevHull : revHull W' T = revHull W T := by unfold revHull; rw [h.image_eq]
  have hfin : fwdHull V' T = fwdHull V T := by
    rw [← LoewnerAlgebra.revHull_eq_fwdHull_timeRev W hW hW0 hT,
      ← LoewnerAlgebra.revHull_eq_fwdHull_timeRev W' hW' hW'0 hT, hrevHull]
  have hfinη : η' '' Ioc 0 T = η '' Ioc 0 T := by rw [← hhull T hTI, ← hhull' T hTI, hfin]
  have hrel : ∀ s ∈ Ioc 0 T, ∀ w ∈ H \ fwdHull V s,
      fwdMap V' s w + V' s = fwdMap V s w + V s := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := exists_reparam hη hη' hT hfinη hs
    have hKt : fwdHull V' s = fwdHull V t := by
      rw [hhull' s ⟨hs.1.le, hs.2⟩, hhull t ⟨ht.1.le, ht.2⟩, hst]
    have hsimple : IsSimpleCurveHull (fwdHull V t) := by
      rw [hhull t ⟨ht.1.le, ht.2⟩]
      exact Thm14FromThm13.isSimpleCurveHull_image_Ioc hη ht.1
    obtain ⟨hts, hmap⟩ := fwdHull_eq_imp hCar hV hV' hV0 hV'0 ht.1 hs.1 hsimple hKt
    subst hts
    exact hmap
  have hVV := eqOn_of_fwdMap_rel hV hV' hV0 hV'0 hT hfin hrel
  have hWT : W T = W' T := by
    have := hVV ⟨hT.le, le_rfl⟩
    simp only [hVdef, hV'def, sub_self, hW0, hW'0] at this
    linarith
  intro r hr
  have := hVV ⟨sub_nonneg.2 hr.2, by linarith [hr.1]⟩
  simp only [hVdef, hV'def, sub_sub_cancel] at this
  linarith

end ArcDriver

end QuantumZipper
