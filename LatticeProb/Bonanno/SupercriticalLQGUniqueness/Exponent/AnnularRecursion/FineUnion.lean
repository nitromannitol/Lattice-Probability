/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.FineUnion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Cover




 













set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Convex

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.LFPP

 
def aQ (m : ℕ) : ℚ := ((2 : ℚ) ^ m)⁻¹

theorem aQ_cast (m : ℕ) : ((aQ m : ℚ) : ℝ) = ((2 : ℝ) ^ m)⁻¹ := by
  unfold aQ; push_cast; rfl

theorem aQ_pos (m : ℕ) : 0 < aQ m := by unfold aQ; positivity

theorem aQ_le (m : ℕ) (hm : 8 ≤ m) : ((aQ m : ℚ) : ℝ) ≤ 1 / 256 := by
  rw [aQ_cast, one_div]
  exact inv_anti₀ (by norm_num) (by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm)

 
def cornerQ (m : ℕ) (ij : ℤ × ℤ) : ℚ × ℚ := ((ij.1 : ℚ) * aQ m, (ij.2 : ℚ) * aQ m)

 
def tileMap (m : ℕ) (ij : ℤ × ℤ) (z : ℂ) : ℂ :=
  (((aQ m : ℚ) : ℝ) : ℂ) * z + ratC (cornerQ m ij)

theorem ratC_re (v : ℚ × ℚ) : (ratC v).re = v.1 := by simp [ratC]

theorem ratC_im (v : ℚ × ℚ) : (ratC v).im = v.2 := by simp [ratC]

theorem cornerQ_fst (m : ℕ) (ij : ℤ × ℤ) :
    (((cornerQ m ij).1 : ℚ) : ℝ) = (ij.1 : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
  simp only [cornerQ]; push_cast; rw [aQ_cast]

theorem cornerQ_snd (m : ℕ) (ij : ℤ × ℤ) :
    (((cornerQ m ij).2 : ℚ) : ℝ) = (ij.2 : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
  simp only [cornerQ]; push_cast; rw [aQ_cast]

theorem tileMap_re (m : ℕ) (ij : ℤ × ℤ) (z : ℂ) :
    (tileMap m ij z).re = ((2 : ℝ) ^ m)⁻¹ * z.re + (ij.1 : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
  rw [tileMap, Complex.add_re, Complex.re_ofReal_mul, aQ_cast, ratC_re, cornerQ_fst]

theorem tileMap_im (m : ℕ) (ij : ℤ × ℤ) (z : ℂ) :
    (tileMap m ij z).im = ((2 : ℝ) ^ m)⁻¹ * z.im + (ij.2 : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
  rw [tileMap, Complex.add_im, Complex.im_ofReal_mul, aQ_cast, ratC_im, cornerQ_snd]

 
def tileInv (m : ℕ) (ij : ℤ × ℤ) (z : ℂ) : ℂ :=
  ⟨(2 : ℝ) ^ m * z.re - ij.1, (2 : ℝ) ^ m * z.im - ij.2⟩

theorem tileMap_tileInv (m : ℕ) (ij : ℤ × ℤ) (z : ℂ) : tileMap m ij (tileInv m ij z) = z := by
  have hp : (2 : ℝ) ^ m ≠ 0 := by positivity
  apply Complex.ext
  · rw [tileMap_re]; simp only [tileInv]; field_simp; ring
  · rw [tileMap_im]; simp only [tileInv]; field_simp; ring

theorem tile_subset_tileMap_image (m : ℕ) (ij : ℤ × ℤ) :
    tile (((2 : ℝ) ^ m)⁻¹) ij ⊆ tileMap m ij '' Exponent.PaidDuality.innerSquare := by
  rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hpi : (2 : ℝ) ^ m * ((2 : ℝ) ^ m)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  refine ⟨tileInv m ij z, ?_, tileMap_tileInv m ij z⟩
  simp only [Exponent.PaidDuality.innerSquare, Complex.mem_reProdIm, mem_Icc, tileInv]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := mul_le_mul_of_nonneg_left h1 hp.le
    rw [show (2 : ℝ) ^ m * ((ij.1 : ℝ) * ((2 : ℝ) ^ m)⁻¹) = ij.1 by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]] at this
    linarith
  · have := mul_le_mul_of_nonneg_left h2 hp.le
    rw [show (2 : ℝ) ^ m * (((ij.1 : ℝ) + 1) * ((2 : ℝ) ^ m)⁻¹) = ij.1 + 1 by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]] at this
    linarith
  · have := mul_le_mul_of_nonneg_left h3 hp.le
    rw [show (2 : ℝ) ^ m * ((ij.2 : ℝ) * ((2 : ℝ) ^ m)⁻¹) = ij.2 by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]] at this
    linarith
  · have := mul_le_mul_of_nonneg_left h4 hp.le
    rw [show (2 : ℝ) ^ m * (((ij.2 : ℝ) + 1) * ((2 : ℝ) ^ m)⁻¹) = ij.2 + 1 by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]] at this
    linarith

theorem tileMap_image_outer_subset (m : ℕ) (ij : ℤ × ℤ) :
    tileMap m ij '' Exponent.PaidDuality.outerOpenSquare ⊆ block (((2 : ℝ) ^ m)⁻¹) ij := by
  rintro _ ⟨z, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
  have ha : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
  rw [mem_block_iff, tileMap_re, tileMap_im]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem mem_tileMap_image_compl (m : ℕ) (ij : ℤ × ℤ) {x : ℂ}
    (hx : x ∉ block (((2 : ℝ) ^ m)⁻¹) ij) :
    x ∈ tileMap m ij '' Exponent.PaidDuality.outerOpenSquareᶜ := by
  refine ⟨tileInv m ij x, fun hO => hx ?_, tileMap_tileInv m ij x⟩
  have := tileMap_image_outer_subset m ij ⟨_, hO, rfl⟩
  rwa [tileMap_tileInv] at this

theorem famAffine_trace_tile (m : ℕ) (ij : ℤ × ℤ) (H : Exponent.PolygonalCost.RatPolygonFamily) :
    (famAffine (aQ m) (cornerQ m ij) H).trace = tileMap m ij '' H.trace := by
  rw [famAffine_trace]; rfl

theorem famAffine_cost_tile (m : ℕ) (ij : ℤ × ℤ) (H : Exponent.PolygonalCost.RatPolygonFamily) (ξ : ℝ)
    (ψ : ℂ → ℝ) :
    (famAffine (aQ m) (cornerQ m ij) H).cost ξ ψ =
      ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) * H.cost ξ (fun z => ψ (tileMap m ij z)) := by
  rw [famAffine_cost (aQ m) (aQ_pos m)]
  congr 1
  rw [aQ_cast]

 
theorem cost_add_le {F : Exponent.PolygonalCost.RatPolygonFamily} {S : Set ℂ} (hF : F.trace ⊆ S) {ξ : ℝ}
    {φ ψ : ℂ → ℝ} {w : ℝ≥0∞} (hw : ∀ z ∈ S, ENNReal.ofReal (Real.exp (ξ * φ z)) ≤ w)
    (hwt : w ≠ ⊤) :
    F.cost ξ (fun z => φ z + ψ z) ≤ w * F.cost ξ ψ := by
  simp only [Exponent.PolygonalCost.RatPolygonFamily.cost, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ hwt]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  have hz : (F.paths i).path t ∈ S := hF (path_subset_trace F i ⟨t, ht, rfl⟩)
  rw [mul_add, Real.exp_add, mul_assoc, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (hw _ hz) bot_le

 
theorem fine_union_family (m : ℕ) (L : Finset (ℤ × ℤ))
    (hL : LQGMetric.Disconnects (⋃ ij ∈ L, tile (((2 : ℝ) ^ m)⁻¹) ij)
      Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ)
    (hLA : ∀ ij ∈ L, block (((2 : ℝ) ^ m)⁻¹) ij ⊆ Exponent.PolygonalCost.openSquareAnnulus)
    (H : ℤ × ℤ → Exponent.PolygonalCost.RatPolygonFamily) (hH : ∀ ij ∈ L, (H ij).Admitted) :
    ∃ H' : Exponent.PolygonalCost.RatPolygonFamily, H'.Admitted ∧
      ∀ (ξ : ℝ) (f : ℂ → ℝ), H'.cost ξ f =
        ∑ ij ∈ L, (famAffine (aQ m) (cornerQ m ij) (H ij)).cost ξ f := by
  obtain ⟨H', htr, hc⟩ := exists_famUnion L (nonempty_of_disconnects hL)
    fun ij => famAffine (aQ m) (cornerQ m ij) (H ij)
  refine ⟨H', ⟨?_, ?_⟩, hc⟩
  · rw [htr]
    intro z hz
    obtain ⟨ij, hij, hz⟩ := mem_iUnion₂.1 hz
    rw [famAffine_trace_tile] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hu' : u ∈ Exponent.PaidDuality.outerOpenSquare := ((hH ij hij).1 hu).1
    exact hLA ij hij (tileMap_image_outer_subset m ij ⟨u, hu', rfl⟩)
  · intro x y γ hx hy
    obtain ⟨z, ⟨t, rfl⟩, hz⟩ := hL x y γ hx hy
    obtain ⟨ij, hij, hzt⟩ := mem_iUnion₂.1 hz
    have hP : IsPathConnected (⇑γ.extend '' Icc (0 : ℝ) t.1) :=
      ((convex_Icc 0 t.1).isPathConnected (nonempty_Icc.2 t.2.1)).image γ.extend.continuous
    have hj' : JoinedIn (⇑γ.extend '' Icc (0 : ℝ) t.1) (γ t) x := by
      have h1 : γ t ∈ ⇑γ.extend '' Icc (0 : ℝ) t.1 :=
        ⟨t.1, ⟨t.2.1, le_rfl⟩, Path.extend_extends' γ t⟩
      have h2 : x ∈ ⇑γ.extend '' Icc (0 : ℝ) t.1 := ⟨0, ⟨le_rfl, t.2.1⟩, γ.extend_zero⟩
      exact hP.joinedIn _ h1 _ h2
    have hj : JoinedIn (range γ) (γ t) x := by
      refine hj'.mono ?_
      rintro _ ⟨s, -, rfl⟩
      rw [← γ.extend_range]
      exact mem_range_self s
    have hxB : x ∉ block (((2 : ℝ) ^ m)⁻¹) ij := fun hxB =>
      openSquareAnnulus_disjoint_inner.le_bot ⟨hLA ij hij hxB, hx⟩
    have hsep := disconnects_affine (((aQ m : ℚ) : ℝ) : ℂ) (ratC (cornerQ m ij))
      (by exact_mod_cast (aQ_pos m).ne') (hH ij hij).2
    obtain ⟨w, ⟨s, rfl⟩, hw⟩ := hsep (γ t) x hj.somePath
      (tile_subset_tileMap_image m ij hzt) (mem_tileMap_image_compl m ij hxB)
    refine ⟨hj.somePath s, hj.somePath_mem s, ?_⟩
    rw [htr]
    refine mem_iUnion₂.2 ⟨ij, hij, ?_⟩
    rw [famAffine_trace_tile]
    exact hw

theorem lt_top_of_mul_lt_top_right' {a b : ℝ≥0∞} (h : a * b < ⊤) (ha : a ≠ 0) : b < ⊤ := by
  by_contra hb
  rw [not_lt, top_le_iff] at hb
  rw [hb, ENNReal.mul_top ha] at h
  exact lt_irrefl _ h

 
theorem fine_union_le (m : ℕ) (L : Finset (ℤ × ℤ))
    (hL : LQGMetric.Disconnects (⋃ ij ∈ L, tile (((2 : ℝ) ^ m)⁻¹) ij)
      Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ)
    (hLA : ∀ ij ∈ L, block (((2 : ℝ) ^ m)⁻¹) ij ⊆ Exponent.PolygonalCost.openSquareAnnulus)
    (ξ : ℝ) (φ ψ : ℂ → ℝ) (w : ℤ × ℤ → ℝ≥0∞)
    (hw : ∀ ij ∈ L, ∀ z ∈ block (((2 : ℝ) ^ m)⁻¹) ij,
      ENNReal.ofReal (Real.exp (ξ * φ z)) ≤ w ij)
    (hwt : ∀ ij ∈ L, w ij ≠ ⊤) :
    Exponent.PolygonalCost.polyAnnularCost ξ (fun z => φ z + ψ z) ≤
      ∑ ij ∈ L, w ij * ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) *
        Exponent.PolygonalCost.polyAnnularCost ξ (fun z => ψ (tileMap m ij z)) := by
  classical
  set a : ℝ := ((2 : ℝ) ^ m)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  set U : ℤ × ℤ → ℝ≥0∞ := fun ij => Exponent.PolygonalCost.polyAnnularCost ξ (fun z => ψ (tileMap m ij z))
  have hwpos : ∀ ij ∈ L, w ij ≠ 0 := by
    intro ij hij h0
    have hc : corner a ij ∈ block a ij := tile_subset_block ha.le ij
      (show corner a ij ∈ tile a ij by
        refine ⟨⟨le_rfl, ?_⟩, ⟨le_rfl, ?_⟩⟩ <;> simp only [corner] <;> nlinarith)
    have := hw ij hij _ hc
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
    exact (not_le.2 (Real.exp_pos _)) this
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hRHS => ?_
  have hUfin : ∀ ij ∈ L, U ij < ⊤ := by
    intro ij hij
    have hterm : w ij * ENNReal.ofReal a * U ij < ⊤ :=
      lt_of_le_of_lt (Finset.single_le_sum (f := fun ij => w ij * ENNReal.ofReal a * U ij)
        (fun _ _ => bot_le) hij) hRHS
    exact lt_top_of_mul_lt_top_right' hterm
      (mul_ne_zero (hwpos ij hij) (ENNReal.ofReal_pos.2 ha).ne')
  set C : ℝ≥0∞ := ∑ ij ∈ L, w ij * ENNReal.ofReal a
  have hC : C ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun ij hij => ENNReal.mul_ne_top (hwt ij hij) ENNReal.ofReal_ne_top
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / (C + 1)
  have hδ0 : δ ≠ 0 := ENNReal.div_ne_zero.2 ⟨by exact_mod_cast hε.ne', ENNReal.add_ne_top.2 ⟨hC, ENNReal.one_ne_top⟩⟩
  have hsel : ∀ ij : ℤ × ℤ, ∃ H : Exponent.PolygonalCost.RatPolygonFamily, ij ∈ L →
      H.Admitted ∧ H.cost ξ (fun z => ψ (tileMap m ij z)) ≤ U ij + δ := by
    intro ij
    by_cases hij : ij ∈ L
    · have hlt : U ij < U ij + δ := ENNReal.lt_add_right (hUfin ij hij).ne hδ0
      obtain ⟨H, hH⟩ := iInf_lt_iff.1 hlt
      obtain ⟨hadm, hlt'⟩ := iInf_lt_iff.1 hH
      exact ⟨H, fun _ => ⟨hadm, hlt'.le⟩⟩
    · obtain ⟨H⟩ : Nonempty Exponent.PolygonalCost.RatPolygonFamily := ⟨⟨0, fun _ => ⟨0, fun _ => (0, 0)⟩⟩⟩
      exact ⟨H, fun h => absurd h hij⟩
  choose H hH using hsel
  obtain ⟨H', hH'adm, hH'cost⟩ := fine_union_family m L hL hLA H fun ij hij => (hH ij hij).1
  have hbound : ∀ ij ∈ L, (famAffine (aQ m) (cornerQ m ij) (H ij)).cost ξ
      (fun z => φ z + ψ z) ≤ w ij * ENNReal.ofReal a * (U ij + δ) := by
    intro ij hij
    have htr : (famAffine (aQ m) (cornerQ m ij) (H ij)).trace ⊆ block a ij := by
      rw [famAffine_trace_tile]
      rintro _ ⟨u, hu, rfl⟩
      exact tileMap_image_outer_subset m ij ⟨u, ((hH ij hij).1.1 hu).1, rfl⟩
    calc (famAffine (aQ m) (cornerQ m ij) (H ij)).cost ξ (fun z => φ z + ψ z) ≤
        w ij * (famAffine (aQ m) (cornerQ m ij) (H ij)).cost ξ ψ :=
          cost_add_le htr (hw ij hij) (hwt ij hij)
      _ = w ij * (ENNReal.ofReal a * (H ij).cost ξ (fun z => ψ (tileMap m ij z))) := by
          rw [famAffine_cost_tile]
      _ ≤ w ij * (ENNReal.ofReal a * (U ij + δ)) := by gcongr; exact (hH ij hij).2
      _ = w ij * ENNReal.ofReal a * (U ij + δ) := by ring
  calc Exponent.PolygonalCost.polyAnnularCost ξ (fun z => φ z + ψ z) ≤ H'.cost ξ (fun z => φ z + ψ z) :=
        iInf₂_le H' hH'adm
    _ = ∑ ij ∈ L, (famAffine (aQ m) (cornerQ m ij) (H ij)).cost ξ (fun z => φ z + ψ z) :=
        hH'cost _ _
    _ ≤ ∑ ij ∈ L, w ij * ENNReal.ofReal a * (U ij + δ) := Finset.sum_le_sum hbound
    _ = (∑ ij ∈ L, w ij * ENNReal.ofReal a * U ij) + δ * C := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ij _ => ?_
        ring
    _ ≤ (∑ ij ∈ L, w ij * ENNReal.ofReal a * U ij) + ε := by
        gcongr
        calc δ * C ≤ δ * (C + 1) := by gcongr; exact le_self_add
          _ = ε := ENNReal.div_mul_cancel (by simp) (ENNReal.add_ne_top.2 ⟨hC, ENNReal.one_ne_top⟩)



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
