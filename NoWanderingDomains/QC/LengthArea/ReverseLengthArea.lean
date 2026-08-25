/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Foundations.BanachZaretsky
import NoWanderingDomains.QC.Foundations.BanachIndicatrix
import NoWanderingDomains.Analysis.Sobolev.AbsolutelyContinuousLines
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# The reverse length–area reduction (general, reusable)

This file packages the **reverse length–area method** into reusable, self-contained reduction
lemmas, so that the quasiconformal inverse (`QC/InverseQC/`) can consume a single, reusable
statement.

The classical reverse length–area theorem asserts that the pointwise a.e. gradient of a
quasiconformal-type map `g` is its
*distributional* gradient — equivalently, `g` is absolutely continuous on almost every line, i.e.
the distributional gradient has **no singular part**. The genuine analytic content lives entirely
in one fact: **almost every horizontal and vertical slice of `g` is absolutely continuous.** This
file proves the two surrounding reductions and isolates that single fact.

## The two fully-proven reductions

1. `hasWeakGradient_of_aeSliceAC` — **slice-AC ⟹ weak gradient.** If `g` is continuous and
   differentiable almost everywhere, and almost every horizontal/vertical slice is absolutely
   continuous, with the pointwise partials `(Dg ·) 1`, `(Dg ·) I` locally integrable, then those
   pointwise partials are the *weak (distributional)* directional derivatives of `g`. This is the
   converse Sobolev embedding *ACL ⇒ W^{1,1}_loc*, assembled here from the Fubini slice derivative,
   the FTC for absolutely continuous functions, and the project's
   `hasWeakGradient_of_acl`. **Fully proven.**

2. `absolutelyContinuousOnInterval_of_monotoneDiffLusinN` — **monotone-piece condition (N) ⟹
   slice-AC.** The Banach–Zaretsky bridge: if almost every slice's real and imaginary parts
   admit a continuous monotone Jordan decomposition `p − q` whose pieces satisfy Lusin's
   condition (N), then almost every slice is absolutely continuous. **Fully proven** from the
   project's complex Banach–Zaretsky
   FTC `complex_bv_ftc_of_monotone_diff` plus the primitive-is-AC lemma. (A homeomorphic `g` makes
   the slices injective continuous, hence continuous BV by `boundedVariationOn_Icc_of_injOn_…`, so
   the Jordan decomposition exists; what is *not* automatic is condition (N) for the monotone
   pieces — that is the irreducible reverse-length-area input.)

## The single irreducible residual

The middle node `inverse_slice_absolutelyContinuous_core_x` / `..._y` — *almost every slice of the
quasiconformal inverse is absolutely continuous* — is the genuine Marcus–Mizel / Stepanov content
that Mathlib lacks (no approximate differentiability, no Federer co-area, no planar Morrey). It is
**sound and load-bearing on the forward structure**: the area-preserving singular shear
`g ⟨x,y⟩ = x + i·(y + s x)` (`s` continuous singular increasing) satisfies *every* pointwise a.e.
datum of the inverse (injective, continuous, a.e.-differentiable, condition N⁺, the pointwise
dilatation bound, `L²_loc` pointwise partials) yet has singular (non-AC) slices — so this statement
is *false* for the shear, and correctly so: the shear is not the inverse of an `IsQCAnalytic` map
(the forward `f`'s genuine `W^{1,2}_loc` structure excludes it). See `QC/InverseQC/`.
-/

open MeasureTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-! ## Affine slice maps -/

/-- The horizontal affine slice map `t ↦ ⟨t, y⟩` has constant real derivative `1`. -/
private theorem hasDerivAt_hSlice (y x : ℝ) :
    HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
  have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [he]
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)

/-- The vertical affine slice map `t ↦ ⟨x, t⟩` has constant real derivative `I`. -/
private theorem hasDerivAt_vSlice (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (⟨x, t⟩ : ℂ)) Complex.I y := by
  have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [he]
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ)

/-- The horizontal affine slice map is continuous. -/
private theorem continuous_hSlice (y : ℝ) : Continuous (fun t : ℝ => (⟨t, y⟩ : ℂ)) := by
  have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [he]; exact (Complex.continuous_ofReal).add continuous_const

/-- The vertical affine slice map is continuous. -/
private theorem continuous_vSlice (x : ℝ) : Continuous (fun t : ℝ => (⟨x, t⟩ : ℂ)) := by
  have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [he]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-! ## Fubini slice derivatives (proven) -/

/-- **The horizontal-slice derivative, a.e., from a.e. differentiability (Fubini).** From `g`
differentiable for almost every plane point, for almost every `y` the horizontal slice
`t ↦ g ⟨t, y⟩` has derivative `(Dg ⟨x, y⟩) 1` for almost every `x`. -/
private theorem aeSliceHasDerivAt_x {g : ℂ → ℂ} (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w) :
    ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, HasDerivAt (fun t : ℝ => g ⟨t, y⟩) ((fderiv ℝ g ⟨x, y⟩) 1) x := by
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hprod : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ g ⟨p.2, p.1⟩ := by
    have hpb : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ g ⟨p.1, p.2⟩ := by
      have := hmpsymm.quasiMeasurePreserving.ae hgdiff
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hpb
    simpa [Prod.swap] using! this
  have hline : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ g ⟨x, y⟩ :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hline] with y hy
  filter_upwards [hy] with x hx
  have := hx.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_hSlice y x)
  simpa [Function.comp_def] using! this

/-- **The vertical-slice derivative, a.e., from a.e. differentiability (Fubini).** Symmetric to
`aeSliceHasDerivAt_x`. -/
private theorem aeSliceHasDerivAt_y {g : ℂ → ℂ} (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w) :
    ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, HasDerivAt (fun t : ℝ => g ⟨x, t⟩) ((fderiv ℝ g ⟨x, y⟩) Complex.I) y := by
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hprod : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ g ⟨p.1, p.2⟩ := by
    have := hmpsymm.quasiMeasurePreserving.ae hgdiff
    filter_upwards [this] with p hp
    simpa [Complex.measurableEquivRealProd_symm_apply] using hp
  have hline : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, DifferentiableAt ℝ g ⟨x, y⟩ :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hline] with x hx
  filter_upwards [hx] with y hy
  have := hy.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_vSlice x y)
  simpa [Function.comp_def] using! this

/-! ## Slice-AC ⟹ ACL (proven)

The candidate partials are the pointwise differential evaluations. On almost every slice the slice
is absolutely continuous (hypothesis) and has the pointwise differential as a.e. derivative (Fubini
above), which is exactly the `ACLHorizontal`/`ACLVertical` conjunction. -/

/-- **Horizontal slice-AC ⟹ `ACLHorizontal`.** If `g` is differentiable a.e. and almost every
horizontal slice is absolutely continuous, then `g` is absolutely continuous on almost every
horizontal line with the pointwise partial `(Dg ·) 1` as the classical line derivative. -/
theorem aclHorizontal_of_aeSliceAC {g : ℂ → ℂ}
    (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    (hac : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => g ⟨x, y⟩) a b) :
    ACLHorizontal g (fun w => (fderiv ℝ g w) 1) := by
  unfold ACLHorizontal
  filter_upwards [hac, aeSliceHasDerivAt_x hgdiff] with y hyac hyderiv
  exact ⟨hyac, hyderiv⟩

/-- **Vertical slice-AC ⟹ `ACLVertical`.** Symmetric to `aclHorizontal_of_aeSliceAC`. -/
theorem aclVertical_of_aeSliceAC {g : ℂ → ℂ}
    (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    (hac : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => g ⟨x, y⟩) a b) :
    ACLVertical g (fun w => (fderiv ℝ g w) Complex.I) := by
  unfold ACLVertical
  filter_upwards [hac, aeSliceHasDerivAt_y hgdiff] with x hxac hxderiv
  exact ⟨hxac, hxderiv⟩

/-! ## The first reduction: slice-AC ⟹ weak gradient (proven) -/

/-- **Slice-AC ⟹ weak gradient** (the converse Sobolev embedding *ACL ⇒ W^{1,1}_loc*, fully
proven). If `g` is continuous, differentiable almost everywhere, almost every horizontal and
vertical slice is absolutely continuous, and the pointwise partials `(Dg ·) 1`, `(Dg ·) I` are
locally integrable, then those pointwise partials are the *weak (distributional)* directional
derivatives of `g`. -/
theorem hasWeakGradient_of_aeSliceAC {g : ℂ → ℂ}
    (hgcont : Continuous g)
    (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    (hgxLI : LocallyIntegrable (fun w => (fderiv ℝ g w) (1 : ℂ)))
    (hgyLI : LocallyIntegrable (fun w => (fderiv ℝ g w) Complex.I))
    (hacx : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => g ⟨x, y⟩) a b)
    (hacy : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => g ⟨x, y⟩) a b) :
    HasWeakGradient (fun w => (fderiv ℝ g w) 1) (fun w => (fderiv ℝ g w) Complex.I) g Set.univ :=
  hasWeakGradient_of_acl hgcont.locallyIntegrable hgxLI hgyLI
    (aclHorizontal_of_aeSliceAC hgdiff hacx)
    (aclVertical_of_aeSliceAC hgdiff hacy)

/-! ## Componentwise absolute continuity (proven, self-contained) -/

/-- A complex function whose real and imaginary parts are absolutely continuous on an interval is
itself absolutely continuous there. -/
theorem absolutelyContinuousOnInterval_of_re_im {F : ℝ → ℂ} {a b : ℝ}
    (hre : AbsolutelyContinuousOnInterval (fun x => (F x).re) a b)
    (him : AbsolutelyContinuousOnInterval (fun x => (F x).im) a b) :
    AbsolutelyContinuousOnInterval F a b := by
  rw [absolutelyContinuousOnInterval_iff] at hre him ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hre (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := him (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hE hlen => ?_⟩
  have hl1 : ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ₁ :=
    lt_of_lt_of_le hlen (min_le_left _ _)
  have hl2 : ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ₂ :=
    lt_of_lt_of_le hlen (min_le_right _ _)
  have k1 := h₁ E hE hl1
  have k2 := h₂ E hE hl2
  have hbound : ∀ i, dist (F (E.2 i).1) (F (E.2 i).2)
      ≤ dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
        + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) := by
    intro i
    rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
    calc ‖F (E.2 i).1 - F (E.2 i).2‖
        ≤ |(F (E.2 i).1 - F (E.2 i).2).re| + |(F (E.2 i).1 - F (E.2 i).2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |(F (E.2 i).1).re - (F (E.2 i).2).re| + |(F (E.2 i).1).im - (F (E.2 i).2).im| := by
        rw [Complex.sub_re, Complex.sub_im]
  calc ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, (dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
          + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im)) :=
        Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).re) ((F (E.2 i).2).re))
          + ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) := by
        rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add k1 k2
    _ = ε := by ring

/-- An `ℝ`-valued primitive `x ↦ ∫₀ˣ φ` of an interval-integrable `φ : ℝ → ℝ` is absolutely
continuous on every interval. We enlarge to an interval `uIcc (-n) n` that contains both `0` and
`uIcc a b`, apply Mathlib's AC-of-primitive there, and restrict. (Self-contained copy of the
project's `private` lemma.) -/
private theorem absolutelyContinuousOnInterval_realPrimitive {φ : ℝ → ℝ}
    (hφ : ∀ a b : ℝ, IntervalIntegrable φ volume a b) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, φ t) a b := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max (|a|) (|b|))
  have h3 := le_max_left (|a|) (|b|)
  have h4 := le_max_right (|a|) (|b|)
  have ha : |a| ≤ n := by linarith
  have hb : |b| ≤ n := by linarith
  rw [abs_le] at ha hb
  have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnn : -(n : ℝ) ≤ (n : ℝ) := by linarith
  have h0 : (0 : ℝ) ∈ uIcc (-(n : ℝ)) n := by
    rw [Set.uIcc_of_le hnn]; exact ⟨by linarith, hN⟩
  have hbig : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, φ t)
      (-(n : ℝ)) n :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (hφ _ _) h0
  refine hbig.mono ?_
  rw [Set.uIcc_of_le hnn]
  intro t ht
  rw [Set.mem_uIcc] at ht
  rw [Set.mem_Icc]
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The `re`-component of an interval-integrable `ℂ`-valued function is interval integrable. -/
private theorem IntervalIntegrable.re_comp {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun t => (φ t).re) volume a b := by
  rw [intervalIntegrable_iff] at hφ ⊢; exact hφ.re

/-- The `im`-component of an interval-integrable `ℂ`-valued function is interval integrable. -/
private theorem IntervalIntegrable.im_comp {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun t => (φ t).im) volume a b := by
  rw [intervalIntegrable_iff] at hφ ⊢; exact hφ.im

/-- `re` commutes with the interval integral of a `ℂ`-valued function. -/
private theorem re_intervalIntegral {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    (∫ t in a..b, φ t).re = ∫ t in a..b, (φ t).re := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hφ
  simpa [Complex.reCLM_apply] using this.symm

/-- `im` commutes with the interval integral of a `ℂ`-valued function. -/
private theorem im_intervalIntegral {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : IntervalIntegrable φ volume a b) :
    (∫ t in a..b, φ t).im = ∫ t in a..b, (φ t).im := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hφ
  simpa [Complex.imCLM_apply] using this.symm

/-- The primitive of a complex interval-integrable function is absolutely continuous on every
interval (componentwise in `re`/`im`). -/
private theorem absolutelyContinuousOnInterval_complexPrimitive {φ : ℝ → ℂ}
    (hφ : ∀ a b : ℝ, IntervalIntegrable φ volume a b) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, φ t) a b := by
  refine absolutelyContinuousOnInterval_of_re_im ?_ ?_
  · have hre : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, (φ t).re) a b :=
      absolutelyContinuousOnInterval_realPrimitive
        (fun a b => IntervalIntegrable.re_comp (hφ a b)) a b
    convert hre using 2 with x
    exact re_intervalIntegral (hφ 0 x)
  · have him : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, (φ t).im) a b :=
      absolutelyContinuousOnInterval_realPrimitive
        (fun a b => IntervalIntegrable.im_comp (hφ a b)) a b
    convert him using 2 with x
    exact im_intervalIntegral (hφ 0 x)

/-! ## The Banach–Zaretsky bridge: monotone-piece condition (N) ⟹ slice-AC (proven)

A continuous slice `s : ℝ → ℂ` whose real and imaginary parts are each a difference `p − q` of
continuous monotone functions satisfying Lusin's condition (N) recovers itself by the fundamental
theorem of calculus (`complex_bv_ftc_of_monotone_diff`); hence it equals `s 0 + ∫₀ˣ s'`, a
constant plus the primitive of an interval-integrable function, which is absolutely continuous. -/

/-- **A slice with monotone-piece condition (N) is absolutely continuous (Banach–Zaretsky).**
If a `s : ℝ → ℂ` has real/imaginary parts each a difference of continuous monotone functions
satisfying Lusin's condition (N), and `s` has an interval-integrable a.e. derivative `s'`, then `s`
is absolutely continuous on every interval. This is the bridge from "continuous BV with condition
(N) monotone pieces" to absolute continuity that the reverse length–area method drives. -/
theorem absolutelyContinuousOnInterval_of_monotoneDiffLusinN {s s' : ℝ → ℂ}
    {pr qr pii qii : ℝ → ℝ}
    (hpr_mono : Monotone pr) (hpr_cont : Continuous pr)
    (hqr_mono : Monotone qr) (hqr_cont : Continuous qr)
    (hpi_mono : Monotone pii) (hpi_cont : Continuous pii)
    (hqi_mono : Monotone qii) (hqi_cont : Continuous qii)
    (hprN : ∀ S : Set ℝ, volume S = 0 → volume (pr '' S) = 0)
    (hqrN : ∀ S : Set ℝ, volume S = 0 → volume (qr '' S) = 0)
    (hpiN : ∀ S : Set ℝ, volume S = 0 → volume (pii '' S) = 0)
    (hqiN : ∀ S : Set ℝ, volume S = 0 → volume (qii '' S) = 0)
    (hre : (fun t => (s t).re) = pr - qr) (him : (fun t => (s t).im) = pii - qii)
    (hderiv : ∀ᵐ t : ℝ, HasDerivAt s (s' t) t)
    (hint : ∀ a b : ℝ, IntervalIntegrable s' volume a b)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval s a b := by
  -- The complex Banach–Zaretsky FTC: `s` recovers itself from `s'`.
  have hFTC : ∀ u v : ℝ, s v - s u = ∫ t in u..v, s' t :=
    fun u v => complex_bv_ftc_of_monotone_diff hpr_mono hpr_cont hqr_mono hqr_cont
      hpi_mono hpi_cont hqi_mono hqi_cont hprN hqrN hpiN hqiN hre him hderiv hint u v
  -- Express `s` as `s 0 + ∫₀ˣ s'`.
  have hslice_eq : ∀ x : ℝ, s x = s 0 + ∫ t in (0 : ℝ)..x, s' t := by
    intro x; have h := hFTC 0 x; linear_combination h
  -- A constant plus the primitive of an interval-integrable function is AC.
  have hprim : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, s' t) a b :=
    absolutelyContinuousOnInterval_complexPrimitive (fun a b => hint a b) a b
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => s 0) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    exact ⟨1, one_pos, fun E _ _ => by simpa using (by positivity : (0 : ℝ) < ε)⟩
  have heq : s = (fun _ : ℝ => s 0) + (fun x => ∫ t in (0 : ℝ)..x, s' t) := by
    funext x; simp [hslice_eq x]
  rw [heq]; exact hconst.add hprim

end NoWanderingDomains
