/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Absolute continuity on lines and weak derivatives

This file develops the absolutely-continuous-on-lines (ACL) characterization of
`W^{1,p}_loc` on `ℂ`, which runs in two directions:

* **`ACL ⇒ Sobolev`** — if `f : ℂ → ℂ` is absolutely continuous on almost every
  horizontal line and on almost every vertical line, with the classical
  line-derivatives given (almost everywhere) by locally integrable functions
  `gx`, `gy`, then `gx`, `gy` are the weak partial derivatives of `f`, so
  `f ∈ W^{1,p}_loc`;
* **`Sobolev ⇒ ACL`** (the converse) — if `gx` (resp. `gy`) is the weak `x`-
  (resp. `y`-) directional derivative of a locally integrable `f`, then `f` has a
  representative that is absolutely continuous on almost every horizontal (resp.
  vertical) line, with that derivative as its classical line-derivative.

This file contains the full `ACL ⇒ Sobolev` direction together with the
**one-dimensional core and infrastructure** of the converse; the companion file
`NoWanderingDomains.Analysis.Sobolev.SobolevToACL` lifts the converse to the
**two-dimensional representative** on almost every line.

Together the two directions feed the quasiconformal-map equivalence
(`QC/Equivalence.lean`): the `ACL ⇒ Sobolev` direction turns the length–area
absolute continuity of a `K`-quasiconformal map into the Sobolev membership
`MemW12loc` and the weak Wirtinger derivatives the analytic definition
`IsQCAnalytic` speaks in (geometric ⇒ analytic), while the `Sobolev ⇒ ACL`
converse extracts absolute continuity on lines from `MemW12loc`
(analytic ⇒ geometric).

## Main definitions

* `ACLHorizontal f g` — for almost every imaginary part `y`, the horizontal slice
  `x ↦ f ⟨x, y⟩` is absolutely continuous on every interval, and almost everywhere
  on the line its derivative is `g ⟨x, y⟩` (the `x`-partial of `f`);
* `ACLVertical f g` — the vertical analogue (the `y`-partial).

## Main results

`ACL ⇒ Sobolev`:
* `hasWeakDirDeriv_one_of_aclHorizontal` — `ACLHorizontal f g` (with `f`, `g`
  locally integrable) gives the weak `x`-directional derivative
  `HasWeakDirDeriv 1 g f univ`;
* `hasWeakDirDeriv_I_of_aclVertical` — the vertical analogue, the weak
  `y`-directional derivative `HasWeakDirDeriv Complex.I g f univ`;
* `hasWeakGradient_of_acl` — packages the two directions into a weak gradient;
* `memWklocP_one_of_acl` — the Sobolev-membership conclusion `MemWklocP f 1 p univ`
  (in particular `MemW12loc f` for `p = 2`).

`Sobolev ⇒ ACL` (one-dimensional core and infrastructure; the two-dimensional
representative theorems are in the companion file
`NoWanderingDomains.Analysis.Sobolev.SobolevToACL`):
* `ae_eq_const_of_oneDim_weakDeriv_zero` — a locally integrable `u : ℝ → ℂ` with
  vanishing one-dimensional weak derivative is almost everywhere constant;
* `exists_absolutelyContinuous_of_oneDim_weakDeriv` — the one-dimensional core: a
  locally integrable `u : ℝ → ℂ` with locally integrable weak derivative agrees
  almost everywhere with an absolutely continuous function (`x ↦ c + ∫₀ˣ u'`);
* `contDiff_intervalIntegral_primitive_fst` — joint `C^∞` of the parametric
  `x`-primitive `(x, y) ↦ ∫ₐˣ w(t, y)` (via a convolution representation), the
  smooth test functions the two-dimensional converse tests against.

The `ACL ⇒ Sobolev` direction is the classical Fubini + per-line integration by
parts: on each line, `∫ φ' · f = − ∫ φ · g` by the fundamental theorem of calculus
for absolutely continuous functions (`AbsolutelyContinuousOnInterval`, boundary
terms vanishing as `φ` has compact support), and Fubini assembles the line
identities into the two-dimensional weak-derivative identity. The one-dimensional
converse core agrees a locally integrable function with `x ↦ c + ∫₀ˣ u'` by
pinning the constant through `ae_eq_const_of_oneDim_weakDeriv_zero`; the companion
file `SobolevToACL` lifts it to almost every line.
-/

open MeasureTheory Complex
open scoped ENNReal ContDiff

namespace NoWanderingDomains

variable {f g gx gy : ℂ → ℂ} {p : ℝ≥0∞}

/-- `f` is **absolutely continuous on almost every horizontal line**, with
`x`-partial `g`: for almost every imaginary part `y`, the horizontal slice
`x ↦ f ⟨x, y⟩` is absolutely continuous on every interval, and almost everywhere
on the line its classical derivative equals `g ⟨x, y⟩`. -/
def ACLHorizontal (f g : ℂ → ℂ) : Prop :=
  ∀ᵐ y : ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b) ∧
    (∀ᵐ x : ℝ, HasDerivAt (fun t : ℝ => f ⟨t, y⟩) (g ⟨x, y⟩) x)

/-- `f` is **absolutely continuous on almost every vertical line**, with
`y`-partial `g`: for almost every real part `x`, the vertical slice
`y ↦ f ⟨x, y⟩` is absolutely continuous on every interval, and almost everywhere
on the line its classical derivative equals `g ⟨x, y⟩`. -/
def ACLVertical (f g : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b) ∧
    (∀ᵐ y : ℝ, HasDerivAt (fun t : ℝ => f ⟨x, t⟩) (g ⟨x, y⟩) y)

set_option maxHeartbeats 400000 in
-- The Fubini transfer, the componentwise integration-by-parts, and the per-line
-- slice bookkeeping make this a long elaboration, so the heartbeat budget is raised.
/-- **Absolute continuity on horizontal lines yields the weak `x`-derivative.**
If `f` is absolutely continuous on almost every horizontal line with `x`-partial
`g`, and both `f` and `g` are locally integrable, then `g` is the weak
directional derivative of `f` in the real direction `1`. Proof: Fubini reduces
the two-dimensional integration-by-parts identity to the one-dimensional one on
each horizontal line, where the fundamental theorem of calculus for absolutely
continuous functions applies (the boundary terms vanish because the test function
has compact support). -/
theorem hasWeakDirDeriv_one_of_aclHorizontal
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hacl : ACLHorizontal f g) :
    HasWeakDirDeriv 1 g f Set.univ := by
  intro φ hφ_smooth hφ_cpt _
  -- **Composition of a Lipschitz map with an absolutely continuous function is AC.**
  have hLipComp : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F Y _ l K hl a b hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- **Per-line integration by parts** (the one-dimensional `∫ Φ' • F = − ∫ Φ • G`).
  -- Reduce to the `ℝ`-valued statement componentwise through `reCLM`/`imCLM`, where
  -- Mathlib's IBP for absolutely continuous functions applies; the boundary terms vanish
  -- since `Φ` has compact support.
  have lineIBP : ∀ (Φ : ℝ → ℝ) (F G : ℝ → ℂ),
      ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) →
      (∀ᵐ t : ℝ, HasDerivAt F (G t) t) →
      Integrable (fun t => deriv Φ t • F t) → Integrable (fun t => Φ t • G t) →
      (∫ t, (deriv Φ t) • F t) = - ∫ t, Φ t • G t := by
    intro Φ F G hΦ_smooth hΦ_cpt hF_ac hF_deriv hintL hintR
    obtain ⟨KΦ, hKΦ⟩ := hΦ_smooth.lipschitzWith_of_hasCompactSupport hΦ_cpt (by norm_num)
    have hΦ_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Φ a b :=
      fun a b => (hKΦ.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
    obtain ⟨R, hR, hRsupp⟩ := hΦ_cpt.exists_pos_le_norm
    have hΦa : Φ (-R) = 0 := hRsupp (-R) (by rw [norm_neg, Real.norm_eq_abs, abs_of_pos hR])
    have hΦb : Φ R = 0 := hRsupp R (by rw [Real.norm_eq_abs, abs_of_pos hR])
    have hΦ_zero : ∀ t ∉ Set.Icc (-R) R, Φ t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
    have hdΦ_zero : ∀ t ∉ Set.Icc (-R) R, deriv Φ t = 0 := by
      intro t ht
      have hne : Φ =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < -R from h)] with x hx
          rw [Set.mem_Iio] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
        · filter_upwards [Ioi_mem_nhds (show R < t from h)] with x hx
          rw [Set.mem_Ioi] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
      rw [Filter.EventuallyEq.deriv_eq hne]; simp
    -- The componentwise IBP, for any `ℝ`-linear projection `proj : ℂ →L[ℝ] ℝ`.
    have compIBP : ∀ proj : ℂ →L[ℝ] ℝ,
        (∫ t, deriv Φ t * proj (F t)) = - ∫ t, Φ t * proj (G t) := by
      intro proj
      have hab : (-R) ≤ R := by linarith
      set Fr : ℝ → ℝ := fun t => proj (F t) with hFr
      set Gr : ℝ → ℝ := fun t => proj (G t) with hGr
      have hFr_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Fr a b :=
        fun a b => hLipComp proj ‖proj‖₊ proj.lipschitz (hF_ac a b)
      have hFr_deriv : ∀ᵐ t : ℝ, deriv Fr t = Gr t := by
        filter_upwards [hF_deriv] with t ht
        have : HasDerivAt Fr (proj (G t)) t := by
          have := proj.hasFDerivAt.comp_hasDerivAt t ht
          simpa [hFr, Function.comp_def] using this
        exact this.deriv
      have hIBP := (hΦ_ac (-R) R).integral_mul_deriv_eq_deriv_mul (hFr_ac (-R) R)
      rw [hΦa, hΦb] at hIBP
      simp only [zero_mul, sub_zero, zero_sub] at hIBP
      have hIBP2 : (∫ x in (-R)..R, Φ x * Gr x) = - ∫ x in (-R)..R, deriv Φ x * Fr x := by
        rw [← hIBP]; apply intervalIntegral.integral_congr_ae
        filter_upwards [hFr_deriv] with x hx _; rw [hx]
      have hconvL : (∫ x in (-R)..R, Φ x * Gr x) = ∫ x, Φ x * Gr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hΦ_zero t ht, zero_mul])
      have hconvR : (∫ x in (-R)..R, deriv Φ x * Fr x) = ∫ x, deriv Φ x * Fr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hdΦ_zero t ht, zero_mul])
      rw [hconvL, hconvR] at hIBP2
      change (∫ t, deriv Φ t * Fr t) = - ∫ t, Φ t * Gr t
      rw [hIBP2, neg_neg]
    apply Complex.ext
    · have hreL : (∫ t, (deriv Φ t) • F t).re = ∫ t, deriv Φ t * (F t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintL
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      have hreR : (∫ t, Φ t • G t).re = ∫ t, Φ t * (G t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintR
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      rw [hreL, Complex.neg_re, hreR]; exact compIBP Complex.reCLM
    · have himL : (∫ t, (deriv Φ t) • F t).im = ∫ t, deriv Φ t * (F t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintL
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      have himR : (∫ t, Φ t • G t).im = ∫ t, Φ t * (G t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintR
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      rw [himL, Complex.neg_im, himR]; exact compIBP Complex.imCLM
  -- **`(continuous, compactly supported real) • (locally integrable ℂ)` is integrable on `ℂ`.**
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m →
      ∀ {h : ℂ → ℂ}, LocallyIntegrable h → Integrable (fun z => m z • h z) := by
    intro m hm hcs h hh
    have hK : IsCompact (tsupport m) := hcs
    have hhon : IntegrableOn h (tsupport m) volume := hh.integrableOn_isCompact hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz; apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  set Lc : ℂ → ℂ := fun z => ((fderiv ℝ φ z) 1) • f z with hLc
  set Rc : ℂ → ℂ := fun z => φ z • g z with hRc
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) (1 : ℂ)) :=
    (hφ_smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) (1 : ℂ)) :=
    HasCompactSupport.fderiv_apply ℝ hφ_cpt 1
  have hintLc : Integrable Lc := integ _ hcont_dφ hcs_dφ hf
  have hintRc : Integrable Rc := integ _ hφ_smooth.continuous hφ_cpt hg
  -- **Transfer from `ℂ` to `ℝ × ℝ`** through the volume-preserving real-coordinate equivalence.
  have hemb := Complex.measurableEquivRealProd.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) := hmp.symm Complex.measurableEquivRealProd
  have transInt : ∀ (W : ℂ → ℂ), (∫ z : ℂ, W z) = ∫ p : ℝ × ℝ, W ⟨p.1, p.2⟩ := by
    intro W
    have key := hmp.integral_comp hemb (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩)
    rw [← key]; apply integral_congr_ae; filter_upwards with z; congr 1
  have transIntg : ∀ (W : ℂ → ℂ), Integrable W →
      Integrable (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩) (volume.prod volume) := by
    intro W hW
    rw [← Measure.volume_eq_prod]
    exact (hmpsymm.integrable_comp_of_integrable hW).congr
      (Filter.Eventually.of_forall fun p => rfl)
  change (∫ z, Lc z) = - ∫ z, Rc z
  rw [transInt Lc, transInt Rc]
  rw [Measure.volume_eq_prod] at *
  -- **Fubini** (inner integral over the first coordinate `x`, outer over `y`).
  rw [integral_prod_symm _ (transIntg Lc hintLc), integral_prod_symm _ (transIntg Rc hintRc)]
  rw [← integral_neg]
  apply integral_congr_ae
  -- Fubini also gives a.e.-`y` integrability of the inner slices.
  have hLslice := (transIntg Lc hintLc).prod_left_ae
  have hRslice := (transIntg Rc hintRc).prod_left_ae
  filter_upwards [hacl, hLslice, hRslice] with y hy_acl hy_Lint hy_Rint
  obtain ⟨hF_ac, hF_deriv⟩ := hy_acl
  -- The horizontal slice `t ↦ φ ⟨t, y⟩` of the test function is smooth and compactly supported.
  have hΦy_smooth : ContDiff ℝ ∞ (fun t : ℝ => φ ⟨t, y⟩) := by
    have hmap : ContDiff ℝ ∞ (fun t : ℝ => (⟨t, y⟩ : ℂ)) := by
      have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]; exact Complex.ofRealCLM.contDiff.add contDiff_const
    exact hφ_smooth.comp hmap
  have hΦy_cpt : HasCompactSupport (fun t : ℝ => φ ⟨t, y⟩) := by
    obtain ⟨R, hR, hRsupp⟩ := hφ_cpt.exists_pos_le_norm
    apply HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc
    intro t ht
    apply hRsupp
    have hle : ‖(t : ℝ)‖ ≤ ‖(⟨t, y⟩ : ℂ)‖ := by
      rw [Real.norm_eq_abs]; simpa using Complex.abs_re_le_norm (⟨t, y⟩ : ℂ)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
        _ ≤ _ := hle
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
        _ ≤ _ := hle
  -- The `x`-partial of `φ` is the derivative of the horizontal slice.
  have hsliceΦ : ∀ x : ℝ, HasDerivAt (fun t : ℝ => φ ⟨t, y⟩) ((fderiv ℝ φ ⟨x, y⟩) 1) x := by
    intro x
    have haff : HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
      have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]; simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
    have hfd : HasFDerivAt φ (fderiv ℝ φ ⟨x, y⟩) ⟨x, y⟩ :=
      (hφ_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    simpa [Function.comp_def] using hfd.comp_hasDerivAt x haff
  have hLeq : (fun x => Lc ⟨x, y⟩) = fun x => deriv (fun t : ℝ => φ ⟨t, y⟩) x • f ⟨x, y⟩ := by
    funext x; rw [hLc, (hsliceΦ x).deriv]
  have hReq : (fun x => Rc ⟨x, y⟩) = fun x => (fun t : ℝ => φ ⟨t, y⟩) x • g ⟨x, y⟩ := by
    funext x; rw [hRc]
  change (∫ x, Lc ⟨x, y⟩) = -(∫ x, Rc ⟨x, y⟩)
  rw [hLeq, hReq]
  refine lineIBP (fun t => φ ⟨t, y⟩) (fun x => f ⟨x, y⟩) (fun x => g ⟨x, y⟩)
    hΦy_smooth hΦy_cpt hF_ac hF_deriv ?_ ?_
  · rw [← hLeq]; exact hy_Lint
  · rw [← hReq]; exact hy_Rint

set_option maxHeartbeats 400000 in
-- The Fubini transfer, the componentwise integration-by-parts, and the per-line
-- slice bookkeeping make this a long elaboration, so the heartbeat budget is raised.
/-- **Absolute continuity on vertical lines yields the weak `y`-derivative.**
The vertical analogue of `hasWeakDirDeriv_one_of_aclHorizontal`: if `f` is
absolutely continuous on almost every vertical line with `y`-partial `g`, and
both `f` and `g` are locally integrable, then `g` is the weak directional
derivative of `f` in the imaginary direction `Complex.I`. -/
theorem hasWeakDirDeriv_I_of_aclVertical
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hacl : ACLVertical f g) :
    HasWeakDirDeriv Complex.I g f Set.univ := by
  intro φ hφ_smooth hφ_cpt _
  -- **Composition of a Lipschitz map with an absolutely continuous function is AC.**
  have hLipComp : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F Y _ l K hl a b hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- **Per-line integration by parts** (the one-dimensional `∫ Φ' • F = − ∫ Φ • G`).
  have lineIBP : ∀ (Φ : ℝ → ℝ) (F G : ℝ → ℂ),
      ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) →
      (∀ᵐ t : ℝ, HasDerivAt F (G t) t) →
      Integrable (fun t => deriv Φ t • F t) → Integrable (fun t => Φ t • G t) →
      (∫ t, (deriv Φ t) • F t) = - ∫ t, Φ t • G t := by
    intro Φ F G hΦ_smooth hΦ_cpt hF_ac hF_deriv hintL hintR
    obtain ⟨KΦ, hKΦ⟩ := hΦ_smooth.lipschitzWith_of_hasCompactSupport hΦ_cpt (by norm_num)
    have hΦ_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Φ a b :=
      fun a b => (hKΦ.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
    obtain ⟨R, hR, hRsupp⟩ := hΦ_cpt.exists_pos_le_norm
    have hΦa : Φ (-R) = 0 := hRsupp (-R) (by rw [norm_neg, Real.norm_eq_abs, abs_of_pos hR])
    have hΦb : Φ R = 0 := hRsupp R (by rw [Real.norm_eq_abs, abs_of_pos hR])
    have hΦ_zero : ∀ t ∉ Set.Icc (-R) R, Φ t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
    have hdΦ_zero : ∀ t ∉ Set.Icc (-R) R, deriv Φ t = 0 := by
      intro t ht
      have hne : Φ =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < -R from h)] with x hx
          rw [Set.mem_Iio] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
        · filter_upwards [Ioi_mem_nhds (show R < t from h)] with x hx
          rw [Set.mem_Ioi] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
      rw [Filter.EventuallyEq.deriv_eq hne]; simp
    -- The componentwise IBP, for any `ℝ`-linear projection `proj : ℂ →L[ℝ] ℝ`.
    have compIBP : ∀ proj : ℂ →L[ℝ] ℝ,
        (∫ t, deriv Φ t * proj (F t)) = - ∫ t, Φ t * proj (G t) := by
      intro proj
      have hab : (-R) ≤ R := by linarith
      set Fr : ℝ → ℝ := fun t => proj (F t) with hFr
      set Gr : ℝ → ℝ := fun t => proj (G t) with hGr
      have hFr_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Fr a b :=
        fun a b => hLipComp proj ‖proj‖₊ proj.lipschitz (hF_ac a b)
      have hFr_deriv : ∀ᵐ t : ℝ, deriv Fr t = Gr t := by
        filter_upwards [hF_deriv] with t ht
        have : HasDerivAt Fr (proj (G t)) t := by
          have := proj.hasFDerivAt.comp_hasDerivAt t ht
          simpa [hFr, Function.comp_def] using this
        exact this.deriv
      have hIBP := (hΦ_ac (-R) R).integral_mul_deriv_eq_deriv_mul (hFr_ac (-R) R)
      rw [hΦa, hΦb] at hIBP
      simp only [zero_mul, sub_zero, zero_sub] at hIBP
      have hIBP2 : (∫ x in (-R)..R, Φ x * Gr x) = - ∫ x in (-R)..R, deriv Φ x * Fr x := by
        rw [← hIBP]; apply intervalIntegral.integral_congr_ae
        filter_upwards [hFr_deriv] with x hx _; rw [hx]
      have hconvL : (∫ x in (-R)..R, Φ x * Gr x) = ∫ x, Φ x * Gr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hΦ_zero t ht, zero_mul])
      have hconvR : (∫ x in (-R)..R, deriv Φ x * Fr x) = ∫ x, deriv Φ x * Fr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hdΦ_zero t ht, zero_mul])
      rw [hconvL, hconvR] at hIBP2
      change (∫ t, deriv Φ t * Fr t) = - ∫ t, Φ t * Gr t
      rw [hIBP2, neg_neg]
    apply Complex.ext
    · have hreL : (∫ t, (deriv Φ t) • F t).re = ∫ t, deriv Φ t * (F t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintL
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      have hreR : (∫ t, Φ t • G t).re = ∫ t, Φ t * (G t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintR
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      rw [hreL, Complex.neg_re, hreR]; exact compIBP Complex.reCLM
    · have himL : (∫ t, (deriv Φ t) • F t).im = ∫ t, deriv Φ t * (F t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintL
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      have himR : (∫ t, Φ t • G t).im = ∫ t, Φ t * (G t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintR
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      rw [himL, Complex.neg_im, himR]; exact compIBP Complex.imCLM
  -- **`(continuous, compactly supported real) • (locally integrable ℂ)` is integrable on `ℂ`.**
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m →
      ∀ {h : ℂ → ℂ}, LocallyIntegrable h → Integrable (fun z => m z • h z) := by
    intro m hm hcs h hh
    have hK : IsCompact (tsupport m) := hcs
    have hhon : IntegrableOn h (tsupport m) volume := hh.integrableOn_isCompact hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz; apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  set Lc : ℂ → ℂ := fun z => ((fderiv ℝ φ z) Complex.I) • f z with hLc
  set Rc : ℂ → ℂ := fun z => φ z • g z with hRc
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) Complex.I) :=
    (hφ_smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) Complex.I) :=
    HasCompactSupport.fderiv_apply ℝ hφ_cpt Complex.I
  have hintLc : Integrable Lc := integ _ hcont_dφ hcs_dφ hf
  have hintRc : Integrable Rc := integ _ hφ_smooth.continuous hφ_cpt hg
  -- **Transfer from `ℂ` to `ℝ × ℝ`** through the volume-preserving real-coordinate equivalence.
  have hemb := Complex.measurableEquivRealProd.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) := hmp.symm Complex.measurableEquivRealProd
  have transInt : ∀ (W : ℂ → ℂ), (∫ z : ℂ, W z) = ∫ p : ℝ × ℝ, W ⟨p.1, p.2⟩ := by
    intro W
    have key := hmp.integral_comp hemb (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩)
    rw [← key]; apply integral_congr_ae; filter_upwards with z; congr 1
  have transIntg : ∀ (W : ℂ → ℂ), Integrable W →
      Integrable (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩) (volume.prod volume) := by
    intro W hW
    rw [← Measure.volume_eq_prod]
    exact (hmpsymm.integrable_comp_of_integrable hW).congr
      (Filter.Eventually.of_forall fun p => rfl)
  change (∫ z, Lc z) = - ∫ z, Rc z
  rw [transInt Lc, transInt Rc]
  rw [Measure.volume_eq_prod] at *
  -- **Fubini** (inner integral over the second coordinate `y`, outer over `x`).
  rw [integral_prod _ (transIntg Lc hintLc), integral_prod _ (transIntg Rc hintRc)]
  rw [← integral_neg]
  apply integral_congr_ae
  -- Fubini also gives a.e.-`x` integrability of the inner slices.
  have hLslice := (transIntg Lc hintLc).prod_right_ae
  have hRslice := (transIntg Rc hintRc).prod_right_ae
  filter_upwards [hacl, hLslice, hRslice] with x hx_acl hx_Lint hx_Rint
  obtain ⟨hF_ac, hF_deriv⟩ := hx_acl
  -- The vertical slice `t ↦ φ ⟨x, t⟩` of the test function is smooth and compactly supported.
  have hΦx_smooth : ContDiff ℝ ∞ (fun t : ℝ => φ ⟨x, t⟩) := by
    have hmap : ContDiff ℝ ∞ (fun t : ℝ => (⟨x, t⟩ : ℂ)) := by
      have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]; exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact hφ_smooth.comp hmap
  have hΦx_cpt : HasCompactSupport (fun t : ℝ => φ ⟨x, t⟩) := by
    obtain ⟨R, hR, hRsupp⟩ := hφ_cpt.exists_pos_le_norm
    apply HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc
    intro t ht
    apply hRsupp
    have hle : ‖(t : ℝ)‖ ≤ ‖(⟨x, t⟩ : ℂ)‖ := by
      rw [Real.norm_eq_abs]; simpa using Complex.abs_im_le_norm (⟨x, t⟩ : ℂ)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
        _ ≤ _ := hle
    · calc R ≤ ‖(t : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
        _ ≤ _ := hle
  -- The `y`-partial of `φ` is the derivative of the vertical slice.
  have hsliceΦ : ∀ y : ℝ, HasDerivAt (fun t : ℝ => φ ⟨x, t⟩) ((fderiv ℝ φ ⟨x, y⟩) Complex.I) y := by
    intro y
    have haff : HasDerivAt (fun t : ℝ => (⟨x, t⟩ : ℂ)) Complex.I y := by
      have he : (fun t : ℝ => (⟨x, t⟩ : ℂ)) = fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [he]
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      simpa using h1.const_add ((x : ℂ))
    have hfd : HasFDerivAt φ (fderiv ℝ φ ⟨x, y⟩) ⟨x, y⟩ :=
      (hφ_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    simpa [Function.comp_def] using hfd.comp_hasDerivAt y haff
  have hLeq : (fun y => Lc ⟨x, y⟩) = fun y => deriv (fun t : ℝ => φ ⟨x, t⟩) y • f ⟨x, y⟩ := by
    funext y; rw [hLc, (hsliceΦ y).deriv]
  have hReq : (fun y => Rc ⟨x, y⟩) = fun y => (fun t : ℝ => φ ⟨x, t⟩) y • g ⟨x, y⟩ := by
    funext y; rw [hRc]
  change (∫ y, Lc ⟨x, y⟩) = -(∫ y, Rc ⟨x, y⟩)
  rw [hLeq, hReq]
  refine lineIBP (fun t => φ ⟨x, t⟩) (fun y => f ⟨x, y⟩) (fun y => g ⟨x, y⟩)
    hΦx_smooth hΦx_cpt hF_ac hF_deriv ?_ ?_
  · rw [← hLeq]; exact hx_Lint
  · rw [← hReq]; exact hx_Rint

/-- **A weak gradient from absolute continuity on lines.** If `f` is absolutely
continuous on almost every horizontal line with `x`-partial `gx` and on almost
every vertical line with `y`-partial `gy`, then `(gx, gy)` is a weak gradient of
`f`. -/
theorem hasWeakGradient_of_acl
    (hf : LocallyIntegrable f) (hgx : LocallyIntegrable gx) (hgy : LocallyIntegrable gy)
    (haclx : ACLHorizontal f gx) (hacly : ACLVertical f gy) :
    HasWeakGradient gx gy f Set.univ :=
  ⟨hasWeakDirDeriv_one_of_aclHorizontal hf hgx haclx,
    hasWeakDirDeriv_I_of_aclVertical hf hgy hacly⟩

/-- **`ACL ⇒ W^{1,p}_loc`.** If `f` is locally `Lᵖ`, absolutely continuous on
almost every horizontal and vertical line with `x`- and `y`-partials `gx`, `gy`
that are themselves locally `Lᵖ` (and locally integrable), then `f` lies in
`W^{1,p}_loc(ℂ)`. Specialized to `p = 2`, this is `MemW12loc f`, the Sobolev
class the analytic quasiconformal theory lives in. -/
theorem memWklocP_one_of_acl
    (hf : MemLpLocOn f p Set.univ)
    (hgx : MemLpLocOn gx p Set.univ) (hgy : MemLpLocOn gy p Set.univ)
    (hfli : LocallyIntegrable f) (hgxli : LocallyIntegrable gx) (hgyli : LocallyIntegrable gy)
    (haclx : ACLHorizontal f gx) (hacly : ACLVertical f gy) :
    MemWklocP f 1 p Set.univ :=
  ⟨hf, gx, gy, hasWeakGradient_of_acl hfli hgxli hgyli haclx hacly, hgx, hgy⟩

/-! ### The converse: `W^{1,p}_loc ⇒ ACL`

The harder direction of the characterization: a Sobolev function has a
representative that is absolutely continuous on almost every line, with the
classical line-derivatives equal almost everywhere to the weak partials. This is
what the analytic ⇒ geometric direction of the quasiconformal-map equivalence
needs (it starts from `MemW12loc` and must extract absolute continuity on lines to
run the length–area modulus estimate).

The engine is the one-dimensional core `exists_absolutelyContinuous_of_oneDim_weakDeriv`:
a locally integrable `u : ℝ → ℂ` whose one-dimensional weak derivative is a
locally integrable `u'` agrees almost everywhere with the absolutely continuous
function `x ↦ c + ∫₀ˣ u'`, whose classical derivative is `u'` almost everywhere
(`x ↦ ∫₀ˣ u'` is AC by `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`
and has derivative `u'` a.e. by `LocallyIntegrable.ae_hasDerivAt_integral`; the
constant `c` is pinned because `u` and `x ↦ ∫₀ˣ u'` share a weak derivative, so
their difference has vanishing weak derivative and is a.e. constant). The two
direction theorems slice the two-dimensional weak-derivative identity to a.e.
lines (Fubini) and apply the core line by line, assembling an explicit jointly
measurable representative.
-/

/-- **A locally integrable function on `ℝ` with vanishing one-dimensional weak
derivative is almost everywhere constant.** If `∫ ψ' • h = 0` for every smooth
compactly supported `ψ : ℝ → ℝ`, then `h =ᵐ c` for some constant `c`. Proof:
fix a smooth compactly supported `η` with `∫ η = 1`; for any test `χ`, the
primitive `x ↦ ∫₋∞ˣ (χ − (∫χ)·η)` is smooth with compact support (its integrand
has total integral `0`) and its derivative is `χ − (∫χ)·η`, so the hypothesis
gives `∫ χ • h = (∫χ) · (∫ η • h)`, i.e. `h` integrates against every test the
same way the constant `c := ∫ η • h` does; conclude by
`MeasureTheory.ae_eq_of_integral_contDiff_smul_eq`. -/
theorem ae_eq_const_of_oneDim_weakDeriv_zero
    {h : ℝ → ℂ} (hh : LocallyIntegrable h)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ t, deriv ψ t • h t = 0) :
    ∃ c : ℂ, h =ᵐ[volume] (fun _ => c) := by
  -- **Step 1: a mean-one mollifier `η`.**
  set b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hb
  set η : ℝ → ℝ := b.normed volume with hη
  have hη_smooth : ContDiff ℝ ∞ η := b.contDiff_normed (n := ⊤)
  have hη_cpt : HasCompactSupport η := b.hasCompactSupport_normed
  have hη_cont : Continuous η := hη_smooth.continuous
  have hη_int : ∫ t, η t = 1 := b.integral_normed
  -- **A continuous compactly supported real function times `h` is integrable.**
  have integ : ∀ m : ℝ → ℝ, Continuous m → HasCompactSupport m →
      Integrable (fun t => m t • h t) := by
    intro m hm hcs
    have hK : IsCompact (tsupport m) := hcs
    have hhon : IntegrableOn h (tsupport m) volume := hh.integrableOn_isCompact hK
    have hon : IntegrableOn (fun t => m t • h t) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun t => m t • h t) ⊆ tsupport m := by
      intro t ht; apply subset_tsupport m
      simp only [Function.mem_support] at ht ⊢
      intro hmt; apply ht; simp [hmt]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- **Step 2: the constant.**
  set c : ℂ := ∫ t, η t • h t with hc
  -- **Step 3: the key claim, `∫ χ • h = (∫ χ) • c` for every test `χ`.**
  have key : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∫ t, χ t • h t) = (∫ s, χ s) • c := by
    intro χ hχ_smooth hχ_cpt
    have hχ_cont : Continuous χ := hχ_smooth.continuous
    -- The mean-zero combination `w := χ − (∫χ)·η`.
    set w : ℝ → ℝ := fun t => χ t - (∫ s, χ s) * η t with hw
    have hw_smooth : ContDiff ℝ ∞ w :=
      hχ_smooth.sub (contDiff_const.mul hη_smooth)
    have hw_cont : Continuous w := hw_smooth.continuous
    have hw_cpt : HasCompactSupport w :=
      hχ_cpt.sub hη_cpt.mul_left
    have hw_int0 : ∫ t, w t = 0 := by
      rw [hw]
      rw [integral_sub (hχ_cont.integrable_of_hasCompactSupport hχ_cpt)
        ((hη_cont.integrable_of_hasCompactSupport hη_cpt).const_mul _)]
      rw [integral_const_mul, hη_int, mul_one, sub_self]
    -- A bound `R` for the supports of both `χ` and `η`, then `a < -R, b > R`.
    obtain ⟨Rχ, hRχ, hRχsupp⟩ := hχ_cpt.exists_pos_le_norm
    obtain ⟨Rη, hRη, hRηsupp⟩ := hη_cpt.exists_pos_le_norm
    set R : ℝ := max Rχ Rη with hR
    have hR0 : 0 < R := lt_max_of_lt_left hRχ
    -- `w` vanishes outside `(-R, R)`.
    have hw_zero : ∀ t : ℝ, R ≤ |t| → w t = 0 := by
      intro t ht
      have h1 : χ t = 0 :=
        hRχsupp t (by rw [Real.norm_eq_abs]; exact le_trans (le_max_left _ _) ht)
      have h2 : η t = 0 :=
        hRηsupp t (by rw [Real.norm_eq_abs]; exact le_trans (le_max_right _ _) ht)
      rw [hw]; simp [h1, h2]
    set aL : ℝ := -R - 1 with haL
    set bR : ℝ := R + 1 with hbR
    have habR : aL ≤ bR := by rw [haL, hbR]; linarith
    -- **The primitive `ψ x := ∫_{aL}^x w`.**
    set ψ : ℝ → ℝ := fun x => ∫ t in aL..x, w t with hψ
    -- Its derivative is `w` everywhere (FTC-1, `w` continuous).
    have hψ_deriv : ∀ x : ℝ, HasDerivAt ψ (w x) x := by
      intro x
      exact intervalIntegral.integral_hasDerivAt_right
        (hw_cont.intervalIntegrable _ _)
        hw_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hw_cont.continuousAt
    have hderiv_ψ : deriv ψ = w := funext fun x => (hψ_deriv x).deriv
    -- `ψ` is smooth.
    have hψ_smooth : ContDiff ℝ ∞ ψ := by
      rw [contDiff_infty_iff_deriv]
      refine ⟨fun x => (hψ_deriv x).differentiableAt, ?_⟩
      rw [hderiv_ψ]; exact hw_smooth
    -- `ψ` has compact support: `ψ x = 0` for `x ∉ [aL, bR]`.
    have hψ_cpt : HasCompactSupport ψ := by
      apply HasCompactSupport.intro (K := Set.Icc aL bR) isCompact_Icc
      intro x hx
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      change (∫ t in aL..x, w t) = 0
      rcases hx with hlt | hgt
      · -- `x < aL`: `∫ aL..x w = -∫ x..aL w = 0` since `w = 0` on `Ι x aL`.
        rw [intervalIntegral.integral_symm, neg_eq_zero]
        apply intervalIntegral.integral_zero_ae
        filter_upwards with t ht
        rw [Set.uIoc_of_le hlt.le, Set.mem_Ioc] at ht
        have ht2 : t ≤ -R - 1 := by have := ht.2; rwa [haL] at this
        apply hw_zero
        rw [abs_of_neg (by linarith)]; linarith
      · -- `x > bR`: `∫ aL..x w = ∫ aL..bR w + ∫ bR..x w`; second is 0, first is `∫ w = 0`.
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hw_cont.intervalIntegrable aL bR) (hw_cont.intervalIntegrable bR x)]
        have hsecond : (∫ t in bR..x, w t) = 0 := by
          apply intervalIntegral.integral_zero_ae
          filter_upwards with t ht
          rw [Set.uIoc_of_le hgt.le, Set.mem_Ioc] at ht
          have ht1 : R + 1 < t := by have := ht.1; rwa [hbR] at this
          apply hw_zero
          rw [abs_of_pos (by linarith)]; linarith
        have hfirst : (∫ t in aL..bR, w t) = 0 := by
          rw [intervalIntegral.integral_of_le habR, ← integral_Icc_eq_integral_Ioc,
            setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc aL bR), hw_int0]
          intro t ht
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
          rcases ht with hlo | hhi
          · have hlo' : t < -R - 1 := by rwa [haL] at hlo
            exact hw_zero t (by rw [abs_of_neg (by linarith)]; linarith)
          · have hhi' : R + 1 < t := by rwa [hbR] at hhi
            exact hw_zero t (by rw [abs_of_pos (by linarith)]; linarith)
        rw [hfirst, hsecond, add_zero]
    -- Apply the weak-derivative hypothesis to `ψ`.
    have hweakψ := hweak ψ hψ_smooth hψ_cpt
    rw [hderiv_ψ] at hweakψ
    -- Expand `∫ w • h = ∫ χ • h − (∫χ) • (∫ η • h) = ∫ χ•h − (∫χ)•c`.
    have hexp : (∫ t, w t • h t) = (∫ t, χ t • h t) - (∫ s, χ s) • c := by
      have hpoint : ∀ t : ℝ,
          w t • h t = χ t • h t - (∫ s, χ s) • (η t • h t) := by
        intro t; simp only [hw]; module
      have hintχ : Integrable (fun t => χ t • h t) := integ χ hχ_cont hχ_cpt
      have hintη : Integrable (fun t => (∫ s, χ s) • (η t • h t)) :=
        (integ η hη_cont hη_cpt).smul (∫ s, χ s)
      calc (∫ t, w t • h t)
          = ∫ t, (χ t • h t - (∫ s, χ s) • (η t • h t)) :=
            integral_congr_ae (Filter.Eventually.of_forall hpoint)
        _ = (∫ t, χ t • h t) - ∫ t, (∫ s, χ s) • (η t • h t) := integral_sub hintχ hintη
        _ = (∫ t, χ t • h t) - (∫ s, χ s) • c := by
            rw [hc]; congr 1
            exact integral_smul (∫ s, χ s) (fun t => η t • h t)
    rw [hexp] at hweakψ
    -- `∫ χ•h − (∫χ)•c = 0  ⟹  ∫ χ•h = (∫χ)•c`.
    linear_combination (norm := module) hweakψ
  -- **Step 4: conclude via `ae_eq_of_integral_contDiff_smul_eq`.**
  refine ⟨c, ?_⟩
  have hconst : LocallyIntegrable (fun _ : ℝ => c) := locallyIntegrable_const c
  have := ae_eq_of_integral_contDiff_smul_eq hh hconst (fun g hg_smooth hg_cpt => ?_)
  · exact this
  · have hk := key g hg_smooth hg_cpt
    have hrhs : (∫ x, g x • c) = (∫ s, g s) • c := integral_smul_const g c
    exact hk.trans hrhs.symm

set_option maxHeartbeats 400000 in
-- The four-step argument (running-integral primitive, componentwise FTC and
-- absolute continuity, per-line integration by parts, and pinning the constant)
-- makes this a long elaboration, so the heartbeat budget is raised.
/-- **One-dimensional core of `W^{1,p} ⇒ ACL`.** A locally integrable
`u : ℝ → ℂ` whose one-dimensional weak derivative is the locally integrable
`u'` (the integration-by-parts identity `∫ ψ' • u = − ∫ ψ • u'` against every
smooth compactly supported `ψ : ℝ → ℝ`) agrees almost everywhere with an
absolutely continuous function whose classical derivative is `u'` almost
everywhere — concretely `x ↦ c + ∫₀ˣ u'` for a suitable constant `c`. -/
theorem exists_absolutelyContinuous_of_oneDim_weakDeriv
    {u u' : ℝ → ℂ} (hu : LocallyIntegrable u) (hu' : LocallyIntegrable u')
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ t, deriv ψ t • u t = - ∫ t, ψ t • u' t) :
    ∃ ũ : ℝ → ℂ, ũ =ᵐ[volume] u ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval ũ a b) ∧
      (∀ᵐ t : ℝ, HasDerivAt ũ (u' t) t) := by
  -- **Lipschitz ∘ AC is AC** (modelled on `hasWeakDirDeriv_one_of_aclHorizontal`).
  have hLipComp : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F Y _ l K hl a b hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- **`(continuous cpt-supp real) • (loc-integrable ℂ)` is integrable.**
  have integ : ∀ m : ℝ → ℝ, Continuous m → HasCompactSupport m →
      ∀ {h : ℝ → ℂ}, LocallyIntegrable h → Integrable (fun t => m t • h t) := by
    intro m hm hcs h hh
    have hK : IsCompact (tsupport m) := hcs
    have hhon : IntegrableOn h (tsupport m) volume := hh.integrableOn_isCompact hK
    have hon : IntegrableOn (fun t => m t • h t) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun t => m t • h t) ⊆ tsupport m := by
      intro t ht; apply subset_tsupport m
      simp only [Function.mem_support] at ht ⊢
      intro hmt; apply ht; simp [hmt]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- **Recombination: `re` AC ∧ `im` AC ⇒ ℂ-valued AC** (ε–δ bookkeeping on the
  -- bound `dist z w ≤ |z.re − w.re| + |z.im − w.im|`, modelled on `hLipComp`).
  have hACofComp : ∀ (F : ℝ → ℂ) (a b : ℝ),
      AbsolutelyContinuousOnInterval (fun x => (F x).re) a b →
      AbsolutelyContinuousOnInterval (fun x => (F x).im) a b →
      AbsolutelyContinuousOnInterval F a b := by
    intro F a b hre him
    rw [absolutelyContinuousOnInterval_iff] at hre him ⊢
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hre (ε/2) (by positivity)
    obtain ⟨δ₂, hδ₂, h₂⟩ := him (ε/2) (by positivity)
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
      _ < ε/2 + ε/2 := add_lt_add k1 k2
      _ = ε := by ring
  -- **Interval-integrability** of `u'` and its components (and local integrability
  -- of the components, for the a.e. fundamental theorem of calculus).
  have hu'II : ∀ a b : ℝ, IntervalIntegrable u' volume a b :=
    fun a b => (hu'.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hu'reII : ∀ a b : ℝ, IntervalIntegrable (fun t => (u' t).re) volume a b :=
    fun a b => ⟨Complex.reCLM.integrable_comp (hu'II a b).1,
      Complex.reCLM.integrable_comp (hu'II a b).2⟩
  have hu'imII : ∀ a b : ℝ, IntervalIntegrable (fun t => (u' t).im) volume a b :=
    fun a b => ⟨Complex.imCLM.integrable_comp (hu'II a b).1,
      Complex.imCLM.integrable_comp (hu'II a b).2⟩
  have hu'reLI : LocallyIntegrable (fun t => (u' t).re) volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk; exact Complex.reCLM.integrable_comp (hu'.integrableOn_isCompact hk)
  have hu'imLI : LocallyIntegrable (fun t => (u' t).im) volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk; exact Complex.imCLM.integrable_comp (hu'.integrableOn_isCompact hk)
  -- **The running integral** `v x = ∫₀ˣ u'`; its `re`/`im` are the component primitives.
  set v : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, u' t with hv
  have hvre : ∀ x : ℝ, (v x).re = ∫ t in (0:ℝ)..x, (u' t).re := by
    intro x
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM (hu'II 0 x)
    simpa [Complex.reCLM_apply, hv] using this.symm
  have hvim : ∀ x : ℝ, (v x).im = ∫ t in (0:ℝ)..x, (u' t).im := by
    intro x
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM (hu'II 0 x)
    simpa [Complex.imCLM_apply, hv] using this.symm
  have hv_cont : Continuous v := intervalIntegral.continuous_primitive (fun a b => hu'II a b) 0
  have hv_LI : LocallyIntegrable v := hv_cont.locallyIntegrable
  -- AC of `x ↦ ∫₀ˣ (real f)` on every `[a,b]` (basepoint shifted to `a`, plus a constant).
  have hACprim : ∀ (f : ℝ → ℝ), (∀ a b : ℝ, IntervalIntegrable f volume a b) →
      ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x => ∫ t in (0:ℝ)..x, f t) a b := by
    intro f hf a b
    have hsplit : (fun x => ∫ t in (0:ℝ)..x, f t)
        = (fun x => (∫ t in a..x, f t) + (∫ t in (0:ℝ)..a, f t)) := by
      funext x
      rw [add_comm, intervalIntegral.integral_add_adjacent_intervals (hf 0 a) (hf a x)]
    rw [hsplit]
    apply AbsolutelyContinuousOnInterval.add
    · exact (hf a b).absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
    · exact ((LipschitzWith.const' (∫ t in (0:ℝ)..a, f t)).lipschitzOnWith
        (s := Set.uIcc a b) (K := 0)).absolutelyContinuousOnInterval
  -- **Step 1a: `v` is AC on every interval** (recombine the component primitives).
  have hv_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval v a b := by
    intro a b
    refine hACofComp v a b ?_ ?_
    · rw [show (fun x => (v x).re) = (fun x => ∫ t in (0:ℝ)..x, (u' t).re) from funext hvre]
      exact hACprim _ hu'reII a b
    · rw [show (fun x => (v x).im) = (fun x => ∫ t in (0:ℝ)..x, (u' t).im) from funext hvim]
      exact hACprim _ hu'imII a b
  -- **Step 1b: a.e. `HasDerivAt v (u' t) t`** (Lebesgue differentiation, componentwise).
  have hv_deriv : ∀ᵐ t : ℝ, HasDerivAt v (u' t) t := by
    have hre := LocallyIntegrable.ae_hasDerivAt_integral hu'reLI
    have him := LocallyIntegrable.ae_hasDerivAt_integral hu'imLI
    filter_upwards [hre, him] with t htre htim
    have h1 : HasDerivAt (fun x => (v x).re) ((u' t).re) t := by
      rw [show (fun x => (v x).re) = (fun x => ∫ s in (0:ℝ)..x, (u' s).re) from funext hvre]
      exact htre 0
    have h2 : HasDerivAt (fun x => (v x).im) ((u' t).im) t := by
      rw [show (fun x => (v x).im) = (fun x => ∫ s in (0:ℝ)..x, (u' s).im) from funext hvim]
      exact htim 0
    have heq : v = fun x => (↑(v x).re : ℂ) + (↑(v x).im : ℂ) * Complex.I := by
      funext x; exact (Complex.re_add_im (v x)).symm
    rw [heq, show u' t = (↑(u' t).re + ↑(u' t).im * Complex.I : ℂ) from
      (Complex.re_add_im (u' t)).symm]
    have hh3 : HasDerivAt (fun x => (↑(v x).im : ℂ) * Complex.I) (↑(u' t).im * Complex.I) t :=
      h2.ofReal_comp.mul_const Complex.I
    exact h1.ofReal_comp.add hh3
  -- **Step 2: `v` has the same weak derivative `u'`** (one-dimensional IBP for AC
  -- functions on `[−R, R] ⊇ supp Φ`, componentwise through `reCLM`/`imCLM`; the
  -- boundary terms vanish since `Φ` has compact support — modelled on the `lineIBP`
  -- block of `hasWeakDirDeriv_one_of_aclHorizontal`).
  have hweakv : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ t, deriv ψ t • v t = - ∫ t, ψ t • u' t := by
    intro Φ hΦ_smooth hΦ_cpt
    have hintL : Integrable (fun t => deriv Φ t • v t) :=
      integ (deriv Φ) (hΦ_smooth.continuous_deriv (by norm_num)) hΦ_cpt.deriv hv_LI
    have hintR : Integrable (fun t => Φ t • u' t) :=
      integ Φ hΦ_smooth.continuous hΦ_cpt hu'
    obtain ⟨KΦ, hKΦ⟩ := hΦ_smooth.lipschitzWith_of_hasCompactSupport hΦ_cpt (by norm_num)
    have hΦ_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Φ a b :=
      fun a b => (hKΦ.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
    obtain ⟨R, hR, hRsupp⟩ := hΦ_cpt.exists_pos_le_norm
    have hΦa : Φ (-R) = 0 := hRsupp (-R) (by rw [norm_neg, Real.norm_eq_abs, abs_of_pos hR])
    have hΦb : Φ R = 0 := hRsupp R (by rw [Real.norm_eq_abs, abs_of_pos hR])
    have hΦ_zero : ∀ t ∉ Set.Icc (-R) R, Φ t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
      · exact hRsupp t (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
    have hdΦ_zero : ∀ t ∉ Set.Icc (-R) R, deriv Φ t = 0 := by
      intro t ht
      have hne : Φ =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < -R from h)] with x hx
          rw [Set.mem_Iio] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
        · filter_upwards [Ioi_mem_nhds (show R < t from h)] with x hx
          rw [Set.mem_Ioi] at hx
          exact hRsupp x (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
      rw [Filter.EventuallyEq.deriv_eq hne]; simp
    have compIBP : ∀ proj : ℂ →L[ℝ] ℝ,
        (∫ t, deriv Φ t * proj (v t)) = - ∫ t, Φ t * proj (u' t) := by
      intro proj
      have hab : (-R) ≤ R := by linarith
      set Fr : ℝ → ℝ := fun t => proj (v t) with hFr
      set Gr : ℝ → ℝ := fun t => proj (u' t) with hGr
      have hFr_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Fr a b :=
        fun a b => hLipComp proj ‖proj‖₊ proj.lipschitz (hv_ac a b)
      have hFr_deriv : ∀ᵐ t : ℝ, deriv Fr t = Gr t := by
        filter_upwards [hv_deriv] with t ht
        have : HasDerivAt Fr (proj (u' t)) t := by
          have := proj.hasFDerivAt.comp_hasDerivAt t ht
          simpa [hFr, Function.comp_def] using this
        exact this.deriv
      have hIBP := (hΦ_ac (-R) R).integral_mul_deriv_eq_deriv_mul (hFr_ac (-R) R)
      rw [hΦa, hΦb] at hIBP
      simp only [zero_mul, sub_zero, zero_sub] at hIBP
      have hIBP2 : (∫ x in (-R)..R, Φ x * Gr x) = - ∫ x in (-R)..R, deriv Φ x * Fr x := by
        rw [← hIBP]; apply intervalIntegral.integral_congr_ae
        filter_upwards [hFr_deriv] with x hx _; rw [hx]
      have hconvL : (∫ x in (-R)..R, Φ x * Gr x) = ∫ x, Φ x * Gr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hΦ_zero t ht, zero_mul])
      have hconvR : (∫ x in (-R)..R, deriv Φ x * Fr x) = ∫ x, deriv Φ x * Fr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hdΦ_zero t ht, zero_mul])
      rw [hconvL, hconvR] at hIBP2
      change (∫ t, deriv Φ t * Fr t) = - ∫ t, Φ t * Gr t
      rw [hIBP2, neg_neg]
    apply Complex.ext
    · have hreL : (∫ t, (deriv Φ t) • v t).re = ∫ t, deriv Φ t * (v t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintL
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      have hreR : (∫ t, Φ t • u' t).re = ∫ t, Φ t * (u' t).re := by
        have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hintR
        simpa [Complex.reCLM_apply, Complex.smul_re] using this.symm
      rw [hreL, Complex.neg_re, hreR]; exact compIBP Complex.reCLM
    · have himL : (∫ t, (deriv Φ t) • v t).im = ∫ t, deriv Φ t * (v t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintL
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      have himR : (∫ t, Φ t • u' t).im = ∫ t, Φ t * (u' t).im := by
        have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hintR
        simpa [Complex.imCLM_apply, Complex.smul_im] using this.symm
      rw [himL, Complex.neg_im, himR]; exact compIBP Complex.imCLM
  -- **Step 3: `u − v` has vanishing weak derivative** (subtract the two identities).
  have hweakdiff : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ t, deriv ψ t • (u t - v t) = 0 := by
    intro Φ hΦ_smooth hΦ_cpt
    have hi1 : Integrable (fun t => deriv Φ t • u t) :=
      integ (deriv Φ) (hΦ_smooth.continuous_deriv (by norm_num)) hΦ_cpt.deriv hu
    have hi2 : Integrable (fun t => deriv Φ t • v t) :=
      integ (deriv Φ) (hΦ_smooth.continuous_deriv (by norm_num)) hΦ_cpt.deriv hv_LI
    have hpoint : ∀ t, deriv Φ t • (u t - v t) = deriv Φ t • u t - deriv Φ t • v t :=
      fun t => smul_sub _ _ _
    rw [show (fun t => deriv Φ t • (u t - v t))
        = (fun t => deriv Φ t • u t - deriv Φ t • v t) from funext hpoint,
      integral_sub hi1 hi2, hweak Φ hΦ_smooth hΦ_cpt, hweakv Φ hΦ_smooth hΦ_cpt, sub_self]
  -- **Step 4: pin the constant and assemble** `ũ := v + c`.
  have hdiff_LI : LocallyIntegrable (fun t => u t - v t) := hu.sub hv_LI
  obtain ⟨c, hc⟩ := ae_eq_const_of_oneDim_weakDeriv_zero hdiff_LI hweakdiff
  refine ⟨fun x => v x + c, ?_, ?_, ?_⟩
  · filter_upwards [hc] with t ht
    show v t + c = u t; rw [← ht]; ring
  · intro a b
    have hcAC : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
      ((LipschitzWith.const' c).lipschitzOnWith (s := Set.uIcc a b)
        (K := 0)).absolutelyContinuousOnInterval
    exact (hv_ac a b).add hcAC
  · filter_upwards [hv_deriv] with t ht; exact ht.add_const c

set_option maxHeartbeats 400000 in
-- The convolution-with-parameter smoothness, the running-integral value identity,
-- and the basepoint splitting make this a long elaboration, so the heartbeat
-- budget is raised.
open Set Function in
open scoped Convolution in
/-- **Joint smoothness of a parametric `x`-primitive.** For a jointly smooth,
compactly supported `w : ℝ × ℝ → ℝ`, the partial primitive
`(x, y) ↦ ∫ t in a..x, w t y` is jointly `C^∞`. The primitive equals a difference
of convolutions with the Heaviside indicator,
`(𝟙_{[0,∞)} ⋆ w(·, y))(x) − (𝟙_{[0,∞)} ⋆ w(·, y))(a)`, which is jointly smooth by
`MeasureTheory.contDiffOn_convolution_right_with_param`. This supplies the smooth
two-dimensional test functions used in `exists_aclHorizontal_of_hasWeakDirDeriv_one`
(Mathlib provides only first-order differentiation under the integral, so the
`C^∞` statement is assembled here through the convolution representation). -/
theorem contDiff_intervalIntegral_primitive_fst {w : ℝ → ℝ → ℝ} (a : ℝ)
    (hw : ContDiff ℝ ∞ (fun p : ℝ × ℝ => w p.1 p.2))
    (hcw : HasCompactSupport (fun p : ℝ × ℝ => w p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ t in a..p.1, w t p.2) := by
  set W : ℝ × ℝ → ℝ := fun p => w p.1 p.2 with hW
  set H : ℝ → ℝ := Set.indicator (Set.Ici 0) (fun _ => 1) with hH
  set Lsm : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLsm
  have H_locint : LocallyIntegrable H volume :=
    (locallyIntegrable_const (1:ℝ)).indicator measurableSet_Ici
  set Φc : ℝ → ℝ → ℝ := fun x y => (H ⋆[Lsm, volume] (fun s => w s y)) x with hΦc
  -- **Step 1: joint smoothness of `Φc`** (the convolution-with-parameter lemma,
  -- with the parameter `y` in the first slot and convolution point `x` in the
  -- second; recover `(x, y)` order by post-composing with the coordinate swap).
  have hΦc_cd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φc p.1 p.2) := by
    have hk'_cpt : IsCompact (Prod.fst '' (tsupport W)) := hcw.isCompact.image continuous_fst
    have hswap : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
        (H ⋆[Lsm, volume] (fun x => W (x, q.1))) q.2) ((univ : Set ℝ) ×ˢ univ) := by
      refine MeasureTheory.contDiffOn_convolution_right_with_param (n := (⊤ : ℕ∞))
        Lsm (P := ℝ) (G := ℝ) (g := fun (y:ℝ) (x:ℝ) => W (x, y))
        isOpen_univ hk'_cpt ?_ H_locint ?_
      · intro y x _ hx
        by_contra hne
        apply hx
        have : (x, y) ∈ tsupport W := subset_tsupport W (by simp [Function.mem_support, hne])
        exact ⟨(x,y), this, rfl⟩
      · have he : (↿(fun (y:ℝ) (x:ℝ) => W (x, y))) = fun q : ℝ × ℝ => W (q.2, q.1) := rfl
        rw [he]
        exact (hw.comp ((contDiff_snd).prodMk contDiff_fst)).contDiffOn
    have heq1 : (fun q : ℝ × ℝ =>
        (H ⋆[Lsm, volume] (fun x => W (x, q.1))) q.2) = (fun q : ℝ × ℝ => Φc q.2 q.1) := by
      funext q; rfl
    rw [heq1, univ_prod_univ] at hswap
    have hcd : ContDiff ℝ ∞ (fun q : ℝ × ℝ => Φc q.2 q.1) := contDiffOn_univ.mp hswap
    have hsw : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1)) :=
      contDiff_snd.prodMk contDiff_fst
    have : (fun p : ℝ × ℝ => Φc p.1 p.2)
        = (fun q : ℝ × ℝ => Φc q.2 q.1) ∘ (fun p : ℝ × ℝ => (p.2, p.1)) := by
      funext p; rfl
    rw [this]
    exact hcd.comp hsw
  -- **Step 2: value identity.** From the compact support get a radius `R` with
  -- `w t y = 0` once `R ≤ |t|`; below the `t`-support (`aL := -R-1`) the running
  -- integral equals the convolution value `Φc`.
  obtain ⟨R, hR, hRsupp⟩ := hcw.exists_pos_le_norm
  have hgsupp : ∀ t y : ℝ, R ≤ |t| → w t y = 0 := by
    intro t y ht
    have : R ≤ ‖((t, y) : ℝ × ℝ)‖ := by
      refine le_trans ?_ (norm_fst_le (t, y))
      rw [Real.norm_eq_abs]; exact ht
    exact hRsupp (t, y) this
  set aL : ℝ := -R - 1 with haL
  have hwcontslice : ∀ y, Continuous (fun t => w t y) :=
    fun y => hw.continuous.comp (continuous_id.prodMk continuous_const)
  have hval : ∀ x y : ℝ, (∫ t in aL..x, w t y) = Φc x y := by
    intro x y
    have hsub_aL : aL ≤ -R := by rw [haL]; linarith
    have hgsy : ∀ s, R ≤ |s| → w s y = 0 := fun s hs => hgsupp s y hs
    change (∫ t in aL..x, w t y) = (H ⋆[Lsm, volume] (fun s => w s y)) x
    by_cases hxle : aL ≤ x
    · rw [convolution_def]
      simp only [hLsm, ContinuousLinearMap.lsmul_apply, hH]
      rw [show (fun t => Set.indicator (Ici (0:ℝ)) (fun _ => (1:ℝ)) t • w (x - t) y)
            = Set.indicator (Ici (0:ℝ)) (fun t => w (x - t) y) from
            by funext t; by_cases ht : t ∈ Ici (0:ℝ) <;> simp [Set.indicator, ht]]
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
      have hge : (0:ℝ) ≤ x - aL := by linarith
      change (∫ s in aL..x, w s y) = _
      have h1 : (∫ s in aL..x, w s y) = ∫ t in (0:ℝ)..(x - aL), w (x - t) y := by
        rw [intervalIntegral.integral_comp_sub_left (fun s => w s y) x]; congr 1 <;> ring
      rw [h1, intervalIntegral.integral_of_le hge,
          ← MeasureTheory.integral_indicator measurableSet_Ioc,
          ← MeasureTheory.integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      have hzero : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
      filter_upwards [hzero] with t ht
      rcases lt_or_gt_of_ne ht with h0 | h0
      · have hnIoc : t ∉ Ioc (0:ℝ) (x - aL) := by
          simp only [Set.mem_Ioc, not_and, not_le]; intro hh; linarith
        have hnIci : t ∉ Ici (0:ℝ) := by simp only [Set.mem_Ici, not_le]; linarith
        rw [Set.indicator_of_notMem hnIoc, Set.indicator_of_notMem hnIci]
      · rcases le_or_gt t (x - aL) with hb | hb
        · rw [Set.indicator_of_mem (show t ∈ Ioc (0:ℝ) (x-aL) from ⟨h0, hb⟩),
              Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from le_of_lt h0)]
        · have hz : w (x - t) y = 0 := hgsy _ (by rw [abs_of_neg (by linarith)]; linarith)
          have hnIoc : t ∉ Ioc (0:ℝ) (x - aL) := by
            simp only [Set.mem_Ioc, not_and, not_le]; intro _; linarith
          rw [Set.indicator_of_notMem hnIoc,
              Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from le_of_lt h0), hz]
    · rw [not_le] at hxle
      change (∫ s in aL..x, w s y) = _
      have hΨ0 : (∫ s in aL..x, w s y) = 0 := by
        rw [intervalIntegral.integral_symm, neg_eq_zero]
        apply intervalIntegral.integral_zero_ae
        filter_upwards with t ht
        rw [Set.uIoc_of_le hxle.le, Set.mem_Ioc] at ht
        have : t ≤ aL := ht.2
        exact hgsy t (by rw [abs_of_neg (by linarith)]; linarith)
      rw [hΨ0]
      rw [convolution_def]
      simp only [hLsm, ContinuousLinearMap.lsmul_apply, hH]
      rw [show (fun t => Set.indicator (Ici (0:ℝ)) (fun _ => (1:ℝ)) t • w (x - t) y)
            = Set.indicator (Ici (0:ℝ)) (fun t => w (x - t) y) from
            by funext t; by_cases ht : t ∈ Ici (0:ℝ) <;> simp [Set.indicator, ht]]
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
      symm
      apply MeasureTheory.integral_eq_zero_of_ae
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Ici (0:ℝ), self_mem_ae_restrict measurableSet_Ici, ?_⟩
      intro t ht
      rw [Set.mem_Ici] at ht
      exact hgsy (x - t) (by rw [abs_of_neg (by linarith)]; linarith)
  -- **Step 2b: general basepoint `a`** by splitting `∫ aL..x = ∫ aL..a + ∫ a..x`
  -- (the slice `w(·, y)` is continuous, hence interval-integrable).
  have hval_a : ∀ x y : ℝ, (∫ t in a..x, w t y) = Φc x y - Φc a y := by
    intro x y
    have hII : ∀ p q : ℝ, IntervalIntegrable (fun t => w t y) volume p q :=
      fun p q => (hwcontslice y).intervalIntegrable p q
    have hsplit : (∫ t in aL..x, w t y)
        = (∫ t in aL..a, w t y) + (∫ t in a..x, w t y) :=
      (intervalIntegral.integral_add_adjacent_intervals (hII aL a) (hII a x)).symm
    have hrw : (∫ t in a..x, w t y) = (∫ t in aL..x, w t y) - (∫ t in aL..a, w t y) := by
      rw [hsplit]; ring
    rw [hrw, hval x y, hval a y]
  -- **Step 3: conclude.** The primitive is the difference of two jointly smooth
  -- maps: `(x, y) ↦ Φc x y` (Step 1) and `(x, y) ↦ Φc a y` (Step 1 ∘ fixing `x = a`).
  have hfun : (fun p : ℝ × ℝ => ∫ t in a..p.1, w t p.2)
      = (fun p : ℝ × ℝ => Φc p.1 p.2 - Φc a p.2) := by
    funext p; exact hval_a p.1 p.2
  rw [hfun]
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φc a p.2) := by
    have : (fun p : ℝ × ℝ => Φc a p.2)
        = (fun q : ℝ × ℝ => Φc q.1 q.2) ∘ (fun p : ℝ × ℝ => (a, p.2)) := by
      funext p; rfl
    rw [this]
    exact hΦc_cd.comp (contDiff_const.prodMk contDiff_snd)
  exact hΦc_cd.sub h2

end NoWanderingDomains
