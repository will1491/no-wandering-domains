/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.AbsolutelyContinuousLines

/-!
# `W^{1,p}_loc ⇒ ACL`: the two-dimensional representative

This file completes the `Sobolev ⇒ ACL` (absolutely-continuous-on-lines) converse
on `ℂ`, lifting the one-dimensional core of
`NoWanderingDomains.Analysis.Sobolev.AbsolutelyContinuousLines`
(`exists_absolutelyContinuous_of_oneDim_weakDeriv` together with the
parametric-primitive smoothness `contDiff_intervalIntegral_primitive_fst`) to the
two-dimensional representative theorems on almost every line.

## Main results

* `exists_aclHorizontal_of_hasWeakDirDeriv_one` — if `gx` is the weak
  `x`-directional derivative of a locally integrable `f`, then `f` has a
  representative `f' =ᵐ f` that is absolutely continuous on almost every
  horizontal line with `x`-partial `gx`;
* `exists_aclVertical_of_hasWeakDirDeriv_I` — the vertical analogue, reduced to the
  horizontal one through the measure-preserving real/imaginary coordinate swap.

The horizontal theorem builds an explicit representative
`f'⟨x,y⟩ = ∫₀ˣ gx⟨t,y⟩ + k y` from the partial primitive of `gx` and identifies it
with `f` almost everywhere by testing the two-dimensional weak-derivative identity
against smooth `x`-primitives (`contDiff_intervalIntegral_primitive_fst`) and
`MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
-/

open MeasureTheory Complex
open scoped ENNReal ContDiff

namespace NoWanderingDomains

variable {f g gx gy : ℂ → ℂ}

set_option maxHeartbeats 400000 in
-- The full converse assembles the representative `f'`, its line-by-line absolute
-- continuity, and the two-dimensional weak-derivative identity tested against
-- smooth `x`-primitives, so the elaboration is long and the heartbeat budget is raised.
open Set Function in
open scoped Convolution in
/-- **`W^{1,p} ⇒ AC on horizontal lines` (converse of
`hasWeakDirDeriv_one_of_aclHorizontal`).** If `gx` is the weak `x`-directional
derivative of a locally integrable `f`, then `f` has a representative `f' =ᵐ f`
that is absolutely continuous on almost every horizontal line with `x`-partial
`gx`. Proof: an explicit representative `f'⟨x,y⟩ = ∫₀ˣ gx⟨t,y⟩ + k y` is built from
the partial primitive of `gx`; that it agrees with `f` almost everywhere follows
from the two-dimensional weak-derivative identity tested against smooth
`x`-primitives (`contDiff_intervalIntegral_primitive_fst`) and
`MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
theorem exists_aclHorizontal_of_hasWeakDirDeriv_one
    (hf : LocallyIntegrable f) (hgx : LocallyIntegrable gx)
    (h : HasWeakDirDeriv 1 gx f Set.univ) :
    ∃ f' : ℂ → ℂ, f' =ᵐ[volume] f ∧ ACLHorizontal f' gx := by
  -- ============================ GENERIC HELPERS ============================
  -- Lipschitz ∘ AC is AC.
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
  -- Recombination re∧im AC ⇒ ℂ AC.
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
        ≤ dist ((F (E.2 i).1).re) ((F (E.2 i).2).re) + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) :=
          by
      intro i
      rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
      calc ‖F (E.2 i).1 - F (E.2 i).2‖
          ≤ |(F (E.2 i).1 - F (E.2 i).2).re| + |(F (E.2 i).1 - F (E.2 i).2).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = |(F (E.2 i).1).re - (F (E.2 i).2).re| + |(F (E.2 i).1).im - (F (E.2 i).2).im| := by
            rw [Complex.sub_re, Complex.sub_im]
    calc ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2)
        ≤ ∑ i ∈ Finset.range E.1, (dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
            + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im)) := Finset.sum_le_sum (fun i _ => hbound i)
      _ = (∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).re) ((F (E.2 i).2).re))
            + ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) := by
            rw [Finset.sum_add_distrib]
      _ < ε/2 + ε/2 := add_lt_add k1 k2
      _ = ε := by ring
  -- AC of a real running-integral primitive on every interval.
  have hACprim : ∀ (φ : ℝ → ℝ), (∀ a b : ℝ, IntervalIntegrable φ volume a b) →
      ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x => ∫ t in (0:ℝ)..x, φ t) a b := by
    intro φ hφ a b
    have hsplit : (fun x => ∫ t in (0:ℝ)..x, φ t)
        = (fun x => (∫ t in a..x, φ t) + (∫ t in (0:ℝ)..a, φ t)) := by
      funext x; rw [add_comm, intervalIntegral.integral_add_adjacent_intervals (hφ 0 a) (hφ a x)]
    rw [hsplit]
    apply AbsolutelyContinuousOnInterval.add
    · exact (hφ a b).absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
    · exact ((LipschitzWith.const' (∫ t in (0:ℝ)..a, φ t)).lipschitzOnWith
        (s := Set.uIcc a b) (K := 0)).absolutelyContinuousOnInterval
  -- The lineIBP block.
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
      intro t ht; rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
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
          simpa [hFr, Function.comp_def] using! this
        exact this.deriv
      have hIBP := (hΦ_ac (-R) R).integral_mul_deriv_eq_deriv_mul (hFr_ac (-R) R)
      rw [hΦa, hΦb] at hIBP
      simp only [zero_mul, sub_zero, zero_sub] at hIBP
      have hIBP2 : (∫ x in (-R)..R, Φ x * Gr x) = - ∫ x in (-R)..R, deriv Φ x * Fr x := by
        rw [← hIBP]; apply intervalIntegral.integral_congr_ae
        filter_upwards [hFr_deriv] with x hx _; rw [hx]
      have hconvL : (∫ x in (-R)..R, Φ x * Gr x) = ∫ x, Φ x * Gr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
          rw [hΦ_zero t ht, zero_mul])
      have hconvR : (∫ x in (-R)..R, deriv Φ x * Fr x) = ∫ x, deriv Φ x * Fr x := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
          rw [hdΦ_zero t ht, zero_mul])
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
  -- Loc-integrable transfer ℂ → ℝ×ℝ.
  have slice_locint : ∀ (G : ℂ → ℂ), LocallyIntegrable G →
      LocallyIntegrable (fun p : ℝ × ℝ => G ⟨p.1, p.2⟩) volume := by
    intro G hG
    rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
    set e := Complex.measurableEquivRealProd
    have hmpsymm : MeasurePreserving e.symm (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      (Complex.volume_preserving_equiv_real_prod).symm e
    have hcont : Continuous (e.symm : ℝ × ℝ → ℂ) := by
      have : (e.symm : ℝ × ℝ → ℂ) = (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) := by
        ext p
        simp [e, Complex.measurableEquivRealProd, Complex.equivRealProdCLM]
      rw [this]; exact Complex.equivRealProdCLM.symm.continuous
    have himg : IsCompact (e.symm '' K) := hK.image hcont
    have hGon : IntegrableOn G (e.symm '' K) volume := hG.integrableOn_isCompact himg
    have hmeas : MeasurableEmbedding e.symm := e.symm.measurableEmbedding
    have key : IntegrableOn (G ∘ e.symm) (e.symm ⁻¹' (e.symm '' K)) volume :=
      (hmpsymm.integrableOn_comp_preimage hmeas).mpr hGon
    rw [e.symm.injective.preimage_image] at key; exact key
  -- a.e.-y slice interval integrability from joint loc-integrability.
  have ae_slice_II : ∀ (G : ℝ × ℝ → ℂ), LocallyIntegrable G volume →
      ∀ᵐ y : ℝ, ∀ a b : ℝ, IntervalIntegrable (fun x => G (x, y)) volume a b := by
    intro G hG
    have hslice' : ∀ n : ℕ, ∀ᵐ y : ℝ, y ∈ Icc (-(n:ℝ)) n →
        IntegrableOn (fun x => G (x, y)) (Icc (-(n:ℝ)) n) volume := by
      intro n
      have hbox : Integrable G ((volume.restrict (Icc (-(n:ℝ)) n)).prod
          (volume.restrict (Icc (-(n:ℝ)) n))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact hG.integrableOn_isCompact (isCompact_Icc.prod isCompact_Icc)
      have := hbox.prod_left_ae
      rw [ae_restrict_iff' measurableSet_Icc] at this; exact this
    rw [← ae_all_iff] at hslice'
    filter_upwards [hslice'] with y hy a b
    obtain ⟨n, hn⟩ := exists_nat_ge (max (max (|a|) (|b|)) (|y|) + 1)
    have h1 := le_max_left (max (|a|) (|b|)) (|y|)
    have h2 := le_max_right (max (|a|) (|b|)) (|y|)
    have h3 := le_max_left (|a|) (|b|)
    have h4 := le_max_right (|a|) (|b|)
    have ha : |a| ≤ n := by linarith
    have hb : |b| ≤ n := by linarith
    have hyb : |y| ≤ n := by linarith
    rw [abs_le] at ha hb hyb
    have hyn : y ∈ Icc (-(n:ℝ)) n := ⟨hyb.1, hyb.2⟩
    have hint := hy n hyn
    have hsub : uIcc a b ⊆ Icc (-(n:ℝ)) n := by
      intro t ht; rw [Set.mem_uIcc] at ht; rw [Set.mem_Icc]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [intervalIntegrable_iff]
    exact hint.mono_set (le_trans Set.uIoc_subset_uIcc hsub)
  -- interval-integrable on all intervals ⇒ loc-integrable on ℝ.
  have II_all_LI : ∀ (φ : ℝ → ℂ), (∀ a b : ℝ, IntervalIntegrable φ volume a b) →
      LocallyIntegrable φ volume := by
    intro φ hφ
    rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
    obtain ⟨a, ha⟩ := hK.bddBelow; obtain ⟨b, hb⟩ := hK.bddAbove
    have hsub : K ⊆ Icc a b := fun x hx => ⟨ha hx, hb hx⟩
    rcases le_or_gt a b with hle | hlt
    · have := (hφ a b); rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle] at this
      exact this.mono_set hsub
    · rw [Icc_eq_empty (not_le.2 hlt), subset_empty_iff] at hsub
      rw [hsub]; exact integrableOn_empty
  -- box ⇒ general K local integrability.
  have box_LI : ∀ (F : ℝ × ℝ → ℂ),
      (∀ a b c d : ℝ, IntegrableOn F (Set.Icc a b ×ˢ Set.Icc c d) (volume.prod volume)) →
      LocallyIntegrable F (volume.prod volume) := by
    intro F hbox
    rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
    obtain ⟨a, ha⟩ := (hK.image continuous_fst).bddBelow
    obtain ⟨b, hb⟩ := (hK.image continuous_fst).bddAbove
    obtain ⟨c, hc⟩ := (hK.image continuous_snd).bddBelow
    obtain ⟨d, hd⟩ := (hK.image continuous_snd).bddAbove
    have hsub : K ⊆ Set.Icc a b ×ˢ Set.Icc c d := fun p hp =>
      ⟨⟨ha ⟨p, hp, rfl⟩, hb ⟨p, hp, rfl⟩⟩, hc ⟨p, hp, rfl⟩, hd ⟨p, hp, rfl⟩⟩
    rw [← Measure.volume_eq_prod] at *
    exact (hbox a b c d).mono_set hsub
  -- transfer integrals/integrability ℂ ↔ ℝ×ℝ.
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
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => W ⟨p.1, p.2⟩) volume := by
      have := hW.aestronglyMeasurable.comp_quasiMeasurePreserving hmpsymm.quasiMeasurePreserving
      exact this
    rw [← hmp.integrable_comp hmeas]; exact hW
  -- (cont cpt-supp real) • (loc-int ℂ) integrable on ℂ.
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m →
      ∀ {hh : ℂ → ℂ}, LocallyIntegrable hh → Integrable (fun z => m z • hh z) := by
    intro m hm hcs hh hhh
    have hK : IsCompact (tsupport m) := hcs
    have hhon : IntegrableOn hh (tsupport m) volume := hhh.integrableOn_isCompact hK
    have hon : IntegrableOn (fun z => m z • hh z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • hh z) ⊆ tsupport m := by
      intro z hz; apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- ============================ SETUP OF OBJECTS ============================
  -- mollifier η, mean one.
  set bη : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hbη
  set η : ℝ → ℝ := bη.normed volume with hη
  have hη_smooth : ContDiff ℝ ∞ η := bη.contDiff_normed (n := ⊤)
  have hη_cpt : HasCompactSupport η := bη.hasCompactSupport_normed
  have hη_cont : Continuous η := hη_smooth.continuous
  have hη_int : ∫ t, η t = 1 := bη.integral_normed
  obtain ⟨Rη, hRη, hRηsupp⟩ := hη_cpt.exists_pos_le_norm
  have hηsupp : ∀ x, Rη ≤ |x| → η x = 0 :=
    fun x hx => hRηsupp x (by rw [Real.norm_eq_abs]; exact hx)
  -- strongly-measurable modification gx₀ =ᵐ gx.
  set gx0 : ℂ → ℂ := hgx.aestronglyMeasurable.mk gx with hgx0
  have hgx0_sm : StronglyMeasurable gx0 := hgx.aestronglyMeasurable.stronglyMeasurable_mk
  have hgx0_eq : gx0 =ᵐ[volume] gx := hgx.aestronglyMeasurable.ae_eq_mk.symm
  have hgx0_li : LocallyIntegrable gx0 := hgx.congr hgx0_eq.symm
  -- D, k, f'.
  set D : ℝ → ℝ → ℂ := fun x y => ∫ t in (0:ℝ)..x, gx0 ⟨t, y⟩ with hD
  set k : ℝ → ℂ := fun y => ∫ x, η x • (f ⟨x, y⟩ - D x y) with hk
  set f' : ℂ → ℂ := fun z => D z.re z.im + k z.im with hf'
  have hgx0_slice : ∀ᵐ y : ℝ, ∀ a b : ℝ, IntervalIntegrable (fun x => gx0 ⟨x, y⟩) volume a b :=
    ae_slice_II _ (slice_locint gx0 hgx0_li)
  refine ⟨f', ?_, ?_⟩
  · -- ======================= GOAL 2: f' =ᵐ f =======================
    have hfli : LocallyIntegrable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩) volume := slice_locint f hf
    have hgx0li2 : LocallyIntegrable (fun p : ℝ × ℝ => gx0 ⟨p.1, p.2⟩) volume :=
      slice_locint gx0 hgx0_li
    -- D aestrongly measurable
    have hD_sm : AEStronglyMeasurable (fun p : ℝ × ℝ => D p.1 p.2) (volume.prod volume) := by
      rw [hD]
      have hbase : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => gx0 ⟨q.2, q.1.2⟩) := by
        apply hgx0_sm.comp_measurable
        have : (fun q : (ℝ × ℝ) × ℝ => (⟨q.2, q.1.2⟩ : ℂ))
            = fun q => Complex.equivRealProdCLM.symm (q.2, q.1.2) := by funext q; rfl
        rw [this]
        exact Complex.equivRealProdCLM.symm.continuous.measurable.comp
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
      have hS1 : MeasurableSet {q : (ℝ × ℝ) × ℝ | 0 < q.2 ∧ q.2 ≤ q.1.1} :=
        (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
      have hS2 : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 < q.2 ∧ q.2 ≤ 0} :=
        (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
      have hf1 : AEStronglyMeasurable
          (fun q : (ℝ × ℝ) × ℝ => (Set.Ioc (0:ℝ) q.1.1).indicator (fun t => gx0 ⟨t, q.1.2⟩) q.2)
          ((volume.prod volume).prod volume) := by
        have : (fun q : (ℝ × ℝ) × ℝ => (Set.Ioc (0:ℝ) q.1.1).indicator (fun t => gx0 ⟨t,
          q.1.2⟩) q.2)
            = {q : (ℝ × ℝ) × ℝ | 0 < q.2 ∧ q.2 ≤ q.1.1}.indicator (fun q => gx0 ⟨q.2, q.1.2⟩) := by
          funext q; simp only [Set.indicator_apply, Set.mem_Ioc, Set.mem_ofPred_eq]
        rw [this]; exact (hbase.indicator hS1).aestronglyMeasurable
      have hf2 : AEStronglyMeasurable
          (fun q : (ℝ × ℝ) × ℝ => (Set.Ioc q.1.1 (0:ℝ)).indicator (fun t => gx0 ⟨t, q.1.2⟩) q.2)
          ((volume.prod volume).prod volume) := by
        have : (fun q : (ℝ × ℝ) × ℝ => (Set.Ioc q.1.1 (0:ℝ)).indicator (fun t => gx0 ⟨t,
          q.1.2⟩) q.2)
            = {q : (ℝ × ℝ) × ℝ | q.1.1 < q.2 ∧ q.2 ≤ 0}.indicator (fun q => gx0 ⟨q.2, q.1.2⟩) := by
          funext q; simp only [Set.indicator_apply, Set.mem_Ioc, Set.mem_ofPred_eq]
        rw [this]; exact (hbase.indicator hS2).aestronglyMeasurable
      have hI1 := hf1.integral_prod_right'
      have hI2 := hf2.integral_prod_right'
      have hsplit : (fun p : ℝ × ℝ => ∫ t in (0:ℝ)..p.1, gx0 ⟨t, p.2⟩)
          = (fun p : ℝ × ℝ => (∫ t, (Set.Ioc (0:ℝ) p.1).indicator (fun t => gx0 ⟨t, p.2⟩) t)
                              - (∫ t, (Set.Ioc p.1 (0:ℝ)).indicator (fun t => gx0 ⟨t, p.2⟩) t)) :=
                                by
        funext p
        rw [intervalIntegral, integral_indicator measurableSet_Ioc,
          integral_indicator measurableSet_Ioc]
      rw [hsplit]; exact hI1.sub hI2
    -- D loc-integrable
    have hD_li : LocallyIntegrable (fun p : ℝ × ℝ => D p.1 p.2) (volume.prod volume) := by
      apply box_LI
      intro a b c d
      rw [hD]
      set M : ℝ := max (max (|a|) (|b|)) 1 with hM
      have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
      have hMa : |a| ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      have hMb : |b| ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      have hbox : Integrable (fun p : ℝ × ℝ => gx0 ⟨p.1, p.2⟩)
          ((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc c d))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← MeasureTheory.IntegrableOn]
        exact hgx0li2.integrableOn_isCompact (isCompact_Icc.prod isCompact_Icc)
      have hB : Integrable (fun y => ∫ x in Set.Icc (-M) M, ‖gx0 ⟨x, y⟩‖)
          (volume.restrict (Set.Icc c d)) := hbox.norm.integral_prod_right
      have hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
      have hBbox : Integrable (fun p : ℝ × ℝ => ∫ x in Set.Icc (-M) M, ‖gx0 ⟨x, p.2⟩‖)
          ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) :=
        hB.comp_snd (volume.restrict (Set.Icc a b))
      have hsl0 : ∀ᵐ y ∂(volume.restrict (Set.Icc c d)),
          IntegrableOn (fun x => gx0 ⟨x, y⟩) (Set.Icc (-M) M) volume := hbox.prod_left_ae
      have hsliceBox : ∀ᵐ p ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))),
          IntegrableOn (fun x => gx0 ⟨x, p.2⟩) (Set.Icc (-M) M) volume :=
        Measure.quasiMeasurePreserving_snd.ae hsl0
      have hp1 : ∀ᵐ p ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))),
          p.1 ∈ Set.Icc a b :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
      have hDsm' : AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ t in (0:ℝ)..p.1, gx0 ⟨t, p.2⟩)
          (volume.prod volume) := by rw [hD] at hD_sm; exact hD_sm
      rw [MeasureTheory.IntegrableOn, ← Measure.prod_restrict]
      apply Integrable.mono' hBbox (by rw [Measure.prod_restrict]; exact hDsm'.restrict)
      filter_upwards [hsliceBox, hp1] with p hpslice hp1mem
      have hsub : Set.uIoc (0:ℝ) p.1 ⊆ Set.Icc (-M) M := by
        rw [Set.mem_Icc] at hp1mem; rw [abs_le] at hMa hMb
        have hp1M : p.1 ∈ Set.Icc (-M) M := by
          rw [Set.mem_Icc]; constructor <;> linarith [hp1mem.1, hp1mem.2]
        apply le_trans Set.uIoc_subset_uIcc
        apply Set.uIcc_subset_Icc
        · rw [Set.mem_Icc]; constructor <;> linarith
        · exact hp1M
      calc ‖∫ t in (0:ℝ)..p.1, gx0 ⟨t, p.2⟩‖
          ≤ ∫ t in Set.uIoc (0:ℝ) p.1, ‖gx0 ⟨t, p.2⟩‖ :=
            intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ x in Set.Icc (-M) M, ‖gx0 ⟨x, p.2⟩‖ :=
            setIntegral_mono_set hpslice.norm (Filter.Eventually.of_forall (fun t => norm_nonneg _))
              hsub.eventuallyLE
    -- k loc-integrable
    have hk_li : LocallyIntegrable k volume := by
      rw [hk]
      set Q : ℝ × ℝ → ℂ := fun p => f ⟨p.1, p.2⟩ - D p.1 p.2 with hQ
      have hQli : LocallyIntegrable Q (volume.prod volume) := by
        rw [hQ]
        have h1 : LocallyIntegrable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩) (volume.prod volume) := by
          rw [← Measure.volume_eq_prod]; exact hfli
        exact h1.sub hD_li
      rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
      obtain ⟨c, hc⟩ := hK.bddBelow; obtain ⟨d, hd⟩ := hK.bddAbove
      have hKsub : K ⊆ Set.Icc c d := fun y hy => ⟨hc hy, hd hy⟩
      have htrunc : ∀ y, (∫ x, η x • (f ⟨x, y⟩ - D x y)) = ∫ x in Set.Icc (-Rη) Rη, η x • Q (x,
        y) := by
        intro y
        refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Set.Icc (-Rη) Rη) (f := fun x => η x • Q (x, y)) ?_).symm
        intro x hx
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        have : η x = 0 := by
          rcases hx with hh | hh
          · exact hηsupp x (by rw [abs_of_neg (by linarith)]; linarith)
          · exact hηsupp x (by rw [abs_of_pos (by linarith)]; linarith)
        change η x • Q (x,y) = 0; rw [this]; simp
      have hWbox : Integrable (fun p : ℝ × ℝ => η p.1 • Q (p.1, p.2))
          ((volume.restrict (Set.Icc (-Rη) Rη)).prod (volume.restrict (Set.Icc c d))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← MeasureTheory.IntegrableOn]
        have hQon : IntegrableOn (fun p : ℝ × ℝ => Q p) (Set.Icc (-Rη) Rη ×ˢ Set.Icc c d)
            (volume.prod volume) := by
          rw [← Measure.volume_eq_prod]
          exact hQli.integrableOn_isCompact (isCompact_Icc.prod isCompact_Icc)
        exact hQon.continuousOn_smul (hη_cont.comp continuous_fst).continuousOn
          (isCompact_Icc.prod isCompact_Icc)
      have hkint : IntegrableOn (fun y => ∫ x in Set.Icc (-Rη) Rη, η x • Q (x, y))
          (Set.Icc c d) volume := by
        have := hWbox.integral_prod_right
        rwa [← MeasureTheory.IntegrableOn] at this
      rw [show (fun y => ∫ x, η x • (f ⟨x, y⟩ - D x y))
          = (fun y => ∫ x in Set.Icc (-Rη) Rη, η x • Q (x, y)) from funext htrunc]
      exact hkint.mono_set hKsub
    -- f' loc-integrable on ℝ×ℝ
    have hf'li : LocallyIntegrable (fun p : ℝ × ℝ => f' ⟨p.1, p.2⟩) (volume.prod volume) := by
      have he : (fun p : ℝ × ℝ => f' ⟨p.1, p.2⟩) = (fun p : ℝ × ℝ => D p.1 p.2 + k p.2) := by
        funext p; rw [hf']
      rw [he]
      refine hD_li.add ?_
      -- k∘snd loc-int: k loc-int on ℝ, lift to product (snd, finite restriction handled via box)
      apply box_LI
      intro a b c d
      have hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
      have hkbox : IntegrableOn k (Set.Icc c d) volume :=
        hk_li.integrableOn_isCompact isCompact_Icc
      rw [MeasureTheory.IntegrableOn, ← Measure.prod_restrict]
      rw [MeasureTheory.IntegrableOn] at hkbox
      exact hkbox.comp_snd (volume.restrict (Set.Icc a b))
    -- ============ THE REDUCTION via the contDiff-smul test lemma ============
    set P : ℝ × ℝ → ℂ := fun p => f ⟨p.1, p.2⟩ - f' ⟨p.1, p.2⟩ with hP
    have hPli : LocallyIntegrable P (volume.prod volume) := by
      rw [hP]
      have h1 : LocallyIntegrable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hfli
      exact h1.sub hf'li
    -- a.e. P = 0
    have hPzero : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), P p = 0 := by
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hPli
      intro Φ₀ hΦ₀_smooth hΦ₀_cpt
      -- the per-test-function identity ∫ Φ₀ • P = 0
      refine Eq.trans (integral_congr_ae (g := fun p : ℝ × ℝ =>
        (Φ₀ p : ℂ) • (f ⟨p.1, p.2⟩ - f' ⟨p.1, p.2⟩)) ?_) ?_
      · filter_upwards with p
        change Φ₀ p • P p = (Φ₀ p : ℂ) • (f ⟨p.1, p.2⟩ - f' ⟨p.1, p.2⟩)
        rw [hP]; exact Complex.coe_smul _ _
      · have hfli2 : LocallyIntegrable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩) (volume.prod volume) := by
          rw [← Measure.volume_eq_prod]; exact hfli
        have hgx0li2' : LocallyIntegrable (fun p : ℝ × ℝ => gx0 ⟨p.1, p.2⟩) (volume.prod volume) :=
          by
          rw [← Measure.volume_eq_prod]; exact hgx0li2
        have hRli : LocallyIntegrable (fun p : ℝ × ℝ => f ⟨p.1,
          p.2⟩ - D p.1 p.2) (volume.prod volume) :=
          hfli2.sub hD_li
        have hk_li2 : LocallyIntegrable (fun p : ℝ × ℝ => k p.2) (volume.prod volume) := by
          rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
          obtain ⟨a, ha⟩ := (hK.image continuous_fst).bddBelow
          obtain ⟨b, hb⟩ := (hK.image continuous_fst).bddAbove
          obtain ⟨c, hc⟩ := (hK.image continuous_snd).bddBelow
          obtain ⟨d, hd⟩ := (hK.image continuous_snd).bddAbove
          have hsub : K ⊆ Set.Icc a b ×ˢ Set.Icc c d := fun p hp =>
            ⟨⟨ha ⟨p, hp, rfl⟩, hb ⟨p, hp, rfl⟩⟩, hc ⟨p, hp, rfl⟩, hd ⟨p, hp, rfl⟩⟩
          have hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
            ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
          have hkbox : IntegrableOn k (Set.Icc c d) volume :=
            hk_li.integrableOn_isCompact isCompact_Icc
          have hh2 : IntegrableOn (fun p : ℝ × ℝ => k p.2) (Set.Icc a b ×ˢ Set.Icc c d)
              (volume.prod volume) := by
            rw [MeasureTheory.IntegrableOn, ← Measure.prod_restrict]
            rw [MeasureTheory.IntegrableOn] at hkbox
            exact hkbox.comp_snd (volume.restrict (Set.Icc a b))
          rw [← Measure.volume_eq_prod] at *
          exact hh2.mono_set hsub
        have integ2 : ∀ (m : ℝ × ℝ → ℝ), Continuous m → HasCompactSupport m →
            ∀ {H : ℝ × ℝ → ℂ}, LocallyIntegrable H (volume.prod volume) →
            Integrable (fun p => m p • H p) (volume.prod volume) := by
          intro m hm hcs H hH
          have hK : IsCompact (tsupport m) := hcs
          have hhon : IntegrableOn H (tsupport m) (volume.prod volume) :=
            hH.integrableOn_isCompact hK
          have hon : IntegrableOn (fun p => m p • H p) (tsupport m) (volume.prod volume) :=
            hhon.continuousOn_smul hm.continuousOn hK
          have hsupp : Function.support (fun p => m p • H p) ⊆ tsupport m := by
            intro z hz; apply subset_tsupport m
            simp only [Function.mem_support] at hz ⊢
            intro hmz; apply hz; simp [hmz]
          exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
        -- ======= GEOMETRY: C, w, Ψ =======
        set C : ℝ → ℝ := fun y => ∫ s, Φ₀ (s, y) with hC
        set Φ2 : ℝ → ℝ → ℝ := fun x y => Φ₀ (x, y) with hΦ2
        have hΦ2_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φ2 p.1 p.2) := by
          simpa [hΦ2] using hΦ₀_smooth
        have hΦ2_cpt : HasCompactSupport (fun p : ℝ × ℝ => Φ2 p.1 p.2) := by
          simpa [hΦ2] using hΦ₀_cpt
        obtain ⟨RΦ, hRΦ, hRΦsupp⟩ := hΦ₀_cpt.exists_pos_le_norm
        have hΦ₀supp_x : ∀ x y : ℝ, RΦ ≤ |x| → Φ₀ (x, y) = 0 := by
          intro x y hx; apply hRΦsupp
          refine le_trans ?_ (norm_fst_le (x, y)); rw [Real.norm_eq_abs]; exact hx
        have hΦ₀supp_y : ∀ x y : ℝ, RΦ ≤ |y| → Φ₀ (x, y) = 0 := by
          intro x y hx; apply hRΦsupp
          refine le_trans ?_ (norm_snd_le (x, y)); rw [Real.norm_eq_abs]; exact hx
        have hCval : ∀ y, C y = ∫ t in (-(RΦ+1))..(RΦ+1), Φ₀ (t, y) := by
          intro y;
            rw [hC, intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
          intro x hx; rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
          rcases hx with hh | hh
          · exact hΦ₀supp_x x y (by rw [abs_of_neg (by linarith)]; linarith)
          · exact hΦ₀supp_x x y (by rw [abs_of_pos (by linarith)]; linarith)
        have hCsmooth : ContDiff ℝ ∞ C := by
          have hprim : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ t in (-(RΦ+1))..p.1, Φ₀ (t, p.2)) :=
            contDiff_intervalIntegral_primitive_fst (-(RΦ+1)) hΦ2_smooth hΦ2_cpt
          have he : C = (fun p : ℝ × ℝ => ∫ t in (-(RΦ+1))..p.1, Φ₀ (t, p.2)) ∘ (fun y => (RΦ+1,
            y)) := by
            funext y; rw [hCval y]; rfl
          rw [he]; exact hprim.comp (contDiff_const.prodMk contDiff_id)
        have hCcont : Continuous C := hCsmooth.continuous
        have hCsupp_y : ∀ y : ℝ, RΦ ≤ |y| → C y = 0 := by
          intro y hy; rw [hC]
          have hz : ∀ s, Φ₀ (s, y) = 0 := fun s => hΦ₀supp_y s y hy
          simp only [hz, integral_zero]
        have hCsupp : HasCompactSupport C := by
          apply HasCompactSupport.intro (K := Set.Icc (-RΦ) RΦ) isCompact_Icc
          intro y hy; apply hCsupp_y
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
          rcases hy with hh | hh
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        set w : ℝ → ℝ → ℝ := fun x y => Φ₀ (x, y) - C y * η x with hw
        have hw_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => w p.1 p.2) := by
          rw [hw]; refine hΦ2_smooth.sub ?_
          exact (hCsmooth.comp contDiff_snd).mul (hη_smooth.comp contDiff_fst)
        have hCη_cpt : HasCompactSupport (fun p : ℝ × ℝ => C p.2 * η p.1) := by
          apply HasCompactSupport.intro (K := tsupport η ×ˢ tsupport C) (hη_cpt.prod hCsupp)
          intro p hp; simp only [Set.mem_prod, not_and_or] at hp
          rcases hp with hh | hh
          · have : η p.1 = 0 := by
              by_contra hne;
                exact hh (subset_tsupport η (by simpa [Function.mem_support] using hne))
            rw [this, mul_zero]
          · have : C p.2 = 0 := by
              by_contra hne;
                exact hh (subset_tsupport C (by simpa [Function.mem_support] using hne))
            rw [this, zero_mul]
        have hw_cpt : HasCompactSupport (fun p : ℝ × ℝ => w p.1 p.2) := by
          rw [hw]; exact HasCompactSupport.sub hΦ2_cpt hCη_cpt
        have hw_cont : Continuous (fun p : ℝ × ℝ => w p.1 p.2) := hw_smooth.continuous
        -- w support / mean
        set Rw : ℝ := max RΦ Rη with hRwdef
        have hRw : 0 < Rw := lt_of_lt_of_le hRΦ (le_max_left _ _)
        have hRwΦ : RΦ ≤ Rw := le_max_left _ _
        have hRwη : Rη ≤ Rw := le_max_right _ _
        have hwsupp_x : ∀ x y : ℝ, Rw ≤ |x| → w x y = 0 := by
          intro x y hx; rw [hw]
          simp [hΦ₀supp_x x y (le_trans hRwΦ hx), hηsupp x (le_trans hRwη hx)]
        have hwsupp_y : ∀ x y : ℝ, Rw ≤ |y| → w x y = 0 := by
          intro x y hy; rw [hw]
          simp [hΦ₀supp_y x y (le_trans hRwΦ hy), hCsupp_y y (le_trans hRwΦ hy)]
        have hwmean : ∀ y, (∫ t, w t y) = 0 := by
          intro y; rw [hw]
          have hslice_cont : Continuous (fun t => Φ₀ (t, y)) :=
            hΦ₀_smooth.continuous.comp (continuous_id.prodMk continuous_const)
          have hslice_cpt : HasCompactSupport (fun t => Φ₀ (t, y)) := by
            apply HasCompactSupport.intro (K := Set.Icc (-RΦ) RΦ) isCompact_Icc
            intro t ht; rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
            rcases ht with hh | hh
            · exact hΦ₀supp_x t y (by rw [abs_of_neg (by linarith)]; linarith)
            · exact hΦ₀supp_x t y (by rw [abs_of_pos (by linarith)]; linarith)
          have hΦ₀int : Integrable (fun t => Φ₀ (t, y)) volume :=
            hslice_cont.integrable_of_hasCompactSupport hslice_cpt
          have hηint : Integrable η volume := hη_cont.integrable_of_hasCompactSupport hη_cpt
          rw [integral_sub hΦ₀int (hηint.const_mul (C y) |>.congr (by filter_upwards with t; ring))]
          rw [integral_const_mul, hη_int, mul_one]
          change C y - C y = 0
          ring
        -- ======= Ψ block =======
        set aL : ℝ := -(Rw + 1) with haL
        set Ψ : ℝ → ℝ → ℝ := fun x y => ∫ t in aL..x, w t y with hΨ
        have hwcontslice : ∀ y, Continuous (fun t => w t y) :=
          fun y => hw_smooth.continuous.comp (continuous_id.prodMk continuous_const)
        have hwII : ∀ (y : ℝ) (p q : ℝ), IntervalIntegrable (fun t => w t y) volume p q :=
          fun y p q => (hwcontslice y).intervalIntegrable p q
        have hΨ_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Ψ p.1 p.2) :=
          contDiff_intervalIntegral_primitive_fst aL hw_smooth hw_cpt
        have hΨ_hasderiv : ∀ x y, HasDerivAt (fun t => Ψ t y) (w x y) x := by
          intro x y; rw [hΨ]
          exact intervalIntegral.integral_hasDerivAt_right (hwII y aL x)
            ((hwcontslice y).stronglyMeasurableAtFilter _ _) (hwcontslice y).continuousAt
        have hΨ_deriv : ∀ y, deriv (fun t => Ψ t y) = fun t => w t y := by
          intro y; funext x; exact (hΨ_hasderiv x y).deriv
        have hΨy_smooth : ∀ y, ContDiff ℝ ∞ (fun t => Ψ t y) :=
          fun y => hΨ_smooth.comp ((contDiff_id).prodMk contDiff_const)
        -- Ψ vanishes outside the x-box, for every y.
        have hΨ_vanish : ∀ x y : ℝ, (x < -(Rw+1) ∨ Rw + 1 < x) → Ψ x y = 0 := by
          intro x y hx
          change (∫ t in aL..x, w t y) = 0
          rcases hx with h1 | h1
          · rw [intervalIntegral.integral_symm, neg_eq_zero]
            apply intervalIntegral.integral_zero_ae
            filter_upwards with t ht
            rw [Set.uIoc_of_le (by linarith [h1] : x ≤ aL), Set.mem_Ioc] at ht
            exact hwsupp_x t y (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
          · have hmean := hwmean y
            have heq : (∫ t in aL..x, w t y) = ∫ t, w t y := by
              rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
              refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
              intro t ht; rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
              rcases ht with hh | hh
              · exact hwsupp_x t y (by rw [abs_of_neg (by linarith)]; linarith)
              · exact hwsupp_x t y (by rw [abs_of_pos (by linarith)]; linarith)
            rw [heq, hmean]
        have hΨ_cpt : HasCompactSupport (fun p : ℝ × ℝ => Ψ p.1 p.2) := by
          apply HasCompactSupport.intro (K := Set.Icc (-(Rw+1)) (Rw+1) ×ˢ Set.Icc (-Rw) Rw)
            (isCompact_Icc.prod isCompact_Icc)
          intro p hp
          simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hp
          by_cases hy : Rw ≤ |p.2|
          · change (∫ t in aL..p.1, w t p.2) = 0
            have hz : ∀ t, w t p.2 = 0 := fun t => hwsupp_y t p.2 hy
            simp only [hz, intervalIntegral.integral_zero]
          · rw [not_le, abs_lt] at hy
            refine hΨ_vanish p.1 p.2 ?_
            rcases hp with (h1|h1)|(h2|h2)
            · exact Or.inl h1
            · exact Or.inr h1
            · exact absurd h2 (by linarith [hy.1])
            · exact absurd h2 (by linarith [hy.2])
        have hΨy_cpt : ∀ y, HasCompactSupport (fun t => Ψ t y) := by
          intro y
          apply HasCompactSupport.intro (K := Set.Icc (-(Rw+1)) (Rw+1)) isCompact_Icc
          intro x hx
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
          exact hΨ_vanish x y (by rcases hx with hh|hh; exacts [Or.inl hh, Or.inr hh])
        -- ======= φc := Ψ∘(re,im), smoothness, compact support, partial =======
        set φc : ℂ → ℝ := fun z => Ψ z.re z.im with hφc
        have hφc_smooth : ContDiff ℝ ∞ φc := by
          have hmap : ContDiff ℝ ∞ (fun z : ℂ => (z.re, z.im)) :=
            Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
          exact hΨ_smooth.comp hmap
        have hφc_cpt : HasCompactSupport φc := by
          -- φc z = Ψ z.re z.im, support transferred from joint Ψ via measurableEquivRealProd
          apply HasCompactSupport.intro (K := Complex.measurableEquivRealProd.symm ''
            (Set.Icc (-(Rw+1)) (Rw+1) ×ˢ Set.Icc (-Rw) Rw)) ?_
          · intro z hz
            have hz' : (z.re, z.im) ∉ Set.Icc (-(Rw+1)) (Rw+1) ×ˢ Set.Icc (-Rw) Rw := by
              intro hmem
              apply hz
              refine ⟨(z.re, z.im), hmem, ?_⟩
              apply Complex.ext <;> rfl
            change Ψ z.re z.im = 0
            simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hz'
            by_cases hy : Rw ≤ |z.im|
            · change (∫ t in aL..z.re, w t z.im) = 0
              have hzz : ∀ t, w t z.im = 0 := fun t => hwsupp_y t z.im hy
              simp only [hzz, intervalIntegral.integral_zero]
            · rw [not_le, abs_lt] at hy
              refine hΨ_vanish z.re z.im ?_
              rcases hz' with (h1|h1)|(h2|h2)
              · exact Or.inl h1
              · exact Or.inr h1
              · exact absurd h2 (by linarith [hy.1])
              · exact absurd h2 (by linarith [hy.2])
          · have hcont : Continuous (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) := by
              have he : (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ)
                  = (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) := by
                ext p
                simp [Complex.measurableEquivRealProd, Complex.equivRealProdCLM]
              rw [he]; exact Complex.equivRealProdCLM.symm.continuous
            exact (isCompact_Icc.prod isCompact_Icc).image hcont
        have hpartial : ∀ z : ℂ, (fderiv ℝ φc z) (1 : ℂ) = w z.re z.im := by
          intro z
          have hzz : (⟨z.re, z.im⟩ : ℂ) = z := by apply Complex.ext <;> rfl
          have haff : HasDerivAt (fun t : ℝ => (⟨t, z.im⟩ : ℂ)) (1 : ℂ) z.re := by
            have he : (fun t : ℝ => (⟨t, z.im⟩ : ℂ)) = fun t : ℝ => (t : ℂ)
              + (z.im : ℂ) * Complex.I := by
              funext t; apply Complex.ext <;> simp
            rw [he]; simpa using (Complex.ofRealCLM.hasDerivAt (x :=
              z.re)).add_const ((z.im : ℂ) * Complex.I)
          have hfd : HasFDerivAt φc (fderiv ℝ φc (⟨z.re, z.im⟩ : ℂ)) (⟨z.re, z.im⟩ : ℂ) :=
            (hφc_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
          have hslice1 : HasDerivAt (fun t : ℝ => φc ⟨t, z.im⟩) ((fderiv ℝ φc (⟨z.re,
            z.im⟩:ℂ)) 1) z.re := by
            simpa [Function.comp_def] using! hfd.comp_hasDerivAt z.re haff
          have hslice2 : HasDerivAt (fun t : ℝ => φc ⟨t, z.im⟩) (w z.re z.im) z.re :=
            hΨ_hasderiv z.re z.im
          have := hslice1.unique hslice2
          rw [hzz] at this; exact this
        -- ======= integrability facts =======
        have hint_ΦR : Integrable (fun p : ℝ × ℝ => Φ₀ p • (f ⟨p.1,
          p.2⟩ - D p.1 p.2)) (volume.prod volume) :=
          integ2 Φ₀ hΦ₀_smooth.continuous hΦ₀_cpt hRli
        have hint_Φk : Integrable (fun p : ℝ × ℝ => Φ₀ p • k p.2) (volume.prod volume) :=
          integ2 Φ₀ hΦ₀_smooth.continuous hΦ₀_cpt hk_li2
        have hint_ηR : Integrable (fun p : ℝ × ℝ => (C p.2 * η p.1) • (f ⟨p.1, p.2⟩ - D p.1 p.2))
            (volume.prod volume) :=
          integ2 (fun p => C p.2 * η p.1)
            ((hCcont.comp continuous_snd).mul (hη_cont.comp continuous_fst))
            hCη_cpt hRli
        have hint_wf : Integrable (fun p : ℝ × ℝ => w p.1 p.2 • f ⟨p.1,
          p.2⟩) (volume.prod volume) :=
          integ2 (fun p => w p.1 p.2) hw_cont hw_cpt hfli2
        have hint_wD : Integrable (fun p : ℝ × ℝ => w p.1 p.2 • D p.1 p.2) (volume.prod volume) :=
          integ2 (fun p => w p.1 p.2) hw_cont hw_cpt hD_li
        have hint_Ψgx0 : Integrable (fun p : ℝ × ℝ => (Ψ p.1 p.2 : ℂ) • gx0 ⟨p.1,
          p.2⟩) (volume.prod volume) := by
          have hh3 := integ2 (fun p => Ψ p.1 p.2) hΨ_smooth.continuous hΨ_cpt hgx0li2'
          refine hh3.congr ?_
          filter_upwards with p; exact (Complex.coe_smul _ _).symm
        -- ======= IBP f: from the hypothesis h =======
        have hIBPf : (∫ p, (w p.1 p.2 : ℂ) • f ⟨p.1, p.2⟩ ∂(volume.prod volume))
            = -∫ p, (Ψ p.1 p.2 : ℂ) • gx ⟨p.1, p.2⟩ ∂(volume.prod volume) := by
          have hh := h φc hφc_smooth hφc_cpt (by simp)
          rw [show (fun z : ℂ => ((fderiv ℝ φc z) (1:ℂ)) • f z)
               = (fun z : ℂ => (w z.re z.im : ℝ) • f z) from by funext z; rw [hpartial z]] at hh
          have hL : (∫ z : ℂ, (w z.re z.im : ℝ) • f z)
              = ∫ p, (w p.1 p.2 : ℂ) • f ⟨p.1, p.2⟩ ∂(volume.prod volume) := by
            rw [transInt (fun z => (w z.re z.im : ℝ) • f z), ← Measure.volume_eq_prod]
            apply integral_congr_ae; filter_upwards with p
            change (w (⟨p.1,p.2⟩:ℂ).re (⟨p.1,p.2⟩:ℂ).im : ℝ) • f ⟨p.1,p.2⟩
              = (w p.1 p.2 : ℂ) • f ⟨p.1,p.2⟩
            rw [Complex.coe_smul]
          have hRr : (∫ z : ℂ, (φc z : ℝ) • gx z)
              = ∫ p, (Ψ p.1 p.2 : ℂ) • gx ⟨p.1, p.2⟩ ∂(volume.prod volume) := by
            rw [transInt (fun z => (φc z : ℝ) • gx z), ← Measure.volume_eq_prod]
            apply integral_congr_ae; filter_upwards with p
            show (φc ⟨p.1,p.2⟩ : ℝ) • gx ⟨p.1,p.2⟩ = (Ψ p.1 p.2 : ℂ) • gx ⟨p.1,p.2⟩
            rw [Complex.coe_smul]
          rw [← hL, ← hRr]; exact hh
        -- ======= IBP D: per-line lineIBP + Fubini =======
        -- per-line interval integrability of Ψ(·,y)•gx0⟨·,y⟩ and w(·,y)•D(·,y)
        have hline : ∀ᵐ y : ℝ, (∫ x, (w x y : ℝ) • D x y) = -(∫ x, (Ψ x y : ℝ) • gx0 ⟨x, y⟩) := by
          filter_upwards [hgx0_slice] with y hyII
          -- per-line D facts from slice integrability
          have hDline : (∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x => D x y) a b) ∧
              (∀ᵐ t : ℝ, HasDerivAt (fun x => D x y) (gx0 ⟨t, y⟩) t) := by
            set gxy : ℝ → ℂ := fun x => gx0 ⟨x, y⟩ with hgxy
            have hgxyLI : LocallyIntegrable gxy volume := II_all_LI _ hyII
            have hreII : ∀ a b : ℝ, IntervalIntegrable (fun t => (gxy t).re) volume a b :=
              fun a b => ⟨Complex.reCLM.integrable_comp (hyII a b).1,
                Complex.reCLM.integrable_comp (hyII a b).2⟩
            have himII : ∀ a b : ℝ, IntervalIntegrable (fun t => (gxy t).im) volume a b :=
              fun a b => ⟨Complex.imCLM.integrable_comp (hyII a b).1,
                Complex.imCLM.integrable_comp (hyII a b).2⟩
            have hreLI : LocallyIntegrable (fun t => (gxy t).re) volume := by
              rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
              exact Complex.reCLM.integrable_comp (hgxyLI.integrableOn_isCompact hK)
            have himLI : LocallyIntegrable (fun t => (gxy t).im) volume := by
              rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
              exact Complex.imCLM.integrable_comp (hgxyLI.integrableOn_isCompact hK)
            have hDval : ∀ x : ℝ, D x y = ∫ t in (0:ℝ)..x, gxy t := by intro x; rw [hD]
            have hDre : ∀ x : ℝ, (D x y).re = ∫ t in (0:ℝ)..x, (gxy t).re := by
              intro x; rw [hDval x]
              have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM (hyII 0 x)
              simpa [Complex.reCLM_apply] using this.symm
            have hDim : ∀ x : ℝ, (D x y).im = ∫ t in (0:ℝ)..x, (gxy t).im := by
              intro x; rw [hDval x]
              have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM (hyII 0 x)
              simpa [Complex.imCLM_apply] using this.symm
            refine ⟨?_, ?_⟩
            · intro a b
              refine hACofComp (fun x => D x y) a b ?_ ?_
              · rw [show (fun x => (D x y).re) = (fun x => ∫ t in (0:ℝ)..x, (gxy t).re)
                from funext hDre]
                exact hACprim _ hreII a b
              · rw [show (fun x => (D x y).im) = (fun x => ∫ t in (0:ℝ)..x, (gxy t).im)
                from funext hDim]
                exact hACprim _ himII a b
            · have hre := LocallyIntegrable.ae_hasDerivAt_integral hreLI
              have him := LocallyIntegrable.ae_hasDerivAt_integral himLI
              filter_upwards [hre, him] with t htre htim
              have h1 : HasDerivAt (fun x => (D x y).re) ((gxy t).re) t := by
                rw [show (fun x => (D x y).re) = (fun x => ∫ s in (0:ℝ)..x, (gxy s).re)
                  from funext hDre]
                exact htre 0
              have h2 : HasDerivAt (fun x => (D x y).im) ((gxy t).im) t := by
                rw [show (fun x => (D x y).im) = (fun x => ∫ s in (0:ℝ)..x, (gxy s).im)
                  from funext hDim]
                exact htim 0
              have heq : (fun x => D x y) = fun x => (↑(D x y).re : ℂ)
                + (↑(D x y).im : ℂ) * Complex.I := by
                funext x; exact (Complex.re_add_im (D x y)).symm
              rw [heq]
              have hh3 :
                HasDerivAt (fun x => (↑(D x y).im : ℂ) * Complex.I) (↑(gxy t).im * Complex.I) t :=
                h2.ofReal_comp.mul_const Complex.I
              have := h1.ofReal_comp.add hh3
              simpa [Pi.add_def] using! this
          obtain ⟨hDy_ac_y, hDy_deriv_y⟩ := hDline
          -- apply lineIBP with Φ = Ψ(·,y), F = D(·,y), G = gx0⟨·,y⟩
          have hintL : Integrable (fun t => deriv (fun t => Ψ t y) t • (fun x => D x y) t) := by
            have hcont : Continuous (fun t => Ψ t y) := (hΨy_smooth y).continuous
            have : (fun t => deriv (fun t => Ψ t y) t • (fun x => D x y) t)
                = (fun t => (w t y : ℝ) • D t y) := by
              funext t; rw [hΨ_deriv y]
            rw [this]
            -- D(·,y) continuous (running integral of interval-integrable slice), hence loc-int
            have hDy_cont : Continuous (fun x => D x y) := by
              rw [hD]
              exact intervalIntegral.continuous_primitive (fun a b => hyII a b) 0
            have hDyLI : LocallyIntegrable (fun x => D x y) volume := hDy_cont.locallyIntegrable
            have hwy_cont : Continuous (fun t => w t y) := hwcontslice y
            have hwy_cpt : HasCompactSupport (fun t => w t y) := by
              apply HasCompactSupport.intro (K := Set.Icc (-Rw) Rw) isCompact_Icc
              intro x hx; rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
              rcases hx with hh | hh
              · exact hwsupp_x x y (by rw [abs_of_neg (by linarith)]; linarith)
              · exact hwsupp_x x y (by rw [abs_of_pos (by linarith)]; linarith)
            -- (cont cpt real) • (loc-int ℂ) integrable on ℝ
            have hK : IsCompact (tsupport (fun t => w t y)) := hwy_cpt
            have hhon : IntegrableOn (fun x => D x y) (tsupport (fun t => w t y)) volume :=
              hDyLI.integrableOn_isCompact hK
            have hon :
              IntegrableOn (fun t => (w t y : ℝ) • D t y) (tsupport (fun t => w t y)) volume :=
              hhon.continuousOn_smul hwy_cont.continuousOn hK
            have hsupp :
              Function.support (fun t => (w t y : ℝ) • D t y) ⊆ tsupport (fun t => w t y) := by
              intro z hz; apply subset_tsupport (fun t => w t y)
              simp only [Function.mem_support] at hz ⊢
              intro hmz; apply hz; simp [hmz]
            exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
          have hintR : Integrable (fun t => (fun t => Ψ t y) t • gx0 ⟨t, y⟩) := by
            -- Ψ(·,y) cont cpt • gx0⟨·,y⟩ loc-int (1-dim)
            have hgx0yLI : LocallyIntegrable (fun x => gx0 ⟨x, y⟩) volume := by
              rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
              obtain ⟨a, ha⟩ := hK.bddBelow; obtain ⟨b, hb⟩ := hK.bddAbove
              have hsub : K ⊆ Set.Icc a b := fun x hx => ⟨ha hx, hb hx⟩
              rcases le_or_gt a b with hle | hlt
              · have hII := hyII a b
                rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle] at hII
                exact hII.mono_set hsub
              · rw [Icc_eq_empty (not_le.2 hlt), subset_empty_iff] at hsub; rw [hsub];
                exact integrableOn_empty
            have hK : IsCompact (tsupport (fun t => Ψ t y)) := hΨy_cpt y
            have hhon : IntegrableOn (fun x => gx0 ⟨x, y⟩) (tsupport (fun t => Ψ t y)) volume :=
              hgx0yLI.integrableOn_isCompact hK
            have hon : IntegrableOn (fun t => Ψ t y • gx0 ⟨t,
              y⟩) (tsupport (fun t => Ψ t y)) volume :=
              hhon.continuousOn_smul (hΨy_smooth y).continuous.continuousOn hK
            have hsupp : Function.support (fun t => Ψ t y • gx0 ⟨t,
              y⟩) ⊆ tsupport (fun t => Ψ t y) := by
              intro z hz; apply subset_tsupport (fun t => Ψ t y)
              simp only [Function.mem_support] at hz ⊢
              intro hmz; apply hz; simp [hmz]
            exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
          -- invoke lineIBP
          have key := lineIBP (fun t => Ψ t y) (fun x => D x y) (fun x => gx0 ⟨x, y⟩)
            (hΨy_smooth y) (hΨy_cpt y) hDy_ac_y hDy_deriv_y hintL hintR
          rw [hΨ_deriv y] at key
          exact key
        have hint_Ψgx0_R : Integrable (fun p : ℝ × ℝ => (Ψ p.1 p.2 : ℝ) • gx0 ⟨p.1,
          p.2⟩) (volume.prod volume) :=
          integ2 (fun p => Ψ p.1 p.2) hΨ_smooth.continuous hΨ_cpt hgx0li2'
        have hIBPD : (∫ p, (w p.1 p.2 : ℝ) • D p.1 p.2 ∂(volume.prod volume))
            = -∫ p, (Ψ p.1 p.2 : ℝ) • gx0 ⟨p.1, p.2⟩ ∂(volume.prod volume) := by
          rw [integral_prod_symm _ hint_wD, integral_prod_symm _ hint_Ψgx0_R, ← integral_neg]
          apply integral_congr_ae
          filter_upwards [hline] with y hy
          exact hy
        -- reconcile gx0 ↔ gx in the Ψ-integral
        have hgx0_eq_prod : (fun p : ℝ × ℝ => (Ψ p.1 p.2 : ℝ) • gx0 ⟨p.1, p.2⟩)
            =ᵐ[volume.prod volume] (fun p : ℝ × ℝ => (Ψ p.1 p.2 : ℝ) • gx ⟨p.1, p.2⟩) := by
          have hbase : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), gx0 ⟨p.1, p.2⟩ = gx ⟨p.1, p.2⟩ := by
            rw [← Measure.volume_eq_prod]
            have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
                (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
              (Complex.volume_preserving_equiv_real_prod).symm Complex.measurableEquivRealProd
            filter_upwards [hmpsymm.quasiMeasurePreserving.ae hgx0_eq] with p hp; exact hp
          filter_upwards [hbase] with p hp; rw [hp]
        -- common Ψgx
        set Ψgx : ℂ := -∫ p, (Ψ p.1 p.2 : ℂ) • gx ⟨p.1, p.2⟩ ∂(volume.prod volume) with hΨgxdef
        have hIBPf_R : (∫ p, (w p.1 p.2 : ℝ) • f ⟨p.1, p.2⟩ ∂(volume.prod volume)) = Ψgx := by
          have hcvt : (∫ p, (w p.1 p.2 : ℝ) • f ⟨p.1, p.2⟩ ∂(volume.prod volume))
              = ∫ p, (w p.1 p.2 : ℂ) • f ⟨p.1, p.2⟩ ∂(volume.prod volume) := by
            apply integral_congr_ae; filter_upwards with p; exact (Complex.coe_smul _ _).symm
          rw [hcvt, hIBPf]
        have hIBPD_R : (∫ p, (w p.1 p.2 : ℝ) • D p.1 p.2 ∂(volume.prod volume)) = Ψgx := by
          rw [hIBPD, hΨgxdef]; congr 1
          rw [integral_congr_ae hgx0_eq_prod]
          apply integral_congr_ae; filter_upwards with p; exact Complex.coe_smul _ _
        -- ======= CORE: ∫ Φ₀ • (f - f') = ∫ w • R = 0 =======
        set R : ℝ → ℝ → ℂ := fun x y => f ⟨x, y⟩ - D x y with hR
        have hint_ΦRc : Integrable (fun p : ℝ × ℝ => (Φ₀ p : ℂ) • R p.1 p.2) (volume.prod volume) :=
          hint_ΦR.congr (by filter_upwards with p; exact (Complex.coe_smul _ _).symm)
        have hint_Φkc : Integrable (fun p : ℝ × ℝ => (Φ₀ p : ℂ) • k p.2) (volume.prod volume) := by
          refine hint_Φk.congr ?_; filter_upwards with p; exact (Complex.coe_smul _ _).symm
        have hint_ηRc : Integrable (fun p : ℝ × ℝ => ((C p.2 * η p.1 : ℝ) : ℂ) • R p.1 p.2)
            (volume.prod volume) :=
          hint_ηR.congr (by filter_upwards with p; exact (Complex.coe_smul _ _).symm)
        have hint_wfc : Integrable (fun p : ℝ × ℝ => (w p.1 p.2 : ℂ) • f ⟨p.1,
          p.2⟩) (volume.prod volume) :=
          hint_wf.congr (by filter_upwards with p; exact (Complex.coe_smul _ _).symm)
        have hint_wDc :
          Integrable (fun p : ℝ × ℝ => (w p.1 p.2 : ℂ) • D p.1 p.2) (volume.prod volume) :=
          hint_wD.congr (by filter_upwards with p; exact (Complex.coe_smul _ _).symm)
        have hPid : ∀ p : ℝ × ℝ, f ⟨p.1, p.2⟩ - f' ⟨p.1, p.2⟩ = R p.1 p.2 - k p.2 := by
          intro p; rw [hf', hR]; ring_nf
        have hstepA : (∫ p, (Φ₀ p : ℂ) • (f ⟨p.1, p.2⟩ - f' ⟨p.1, p.2⟩) ∂(volume.prod volume))
            = (∫ p, (Φ₀ p : ℂ) • R p.1 p.2 ∂(volume.prod volume))
              - (∫ p, (Φ₀ p : ℂ) • k p.2 ∂(volume.prod volume)) := by
          rw [← integral_sub hint_ΦRc hint_Φkc]
          apply integral_congr_ae; filter_upwards with p
          rw [hPid p, smul_sub]
        have hwR : (∫ p, (w p.1 p.2 : ℂ) • R p.1 p.2 ∂(volume.prod volume))
            = (∫ p, (Φ₀ p : ℂ) • R p.1 p.2 ∂(volume.prod volume))
              - (∫ p, ((C p.2 * η p.1 : ℝ) : ℂ) • R p.1 p.2 ∂(volume.prod volume)) := by
          rw [← integral_sub hint_ΦRc hint_ηRc]
          apply integral_congr_ae; filter_upwards with p
          rw [hw]; push_cast; rw [sub_smul]
        have factor_smulconst : (∫ p, (Φ₀ p : ℂ) • k p.2 ∂(volume.prod volume)) = ∫ y,
          (C y : ℂ) • k y := by
          rw [show (fun p : ℝ × ℝ => (Φ₀ p : ℂ) • k p.2)
              = (fun p : ℝ × ℝ => (Φ₀ p : ℝ) • k p.2) from by
              funext p; exact Complex.coe_smul _ _]
          rw [integral_prod_symm _ hint_Φk]
          apply integral_congr_ae; filter_upwards with y
          rw [hC, Complex.coe_smul]
          exact integral_smul_const (fun x => Φ₀ (x,y)) (k y)
        have factor_etaR : (∫ p, ((C p.2 * η p.1 : ℝ) : ℂ) • R p.1 p.2 ∂(volume.prod volume))
            = ∫ y, (C y : ℂ) • k y := by
          rw [show (fun p : ℝ × ℝ => ((C p.2 * η p.1 : ℝ) : ℂ) • R p.1 p.2)
              = (fun p : ℝ × ℝ => (C p.2 * η p.1 : ℝ) • R p.1 p.2) from by
              funext p; exact Complex.coe_smul _ _]
          rw [integral_prod_symm _ hint_ηR]
          apply integral_congr_ae; filter_upwards with y
          rw [show (∫ x, (C y * η x) • R x y) = ∫ x, C y • (η x • R x y) from by
            apply integral_congr_ae; filter_upwards with x; exact mul_smul (C y) (η x) (R x y)]
          rw [hk, Complex.coe_smul]
          exact integral_smul (C y) (fun x => η x • R x y)
        have hkey : (∫ p, (Φ₀ p : ℂ) • (f ⟨p.1, p.2⟩ - f' ⟨p.1, p.2⟩) ∂(volume.prod volume))
            = ∫ p, (w p.1 p.2 : ℂ) • R p.1 p.2 ∂(volume.prod volume) := by
          rw [hstepA, hwR, factor_smulconst, factor_etaR]
        rw [hkey]
        rw [show (fun p : ℝ × ℝ => (w p.1 p.2 : ℂ) • R p.1 p.2)
            = (fun p : ℝ × ℝ => (w p.1 p.2 : ℂ) • f ⟨p.1,
              p.2⟩ - (w p.1 p.2 : ℂ) • D p.1 p.2) from by
            funext p; rw [hR, smul_sub]]
        rw [integral_sub hint_wfc hint_wDc]
        have e1 : (∫ p, (w p.1 p.2 : ℂ) • f ⟨p.1, p.2⟩ ∂(volume.prod volume)) = Ψgx := by
          rw [← hIBPf_R]; apply integral_congr_ae; filter_upwards with p;
            exact (Complex.coe_smul _ _).symm
        have e2 : (∫ p, (w p.1 p.2 : ℂ) • D p.1 p.2 ∂(volume.prod volume)) = Ψgx := by
          rw [← hIBPD_R]; apply integral_congr_ae; filter_upwards with p;
            exact (Complex.coe_smul _ _).symm
        rw [e1, e2, sub_self]
    -- transfer a.e. P=0 to f' =ᵐ f
    set e := Complex.measurableEquivRealProd
    have hmp : MeasurePreserving e (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
      Complex.volume_preserving_equiv_real_prod
    have hz : ∀ᵐ z : ℂ, P (e z) = 0 := by
      rw [← Measure.volume_eq_prod] at hPzero
      exact hmp.quasiMeasurePreserving.ae hPzero
    filter_upwards [hz] with z hzz
    have hzz2 : f ⟨z.re, z.im⟩ - f' ⟨z.re, z.im⟩ = 0 := hzz
    have hzc : (⟨z.re, z.im⟩ : ℂ) = z := by apply Complex.ext <;> rfl
    rw [hzc] at hzz2
    exact (sub_eq_zero.mp hzz2).symm
  · -- ======================= GOAL 1: ACLHorizontal =======================
    -- a.e. y, slice of gx0 interval-integrable; and gx0 ↔ gx a.e. on lines.
    have hgxLIprod : LocallyIntegrable (fun p : ℝ × ℝ => gx ⟨p.1, p.2⟩) volume :=
      slice_locint gx hgx
    have hslice_gx := ae_slice_II _ hgxLIprod
    -- gx0 ↔ gx slice a.e.
    have hslicemod : ∀ᵐ y : ℝ, (fun x => gx0 ⟨x, y⟩) =ᵐ[volume] (fun x => gx ⟨x, y⟩) := by
      have hbase : ∀ᵐ p : ℝ × ℝ, gx0 ⟨p.1, p.2⟩ = gx ⟨p.1, p.2⟩ := by
        filter_upwards [hmpsymm.quasiMeasurePreserving.ae hgx0_eq] with p hp; exact hp
      have hswap : ∀ᵐ q : ℝ × ℝ ∂(volume.prod volume), gx0 ⟨q.2, q.1⟩ = gx ⟨q.2, q.1⟩ := by
        rw [← Measure.volume_eq_prod]
        have hsw : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
          rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap
        filter_upwards [hsw.quasiMeasurePreserving.ae hbase] with q hq; exact hq
      exact Measure.ae_ae_of_ae_prod hswap
    filter_upwards [hslice_gx, hslicemod] with y hyII hymod
    -- work with gxy := gx⟨·,y⟩ throughout; Dy x = ∫₀ˣ gx⟨t,y⟩ via a.e. equality with gx0.
    set gxy : ℝ → ℂ := fun x => gx ⟨x, y⟩ with hgxy
    have hgxyLI : LocallyIntegrable gxy volume := II_all_LI _ hyII
    have hreII : ∀ a b : ℝ, IntervalIntegrable (fun t => (gxy t).re) volume a b :=
      fun a b => ⟨Complex.reCLM.integrable_comp (hyII a b).1,
        Complex.reCLM.integrable_comp (hyII a b).2⟩
    have himII : ∀ a b : ℝ, IntervalIntegrable (fun t => (gxy t).im) volume a b :=
      fun a b => ⟨Complex.imCLM.integrable_comp (hyII a b).1,
        Complex.imCLM.integrable_comp (hyII a b).2⟩
    have hreLI : LocallyIntegrable (fun t => (gxy t).re) volume := by
      rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
      exact Complex.reCLM.integrable_comp (hgxyLI.integrableOn_isCompact hK)
    have himLI : LocallyIntegrable (fun t => (gxy t).im) volume := by
      rw [MeasureTheory.locallyIntegrable_iff]; intro K hK
      exact Complex.imCLM.integrable_comp (hgxyLI.integrableOn_isCompact hK)
    set Dy : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, gxy t with hDy
    have hDxy : ∀ x, D x y = Dy x := by
      intro x
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hymod] with t ht _; exact ht
    have hDre : ∀ x : ℝ, (Dy x).re = ∫ t in (0:ℝ)..x, (gxy t).re := by
      intro x
      have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM (hyII 0 x)
      simpa [Complex.reCLM_apply, hDy] using this.symm
    have hDim : ∀ x : ℝ, (Dy x).im = ∫ t in (0:ℝ)..x, (gxy t).im := by
      intro x
      have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM (hyII 0 x)
      simpa [Complex.imCLM_apply, hDy] using this.symm
    have hDy_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval Dy a b := by
      intro a b
      refine hACofComp Dy a b ?_ ?_
      · rw [show (fun x => (Dy x).re) = (fun x => ∫ t in (0:ℝ)..x, (gxy t).re) from funext hDre]
        exact hACprim _ hreII a b
      · rw [show (fun x => (Dy x).im) = (fun x => ∫ t in (0:ℝ)..x, (gxy t).im) from funext hDim]
        exact hACprim _ himII a b
    have hDy_deriv : ∀ᵐ t : ℝ, HasDerivAt Dy (gxy t) t := by
      have hre := LocallyIntegrable.ae_hasDerivAt_integral hreLI
      have him := LocallyIntegrable.ae_hasDerivAt_integral himLI
      filter_upwards [hre, him] with t htre htim
      have h1 : HasDerivAt (fun x => (Dy x).re) ((gxy t).re) t := by
        rw [show (fun x => (Dy x).re) = (fun x => ∫ s in (0:ℝ)..x, (gxy s).re) from funext hDre]
        exact htre 0
      have h2 : HasDerivAt (fun x => (Dy x).im) ((gxy t).im) t := by
        rw [show (fun x => (Dy x).im) = (fun x => ∫ s in (0:ℝ)..x, (gxy s).im) from funext hDim]
        exact htim 0
      have heq : Dy = fun x => (↑(Dy x).re : ℂ) + (↑(Dy x).im : ℂ) * Complex.I := by
        funext x; exact (Complex.re_add_im (Dy x)).symm
      rw [heq]
      have hh3 : HasDerivAt (fun x => (↑(Dy x).im : ℂ) * Complex.I) (↑(gxy t).im * Complex.I) t :=
        h2.ofReal_comp.mul_const Complex.I
      have := h1.ofReal_comp.add hh3
      simpa [Pi.add_def] using! this
    -- the f'-slice = Dy + k y.
    have hfx : (fun x : ℝ => f' ⟨x, y⟩) = (fun x => Dy x + k y) := by
      funext x; rw [show f' ⟨x,y⟩ = D x y + k y from rfl, hDxy]
    refine ⟨?_, ?_⟩
    · intro a b
      rw [hfx]
      have hcAC : AbsolutelyContinuousOnInterval (fun _ : ℝ => k y) a b :=
        ((LipschitzWith.const' (k y)).lipschitzOnWith (s := Set.uIcc a b)
          (K := 0)).absolutelyContinuousOnInterval
      exact (hDy_ac a b).add hcAC
    · rw [hfx]
      filter_upwards [hDy_deriv] with t ht
      exact ht.add_const (k y)

/-- **`W^{1,p} ⇒ AC on vertical lines` (converse of
`hasWeakDirDeriv_I_of_aclVertical`).** The vertical analogue: if `gy` is the weak
`y`-directional derivative of a locally integrable `f`, then `f` has a
representative `f̃ =ᵐ f` that is absolutely continuous on almost every vertical
line with `y`-partial `gy`. -/
theorem exists_aclVertical_of_hasWeakDirDeriv_I
    (hf : LocallyIntegrable f) (hgy : LocallyIntegrable gy)
    (h : HasWeakDirDeriv Complex.I gy f Set.univ) :
    ∃ f' : ℂ → ℂ, f' =ᵐ[volume] f ∧ ACLVertical f' gy := by
  -- =============== THE COORDINATE SWAP `σ⟨x,y⟩ = ⟨y,x⟩` ===============
  -- Realize the swap as a real-linear isometric equivalence of `ℂ`,
  -- `σ z = I · conj z`, so that it is smooth, measure-preserving, and an
  -- involution, and reduce the vertical statement to the horizontal one.
  classical
  set σ : ℂ ≃ₗᵢ[ℝ] ℂ :=
    Complex.conjLIE.trans (rotation ⟨Complex.I, by simp [Submonoid.unitSphere, Metric.sphere]⟩)
    with hσ_def
  -- `σ` swaps real and imaginary parts.
  have hσ_apply : ∀ z : ℂ, σ z = ⟨z.im, z.re⟩ := by
    intro z
    have key : ∀ w : ℂ,
        (rotation ⟨Complex.I, by simp [Submonoid.unitSphere, Metric.sphere]⟩ : ℂ ≃ₗᵢ[ℝ] ℂ) w
          = Complex.I * w := fun _ => rfl
    simp only [hσ_def, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply, key]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  -- `σ` is an involution.
  have hσ_invol : ∀ z : ℂ, σ (σ z) = z := by
    intro z; rw [hσ_apply, hσ_apply]
  -- The scalar values `σ·I = 1` (the only direction needed below).
  have hσ_I : (σ : ℂ →L[ℝ] ℂ) Complex.I = 1 := by
    have : σ Complex.I = 1 := by rw [hσ_apply]; apply Complex.ext <;> simp
    simpa using this
  -- `σ` preserves Lebesgue measure (linear isometry of a finite-dim. Hilbert space).
  have hmp : MeasurePreserving σ volume volume := σ.measurePreserving
  have hemb : MeasurableEmbedding σ := σ.toMeasurableEquiv.measurableEmbedding
  -- ============ TRANSFER THE HYPOTHESIS TO THE HORIZONTAL DIRECTION ============
  -- `HasWeakDirDeriv 1 (gy∘σ) (f∘σ)`: test against `ψ`, apply `h` to `ψ∘σ`, and
  -- change variables `z ↦ σ z`; the chain rule turns `∂_I(ψ∘σ)` into `(∂₁ψ)∘σ`
  -- because `σ·I = 1`.
  have hweak : HasWeakDirDeriv 1 (fun z => gy (σ z)) (fun z => f (σ z)) Set.univ := by
    intro ψ hψ_smooth hψ_cpt _
    -- chain rule: `(fderiv (ψ∘σ) w) I = (fderiv ψ (σ w)) 1`.
    have hchain : ∀ w : ℂ,
        (fderiv ℝ (fun z => ψ (σ z)) w) Complex.I = (fderiv ℝ ψ (σ w)) 1 := by
      intro w
      have hd1 : DifferentiableAt ℝ ψ (σ w) :=
        (hψ_smooth.differentiable (by norm_num)).differentiableAt
      have hσd : DifferentiableAt ℝ (fun z => σ z) w :=
        σ.toContinuousLinearEquiv.differentiableAt
      have he : (fun z => ψ (σ z)) = ψ ∘ (fun z => σ z) := rfl
      rw [he, fderiv_comp w hd1 hσd]
      have hσfd : fderiv ℝ (fun z => σ z) w = (σ : ℂ →L[ℝ] ℂ) :=
        (σ.toContinuousLinearEquiv.hasFDerivAt).fderiv
      rw [hσfd]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hσ_I]
    -- `ψ∘σ` is a valid test function.
    have hψσ_smooth : ContDiff ℝ ∞ (fun z => ψ (σ z)) :=
      hψ_smooth.comp σ.toContinuousLinearEquiv.contDiff
    have hψσ_cpt : HasCompactSupport (fun z => ψ (σ z)) := by
      have := hψ_cpt.comp_homeomorph σ.toHomeomorph
      simpa [Function.comp_def] using this
    have hH := h (fun z => ψ (σ z)) hψσ_smooth hψσ_cpt (by simp)
    -- rewrite `h`'s identity using the chain rule.
    rw [show (fun z => ((fderiv ℝ (fun z => ψ (σ z)) z) Complex.I) • f z)
          = (fun z => ((fderiv ℝ ψ (σ z)) 1) • f z) from
          funext (fun z => by rw [hchain z])] at hH
    -- change of variables on both sides via `σ` (measure-preserving involution).
    have hLHS : (∫ w, ((fderiv ℝ ψ w) 1) • f (σ w))
        = ∫ z, ((fderiv ℝ ψ (σ z)) 1) • f z := by
      have := MeasureTheory.integral_comp σ (fun w => ((fderiv ℝ ψ w) 1) • f (σ w))
      rw [← this]
      refine integral_congr_ae ?_; filter_upwards with z; rw [hσ_invol]
    have hRHS : (∫ w, ψ w • gy (σ w)) = ∫ z, ψ (σ z) • gy z := by
      have := MeasureTheory.integral_comp σ (fun w => ψ w • gy (σ w))
      rw [← this]
      refine integral_congr_ae ?_; filter_upwards with z; rw [hσ_invol]
    rw [hLHS, hRHS]
    exact hH
  -- Local integrability of `f∘σ` and `gy∘σ` (preserved by `σ`).
  have hLIcomp : ∀ {u : ℂ → ℂ}, LocallyIntegrable u volume →
      LocallyIntegrable (fun z => u (σ z)) volume := by
    intro u hu
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    have hpre : (σ ⁻¹' (σ '' K)) = K := Set.preimage_image_eq _ σ.injective
    have hKimg : IsCompact (σ '' K) := hK.image σ.continuous
    have := (hmp.integrableOn_comp_preimage hemb (f := u) (s := σ '' K)).mpr
      (hu.integrableOn_isCompact hKimg)
    rwa [hpre] at this
  -- ============ APPLY THE HORIZONTAL THEOREM ============
  obtain ⟨F', hF'ae, hF'acl⟩ :=
    exists_aclHorizontal_of_hasWeakDirDeriv_one (hLIcomp hf) (hLIcomp hgy) hweak
  -- =================== TRANSFER THE CONCLUSION BACK ===================
  refine ⟨fun z => F' (σ z), ?_, ?_⟩
  · -- `F'∘σ =ᵐ f`: precompose `F' =ᵐ f∘σ` with `σ`, then use `σ∘σ = id`.
    have := hmp.quasiMeasurePreserving.ae_eq_comp hF'ae
    refine this.trans ?_
    filter_upwards with z
    simp only [Function.comp_apply, hσ_invol]
  · -- `ACLVertical (F'∘σ) gy`: the `∀ᵐ`-over-`ℝ` index is shared; the vertical
    -- slice `t ↦ (F'∘σ)⟨x,t⟩ = t ↦ F'⟨t,x⟩` is the horizontal slice of `F'`, and
    -- `(gy∘σ)⟨y,x⟩ = gy⟨x,y⟩`, so the two clauses match termwise.
    filter_upwards [hF'acl] with x hx
    obtain ⟨hac, hderiv⟩ := hx
    refine ⟨?_, ?_⟩
    · intro a b
      have heq : (fun y : ℝ => F' (σ ⟨x, y⟩)) = (fun u : ℝ => F' ⟨u, x⟩) := by
        funext y; rw [hσ_apply]
      rw [heq]; exact hac a b
    · filter_upwards [hderiv] with y hy
      have heqf : (fun t : ℝ => F' (σ ⟨x, t⟩)) = (fun t : ℝ => F' ⟨t, x⟩) := by
        funext t; rw [hσ_apply]
      have heqg : gy (σ ⟨y, x⟩) = gy ⟨x, y⟩ := by rw [hσ_apply]
      rw [heqf, ← heqg]
      exact hy

end NoWanderingDomains
