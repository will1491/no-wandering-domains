/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Regularity.RingModulus
import NoWanderingDomains.QC.Regularity.GeometricDilatation
import NoWanderingDomains.QC.Equivalence

/-!
# Quasiconformal transport of the round-annulus ring modulus

For a geometrically `K`-quasiconformal homeomorphism `f`, the modulus of the image of the
connecting family of a round annulus is at most `K` times the round-annulus modulus
`2π / log(R/r)`.

The route runs through the pointwise dilatation bound `geometric_pointwise_dilatation`: the
length–area change of variables driven by `‖(Df)⁻¹‖² · det (Df) ≤ K` transports the extremal
density of the source ring to an admissible density for the image connecting family with energy
inflated by at most `K` (`ring_image_modulus_le`). Combined with the closed-form source modulus
`source_ring_modulus` (`= 2π / log(R/r)`), this gives the transported bound.

## Main statements

* `source_ring_modulus` — the round-annulus connecting-family modulus equals `2π / log(R/r)`;
* `ring_image_modulus_le` — the dilatation-controlled transport of the connecting-family modulus;
* `geometric_ring_modulus_transport` — the image ring modulus is at most `K · (2π / log(R/r))`.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology Real

namespace NoWanderingDomains

/-- **Closed form of the round-annulus modulus.** For radii `0 < r < R`, the conformal modulus of
the connecting family joining the inner circle `{|z - z₀| = r}` to the outer circle
`{|z - z₀| = R}` inside the round annulus equals `2π / log(R/r)`. This is `ringModulus_roundAnnulus`
read through the definition of `ringModulus` as the connecting-family modulus. -/
theorem source_ring_modulus {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    curveModulus (connectingCurveFamily (innerCircle z₀ r) (outerCircle z₀ R)
        (RoundAnnulus z₀ r R))
      = ENNReal.ofReal (2 * Real.pi / Real.log (R / r)) :=
  ringModulus_roundAnnulus hr hrR

/-- **Almost-everywhere dilatation bound from the analytic Beltrami bound.** For an
`IsQCAnalytic` map `f` with Beltrami norm at most `(K − 1)/(K + 1)`, the pointwise
dilatation `‖(Df z)⁻¹‖² · det (Df z)` is at most `K` for almost every `z`. This is the
Wirtinger derivation `‖(Df)⁻¹‖² · det Df = (‖∂f‖ + ‖∂̄f‖)/(‖∂f‖ − ‖∂̄f‖)`, bounded by
`(1 + ‖μ‖)/(1 − ‖μ‖) ≤ K` from the Beltrami equation `∂̄f = μ · ∂f` and the essential-sup
bound `‖μ‖ ≤ (K − 1)/(K + 1)`. -/
private theorem ae_dilatation_of_isQCAnalytic {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    {b : BeltramiCoeff} (hb : b.normInf ≤ (K - 1) / (K + 1)) (hf : IsQCAnalytic f b) :
    ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K := by
  have hμae : ∀ᵐ z : ℂ, ‖b.μ z‖ ≤ b.normInf := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := ne_top_of_lt b.bound
    have hz' : (‖b.μ z‖₊ : ℝ≥0∞) ≤ eLpNormEssSup b.μ volume := by
      simpa [enorm_eq_nnnorm] using hz
    have := (ENNReal.toReal_le_toReal (by simp) hfin).mpr hz'
    simpa [BeltramiCoeff.normInf, coe_nnnorm] using this
  have hkbound : b.normInf < 1 := b.normInf_lt_one
  have hKkey : (1 + b.normInf) / (1 - b.normInf) ≤ K := by
    have hknn : (0 : ℝ) ≤ b.normInf := b.normInf_nonneg
    have hKpos : (0 : ℝ) < K + 1 := by linarith
    have hk_le : b.normInf ≤ (K - 1) / (K + 1) := hb
    have h1mk : (0 : ℝ) < 1 - b.normInf := by linarith
    rw [div_le_iff₀ h1mk]
    have hk_mul : b.normInf * (K + 1) ≤ K - 1 := by
      rw [← le_div_iff₀ hKpos]; exact hk_le
    nlinarith [hk_mul]
  filter_upwards [hf.1.2, hf.2.2, hμae] with z hdet hbel hμz
  set p : ℂ := dz f z with hp
  set q : ℂ := dzbar f z with hq
  set d : ℝ := (fderiv ℝ f z).det with hd
  have hdval : d = ‖p‖ ^ 2 - ‖q‖ ^ 2 := det_fderiv_eq_wirtinger f z
  have hinvval : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ = (‖p‖ + ‖q‖) / d :=
    opNorm_inverse_eq_wirtinger f z hdet
  have hqeq : ‖q‖ = ‖b.μ z‖ * ‖p‖ := by rw [hq, ← hq, hbel, norm_mul]
  have hqp : ‖q‖ ≤ b.normInf * ‖p‖ := by rw [hqeq]; gcongr
  have hdpos : 0 < d := hdet
  have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg q, norm_nonneg p, hdval, hdpos]
  have hpqlt : ‖q‖ < ‖p‖ := by nlinarith [hdval, hdpos, norm_nonneg p]
  have hpmq : 0 < ‖p‖ - ‖q‖ := by linarith
  have hfactor : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * d
      = (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) := by
    rw [hinvval, div_pow, hdval]
    have hsplit : ‖p‖ ^ 2 - ‖q‖ ^ 2 = (‖p‖ + ‖q‖) * (‖p‖ - ‖q‖) := by ring
    rw [hsplit]
    have hsum_ne : ‖p‖ + ‖q‖ ≠ 0 := by positivity
    have hpmq_ne : ‖p‖ - ‖q‖ ≠ 0 := ne_of_gt hpmq
    field_simp
  rw [hfactor]
  refine le_trans ?_ hKkey
  rw [div_le_div_iff₀ hpmq (by linarith : (0:ℝ) < 1 - b.normInf)]
  nlinarith [hqp, hppos]

/-- **Dilatation-controlled transport of the connecting-family modulus.** Given the pointwise
dilatation bound `‖(Df)⁻¹‖² · det (Df) ≤ K` almost everywhere (the output of
`geometric_pointwise_dilatation`) and the regularity of a geometrically `K`-quasiconformal
homeomorphism `f`, the image of the connecting family of the round annulus has modulus at most `K`
times the source connecting-family modulus. The image family joins the image inner circle
`f '' innerCircle` to the image outer circle `f '' outerCircle` inside the image annulus
`f '' RoundAnnulus`. The proof is the length–area change of variables: the extremal density of the
source ring is transported to an admissible density for the image family with energy inflated by at
most the dilatation factor `K`. -/
theorem ring_image_modulus_le {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (_hdil : ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K)
    {z₀ : ℂ} {r R : ℝ} (_hr : 0 < r) (_hrR : r < R) :
    curveModulus (connectingCurveFamily (f '' innerCircle z₀ r) (f '' outerCircle z₀ R)
        (f '' RoundAnnulus z₀ r R))
      ≤ ENNReal.ofReal K * curveModulus (connectingCurveFamily (innerCircle z₀ r)
        (outerCircle z₀ R) (RoundAnnulus z₀ r R)) := by
  classical
  -- The analytic-quasiconformal structure supplied by the equivalence bridge.
  obtain ⟨b, hb, hfa⟩ := isQCAnalytic_of_isQCGeometric hf.1 hf
  -- The inverse homeomorphism `g = f⁻¹` and the two inversion identities.
  set g : ℂ → ℂ := ⇑(hfa.1.1.homeomorph f).symm with hg
  have hfwd : ∀ z, (hfa.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hfa.1.1 z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hfa.1.1.homeomorph f).symm w)]
    exact (hfa.1.1.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg, ← hfwd z]
    exact (hfa.1.1.homeomorph f).symm_apply_apply z
  have hgcont : Continuous g := (hfa.1.1.homeomorph f).continuous_symm
  -- The source connecting family and the image connecting family.
  set Γ : Set (ℝ → ℂ) :=
    connectingCurveFamily (innerCircle z₀ r) (outerCircle z₀ R) (RoundAnnulus z₀ r R) with hΓ
  set Δ : Set (ℝ → ℂ) :=
    connectingCurveFamily (f '' innerCircle z₀ r) (f '' outerCircle z₀ R)
      (f '' RoundAnnulus z₀ r R) with hΔ
  -- The `f`-degeneracy set `Nf` in the source.
  set Nf : Set ℂ := {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hNf
  have hNfmeas : MeasurableSet Nf := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    have hrw : Nf = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [hNf, Set.mem_compl_iff, not_and]
    rw [hrw]; exact (hd.inter hdet).compl
  -- The members of `Δ` are continuous and absolutely continuous.
  have hΔcont : ∀ δ ∈ Δ, Continuous δ := fun δ hδ => hδ.1
  have hΔac : ∀ δ ∈ Δ, AbsolutelyContinuousOnInterval δ 0 1 := fun δ hδ => hδ.2.1
  -- The `g`-chain-rule exceptional subfamily and the image-stationary subfamily.
  set Δbad : Set (ℝ → ℂ) :=
    {δ ∈ Δ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (g ∘ δ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv δ t ≠ 0 → 0 < (fderiv ℝ g (δ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv δ t ≠ 0 →
          HasDerivAt (g ∘ δ) ((fderiv ℝ g (δ t)) (deriv δ t)) t)} with hΔbad
  set Δmeet : Set (ℝ → ℂ) :=
    {δ ∈ Δ | 1 ≤ arcLengthLineIntegral (Nf.indicator (fun _ => ∞)) (g ∘ δ)} with hΔmeet
  set Δexc : Set (ℝ → ℂ) := Δbad ∪ Δmeet with hΔexc
  -- The inverse `g` is itself analytic-quasiconformal, so `Δbad` has zero modulus.
  obtain ⟨b', hg_qc⟩ : ∃ b' : BeltramiCoeff, IsQCAnalytic g b' := hfa.inverse_isQCAnalytic
  have hbad0 : curveModulus Δbad = 0 :=
    IsQCAnalytic.chainRule_exceptional_modulus_zero hg_qc Δ hΔcont hΔac
  -- The image-stationary subfamily has zero modulus.
  have hmeet0 : curveModulus Δmeet = 0 :=
    isQCGeometric_imageStationary_residual_modulus_zero hfa Δ hΔcont hΔac
  have hexc0 : curveModulus Δexc = 0 := curveModulus_union_zero hbad0 hmeet0
  -- The `f`-chain-rule exceptional predicate on source curves.
  set Γfbadprop : (ℝ → ℂ) → Prop := fun γ =>
    ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t) with hΓfbadprop
  -- The non-exceptional good part embeds in the `f`-pushforward of the good source curves.
  have hgood_sub :
      Δ \ Δexc ⊆
        (fun γ : ℝ → ℂ => f ∘ γ) '' (Γ \ {γ ∈ Γ | Γfbadprop γ}) := by
    rintro δ ⟨hδΔ, hδnotexc⟩
    have hδnotbad : δ ∉ Δbad := fun h => hδnotexc (Or.inl h)
    have hδnotmeet : δ ∉ Δmeet := fun h => hδnotexc (Or.inr h)
    have hδgood : (∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (g ∘ δ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv δ t ≠ 0 → 0 < (fderiv ℝ g (δ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv δ t ≠ 0 →
          HasDerivAt (g ∘ δ) ((fderiv ℝ g (δ t)) (deriv δ t)) t := by
      by_contra hc; exact hδnotbad ⟨hδΔ, hc⟩
    obtain ⟨hgAC, _hgdet, _hgchain⟩ := hδgood
    have hδmemΔ : δ ∈ Δ := hδΔ
    obtain ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩ := hδΔ
    have h01 : Set.uIcc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (zero_le_one)]
    set γ : ℝ → ℂ := g ∘ δ with hγ
    have hγcont : Continuous γ := hgcont.comp hδcont
    have hγac : AbsolutelyContinuousOnInterval γ 0 1 := hgAC 0 1 h01
    have hmeet : ¬ 1 ≤ arcLengthLineIntegral (Nf.indicator (fun _ => (∞ : ℝ≥0∞))) γ := by
      intro hge; exact hδnotmeet ⟨hδmemΔ, hge⟩
    have hfgood : (∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
          HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t := by
      have hfγeq : f ∘ γ = δ := by funext t; simp only [hγ, Function.comp_apply, hfg (δ t)]
      set B : Set ℝ := {t : ℝ | deriv γ t ≠ 0 ∧ γ t ∈ Nf} with hB
      have hBmeas : MeasurableSet B := by
        have hd : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
          (measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv γ) |>.compl
        have hpre : MeasurableSet {t : ℝ | γ t ∈ Nf} := hNfmeas.preimage hγcont.measurable
        have hrw : B = {t : ℝ | deriv γ t ≠ 0} ∩ {t : ℝ | γ t ∈ Nf} := by
          ext t; simp [hB, Set.mem_inter_iff]
        rw [hrw]; exact hd.inter hpre
      have hintegrand : ∀ t, (Nf.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
          (‖deriv γ t‖₊ : ℝ≥0∞) = B.indicator (fun _ => (∞ : ℝ≥0∞)) t := by
        intro t
        by_cases hd : deriv γ t = 0
        · have htB : t ∉ B := fun h => h.1 hd
          rw [Set.indicator_of_notMem htB]; simp [hd]
        · by_cases hγN : γ t ∈ Nf
          · have htB : t ∈ B := ⟨hd, hγN⟩
            have hnz : (‖deriv γ t‖₊ : ℝ≥0∞) ≠ 0 := by
              simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]; exact hd
            rw [Set.indicator_of_mem hγN, Set.indicator_of_mem htB, ENNReal.top_mul hnz]
          · have htB : t ∉ B := fun h => hγN h.2
            rw [Set.indicator_of_notMem hγN, Set.indicator_of_notMem htB, zero_mul]
      have hLI : arcLengthLineIntegral (Nf.indicator (fun _ => (∞ : ℝ≥0∞))) γ
          = (∞ : ℝ≥0∞) * volume (B ∩ Set.Icc (0 : ℝ) 1) := by
        unfold arcLengthLineIntegral
        rw [show (fun t => (Nf.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
            (‖deriv γ t‖₊ : ℝ≥0∞)) = B.indicator (fun _ => (∞ : ℝ≥0∞)) from funext hintegrand]
        rw [lintegral_indicator hBmeas, setLIntegral_const,
          Measure.restrict_apply hBmeas, Set.inter_comm]
      have hBnull : volume (B ∩ Set.Icc (0 : ℝ) 1) = 0 := by
        by_contra hpos
        apply hmeet; rw [hLI, ENNReal.top_mul hpos]; exact le_top
      have hγNnegl : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → (DifferentiableAt ℝ f (γ t) ∧ 0 < (fderiv ℝ f (γ t)).det) := by
        rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
        apply measure_mono_null _ hBnull
        intro t ht
        simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
        obtain ⟨hmem, hd, hnotgood⟩ := ht
        refine ⟨⟨hd, ?_⟩, hmem⟩
        simp only [hNf, Set.mem_ofPred_eq]; exact hnotgood
      have hdiffγ : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          DifferentiableAt ℝ γ t := by
        rw [ae_restrict_iff' measurableSet_Icc]
        have hbv : BoundedVariationOn γ (Set.uIcc (0 : ℝ) 1) := hγac.boundedVariationOn
        filter_upwards [hbv.ae_differentiableAt_of_mem_uIcc] with t ht htmem
        exact ht (by rw [Set.uIcc_of_le (by norm_num)]; exact htmem)
      refine ⟨?_, ?_, ?_⟩
      · intro a c hac
        rw [hfγeq]
        exact hδac.mono_subinterval hac
      · filter_upwards [hγNnegl] with t hgoodt hγderiv
        exact (hgoodt hγderiv).2
      · filter_upwards [hγNnegl, hdiffγ] with t hgoodt hdiffγt hγderiv
        have hfd : HasFDerivAt f (fderiv ℝ f (γ t)) (γ t) := (hgoodt hγderiv).1.hasFDerivAt
        have hγd : HasDerivAt γ (deriv γ t) t := hdiffγt.hasDerivAt
        exact hfd.comp_hasDerivAt t hγd
    -- Hence `γ ∈ Γ` (source connecting family) and `γ` is `f`-good, and `δ = f ∘ γ`.
    refine ⟨γ, ⟨⟨hγcont, hγac, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨p, hp, hpeq⟩ := hδ0
      simp only [hγ, Function.comp_apply]; rw [← hpeq, hgf p]; exact hp
    · obtain ⟨p, hp, hpeq⟩ := hδ1
      simp only [hγ, Function.comp_apply]; rw [← hpeq, hgf p]; exact hp
    · intro t ht
      obtain ⟨p, hp, hpeq⟩ := hδimg t ht
      simp only [hγ, Function.comp_apply]; rw [← hpeq, hgf p]; exact hp
    · intro hmem; exact (not_not.mpr hfgood) hmem.2
    · funext t; simp only [hγ, Function.comp_apply, hfg (δ t)]
  -- Bound the good part by the clean pushforward energy transfer.
  have hΓcont : ∀ γ ∈ Γ, Continuous γ := fun γ hγ => hγ.1
  have hΓac : ∀ γ ∈ Γ, AbsolutelyContinuousOnInterval γ 0 1 := fun γ hγ => hγ.2.1
  have hpush := pushforwardGood_modulus_le hf.1 hb hfa Γ hΓcont hΓac
  have hgood_le : curveModulus (Δ \ Δexc) ≤ ENNReal.ofReal K * curveModulus Γ := by
    refine le_trans (curveModulus_mono hgood_sub) ?_
    exact hpush
  -- Remove the zero-modulus exceptional part.
  have hexcsub : Δexc ⊆ Δ := by
    rw [hΔexc]; exact Set.union_subset (Set.sep_subset _ _) (Set.sep_subset _ _)
  have hsdiff : curveModulus (Δ \ Δexc) = curveModulus Δ :=
    curveModulus_sdiff_modulus_zero hexcsub hexc0
  rw [← hsdiff]; exact hgood_le

/-- **Quasiconformal transport of the round-annulus modulus.** For a geometrically
`K`-quasiconformal homeomorphism `f`, the modulus of the image of the round-annulus connecting
family is at most `K · (2π / log(R/r))`. This chains the dilatation-controlled transport
`ring_image_modulus_le`, driven by the almost-everywhere dilatation bound
`ae_dilatation_of_isQCAnalytic` extracted from the analytic ⇔ geometric bridge, with the
closed-form source modulus `source_ring_modulus`. -/
theorem geometric_ring_modulus_transport {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    curveModulus (connectingCurveFamily (f '' innerCircle z₀ r) (f '' outerCircle z₀ R)
        (f '' RoundAnnulus z₀ r R))
      ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * Real.pi / Real.log (R / r)) := by
  obtain ⟨b, hb, hfa⟩ := isQCAnalytic_of_isQCGeometric hf.1 hf
  have hdil := ae_dilatation_of_isQCAnalytic hf.1 hb hfa
  calc curveModulus (connectingCurveFamily (f '' innerCircle z₀ r) (f '' outerCircle z₀ R)
          (f '' RoundAnnulus z₀ r R))
      ≤ ENNReal.ofReal K * curveModulus (connectingCurveFamily (innerCircle z₀ r)
          (outerCircle z₀ R) (RoundAnnulus z₀ r R)) :=
        ring_image_modulus_le hf hdil hr hrR
    _ = ENNReal.ofReal K * ENNReal.ofReal (2 * Real.pi / Real.log (R / r)) := by
        rw [source_ring_modulus hr hrR]

end NoWanderingDomains
