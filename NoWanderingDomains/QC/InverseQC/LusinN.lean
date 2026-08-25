/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.LengthArea.LengthAreaInverse
import NoWanderingDomains.QC.LengthArea.ReverseLengthArea
import NoWanderingDomains.QC.Foundations.MultiplicityAreaFormula
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.LpHighOpNorm
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.Beltrami
import NoWanderingDomains.Analysis.Sobolev.Morrey.LusinN

/-!
# The inverse of an analytic-quasiconformal map is analytic-quasiconformal

This subfolder proves, in a dependency-ordered chain, that the homeomorphic inverse of an
`IsQCAnalytic` map is again `IsQCAnalytic` (with the "reflected" Beltrami
coefficient). This is the *inverse-is-QC* root that unlocks the genuine
`isQCGeometric_of_isQCAnalytic` modulus bound, which follows by applying the
*source-side* length–area machinery to the inverse map `g = f⁻¹`. The signatures are
maximally general and mathematically faithful.

## The chain

1. `beltrami_higher_integrability` — **Bojarski higher integrability** (the hard
   load-bearing analytic lemma): a `W^{1,2}_loc` solution of an elliptic Beltrami
   equation `∂̄f = μ ∂f` with `‖μ‖∞ < 1` has its `∂`-derivative locally in `Lᵖ` for
   some exponent `p > 2`. Driven by the `Lᵖ` operator-norm continuity of the
   Beurling transform near `p = 2` (`Analysis/SingularIntegral/Beurling`).
2. `IsQCAnalytic.dz_higher_integrability` — the same conclusion specialised to an
   `IsQCAnalytic` map, feeding (1) the `MemW12loc` and Beltrami fields.
3. `IsQCAnalytic.inverse_differentiableAt_ae` — the inverse homeomorphism `g = f⁻¹`
   is differentiable almost everywhere (a `W^{1,p}`, `p > 2`, inverse function
   theorem fed by (2)).
4. `IsQCAnalytic.inverse_beltrami` — `g` solves a Beltrami equation
   `∂̄g = b'.μ ∂g` a.e. for an explicit `b' : BeltramiCoeff` (so `b'.normInf < 1`),
   the "reflected" coefficient.
5. `IsQCAnalytic.inverse_memW12loc` — `g ∈ W^{1,2}_loc`.
6. `IsQCAnalytic.inverse_orientationPreservingHomeo` — `g` is an
   orientation-preserving homeomorphism.
7. `IsQCAnalytic.inverse_isQCAnalytic` — **the root**: `g` is `IsQCAnalytic` for
   some `b'` (assembles 4, 5, 6).
8. `IsQCAnalytic.image_lusinN` — planar **Lusin-(N)** for the degeneracy set:
   `volume (f '' {z | f not differentiable-with-positive-Jacobian at z}) = 0`,
   the crux of the image-side exceptional sweep (follows from (7) by running the
   source-side change of variables for `g`).

The genuine modulus bound is assembled downstream in `QC/Equivalence.lean`.

The predicate used for "`∂f` is locally `Lᵖ`" is the repo's existing
`MemLpLocOn (fun z => dz f z) (ENNReal.ofReal p) Set.univ` (from
`Analysis/Sobolev/WeakDeriv.lean`): `Lᵖ` on every compact subset of the plane.
-/

open MeasureTheory Complex
open scoped ENNReal ComplexConjugate

namespace NoWanderingDomains

/-- **Bojarski higher integrability** (the hard load-bearing analytic lemma),
phrased on the **weak gradient** (the sound statement).

A function `f : ℂ → ℂ` in `W^{1,2}_loc` with weak partials `gx, gy` (directions `1`,
`I`, loc-`L²`) solving an *elliptic* Beltrami equation in its weak Wirtinger form
`½(gx + i gy) = μ · ½(gx − i gy)` almost everywhere, with `‖μ‖∞ < 1`, has its **weak**
holomorphic Wirtinger derivative `½(gx − i gy)` locally in `Lᵖ` for some `p > 2`.

This is the mathematically honest content: it speaks of the weak gradient, never of
the pointwise Fréchet derivative `fderiv ℝ f`. The previous form concluded about
`dz f` (built from `fderiv`) and silently assumed `dz f =ᵐ ½(gx − i gy)`, which is
false for a bare `W^{1,2}_loc` function. The pointwise passage is performed by the
quasiconformal consumer below.

*Proof sketch.* Write the Beltrami equation as a fixed point of the Beurling/Hilbert
transform `S` on the weak `∂`-field: `∂f = h + S(μ · ∂f)` for a holomorphic
remainder. The `Lᵖ` operator norm of `S` is continuous in `p` with `‖S‖₂ = 1`
(`Analysis/SingularIntegral/Beurling`), so for `p` slightly above `2` one still has
`‖μ‖∞ · ‖S‖ₚ < 1`; the resulting Neumann series converges in `Lᵖ`, giving local
`Lᵖ` control. *Dependency:* `dz_memLpLocOn_of_beltrami` (L6). -/
theorem beltrami_higher_integrability {μ : ℂ → ℂ} (hμmeas : Measurable μ)
    (hμbound : eLpNormEssSup μ volume < 1) {f gx gy : ℂ → ℂ}
    (hfcont : Continuous f)
    (hfLp : MemLpLocOn f (2 : ℝ≥0∞) Set.univ)
    (hgx : HasWeakDirDeriv 1 gx f Set.univ) (hgy : HasWeakDirDeriv Complex.I gy f Set.univ)
    (hgxLp : MemLpLocOn gx (2 : ℝ≥0∞) Set.univ) (hgyLp : MemLpLocOn gy (2 : ℝ≥0∞) Set.univ)
    (hbel : ∀ᵐ z, (1 / 2 : ℂ) * (gx z + Complex.I * gy z)
      = μ z * ((1 / 2 : ℂ) * (gx z - Complex.I * gy z))) :
    ∃ p : ℝ, 2 < p ∧
      MemLpLocOn (fun z => (1 / 2 : ℂ) * (gx z - Complex.I * gy z)) (ENNReal.ofReal p)
        Set.univ :=
  -- Reduced to the assembled Beurling sub-decomposition lemma `L6`
  -- (`dz_memLpLocOn_of_beltrami`) in
  -- `Analysis/SingularIntegral/Beurling/Beltrami.lean`, whose statement matches
  -- this conclusion verbatim. Continuity of `f` is threaded into L6 to upgrade the
  -- cutoff-commutator remainder to `L³` (the `δ = 1` higher integrability the corrected
  -- Gehring forcing term consumes).
  dz_memLpLocOn_of_beltrami hμmeas hμbound hfcont hfLp hgx hgy hgxLp hgyLp hbel

/-- **The strong⇄weak Wirtinger bridge for an analytic-quasiconformal map.** For an
`IsQCAnalytic` map `f` with the canonical weak gradient `(gx, gy)` of `MemW12loc f`,
the pointwise holomorphic Wirtinger derivative `dz f` agrees almost everywhere with
the **weak** holomorphic Wirtinger derivative `½(gx − i gy)`.

This is sound *for `IsQCAnalytic`* — unlike for a bare `W^{1,2}_loc` function — because
the orientation/Jacobian datum of `IsQCAnalytic` supplies a.e. differentiability
(`IsQCAnalytic.ae_differentiableAt`), at which point the converse-of-ACL bridge
`fderiv_ae_eq_weakDirDeriv` identifies each pointwise directional derivative
`(fderiv ℝ f ·) v` with the corresponding weak partial a.e. (`v ∈ {1, I}`).
*Dependency:* `fderiv_ae_eq_weakDirDeriv`, `IsQCAnalytic.ae_differentiableAt`. -/
theorem IsQCAnalytic.dz_aeeq_weakDz {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    {gx gy : ℂ → ℂ} (hgx : HasWeakDirDeriv 1 gx f Set.univ)
    (hgy : HasWeakDirDeriv Complex.I gy f Set.univ)
    (hgxLp : MemLpLocOn gx (2 : ℝ≥0∞) Set.univ) (hgyLp : MemLpLocOn gy (2 : ℝ≥0∞) Set.univ) :
    (fun z => dz f z) =ᵐ[volume] (fun z => (1 / 2 : ℂ) * (gx z - Complex.I * gy z)) := by
  -- `f` is differentiable a.e. (orientation preservation, Gehring–Lehto).
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ f z := IsQCAnalytic.ae_differentiableAt hf
  -- `f` is locally integrable (it is a continuous homeomorphism).
  have hfloc : LocallyIntegrable f := hf.1.1.continuous.locallyIntegrable
  -- Local integrability of the weak partials, from their loc-`L²` membership.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      LocallyIntegrableOn g Set.univ := by
    intro g hg
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MemLp g 1 (volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp hmem1
  have hgxloc : LocallyIntegrableOn gx Set.univ := memLpLoc_to_loc hgxLp
  have hgyloc : LocallyIntegrableOn gy Set.univ := memLpLoc_to_loc hgyLp
  -- The converse-of-ACL bridge: classical partials equal the weak partials a.e.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hgx hgxloc hdiff (Or.inl rfl) hfloc
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hgy hgyloc hdiff (Or.inr rfl) hfloc
  -- Combine into `dz f = ½((fderiv) 1 − i (fderiv) I) =ᵐ ½(gx − i gy)`.
  filter_upwards [haex, haey] with z hzx hzy
  simp only [dz, hzx, hzy]

/-- **Higher integrability for an analytic-quasiconformal map.** The holomorphic
Wirtinger derivative `∂f` of an `IsQCAnalytic` map is locally `Lᵖ` for some `p > 2`.

*Proof sketch.* Unpack the canonical weak gradient `(gx, gy)` of `MemW12loc f`. The
pointwise Beltrami field `hf.2.2 : ∂̄f = b.μ ∂f` transports — via the strong⇄weak
bridge `IsQCAnalytic.dz_aeeq_weakDz` — to the *weak* Beltrami equation
`½(gx + i gy) = b.μ · ½(gx − i gy)`, so `beltrami_higher_integrability` gives
`½(gx − i gy) ∈ Lᵖ_loc`. The same bridge `dz f =ᵐ ½(gx − i gy)` then converts the
weak conclusion back to the pointwise one (`MemLpLocOn` respects a.e.-equality).
*Dependency:* `beltrami_higher_integrability`, `IsQCAnalytic.dz_aeeq_weakDz`. -/
theorem IsQCAnalytic.dz_higher_integrability {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ p : ℝ, 2 < p ∧ MemLpLocOn (fun z => dz f z) (ENNReal.ofReal p) Set.univ := by
  -- The canonical weak gradient `(gx, gy)` of `MemW12loc f`.
  obtain ⟨hfLp, gx, gy, ⟨hgx, hgy⟩, hmgx, hmgy⟩ := hf.2.1
  have hgxLp : MemLpLocOn gx 2 Set.univ := hmgx
  have hgyLp : MemLpLocOn gy 2 Set.univ := hmgy
  -- The strong⇄weak bridge `dz f =ᵐ ½(gx − i gy)`.
  have hbridge := hf.dz_aeeq_weakDz hgx hgy hgxLp hgyLp
  -- Transport the pointwise Beltrami equation `hf.2.2` to its weak form.
  have hbel : ∀ᵐ z, (1 / 2 : ℂ) * (gx z + Complex.I * gy z)
      = b.μ z * ((1 / 2 : ℂ) * (gx z - Complex.I * gy z)) := by
    -- `dzbar f =ᵐ ½(gx + i gy)` from the bridge (using `dzbar f = dz f + i (fderiv) I`-type
    -- algebra is unnecessary: derive directly from the two partial bridges as below).
    have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
      fderiv_ae_eq_weakDirDeriv hgx (by
        rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
        intro k hk
        have : IsFiniteMeasure (volume.restrict k) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
        exact memLp_one_iff_integrable.mp ((hgxLp k (Set.subset_univ _) hk).mono_exponent
          (by norm_num)))
        (IsQCAnalytic.ae_differentiableAt hf) (Or.inl rfl)
        (hf.1.1.continuous.locallyIntegrable)
    have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
      fderiv_ae_eq_weakDirDeriv hgy (by
        rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
        intro k hk
        have : IsFiniteMeasure (volume.restrict k) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
        exact memLp_one_iff_integrable.mp ((hgyLp k (Set.subset_univ _) hk).mono_exponent
          (by norm_num)))
        (IsQCAnalytic.ae_differentiableAt hf) (Or.inr rfl)
        (hf.1.1.continuous.locallyIntegrable)
    filter_upwards [hf.2.2, haex, haey] with z hbelz hzx hzy
    -- `dzbar f z = ½((fderiv) 1 + i (fderiv) I) = ½(gx + i gy)`,
    -- `dz f z = ½((fderiv) 1 − i (fderiv) I) = ½(gx − i gy)`.
    have hdzbar : dzbar f z = (1 / 2 : ℂ) * (gx z + Complex.I * gy z) := by
      simp only [dzbar, hzx, hzy]
    have hdz : dz f z = (1 / 2 : ℂ) * (gx z - Complex.I * gy z) := by
      simp only [dz, hzx, hzy]
    rw [← hdzbar, ← hdz]; exact hbelz
  -- Apply the (sound, weak-gradient) Bojarski lemma, then convert back to `dz f`.
  -- The new `Continuous f` hypothesis is discharged by `hf.1.1.continuous` (the map is a
  -- homeomorphism, already used above for local integrability of `f`).
  obtain ⟨p, hp2, hlocp⟩ :=
    beltrami_higher_integrability b.measurable b.bound hf.1.1.continuous hfLp hgx hgy
      hgxLp hgyLp hbel
  refine ⟨p, hp2, ?_⟩
  -- `MemLpLocOn` respects a.e.-equality: `dz f =ᵐ ½(gx − i gy)` and the latter is `Lᵖ_loc`.
  intro K hKuniv hKcompact
  exact (hlocp K hKuniv hKcompact).ae_eq
    (Filter.EventuallyEq.symm (ae_restrict_of_ae hbridge))

/-- **Super-critical weak gradient.** An `IsQCAnalytic` map has a weak gradient `(gx, gy)`
whose components are locally `Lᵖ` for some `p > 2`. This packages the higher integrability
`IsQCAnalytic.dz_higher_integrability` (`∂f ∈ Lᵖ_loc`) with the Beltrami relation
`∂̄f = b.μ · ∂f` and the dilatation bound `‖b.μ‖∞ < 1` (so `∂̄f ∈ Lᵖ_loc` too), via the
partial decomposition `gx = ∂f + ∂̄f`, `gy = i(∂f − ∂̄f)`. *Dependency:*
`dz_higher_integrability`, `dz_aeeq_weakDz`. -/
theorem IsQCAnalytic.exists_weakGradient_memLpLocOn_gt_two {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ (p : ℝ) (gx gy : ℂ → ℂ), 2 < p ∧ HasWeakGradient gx gy f Set.univ ∧
      MemLpLocOn gx (ENNReal.ofReal p) Set.univ ∧
      MemLpLocOn gy (ENNReal.ofReal p) Set.univ := by
  -- The canonical weak gradient `(gx, gy)` of `MemW12loc f`, with loc-`L²` partials.
  obtain ⟨hfLp, gx, gy, ⟨hgx, hgy⟩, hmgx, hmgy⟩ := hf.2.1
  have hgxLp : MemLpLocOn gx 2 Set.univ := hmgx
  have hgyLp : MemLpLocOn gy 2 Set.univ := hmgy
  -- Higher integrability of `∂f`: `∂f ∈ Lᵖ_loc` for some `p > 2`.
  obtain ⟨p, hp2, hdzp⟩ := hf.dz_higher_integrability
  -- The strong⇄weak Wirtinger bridges identify `dz`/`dzbar f` with the weak partials.
  have hbridge_dz := hf.dz_aeeq_weakDz hgx hgy hgxLp hgyLp
  -- The `∂̄`-bridge `dzbar f =ᵐ ½(gx + i gy)`, derived inline from the two partial
  -- bridges exactly as in `dz_higher_integrability`.
  have hbridge_dzbar : (fun z => dzbar f z) =ᵐ[volume]
      (fun z => (1 / 2 : ℂ) * (gx z + Complex.I * gy z)) := by
    have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
      fderiv_ae_eq_weakDirDeriv hgx (by
        rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
        intro k hk
        have : IsFiniteMeasure (volume.restrict k) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
        exact memLp_one_iff_integrable.mp ((hgxLp k (Set.subset_univ _) hk).mono_exponent
          (by norm_num)))
        (IsQCAnalytic.ae_differentiableAt hf) (Or.inl rfl)
        (hf.1.1.continuous.locallyIntegrable)
    have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
      fderiv_ae_eq_weakDirDeriv hgy (by
        rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
        intro k hk
        have : IsFiniteMeasure (volume.restrict k) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
        exact memLp_one_iff_integrable.mp ((hgyLp k (Set.subset_univ _) hk).mono_exponent
          (by norm_num)))
        (IsQCAnalytic.ae_differentiableAt hf) (Or.inr rfl)
        (hf.1.1.continuous.locallyIntegrable)
    filter_upwards [haex, haey] with z hzx hzy
    simp only [dzbar, hzx, hzy]
  -- `∂̄f =ᵐ b.μ · ∂f`, so `∂̄f ∈ Lᵖ_loc` too (a.e.-bounded multiple of an `Lᵖ_loc`
  -- function, with `‖b.μ‖∞ < 1 ≤ 1` a.e.).
  have hμle : ∀ᵐ z, ‖b.μ z‖ ≤ 1 := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    have h1 : ENNReal.ofReal ‖b.μ z‖ ≤ 1 := by
      rw [ofReal_norm]; exact le_trans hz b.bound.le
    exact ENNReal.ofReal_le_one.mp h1
  have hdzbarp : MemLpLocOn (fun z => dzbar f z) (ENNReal.ofReal p) Set.univ := by
    intro K hKuniv hKcompact
    have hdzK : MemLp (fun z => dz f z) (ENNReal.ofReal p) (volume.restrict K) :=
      hdzp K hKuniv hKcompact
    have hmeasK : AEStronglyMeasurable (fun z => b.μ z * dz f z) (volume.restrict K) :=
      (b.measurable.aestronglyMeasurable).mul hdzK.1
    have hboundK : MemLp (fun z => b.μ z * dz f z) (ENNReal.ofReal p) (volume.restrict K) := by
      refine hdzK.of_le hmeasK ?_
      filter_upwards [ae_restrict_of_ae hμle] with z hz
      rw [norm_mul]
      calc ‖b.μ z‖ * ‖dz f z‖ ≤ 1 * ‖dz f z‖ :=
            mul_le_mul_of_nonneg_right hz (norm_nonneg _)
        _ = ‖dz f z‖ := one_mul _
    -- Transfer to `dzbar f` via `dzbar f =ᵐ b.μ · dz f`.
    refine hboundK.ae_eq ?_
    filter_upwards [ae_restrict_of_ae hf.2.2] with z hz
    simp only [hz]
  -- The weak partials decompose: `gx =ᵐ ∂f + ∂̄f`, `gy =ᵐ i(∂f − ∂̄f)`.
  have hgx_eq : gx =ᵐ[volume] (fun z => dz f z + dzbar f z) := by
    filter_upwards [hbridge_dz, hbridge_dzbar] with z hdz hdzbar
    rw [hdz, hdzbar]; ring
  have hgy_eq : gy =ᵐ[volume] (fun z => Complex.I * (dz f z - dzbar f z)) := by
    filter_upwards [hbridge_dz, hbridge_dzbar] with z hdz hdzbar
    rw [hdz, hdzbar]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (gy z) * hI
  -- `gx, gy ∈ Lᵖ_loc` by closure of `Lᵖ_loc` under sums/scalars, transferred a.e.
  refine ⟨p, gx, gy, hp2, ⟨hgx, hgy⟩, ?_, ?_⟩
  · intro K hKuniv hKcompact
    have hsum : MemLp (fun z => dz f z + dzbar f z) (ENNReal.ofReal p) (volume.restrict K) :=
      (hdzp K hKuniv hKcompact).add (hdzbarp K hKuniv hKcompact)
    exact hsum.ae_eq (Filter.EventuallyEq.symm (ae_restrict_of_ae hgx_eq))
  · intro K hKuniv hKcompact
    have hsub : MemLp (fun z => dz f z - dzbar f z) (ENNReal.ofReal p) (volume.restrict K) :=
      (hdzp K hKuniv hKcompact).sub (hdzbarp K hKuniv hKcompact)
    have hscal : MemLp (fun z => Complex.I * (dz f z - dzbar f z)) (ENNReal.ofReal p)
        (volume.restrict K) := hsub.const_mul Complex.I
    exact hscal.ae_eq (Filter.EventuallyEq.symm (ae_restrict_of_ae hgy_eq))

/-- **Planar Lusin-(N) for the singular set.** For an `IsQCAnalytic` map `f`, the
image under `f` of the set where `f` fails to be (real-)differentiable is
Lebesgue-null.

This is the genuine analytic core of the image-side exceptional sweep. A planar
`W^{1,p}_loc` homeomorphism with `p > 2` (`dz_higher_integrability` gives the higher
integrability `∂f ∈ L^p_loc`, and the dilatation bound `‖b.μ‖∞ < 1` carries `∂̄f`
along) is Hölder-continuous and satisfies the Lusin-(N) property, so it maps the
(null) non-differentiability set to a null set. The Lusin-(N) input is the general
Sobolev fact `lusinN_image_null_of_weakGradient` (`Analysis/Sobolev/Morrey/LusinN.lean`).
*Dependency:* `exists_weakGradient_memLpLocOn_gt_two`, `lusinN_image_null_of_weakGradient`,
`ae_differentiableAt`. -/
theorem IsQCAnalytic.image_singular_set_null {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    volume (f '' {z : ℂ | ¬ DifferentiableAt ℝ f z}) = 0 := by
  obtain ⟨p, gx, gy, hp2, hgrad, hgxp, hgyp⟩ := hf.exists_weakGradient_memLpLocOn_gt_two
  have hNnull : volume {z : ℂ | ¬ DifferentiableAt ℝ f z} = 0 :=
    MeasureTheory.ae_iff.mp (IsQCAnalytic.ae_differentiableAt hf)
  exact lusinN_image_null_of_weakGradient hp2 hf.1.1.continuous hgrad hgxp hgyp hNnull

/-- **Planar Lusin-(N) for the degeneracy set.** For an `IsQCAnalytic` map `f`, the
image under `f` of the set where `f` fails to be differentiable with positive
Jacobian is Lebesgue-null. This is the crux of the image-side exceptional sweep
(the former wall, now removed and superseded by the downstream rebuild in
`QC/Equivalence.lean`).

*Proof sketch.* Split the degeneracy set as `{¬ differentiable} ∪
{differentiable ∧ Jacobian ≤ 0}`. The first piece's image is null by
`image_singular_set_null`. The second piece is itself null in the domain (`hf.1.2`
gives a positive Jacobian almost everywhere, so `{¬ 0 < det}` is null), and `f` is
differentiable on it, so its image is null by Mathlib's
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (a differentiable map
sends null sets to null sets). *Dependency:* `image_singular_set_null`. -/
theorem IsQCAnalytic.image_lusinN {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    volume (f '' {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det}) = 0 := by
  -- Decompose the degeneracy set into the non-differentiability piece and the
  -- (differentiable but) non-positive-Jacobian piece.
  have hsplit : {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det}
      = {z : ℂ | ¬ DifferentiableAt ℝ f z}
        ∪ {z : ℂ | DifferentiableAt ℝ f z ∧ ¬ 0 < (fderiv ℝ f z).det} := by
    ext z
    constructor
    · rintro (hnd | hdet)
      · exact Or.inl hnd
      · rcases Classical.em (DifferentiableAt ℝ f z) with hd | hnd
        · exact Or.inr ⟨hd, hdet⟩
        · exact Or.inl hnd
    · rintro (hnd | ⟨_, hdet⟩)
      · exact Or.inl hnd
      · exact Or.inr hdet
  rw [hsplit, Set.image_union]
  refine measure_union_null hf.image_singular_set_null ?_
  -- The non-positive-Jacobian piece has null image: `f` is differentiable there,
  -- and the set itself is null since the Jacobian is positive almost everywhere.
  -- The set of non-positive Jacobian is null (`hf.1.2` gives a.e. positivity).
  have hdetnull : volume {z : ℂ | ¬ 0 < (fderiv ℝ f z).det} = 0 := by
    rw [← ae_iff]; exact hf.1.2
  have hsubnull : volume {z : ℂ | DifferentiableAt ℝ f z ∧ ¬ 0 < (fderiv ℝ f z).det} = 0 :=
    measure_mono_null (fun z hz => hz.2) hdetnull
  -- `f` is differentiable on the piece, so its null set maps to a null set.
  have hdiffOn : DifferentiableOn ℝ f {z : ℂ | DifferentiableAt ℝ f z ∧ ¬ 0 < (fderiv ℝ f z).det} :=
    fun z hz => hz.1.differentiableWithinAt
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hdiffOn hsubnull

/-- **Almost-everywhere differentiability of the inverse.** For an `IsQCAnalytic`
map `f` with inverse homeomorphism `g = f⁻¹`, the inverse `g` is real-differentiable
at almost every point of the plane.

*Proof sketch.* By the easy half of the inverse function theorem
(`HasFDerivAt.of_local_left_inverse`): at every point `w` whose preimage `g w` lies
outside the degeneracy set, `f` is differentiable at `g w` with invertible
differential (`ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`, using
positivity of the Jacobian), and `g` is the continuous global inverse, so `g` is
differentiable at `w`. The complement of this good set of `w` is exactly
`f '' {degeneracy set}`, which is null by `image_lusinN`. *Dependency:*
`image_lusinN`. -/
theorem IsQCAnalytic.inverse_differentiableAt_ae {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∀ᵐ w, DifferentiableAt ℝ (⇑(hf.1.1.homeomorph f).symm) w := by
  -- The inverse homeomorphism `g = f⁻¹`.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  -- The forward map of the homeomorphism is `f`.
  have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.1.1 z
  -- The two inverse relations: `f (g w) = w` and `g (f z) = z`.
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
    exact (hf.1.1.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg, ← hfwd z]
    exact (hf.1.1.homeomorph f).symm_apply_apply z
  -- `g` is continuous.
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_symm
  -- The degeneracy set in the domain.
  set D : Set ℂ := {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det} with hD
  -- The complement of the good set of `w` is `{w | g w ∈ D}`, which equals `f '' D`.
  have hcompl : {w : ℂ | g w ∈ D} = f '' D := by
    ext w
    constructor
    · intro hw
      exact ⟨g w, hw, hfg w⟩
    · rintro ⟨z, hzD, rfl⟩
      simp only [Set.mem_ofPred_eq, hgf z]
      exact hzD
  -- Hence the complement is null (by `image_lusinN` / Target 1).
  have hnull : volume {w : ℂ | g w ∈ D} = 0 := by rw [hcompl]; exact hf.image_lusinN
  -- So almost every `w` has `g w ∉ D`, i.e. `f` is differentiable at `g w` with
  -- positive Jacobian.
  have hgood : ∀ᵐ w, g w ∉ D := by
    rw [ae_iff]
    convert hnull using 2
    ext w
    simp only [Set.mem_ofPred_eq, not_not]
  -- At each good `w`, apply the easy inverse function theorem.
  filter_upwards [hgood] with w hw
  -- `g w ∉ D` unpacks to differentiability and positive Jacobian.
  rw [hD] at hw
  simp only [Set.mem_ofPred_eq, not_or, not_not] at hw
  obtain ⟨hdiff, hdetpos⟩ := hw
  -- The differential of `f` at `g w` and its determinant nonvanishing.
  set f' : ℂ →L[ℝ] ℂ := fderiv ℝ f (g w) with hf'
  have hdetne : f'.det ≠ 0 := ne_of_gt hdetpos
  -- The continuous linear equivalence built from the nonvanishing determinant.
  set e : ℂ ≃L[ℝ] ℂ := f'.toContinuousLinearEquivOfDetNeZero hdetne with he
  have hecoe : (e : ℂ →L[ℝ] ℂ) = f' :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero f' hdetne
  -- `f` has `f'` as its Fréchet derivative at `g w`.
  have hfderiv : HasFDerivAt f (e : ℂ →L[ℝ] ℂ) (g w) := by
    rw [hecoe]; exact hdiff.hasFDerivAt
  -- The local left-inverse identity near `w`.
  have hloc : ∀ᶠ y in nhds w, f (g y) = y := Filter.Eventually.of_forall hfg
  -- The easy half of the inverse function theorem.
  have hgfderiv : HasFDerivAt g (e.symm : ℂ →L[ℝ] ℂ) w :=
    HasFDerivAt.of_local_left_inverse hgcont.continuousAt hfderiv hloc
  exact hgfderiv.differentiableAt

/-- **The inverse solves a Beltrami equation.** The inverse homeomorphism
`g = f⁻¹` of an `IsQCAnalytic` map satisfies, almost everywhere, a Beltrami
equation `∂̄g = b'.μ ∂g` for an explicit Beltrami coefficient `b'` (so
`b'.normInf < 1`). The coefficient `b'` is the "reflected" one:
`b'.μ (f z) = − (b.μ z) · (∂f z / conj (∂f z))` where it is invertible, the
algebraic image of `b` under `f`.

*Proof sketch.* Where both `f` and `g` are differentiable with invertible
differential (a.e., by `inverse_differentiableAt_ae` and `ae_differentiableAt`),
the Wirtinger chain rule for `g ∘ f = id` inverts the linear relation
`∂̄f = b.μ ∂f`, yielding `∂̄g = b'.μ ∂g` with `‖b'.μ‖ = ‖b.μ‖` pointwise — hence
`‖b'‖∞ = ‖b‖∞ < 1`, so `b'` is a genuine `BeltramiCoeff`. *Dependency:*
`inverse_differentiableAt_ae`, `dzbar_comp`/`dz_comp`. -/
theorem IsQCAnalytic.inverse_beltrami {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ b' : BeltramiCoeff, b'.normInf ≤ b.normInf ∧
      ∀ᵐ w, dzbar (⇑(hf.1.1.homeomorph f).symm) w
        = b'.μ w * dz (⇑(hf.1.1.homeomorph f).symm) w := by
  classical
  -- The inverse homeomorphism `g = f⁻¹`.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  -- The forward map of the homeomorphism is `f`; the two inverse relations.
  have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.1.1 z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
    exact (hf.1.1.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg, ← hfwd z]
    exact (hf.1.1.homeomorph f).symm_apply_apply z
  -- **`f` maps null sets to null sets** (planar Lusin-(N) for arbitrary null sets,
  -- from the super-critical weak gradient of `f`).
  obtain ⟨p, gx, gy, hp2, hgrad, hgxp, hgyp⟩ := hf.exists_weakGradient_memLpLocOn_gt_two
  have hfNull : ∀ S : Set ℂ, volume S = 0 → volume (f '' S) = 0 := fun S hS =>
    lusinN_image_null_of_weakGradient hp2 hf.1.1.continuous hgrad hgxp hgyp hS
  -- **Pullback of a.e. properties through `g`.** If `P` holds a.e. (in `z`), then
  -- `P (g w)` holds for a.e. `w`: the bad set `{w | ¬ P (g w)}` equals `f '' {z | ¬ P z}`,
  -- which is null because `f` maps the (null) bad source-set to a null set.
  have pullback : ∀ P : ℂ → Prop, (∀ᵐ z, P z) → ∀ᵐ w, P (g w) := by
    intro P hP
    have hbadnull : volume {z : ℂ | ¬ P z} = 0 := ae_iff.mp hP
    have himgnull : volume (f '' {z : ℂ | ¬ P z}) = 0 := hfNull _ hbadnull
    rw [ae_iff]
    refine measure_mono_null ?_ himgnull
    intro w hw
    -- `¬ P (g w)` means `g w ∈ {z | ¬ P z}`, and `f (g w) = w`, so `w ∈ f '' {z | ¬ P z}`.
    exact ⟨g w, hw, hfg w⟩
  -- A.e. data for `w`: `g` differentiable, `f` differentiable at `g w` with positive
  -- Jacobian, the Beltrami equation at `g w`, and the dilatation bound at `g w`.
  have hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w := hf.inverse_differentiableAt_ae
  have hfdiff : ∀ᵐ w, DifferentiableAt ℝ f (g w) :=
    pullback _ (IsQCAnalytic.ae_differentiableAt hf)
  have hdetpos : ∀ᵐ w, 0 < (fderiv ℝ f (g w)).det := pullback _ hf.1.2
  have hbelw : ∀ᵐ w, dzbar f (g w) = b.μ (g w) * dz f (g w) := pullback _ hf.2.2
  -- The dilatation bound `‖b.μ‖ ≤ b.normInf` pulled back to `w` (a.e.).
  have hμbnd : ∀ᵐ z, ‖b.μ z‖ ≤ b.normInf := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    -- `‖b.μ z‖₊ ≤ eLpNormEssSup b.μ`, and `eLpNormEssSup b.μ = b.normInf` (it is `< 1 < ⊤`).
    have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := ne_top_of_lt b.bound
    have : ENNReal.ofReal ‖b.μ z‖ ≤ eLpNormEssSup b.μ volume := by
      rw [ofReal_norm]; exact hz
    have h2 : ‖b.μ z‖ ≤ (eLpNormEssSup b.μ volume).toReal := by
      rw [← ENNReal.toReal_ofReal (norm_nonneg _)]
      exact ENNReal.toReal_mono hfin this
    simpa [BeltramiCoeff.normInf] using h2
  have hμbndw : ∀ᵐ w, ‖b.μ (g w)‖ ≤ b.normInf := pullback _ hμbnd
  -- **The reflected Beltrami coefficient.** Clamp the raw quotient `∂̄g / ∂g` to keep its
  -- modulus at most `c = b.normInf < 1` *everywhere*, so the essential-sup bound is free.
  set c : ℝ := b.normInf with hc
  have hc0 : 0 ≤ c := b.normInf_nonneg
  have hc1 : c < 1 := b.normInf_lt_one
  set raw : ℂ → ℂ := fun w => dzbar g w / dz g w with hraw
  set μ' : ℂ → ℂ := fun w => if ‖raw w‖ ≤ c then raw w else 0 with hμ'
  -- Measurability of `μ'` (built from `fderiv ℝ g`, hence measurable).
  have hdzg_meas : Measurable (fun w : ℂ => dz g w) := by
    have h1 : Measurable (fun w : ℂ => (fderiv ℝ g w) 1) := measurable_fderiv_apply_const ℝ g 1
    have h2 : Measurable (fun w : ℂ => (fderiv ℝ g w) Complex.I) :=
      measurable_fderiv_apply_const ℝ g Complex.I
    simpa only [dz] using! (measurable_const.mul (h1.sub (measurable_const.mul h2)))
  have hdzbarg_meas : Measurable (fun w : ℂ => dzbar g w) := by
    have h1 : Measurable (fun w : ℂ => (fderiv ℝ g w) 1) := measurable_fderiv_apply_const ℝ g 1
    have h2 : Measurable (fun w : ℂ => (fderiv ℝ g w) Complex.I) :=
      measurable_fderiv_apply_const ℝ g Complex.I
    simpa only [dzbar] using! (measurable_const.mul (h1.add (measurable_const.mul h2)))
  have hraw_meas : Measurable raw := hdzbarg_meas.div hdzg_meas
  have hμ'_meas : Measurable μ' :=
    Measurable.ite (measurableSet_le hraw_meas.norm measurable_const) hraw_meas measurable_const
  -- `‖μ' w‖ ≤ c` everywhere, so `eLpNormEssSup μ' < 1`.
  have hμ'_le : ∀ w, ‖μ' w‖ ≤ c := by
    intro w
    rw [hμ']
    by_cases h : ‖raw w‖ ≤ c
    · simp [h]
    · simp [h, hc0]
  have hμ'_bound : eLpNormEssSup μ' volume < 1 := by
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hμ'_le)) ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mpr hc1
  -- The essential-sup bound `‖μ'‖∞ ≤ c = b.normInf`, exported from the everywhere clamp.
  have hμ'_essle : eLpNormEssSup μ' volume ≤ ENNReal.ofReal c :=
    eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hμ'_le)
  have hnormInf_le : (⟨μ', hμ'_meas, hμ'_bound⟩ : BeltramiCoeff).normInf ≤ b.normInf := by
    rw [BeltramiCoeff.normInf, ← hc, ← ENNReal.toReal_ofReal hc0]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ'_essle
  refine ⟨⟨μ', hμ'_meas, hμ'_bound⟩, hnormInf_le, ?_⟩
  -- **The Beltrami equation for `g`** at a.e. `w`.
  filter_upwards [hgdiff, hfdiff, hdetpos, hbelw, hμbndw]
    with w hwg hwf hwdet hwbel hwbnd
  -- Set `z := g w`; the chain rule for `g ∘ f = id` at `z`.
  set z : ℂ := g w with hz
  -- `f z = w` and the identity `(fun y => g (f y)) = (fun y => y)`.
  have hfz : f z = w := hfg w
  have hcompid : (fun y => g (f y)) = (fun y : ℂ => y) := funext hgf
  -- `g` is differentiable at `f z = w`.
  have hwg' : DifferentiableAt ℝ g (f z) := by rw [hfz]; exact hwg
  -- Wirtinger derivatives of the identity.
  have hdzid : dz (fun y : ℂ => y) z = 1 := by simp only [dz, fderiv_fun_id]; simp; ring
  have hdzbarid : dzbar (fun y : ℂ => y) z = 0 := by simp only [dzbar, fderiv_fun_id]; simp
  -- Abbreviations for the four Wirtinger values.
  set P : ℂ := dz g w with hP
  set Q : ℂ := dzbar g w with hQ
  set pp : ℂ := dz f z with hpp
  set qq : ℂ := dzbar f z with hqq
  -- The two chain-rule equations, with `f z = w` and `g ∘ f = id` substituted.
  have heq1 : P * pp + Q * conj qq = 1 := by
    have hcr : dz (fun y => g (f y)) z = dz g (f z) * dz f z + dzbar g (f z) * conj (dzbar f z) :=
      dz_comp hwf hwg'
    rw [hcompid, hdzid, hfz] at hcr
    exact hcr.symm
  have heq2 : P * qq + Q * conj pp = 0 := by
    have hcr : dzbar (fun y => g (f y)) z
        = dz g (f z) * dzbar f z + dzbar g (f z) * conj (dz f z) := dzbar_comp hwf hwg'
    rw [hcompid, hdzbarid, hfz] at hcr
    exact hcr.symm
  -- `pp = dz f z ≠ 0` from the positive Jacobian: `det = ‖pp‖² − ‖qq‖² > 0`, so `‖pp‖ > 0`.
  have hppne : pp ≠ 0 := by
    have hdet : (fderiv ℝ f z).det = ‖pp‖ ^ 2 - ‖qq‖ ^ 2 := det_fderiv_eq_wirtinger f z
    rw [hdet] at hwdet
    intro h0
    rw [h0, norm_zero] at hwdet
    nlinarith [sq_nonneg ‖qq‖, hwdet]
  -- The Beltrami relation at `z`: `qq = b.μ z · pp`.
  have hbelz : qq = b.μ z * pp := hwbel
  -- **Algebraic inversion.** From `heq2` and `pp ≠ 0`: `Q = (b'.μ) · P` with
  -- `‖Q‖ = ‖b.μ z‖ · ‖P‖`, and `P ≠ 0`.
  have hQrel : Q * conj pp = -(P * (b.μ z * pp)) := by
    rw [hbelz] at heq2; linear_combination heq2
  have hnorm : ‖Q‖ * ‖pp‖ = ‖b.μ z‖ * ‖P‖ * ‖pp‖ := by
    have := congrArg norm hQrel
    simp only [norm_mul, norm_neg, norm_conj] at this
    linarith [this]
  have hppn : ‖pp‖ ≠ 0 := norm_ne_zero_iff.mpr hppne
  have hQnorm : ‖Q‖ = ‖b.μ z‖ * ‖P‖ := mul_right_cancel₀ hppn hnorm
  have hPne : P ≠ 0 := by
    intro hP0
    rw [hP0] at heq1 heq2
    simp only [zero_mul, zero_add] at heq1 heq2
    have hcp : conj pp ≠ 0 := by simpa using hppne
    have hQ0 : Q = 0 := by
      rcases mul_eq_zero.mp heq2 with h | h
      · exact h
      · exact absurd h hcp
    rw [hQ0] at heq1; simp at heq1
  -- The clamp condition holds: `‖raw w‖ = ‖Q/P‖ = ‖Q‖/‖P‖ = ‖b.μ z‖ ≤ c`.
  have hPnn : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hPne
  have hraww : ‖raw w‖ ≤ c := by
    have hrawval : raw w = Q / P := by rw [hraw, hP, hQ]
    rw [hrawval, norm_div, hQnorm, mul_div_assoc, div_self hPnn, mul_one]
    exact hwbnd
  -- Conclude `∂̄g w = μ' w · ∂g w`: the clamp returns the raw quotient, and `P ≠ 0`.
  change Q = μ' w * P
  have hμ'w : μ' w = Q / P := by
    rw [hμ']; simp only [hraww, if_true]; rw [hraw, hP, hQ]
  rw [hμ'w, div_mul_cancel₀ Q hPne]

/-- **The inverse is an orientation-preserving homeomorphism.** The inverse
`g = f⁻¹` of an `IsQCAnalytic` map is a homeomorphism with a.e. positive Jacobian.

*Proof sketch.* `g = (hf.1.1.homeomorph f).symm` is a homeomorphism by construction.
For the Jacobian: where `g` is differentiable with `f` differentiable at `g w`
(a.e.), `Dg w = (Df (g w))⁻¹`, so `det (Dg w) = 1 / det (Df (g w)) > 0` from the
a.e. positivity field `hf.1.2` pulled back through the measure-preserving-up-to-
Jacobian change of variables. *Dependency:* `inverse_differentiableAt_ae`,
`IsQCAnalytic.ae_differentiableAt`. -/
theorem IsQCAnalytic.inverse_orientationPreservingHomeo {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    OrientationPreservingHomeo (⇑(hf.1.1.homeomorph f).symm) := by
  -- `OrientationPreservingHomeo g` is the conjunction of `IsHomeomorph g` and a.e.
  -- positivity of the Jacobian `det (Dg)`.
  refine ⟨?_, ?_⟩
  · -- `g = ⇑(hf.1.1.homeomorph f).symm` is the coercion of a `Homeomorph`, hence an
    -- `IsHomeomorph` (`Homeomorph.isHomeomorph`).
    exact (hf.1.1.homeomorph f).symm.isHomeomorph
  · -- A.e. positivity of `det (Dg)`. We reuse the exact good-set / inverse-function
    -- construction from `inverse_differentiableAt_ae`.
    -- The inverse homeomorphism `g = f⁻¹`.
    set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
    -- The forward map of the homeomorphism is `f`.
    have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
      IsHomeomorph.homeomorph_apply f hf.1.1 z
    -- The two inverse relations: `f (g w) = w` and `g (f z) = z`.
    have hfg : ∀ w, f (g w) = w := fun w => by
      rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
      exact (hf.1.1.homeomorph f).apply_symm_apply w
    have hgf : ∀ z, g (f z) = z := fun z => by
      rw [hg, ← hfwd z]
      exact (hf.1.1.homeomorph f).symm_apply_apply z
    -- `g` is continuous.
    have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_symm
    -- The degeneracy set in the domain.
    set D : Set ℂ := {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det} with hD
    -- The complement of the good set of `w` is `{w | g w ∈ D}`, which equals `f '' D`.
    have hcompl : {w : ℂ | g w ∈ D} = f '' D := by
      ext w
      constructor
      · intro hw
        exact ⟨g w, hw, hfg w⟩
      · rintro ⟨z, hzD, rfl⟩
        simp only [Set.mem_ofPred_eq, hgf z]
        exact hzD
    -- Hence the complement is null (by `image_lusinN`).
    have hnull : volume {w : ℂ | g w ∈ D} = 0 := by rw [hcompl]; exact hf.image_lusinN
    -- So almost every `w` has `g w ∉ D`, i.e. `f` is differentiable at `g w` with
    -- positive Jacobian.
    have hgood : ∀ᵐ w, g w ∉ D := by
      rw [ae_iff]
      convert hnull using 2
      ext w
      simp only [Set.mem_ofPred_eq, not_not]
    -- At each good `w`, the easy inverse function theorem gives `Dg w = (Df (g w))⁻¹`,
    -- whose determinant is the reciprocal of the (positive) Jacobian of `f`.
    filter_upwards [hgood] with w hw
    -- `g w ∉ D` unpacks to differentiability and positive Jacobian.
    rw [hD] at hw
    simp only [Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨hdiff, hdetpos⟩ := hw
    -- The differential of `f` at `g w` and its determinant nonvanishing.
    set f' : ℂ →L[ℝ] ℂ := fderiv ℝ f (g w) with hf'
    have hdetne : f'.det ≠ 0 := ne_of_gt hdetpos
    -- The continuous linear equivalence built from the nonvanishing determinant.
    set e : ℂ ≃L[ℝ] ℂ := f'.toContinuousLinearEquivOfDetNeZero hdetne with he
    have hecoe : (e : ℂ →L[ℝ] ℂ) = f' :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero f' hdetne
    -- `f` has `f'` as its Fréchet derivative at `g w`.
    have hfderiv : HasFDerivAt f (e : ℂ →L[ℝ] ℂ) (g w) := by
      rw [hecoe]; exact hdiff.hasFDerivAt
    -- The local left-inverse identity near `w`.
    have hloc : ∀ᶠ y in nhds w, f (g y) = y := Filter.Eventually.of_forall hfg
    -- The easy half of the inverse function theorem: `Dg w = e.symm`.
    have hgfderiv : HasFDerivAt g (e.symm : ℂ →L[ℝ] ℂ) w :=
      HasFDerivAt.of_local_left_inverse hgcont.continuousAt hfderiv hloc
    -- Identify `fderiv ℝ g w` with `e.symm`, and compute its determinant.
    have hfderivg : fderiv ℝ g w = (e.symm : ℂ →L[ℝ] ℂ) := hgfderiv.fderiv
    rw [hfderivg]
    -- `det (e.symm) = (det e)⁻¹ = (det f')⁻¹`, and `det f' = det (Df (g w)) > 0`.
    rw [ContinuousLinearEquiv.det_coe_symm, hecoe]
    exact inv_pos.mpr hdetpos

/-- **Local `L²` energy bound for the inverse partials** (the inverse-side `L²_loc`
membership of `w ↦ (Dg w) v`). For an `IsQCAnalytic` map `f` with inverse `g = f⁻¹`, the
pointwise partial `w ↦ (fderiv ℝ g w) v` is locally square-integrable, for any direction
`v`. This packages the inverse-side dilatation bound `‖Dg w‖² ≤ K · det (Dg w)` (assembled
from `f`'s a.e. positive Jacobian, the Beltrami bound, and the easy inverse-function
theorem, exactly as in `inverse_memW12loc`) with the change-of-variables energy estimate
`memLpLocOn_inverse_partial_of_dilatation`. *Dependency:*
`inverse_orientationPreservingHomeo`, `inverse_differentiableAt_ae`,
`exists_weakGradient_memLpLocOn_gt_two`, `inverse_fderiv_normSq_le_K_mul_det`,
`memLpLocOn_inverse_partial_of_dilatation`. -/
theorem IsQCAnalytic.inverse_partial_memLpLocOn {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (v : ℂ) :
    MemLpLocOn (fun w => (fderiv ℝ (⇑(hf.1.1.homeomorph f).symm) w) v) (2 : ℝ≥0∞) Set.univ := by
  classical
  -- The inverse homeomorphism `g = f⁻¹` and the standard inverse data.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.1.1 z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
    exact (hf.1.1.homeomorph f).apply_symm_apply w
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_symm
  obtain ⟨hghomeo, hdetpos⟩ := IsQCAnalytic.inverse_orientationPreservingHomeo hf
  have hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w := IsQCAnalytic.inverse_differentiableAt_ae hf
  -- The constant `K = (1 + c)/(1 - c)` with `c = b.normInf ∈ [0, 1)`.
  set c : ℝ := b.normInf with hc
  have hc0 : 0 ≤ c := b.normInf_nonneg
  have hc1 : c < 1 := b.normInf_lt_one
  set K : ℝ := (1 + c) / (1 - c) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; apply div_pos <;> linarith
  -- A.e. dilatation bound on `b.μ`.
  have hμbnd : ∀ᵐ z, ‖b.μ z‖ ≤ c := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := ne_top_of_lt b.bound
    have : ENNReal.ofReal ‖b.μ z‖ ≤ eLpNormEssSup b.μ volume := by
      rw [ofReal_norm]; exact hz
    have h2 : ‖b.μ z‖ ≤ (eLpNormEssSup b.μ volume).toReal := by
      rw [← ENNReal.toReal_ofReal (norm_nonneg _)]
      exact ENNReal.toReal_mono hfin this
    simpa [hc, BeltramiCoeff.normInf] using h2
  -- Pull a.e. source-side properties back through `g` (via `f`-Lusin-N).
  obtain ⟨p, gxf, gyf, hp2, hgradf, hgxfp, hgyfp⟩ :=
    IsQCAnalytic.exists_weakGradient_memLpLocOn_gt_two hf
  have hfNull : ∀ S : Set ℂ, volume S = 0 → volume (f '' S) = 0 := fun S hS =>
    lusinN_image_null_of_weakGradient hp2 hf.1.1.continuous hgradf hgxfp hgyfp hS
  have pullback : ∀ P : ℂ → Prop, (∀ᵐ z, P z) → ∀ᵐ w, P (g w) := by
    intro P hP
    have hbadnull : volume {z : ℂ | ¬ P z} = 0 := ae_iff.mp hP
    have himgnull : volume (f '' {z : ℂ | ¬ P z}) = 0 := hfNull _ hbadnull
    rw [ae_iff]
    refine measure_mono_null ?_ himgnull
    intro w hw
    exact ⟨g w, hw, hfg w⟩
  have hfdiffw : ∀ᵐ w, DifferentiableAt ℝ f (g w) :=
    pullback _ (IsQCAnalytic.ae_differentiableAt hf)
  have hfdetposw : ∀ᵐ w, 0 < (fderiv ℝ f (g w)).det := pullback _ hf.1.2
  have hbelw : ∀ᵐ w, dzbar f (g w) = b.μ (g w) * dz f (g w) := pullback _ hf.2.2
  have hμbndw : ∀ᵐ w, ‖b.μ (g w)‖ ≤ c := pullback _ hμbnd
  have hbelbnd : ∀ᵐ w, ‖dzbar f (g w)‖ ≤ c * ‖dz f (g w)‖ := by
    filter_upwards [hbelw, hμbndw] with w hbel hμ
    rw [hbel, norm_mul]
    exact mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
  have hgderivw : ∀ᵐ w, fderiv ℝ g w
      = ContinuousLinearMap.inverse (fderiv ℝ f (g w)) := by
    filter_upwards [hgdiff, hfdiffw, hfdetposw] with w hwg hwf hwdet
    set f' : ℂ →L[ℝ] ℂ := fderiv ℝ f (g w) with hf'
    have hdetne : f'.det ≠ 0 := ne_of_gt hwdet
    set e : ℂ ≃L[ℝ] ℂ := f'.toContinuousLinearEquivOfDetNeZero hdetne with he
    have hecoe : (e : ℂ →L[ℝ] ℂ) = f' :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero f' hdetne
    have hfderiv : HasFDerivAt f (e : ℂ →L[ℝ] ℂ) (g w) := by
      rw [hecoe]; exact hwf.hasFDerivAt
    have hloc : ∀ᶠ y in nhds w, f (g y) = y := Filter.Eventually.of_forall hfg
    have hgfderiv : HasFDerivAt g (e.symm : ℂ →L[ℝ] ℂ) w :=
      HasFDerivAt.of_local_left_inverse hgcont.continuousAt hfderiv hloc
    rw [hgfderiv.fderiv, ← hecoe, ContinuousLinearMap.inverse_equiv e]
  have hdil : ∀ᵐ w, ‖fderiv ℝ g w‖ ^ 2 ≤ K * (fderiv ℝ g w).det := by
    filter_upwards [hfdetposw, hbelbnd, hgderivw] with w hwdet hwbel hwgderiv
    exact inverse_fderiv_normSq_le_K_mul_det hc0 hc1 hwdet hwbel hwgderiv
  -- The change-of-variables `L²_loc` energy bound for the partial.
  exact memLpLocOn_inverse_partial_of_dilatation hKpos hghomeo hgdiff hdetpos hdil v

/-! ## The fibered Lusin-(N) maps of the inverse (Steps 1–2 of the reverse length–area route)

To control the slices of `g = f⁻¹` we use the four "y-fibered" auxiliary maps
`Φ := ⟨(g ·).re, (·).im⟩`, `Ψ := ⟨(g ·).im, (·).im⟩`, and their vertical analogues
`Φ' := ⟨(g ·).re, (·).re⟩`, `Ψ' := ⟨(g ·).im, (·).re⟩`. Each factors as `H ∘ g` with `H` a
map whose components are `w.re`/`w.im` (smooth) and `(f w).re`/`(f w).im` (a `W^{1,p>2}` part of
`f`). By Morrey's theorem (`lusinN_image_null_of_weakGradient`) each such `H` is Lusin-(N), and `g`
is Lusin-(N) (`inverse_conditionNPlus`); hence each fibered map is Lusin-(N). This is the genuine
consumer of `f`'s super-critical weak gradient `exists_weakGradient_memLpLocOn_gt_two` — the
area-preserving singular shear has no `Lᵖ`, `p > 2`, weak gradient, so this route excludes it. -/

/-- **Continuous-linear post-composition preserves a weak directional derivative.** If `g` is the
weak `v`-directional derivative of `f` on `Ω`, and both `f`, `g` are locally integrable on `Ω`,
then `L ∘ g` is the weak `v`-directional derivative of `L ∘ f` for any continuous linear
`L : ℂ →L[ℝ] ℂ`. (The integration-by-parts identity is post-composed with `L`, commuting through
the Bochner integral by `ContinuousLinearMap.integral_comp_comm`.) -/
private theorem hasWeakDirDeriv_clm_comp {v : ℂ} {g f : ℂ → ℂ} {Ω : Set ℂ}
    (L : ℂ →L[ℝ] ℂ) (h : HasWeakDirDeriv v g f Ω)
    (hfloc : LocallyIntegrableOn f Ω) (hgloc : LocallyIntegrableOn g Ω) :
    HasWeakDirDeriv v (fun z => L (g z)) (fun z => L (f z)) Ω := by
  intro φ hφ hcs htsupp
  -- The test-function pieces are continuous and compactly supported in `Ω`.
  have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) v) :=
    HasCompactSupport.fderiv_apply ℝ hcs v
  have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans htsupp
  -- A generic integrability helper: (continuous, compactly supported in `Ω`) • (loc. integrable).
  have integ : ∀ (m : ℂ → ℝ), Continuous m → HasCompactSupport m → tsupport m ⊆ Ω →
      ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h Ω → Integrable (fun z => m z • h z) volume := by
    intro m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume := hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz; apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  -- Integrability of the two integrands (before post-composition by `L`).
  have hL_int : Integrable (fun z => ((fderiv ℝ φ z) v) • f z) volume :=
    integ _ hcont_dφ hcs_dφ hts_dφ hfloc
  have hR_int : Integrable (fun z => φ z • g z) volume :=
    integ _ hφ.continuous hcs htsupp hgloc
  -- Post-compose the IBP identity with `L`, commuting `L` through both integrals.
  change ∫ z, ((fderiv ℝ φ z) v) • L (f z) = - ∫ z, φ z • L (g z)
  have hLleft : (∫ z, ((fderiv ℝ φ z) v) • L (f z)) = L (∫ z, ((fderiv ℝ φ z) v) • f z) := by
    rw [← ContinuousLinearMap.integral_comp_comm L hL_int]
    apply integral_congr_ae; filter_upwards with z; exact (L.map_smul _ _).symm
  have hLright : (∫ z, φ z • L (g z)) = L (∫ z, φ z • g z) := by
    rw [← ContinuousLinearMap.integral_comp_comm L hR_int]
    apply integral_congr_ae; filter_upwards with z; exact (L.map_smul _ _).symm
  rw [hLleft, hLright, h φ hφ hcs htsupp, L.map_neg]

/-- **Local integrability on `univ` of a `MemLpLocOn p`, `p ≥ 1`, function.** -/
theorem locallyIntegrableOn_of_memLpLocOn {h : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hmem : MemLpLocOn h (ENNReal.ofReal p) Set.univ) : LocallyIntegrableOn h Set.univ := by
  rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
  intro k hk
  have : IsFiniteMeasure (volume.restrict k) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
  have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]; exact ENNReal.ofReal_le_ofReal hp
  exact memLp_one_iff_integrable.mp ((hmem k (Set.subset_univ _) hk).mono_exponent h1le)

/-- **Lusin-(N) of a fibered map of the inverse.** For continuous-linear "selectors"
`P Q : ℂ →L[ℝ] ℝ`, the map `Fib p := (P (g p)) • 1 + (Q p) • I` (`g = f⁻¹`) carries null sets
to null sets. It factors as `H ∘ g` with `H w := (P w) • 1 + (Q (f w)) • I`; `H` is Lusin-(N)
by Morrey (its weak gradient is `L^{p>2}_loc` — the `P w` part is a continuous linear map of `w`,
hence smooth, and the `Q (f w)` part is the `Q`-postcomposition of `f`'s super-critical weak
gradient), and `g` is Lusin-(N) (`inverse_conditionNPlus`). Specialising `(P, Q)` to the four
projection pairs gives the fibered maps `Φ`, `Ψ`, `Φ'`, `Ψ'` of the reverse length–area route.
The genuine consumer of `f`'s super-critical weak gradient: the area-preserving singular shear has
no `Lᵖ`, `p > 2`, weak gradient, so this route correctly excludes it. -/
theorem IsQCAnalytic.inverse_fiber_lusinN {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (P Q : ℂ →L[ℝ] ℝ) :
    ∀ S : Set ℂ, volume S = 0 →
      volume ((fun p : ℂ => (P ((hf.1.1.homeomorph f).symm p) : ℝ) • (1 : ℂ)
        + (Q p : ℝ) • Complex.I) '' S) = 0 := by
  classical
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.1.1 z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
    exact (hf.1.1.homeomorph f).apply_symm_apply w
  -- `f`'s super-critical weak gradient `(gxf, gyf) ∈ L^{p>2}_loc`.
  obtain ⟨p, gxf, gyf, hp2, ⟨hgxw, hgyw⟩, hgxfp, hgyfp⟩ :=
    IsQCAnalytic.exists_weakGradient_memLpLocOn_gt_two hf
  have hp1 : (1 : ℝ) ≤ p := le_of_lt (lt_trans one_lt_two hp2)
  have hfcont : Continuous f := hf.1.1.continuous
  have hfloc : LocallyIntegrableOn f Set.univ := by
    rw [locallyIntegrableOn_univ]; exact hfcont.locallyIntegrable
  have hgxfloc : LocallyIntegrableOn gxf Set.univ := locallyIntegrableOn_of_memLpLocOn hp1 hgxfp
  have hgyfloc : LocallyIntegrableOn gyf Set.univ := locallyIntegrableOn_of_memLpLocOn hp1 hgyfp
  -- The map `H w := (P w) • 1 + (Q (f w)) • I = A w + B w`, with `A` a CLM of `w` and `B = LP ∘ f`.
  --   `A w := (P w) • 1` (continuous linear in `w`), `B w := (Q (f w)) • I`.
  set A : ℂ → ℂ := fun w => (P w : ℝ) • (1 : ℂ) with hA
  set B : ℂ → ℂ := fun w => (Q (f w) : ℝ) • Complex.I with hB
  set H : ℂ → ℂ := fun w => (P w : ℝ) • (1 : ℂ) + (Q (f w) : ℝ) • Complex.I with hH
  have hHsum : H = fun w => A w + B w := rfl
  -- Continuous-linear maps realizing the two components.
  -- `A = LP1`, with `LP1 w := (P w) • 1`; `B = LQI ∘ f`, with `LQI z := (Q z) • I`.
  set LP1 : ℂ →L[ℝ] ℂ := P.smulRight (1 : ℂ) with hLP1
  set LQI : ℂ →L[ℝ] ℂ := Q.smulRight Complex.I with hLQI
  have hAeq : A = fun w => LP1 w := rfl
  have hBeq : B = fun w => LQI (f w) := rfl
  -- `fderiv ℝ A w = LP1` (the derivative of a continuous linear map is itself).
  have hAfderiv : ∀ w, fderiv ℝ A w = LP1 := by
    intro w; rw [hAeq]; exact (LP1.hasFDerivAt).fderiv
  -- Weak gradient of `A`: `A` is a CLM, so its classical partials are weak.
  have hAweakx : HasWeakDirDeriv 1 (fun w => (fderiv ℝ A w) 1) A Set.univ := by
    rw [hAeq]; exact HasWeakDirDeriv.of_contDiffOn isOpen_univ LP1.contDiff.contDiffOn
  have hAweaky : HasWeakDirDeriv Complex.I (fun w => (fderiv ℝ A w) Complex.I) A Set.univ := by
    rw [hAeq]; exact HasWeakDirDeriv.of_contDiffOn isOpen_univ LP1.contDiff.contDiffOn
  -- Weak gradient of `B = LQI ∘ f`: post-compose `f`'s weak gradient by the CLM `LQI`.
  have hBweakx : HasWeakDirDeriv 1 (fun w => LQI (gxf w)) B Set.univ := by
    rw [hBeq]; exact hasWeakDirDeriv_clm_comp LQI hgxw hfloc hgxfloc
  have hBweaky : HasWeakDirDeriv Complex.I (fun w => LQI (gyf w)) B Set.univ := by
    rw [hBeq]; exact hasWeakDirDeriv_clm_comp LQI hgyw hfloc hgyfloc
  -- Local integrability of the partial pieces (for `HasWeakDirDeriv.add`).
  have hAxloc : LocallyIntegrableOn (fun w => (fderiv ℝ A w) 1) Set.univ := by
    simp only [hAfderiv]; rw [locallyIntegrableOn_univ]; exact (continuous_const).locallyIntegrable
  have hAyloc : LocallyIntegrableOn (fun w => (fderiv ℝ A w) Complex.I) Set.univ := by
    simp only [hAfderiv]; rw [locallyIntegrableOn_univ]; exact (continuous_const).locallyIntegrable
  have hAloc : LocallyIntegrableOn A Set.univ := by
    rw [hAeq, locallyIntegrableOn_univ]; exact LP1.continuous.locallyIntegrable
  have hBloc : LocallyIntegrableOn B Set.univ := by
    rw [hBeq]; exact LQI.locallyIntegrableOn_comp hfloc
  have hBxloc : LocallyIntegrableOn (fun w => LQI (gxf w)) Set.univ :=
    LQI.locallyIntegrableOn_comp hgxfloc
  have hByloc : LocallyIntegrableOn (fun w => LQI (gyf w)) Set.univ :=
    LQI.locallyIntegrableOn_comp hgyfloc
  -- Assemble the weak gradient of `H = A + B`.
  have hHweakx : HasWeakDirDeriv 1 (fun w => (fderiv ℝ A w) 1 + LQI (gxf w)) H Set.univ := by
    rw [hHsum]; exact hAweakx.add hBweakx hAloc hBloc hAxloc hBxloc
  have hHweaky : HasWeakDirDeriv Complex.I
      (fun w => (fderiv ℝ A w) Complex.I + LQI (gyf w)) H Set.univ := by
    rw [hHsum]; exact hAweaky.add hBweaky hAloc hBloc hAyloc hByloc
  -- The two weak partials lie in `L^{p>2}_loc`: the `A`-part is a constant, the `LQI∘g·` part is
  -- `MemLp` because the continuous linear map `LQI` preserves `MemLp`.
  have memLp_clm_part : ∀ (cpart : ℂ) (gpart : ℂ → ℂ),
      MemLpLocOn gpart (ENNReal.ofReal p) Set.univ →
      MemLpLocOn (fun w => cpart + LQI (gpart w)) (ENNReal.ofReal p) Set.univ := by
    intro cpart gpart hgmem K hKuniv hKcomp
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKcomp.measure_lt_top⟩
    have hcMemLp : MemLp (fun _ : ℂ => cpart) (ENNReal.ofReal p) (volume.restrict K) :=
      (memLp_top_const cpart).mono_exponent le_top
    have hgpartMemLp : MemLp gpart (ENNReal.ofReal p) (volume.restrict K) :=
      hgmem K hKuniv hKcomp
    -- `LQI ∘ gpart` is `MemLp`: a continuous linear map preserves `MemLp`.
    have hLQIgMemLp : MemLp (fun w => LQI (gpart w)) (ENNReal.ofReal p) (volume.restrict K) :=
      LQI.comp_memLp' hgpartMemLp
    exact hcMemLp.add hLQIgMemLp
  have hHxMemLp : MemLpLocOn (fun w => (fderiv ℝ A w) 1 + LQI (gxf w))
      (ENNReal.ofReal p) Set.univ := by
    simp only [hAfderiv]; exact memLp_clm_part (LP1 1) _ hgxfp
  have hHyMemLp : MemLpLocOn (fun w => (fderiv ℝ A w) Complex.I + LQI (gyf w))
      (ENNReal.ofReal p) Set.univ := by
    simp only [hAfderiv]; exact memLp_clm_part (LP1 Complex.I) _ hgyfp
  -- Morrey: `H` is Lusin-(N).
  have hHcont : Continuous H := by
    rw [hH]
    exact ((Complex.continuous_ofReal.comp (P.continuous)).smul continuous_const).add
      ((Complex.continuous_ofReal.comp (Q.continuous.comp hfcont)).smul continuous_const)
  have hHNull : ∀ S : Set ℂ, volume S = 0 → volume (H '' S) = 0 := fun S hS =>
    lusinN_image_null_of_weakGradient hp2 hHcont ⟨hHweakx, hHweaky⟩ hHxMemLp hHyMemLp hS
  -- `g` is Lusin-(N) (`inverse_conditionNPlus`); compose.
  have hgNull : ∀ S : Set ℂ, volume S = 0 → volume (g '' S) = 0 :=
    IsQCAnalytic.inverse_conditionNPlus hf
  -- `Fib '' S = H '' (g '' S)`.
  intro S hS
  have himg : (fun p : ℂ => (P (g p) : ℝ) • (1 : ℂ) + (Q p : ℝ) • Complex.I) '' S
      = H '' (g '' S) := by
    ext z; constructor
    · rintro ⟨s, hsS, rfl⟩
      exact ⟨g s, ⟨s, hsS, rfl⟩, by simp [hH, hfg]⟩
    · rintro ⟨w, ⟨s, hsS, rfl⟩, rfl⟩
      exact ⟨s, hsS, by simp [hH, hfg]⟩
  rw [show (fun p : ℂ => (P ((hf.1.1.homeomorph f).symm p) : ℝ) • (1 : ℂ) + (Q p : ℝ) • Complex.I)
        = fun p : ℂ => (P (g p) : ℝ) • (1 : ℂ) + (Q p : ℝ) • Complex.I from rfl, himg]
  exact hHNull _ (hgNull S hS)

/-! ## Step 2: per-slice image nullity from the fibered Lusin-(N)

The horizontal fibered map `Φ p = ⟨F p, p.im⟩` (`F p := (g p).re`, second coordinate exactly the
imaginary part of `p`) is Lusin-(N) (Step 1). For a fixed null set `E ⊆ ℝ`, the strip
`{p : ℂ | p.re ∈ E}` is null; its image under `Φ` is null, and that image is exactly the union over
`y` of `(slice-component image of E) × {y}`. Through a measurable null hull and Tonelli, a.e.
`y`-fiber of the strip image is null — i.e. almost every slice-component image of `E` is null. -/

/-- **Strips of the form `{p | p.re ∈ E}` are null when `E ⊆ ℝ` is null.** -/
private theorem volume_re_preimage_null {E : Set ℝ} (hE : volume E = 0) :
    volume {p : ℂ | p.re ∈ E} = 0 := by
  -- Transport to `ℝ × ℝ` via the measure-preserving `Complex.measurableEquivRealProd`.
  have hmp : MeasurePreserving Complex.measurableEquivRealProd
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
    Complex.volume_preserving_equiv_real_prod
  have hpre : {p : ℂ | p.re ∈ E}
      = Complex.measurableEquivRealProd ⁻¹' {q : ℝ × ℝ | q.1 ∈ E} := by
    ext p; simp [Complex.measurableEquivRealProd_apply]
  -- The target strip in `ℝ × ℝ` is `E ×ˢ univ`, which is null.
  have hstrip : volume {q : ℝ × ℝ | q.1 ∈ E} = 0 := by
    have heq : {q : ℝ × ℝ | q.1 ∈ E} = E ×ˢ (Set.univ : Set ℝ) := by ext q; simp
    rw [heq, Measure.volume_eq_prod, Measure.prod_prod, hE, zero_mul]
  -- Pull back the null set through the measure-preserving equivalence (quasi-measure-preserving).
  rw [hpre]
  exact measure_mono_null (Set.Subset.refl _)
    (hmp.quasiMeasurePreserving.preimage_null hstrip)

/-- **A.e. second-coordinate fiber of a null planar set is null.** If `T : Set ℂ` has
`volume T = 0`, then for almost every `y : ℝ` the set `{x : ℝ | ⟨x, y⟩ ∈ T}` is null. -/
theorem ae_slice_re_null_of_null {T : Set ℂ} (hT : volume T = 0) :
    ∀ᵐ y : ℝ, volume {x : ℝ | (Complex.mk x y) ∈ T} = 0 := by
  -- Transport `T` to a null set `T'` in `ℝ × ℝ` (coordinates `(x, y)`).
  have hmp : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  set T' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' T with hT'def
  have hT'null : volume T' = 0 := hmp.quasiMeasurePreserving.preimage_null hT
  -- `T' = {q | ⟨q.1, q.2⟩ ∈ T}`; swap so the fiber index is the second coordinate.
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  set T'' : Set (ℝ × ℝ) := Prod.swap ⁻¹' T' with hT''def
  have hT''null : volume T'' = 0 := hswap.quasiMeasurePreserving.preimage_null hT'null
  -- For the product measure, `volume T'' = 0` ⟹ a.e. first-fiber (the `y`) is null.
  have hprodnull : ∀ᵐ q : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), q ∉ T'' := by
    rw [ae_iff]; simpa [Measure.volume_eq_prod] using hT''null
  have hae : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, (y, x) ∉ T'' := Measure.ae_ae_of_ae_prod hprodnull
  -- Identify `{x | (y, x) ∈ T''}` with `{x | ⟨x, y⟩ ∈ T}`, and turn a.e.-not-mem into null fiber.
  refine hae.mono (fun y hy => ?_)
  have hmem : ∀ x : ℝ, ((y, x) ∈ T'') ↔ ((Complex.mk x y) ∈ T) := by
    intro x
    simp only [hT''def, hT'def, Set.mem_preimage, Prod.swap_prod_mk,
      Complex.measurableEquivRealProd_symm_apply]
  rw [ae_iff] at hy
  have hset : {x : ℝ | (Complex.mk x y) ∈ T} = {x : ℝ | (y, x) ∈ T''} := by
    ext x; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hmem x]
  rw [hset]; simpa using hy


end NoWanderingDomains
