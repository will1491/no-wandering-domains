/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.InfinitesimalModulus
import NoWanderingDomains.QC.LengthArea.ReverseLengthAreaEnergy
import NoWanderingDomains.QC.LengthArea.Fuglede
import NoWanderingDomains.QC.InverseQC.LusinN
import NoWanderingDomains.Analysis.Sobolev.Morrey.LusinN

/-!
# Nondegeneracy assembly: the inverse Lusin condition and `J_f > 0` a.e.

This file assembles the almost-everywhere nondegeneracy of the differential of a geometric
`K`-quasiconformal homeomorphism `f : ℂ → ℂ` — the classical `J_f > 0` a.e. theorem —
from the **inverse Lusin condition (N⁻¹)**:
the inverse homeomorphism `g = f⁻¹` maps Lebesgue-null sets to Lebesgue-null sets.

Classically, (N⁻¹) for `f` is exactly condition (N) for `g`, and the classical treatments
obtain it by showing the inverse map is itself Sobolev-regular and then applying a
condition-(N) theorem to it (through the metric definition's symmetry, the quadrilateral
reciprocity `M(Q)·M(Q̃) = 1`, or the analytic machinery run at the inverse). Here the
reciprocity step is replaced by the **length–area transfer with an explicit
admissible density** (the keystone `IsQCGeometric.inverse_axisRectModulusBound` below), which
produces the axis-rectangle modulus bounds for `g` directly; the parametrized forward ACL
chain (`AxisRectModulusBound.*`, `QC/LengthArea/ReverseLengthAreaEnergy.lean`) then applies
verbatim at `g`, and the Bojarski higher integrability (`beltrami_higher_integrability`) plus
the planar Marcus–Mizel theorem (`lusinN_image_null_of_weakGradient`) close condition (N) for
`g`.

## The node DAG (Phase-1 statements; proofs are Phase 3)

All nodes about the inverse are stated over an **abstract two-sided inverse**
`g` with `hfg : ∀ w, f (g w) = w` and `hgf : ∀ z, g (f z) = z` (maximal generality; the
homeomorphism-package inverse `⇑(hf.2.1.isHomeomorph.homeomorph f).symm` satisfies both
identities definitionally, and any two-sided inverse of a bijection is that one).

* `IsQCGeometric.forwardW12Data` (N4) — the forward Sobolev package: a.e. differentiability,
  the pointwise-partial weak gradient with `L²_loc` energy, `MemW12loc f`, and the or-zero
  dilatation bound. Assembled from the proved parametrized ACL chain and
  `IsQCGeometric.dilatation_le_or_zero`.
* `IsQCGeometric.inverse_axisRectModulusBound` (N3, **keystone**) — `AxisRectModulusBound g K`:
  the image-family modulus of every axis rectangle under `g` is at most `K` times the
  rectangle modulus, by exhibiting the explicit admissible density `𝟙_{g(R̄)}·‖Df‖/(b−a)`
  whose admissibility is the Fuglede upper-gradient inequality and whose energy is bounded by
  the dilatation and the injective half of the area formula.
* `IsQCGeometric.exists_weakGradient_memLpLocOn_gt_two` (N5a) — forward Bojarski higher
  integrability: `f ∈ W^{1,p}_loc` for some `p > 2`.
* `IsQCGeometric.lusinN` (N5) — the forward Lusin condition (N) for `f` (Marcus–Mizel at `f`).
* `ContinuousLinearMap.inverse_dilatation` (N6a) — planar linear algebra: inversion preserves
  the linear dilatation bound.
* `IsQCGeometric.inverse_pointwise_data` (N6) — a.e. differentiability of `g`, the inverse
  differential formula, positivity of `J_g`, and the dilatation bound `‖Dg‖² ≤ K·J_g`.
* `IsQCGeometric.inverse_exists_acl_memLp_sliceGradient` (N8, **proved glue**) — ACL slices
  of `g` with `L²_loc` energy, by instantiating the parametrized chain at N3.
* `IsQCGeometric.inverse_weakGradient_beltrami` (N9) — `g ∈ W^{1,2}_loc` (weak gradient =
  pointwise partials) solving a weak Beltrami equation with `‖μ‖∞ < 1`.
* `IsQCGeometric.inverse_exists_weakGradient_memLpLocOn_gt_two` (N10) — Bojarski at `g`:
  `g ∈ W^{1,p}_loc` for some `p > 2`.
* `IsQCGeometric.inverse_lusinN` (N11, the target; **statement frozen**) — condition (N⁻¹),
  i.e. Marcus–Mizel at `g`.

Downstream (proved here, re-homed from `InfinitesimalModulus.lean`):
`IsQCGeometric.ae_fderiv_ne_zero` (the `J_f ≠ 0` a.e. complement via the easy half of the
area formula and (N⁻¹)), `IsQCGeometric.wirtinger_bracket_of_blowup` (the two-conjunct
Wirtinger bracket, from the or-zero form filtered against nondegeneracy), and
`IsQCGeometric.infinitesimal_dilatation` (the sharp pointwise dilatation bound).
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-! ## N6a — inversion preserves the linear dilatation bound (planar linear algebra) -/

/-- **Inversion preserves the planar linear dilatation bound.** For a real-linear self-map
`L` of `ℂ` with positive determinant and linear dilatation at most `K`
(`‖L‖² ≤ K·det L`), the inverse map `L⁻¹` (Mathlib's `ContinuousLinearMap.inverse`, which is
the genuine inverse here since `det L ≠ 0` makes `L` a continuous linear equivalence) has
positive determinant and the same dilatation bound.

*Proof sketch.* Wirtinger singular-value algebra. Write `L w = p₀·w + q₀·conj w`; then
`‖L‖ = ‖p₀‖ + ‖q₀‖` and `det L = ‖p₀‖² − ‖q₀‖²` (the identities
`opNorm_fderiv_eq_wirtinger`, `det_fderiv_eq_wirtinger`, applied to the affine realization
`fderiv ℝ (⇑L) = L`, `ContinuousLinearMap.fderiv`). The inverse has Wirtinger data
`(conj p₀, −q₀)/det L`, so with `p = ‖p₀‖`, `q = ‖q₀‖`:
`‖L⁻¹‖ = (p + q)/det L` and `det (L⁻¹) = (p² − q²)/(det L)² = (det L)⁻¹`, whence
`‖L⁻¹‖²/det (L⁻¹) = (p + q)²/(p² − q²) = ‖L‖²/det L ≤ K`. The `ContinuousLinearMap.inverse`
bookkeeping goes through `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero` and
`ContinuousLinearMap.inverse_equiv`.
-/
theorem _root_.ContinuousLinearMap.inverse_dilatation {L : ℂ →L[ℝ] ℂ} {K : ℝ}
    (hdet : 0 < L.det) (hK : ‖L‖ ^ 2 ≤ K * L.det) :
    0 < (ContinuousLinearMap.inverse L).det ∧
      ‖ContinuousLinearMap.inverse L‖ ^ 2 ≤ K * (ContinuousLinearMap.inverse L).det := by
  classical
  -- Realize `L` as the differential of its own affine map: `fderiv ℝ (⇑L) 0 = L`.
  have hfd : fderiv ℝ (⇑L) 0 = L := L.fderiv
  -- Wirtinger data of `⇑L` at `0`.
  set p : ℝ := ‖dz (⇑L) 0‖ with hp
  set q : ℝ := ‖dzbar (⇑L) 0‖ with hq
  set d : ℝ := L.det with hd
  have hdpos : 0 < d := hdet
  -- The two singular-value identities, transported through `hfd`.
  have hdval : d = p ^ 2 - q ^ 2 := by
    rw [hd, ← hfd]; exact det_fderiv_eq_wirtinger (⇑L) 0
  have hnval : ‖L‖ = p + q := by
    rw [← hfd]; exact opNorm_fderiv_eq_wirtinger (⇑L) 0
  -- The operator norm of the inverse: `‖L⁻¹‖ = (p + q)/d`.
  have hdet0 : 0 < (fderiv ℝ (⇑L) 0).det := by rw [hfd]; exact hdet
  have hninv : ‖ContinuousLinearMap.inverse L‖ = (p + q) / d := by
    have := opNorm_inverse_eq_wirtinger (⇑L) 0 hdet0
    rwa [hfd] at this
  -- The determinant of the inverse: `det (L⁻¹) = d⁻¹`, via the linear equivalence.
  have hdetne : L.det ≠ 0 := ne_of_gt hdet
  set e : ℂ ≃L[ℝ] ℂ := L.toContinuousLinearEquivOfDetNeZero hdetne with he
  have hecoe : (e : ℂ →L[ℝ] ℂ) = L :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero L hdetne
  have hinv_eq : ContinuousLinearMap.inverse L = (e.symm : ℂ →L[ℝ] ℂ) := by
    rw [← hecoe, ContinuousLinearMap.inverse_equiv e]
  have hinvdet : (ContinuousLinearMap.inverse L).det = d⁻¹ := by
    rw [hinv_eq, ContinuousLinearEquiv.det_coe_symm, hecoe, hd]
  constructor
  · -- Positivity of the inverse determinant.
    rw [hinvdet]; exact inv_pos.mpr hdpos
  · -- The dilatation bound: `((p+q)/d)² ≤ K·d⁻¹ ⟺ (p+q)² ≤ K·d`.
    have hKd : (p + q) ^ 2 ≤ K * d := by rw [← hnval]; exact hK
    rw [hninv, hinvdet, div_pow]
    have hrhs : K * d⁻¹ = (K * d) / d ^ 2 := by
      field_simp
    rw [hrhs]
    gcongr

/-! ## N4 — the forward Sobolev package -/

/-- **The forward `W^{1,2}_loc` package of a geometric quasiconformal map (cycle-free).**
A geometric `K`-quasiconformal map is differentiable almost everywhere, its pointwise
partials `(Df·)1`, `(Df·)I` form its weak gradient with locally square-integrable
components, `f ∈ W^{1,2}_loc`, and the or-zero dilatation bound
`0 ≤ det Df ∧ ‖Df‖² ≤ K·det Df` holds at almost every point of differentiability.

Everything here is downstream of the **proved** parametrized ACL chain and the **proved**
or-zero dilatation bound; in particular no nondegeneracy (`J_f > 0`) is claimed or consumed.

*Proof sketch.* A.e. differentiability is `ae_differentiableAt_gehringLehto` (via
`IsQCGeometric.toAxisRectModulusBound`). The slice gradient of
`exists_acl_memLp_sliceGradient` agrees a.e. with the pointwise partials by
`fderiv_ae_eq_weakDirDeriv` (`QC/LengthArea/Mollification.lean`), transferring the `L²_loc`
bounds; the weak gradient is `hasWeakGradient_of_aeSliceAC`
(`QC/LengthArea/ReverseLengthArea.lean`) fed by the slice absolute continuity. `MemW12loc f`
is `memWklocP_one_of_acl` (`Analysis/Sobolev/AbsolutelyContinuousLines.lean`) with
`MemLpLocOn f 2` from continuity on compacts. The last conjunct is
`IsQCGeometric.dilatation_le_or_zero`. This is the pattern of
`IsQCGeometric.reverseLengthArea_data` (`QC/GeometricToAnalytic/Assembly.lean`) run with the
or-zero bound in place of the nondegenerate one.
-/
theorem IsQCGeometric.forwardW12Data {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    (∀ᵐ z : ℂ, DifferentiableAt ℝ f z) ∧
    HasWeakGradient (fun w => (fderiv ℝ f w) 1) (fun w => (fderiv ℝ f w) Complex.I) f
      Set.univ ∧
    MemLpLocOn (fun w => (fderiv ℝ f w) 1) (2 : ℝ≥0∞) Set.univ ∧
    MemLpLocOn (fun w => (fderiv ℝ f w) Complex.I) (2 : ℝ≥0∞) Set.univ ∧
    MemW12loc f ∧
    (∀ᵐ z : ℂ, DifferentiableAt ℝ f z →
      0 ≤ (fderiv ℝ f z).det ∧ ‖fderiv ℝ f z‖ ^ 2 ≤ K * (fderiv ℝ f z).det) := by
  classical
  have hfcont : Continuous f := hf.2.1.isHomeomorph.continuous
  -- (1) A.e. differentiability, Grötzsch-free (via the proved forward ACL chain).
  have hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z := hf.ae_differentiableAt_gehringLehto
  -- The ACL slice gradient with `L²_loc` energy.
  obtain ⟨gx, gy, haclx, hacly, hgx2, hgy2⟩ := hf.exists_acl_memLp_sliceGradient
  -- `L²_loc ⟹ L¹_loc` on compacts.
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict Kc) := hh Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hfLI : LocallyIntegrable f := hfcont.locallyIntegrable
  have hgxLI : LocallyIntegrable gx := hLIofL2 hgx2
  have hgyLI : LocallyIntegrable gy := hLIofL2 hgy2
  -- The slice gradient is a weak gradient of `f`.
  have hwg0 : HasWeakGradient gx gy f Set.univ :=
    hasWeakGradient_of_acl hfLI hgxLI hgyLI haclx hacly
  -- Bridge: the pointwise partials agree a.e. with the slice partials.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwg0.1 (locallyIntegrableOn_univ.mpr hgxLI) hdiff
      (Or.inl rfl) hfLI
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwg0.2 (locallyIntegrableOn_univ.mpr hgyLI) hdiff
      (Or.inr rfl) hfLI
  -- (3),(4) `L²_loc` of the pointwise partials, transported a.e. from the slice partials.
  have hpx2 : MemLpLocOn (fun w => (fderiv ℝ f w) 1) (2 : ℝ≥0∞) Set.univ := by
    intro Kc hKu hKc
    exact (hgx2 Kc hKu hKc).ae_eq (Filter.EventuallyEq.symm (ae_restrict_of_ae haex))
  have hpy2 : MemLpLocOn (fun w => (fderiv ℝ f w) Complex.I) (2 : ℝ≥0∞) Set.univ := by
    intro Kc hKu hKc
    exact (hgy2 Kc hKu hKc).ae_eq (Filter.EventuallyEq.symm (ae_restrict_of_ae haey))
  -- (2) The pointwise-partial weak gradient via the slice-AC bridge.
  have hacx : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b := by
    filter_upwards [haclx] with y hy using hy.1
  have hacy : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b := by
    filter_upwards [hacly] with x hx using hx.1
  have hpxLI : LocallyIntegrable (fun w => (fderiv ℝ f w) 1) := hLIofL2 hpx2
  have hpyLI : LocallyIntegrable (fun w => (fderiv ℝ f w) Complex.I) := hLIofL2 hpy2
  have hwg : HasWeakGradient (fun w => (fderiv ℝ f w) 1)
      (fun w => (fderiv ℝ f w) Complex.I) f Set.univ :=
    hasWeakGradient_of_aeSliceAC hfcont hdiff hpxLI hpyLI hacx hacy
  -- (5) `MemW12loc f`: `f ∈ L²_loc` from continuity on compacts, plus the ACL package.
  have hfL2 : MemLpLocOn f (2 : ℝ≥0∞) Set.univ := by
    intro Kc _ hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hfcont.continuousOn
    have hbound : ∀ᵐ x ∂(volume.restrict Kc), ‖f x‖ ≤ C := by
      rw [ae_restrict_iff' hKc.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hfcont.aestronglyMeasurable C hbound).mono_exponent le_top
  have hW12 : MemW12loc f :=
    memWklocP_one_of_acl hfL2 hgx2 hgy2 hfLI hgxLI hgyLI haclx hacly
  -- (6) The or-zero dilatation bound.
  exact ⟨hdiff, hwg, hpx2, hpy2, hW12, hf.dilatation_le_or_zero⟩

/-! ## N3 — the keystone: axis-rectangle modulus bounds for the inverse -/

/-- **KEYSTONE: the inverse of a geometric quasiconformal map satisfies the axis-rectangle
modulus bounds** — `AxisRectModulusBound g K` for any two-sided inverse `g` of `f`. This is
the classical inverse-invariance estimate `M(g(R)) ≤ K·M(R)` on axis rectangles, obtained
**without** quadrilateral modulus reciprocity (no Riemann mapping, no Carathéodory boundary
correspondence): the length–area / Cauchy–Schwarz mechanism is run through the forward map
with an explicit admissible density.

*Proof sketch (crossing family; the separating family is the mirror with `Re` replaced by
`Im` and `(b−a)` by `(t−s)`).* Fix the rectangle `R = (a,b)×(s,t)` and let
`Γ := R.imageCurveFamily g`; unfolding `imageCurveFamily` through `f '' (g '' S) = S`
(`Set.image_image` with `hfg`), the members of `Γ` are the AC curves `δ` joining
`g '' ({a}×[s,t])` to `g '' ({b}×[s,t])` inside the compact `T := g '' R̄`.

1. *Exceptional removal.* The subfamily `Γ∞` with
   `arcLengthLineIntegral ‖fderiv ℝ f‖₊ δ = ∞` has zero modulus
   (`curveModulus_lineIntegral_top_zero_of_memW12loc`, fed by N4), and the non-good
   subfamily `Γbad` has zero modulus (`curveModulus_notGoodCurve_zero_of_memW12loc`);
   `curveModulus_union_zero` and `curveModulus_sdiff_modulus_zero` reduce to
   `Γ' := Γ ∖ (Γ∞ ∪ Γbad)`.
2. *Admissible density.* `ρ := T.indicator (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) / ofReal (b−a)`
   is measurable (`measurable_fderiv`, `T` compact hence closed). For `δ ∈ Γ'`, the Fuglede
   upper-gradient inequality (`fugledeUpperGradient_of_continuous` at `x = 0`, `y = 1`)
   gives `dist (f (δ 0)) (f (δ 1)) ≤ ∫ fdNormMulDeriv f δ`; the endpoints satisfy
   `Re (f (δ 0)) = a`, `Re (f (δ 1)) = b`, so the left side is at least `b − a`; the trace
   lies in `T`, so the right side is dominated by
   `(arcLengthLineIntegral (T.indicator ‖fderiv f‖₊) δ).toReal` (finite since `δ ∉ Γ∞`).
   Hence `1 ≤ arcLengthLineIntegral ρ δ`: `ρ` is admissible for `Γ'`.
3. *Energy.* With `S := T ∩ {z | DifferentiableAt ℝ f z}` (measurable by
   `measurableSet_of_differentiableAt`; the complement in `T` is null by N4),
   `∫⁻ ρ² = (b−a)⁻²·∫⁻_S ‖Df‖² ≤ (b−a)⁻²·K·∫⁻_S ofReal |det Df|` (the or-zero dilatation of
   N4, `det ≥ 0` a.e.) `≤ (b−a)⁻²·K·volume (f '' S)` (the injective easy half of the area
   formula, `MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image`, with `InjOn` from the
   homeomorphism) `≤ (b−a)⁻²·K·volume R̄ = K·(t−s)/(b−a)` (`f '' S ⊆ f '' (g '' R̄) = R̄`,
   `volume_axisRect`).
4. `curveModulus Γ' ≤ ∫⁻ ρ²` by the infimum definition; combine with step 1. The bundle's
   remaining fields are `hf.1 : 1 ≤ K` and `IsHomeomorph g` (the two-sided inverse of the
   homeomorphism `f` is `(hf.2.1.isHomeomorph.homeomorph f).symm` as a function, hence a
   homeomorphism).

This is Lehto–Virtanen's rectangle length–area estimate (Ch. IV §2) with the "image length
dominates the side" step justified by Fuglede's theorem instead of piecewise smoothness; it
is the standard proof that the analytic definition is inverse-invariant, run directly at the
geometric data. -/
theorem IsQCGeometric.inverse_axisRectModulusBound {f g : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (hfg : ∀ w, f (g w) = w) (hgf : ∀ z, g (f z) = z) :
    AxisRectModulusBound g K := by
  classical
  -- `hgf` is carried for interface symmetry with the sibling inverse nodes; this proof
  -- reconstructs `g` from `hfg` and injectivity alone.
  have _ := hgf
  have hfcont : Continuous f := hf.2.1.isHomeomorph.continuous
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  -- `g` is a homeomorphism (the two-sided inverse of the homeomorphism `f`).
  have hgeq : g = ⇑(hf.2.1.isHomeomorph.homeomorph f).symm := by
    funext w
    apply hf.2.1.isHomeomorph.injective
    rw [hfg w]
    exact ((hf.2.1.isHomeomorph.homeomorph f).apply_symm_apply w).symm
  have hghomeo : IsHomeomorph g := by
    rw [hgeq]; exact (hf.2.1.isHomeomorph.homeomorph f).symm.isHomeomorph
  have hgcont : Continuous g := hghomeo.continuous
  -- The forward package (N4): a.e. differentiability, `W^{1,2}_loc`, or-zero dilatation.
  obtain ⟨hdiff, -, -, -, hW12, hdil⟩ := hf.forwardW12Data
  -- The gradient-norm density.
  set G : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞) with hG
  have hGmeas : Measurable G := ((measurable_fderiv ℝ f).nnnorm).coe_nnreal_ennreal
  -- ==================================================================
  -- The generic one-parametrization estimate: for any quadrilateral `Q` whose left/right
  -- sides sit on the levels `cL < cR` of a `1`-Lipschitz coordinate `proj`, the `g`-image
  -- family has modulus at most `K · volume Q.image / (cR − cL)²`.
  -- ==================================================================
  have main : ∀ (Q : Quadrilateral) (proj : ℂ → ℝ) (cL cR : ℝ),
      (∀ z z' : ℂ, |proj z - proj z'| ≤ dist z z') →
      (∀ z ∈ Q.leftSide, proj z = cL) →
      (∀ z ∈ Q.rightSide, proj z = cR) →
      0 < cR - cL →
      curveModulus (Q.imageCurveFamily g)
        ≤ (ENNReal.ofReal K * volume Q.image) / (ENNReal.ofReal (cR - cL)) ^ 2 := by
    intro Q proj cL cR hlip hleft hright hw
    set cE : ℝ≥0∞ := ENNReal.ofReal (cR - cL) with hcE
    have hcE0 : cE ≠ 0 := by
      rw [hcE, Ne, ENNReal.ofReal_eq_zero, not_le]; exact hw
    have hcEtop : cE ≠ ⊤ := by rw [hcE]; exact ENNReal.ofReal_ne_top
    set Γ : Set (ℝ → ℂ) := Q.imageCurveFamily g with hΓ
    have hΓcont : ∀ γ ∈ Γ, Continuous γ := fun γ hγ => hγ.1
    -- The compact carrier `T := g '' Q.image`.
    set T : Set ℂ := g '' Q.image with hT
    have hTcpt : IsCompact T := Q.isCompact_image.image hgcont
    have hTmeas : MeasurableSet T := hTcpt.isClosed.measurableSet
    -- STEP 1 — exceptional removal: infinite-line-integral and non-good subfamilies.
    set Γinf : Set (ℝ → ℂ) := {γ ∈ Γ | arcLengthLineIntegral G γ = ∞} with hΓinf
    set Γbad : Set (ℝ → ℂ) := {γ ∈ Γ | ¬ GoodCurve f γ} with hΓbad
    have hinf0 : curveModulus Γinf = 0 :=
      curveModulus_lineIntegral_top_zero_of_memW12loc hfcont hdiff hW12 Γ hΓcont
    have hbad0 : curveModulus Γbad = 0 :=
      curveModulus_notGoodCurve_zero_of_memW12loc hfcont hdiff hW12 Γ hΓcont
    have hsub : Γinf ∪ Γbad ⊆ Γ := by
      rintro γ (hγ | hγ) <;> exact hγ.1
    have hmod_eq : curveModulus (Γ \ (Γinf ∪ Γbad)) = curveModulus Γ :=
      curveModulus_sdiff_modulus_zero hsub (curveModulus_union_zero hinf0 hbad0)
    -- STEP 2 — the explicit admissible density `ρ := 𝟙_T · ‖Df‖ / (cR − cL)`.
    set ρ : ℂ → ℝ≥0∞ := fun z => T.indicator G z / cE with hρ
    have hρmeas : Measurable ρ := (hGmeas.indicator hTmeas).div_const cE
    -- STEP 3 — admissibility on the reduced family, via the Fuglede upper gradient.
    have hadm : ∀ γ ∈ Γ \ (Γinf ∪ Γbad), 1 ≤ arcLengthLineIntegral ρ γ := by
      rintro γ ⟨hγΓ, hγnot⟩
      have hγfin : arcLengthLineIntegral G γ ≠ ∞ := by
        intro hcon
        exact hγnot (Or.inl ⟨hγΓ, hcon⟩)
      have hγgood : GoodCurve f γ := by
        by_contra hcon
        exact hγnot (Or.inr ⟨hγΓ, hcon⟩)
      obtain ⟨hγcont, hγac, hγ0, hγ1, hγtrace⟩ := hγΓ
      -- The Fuglede upper-gradient inequality across `[0, 1]`.
      have huIcc : Set.uIcc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      have hfug := fugledeUpperGradient_of_continuous hfcont hγcont hγac hγfin 0 1
        huIcc hγgood
      -- The endpoints of `f ∘ γ` sit on the two levels.
      have hf0 : proj (f (γ 0)) = cL := by
        obtain ⟨z, hz, hzeq⟩ := hγ0
        rw [← hzeq, hfg z]
        exact hleft z hz
      have hf1 : proj (f (γ 1)) = cR := by
        obtain ⟨z, hz, hzeq⟩ := hγ1
        rw [← hzeq, hfg z]
        exact hright z hz
      have hdistlb : cR - cL ≤ dist ((f ∘ γ) 0) ((f ∘ γ) 1) := by
        have hl := hlip (f (γ 1)) (f (γ 0))
        rw [hf1, hf0] at hl
        calc cR - cL ≤ |cR - cL| := le_abs_self _
          _ ≤ dist (f (γ 1)) (f (γ 0)) := hl
          _ = dist ((f ∘ γ) 0) ((f ∘ γ) 1) := by rw [dist_comm]; rfl
      -- The Bochner integral of the density is dominated by the arc-length line integral.
      have hBochner_le : (∫ t in Set.uIoc (0:ℝ) 1, fdNormMulDeriv f γ t)
          ≤ (arcLengthLineIntegral G γ).toReal := by
        have hnn : ∀ t, 0 ≤ fdNormMulDeriv f γ t := fun t =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have hmeas : Measurable (fdNormMulDeriv f γ) := by
          have h1 : Measurable (fun t => ‖fderiv ℝ f (γ t)‖) :=
            ((measurable_fderiv ℝ f).norm).comp hγcont.measurable
          have h2 : Measurable (fun t => ‖deriv γ t‖) := (measurable_deriv γ).norm
          simpa only [fdNormMulDeriv] using! h1.mul h2
        rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall (fun t => hnn t)) hmeas.aestronglyMeasurable]
        apply ENNReal.toReal_mono hγfin
        have hpt : ∀ t, ENNReal.ofReal (fdNormMulDeriv f γ t)
            = G (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
          intro t
          rw [fdNormMulDeriv, ENNReal.ofReal_mul (norm_nonneg _),
            show ENNReal.ofReal ‖fderiv ℝ f (γ t)‖ = (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) from by
              rw [ofReal_norm, enorm_eq_nnnorm],
            show ENNReal.ofReal ‖deriv γ t‖ = (‖deriv γ t‖₊ : ℝ≥0∞) from by
              rw [ofReal_norm, enorm_eq_nnnorm]]
        calc ∫⁻ t in Set.uIoc (0:ℝ) 1, ENNReal.ofReal (fdNormMulDeriv f γ t)
            = ∫⁻ t in Set.uIoc (0:ℝ) 1, G (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
              simp_rw [hpt]
          _ ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, G (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
              apply lintegral_mono_set
              rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
              exact Set.Ioc_subset_Icc_self
          _ = arcLengthLineIntegral G γ := rfl
      -- Hence `cR − cL ≤ arcLengthLineIntegral G γ` in `ℝ≥0∞`.
      have hlb : cE ≤ arcLengthLineIntegral G γ := by
        rw [hcE]
        calc ENNReal.ofReal (cR - cL)
            ≤ ENNReal.ofReal (dist ((f ∘ γ) 0) ((f ∘ γ) 1)) :=
              ENNReal.ofReal_le_ofReal hdistlb
          _ ≤ ENNReal.ofReal (∫ t in Set.uIoc (0:ℝ) 1, fdNormMulDeriv f γ t) :=
              ENNReal.ofReal_le_ofReal hfug
          _ ≤ ENNReal.ofReal ((arcLengthLineIntegral G γ).toReal) :=
              ENNReal.ofReal_le_ofReal hBochner_le
          _ = arcLengthLineIntegral G γ := ENNReal.ofReal_toReal hγfin
      -- The trace stays in `T`, so the `ρ`-line-integral is the `G`-one over `cE`.
      have hint_eq : arcLengthLineIntegral ρ γ = arcLengthLineIntegral G γ * cE⁻¹ := by
        rw [arcLengthLineIntegral, arcLengthLineIntegral,
          ← lintegral_mul_const' cE⁻¹ _ (ENNReal.inv_ne_top.mpr hcE0)]
        refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
        simp only [hρ]
        rw [Set.indicator_of_mem (hγtrace t ht), div_eq_mul_inv]
        ring
      rw [hint_eq]
      calc (1 : ℝ≥0∞) = cE * cE⁻¹ := (ENNReal.mul_inv_cancel hcE0 hcEtop).symm
        _ ≤ arcLengthLineIntegral G γ * cE⁻¹ := by gcongr
    -- STEP 4 — the energy of `ρ`: dilatation + injective area formula.
    have henergy : (∫⁻ z, ρ z ^ 2)
        ≤ (ENNReal.ofReal K * volume Q.image) / cE ^ 2 := by
      have hinvpow_ne_top : (cE⁻¹) ^ 2 ≠ ⊤ :=
        ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hcE0)
      -- Split off the constant.
      have hpt : ∀ z, ρ z ^ 2 = T.indicator (fun w => G w ^ 2) z * (cE⁻¹) ^ 2 := by
        intro z
        simp only [hρ]
        rw [div_eq_mul_inv, mul_pow]
        congr 1
        by_cases hz : z ∈ T
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
          simp
      have hstep1 : (∫⁻ z, ρ z ^ 2) = (∫⁻ z in T, G z ^ 2) * (cE⁻¹) ^ 2 := by
        simp_rw [hpt]
        rw [lintegral_mul_const' _ _ hinvpow_ne_top, lintegral_indicator hTmeas]
      -- Pass to the differentiability subset `S` (the complement is null).
      set S : Set ℂ := T ∩ {z : ℂ | DifferentiableAt ℝ f z} with hS
      have hSmeas : MeasurableSet S := hTmeas.inter (measurableSet_of_differentiableAt ℝ f)
      have hTSae : S =ᵐ[volume] T := by
        rw [MeasureTheory.ae_eq_set]
        constructor
        · rw [Set.sdiff_eq_empty.mpr Set.inter_subset_left]
          exact measure_empty
        · refine measure_mono_null ?_ (MeasureTheory.ae_iff.mp hdiff)
          rintro z ⟨hzT, hzS⟩
          simp only [hS, Set.mem_inter_iff, not_and] at hzS
          exact hzS hzT
      have hTS : (∫⁻ z in T, G z ^ 2) = ∫⁻ z in S, G z ^ 2 :=
        (MeasureTheory.setLIntegral_congr hTSae).symm
      -- The or-zero dilatation bound under the integral.
      have hdilS : ∀ᵐ z ∂(volume.restrict S), G z ^ 2
          ≤ ENNReal.ofReal K * ENNReal.ofReal |(fderiv ℝ f z).det| := by
        rw [ae_restrict_iff' hSmeas]
        filter_upwards [hdil] with z hz hzS
        obtain ⟨hdet0, hdil2⟩ := hz hzS.2
        have h1 : G z ^ 2 = ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) := by
          rw [hG, ENNReal.ofReal_pow (norm_nonneg _)]
          congr 1
          rw [ofReal_norm, enorm_eq_nnnorm]
        rw [h1, abs_of_nonneg hdet0, ← ENNReal.ofReal_mul (le_of_lt hK0)]
        exact ENNReal.ofReal_le_ofReal hdil2
      have hSdil : (∫⁻ z in S, G z ^ 2)
          ≤ ENNReal.ofReal K * ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_mono_ae hdilS
      -- The injective easy half of the area formula.
      have hderivS : ∀ x ∈ S, HasFDerivWithinAt f (fderiv ℝ f x) S x := fun x hx =>
        (hx.2.hasFDerivAt).hasFDerivWithinAt
      have hinjS : Set.InjOn f S := hf.2.1.isHomeomorph.injective.injOn
      have hcov : (∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det|) ≤ volume (f '' S) :=
        MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image volume hSmeas hderivS hinjS
      -- `f '' S ⊆ f '' (g '' Q.image) = Q.image`.
      have hfS : f '' S ⊆ Q.image := by
        rintro w ⟨z, hz, rfl⟩
        obtain ⟨u, hu, huz⟩ := hz.1
        rw [← huz, hfg u]
        exact hu
      have hvol_le : volume (f '' S) ≤ volume Q.image := measure_mono hfS
      -- Assemble the energy chain.
      calc (∫⁻ z, ρ z ^ 2) = (∫⁻ z in T, G z ^ 2) * (cE⁻¹) ^ 2 := hstep1
        _ = (∫⁻ z in S, G z ^ 2) * (cE⁻¹) ^ 2 := by rw [hTS]
        _ ≤ (ENNReal.ofReal K * volume Q.image) * (cE⁻¹) ^ 2 := by
            gcongr
            refine le_trans hSdil ?_
            gcongr
            exact le_trans hcov hvol_le
        _ = (ENNReal.ofReal K * volume Q.image) / cE ^ 2 := by
            rw [div_eq_mul_inv, ← ENNReal.inv_pow]
    -- STEP 5 — conclude via the modulus infimum.
    have hadm' : IsAdmissibleDensity ρ (Γ \ (Γinf ∪ Γbad)) := ⟨hρmeas, hadm⟩
    calc curveModulus Γ = curveModulus (Γ \ (Γinf ∪ Γbad)) := hmod_eq.symm
      _ ≤ ∫⁻ z, ρ z ^ 2 := iInf₂_le ρ hadm'
      _ ≤ (ENNReal.ofReal K * volume Q.image) / cE ^ 2 := henergy
  -- ==================================================================
  -- Assemble the bundle: the two instances of `main` and the final arithmetic.
  -- ==================================================================
  have harith : ∀ u v : ℝ, 0 < u → 0 < v →
      (ENNReal.ofReal K * (ENNReal.ofReal u * ENNReal.ofReal v)) / (ENNReal.ofReal u) ^ 2
        = ENNReal.ofReal (K * (v / u)) := by
    intro u v hu hv
    have hu' : u ≠ 0 := ne_of_gt hu
    have huu : (0:ℝ) < u * u := by positivity
    rw [show K * (v / u) = (K * (u * v)) / (u * u) from by
        field_simp,
      ENNReal.ofReal_div_of_pos huu, ENNReal.ofReal_mul (le_of_lt hK0),
      ENNReal.ofReal_mul hu.le, sq, ENNReal.ofReal_mul hu.le]
  refine ⟨hf.1, hghomeo, ?_, ?_⟩
  · -- The crossing (standard) parametrization: `proj = re`, levels `a < b`.
    intro a b s t hab hst
    have hba : (0:ℝ) < b - a := by linarith
    have hvol : volume (axisRectQuadrilateral a b s t hab hst).image
        = ENNReal.ofReal (b - a) * ENNReal.ofReal (t - s) := by
      rw [show (axisRectQuadrilateral a b s t hab hst).image = axisRect a b s t from
        axisRectQuadrilateral_image hab hst]
      exact volume_axisRect a b s t
    have hlip : ∀ z z' : ℂ, |z.re - z'.re| ≤ dist z z' := by
      intro z z'
      rw [dist_eq_norm, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hleft : ∀ z ∈ (axisRectQuadrilateral a b s t hab hst).leftSide, z.re = a := by
      intro z hz
      rw [axisRectQuadrilateral_leftSide hab hst] at hz
      exact hz.1
    have hright : ∀ z ∈ (axisRectQuadrilateral a b s t hab hst).rightSide, z.re = b := by
      intro z hz
      rw [axisRectQuadrilateral_rightSide hab hst] at hz
      exact hz.1
    calc curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily g)
        ≤ (ENNReal.ofReal K * volume (axisRectQuadrilateral a b s t hab hst).image)
            / (ENNReal.ofReal (b - a)) ^ 2 :=
          main (axisRectQuadrilateral a b s t hab hst) Complex.re a b hlip hleft hright
            (by linarith)
      _ = (ENNReal.ofReal K * (ENNReal.ofReal (b - a) * ENNReal.ofReal (t - s)))
            / (ENNReal.ofReal (b - a)) ^ 2 := by rw [hvol]
      _ = ENNReal.ofReal (K * ((t - s) / (b - a))) := harith (b - a) (t - s) hba (by linarith)
  · -- The separating (swapped) parametrization: `proj = im`, levels `s < t`.
    intro a b s t hab hst
    have hts : (0:ℝ) < t - s := by linarith
    have hvol : volume (axisRectQuadrilateralSwap a b s t hab hst).image
        = ENNReal.ofReal (b - a) * ENNReal.ofReal (t - s) := by
      rw [axisRectQuadrilateralSwap_image hab hst,
        show (axisRectQuadrilateral a b s t hab hst).image = axisRect a b s t from
          axisRectQuadrilateral_image hab hst]
      exact volume_axisRect a b s t
    have hlip : ∀ z z' : ℂ, |z.im - z'.im| ≤ dist z z' := by
      intro z z'
      rw [dist_eq_norm, ← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have hleft : ∀ z ∈ (axisRectQuadrilateralSwap a b s t hab hst).leftSide, z.im = s := by
      intro z hz
      rw [axisRectQuadrilateralSwap_leftSide hab hst] at hz
      exact hz.1
    have hright : ∀ z ∈ (axisRectQuadrilateralSwap a b s t hab hst).rightSide, z.im = t := by
      intro z hz
      rw [axisRectQuadrilateralSwap_rightSide hab hst] at hz
      exact hz.1
    calc curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily g)
        ≤ (ENNReal.ofReal K * volume (axisRectQuadrilateralSwap a b s t hab hst).image)
            / (ENNReal.ofReal (t - s)) ^ 2 :=
          main (axisRectQuadrilateralSwap a b s t hab hst) Complex.im s t hlip hleft hright
            (by linarith)
      _ = (ENNReal.ofReal K * (ENNReal.ofReal (t - s) * ENNReal.ofReal (b - a)))
            / (ENNReal.ofReal (t - s)) ^ 2 := by
          rw [hvol, mul_comm (ENNReal.ofReal (b - a))]
      _ = ENNReal.ofReal (K * ((b - a) / (t - s))) := harith (t - s) (b - a) hts (by linarith)

/-! ## N5a, N5 — forward higher integrability and the forward Lusin condition (N) -/

/-- **Forward Bojarski higher integrability.** A geometric `K`-quasiconformal map has a weak
gradient `(gx, gy)` whose components are locally `Lᵖ` for some exponent `p > 2`.

*Proof sketch.* Clamp the Beltrami quotient:
`μ z := if ‖dzbar f z / dz f z‖ ≤ (K−1)/(K+1) then dzbar f z / dz f z else 0`. It is
measurable (`measurable_fderiv_apply_const`) with `‖μ‖∞ ≤ (K−1)/(K+1) < 1` by construction —
the STEP 2–8 clamping pattern of `IsQCGeometric.exists_beltrami`
(`QC/GeometricToAnalytic/Assembly.lean`) run with `IsQCGeometric.dilatation_le_or_zero` in
place of `infinitesimal_dilatation`: at points where `Df z = 0` both Wirtinger derivatives
vanish and the convention `0/0 = 0` makes the clamp return `0`, so the pointwise Beltrami
equation `dzbar f z = μ z · dz f z` holds trivially there — this is why the or-zero bound
suffices and `J_f > 0` is never needed. The pointwise equation transfers to the weak partials
of `IsQCGeometric.forwardW12Data` (they agree a.e. with the pointwise ones by construction),
producing the weak Wirtinger form consumed by `beltrami_higher_integrability`
(`QC/InverseQC/LusinN.lean`, taking raw hypotheses: `Measurable μ`, `eLpNormEssSup μ < 1`,
`Continuous f`, `MemLpLocOn f 2` from continuity on compacts, the weak gradient and its
`L²_loc` bounds). Decompose `∂f ∈ Lᵖ_loc` back into both partials via `gx = ∂f + ∂̄f`,
`gy = i(∂f − ∂̄f)` and `‖∂̄f‖ ≤ ‖μ‖∞·‖∂f‖`, as in
`IsQCAnalytic.exists_weakGradient_memLpLocOn_gt_two` (`QC/InverseQC/LusinN.lean`).
-/
theorem IsQCGeometric.exists_weakGradient_memLpLocOn_gt_two {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∃ (p : ℝ) (gx gy : ℂ → ℂ), 2 < p ∧ HasWeakGradient gx gy f Set.univ ∧
      MemLpLocOn gx (ENNReal.ofReal p) Set.univ ∧
      MemLpLocOn gy (ENNReal.ofReal p) Set.univ := by
  classical
  have hfcont : Continuous f := hf.2.1.isHomeomorph.continuous
  -- STEP 0 — the forward `W^{1,2}_loc` package (no nondegeneracy consumed).
  obtain ⟨hdiff, hwg, hpx2, hpy2, _hW12, _⟩ := hf.forwardW12Data
  -- STEP 1 — scalar bookkeeping.
  have hK1 : (0 : ℝ) < K + 1 := by linarith [hf.1]
  set c : ℝ := (K - 1) / (K + 1) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; apply div_nonneg <;> linarith [hf.1]
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hK1]; linarith
  -- STEP 2 — the clamped Beltrami coefficient (Lean's `0/0 = 0` handles collapse points).
  set raw : ℂ → ℂ := fun w => dzbar f w / dz f w with hraw
  set μ : ℂ → ℂ := fun w => if ‖raw w‖ ≤ c then raw w else 0 with hμ
  -- STEP 3 — measurability.
  have hdzf_meas : Measurable (fun w : ℂ => dz f w) := by
    have h1 : Measurable (fun w : ℂ => (fderiv ℝ f w) 1) := measurable_fderiv_apply_const ℝ f 1
    have h2 : Measurable (fun w : ℂ => (fderiv ℝ f w) Complex.I) :=
      measurable_fderiv_apply_const ℝ f Complex.I
    simpa only [dz] using! (measurable_const.mul (h1.sub (measurable_const.mul h2)))
  have hdzbarf_meas : Measurable (fun w : ℂ => dzbar f w) := by
    have h1 : Measurable (fun w : ℂ => (fderiv ℝ f w) 1) := measurable_fderiv_apply_const ℝ f 1
    have h2 : Measurable (fun w : ℂ => (fderiv ℝ f w) Complex.I) :=
      measurable_fderiv_apply_const ℝ f Complex.I
    simpa only [dzbar] using! (measurable_const.mul (h1.add (measurable_const.mul h2)))
  have hraw_meas : Measurable raw := hdzbarf_meas.div hdzf_meas
  have hμ_meas : Measurable μ :=
    Measurable.ite (measurableSet_le hraw_meas.norm measurable_const) hraw_meas measurable_const
  -- STEP 4 — pointwise bound `‖μ w‖ ≤ c` and the essential-sup bound.
  have hμ_le : ∀ w, ‖μ w‖ ≤ c := by
    intro w
    rw [hμ]
    by_cases h : ‖raw w‖ ≤ c
    · simp [h]
    · simp [h, hc0]
  have hμ_bound : eLpNormEssSup μ volume < 1 := by
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hμ_le)) ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mpr hc1
  -- STEP 5 — the pointwise Beltrami equation from the or-zero Wirtinger bracket.
  have hbel0 : ∀ᵐ z, dzbar f z = μ z * dz f z := by
    filter_upwards [hdiff, hf.wirtinger_bracket_or_zero] with z hzd hor
    rcases hor hzd with hzero | ⟨hqp, hbr⟩
    · -- Total collapse: `Df z = 0` makes both Wirtinger derivatives vanish.
      have hdz0 : dz f z = 0 := by rw [dz, hzero]; simp
      have hdzbar0 : dzbar f z = 0 := by rw [dzbar, hzero]; simp
      rw [hdzbar0, hdz0, mul_zero]
    · -- Bracket branch: `q ≤ c·p` with `p > 0`, so the clamp returns the raw quotient.
      have hppos : 0 < ‖dz f z‖ := lt_of_le_of_lt (norm_nonneg _) hqp
      have hdzne : dz f z ≠ 0 := by rw [← norm_pos_iff]; exact hppos
      have hqcp : ‖dzbar f z‖ ≤ c * ‖dz f z‖ := by
        have hstep : (K + 1) * ‖dzbar f z‖ ≤ (K - 1) * ‖dz f z‖ := by nlinarith [hbr]
        rw [hc, div_mul_eq_mul_div, le_div_iff₀ hK1]
        nlinarith [hstep]
      have hraww : ‖raw z‖ ≤ c := by
        rw [hraw]; simp only; rw [norm_div, div_le_iff₀ hppos]
        exact hqcp
      have hμz : μ z = dzbar f z / dz f z := by
        rw [hμ]; simp only [hraww, if_true]; rw [hraw]
      rw [hμz, div_mul_cancel₀ (dzbar f z) hdzne]
  -- The weak Wirtinger–Beltrami form is the same statement (the pointwise partials are the
  -- weak gradient and `dz`/`dzbar` are by definition their Wirtinger combinations).
  have hbel : ∀ᵐ z, (1 / 2 : ℂ)
      * ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I)
      = μ z * ((1 / 2 : ℂ)
        * ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I)) := hbel0
  -- STEP 6 — `f ∈ L²_loc` from continuity on compacts.
  have hfL2 : MemLpLocOn f (2 : ℝ≥0∞) Set.univ := by
    intro Kc _ hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hfcont.continuousOn
    have hbound : ∀ᵐ x ∂(volume.restrict Kc), ‖f x‖ ≤ C := by
      rw [ae_restrict_iff' hKc.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hfcont.aestronglyMeasurable C hbound).mono_exponent le_top
  -- STEP 7 — Bojarski higher integrability on the weak `∂`-derivative.
  obtain ⟨p, hp2, hdzp'⟩ :=
    beltrami_higher_integrability hμ_meas hμ_bound hfcont hfL2 hwg.1 hwg.2 hpx2 hpy2 hbel
  have hdzp : MemLpLocOn (fun z => dz f z) (ENNReal.ofReal p) Set.univ := hdzp'
  -- STEP 8 — carry `∂̄f` along: `dzbar f =ᵐ μ · dz f` with `‖μ‖ ≤ c < 1` pointwise.
  have hdzbarp : MemLpLocOn (fun z => dzbar f z) (ENNReal.ofReal p) Set.univ := by
    intro Kc hKu hKc
    have hdzK : MemLp (fun z => dz f z) (ENNReal.ofReal p) (volume.restrict Kc) :=
      hdzp Kc hKu hKc
    have hmeasK : AEStronglyMeasurable (fun z => μ z * dz f z) (volume.restrict Kc) :=
      (hμ_meas.aestronglyMeasurable).mul hdzK.1
    have hboundK : MemLp (fun z => μ z * dz f z) (ENNReal.ofReal p) (volume.restrict Kc) := by
      refine hdzK.of_le hmeasK ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [norm_mul]
      calc ‖μ z‖ * ‖dz f z‖ ≤ 1 * ‖dz f z‖ :=
            mul_le_mul_of_nonneg_right (le_trans (hμ_le z) hc1.le) (norm_nonneg _)
        _ = ‖dz f z‖ := one_mul _
    refine hboundK.ae_eq ?_
    filter_upwards [ae_restrict_of_ae hbel0] with z hz
    exact hz.symm
  -- STEP 9 — decompose back into both partials via the pointwise Wirtinger identities.
  have hgx_eq : (fun w => (fderiv ℝ f w) 1) = fun z => dz f z + dzbar f z := by
    funext z; rw [dz, dzbar]; ring
  have hgy_eq : (fun w => (fderiv ℝ f w) Complex.I)
      = fun z => Complex.I * (dz f z - dzbar f z) := by
    funext z; rw [dz, dzbar]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((fderiv ℝ f z) Complex.I) * hI
  refine ⟨p, (fun w => (fderiv ℝ f w) 1), (fun w => (fderiv ℝ f w) Complex.I), hp2, hwg,
    ?_, ?_⟩
  · rw [hgx_eq]
    intro Kc hKu hKc
    exact (hdzp Kc hKu hKc).add (hdzbarp Kc hKu hKc)
  · rw [hgy_eq]
    intro Kc hKu hKc
    exact ((hdzp Kc hKu hKc).sub (hdzbarp Kc hKu hKc)).const_mul Complex.I

/-- **Forward Lusin condition (N).** A geometric `K`-quasiconformal map carries
Lebesgue-null sets to Lebesgue-null sets.

*Proof sketch.* `IsQCGeometric.exists_weakGradient_memLpLocOn_gt_two` supplies
`f ∈ W^{1,p}_loc` with `p > 2`; the planar Marcus–Mizel theorem
`lusinN_image_null_of_weakGradient` (`Analysis/Sobolev/Morrey/LusinN.lean`) applies to the
continuous `f` and its super-critical weak gradient.
-/
theorem IsQCGeometric.lusinN {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ S : Set ℂ, volume S = 0 → volume (f '' S) = 0 := by
  intro S hS
  obtain ⟨p, gx, gy, hp2, hwg, hgxp, hgyp⟩ := hf.exists_weakGradient_memLpLocOn_gt_two
  exact lusinN_image_null_of_weakGradient hp2 hf.2.1.isHomeomorph.continuous
    hwg hgxp hgyp hS

/-! ## N6 — pointwise data of the inverse map -/

/-- **Pointwise infinitesimal data of the inverse map.** For any two-sided inverse `g` of a
geometric `K`-quasiconformal map `f`: at almost every `w`, the forward map is differentiable
at `g w` with positive Jacobian; `g` is differentiable at `w` with
`Dg w = (Df (g w))⁻¹`; and `J_g > 0` with the dilatation bound `‖Dg‖² ≤ K·J_g`.

*Proof sketch.* Let
`B := {¬diff} ∪ E₀ ∪ {diff ∧ det < 0} ∪ {diff ∧ Df ≠ 0 ∧ det = 0}` with
`E₀ := {diff ∧ Df = 0}`, and use the transport identity `{w | g w ∈ B} = f '' B` (mutual
inverses). `volume (f '' {¬diff}) = 0` by the forward Lusin condition
`IsQCGeometric.lusinN` and a.e. differentiability; `volume (f '' E₀) = 0` by the easy half
of the area formula (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` — null regardless
of `volume E₀`); the last two pieces are a.e. empty by
`IsQCGeometric.wirtinger_bracket_or_zero` (the bracket branch gives `det = p² − q² > 0`).
At each good `w`, the easy half of the inverse function theorem
(`HasFDerivAt.of_local_left_inverse` with
`ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`, the pattern of
`IsQCAnalytic.inverse_differentiableAt_ae`, `QC/InverseQC/LusinN.lean`) gives
differentiability of `g` and the inverse differential formula;
`ContinuousLinearMap.inverse_dilatation` transfers positivity of the Jacobian and the
dilatation bound.
-/
theorem IsQCGeometric.inverse_pointwise_data {f g : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (hfg : ∀ w, f (g w) = w) (hgf : ∀ z, g (f z) = z) :
    (∀ᵐ w : ℂ, DifferentiableAt ℝ f (g w) ∧ 0 < (fderiv ℝ f (g w)).det) ∧
    (∀ᵐ w : ℂ, DifferentiableAt ℝ g w) ∧
    (∀ᵐ w : ℂ, fderiv ℝ g w = ContinuousLinearMap.inverse (fderiv ℝ f (g w))) ∧
    (∀ᵐ w : ℂ, 0 < (fderiv ℝ g w).det) ∧
    (∀ᵐ w : ℂ, ‖fderiv ℝ g w‖ ^ 2 ≤ K * (fderiv ℝ g w).det) := by
  classical
  -- `g` is the homeomorphism-package inverse as a function, hence continuous.
  have hgeq : g = ⇑(hf.2.1.isHomeomorph.homeomorph f).symm := by
    funext w
    apply hf.2.1.isHomeomorph.injective
    rw [hfg w]
    exact ((hf.2.1.isHomeomorph.homeomorph f).apply_symm_apply w).symm
  have hgcont : Continuous g := by
    rw [hgeq]; exact (hf.2.1.isHomeomorph.homeomorph f).continuous_symm
  -- The forward data: a.e. differentiability and the forward Lusin condition (N).
  have hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z := hf.ae_differentiableAt_gehringLehto
  have hlusin : ∀ S : Set ℂ, volume S = 0 → volume (f '' S) = 0 := hf.lusinN
  -- The transport identity `{w | g w ∈ B} = f '' B` (mutual inverses).
  have htrans : ∀ B : Set ℂ, {w : ℂ | g w ∈ B} = f '' B := by
    intro B
    ext w
    constructor
    · intro hw
      exact ⟨g w, hw, hfg w⟩
    · rintro ⟨z, hzB, rfl⟩
      simpa only [Set.mem_ofPred_eq, hgf z] using hzB
  -- The bad set `B` in the source and the nullity of its image.
  set B : Set ℂ := {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hB
  have hfB : volume (f '' B) = 0 := by
    -- Split `B` into non-differentiability, total collapse, and degenerate-nonzero parts.
    have hsplit : B ⊆ {z : ℂ | ¬ DifferentiableAt ℝ f z}
        ∪ ({z : ℂ | DifferentiableAt ℝ f z ∧ fderiv ℝ f z = 0}
          ∪ {z : ℂ | DifferentiableAt ℝ f z ∧ fderiv ℝ f z ≠ 0
              ∧ ¬ 0 < (fderiv ℝ f z).det}) := by
      intro z hz
      simp only [hB, Set.mem_ofPred_eq, not_and] at hz
      by_cases hd : DifferentiableAt ℝ f z
      · by_cases h0 : fderiv ℝ f z = 0
        · exact Or.inr (Or.inl ⟨hd, h0⟩)
        · exact Or.inr (Or.inr ⟨hd, h0, hz hd⟩)
      · exact Or.inl hd
    -- (i) The non-differentiability set has null image by the forward Lusin condition.
    have h1 : volume (f '' {z : ℂ | ¬ DifferentiableAt ℝ f z}) = 0 :=
      hlusin _ (MeasureTheory.ae_iff.mp hdiff)
    -- (ii) The total-collapse set has null image by the easy half of the area formula
    -- (null regardless of its own measure).
    have h2 : volume (f '' {z : ℂ | DifferentiableAt ℝ f z ∧ fderiv ℝ f z = 0}) = 0 := by
      refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
        (f' := fun x => fderiv ℝ f x) ?_ ?_
      · intro x hx; exact hx.1.hasFDerivAt.hasFDerivWithinAt
      · intro x hx; change (fderiv ℝ f x).det = 0; rw [hx.2, ContinuousLinearMap.det]; simp
    -- (iii) The degenerate-nonzero set is a.e. empty by the or-zero Wirtinger bracket.
    have h3ae : ∀ᵐ z : ℂ, ¬ (DifferentiableAt ℝ f z ∧ fderiv ℝ f z ≠ 0
        ∧ ¬ 0 < (fderiv ℝ f z).det) := by
      filter_upwards [hf.wirtinger_bracket_or_zero] with z hor
      rintro ⟨hzd, hne, hnpos⟩
      rcases hor hzd with hzero | ⟨hqp, -⟩
      · exact hne hzero
      · apply hnpos
        rw [det_fderiv_eq_wirtinger]
        nlinarith [hqp, norm_nonneg (dzbar f z), norm_nonneg (dz f z)]
    have h3null : volume {z : ℂ | DifferentiableAt ℝ f z ∧ fderiv ℝ f z ≠ 0
        ∧ ¬ 0 < (fderiv ℝ f z).det} = 0 := by
      have := MeasureTheory.ae_iff.mp h3ae
      simpa only [not_not] using this
    have h3 : volume (f '' {z : ℂ | DifferentiableAt ℝ f z ∧ fderiv ℝ f z ≠ 0
        ∧ ¬ 0 < (fderiv ℝ f z).det}) = 0 := hlusin _ h3null
    have himg : f '' B ⊆ f '' {z : ℂ | ¬ DifferentiableAt ℝ f z}
        ∪ (f '' {z : ℂ | DifferentiableAt ℝ f z ∧ fderiv ℝ f z = 0}
          ∪ f '' {z : ℂ | DifferentiableAt ℝ f z ∧ fderiv ℝ f z ≠ 0
              ∧ ¬ 0 < (fderiv ℝ f z).det}) := by
      rw [← Set.image_union, ← Set.image_union]
      exact Set.image_mono hsplit
    exact measure_mono_null himg
      (measure_union_null h1 (measure_union_null h2 h3))
  -- The good set: a.e. `w`, the forward map is differentiable at `g w` with `J_f > 0`.
  have hgood : ∀ᵐ w : ℂ, DifferentiableAt ℝ f (g w) ∧ 0 < (fderiv ℝ f (g w)).det := by
    rw [MeasureTheory.ae_iff]
    have hset : {w : ℂ | ¬ (DifferentiableAt ℝ f (g w) ∧ 0 < (fderiv ℝ f (g w)).det)}
        = {w : ℂ | g w ∈ B} := rfl
    rw [hset, htrans B]
    exact hfB
  -- Pull back a.e. source-side statements through `g` (forward Lusin condition).
  have pullback : ∀ P : ℂ → Prop, (∀ᵐ z : ℂ, P z) → ∀ᵐ w : ℂ, P (g w) := by
    intro P hP
    have himgnull : volume (f '' {z : ℂ | ¬ P z}) = 0 :=
      hlusin _ (MeasureTheory.ae_iff.mp hP)
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ himgnull
    intro w hw
    exact ⟨g w, hw, hfg w⟩
  have hdilw : ∀ᵐ w : ℂ, DifferentiableAt ℝ f (g w) →
      0 ≤ (fderiv ℝ f (g w)).det
        ∧ ‖fderiv ℝ f (g w)‖ ^ 2 ≤ K * (fderiv ℝ f (g w)).det :=
    pullback _ hf.dilatation_le_or_zero
  -- The easy inverse function theorem at each good point.
  have hmain : ∀ᵐ w : ℂ, DifferentiableAt ℝ g w ∧
      fderiv ℝ g w = ContinuousLinearMap.inverse (fderiv ℝ f (g w)) := by
    filter_upwards [hgood] with w hw
    obtain ⟨hdiffw, hdetpos⟩ := hw
    set f' : ℂ →L[ℝ] ℂ := fderiv ℝ f (g w) with hf'
    have hdetne : f'.det ≠ 0 := ne_of_gt hdetpos
    set e : ℂ ≃L[ℝ] ℂ := f'.toContinuousLinearEquivOfDetNeZero hdetne with he
    have hecoe : (e : ℂ →L[ℝ] ℂ) = f' :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero f' hdetne
    have hfderiv : HasFDerivAt f (e : ℂ →L[ℝ] ℂ) (g w) := by
      rw [hecoe]; exact hdiffw.hasFDerivAt
    have hloc : ∀ᶠ y in nhds w, f (g y) = y := Filter.Eventually.of_forall hfg
    have hgfderiv : HasFDerivAt g (e.symm : ℂ →L[ℝ] ℂ) w :=
      HasFDerivAt.of_local_left_inverse hgcont.continuousAt hfderiv hloc
    refine ⟨hgfderiv.differentiableAt, ?_⟩
    rw [hgfderiv.fderiv, ← hecoe, ContinuousLinearMap.inverse_equiv e]
  -- Jacobian positivity and the dilatation bound for `g`, via `inverse_dilatation` (N6a).
  have hlast : ∀ᵐ w : ℂ,
      0 < (fderiv ℝ g w).det ∧ ‖fderiv ℝ g w‖ ^ 2 ≤ K * (fderiv ℝ g w).det := by
    filter_upwards [hgood, hdilw, hmain] with w hw hdil hm
    obtain ⟨hdiffw, hdetpos⟩ := hw
    have hbound := (hdil hdiffw).2
    rw [hm.2]
    exact ContinuousLinearMap.inverse_dilatation hdetpos hbound
  exact ⟨hgood,
    (by filter_upwards [hmain] with w hw using hw.1),
    (by filter_upwards [hmain] with w hw using hw.2),
    (by filter_upwards [hlast] with w hw using hw.1),
    (by filter_upwards [hlast] with w hw using hw.2)⟩

/-! ## N8 — ACL slices of the inverse (proved glue: the parametrized chain at N3) -/

/-- **ACL slices of the inverse with `L²_loc` energy.** Any two-sided inverse `g` of a
geometric `K`-quasiconformal map is absolutely continuous on almost every horizontal and
vertical line, with locally square-integrable slice partials. Pure instantiation of the
parametrized forward ACL chain (`AxisRectModulusBound.exists_acl_memLp_sliceGradient`)
at the keystone axis-rectangle bounds for `g`
(`IsQCGeometric.inverse_axisRectModulusBound`).
-/
theorem IsQCGeometric.inverse_exists_acl_memLp_sliceGradient {f g : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (hfg : ∀ w, f (g w) = w) (hgf : ∀ z, g (f z) = z) :
    ∃ gx gy : ℂ → ℂ, ACLHorizontal g gx ∧ ACLVertical g gy ∧
      MemLpLocOn gx (2 : ℝ≥0∞) Set.univ ∧ MemLpLocOn gy (2 : ℝ≥0∞) Set.univ :=
  (hf.inverse_axisRectModulusBound hfg hgf).exists_acl_memLp_sliceGradient

/-! ## N9 — the inverse is a weak `W^{1,2}_loc` Beltrami solution -/

/-- **The inverse solves a weak Beltrami equation in `W^{1,2}_loc`.** For any two-sided
inverse `g` of a geometric `K`-quasiconformal map, the pointwise partials `(Dg·)1`, `(Dg·)I`
form a weak gradient of `g` with locally square-integrable components, and there is a
measurable `μ` with `‖μ‖∞ < 1` satisfying the weak Wirtinger–Beltrami equation
`½(g_x + i·g_y) = μ·½(g_x − i·g_y)` almost everywhere — exactly the input format of
`beltrami_higher_integrability`.

*Proof sketch.* The weak gradient is `hasWeakGradient_of_aeSliceAC`
(`QC/LengthArea/ReverseLengthArea.lean`): continuity of `g` (the inverse of a homeomorphism),
a.e. differentiability from `IsQCGeometric.inverse_pointwise_data`, local integrability of
the partials from their `L²_loc` bounds, and a.e. slice absolute continuity from
`IsQCGeometric.inverse_exists_acl_memLp_sliceGradient` (whose `ACLHorizontal`/`ACLVertical`
conjuncts bundle it). The `L²_loc` bounds are `memLpLocOn_inverse_partial_of_dilatation`
(`QC/LengthArea/LengthAreaInverse.lean`) fed by the pointwise data of N6. The coefficient is
the clamped quotient `μ w := if ‖dzbar g w / dz g w‖ ≤ (K−1)/(K+1) then … else 0`
(measurable, `‖μ‖∞ ≤ (K−1)/(K+1) < 1`), and the pointwise Beltrami equation
`dzbar g = μ·dz g` a.e. follows from the dilatation bound `‖Dg‖² ≤ K·J_g` with `J_g > 0`
(N6) by the reverse dilatation algebra of `IsQCGeometric.exists_beltrami`
(`QC/GeometricToAnalytic/Assembly.lean`, STEP 8); since `dz g`/`dzbar g` are by definition
the Wirtinger combinations of the pointwise partials, the weak form is definitional.
-/
theorem IsQCGeometric.inverse_weakGradient_beltrami {f g : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (hfg : ∀ w, f (g w) = w) (hgf : ∀ z, g (f z) = z) :
    ∃ μ : ℂ → ℂ, Measurable μ ∧ eLpNormEssSup μ volume < 1 ∧
      HasWeakGradient (fun w => (fderiv ℝ g w) 1) (fun w => (fderiv ℝ g w) Complex.I) g
        Set.univ ∧
      MemLpLocOn (fun w => (fderiv ℝ g w) 1) (2 : ℝ≥0∞) Set.univ ∧
      MemLpLocOn (fun w => (fderiv ℝ g w) Complex.I) (2 : ℝ≥0∞) Set.univ ∧
      (∀ᵐ w : ℂ, (1 / 2 : ℂ) * ((fderiv ℝ g w) 1 + Complex.I * (fderiv ℝ g w) Complex.I)
          = μ w * ((1 / 2 : ℂ)
            * ((fderiv ℝ g w) 1 - Complex.I * (fderiv ℝ g w) Complex.I))) := by
  classical
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  -- `g` is a homeomorphism (the two-sided inverse of the homeomorphism `f`).
  have hgeq : g = ⇑(hf.2.1.isHomeomorph.homeomorph f).symm := by
    funext w
    apply hf.2.1.isHomeomorph.injective
    rw [hfg w]
    exact ((hf.2.1.isHomeomorph.homeomorph f).apply_symm_apply w).symm
  have hghomeo : IsHomeomorph g := by
    rw [hgeq]; exact (hf.2.1.isHomeomorph.homeomorph f).symm.isHomeomorph
  have hgcont : Continuous g := hghomeo.continuous
  -- The pointwise inverse data (N6).
  obtain ⟨-, hgdiff, -, hgdetpos, hgdil⟩ := hf.inverse_pointwise_data hfg hgf
  -- The `L²_loc` partials of `g`, from the inverse dilatation bound.
  have hgx2 : MemLpLocOn (fun w => (fderiv ℝ g w) 1) (2 : ℝ≥0∞) Set.univ :=
    memLpLocOn_inverse_partial_of_dilatation hKpos hghomeo hgdiff hgdetpos hgdil 1
  have hgy2 : MemLpLocOn (fun w => (fderiv ℝ g w) Complex.I) (2 : ℝ≥0∞) Set.univ :=
    memLpLocOn_inverse_partial_of_dilatation hKpos hghomeo hgdiff hgdetpos hgdil Complex.I
  -- A.e. slice absolute continuity from the keystone-fed ACL chain (N8).
  obtain ⟨gx0, gy0, haclx, hacly, -, -⟩ := hf.inverse_exists_acl_memLp_sliceGradient hfg hgf
  have hacx : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => g ⟨x, y⟩) a b := by
    filter_upwards [haclx] with y hy using hy.1
  have hacy : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => g ⟨x, y⟩) a b := by
    filter_upwards [hacly] with x hx using hx.1
  -- `L²_loc ⟹ L¹_loc` on compacts.
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict Kc) := hh Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  -- The weak gradient of `g` is the pair of pointwise partials.
  have hwg : HasWeakGradient (fun w => (fderiv ℝ g w) 1)
      (fun w => (fderiv ℝ g w) Complex.I) g Set.univ :=
    hasWeakGradient_of_aeSliceAC hgcont hgdiff (hLIofL2 hgx2) (hLIofL2 hgy2) hacx hacy
  -- The clamped Beltrami coefficient for `g`.
  have hK1 : (0 : ℝ) < K + 1 := by linarith [hf.1]
  set c : ℝ := (K - 1) / (K + 1) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; apply div_nonneg <;> linarith [hf.1]
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hK1]; linarith
  set raw : ℂ → ℂ := fun w => dzbar g w / dz g w with hraw
  set μ : ℂ → ℂ := fun w => if ‖raw w‖ ≤ c then raw w else 0 with hμ
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
  have hμ_meas : Measurable μ :=
    Measurable.ite (measurableSet_le hraw_meas.norm measurable_const) hraw_meas measurable_const
  have hμ_le : ∀ w, ‖μ w‖ ≤ c := by
    intro w
    rw [hμ]
    by_cases h : ‖raw w‖ ≤ c
    · simp [h]
    · simp [h, hc0]
  have hμ_bound : eLpNormEssSup μ volume < 1 := by
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hμ_le)) ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mpr hc1
  -- The pointwise Beltrami equation for `g` (reverse dilatation algebra at `J_g > 0`).
  have hbel0 : ∀ᵐ w : ℂ, dzbar g w = μ w * dz g w := by
    filter_upwards [hgdetpos, hgdil] with w hdz hdl
    set p : ℝ := ‖dz g w‖ with hpdef
    set q : ℝ := ‖dzbar g w‖ with hqdef
    have hp0 : 0 ≤ p := norm_nonneg _
    have hq0 : 0 ≤ q := norm_nonneg _
    have hdet : (fderiv ℝ g w).det = p ^ 2 - q ^ 2 := det_fderiv_eq_wirtinger g w
    have hop : ‖fderiv ℝ g w‖ = p + q := opNorm_fderiv_eq_wirtinger g w
    rw [hdet] at hdz
    have hqltp : q < p := by nlinarith [hp0, hq0]
    have hppos : 0 < p := lt_of_le_of_lt hq0 hqltp
    have hpqpos : 0 < p + q := by linarith
    have hdzne : dz g w ≠ 0 := by rw [← norm_pos_iff]; exact hppos
    rw [hop, hdet] at hdl
    have hqcp : q ≤ c * p := by
      have hstep : (K + 1) * q ≤ (K - 1) * p := by nlinarith [hpqpos, hdl]
      rw [hc, div_mul_eq_mul_div, le_div_iff₀ hK1]
      nlinarith [hstep]
    have hraww : ‖raw w‖ ≤ c := by
      have hrawval : raw w = dzbar g w / dz g w := by rw [hraw]
      rw [hrawval, norm_div, ← hpdef, ← hqdef, div_le_iff₀ hppos]
      exact hqcp
    have hμw : μ w = dzbar g w / dz g w := by
      rw [hμ]; simp only [hraww, if_true]; rw [hraw]
    rw [hμw, div_mul_cancel₀ (dzbar g w) hdzne]
  exact ⟨μ, hμ_meas, hμ_bound, hwg, hgx2, hgy2, hbel0⟩

/-! ## N10 — Bojarski higher integrability at the inverse -/

/-- **Bojarski higher integrability for the inverse.** Any two-sided inverse `g` of a
geometric `K`-quasiconformal map has a weak gradient with components locally `Lᵖ` for some
`p > 2`.

*Proof sketch.* Feed the weak Beltrami package of
`IsQCGeometric.inverse_weakGradient_beltrami` to `beltrami_higher_integrability`
(`QC/InverseQC/LusinN.lean`; `MemLpLocOn g 2` from continuity of `g` on compacts), then
decompose the super-critical weak `∂`-derivative into both partials via
`g_x = ∂g + ∂̄g`, `g_y = i(∂g − ∂̄g)` and `‖∂̄g‖ ≤ ‖μ‖∞·‖∂g‖`, exactly as in
`IsQCAnalytic.exists_weakGradient_memLpLocOn_gt_two` (`QC/InverseQC/LusinN.lean`).
-/
theorem IsQCGeometric.inverse_exists_weakGradient_memLpLocOn_gt_two {f g : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (hfg : ∀ w, f (g w) = w) (hgf : ∀ z, g (f z) = z) :
    ∃ (p : ℝ) (gx gy : ℂ → ℂ), 2 < p ∧ HasWeakGradient gx gy g Set.univ ∧
      MemLpLocOn gx (ENNReal.ofReal p) Set.univ ∧
      MemLpLocOn gy (ENNReal.ofReal p) Set.univ := by
  classical
  -- The weak Beltrami package of the inverse (N9).
  obtain ⟨μ, hμ_meas, hμ_bound, hwg, hgx2, hgy2, hbel⟩ :=
    hf.inverse_weakGradient_beltrami hfg hgf
  -- `g` is continuous (the two-sided inverse of the homeomorphism `f`).
  have hgeq : g = ⇑(hf.2.1.isHomeomorph.homeomorph f).symm := by
    funext w
    apply hf.2.1.isHomeomorph.injective
    rw [hfg w]
    exact ((hf.2.1.isHomeomorph.homeomorph f).apply_symm_apply w).symm
  have hgcont : Continuous g := by
    rw [hgeq]; exact (hf.2.1.isHomeomorph.homeomorph f).continuous_symm
  -- `g ∈ L²_loc` from continuity on compacts.
  have hgL2 : MemLpLocOn g (2 : ℝ≥0∞) Set.univ := by
    intro Kc _ hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hgcont.continuousOn
    have hbound : ∀ᵐ x ∂(volume.restrict Kc), ‖g x‖ ≤ C := by
      rw [ae_restrict_iff' hKc.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hgcont.aestronglyMeasurable C hbound).mono_exponent le_top
  -- Bojarski higher integrability at `g`.
  obtain ⟨p, hp2, hdzp'⟩ :=
    beltrami_higher_integrability hμ_meas hμ_bound hgcont hgL2 hwg.1 hwg.2 hgx2 hgy2 hbel
  have hdzp : MemLpLocOn (fun w => dz g w) (ENNReal.ofReal p) Set.univ := hdzp'
  -- The a.e. bound `‖μ‖ ≤ 1` from the essential-sup bound.
  have hμle : ∀ᵐ w : ℂ, ‖μ w‖ ≤ 1 := by
    filter_upwards [ae_le_eLpNormEssSup (f := μ) (μ := volume)] with w hw
    have h1 : ENNReal.ofReal ‖μ w‖ ≤ 1 := by
      rw [ofReal_norm]; exact le_trans hw hμ_bound.le
    exact ENNReal.ofReal_le_one.mp h1
  -- `∂̄g ∈ Lᵖ_loc` via `dzbar g =ᵐ μ · dz g`.
  have hdzbarp : MemLpLocOn (fun w => dzbar g w) (ENNReal.ofReal p) Set.univ := by
    intro Kc hKu hKc
    have hdzK : MemLp (fun w => dz g w) (ENNReal.ofReal p) (volume.restrict Kc) :=
      hdzp Kc hKu hKc
    have hmeasK : AEStronglyMeasurable (fun w => μ w * dz g w) (volume.restrict Kc) :=
      (hμ_meas.aestronglyMeasurable).mul hdzK.1
    have hboundK : MemLp (fun w => μ w * dz g w) (ENNReal.ofReal p) (volume.restrict Kc) := by
      refine hdzK.of_le hmeasK ?_
      filter_upwards [ae_restrict_of_ae hμle] with w hw
      rw [norm_mul]
      calc ‖μ w‖ * ‖dz g w‖ ≤ 1 * ‖dz g w‖ :=
            mul_le_mul_of_nonneg_right hw (norm_nonneg _)
        _ = ‖dz g w‖ := one_mul _
    refine hboundK.ae_eq ?_
    filter_upwards [ae_restrict_of_ae hbel] with w hw
    exact hw.symm
  -- Decompose into both partials via the pointwise Wirtinger identities.
  have hgx_eq : (fun w => (fderiv ℝ g w) 1) = fun w => dz g w + dzbar g w := by
    funext w; rw [dz, dzbar]; ring
  have hgy_eq : (fun w => (fderiv ℝ g w) Complex.I)
      = fun w => Complex.I * (dz g w - dzbar g w) := by
    funext w; rw [dz, dzbar]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((fderiv ℝ g w) Complex.I) * hI
  refine ⟨p, (fun w => (fderiv ℝ g w) 1), (fun w => (fderiv ℝ g w) Complex.I), hp2, hwg,
    ?_, ?_⟩
  · rw [hgx_eq]
    intro Kc hKu hKc
    exact (hdzp Kc hKu hKc).add (hdzbarp Kc hKu hKc)
  · rw [hgy_eq]
    intro Kc hKu hKc
    exact ((hdzp Kc hKu hKc).sub (hdzbarp Kc hKu hKc)).const_mul Complex.I

/-! ## N11 — the target: the inverse Lusin condition (N⁻¹) -/

/-- **Inverse Lusin condition (`N⁻¹`) of a geometric quasiconformal map.** The inverse `f⁻¹`
of a geometric `K`-quasiconformal homeomorphism maps Lebesgue-null sets to Lebesgue-null
sets. This is condition (N) for the inverse map, and the genuine remaining content of the
a.e. nondegeneracy `J_f > 0` (the area-formula half is proved against it in
`ae_fderiv_ne_zero` below).

*Proof plan (a composition of the stated nodes above).* The inverse
`g = ⇑(hf.2.1.isHomeomorph.homeomorph f).symm` satisfies the two-sided inverse identities
definitionally (`Homeomorph.apply_symm_apply`, `Homeomorph.symm_apply_apply`), is continuous
(`Homeomorph.continuous_symm`), and by
`IsQCGeometric.inverse_exists_weakGradient_memLpLocOn_gt_two` (N10 — through the keystone
axis-rectangle bounds N3, the parametrized ACL chain N8, the pointwise inverse data N6, and
Bojarski at `g`) lies in `W^{1,p}_loc` for some `p > 2`. The planar Marcus–Mizel theorem
`lusinN_image_null_of_weakGradient` (`Analysis/Sobolev/Morrey/LusinN.lean`) then yields
condition (N) for `g`, which is the stated conclusion.
-/
theorem IsQCGeometric.inverse_lusinN {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ A : Set ℂ, volume A = 0 →
      volume (⇑(hf.2.1.isHomeomorph.homeomorph f).symm '' A) = 0 := by
  intro A hA
  set g : ℂ → ℂ := ⇑(hf.2.1.isHomeomorph.homeomorph f).symm with hg
  -- The two-sided inverse identities (definitional for the homeomorphism package).
  have hfg : ∀ w, f (g w) = w := fun w =>
    (hf.2.1.isHomeomorph.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z =>
    (hf.2.1.isHomeomorph.homeomorph f).symm_apply_apply z
  -- Bojarski at `g` (through the keystone N3, the ACL chain N8, and the inverse data N6).
  obtain ⟨p, gx, gy, hp2, hwg, hgxp, hgyp⟩ :=
    hf.inverse_exists_weakGradient_memLpLocOn_gt_two hfg hgf
  have hgcont : Continuous g := (hf.2.1.isHomeomorph.homeomorph f).continuous_symm
  -- The planar Marcus–Mizel theorem at `g`.
  exact lusinN_image_null_of_weakGradient hp2 hgcont hwg hgxp hgyp hA

/-! ## The nondegeneracy assembly (re-homed from `InfinitesimalModulus.lean`) -/

/-- **A.e. nondegeneracy of the differential (`J_f > 0` almost everywhere).** For a geometric
`K`-quasiconformal map `f`, at almost every point of differentiability the differential `L = Df x`
is nonzero. Combined with the worst-orientation Rengel bound (which excludes the rank-one
degeneration `q = p > 0`), this yields `det L > 0` almost everywhere.

WARNING — the *pointwise* exclusion of `L = 0` is **mathematically false**. A `K`-quasiconformal
homeomorphism may be differentiable at an individual point with vanishing differential: the radial
stretch `f (z) = z · |z|` is a sense-preserving `2`-quasiconformal homeomorphism — in polar form it
is `(r, θ) ↦ (r², θ)`, whose principal stretches `2r` (radial) and `r` (tangential) give the
constant dilatation `2` — yet it is real-differentiable at `0` with `fderiv ℝ f 0 = 0`, because
`‖f z − f 0‖ / ‖z − 0‖ = |z| → 0`. Thus `f` and `x = 0` satisfy `IsQCGeometric f 2`,
`DifferentiableAt ℝ f 0`, and `fderiv ℝ f 0 = 0` with **no** contradiction available: the
zero-differential set is the single null point `{0}`. Nondegeneracy therefore can only hold almost
everywhere, exactly as stated here.

This is the classical `J_f > 0` a.e. theorem for quasiconformal homeomorphisms.
The proof here is **complete modulo the inverse Lusin
residual** `IsQCGeometric.inverse_lusinN`: the easy `≤` half of the area formula
(`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) shows the zero-Jacobian set
`E = {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0}` has null image `f '' E` (the determinant
`(fderiv ℝ f).det` vanishes on `E`); the inverse Lusin condition `(N⁻¹)` then pulls this back,
`E = f⁻¹ '' (f '' E)`, to `volume E = 0`, which is exactly the complement of the a.e. statement. It
is consumed by `wirtinger_bracket_of_blowup` to discharge the total-collapse case `p = q = 0`. -/
theorem IsQCGeometric.ae_fderiv_ne_zero {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x → fderiv ℝ f x ≠ 0 := by
  classical
  set g : ℂ → ℂ := ⇑(hf.2.1.isHomeomorph.homeomorph f).symm with hg
  set E : Set ℂ := {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0} with hE
  -- (a) The zero-Jacobian set has null image (easy `≤` half of the area formula).
  have hfE : volume (f '' E) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ f x) ?_ ?_
    · intro x hx; exact hx.1.hasFDerivAt.hasFDerivWithinAt
    · intro x hx; change (fderiv ℝ f x).det = 0; rw [hx.2, ContinuousLinearMap.det]; simp
  -- (b) Pull back through the inverse Lusin condition `N⁻¹`.
  have hgfE : volume (g '' (f '' E)) = 0 := hf.inverse_lusinN _ hfE
  have hgfx : ∀ x : ℂ, g (f x) = x := by
    intro x
    have hfx : (hf.2.1.isHomeomorph.homeomorph f) x = f x := rfl
    rw [hg, ← hfx, Homeomorph.symm_apply_apply]
  have hgf : g '' (f '' E) = E := by
    rw [Set.image_image]; simp only [hgfx, Set.image_id']
  rw [hgf] at hgfE
  -- `volume E = 0` is the complement of the a.e. statement.
  rw [MeasureTheory.ae_iff]
  have hset : {x : ℂ | ¬ (DifferentiableAt ℝ f x → fderiv ℝ f x ≠ 0)} = E := by
    ext x; simp only [hE, Set.mem_ofPred_eq, Classical.not_imp, not_not]
  rw [hset]; exact hgfE

/-- **Worst-orientation Wirtinger bracket from the modulus blow-up.** At almost every point of
differentiability, the Wirtinger data `p = ‖∂f x‖`, `q = ‖∂̄f x‖` of a geometric `K`-quasiconformal
map satisfies the worst-orientation linear-dilatation bracket

  `q < p`    and    `(p + q) ≤ K·(p − q)`,

equivalently `det L = p² − q² > 0` (nondegeneracy) and `‖L‖²/det L = (p+q)/(p−q) ≤ K` (sharp
dilatation), where `L = Df x`. The cycle-free or-zero form
`IsQCGeometric.wirtinger_bracket_or_zero` (`InfinitesimalModulus.lean`) supplies the dichotomy;
the total-collapse branch `Df x = 0` is discharged by the a.e. nondegeneracy
`IsQCGeometric.ae_fderiv_ne_zero`. -/
theorem IsQCGeometric.wirtinger_bracket_of_blowup {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x →
      ‖dzbar f x‖ < ‖dz f x‖ ∧
        ‖dz f x‖ + ‖dzbar f x‖ ≤ K * (‖dz f x‖ - ‖dzbar f x‖) := by
  filter_upwards [hf.wirtinger_bracket_or_zero, hf.ae_fderiv_ne_zero] with x hor hne hxd
  rcases hor hxd with hzero | hbracket
  · exact absurd hzero (hne hxd)
  · exact hbracket

/-- **Infinitesimal modulus distortion (sharp pointwise dilatation bound).** For a geometric
`K`-quasiconformal map `f`, at almost every point of differentiability the differential `L = Df x`
is nondegenerate and has linear dilatation at most `K`:
`det L ≠ 0` and `‖L‖² ≤ K · det L`. This is the infinitesimal modulus blow-up argument; it is the
operator-norm residual consumed by `IsQCGeometric.reverseLengthArea_data`. -/
theorem IsQCGeometric.infinitesimal_dilatation {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x →
      (fderiv ℝ f x).det ≠ 0 ∧ ‖fderiv ℝ f x‖ ^ 2 ≤ K * (fderiv ℝ f x).det := by
  filter_upwards [hf.wirtinger_bracket_of_blowup] with x hx hxdiff
  obtain ⟨hqp, hbracket⟩ := hx hxdiff
  exact infinitesimal_dilatation_of_wirtinger_bracket hqp hbracket

end NoWanderingDomains
