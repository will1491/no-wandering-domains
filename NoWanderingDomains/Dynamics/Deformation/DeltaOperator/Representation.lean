/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Deformation.DeltaOperator.ChainRule

/-!
# The deformation field in the section space, and Julia-set vanishing

Invariance of `μ = ∂̄v` kills the weak `∂̄` of the deformation field, so `δv`
is holomorphic off the poles; pole and infinity analysis places it in the
section space. A vanishing deformation field forces the vector field to vanish
at every finite point of the Julia set, through repelling cycles and their
density.

* `differentiableOn_deltaField`, `deltaField_pole_bound`,
  `deltaField_growth_at_infty`, `exists_sectionSpace_rep_of_pole_growth`,
  `exists_sectionSpace_rep_deltaField` — the section-space representative.
* `deltaField_zero_iterate`,
  `sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero` — Julia vanishing.
-/

open MeasureTheory Complex Metric Filter Topology Polynomial OnePoint

namespace NoWanderingDomains

/-! ## Invariance places the deformation field in the section space -/

/-- **Holomorphy of the deformation field off the poles.** If `v` is a sphere
vector field with weak `∂̄`-derivative `μ` and `μ` is `f`-invariant, then
`δv` is holomorphic on the complement of the pole set: its weak `∂̄` is
`f′·μ − (μ∘f)·conj(f′)`, which vanishes a.e. by the invariance law, and the
open-set Weyl lemma upgrades this to holomorphy. -/
theorem differentiableOn_deltaField {r : RationalData} (_hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ) :
    DifferentiableOn ℂ (deltaField r v)
      {z : ℂ | r.denReduced.eval z ≠ 0} := by
  -- The non-pole set is open (preimage of `{0}ᶜ` under the polynomial evaluation).
  have hΩ : IsOpen {z : ℂ | r.denReduced.eval z ≠ 0} :=
    isOpen_compl_singleton.preimage r.denReduced.continuous
  have hvcont : Continuous v := hv.1
  -- The finite-chart reading of the map is holomorphic off the poles: near a
  -- non-pole it agrees with the rational function `numReduced/denReduced`.
  have hφdiff : DifferentiableOn ℂ
      (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
      {z : ℂ | r.denReduced.eval z ≠ 0} := by
    intro w hw
    have hw' : r.denReduced.eval w ≠ 0 := hw
    have hev : (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
        =ᶠ[𝓝 w] fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x := by
      filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hw'] with x hx
      have hread : r.toSphereMap ↑x
          = if r.denReduced.eval x = 0 then (∞ : ℂ̂)
            else ((r.numReduced.eval x / r.denReduced.eval x : ℂ) : ℂ̂) := rfl
      rw [hread, if_neg hx]
      rfl
    have hdiv : DifferentiableAt ℂ
        (fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x) w :=
      ((r.numReduced.hasDerivAt w).div (r.denReduced.hasDerivAt w) hw').differentiableAt
    exact (hdiv.congr_of_eventuallyEq hev).differentiableWithinAt
  have hφcont : ContinuousOn
      (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
      {z : ℂ | r.denReduced.eval z ≠ 0} := hφdiff.continuousOn
  -- The finite-chart derivative is holomorphic off the poles (rational function
  -- with nonvanishing denominator).
  have hFdiff : DifferentiableOn ℂ (fderivRational r)
      {z : ℂ | r.denReduced.eval z ≠ 0} := by
    intro z hz
    have hz' : r.denReduced.eval z ≠ 0 := hz
    have hat : DifferentiableAt ℂ
        (fun z : ℂ => r.wronskian.eval z / (r.denReduced.eval z) ^ 2) z :=
      (r.wronskian.differentiableAt).div ((r.denReduced.differentiableAt).pow 2)
        (pow_ne_zero 2 hz')
    exact hat.differentiableWithinAt
  -- `L²_loc` on the non-pole set implies `L¹_loc` there.
  have hL2toLI : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 {z : ℂ | r.denReduced.eval z ≠ 0} →
      LocallyIntegrableOn g {z : ℂ | r.denReduced.eval z ≠ 0} := by
    intro g hg
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro K hK hKc
    have hmem : MemLp g 2 (volume.restrict K) := hg K hK hKc
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  -- Restrict the global weak-`∂̄` data of `v` to the non-pole set.
  have hgradΩ : HasL2WeakDzbar v μ {z : ℂ | r.denReduced.eval z ≠ 0} := by
    obtain ⟨gx, gy, hwg, hgx2, hgy2, hcomb⟩ := hgrad
    refine ⟨gx, gy, ⟨hwg.1.mono (Set.subset_univ _), hwg.2.mono (Set.subset_univ _)⟩,
      hgx2.mono (Set.subset_univ _), hgy2.mono (Set.subset_univ _), ?_⟩
    filter_upwards [hcomb] with z hz _
    exact hz (Set.mem_univ z)
  have hvloc : LocallyIntegrableOn v {z : ℂ | r.denReduced.eval z ≠ 0} :=
    hvcont.locallyIntegrable.locallyIntegrableOn _
  -- Weak `∂̄` of the product term `f′·v` is `f′·μ`.
  obtain ⟨gx1, gy1, hwg1, hgx1L2, hgy1L2, hcomb1⟩ :=
    hasL2WeakDzbar_holomorphic_mul hΩ hFdiff hvloc hgradΩ
  -- Weak `∂̄` of the composed term `v∘f` is `(μ∘f)·conj(f′)`.
  obtain ⟨gx2, gy2, hwg2, hgx2L2, hgy2L2, hcomb2⟩ :=
    hasL2WeakDzbar_comp_holomorphic hΩ hφdiff hvcont hgrad
  -- Local integrability of the two terms and the four weak-gradient witnesses.
  have hf1loc : LocallyIntegrableOn (fun z : ℂ => fderivRational r z * v z)
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    (hFdiff.continuousOn.mul hvcont.continuousOn).locallyIntegrableOn hΩ.measurableSet
  have hf2loc : LocallyIntegrableOn
      (fun z : ℂ => v (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))))
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    (hvcont.comp_continuousOn hφcont).locallyIntegrableOn hΩ.measurableSet
  have hgx1LI := hL2toLI hgx1L2
  have hgy1LI := hL2toLI hgy1L2
  have hgx2LI := hL2toLI hgx2L2
  have hgy2LI := hL2toLI hgy2L2
  -- Weak gradient of the difference `δv = f′·v − v∘f`.
  have hsubx : HasWeakDirDeriv 1 (fun z => gx1 z - gx2 z) (deltaField r v)
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    hwg1.1.sub hwg2.1 hf1loc hf2loc hgx1LI hgx2LI
  have hsuby : HasWeakDirDeriv Complex.I (fun z => gy1 z - gy2 z) (deltaField r v)
      {z : ℂ | r.denReduced.eval z ≠ 0} :=
    hwg1.2.sub hwg2.2 hf1loc hf2loc hgy1LI hgy2LI
  -- The Wirtinger combination of the difference vanishes a.e. on the non-pole
  -- set: it equals `2(f′·μ − (μ∘f)·conj(f′))`, killed by the invariance law.
  have hinv' : ∀ᵐ z ∂(volume : Measure ℂ),
      μ z * fderivRational r z
        = μ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
            * starRingEnd ℂ (fderivRational r z) := hinv
  have hcomb0 : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ {z : ℂ | r.denReduced.eval z ≠ 0} →
      (gx1 z - gx2 z) + Complex.I * (gy1 z - gy2 z) = 0 := by
    filter_upwards [hcomb1, hcomb2, hinv'] with z h1 h2 h3 hz
    have hz' : r.denReduced.eval z ≠ 0 := hz
    have e1 : gx1 z + Complex.I * gy1 z = 2 * (fderivRational r z * μ z) := h1 hz
    have e2 : gx2 z + Complex.I * gy2 z
        = 2 * (μ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
            * starRingEnd ℂ
              (deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) z)) := h2 hz
    rw [← fderivRational_eq_deriv_reading r hz'] at e2
    have hsplit : (gx1 z - gx2 z) + Complex.I * (gy1 z - gy2 z)
        = (gx1 z + Complex.I * gy1 z) - (gx2 z + Complex.I * gy2 z) := by ring
    rw [hsplit, e1, e2]
    linear_combination 2 * h3
  -- Continuity of `δv` on the non-pole set.
  have hδcont : ContinuousOn (deltaField r v) {z : ℂ | r.denReduced.eval z ≠ 0} := by
    have h1 : ContinuousOn (fun z : ℂ => fderivRational r z * v z)
        {z : ℂ | r.denReduced.eval z ≠ 0} :=
      hFdiff.continuousOn.mul hvcont.continuousOn
    have h2 : ContinuousOn
        (fun z : ℂ => v (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))))
        {z : ℂ | r.denReduced.eval z ≠ 0} :=
      hvcont.comp_continuousOn hφcont
    exact h1.sub h2
  -- Weyl's lemma on the open non-pole set.
  exact weyl_lemma_on hΩ hδcont ⟨hsubx, hsuby⟩ (hgx1LI.sub hgx2LI) (hgy1LI.sub hgy2LI) hcomb0

/-- **Pole-order bound.** At a root `p` of the reduced denominator of
multiplicity `k`, the deformation field has a pole of order at most `2k`:
there is a holomorphic `h` near `p` with `δv = h(z)/(z−p)^{2k}` off `p`.
Route: the transformed reading `−δv/f² = −(f′/f²)·v + u(1/f)` — where `u` is
the continuous infinity-chart reading `w ↦ w²·v(1/w)` of `v` and `f′/f²`,
`1/f` are holomorphic near `p` (coprimality of the reduced fraction) — is
continuous near `p` and weakly holomorphic (invariance transported through
the chain rule, essential boundedness of `μ` controlling the transported
gradient), hence holomorphic by the open-set Weyl lemma; then
`δv = −(that reading)·f²` and `f²` has a pole of order exactly `2k` at `p`. -/
theorem deltaField_pole_bound {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (_hb : eLpNormEssSup μ volume < ⊤)
    {p : ℂ} (hp : r.denReduced.eval p = 0) :
    ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ p ∈ W ∧
      DifferentiableOn ℂ h W ∧
      ∀ z ∈ W, z ≠ p →
        deltaField r v z
          = h z / (z - p) ^ (2 * Polynomial.rootMultiplicity p r.denReduced) := by
  classical
  obtain ⟨hvcont, L, hL⟩ := hv
  -- The reduced denominator is a nonzero polynomial.
  have hQ0 : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  -- Coprimality of the reduced fraction: the numerator does not vanish at `p`.
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  have hNp : r.numReduced.eval p ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hcop
    intro hN0
    have heval := congrArg (Polynomial.eval p) hab
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hN0, hp,
      mul_zero, add_zero] at heval
    exact one_ne_zero heval.symm
  -- Factor out the root: `Q(z) = (z-p)^k · g(z)` with `g(p) ≠ 0`.
  obtain ⟨g, hgp, hfact⟩ : ∃ g : ℂ[X], g.eval p ≠ 0 ∧
      ∀ z : ℂ, r.denReduced.eval z
        = (z - p) ^ (Polynomial.rootMultiplicity p r.denReduced) * g.eval z := by
    refine ⟨r.denReduced /ₘ (Polynomial.X - Polynomial.C p)
        ^ (Polynomial.rootMultiplicity p r.denReduced),
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero p hQ0, fun z => ?_⟩
    conv_lhs => rw [← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq r.denReduced p]
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  set k : ℕ := Polynomial.rootMultiplicity p r.denReduced with hk
  -- The open neighborhood: both `g` and the numerator nonvanishing.
  set W : Set ℂ := {z : ℂ | g.eval z ≠ 0} ∩ {z : ℂ | r.numReduced.eval z ≠ 0} with hWdef
  have hWopen : IsOpen W :=
    (isOpen_compl_singleton.preimage g.continuous).inter
      (isOpen_compl_singleton.preimage r.numReduced.continuous)
  have hpW : p ∈ W := ⟨hgp, hNp⟩
  have hWnhds : W ∈ 𝓝 p := hWopen.mem_nhds hpW
  -- Off `p`, points of `W` are non-poles.
  have hQne : ∀ z ∈ W, z ≠ p → r.denReduced.eval z ≠ 0 := by
    intro z hz hzp
    rw [hfact z]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzp)) hz.1
  -- The finite reading of the map at non-poles.
  have hread : ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
      chartFiniteMap (r.toSphereMap ((z : ℂ̂)))
        = r.numReduced.eval z / r.denReduced.eval z := by
    intro z hz
    have h1 : r.toSphereMap ↑z
        = if r.denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := rfl
    rw [h1, if_neg hz]
    rfl
  have hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
      deltaField r v z = r.wronskian.eval z / (r.denReduced.eval z) ^ 2 * v z
        - v (r.numReduced.eval z / r.denReduced.eval z) := by
    intro z hz
    simp only [deltaField, fderivRational]
    rw [hread z hz]
  -- The limit value at `p` of `(z-p)^{2k} · δv`.
  set Lval : ℂ := r.wronskian.eval p * v p / (g.eval p) ^ 2
      - (r.numReduced.eval p) ^ 2 / (g.eval p) ^ 2 * L with hLval
  -- Eventual identity on the punctured neighborhood.
  have heq : (fun z => (z - p) ^ (2 * k) * deltaField r v z) =ᶠ[𝓝[≠] p]
      (fun z => r.wronskian.eval z * v z / (g.eval z) ^ 2
        - (r.numReduced.eval z) ^ 2 / (g.eval z) ^ 2
          * ((r.denReduced.eval z / r.numReduced.eval z) ^ 2
              * v ((r.denReduced.eval z / r.numReduced.eval z)⁻¹))) := by
    filter_upwards [nhdsWithin_le_nhds hWnhds, self_mem_nhdsWithin] with z hzW hzp
    have hzp' : z ≠ p := hzp
    have hgz : g.eval z ≠ 0 := hzW.1
    have hNz : r.numReduced.eval z ≠ 0 := hzW.2
    have htz : z - p ≠ 0 := sub_ne_zero.mpr hzp'
    have htzk : (z - p) ^ k ≠ 0 := pow_ne_zero _ htz
    have hQz0 : r.denReduced.eval z ≠ 0 := hQne z hzW hzp'
    rw [hδ z hQz0, inv_div, hfact z]
    field_simp
    ring
  -- Convergence of the right-hand side.
  have hcomp : Tendsto (fun z => r.denReduced.eval z / r.numReduced.eval z)
      (𝓝[≠] p) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun z => r.denReduced.eval z / r.numReduced.eval z) p :=
        (r.denReduced.continuous.continuousAt).div
          (r.numReduced.continuous.continuousAt) hNp
      have h0 : r.denReduced.eval p / r.numReduced.eval p = 0 := by
        rw [hp, zero_div]
      rw [← h0]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds hWnhds, self_mem_nhdsWithin] with z hzW hzp
      have hzp' : z ≠ p := hzp
      exact Set.mem_compl_singleton_iff.mpr
        (div_ne_zero (hQne z hzW hzp') hzW.2)
  have hL' : Tendsto (fun z => (r.denReduced.eval z / r.numReduced.eval z) ^ 2
      * v ((r.denReduced.eval z / r.numReduced.eval z)⁻¹)) (𝓝[≠] p) (𝓝 L) :=
    hL.comp hcomp
  have hT1 : Tendsto (fun z => r.wronskian.eval z * v z / (g.eval z) ^ 2)
      (𝓝 p) (𝓝 (r.wronskian.eval p * v p / (g.eval p) ^ 2)) :=
    ((r.wronskian.continuous.continuousAt.mul hvcont.continuousAt).div
      ((g.continuous.continuousAt).pow 2) (pow_ne_zero 2 hgp)).tendsto
  have hT2 : Tendsto (fun z => (r.numReduced.eval z) ^ 2 / (g.eval z) ^ 2)
      (𝓝 p) (𝓝 ((r.numReduced.eval p) ^ 2 / (g.eval p) ^ 2)) :=
    (((r.numReduced.continuous.continuousAt).pow 2).div
      ((g.continuous.continuousAt).pow 2) (pow_ne_zero 2 hgp)).tendsto
  have hlim : Tendsto (fun z => (z - p) ^ (2 * k) * deltaField r v z)
      (𝓝[≠] p) (𝓝 Lval) := by
    have hrhs : Tendsto (fun z => r.wronskian.eval z * v z / (g.eval z) ^ 2
        - (r.numReduced.eval z) ^ 2 / (g.eval z) ^ 2
          * ((r.denReduced.eval z / r.numReduced.eval z) ^ 2
              * v ((r.denReduced.eval z / r.numReduced.eval z)⁻¹)))
        (𝓝[≠] p) (𝓝 Lval) := by
      rw [hLval]
      exact (hT1.mono_left nhdsWithin_le_nhds).sub
        ((hT2.mono_left nhdsWithin_le_nhds).mul hL')
    exact Tendsto.congr' heq.symm hrhs
  -- The candidate holomorphic numerator.
  set H : ℂ → ℂ := Function.update
      (fun z => (z - p) ^ (2 * k) * deltaField r v z) p Lval with hH
  have hHcont : ContinuousAt H p := continuousAt_update_same.mpr hlim
  have hHdiff : DifferentiableOn ℂ H W := by
    rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff hWnhds]
    refine ⟨?_, hHcont⟩
    intro z hz
    have hzW : z ∈ W := hz.1
    have hzp : z ≠ p := hz.2
    have hQz0 : r.denReduced.eval z ≠ 0 := hQne z hzW hzp
    have hδdiff : DifferentiableAt ℂ (deltaField r v) z := by
      have h1 := differentiableOn_deltaField hd ⟨hvcont, L, hL⟩ hgrad hinv
      have h2 : IsOpen {z : ℂ | r.denReduced.eval z ≠ 0} :=
        isOpen_compl_singleton.preimage r.denReduced.continuous
      exact h1.differentiableAt (h2.mem_nhds hQz0)
    have hFdiff : DifferentiableAt ℂ
        (fun x => (x - p) ^ (2 * k) * deltaField r v x) z :=
      ((differentiableAt_id.sub (differentiableAt_const p)).pow _).mul hδdiff
    have hHeq : H =ᶠ[𝓝 z] fun x => (x - p) ^ (2 * k) * deltaField r v x := by
      filter_upwards [isOpen_ne.mem_nhds hzp] with x hx
      rw [hH]
      exact Function.update_of_ne hx _ _
    exact (hFdiff.congr_of_eventuallyEq hHeq).differentiableWithinAt
  refine ⟨W, H, hWopen, hpW, hHdiff, ?_⟩
  intro z hzW hzp
  have hne : (z - p) ^ (2 * k) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzp)
  have hHz : H z = (z - p) ^ (2 * k) * deltaField r v z := by
    rw [hH]
    exact Function.update_of_ne hzp _ _
  rw [hHz, mul_div_cancel_left₀ _ hne]

/-- **Growth bound at infinity.** Multiplied by the squared reduced
denominator, the deformation field grows at most like `|z|^{2d}` near
infinity — the two-chart bookkeeping: `v(z) = O(|z|²)` (sphere field), the
numerator and denominator have degree at most `d`, and the composed term
`v(f z)` is controlled by the infinity-chart reading of `v` when `f z` is
large. This is exactly the numerator-degree bound `natDegree A ≤ 2d` of the
section-space representation. -/
theorem deltaField_growth_at_infty {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (_hgrad : HasL2WeakDzbar v μ Set.univ)
    (_hinv : IsInvariantBeltrami r μ)
    (_hb : eLpNormEssSup μ volume < ⊤) :
    ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      ‖(r.denReduced.eval z) ^ 2 * deltaField r v z‖
        ≤ C * ‖z‖ ^ (2 * r.degree) := by
  classical
  obtain ⟨hvcont, L, hL⟩ := hv
  -- The reduced denominator is a nonzero polynomial.
  have hQ0 : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  -- (1) Uniform quadratic bound for the sphere vector field.
  obtain ⟨B, hB0, hBv⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, ‖v w‖ ≤ B * (1 + ‖w‖ ^ 2) := by
    have h1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖w ^ 2 * v w⁻¹‖ ≤ ‖L‖ + 1 :=
      hL.norm.eventually_le_const (lt_add_one ‖L‖)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp h1
    have houter : ∀ u : ℂ, δ⁻¹ < ‖u‖ → ‖v u‖ ≤ (‖L‖ + 1) * ‖u‖ ^ 2 := by
      intro u hu
      have hu0 : u ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hu
        exact absurd hu (not_lt.mpr (inv_pos.mpr hδpos).le)
      have hw : u⁻¹ ∈ Metric.ball (0 : ℂ) δ ∩ {0}ᶜ := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_inv]
          exact inv_lt_of_inv_lt₀ hδpos hu
        · exact Set.mem_compl_singleton_iff.mpr (inv_ne_zero hu0)
      have hbd : ‖(u⁻¹) ^ 2 * v (u⁻¹)⁻¹‖ ≤ ‖L‖ + 1 := hδ hw
      rw [inv_inv, norm_mul, norm_pow, norm_inv] at hbd
      have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
      have hun' : ‖u‖ ≠ 0 := ne_of_gt hun
      have h3 : ‖v u‖ = ‖u‖ ^ 2 * ((‖u‖⁻¹) ^ 2 * ‖v u‖) := by
        field_simp
      rw [h3]
      calc ‖u‖ ^ 2 * ((‖u‖⁻¹) ^ 2 * ‖v u‖)
          ≤ ‖u‖ ^ 2 * (‖L‖ + 1) := mul_le_mul_of_nonneg_left hbd (sq_nonneg _)
        _ = (‖L‖ + 1) * ‖u‖ ^ 2 := mul_comm _ _
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) δ⁻¹).exists_bound_of_continuousOn
      hvcont.continuousOn
    have hM0 : 0 ≤ M :=
      le_trans (norm_nonneg (v 0)) (hM 0 (Metric.mem_closedBall_self (inv_pos.mpr hδpos).le))
    refine ⟨max M (‖L‖ + 1), le_trans hM0 (le_max_left _ _), fun w => ?_⟩
    have hmax0 : 0 ≤ max M (‖L‖ + 1) := le_trans hM0 (le_max_left _ _)
    by_cases hw : ‖w‖ ≤ δ⁻¹
    · have h1 := hM w (by rwa [Metric.mem_closedBall, dist_zero_right])
      have h2 : (1 : ℝ) ≤ 1 + ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
      calc ‖v w‖ ≤ M := h1
        _ ≤ max M (‖L‖ + 1) := le_max_left _ _
        _ = max M (‖L‖ + 1) * 1 := (mul_one _).symm
        _ ≤ max M (‖L‖ + 1) * (1 + ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hmax0
    · have hw' : δ⁻¹ < ‖w‖ := not_le.mp hw
      calc ‖v w‖ ≤ (‖L‖ + 1) * ‖w‖ ^ 2 := houter w hw'
        _ ≤ max M (‖L‖ + 1) * (1 + ‖w‖ ^ 2) :=
            mul_le_mul (le_max_right _ _) (by nlinarith [sq_nonneg ‖w‖])
              (sq_nonneg _) hmax0
  -- (2) Polynomial evaluations grow at most like the prescribed power.
  have hpolybound : ∀ (P : ℂ[X]) (n : ℕ), P.natDegree ≤ n →
      ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖P.eval z‖ ≤ Cp * ‖z‖ ^ n := by
    intro P n hn
    refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖,
      Finset.sum_nonneg (fun i _ => norm_nonneg _), fun z hz => ?_⟩
    rw [Polynomial.eval_eq_sum_range]
    calc ‖∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i * z ^ i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖z‖ ^ n := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul, norm_pow]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine pow_le_pow_right₀ hz ?_
          have := Finset.mem_range.mp hi
          omega
      _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * ‖z‖ ^ n := by
          rw [← Finset.sum_mul]
  -- (3) Wronskian degree bound: at most `2d - 2`.
  have hWrHelp : ∀ (A E : ℂ[X]) (d : ℕ), A.natDegree + 1 ≤ d → E.natDegree ≤ d →
      (Polynomial.derivative A * E - A * Polynomial.derivative E).natDegree
        ≤ 2 * d - 2 := by
    intro A E d hA hE
    have h1 : (Polynomial.derivative A * E).natDegree ≤ 2 * d - 2 := by
      by_cases h0 : A.natDegree = 0
      · obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
        rw [← ha, Polynomial.derivative_C, zero_mul, Polynomial.natDegree_zero]
        omega
      · have h2 : (Polynomial.derivative A).natDegree < A.natDegree :=
          Polynomial.natDegree_derivative_lt h0
        have h3 := Polynomial.natDegree_mul_le
          (p := Polynomial.derivative A) (q := E)
        omega
    have h2 : (A * Polynomial.derivative E).natDegree ≤ 2 * d - 2 := by
      by_cases h0 : E.natDegree = 0
      · obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
        rw [← ha, Polynomial.derivative_C, mul_zero, Polynomial.natDegree_zero]
        omega
      · have h2 : (Polynomial.derivative E).natDegree < E.natDegree :=
          Polynomial.natDegree_derivative_lt h0
        have h3 := Polynomial.natDegree_mul_le
          (p := A) (q := Polynomial.derivative E)
        omega
    have h3 := Polynomial.natDegree_sub_le
      (Polynomial.derivative A * E) (A * Polynomial.derivative E)
    omega
  have hNd : r.numReduced.natDegree ≤ r.degree := le_max_left _ _
  have hQd : r.denReduced.natDegree ≤ r.degree := le_max_right _ _
  have hWrdeg : r.wronskian.natDegree ≤ 2 * r.degree - 2 := by
    by_cases hcase : r.numReduced.natDegree < r.degree
    · exact hWrHelp r.numReduced r.denReduced r.degree (by omega) hQd
    · by_cases hcase2 : r.denReduced.natDegree < r.degree
      · have h := hWrHelp r.denReduced r.numReduced r.degree (by omega) hNd
        have hneg : r.wronskian
            = -(Polynomial.derivative r.denReduced * r.numReduced
                - r.denReduced * Polynomial.derivative r.numReduced) := by
          unfold RationalData.wronskian
          ring
        rw [hneg, Polynomial.natDegree_neg]
        exact h
      · -- both of full degree: cancel the leading terms
        have hn : r.numReduced.natDegree = r.degree := by omega
        have hq : r.denReduced.natDegree = r.degree := by omega
        have hN0 : r.numReduced ≠ 0 := by
          intro h0
          rw [h0, Polynomial.natDegree_zero] at hn
          omega
        have hlcQ : r.denReduced.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hQ0
        have hlcN : r.numReduced.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hN0
        set c : ℂ := r.numReduced.leadingCoeff / r.denReduced.leadingCoeff with hc
        have hc0 : c ≠ 0 := div_ne_zero hlcN hlcQ
        have hdegeq : r.numReduced.degree = (Polynomial.C c * r.denReduced).degree := by
          rw [Polynomial.degree_C_mul hc0, Polynomial.degree_eq_natDegree hQ0,
            Polynomial.degree_eq_natDegree hN0, hn, hq]
        have hlceq : r.numReduced.leadingCoeff
            = (Polynomial.C c * r.denReduced).leadingCoeff := by
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
            div_mul_cancel₀ _ hlcQ]
        have hsub := Polynomial.degree_sub_lt_left hdegeq hN0 hlceq
        have hdegN1 : (r.numReduced - Polynomial.C c * r.denReduced).natDegree + 1
            ≤ r.degree := by
          by_cases h0 : r.numReduced - Polynomial.C c * r.denReduced = 0
          · rw [h0, Polynomial.natDegree_zero]
            omega
          · have := Polynomial.natDegree_lt_natDegree h0 hsub
            omega
        have hWid : r.wronskian
            = Polynomial.derivative (r.numReduced - Polynomial.C c * r.denReduced)
                * r.denReduced
              - (r.numReduced - Polynomial.C c * r.denReduced)
                * Polynomial.derivative r.denReduced := by
          rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul]
          unfold RationalData.wronskian
          ring
        rw [hWid]
        exact hWrHelp _ _ r.degree hdegN1 hQd
  -- (4) Beyond a radius, the reduced denominator does not vanish.
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ z : ℂ, R0 < ‖z‖ → r.denReduced.eval z ≠ 0 := by
    have hfin : {z : ℂ | r.denReduced.IsRoot z}.Finite :=
      Polynomial.finite_setOfPred_isRoot hQ0
    obtain ⟨R0, hR0⟩ := hfin.isBounded.subset_closedBall 0
    refine ⟨R0, fun z hz h0 => ?_⟩
    have hmem : z ∈ Metric.closedBall (0 : ℂ) R0 := hR0 h0
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact absurd hz (not_lt.mpr hmem)
  -- (5) Assemble the growth bound.
  obtain ⟨C1, hC10, hC1⟩ := hpolybound r.wronskian (2 * r.degree - 2) hWrdeg
  obtain ⟨C2, hC20, hC2⟩ := hpolybound r.numReduced r.degree hNd
  obtain ⟨C3, hC30, hC3⟩ := hpolybound r.denReduced r.degree hQd
  refine ⟨2 * C1 * B + B * (C3 ^ 2 + C2 ^ 2), max R0 1, fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right R0 1) hz)
  have hzR : R0 < ‖z‖ := lt_of_le_of_lt (le_max_left R0 1) hz
  have hQz : r.denReduced.eval z ≠ 0 := hR0 z hzR
  -- Expand `deltaField` at the non-pole `z`.
  have hread : chartFiniteMap (r.toSphereMap ((z : ℂ̂)))
      = r.numReduced.eval z / r.denReduced.eval z := by
    have h1 : r.toSphereMap ↑z
        = if r.denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := rfl
    rw [h1, if_neg hQz]
    rfl
  have hexp : (r.denReduced.eval z) ^ 2 * deltaField r v z
      = r.wronskian.eval z * v z
        - (r.denReduced.eval z) ^ 2
          * v (r.numReduced.eval z / r.denReduced.eval z) := by
    simp only [deltaField, fderivRational]
    rw [hread]
    field_simp
  -- Bound the Wronskian term.
  have ht1 : ‖r.wronskian.eval z * v z‖ ≤ 2 * C1 * B * ‖z‖ ^ (2 * r.degree) := by
    rw [norm_mul]
    have e1 : ‖z‖ ^ (2 * r.degree - 2) * ‖z‖ ^ 2 = ‖z‖ ^ (2 * r.degree) := by
      rw [← pow_add]
      congr 1
      omega
    have e2 : ‖z‖ ^ (2 * r.degree - 2) ≤ ‖z‖ ^ (2 * r.degree) :=
      pow_le_pow_right₀ hz1 (by omega)
    calc ‖r.wronskian.eval z‖ * ‖v z‖
        ≤ (C1 * ‖z‖ ^ (2 * r.degree - 2)) * (B * (1 + ‖z‖ ^ 2)) :=
          mul_le_mul (hC1 z hz1) (hBv z) (norm_nonneg _)
            (by positivity)
      _ = C1 * B * (‖z‖ ^ (2 * r.degree - 2) + ‖z‖ ^ (2 * r.degree)) := by
          rw [← e1]
          ring
      _ ≤ C1 * B * (‖z‖ ^ (2 * r.degree) + ‖z‖ ^ (2 * r.degree)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ = 2 * C1 * B * ‖z‖ ^ (2 * r.degree) := by ring
  -- Bound the composed term.
  have ht2 : ‖(r.denReduced.eval z) ^ 2
        * v (r.numReduced.eval z / r.denReduced.eval z)‖
      ≤ B * (C3 ^ 2 + C2 ^ 2) * ‖z‖ ^ (2 * r.degree) := by
    rw [norm_mul, norm_pow]
    have hv2 := hBv (r.numReduced.eval z / r.denReduced.eval z)
    have hQn : ‖r.denReduced.eval z‖ ≠ 0 := norm_ne_zero_iff.mpr hQz
    calc ‖r.denReduced.eval z‖ ^ 2
          * ‖v (r.numReduced.eval z / r.denReduced.eval z)‖
        ≤ ‖r.denReduced.eval z‖ ^ 2
            * (B * (1 + ‖r.numReduced.eval z / r.denReduced.eval z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hv2 (sq_nonneg _)
      _ = B * (‖r.denReduced.eval z‖ ^ 2 + ‖r.numReduced.eval z‖ ^ 2) := by
          rw [norm_div]
          field_simp
      _ ≤ B * ((C3 * ‖z‖ ^ r.degree) ^ 2 + (C2 * ‖z‖ ^ r.degree) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          have b1 : ‖r.denReduced.eval z‖ ^ 2 ≤ (C3 * ‖z‖ ^ r.degree) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hC3 z hz1) 2
          have b2 : ‖r.numReduced.eval z‖ ^ 2 ≤ (C2 * ‖z‖ ^ r.degree) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hC2 z hz1) 2
          linarith
      _ = B * (C3 ^ 2 + C2 ^ 2) * ‖z‖ ^ (2 * r.degree) := by ring
  calc ‖(r.denReduced.eval z) ^ 2 * deltaField r v z‖
      = ‖r.wronskian.eval z * v z
          - (r.denReduced.eval z) ^ 2
            * v (r.numReduced.eval z / r.denReduced.eval z)‖ := by rw [hexp]
    _ ≤ ‖r.wronskian.eval z * v z‖
        + ‖(r.denReduced.eval z) ^ 2
            * v (r.numReduced.eval z / r.denReduced.eval z)‖ := norm_sub_le _ _
    _ ≤ 2 * C1 * B * ‖z‖ ^ (2 * r.degree)
        + B * (C3 ^ 2 + C2 ^ 2) * ‖z‖ ^ (2 * r.degree) := add_le_add ht1 ht2
    _ = (2 * C1 * B + B * (C3 ^ 2 + C2 ^ 2)) * ‖z‖ ^ (2 * r.degree) := by ring

/-- **Representation from pole and growth data** (pure function theory /
polynomial algebra). A function holomorphic off the roots of the reduced
denominator, with pole order at most twice the root multiplicity at each
root and with `Q²`-weighted growth `O(|z|^{2d})` at infinity, agrees off the
poles with an element of the section space: `Q²·g` extends to an entire
function of polynomial growth `O(|z|^{2d})`, hence is a polynomial of degree
at most `2d` by Liouville/Cauchy estimates. -/
theorem exists_sectionSpace_rep_of_pole_growth {r : RationalData} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {z : ℂ | r.denReduced.eval z ≠ 0})
    (hpole : ∀ p : ℂ, r.denReduced.eval p = 0 →
      ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ p ∈ W ∧
        DifferentiableOn ℂ h W ∧
        ∀ z ∈ W, z ≠ p →
          g z = h z / (z - p) ^ (2 * Polynomial.rootMultiplicity p r.denReduced))
    (hgrow : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      ‖(r.denReduced.eval z) ^ 2 * g z‖ ≤ C * ‖z‖ ^ (2 * r.degree)) :
    ∃ s ∈ SectionSpaceCarrier r,
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 → g z = s z := by
  classical
  obtain ⟨c₀, R, hCR⟩ := hgrow
  -- The reduced denominator is a nonzero polynomial.
  have hQ0 : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  -- The finite set of poles.
  set S : Finset ℂ := r.denReduced.roots.toFinset with hSdef
  have hmemS : ∀ z : ℂ, z ∈ S ↔ r.denReduced.eval z = 0 := fun z =>
    Multiset.mem_toFinset.trans (Polynomial.mem_roots hQ0)
  have hset : {z : ℂ | z ∉ S} = {z : ℂ | r.denReduced.eval z ≠ 0} :=
    Set.ext fun z => not_congr (hmemS z)
  -- ===== Generic removable-singularity extension over a finite set. =====
  have hremove : ∀ (T : Finset ℂ) (f : ℂ → ℂ),
      DifferentiableOn ℂ f {z : ℂ | z ∉ T} →
      (∀ p ∈ T, ∃ G : ℂ → ℂ, ContinuousAt G p ∧ ∀ᶠ z in 𝓝[≠] p, f z = G z) →
      ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ z ∉ T, E z = f z := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro f hf _
        have huniv : {z : ℂ | z ∉ (∅ : Finset ℂ)} = Set.univ := by
          ext z; simp
        rw [huniv] at hf
        exact ⟨f, differentiableOn_univ.mp hf, fun z _ => rfl⟩
    | insert p T hpT ih =>
        intro f hf hb
        -- The complement of the enlarged finite set is open.
        have hopen_ins : IsOpen {z : ℂ | z ∉ insert p T} := by
          have hcl : IsClosed (↑(insert p T) : Set ℂ) :=
            (insert p T).finite_toSet.isClosed
          have hco : {z : ℂ | z ∉ insert p T} = (↑(insert p T) : Set ℂ)ᶜ := by
            ext z; simp
          rw [hco]
          exact hcl.isOpen_compl
        -- The continuous comparison function at `p`.
        obtain ⟨G, hGc, hGev⟩ := hb p (Finset.mem_insert_self p T)
        -- A ball around `p` avoiding `T`.
        have hTcl : IsClosed (↑T : Set ℂ) := T.finite_toSet.isClosed
        have hpT' : p ∈ (↑T : Set ℂ)ᶜ := by simp [hpT]
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hTcl.isOpen_compl p hpT'
        -- A punctured ball around `p` on which `f` is bounded.
        have h1 : ∀ᶠ z in 𝓝 p, ‖G z‖ ≤ ‖G p‖ + 1 :=
          hGc.norm.eventually (eventually_le_nhds (lt_add_one ‖G p‖))
        have hfb : ∀ᶠ z in 𝓝[≠] p, ‖f z‖ ≤ ‖G p‖ + 1 := by
          filter_upwards [hGev, h1.filter_mono nhdsWithin_le_nhds] with z hz1 hz2
          rw [hz1]; exact hz2
        obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp
          (Filter.eventually_iff.mp hfb)
        set ρ : ℝ := min ε δ with hρdef
        have hρ : 0 < ρ := lt_min hε hδ
        -- Differentiability on the punctured ball.
        have hdiffU : DifferentiableOn ℂ f (Metric.ball p ρ \ {p}) := by
          intro z hz
          have hzp : z ≠ p := fun h => hz.2 (Set.mem_singleton_iff.mpr h)
          have hzT : z ∉ T := by
            have hmem := hball (Metric.ball_subset_ball (min_le_left ε δ) hz.1)
            simpa using hmem
          have hz' : z ∈ {w : ℂ | w ∉ insert p T} := by
            simp only [Set.mem_ofPred_eq, Finset.mem_insert, not_or]
            exact ⟨hzp, hzT⟩
          exact ((hf z hz').differentiableAt
            (hopen_ins.mem_nhds hz')).differentiableWithinAt
        -- Boundedness on the punctured ball.
        have hbdd : BddAbove ((norm ∘ f) '' (Metric.ball p ρ \ {p})) := by
          refine ⟨‖G p‖ + 1, ?_⟩
          rintro x ⟨w, hw, rfl⟩
          have hw1 : w ∈ Metric.ball p δ :=
            Metric.ball_subset_ball (min_le_right ε δ) hw.1
          have hw2 : w ∈ ({p} : Set ℂ)ᶜ := hw.2
          simp only [Function.comp_apply]
          exact hδsub ⟨hw1, hw2⟩
        -- Remove the singularity at `p`.
        set f' : ℂ → ℂ := Function.update f p (Filter.limUnder (𝓝[≠] p) f)
          with hf'def
        have hf'U : DifferentiableOn ℂ f' (Metric.ball p ρ) :=
          Complex.differentiableOn_update_limUnder_of_bddAbove
            (Metric.ball_mem_nhds p hρ) hdiffU hbdd
        -- The updated function is differentiable off `T`.
        have hf'T : DifferentiableOn ℂ f' {z : ℂ | z ∉ T} := by
          intro z hz
          rcases eq_or_ne z p with rfl | hzp
          · exact (hf'U.differentiableAt
              (Metric.ball_mem_nhds z hρ)).differentiableWithinAt
          · have hz' : z ∈ {w : ℂ | w ∉ insert p T} := by
              simp only [Set.mem_ofPred_eq, Finset.mem_insert, not_or]
              exact ⟨hzp, hz⟩
            have hfz : DifferentiableAt ℂ f z :=
              (hf z hz').differentiableAt (hopen_ins.mem_nhds hz')
            have hev : f' =ᶠ[𝓝 z] f := by
              filter_upwards [isOpen_ne.eventually_mem (hzp : z ≠ p)] with w hw
              exact Function.update_of_ne hw _ _
            exact (hev.differentiableAt_iff.mpr hfz).differentiableWithinAt
        -- The comparison data survives the update at the remaining points.
        have hb' : ∀ q ∈ T, ∃ G' : ℂ → ℂ, ContinuousAt G' q ∧
            ∀ᶠ z in 𝓝[≠] q, f' z = G' z := by
          intro q hq
          obtain ⟨G', hG'c, hG'ev⟩ := hb q (Finset.mem_insert_of_mem hq)
          refine ⟨G', hG'c, ?_⟩
          have hqp : q ≠ p := fun h => hpT (h ▸ hq)
          have hne : ∀ᶠ z in 𝓝[≠] q, z ≠ p :=
            (isOpen_ne.eventually_mem hqp).filter_mono nhdsWithin_le_nhds
          filter_upwards [hG'ev, hne] with z hz1 hz2
          exact (Function.update_of_ne hz2 _ _).trans hz1
        -- Conclude by the induction hypothesis.
        obtain ⟨E, hEdiff, hEeq⟩ := ih f' hf'T hb'
        refine ⟨E, hEdiff, ?_⟩
        intro z hz
        rw [Finset.mem_insert, not_or] at hz
        rw [hEeq z hz.2]
        exact Function.update_of_ne hz.1 _ _
  -- ===== `Q²·g` is differentiable off the poles. =====
  have hFdiff : DifferentiableOn ℂ (fun z => (r.denReduced.eval z) ^ 2 * g z)
      {z : ℂ | z ∉ S} := by
    rw [hset]
    exact ((r.denReduced.differentiable.pow 2).differentiableOn).mul hg
  -- ===== `Q²·g` agrees with a continuous function near each pole. =====
  have hFnear : ∀ p ∈ S, ∃ G : ℂ → ℂ, ContinuousAt G p ∧
      ∀ᶠ z in 𝓝[≠] p, (r.denReduced.eval z) ^ 2 * g z = G z := by
    intro p hp
    have hproot : r.denReduced.eval p = 0 := (hmemS p).mp hp
    obtain ⟨W, h, hWopen, hpW, hhdiff, hgeq⟩ := hpole p hproot
    set k : ℕ := Polynomial.rootMultiplicity p r.denReduced with hkdef
    set Q₁ : Polynomial ℂ :=
      r.denReduced /ₘ (Polynomial.X - Polynomial.C p) ^ k with hQ₁def
    have hfact : (Polynomial.X - Polynomial.C p) ^ k * Q₁ = r.denReduced :=
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq r.denReduced p
    have hevalfact : ∀ z : ℂ, r.denReduced.eval z = (z - p) ^ k * Q₁.eval z := by
      intro z
      conv_lhs => rw [← hfact]
      simp
    refine ⟨fun z => (Q₁.eval z) ^ 2 * h z, ?_, ?_⟩
    · exact ((Q₁.continuous.pow 2).continuousAt).mul
        ((hhdiff.differentiableAt (hWopen.mem_nhds hpW)).continuousAt)
    · have hWev : ∀ᶠ z in 𝓝[≠] p, z ∈ W :=
        Filter.eventually_mem_set.mpr (nhdsWithin_le_nhds (hWopen.mem_nhds hpW))
      have hne : ∀ᶠ z in 𝓝[≠] p, z ≠ p :=
        Filter.eventually_mem_set.mpr self_mem_nhdsWithin
      filter_upwards [hWev, hne] with z hzW hzp
      have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
      change (r.denReduced.eval z) ^ 2 * g z = (Q₁.eval z) ^ 2 * h z
      rw [hgeq z hzW hzp, hevalfact z]
      have hpow : ((z - p) ^ k) ^ 2 = (z - p) ^ (2 * k) := by
        rw [← pow_mul, mul_comm]
      calc ((z - p) ^ k * Q₁.eval z) ^ 2 * (h z / (z - p) ^ (2 * k))
          = (Q₁.eval z ^ 2 * h z) * ((z - p) ^ (2 * k) / (z - p) ^ (2 * k)) := by
            rw [mul_pow, hpow]; ring
        _ = Q₁.eval z ^ 2 * h z := by
            rw [div_self (pow_ne_zero _ hzp'), mul_one]
  -- ===== The entire extension of `Q²·g`. =====
  obtain ⟨E, hEdiff, hEeq⟩ :=
    hremove S (fun z => (r.denReduced.eval z) ^ 2 * g z) hFdiff hFnear
  have hEF : ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
      E z = (r.denReduced.eval z) ^ 2 * g z := by
    intro z hz
    have hzS : z ∉ S := fun hmem => hz ((hmemS z).mp hmem)
    exact hEeq z hzS
  -- ===== Growth bound for the entire extension. =====
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w ∈ S, ‖w‖ ≤ M := by
    obtain ⟨M, hM⟩ := (S.image fun w : ℂ => ‖w‖).exists_le
    exact ⟨M, fun w hw => hM _ (Finset.mem_image_of_mem _ hw)⟩
  set R₀ : ℝ := max (max R M) 0 + 1 with hR₀def
  have hR₀pos : 0 < R₀ := lt_of_le_of_lt (le_max_right (max R M) 0) (lt_add_one _)
  have hRR₀ : R < R₀ :=
    lt_of_le_of_lt ((le_max_left R M).trans (le_max_left _ 0)) (lt_add_one _)
  have hMR₀ : M < R₀ :=
    lt_of_le_of_lt ((le_max_right R M).trans (le_max_left _ 0)) (lt_add_one _)
  have hEgrow : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖E z‖ ≤ c₀ * ‖z‖ ^ (2 * r.degree) := by
    intro z hz
    have hzQ : r.denReduced.eval z ≠ 0 := by
      intro h0
      have h1 : ‖z‖ ≤ M := hM z ((hmemS z).mpr h0)
      have h2 : M < ‖z‖ := lt_of_lt_of_le hMR₀ hz
      linarith
    rw [hEF z hzQ]
    exact hCR z (lt_of_lt_of_le hRR₀ hz)
  -- ===== Cauchy estimates: Taylor coefficients above `2d` vanish. =====
  have hvanish : ∀ n : ℕ, 2 * r.degree < n → iteratedDeriv n E 0 = 0 := by
    intro n hn
    have key : ∀ ρ : ℝ, R₀ ≤ ρ →
        ‖iteratedDeriv n E 0‖
          ≤ (n.factorial : ℝ) * (c₀ * ρ ^ (2 * r.degree)) / ρ ^ n := by
      intro ρ hρ
      have hρpos : 0 < ρ := lt_of_lt_of_le hR₀pos hρ
      apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρpos
        hEdiff.diffContOnCl
      intro z hz
      rw [mem_sphere_iff_norm, sub_zero] at hz
      calc ‖E z‖ ≤ c₀ * ‖z‖ ^ (2 * r.degree) := hEgrow z (by rw [hz]; exact hρ)
        _ = c₀ * ρ ^ (2 * r.degree) := by rw [hz]
    have htend : Filter.Tendsto
        (fun ρ : ℝ => (n.factorial : ℝ) * (c₀ * ρ ^ (2 * r.degree)) / ρ ^ n)
        Filter.atTop (𝓝 0) := by
      have h0 : Filter.Tendsto
          (fun ρ : ℝ => ((n.factorial : ℝ) * c₀) * (ρ ^ (2 * r.degree) / ρ ^ n))
          Filter.atTop (𝓝 (((n.factorial : ℝ) * c₀) * 0)) :=
        (tendsto_pow_div_pow_atTop_zero hn).const_mul _
      rw [mul_zero] at h0
      exact h0.congr fun ρ => by ring
    have hle : ‖iteratedDeriv n E 0‖ ≤ 0 :=
      ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨R₀, key⟩)
    exact norm_le_zero_iff.mp hle
  -- ===== The entire extension is a polynomial of degree at most `2d`. =====
  set A : Polynomial ℂ := ∑ n ∈ Finset.range (2 * r.degree + 1),
    Polynomial.C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0) * Polynomial.X ^ n
    with hAdef
  have hEA : ∀ z : ℂ, E z = A.eval z := by
    intro z
    have htay : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0 * z ^ n
        = E z := by
      simpa using Complex.taylorSeries_eq_of_entire' 0 z hEdiff
    have hsum : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0 * z ^ n
        = ∑ n ∈ Finset.range (2 * r.degree + 1),
            (n.factorial : ℂ)⁻¹ * iteratedDeriv n E 0 * z ^ n := by
      refine tsum_eq_sum fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      rw [hvanish n hn]
      ring
    rw [← htay, hsum, hAdef, Polynomial.eval_finsetSum]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  have hAdeg : A.natDegree ≤ 2 * r.degree := by
    rw [hAdef]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)
  -- ===== Package the carrier element `A/Q²`. =====
  refine ⟨fun z => A.eval z / (r.denReduced.eval z) ^ 2, ?_, ?_⟩
  · exact mem_sectionSpaceCarrier_iff.mpr ⟨A, hAdeg, rfl⟩
  · intro z hz
    have hQz : (r.denReduced.eval z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
    change g z = A.eval z / (r.denReduced.eval z) ^ 2
    rw [← hEA z, hEF z hz]
    exact (mul_div_cancel_left₀ _ hQz).symm

/-- **The deformation field of an invariant coefficient lies in the section
space** — the assembly of holomorphy off poles, the pole-order bound, the
growth bound at infinity, and the representation lemma. The carrier
representative agrees with `δv` off the poles and is unique by
`sectionSpaceCarrier_eqOn_nonpoles_eq`. -/
theorem exists_sectionSpace_rep_deltaField {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (hb : eLpNormEssSup μ volume < ⊤) :
    ∃ s ∈ SectionSpaceCarrier r,
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = s z := by
  exact exists_sectionSpace_rep_of_pole_growth
    (differentiableOn_deltaField hd hv hgrad hinv)
    (fun p hp => deltaField_pole_bound hd hv hgrad hinv hb hp)
    (deltaField_growth_at_infty hd hv hgrad hinv hb)

/-! ## Trivial deformations vanish on the Julia set -/

/-- **Iterated functional equation from a trivial deformation.** If
`δv = 0` off the poles — i.e. `v(f z) = f′(z)·v(z)` at every non-pole `z` —
then along any finite orbit segment that stays off `∞`,

`v(fⁿ z) = (fⁿ)′(z)·v(z)`,

with `(fⁿ)′` the derivative of the finite-chart reading of the iterate (the
chain rule telescopes the one-step law along the orbit). -/
theorem deltaField_zero_iterate {r : RationalData} {v : ℂ → ℂ}
    (hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = 0)
    (n : ℕ) (z : ℂ)
    (hfin : ∀ j : ℕ, j ≤ n → r.toSphereMap^[j] ((z : ℂ̂)) ≠ ∞) :
    v (chartFiniteMap (r.toSphereMap^[n] ((z : ℂ̂))))
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) z
          * v z := by
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  -- Combined induction: the reading of the `k`-th iterate has a derivative
  -- `D` at `w`, and the one-step law telescopes to `v(f^[k] w) = D · v w`.
  have key : ∀ (k : ℕ) (w : ℂ),
      (∀ j : ℕ, j ≤ k → r.toSphereMap^[j] ((w : ℂ̂)) ≠ ∞) →
      ∃ D : ℂ,
        HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂)))) D w ∧
        v (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂)))) = D * v w := by
    intro k
    induction k with
    | zero =>
        intro w _
        refine ⟨1, ?_, ?_⟩
        · have h2 : (fun x : ℂ => chartFiniteMap (r.toSphereMap^[0] ((x : ℂ̂))))
              = fun x : ℂ => x := funext fun x => rfl
          rw [h2]
          exact hasDerivAt_id w
        · rw [Function.iterate_zero_apply, cf, one_mul]
    | succ k ih =>
        intro w hw
        -- the derivative and the functional equation at time `k`
        obtain ⟨D, hD, hDval⟩ := ih w fun j hj => hw j (Nat.le_succ_of_le hj)
        -- the finite reading `u` of the `k`-th iterate at `w`
        obtain ⟨u, hu⟩ : ∃ u : ℂ, r.toSphereMap^[k] ((w : ℂ̂)) = ((u : ℂ̂)) := by
          cases hc : r.toSphereMap^[k] ((w : ℂ̂)) with
          | infty => exact absurd hc (hw k (Nat.le_succ k))
          | coe v' => exact ⟨v', rfl⟩
        have hhw : chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))) = u := by
          rw [hu, cf]
        -- `u` is not a pole: the `(k+1)`-st point is finite
        have hfu : r.toSphereMap ((u : ℂ̂)) ≠ ∞ := by
          have h1 : r.toSphereMap^[k + 1] ((w : ℂ̂)) ≠ ∞ := hw (k + 1) le_rfl
          rw [Function.iterate_succ_apply', hu] at h1
          exact h1
        have hden : r.denReduced.eval u ≠ 0 := by
          intro h0
          apply hfu
          have hread : r.toSphereMap ((u : ℂ̂))
              = if r.denReduced.eval u = 0 then (∞ : ℂ̂)
                else ((r.numReduced.eval u / r.denReduced.eval u : ℂ) : ℂ̂) := rfl
          rw [hread, if_pos h0]
        -- the derivative of the reading of `f` at the non-pole `u`
        have hg : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u) u := by
          have hdiv : HasDerivAt (fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x)
              (((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2) u :=
            (r.numReduced.hasDerivAt u).div (r.denReduced.hasDerivAt u) hden
          have hev' : (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              =ᶠ[𝓝 u] fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x := by
            filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with x hx
            have hread : r.toSphereMap ((x : ℂ̂))
                = if r.denReduced.eval x = 0 then (∞ : ℂ̂)
                  else ((r.numReduced.eval x / r.denReduced.eval x : ℂ) : ℂ̂) := rfl
            rw [hread, if_neg hx, cf]
          have hfd : fderivRational r u
              = ((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2 := by
            have hwr : r.wronskian.eval u
                = (Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u := by
              simp only [RationalData.wronskian, Polynomial.eval_sub, Polynomial.eval_mul]
            have hfd0 : fderivRational r u
                = r.wronskian.eval u / (r.denReduced.eval u) ^ 2 := rfl
            rw [hfd0, hwr]
          rw [hfd]
          exact hdiv.congr_of_eventuallyEq hev'
        -- the set where the `k`-th iterate stays finite is open
        have hopen : IsOpen {x : ℂ | r.toSphereMap^[k] ((x : ℂ̂)) ≠ ∞} := by
          have hc : Continuous fun x : ℂ => r.toSphereMap^[k] ((x : ℂ̂)) :=
            (r.continuous_toSphereMap.iterate k).comp OnePoint.continuous_coe
          exact OnePoint.isClosed_infty.isOpen_compl.preimage hc
        -- near `w`, the `(k+1)`-reading is the composite of the two readings
        have hev : ((fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              ∘ fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂))))
            =ᶠ[𝓝 w] fun x : ℂ => chartFiniteMap (r.toSphereMap^[k + 1] ((x : ℂ̂))) := by
          filter_upwards [hopen.mem_nhds (hw k (Nat.le_succ k))] with x hx
          obtain ⟨y, hy⟩ : ∃ y : ℂ, r.toSphereMap^[k] ((x : ℂ̂)) = ((y : ℂ̂)) := by
            cases hc : r.toSphereMap^[k] ((x : ℂ̂)) with
            | infty => exact absurd hc hx
            | coe y => exact ⟨y, rfl⟩
          simp only [Function.comp_apply]
          rw [Function.iterate_succ_apply', hy, cf]
        -- chain rule at the pair of matched points
        have hg2 : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u)
            ((fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂)))) w) := by
          change HasDerivAt _ _ (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))))
          rw [hhw]
          exact hg
        have hcomp := HasDerivAt.comp w hg2 hD
        refine ⟨fderivRational r u * D, hcomp.congr_of_eventuallyEq hev.symm, ?_⟩
        -- the one-step functional equation at `u`, from `δv = 0`
        have hδu : fderivRational r u * v u
            - v (chartFiniteMap (r.toSphereMap ((u : ℂ̂)))) = 0 := hδ u hden
        have h1 : v (chartFiniteMap (r.toSphereMap ((u : ℂ̂)))) = fderivRational r u * v u :=
          (sub_eq_zero.mp hδu).symm
        have h2 : v u = D * v w := by rw [← hhw]; exact hDval
        have hsucc : chartFiniteMap (r.toSphereMap^[k + 1] ((w : ℂ̂)))
            = chartFiniteMap (r.toSphereMap ((u : ℂ̂))) := by
          rw [Function.iterate_succ_apply', hu]
        rw [hsucc, h1, h2, mul_assoc]
  obtain ⟨D, hD, hval⟩ := key n z hfin
  rw [hD.deriv]
  exact hval

/-- **A trivial deformation vanishes on the Julia set** (at its finite
points). At a repelling periodic point `p` of period `n` whose cycle avoids
`∞`, the iterated functional equation gives `v(p) = m·v(p)` with
`m = multiplier (f^[n]) p`, `|m| > 1`, forcing `v(p) = 0`; repelling cycles
through `∞` are handled by discarding the at most one exceptional cycle
(density is preserved under removing finitely many points from a subset
dense in the perfect Julia set). Density of repelling cycles
(`juliaSet_eq_closure_repelling`, needing degree at least two) and
continuity of `v` conclude. -/
theorem sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero
    {r : RationalData} (hd : 2 ≤ r.degree) {v : ℂ → ℂ}
    (hv : IsSphereVectorField v)
    (hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = 0) :
    ∀ z : ℂ, ((z : ℂ̂) ∈ JuliaSet r.toSphereMap) → v z = 0 := by
  classical
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 2 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  -- The repelling set and its exceptional part (cycles through `∞`).
  set R : Set ℂ̂ := {p : ℂ̂ | ∃ n : ℕ, IsRepellingPeriodicPt r.toSphereMap n p}
    with hRdef
  set B : Set ℂ̂ := {p : ℂ̂ | p ∈ R ∧ ∃ j : ℕ, r.toSphereMap^[j] p = ∞}
    with hBdef
  -- ===== Step 0: the exceptional set is finite (at most one cycle). =====
  have hBfin : B.Finite := by
    rcases Set.eq_empty_or_nonempty B with hB | hB
    · rw [hB]; exact Set.finite_empty
    · obtain ⟨p₀, hp₀⟩ := hB
      obtain ⟨hp₀R, j₀, hj₀⟩ := hp₀
      obtain ⟨n₀, hn₀pos, hper₀, -⟩ := hp₀R
      have hper₀' : r.toSphereMap^[n₀] p₀ = p₀ := hper₀
      -- `∞` is a periodic point (of period `n₀`).
      have hinfper : r.toSphereMap^[n₀] (∞ : ℂ̂) = ∞ := by
        calc r.toSphereMap^[n₀] (∞ : ℂ̂)
            = r.toSphereMap^[n₀] (r.toSphereMap^[j₀] p₀) := by rw [hj₀]
          _ = r.toSphereMap^[n₀ + j₀] p₀ := (Function.iterate_add_apply _ _ _ _).symm
          _ = r.toSphereMap^[j₀ + n₀] p₀ := by rw [add_comm]
          _ = r.toSphereMap^[j₀] (r.toSphereMap^[n₀] p₀) :=
              Function.iterate_add_apply _ _ _ _
          _ = r.toSphereMap^[j₀] p₀ := by rw [hper₀']
          _ = ∞ := hj₀
      have hinfper' : Function.IsPeriodicPt r.toSphereMap n₀ (∞ : ℂ̂) := hinfper
      -- Every exceptional point lies on the (finite) orbit of `∞`.
      have hBsub : B ⊆ (fun k : ℕ => r.toSphereMap^[k] (∞ : ℂ̂)) '' (Set.Iio n₀) := by
        rintro p ⟨hpR, j, hj⟩
        obtain ⟨n, hnpos, hper, -⟩ := hpR
        have hper' : r.toSphereMap^[n] p = p := hper
        have hj' : r.toSphereMap^[j % n] p = ∞ := by
          rw [Function.IsPeriodicPt.iterate_mod_apply hper j]
          exact hj
        have hjn : j % n < n := Nat.mod_lt j hnpos
        have hp_orbit : r.toSphereMap^[n - j % n] (∞ : ℂ̂) = p := by
          calc r.toSphereMap^[n - j % n] (∞ : ℂ̂)
              = r.toSphereMap^[n - j % n] (r.toSphereMap^[j % n] p) := by rw [hj']
            _ = r.toSphereMap^[n - j % n + j % n] p :=
                (Function.iterate_add_apply _ _ _ _).symm
            _ = r.toSphereMap^[n] p := by rw [Nat.sub_add_cancel hjn.le]
            _ = p := hper'
        refine ⟨(n - j % n) % n₀, Nat.mod_lt _ hn₀pos, ?_⟩
        change r.toSphereMap^[(n - j % n) % n₀] (∞ : ℂ̂) = p
        rw [hinfper'.iterate_mod_apply]
        exact hp_orbit
      exact Set.Finite.subset ((Set.finite_Iio n₀).image _) hBsub
  -- ===== Step 1: `v` vanishes at finite repelling points off `B`. =====
  have hvanish : ∀ w : ℂ, ((w : ℂ̂)) ∈ R \ B → v w = 0 := by
    intro w hw
    obtain ⟨hwR, hwB⟩ := hw
    obtain ⟨n, hnpos, hper, hmul⟩ := hwR
    -- the full orbit of `w` avoids `∞`
    have hinf : ∀ j : ℕ, r.toSphereMap^[j] ((w : ℂ̂)) ≠ ∞ := by
      intro j hj
      exact hwB ⟨⟨n, hnpos, hper, hmul⟩, j, hj⟩
    -- the iterated functional equation at the period
    have hiter := deltaField_zero_iterate hδ n w (fun j _ => hinf j)
    have hper' : r.toSphereMap^[n] ((w : ℂ̂)) = ((w : ℂ̂)) := hper
    rw [hper', cf] at hiter
    -- the derivative of the return reading is the multiplier, of norm `> 1`
    have hmul' : 1 < ‖deriv (fun x : ℂ =>
        chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) w‖ := hmul
    have hm1 : deriv (fun x : ℂ =>
        chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) w ≠ 1 := by
      intro h1
      rw [h1] at hmul'
      simp at hmul'
    have h0 : (1 - deriv (fun x : ℂ =>
        chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) w) * v w = 0 := by
      linear_combination hiter
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hm1
    · exact h
  -- ===== Step 2: the Julia set lies in the closure of `R \ B`. =====
  have hJR : JuliaSet r.toSphereMap = closure R :=
    juliaSet_eq_closure_repelling hfr hdeg
  have hRB : JuliaSet r.toSphereMap ⊆ closure (R \ B) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro U hUopen hxU
    -- find a Julia point of `U` off `B` (perfectness beats the finite `B`)
    obtain ⟨y, hyU, hyJ, hyB⟩ : ∃ y, y ∈ U ∧ y ∈ JuliaSet r.toSphereMap ∧ y ∉ B := by
      by_cases hxB : x ∈ B
      · have hperf := juliaSet_perfect hfr hdeg
        have hacc := hperf.acc x hx
        rw [accPt_iff_nhds] at hacc
        have hBx_closed : IsClosed (B \ {x}) := (hBfin.subset Set.sdiff_subset).isClosed
        have hUx_open : IsOpen (U \ (B \ {x})) := hUopen.sdiff hBx_closed
        have hxUx : x ∈ U \ (B \ {x}) := ⟨hxU, fun h => h.2 rfl⟩
        obtain ⟨y, ⟨⟨hyU1, hyU2⟩, hyJ⟩, hyx⟩ := hacc _ (hUx_open.mem_nhds hxUx)
        exact ⟨y, hyU1, hyJ, fun hyB => hyU2 ⟨hyB, hyx⟩⟩
      · exact ⟨x, hxU, hx, hxB⟩
    -- near `y`, repelling points avoid the finite closed set `B`
    have hyR : y ∈ closure R := by rw [← hJR]; exact hyJ
    have hUB_open : IsOpen (U \ B) := hUopen.sdiff hBfin.isClosed
    have hyUB : y ∈ U \ B := ⟨hyU, hyB⟩
    obtain ⟨p, hpUB, hpR⟩ := _root_.mem_closure_iff.mp hyR _ hUB_open hyUB
    exact ⟨p, hpUB.1, hpR, hpUB.2⟩
  -- ===== Step 3: pull the closure back through the finite chart. =====
  intro z hz
  -- points of `R \ B` are finite (their orbits avoid `∞`, already at time `0`)
  have hGrange : R \ B ⊆ Set.range ((↑) : ℂ → ℂ̂) := by
    rintro p ⟨hpR, hpB⟩
    cases p with
    | infty => exact absurd ⟨hpR, 0, rfl⟩ hpB
    | coe w => exact ⟨w, rfl⟩
  have hzcl : (z : ℂ̂) ∈ closure (R \ B) := hRB hz
  have hpre : z ∈ closure {w : ℂ | ((w : ℂ̂)) ∈ R \ B} := by
    have hind : Topology.IsInducing ((↑) : ℂ → ℂ̂) :=
      OnePoint.isOpenEmbedding_coe.isInducing
    have h1 : closure {w : ℂ | ((w : ℂ̂)) ∈ R \ B}
        = ((↑) : ℂ → ℂ̂) ⁻¹' closure (((↑) : ℂ → ℂ̂) '' {w : ℂ | ((w : ℂ̂)) ∈ R \ B}) :=
      hind.closure_eq_preimage_closure_image _
    have h2 : ((↑) : ℂ → ℂ̂) '' {w : ℂ | ((w : ℂ̂)) ∈ R \ B} = R \ B := by
      have h3 : {w : ℂ | ((w : ℂ̂)) ∈ R \ B} = ((↑) : ℂ → ℂ̂) ⁻¹' (R \ B) := rfl
      rw [h3]
      exact Set.image_preimage_eq_of_subset hGrange
    rw [h1, h2]
    exact hzcl
  -- ===== Conclude by continuity of `v`. =====
  have hclosed : IsClosed {w : ℂ | v w = 0} := isClosed_eq hv.1 continuous_const
  have hsub : {w : ℂ | ((w : ℂ̂)) ∈ R \ B} ⊆ {w : ℂ | v w = 0} :=
    fun w hw => hvanish w hw
  exact closure_minimal hsub hclosed hpre

end NoWanderingDomains
