/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Carleson.ToMathlib.RealInterpolation.Misc
import NoWanderingDomains.Analysis.SingularIntegral.LpDuality

/-!
# Riesz–Thorin / Stein complex interpolation

The **Riesz–Thorin interpolation theorem**: an (a.e.) linear operator `T` on
`ℂ`-valued functions that is bounded `L^{p₀} → L^{p₀}` with constant `M₀` and
`L^{p₁} → L^{p₁}` with constant `M₁` is bounded `Lᵖ → Lᵖ` with the multiplicative
constant `M₀^{1-θ} · M₁^θ`, where `1/p = (1-θ)/p₀ + θ/p₁` for `θ ∈ (0,1)`.

Unlike the real (Marcinkiewicz) interpolation theorem, the constant here is
**multiplicatively sharp**: it tends to `M₀` as `θ → 0`. This is the qualitative
input the measurable Riemann mapping theorem consumes for the Beurling transform:
since the Beurling transform is an `L²` isometry (`M₀ = 1` at `p₀ = 2`) and
`Lᵖ`-bounded for every `p`, its operator norm on `Lᵖ` tends to `1` as `p → 2`, so
the Neumann series `∑ (μ T)ⁿ μ` converges in `Lᵖ` for `‖μ‖∞ < 1` and `p` near `2`.

The proof is the Stein/Thorin argument: reduce to simple `f, g` by density and
`Lᵖ`–`Lᵖ'` duality (`eLpNorm_le_iSup_integral_mul`); form the analytic family
`f_z = |f|^{p·P(z)} sgn f`, `g_z = |g|^{p'·Q(z)} sgn g` interpolating the
exponents; then `F(z) = ∫ (T f_z)·g_z` is — because `f, g` are simple and `T` is
a.e. linear — a **finite sum of exponentials** `c·exp(λ z)`, hence entire and
bounded on the strip `0 ≤ Re z ≤ 1`, with `|F(it)| ≤ M₀`, `|F(1+it)| ≤ M₁`. The
Hadamard three-lines theorem
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`)
gives `|F(θ)| ≤ M₀^{1-θ} M₁^θ`, and `F(θ) = ∫ (T f)·g`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

namespace RieszThorin

open Complex.HadamardThreeLines

/-! ## The analytic building block `fpow`

For a complex number `w` and an "exponent" `c : ℂ`, `fpow c w` is `|w|^{Re c} · sgn w`
extended by `0` at `w = 0`, but where the modulus part is taken with the *complex* exponent
`c`: `fpow c w = exp (c · log ‖w‖) · (w / ‖w‖)`. Along a vertical line `c = α + i β`, its
modulus is `|w|^α` (independent of `β`), and as a function of `c` (for fixed `w ≠ 0`) it is
`(const) · exp (c · log ‖w‖)`, an entire function. -/

/-- `fpow c w = |w| ^ c · sgn w`, extended by `0` at `w = 0`. -/
noncomputable def fpow (c : ℂ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else Complex.exp (c * Real.log ‖w‖) * (w / (‖w‖ : ℂ))

@[simp] lemma fpow_zero_right (c : ℂ) : fpow c 0 = 0 := by simp [fpow]

lemma fpow_eq_of_ne {c w : ℂ} (hw : w ≠ 0) :
    fpow c w = Complex.exp (c * Real.log ‖w‖) * (w / (‖w‖ : ℂ)) := by
  simp [fpow, hw]

/-- The modulus of `fpow c w` depends only on `Re c`: for `w ≠ 0` it is `‖w‖^{Re c}`. -/
lemma norm_fpow_of_ne {c w : ℂ} (hw : w ≠ 0) : ‖fpow c w‖ = ‖w‖ ^ c.re := by
  rw [fpow_eq_of_ne hw, norm_mul, Complex.norm_exp]
  have hwpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_pos_iff.mpr hw).ne', mul_one]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Real.rpow_def_of_pos hwpos, mul_comm]

@[simp] lemma fpow_one (w : ℂ) : fpow 1 w = w := by
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw]
  · rw [fpow_eq_of_ne hw]
    have hwpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log hwpos]
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm ((‖w‖ : ℝ) : ℂ) (w : ℂ), mul_assoc]
    rw [show ((‖w‖ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ)⁻¹ = 1 from
      mul_inv_cancel₀ (by exact_mod_cast hwpos.ne'), mul_one]

/-- When `Re c > 0`, the modulus of `fpow c w` is `‖w‖ ^ Re c` for *all* `w` (including `0`). -/
lemma norm_fpow_of_re_pos {c : ℂ} (hc : 0 < c.re) (w : ℂ) : ‖fpow c w‖ = ‖w‖ ^ c.re := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw; simp [Real.zero_rpow hc.ne']
  · exact norm_fpow_of_ne hw

/-- For fixed `y`, `z ↦ fpow (g z) y` is differentiable whenever `g` is, since for `y ≠ 0`
it equals `(const) · exp (g z · log ‖y‖)` and for `y = 0` it is constantly `0`. -/
lemma differentiable_fpow_comp {g : ℂ → ℂ} (hg : Differentiable ℂ g) (y : ℂ) :
    Differentiable ℂ (fun z => fpow (g z) y) := by
  rcases eq_or_ne y 0 with hy | hy
  · simp only [hy, fpow_zero_right]
    exact differentiable_const 0
  · have heq : (fun z => fpow (g z) y)
        = fun z => Complex.exp (g z * (Real.log ‖y‖ : ℂ)) * (y / (‖y‖ : ℂ)) := by
      ext z; rw [fpow_eq_of_ne hy]
    rw [heq]
    exact (((hg.mul_const _).cexp).mul_const _)

/-- For a simple function `s` with range `R`, the function `x ↦ fpow c (s x)` is the finite
sum over `y ∈ R` of `fpow c y` on the fiber `s ⁻¹' {y}`. -/
lemma fpow_comp_eq_sum {s : ℂ → ℂ} {R : Finset ℂ} (hR : ∀ x, s x ∈ R) (c : ℂ) (x : ℂ) :
    fpow c (s x) = ∑ y ∈ R, (s ⁻¹' {y}).indicator (fun _ => fpow c y) x := by
  rw [Finset.sum_eq_single (s x)]
  · rw [Set.indicator_of_mem (by simp : x ∈ s ⁻¹' {s x})]
  · intro y _ hy
    apply Set.indicator_of_notMem
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fun h => hy h.symm
  · intro h
    exact absurd (hR x) h

/-- If every nonzero fiber of a simple function `s` has finite measure, then `x ↦ fpow c (s x)`
is `MemLp` at every exponent `q`. -/
lemma memLp_fpow_comp (s : MeasureTheory.SimpleFunc ℂ ℂ) (c : ℂ)
    (hfib : ∀ y, y ≠ 0 → volume (s ⁻¹' {y}) ≠ ⊤) (q : ℝ≥0∞) :
    MemLp (fun x => fpow c (s x)) q volume := by
  have hsum : (fun x => fpow c (s x))
      = ∑ y ∈ s.range, (s ⁻¹' {y}).indicator (fun _ => fpow c y) := by
    ext x
    rw [Finset.sum_apply]
    exact fpow_comp_eq_sum (R := s.range) (fun x => SimpleFunc.mem_range_self s x) c x
  rw [hsum]
  apply memLp_finsetSum'
  intro y _
  rcases eq_or_ne y 0 with hy | hy
  · exact memLp_indicator_const q (s.measurableSet_fiber y) (fpow c y) (Or.inl (by simp [hy]))
  · exact memLp_indicator_const q (s.measurableSet_fiber y) (fpow c y) (Or.inr (hfib y hy))

/-! ## Linearity of `T` over finite sums of `L^{p₀}` functions -/

variable {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ : ℝ≥0∞}

/-- If `T` is a.e.-additive on functions in `L^{p₀} ∪ L^{p₁}`, then it commutes (a.e.) with
finite sums of `L^{p₀}` functions. -/
lemma T_finset_sum
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    {ι : Type*} (R : Finset ι) (h : ι → ℂ → ℂ) (hmem : ∀ i ∈ R, MemLp (h i) p₀ volume) :
    T (∑ i ∈ R, h i) =ᵐ[volume] ∑ i ∈ R, T (h i) := by
  classical
  induction R using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    -- `T 0 =ᵐ 0`: from `T (0 + 0) =ᵐ T 0 + T 0`.
    have h0 : MemLp (0 : ℂ → ℂ) p₀ volume := MemLp.zero
    have := hadd 0 0 (Or.inl h0) (Or.inl h0)
    rw [add_zero] at this
    filter_upwards [this] with x hx
    simpa using hx
  | insert a R ha ih =>
    have hmemR : ∀ i ∈ R, MemLp (h i) p₀ volume := fun i hi => hmem i (Finset.mem_insert_of_mem hi)
    have hsumR : MemLp (∑ i ∈ R, h i) p₀ volume := memLp_finsetSum' R hmemR
    have hha : MemLp (h a) p₀ volume := hmem a (Finset.mem_insert_self a R)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hstep := hadd (h a) (∑ i ∈ R, h i) (Or.inl hha) (Or.inl hsumR)
    have hih := ih hmemR
    filter_upwards [hstep, hih] with x hx hxih
    simp only [Pi.add_apply] at hx ⊢
    rw [hx, hxih]

/-- The image `T(fpow c ∘ s)` of the analytic family at a simple function `s`, expressed (a.e.)
as a finite combination of the fixed functions `T(𝟙_{fiber})` over the *nonzero* fibers. -/
lemma T_fpow_comp_ae
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (s : MeasureTheory.SimpleFunc ℂ ℂ) (c : ℂ)
    (hfib : ∀ y, y ≠ 0 → volume (s ⁻¹' {y}) ≠ ⊤) :
    T (fun x => fpow c (s x)) =ᵐ[volume]
      ∑ y ∈ s.range.filter (· ≠ 0), fpow c y • T ((s ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) := by
  classical
  set R := s.range.filter (· ≠ 0) with hR
  have hmemfib : ∀ y ∈ R, MemLp ((s ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) p₀ volume := by
    intro y hy
    have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
    exact memLp_indicator_const p₀ (s.measurableSet_fiber y) (1 : ℂ) (Or.inr (hfib y hy0))
  -- Write `fpow c ∘ s` as a finite sum of scaled fiber indicators over nonzero fibers.
  set u : ℂ → ℂ → ℂ := fun y => fpow c y • (s ⁻¹' {y}).indicator (fun _ => (1 : ℂ)) with hu
  have hmem_u : ∀ y ∈ R, MemLp (u y) p₀ volume :=
    fun y hy => (hmemfib y hy).const_smul (fpow c y)
  have huapply : ∀ y x, u y x = (s ⁻¹' {y}).indicator (fun _ => fpow c y) x := by
    intro y x
    simp only [hu, Pi.smul_apply, Set.indicator]
    by_cases hx : x ∈ s ⁻¹' {y} <;> simp [hx]
  have hdecomp : (fun x => fpow c (s x)) = ∑ y ∈ R, u y := by
    ext x
    rw [Finset.sum_apply,
      fpow_comp_eq_sum (R := s.range) (fun x => SimpleFunc.mem_range_self s x) c x]
    rw [show (∑ y ∈ s.range, (s ⁻¹' {y}).indicator (fun _ => fpow c y) x)
          = ∑ y ∈ s.range, u y x from Finset.sum_congr rfl (fun y _ => (huapply y x).symm)]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro y _ hy
    have hy0 : y = 0 := by
      by_contra h
      exact hy (Finset.mem_filter.mpr ⟨‹_›, h⟩)
    subst hy0
    rw [huapply]
    simp
  rw [hdecomp]
  -- Push `T` through the finite sum, then through each scalar.
  refine (T_finset_sum hadd R u hmem_u).trans ?_
  -- `T (u y) =ᵐ fpow c y • T (𝟙_{fy})` for each `y ∈ R`.
  apply eventuallyEq_sum (s := R)
  intro y hy
  exact hsmul (fpow c y) ((s ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) (Or.inl (hmemfib y hy))

/-- The integral `∫ T(f_c)·g_d` of the analytic family, written as a finite double sum of
exponentials. Here `f_c = fpow c ∘ sf`, `g_d = fpow d ∘ sg` with `sf, sg` simple. -/
lemma integral_T_fpow_eq_double_sum
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (sf sg : MeasureTheory.SimpleFunc ℂ ℂ) (c d : ℂ)
    (hfibf : ∀ y, y ≠ 0 → volume (sf ⁻¹' {y}) ≠ ⊤)
    (hint : ∀ y ∈ sf.range.filter (· ≠ 0), ∀ y' ∈ sg.range.filter (· ≠ 0),
      Integrable (fun x => T ((sf ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) x *
        (sg ⁻¹' {y'}).indicator (fun _ => (1 : ℂ)) x) volume) :
    ∫ x, T (fun x => fpow c (sf x)) x * fpow d (sg x) ∂volume
      = ∑ y ∈ sf.range.filter (· ≠ 0), ∑ y' ∈ sg.range.filter (· ≠ 0),
          fpow c y * fpow d y' *
            ∫ x, T ((sf ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) x *
              (sg ⁻¹' {y'}).indicator (fun _ => (1 : ℂ)) x ∂volume := by
  classical
  set Rf := sf.range.filter (· ≠ 0) with hRf
  set Rg := sg.range.filter (· ≠ 0) with hRg
  set uf : ℂ → ℂ → ℂ := fun y => T ((sf ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) with huf
  set vg : ℂ → ℂ → ℂ := fun y' => (sg ⁻¹' {y'}).indicator (fun _ => (1 : ℂ)) with hvg
  -- (a) rewrite the integrand a.e.
  have hTf : T (fun x => fpow c (sf x)) =ᵐ[volume] ∑ y ∈ Rf, fpow c y • uf y :=
    T_fpow_comp_ae hadd hsmul sf c hfibf
  have hgd : (fun x => fpow d (sg x)) = ∑ y' ∈ Rg, fpow d y' • vg y' := by
    ext x
    rw [Finset.sum_apply,
      fpow_comp_eq_sum (R := sg.range) (fun x => SimpleFunc.mem_range_self sg x) d x]
    rw [show (∑ y' ∈ sg.range, (sg ⁻¹' {y'}).indicator (fun _ => fpow d y') x)
          = ∑ y' ∈ sg.range, (fpow d y' • vg y') x from
        Finset.sum_congr rfl (fun y' _ => by
          simp only [hvg, Pi.smul_apply, Set.indicator]
          by_cases hx : x ∈ sg ⁻¹' {y'} <;> simp [hx])]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro y' _ hy'
    have hy'0 : y' = 0 := by
      by_contra h; exact hy' (Finset.mem_filter.mpr ⟨‹_›, h⟩)
    subst hy'0
    simp [hvg]
  -- (b) integrand a.e. equals the product of the two finite sums.
  have hprod : (fun x => T (fun x => fpow c (sf x)) x * fpow d (sg x))
      =ᵐ[volume] fun x => (∑ y ∈ Rf, fpow c y • uf y) x * (∑ y' ∈ Rg, fpow d y' • vg y') x := by
    filter_upwards [hTf] with x hx
    rw [hx, congrFun hgd x]
  rw [integral_congr_ae hprod]
  -- (c) expand the product of finite sums pointwise.
  have hexp : (fun x => (∑ y ∈ Rf, fpow c y • uf y) x * (∑ y' ∈ Rg, fpow d y' • vg y') x)
      = fun x => ∑ y ∈ Rf, ∑ y' ∈ Rg, (fpow c y * fpow d y') * (uf y x * vg y' x) := by
    ext x
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro y' _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexp]
  -- (d) push the integral through the two finite sums and pull out constants.
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl; intro y hy
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl; intro y' hy'
      exact integral_const_mul (fpow c y * fpow d y') (fun x => uf y x * vg y' x)
    · intro y' hy'
      exact ((hint y hy y' hy').const_mul _)
  · intro y hy
    apply integrable_finsetSum
    intro y' hy'
    exact ((hint y hy y' hy').const_mul _)

/-! ## The three-lines bound for simple functions -/

/-- The real affine exponent function `z ↦ r₀(1 - z) + r₁ z`, with `(·).re = r₀(1-Re z)+r₁ Re z`. -/
noncomputable def affLine (r₀ r₁ : ℝ) (z : ℂ) : ℂ := (r₀ : ℂ) * (1 - z) + (r₁ : ℂ) * z

@[simp] lemma affLine_re (r₀ r₁ : ℝ) (z : ℂ) :
    (affLine r₀ r₁ z).re = r₀ * (1 - z.re) + r₁ * z.re := by
  simp only [affLine, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, sub_zero,
    zero_mul]

lemma differentiable_affLine (r₀ r₁ : ℝ) : Differentiable ℂ (affLine r₀ r₁) := by
  unfold affLine; fun_prop

/-! ## Conjugate exponents -/

/-- For `1 ≤ p ≤ ∞`, the conjugate exponent `(1 - p⁻¹)⁻¹` satisfies `p⁻¹ + (conj)⁻¹ = 1`. -/
lemma holderConjugate_inv {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ := by
  rw [ENNReal.holderConjugate_iff]
  have hpinv_le : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp
  rw [inv_inv, add_comm, tsub_add_cancel_of_le hpinv_le]

/-- **Bilinear Hölder bound.** If `F ∈ L^q` and `g ∈ L^{q'}` with `q, q'` Hölder conjugates,
then `‖∫ F·g‖ₑ ≤ eLpNorm F q · eLpNorm g q'`. -/
lemma enorm_integral_mul_le {q q' : ℝ≥0∞} [hqq' : ENNReal.HolderConjugate q q']
    {F g : ℂ → ℂ} (hF : AEStronglyMeasurable F volume) (hg : AEStronglyMeasurable g volume) :
    ‖∫ x, F x * g x ∂volume‖ₑ ≤ eLpNorm F q volume * eLpNorm g q' volume := by
  have : ENNReal.HolderTriple q' q 1 := ENNReal.HolderTriple.symm
  have hholder : eLpNorm (g • F) 1 volume ≤ eLpNorm g q' volume * eLpNorm F q volume :=
    eLpNorm_smul_le_mul_eLpNorm (f := F) (φ := g) hF hg
  calc ‖∫ x, F x * g x ∂volume‖ₑ
      ≤ ∫⁻ x, ‖F x * g x‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (g • F) 1 volume := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        congr 1; ext x; rw [Pi.smul_apply', smul_eq_mul, mul_comm]
    _ ≤ eLpNorm g q' volume * eLpNorm F q volume := hholder
    _ = eLpNorm F q volume * eLpNorm g q' volume := mul_comm _ _

/-- The product `T(F)·G` is integrable when `T(F) ∈ L^{q}` and `G ∈ L^{q'}` (conjugates). -/
lemma integrable_mul_of_memLp {q q' : ℝ≥0∞} [hqq' : ENNReal.HolderConjugate q q']
    {F G : ℂ → ℂ} (hF : MemLp F q volume) (hG : MemLp G q' volume) :
    Integrable (fun x => F x * G x) volume := by
  have : ENNReal.HolderTriple q' q 1 := ENNReal.HolderTriple.symm
  have hsmul : MemLp (G • F) 1 volume := hF.smul (f := F) (φ := G) hG
  rw [memLp_one_iff_integrable] at hsmul
  have heq : (fun x => F x * G x) = G • F := by
    ext x; rw [Pi.smul_apply', smul_eq_mul, mul_comm]
  rw [heq]; exact hsmul

/-- `x ^ t ≤ max (x ^ lo) (x ^ hi)` for `0 < x` and `lo ≤ t ≤ hi`. -/
lemma rpow_le_max_of_mem_Icc {x lo hi t : ℝ} (hx : 0 < x) (hlo : lo ≤ t) (hhi : t ≤ hi) :
    x ^ t ≤ max (x ^ lo) (x ^ hi) := by
  rcases le_or_gt x 1 with hx1 | hx1
  · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hx hx1 hlo) (le_max_left _ _)
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le hhi) (le_max_right _ _)

/-- When `Re c = 0`, the modulus of `fpow c w` is at most `1`. -/
lemma norm_fpow_le_one_of_re_zero {c : ℂ} (hc : c.re = 0) (w : ℂ) : ‖fpow c w‖ ≤ 1 := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw; simp
  · rw [norm_fpow_of_ne hw, hc, Real.rpow_zero]

/-- The `L^q` norm of the analytic family `fpow c ∘ s` (for `Re c > 0`): it equals
`(eLpNorm s (q · Re c))^{Re c}`. -/
lemma eLpNorm_fpow_comp {c : ℂ} (hc : 0 < c.re) (s : ℂ → ℂ) (q : ℝ≥0∞) :
    eLpNorm (fun x => fpow c (s x)) q volume
      = eLpNorm s (q * ENNReal.ofReal c.re) volume ^ c.re := by
  rw [show eLpNorm (fun x => fpow c (s x)) q volume
        = eLpNorm (fun x => ‖s x‖ ^ c.re) q volume from
      eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
        rw [norm_fpow_of_re_pos hc, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])]
  exact eLpNorm_norm_rpow s hc

/-- `eLpNorm (fpow c ∘ g) q ≤ 1`, in either of two regimes: `Re c > 0` with
`eLpNorm g (q · Re c) ≤ 1`; or `Re c = 0` and `q = ∞`. -/
lemma eLpNorm_fpow_comp_le_one {c : ℂ} {q : ℝ≥0∞} (g : ℂ → ℂ)
    (h : (0 < c.re ∧ eLpNorm g (q * ENNReal.ofReal c.re) volume ≤ 1) ∨ (c.re = 0 ∧ q = ⊤)) :
    eLpNorm (fun x => fpow c (g x)) q volume ≤ 1 := by
  rcases h with ⟨hc, hg⟩ | ⟨hc, hq⟩
  · rw [eLpNorm_fpow_comp hc]
    calc eLpNorm g (q * ENNReal.ofReal c.re) volume ^ c.re
        ≤ 1 ^ c.re := by gcongr
      _ = 1 := ENNReal.one_rpow _
  · subst hq
    rw [eLpNorm_exponent_top]
    refine le_trans (eLpNormEssSup_le_of_ae_bound (C := 1)
      (Eventually.of_forall fun x => norm_fpow_le_one_of_re_zero hc (g x))) ?_
    rw [ENNReal.ofReal_one]

/-! ## Analyticity and boundedness of the double sum -/

/-- The double sum `G z = ∑_{y∈Rf} ∑_{y'∈Rg} fpow (P z) y · fpow (Q z) y' · coef y y'`. -/
noncomputable def doubleSum (P Q : ℂ → ℂ) (Rf Rg : Finset ℂ) (coef : ℂ → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ y ∈ Rf, ∑ y' ∈ Rg, fpow (P z) y * fpow (Q z) y' * coef y y'

/-- The double sum is differentiable whenever `P, Q` are. -/
lemma differentiable_doubleSum {P Q : ℂ → ℂ} (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q)
    (Rf Rg : Finset ℂ) (coef : ℂ → ℂ → ℂ) :
    Differentiable ℂ (doubleSum P Q Rf Rg coef) := by
  unfold doubleSum
  apply Differentiable.fun_sum
  intro y _
  apply Differentiable.fun_sum
  intro y' _
  exact ((differentiable_fpow_comp hP y).mul (differentiable_fpow_comp hQ y')).mul_const _

/-- On the closed strip, the double sum is bounded in norm. -/
lemma norm_doubleSum_le {P Q : ℂ → ℂ} (Rf Rg : Finset ℂ) (coef : ℂ → ℂ → ℂ)
    {loP hiP loQ hiQ : ℝ}
    (hRf : ∀ y ∈ Rf, y ≠ 0) (hRg : ∀ y' ∈ Rg, y' ≠ 0)
    (hP : ∀ z ∈ verticalClosedStrip 0 1, (P z).re ∈ Set.Icc loP hiP)
    (hQ : ∀ z ∈ verticalClosedStrip 0 1, (Q z).re ∈ Set.Icc loQ hiQ)
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖doubleSum P Q Rf Rg coef z‖ ≤
      ∑ y ∈ Rf, ∑ y' ∈ Rg,
        max (‖y‖ ^ loP) (‖y‖ ^ hiP) * max (‖y'‖ ^ loQ) (‖y'‖ ^ hiQ) * ‖coef y y'‖ := by
  unfold doubleSum
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro y hy
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro y' hy'
  rw [norm_mul, norm_mul, norm_fpow_of_ne (hRf y hy), norm_fpow_of_ne (hRg y' hy')]
  gcongr
  · exact rpow_le_max_of_mem_Icc (norm_pos_iff.mpr (hRf y hy)) (hP z hz).1 (hP z hz).2
  · exact rpow_le_max_of_mem_Icc (norm_pos_iff.mpr (hRg y' hy')) (hQ z hz).1 (hQ z hz).2

/-! ## Exponent arithmetic -/

/-- Multiplying a finite nonzero exponent `pᵢ` by `ofReal r` (with `r ≥ 0`) gives `target`,
provided the real exponents satisfy `pᵢ.toReal * r = target.toReal`. -/
lemma mul_ofReal_eq {pᵢ target : ℝ≥0∞} (hpᵢtop : pᵢ ≠ ⊤) (_hpᵢ0 : pᵢ ≠ 0)
    (htgtop : target ≠ ⊤) (_htg0 : target ≠ 0) {r : ℝ} (_hr : 0 ≤ r)
    (hreal : pᵢ.toReal * r = target.toReal) :
    pᵢ * ENNReal.ofReal r = target := by
  rw [← ENNReal.ofReal_toReal hpᵢtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, hreal,
    ENNReal.ofReal_toReal htgtop]

/-- From the interpolation relation on inverses, `p` is a genuine finite exponent `≥ 1`. -/
lemma p_ne_top_of_interp {p₀ p₁ p : ℝ≥0∞} {θ : ℝ} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₁top : p₁ ≠ ⊤) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    p ≠ ⊤ ∧ p ≠ 0 ∧ 1 ≤ p := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h1θ : (0:ℝ) < 1 - θ := by linarith
  have hp₀0 : p₀ ≠ 0 := (lt_of_lt_of_le one_pos hp₀).ne'
  have hp₁0 : p₁ ≠ 0 := (lt_of_lt_of_le one_pos hp₁).ne'
  have hp₀inv_le : p₀⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp₀
  have hp₁inv_le : p₁⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp₁
  -- `p⁻¹ ≤ 1` so `1 ≤ p`.
  have hpinv_le_one : p⁻¹ ≤ 1 := by
    rw [hp]
    calc ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹
        ≤ ENNReal.ofReal (1 - θ) * 1 + ENNReal.ofReal θ * 1 := by gcongr
      _ = ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ := by rw [mul_one, mul_one]
      _ = ENNReal.ofReal ((1 - θ) + θ) := by
          rw [ENNReal.ofReal_add h1θ.le hθ0.le]
      _ = 1 := by norm_num
  have h1p : 1 ≤ p := ENNReal.inv_le_one.mp hpinv_le_one
  -- `p⁻¹ ≠ 0`: bounded below by `ofReal θ * p₁⁻¹ > 0`.
  have hp₁inv_pos : 0 < p₁⁻¹ := ENNReal.inv_pos.mpr hp₁top
  have hpinv_pos : 0 < p⁻¹ := by
    rw [hp]
    have : 0 < ENNReal.ofReal θ * p₁⁻¹ :=
      ENNReal.mul_pos (by rw [ENNReal.ofReal_ne_zero_iff]; exact hθ0) hp₁inv_pos.ne'
    exact lt_of_lt_of_le this le_add_self
  refine ⟨?_, ?_, h1p⟩
  · -- p ≠ ⊤ from p⁻¹ ≠ 0
    intro htop
    rw [htop] at hpinv_pos; simp at hpinv_pos
  · -- p ≠ 0 from p⁻¹ ≤ 1 ≠ ⊤
    intro h0
    rw [h0] at hpinv_le_one; simp at hpinv_le_one

/-- The interpolation relation in real exponents: `1/a = (1-θ)/a₀ + θ/a₁`. -/
lemma toReal_interp {p₀ p₁ p : ℝ≥0∞} {θ : ℝ}
    (_hp₀top : p₀ ≠ ⊤) (_hp₁top : p₁ ≠ ⊤) (hp₀0 : p₀ ≠ 0) (hp₁0 : p₁ ≠ 0)
    (_hptop : p ≠ ⊤) (_hp0 : p ≠ 0) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    (p.toReal)⁻¹ = (1 - θ) * (p₀.toReal)⁻¹ + θ * (p₁.toReal)⁻¹ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h1θ : (0:ℝ) ≤ 1 - θ := by linarith
  have key : (p⁻¹).toReal = (ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹).toReal := by
    rw [hp]
  rw [ENNReal.toReal_inv] at key
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal h1θ, ENNReal.toReal_ofReal hθ0.le] at key
  exact key

/-- Interpolation inclusion: `L^{p₀} ∩ L^{p₁} ⊆ L^p` for `p₀ ≤ p ≤ p₁` (with `p₁ ≠ ⊤`).
Proved via the truncation decomposition. -/
lemma memLp_of_memLp_memLp {p₀ p₁ p : ℝ≥0∞} {h : ℂ → ℂ}
    (hp₀0 : p₀ ≠ 0) (hp₁top : p₁ ≠ ⊤) (hp₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (h0 : MemLp h p₀ volume) (h1 : MemLp h p₁ volume) :
    MemLp h p volume := by
  have hp0 : 0 < p := lt_of_lt_of_le (pos_iff_ne_zero.mpr hp₀0) hp₀p
  have htrunc : MemLp (MeasureTheory.trunc h 1) p volume := by
    have := MeasureTheory.trunc_Lp_Lq_higher (p := p₀) (q := p) (t := 1) (μ := volume)
      ⟨pos_iff_ne_zero.mpr hp₀0, hp₀p⟩ h0 (by simp)
    simpa using this
  have htruncCompl : MemLp (MeasureTheory.truncCompl h 1) p volume := by
    have := MeasureTheory.truncCompl_Lp_Lq_lower (p := p₁) (q := p) (t := 1) (μ := volume)
      hp₁top ⟨hp0, hpp₁⟩ (by norm_num) h1
    simpa using this
  have hsum : MemLp (MeasureTheory.trunc h 1 + MeasureTheory.truncCompl h 1) p volume :=
    htrunc.add htruncCompl
  rwa [MeasureTheory.trunc_add_truncCompl] at hsum

/-- Pointwise: for the large part (`truncCompl`, where `‖r‖ₑ > 1`), `‖·‖ₑ^{a₀} ≤ ‖r‖ₑ^{a}`
when `a₀ ≤ a`; for the small part (`trunc`, where `‖r‖ₑ ≤ 1`), `‖·‖ₑ^{a₁} ≤ ‖r‖ₑ^{a}` when
`a ≤ a₁`. -/
lemma enorm_truncCompl_rpow_le {r : ℂ → ℂ} {a₀ a : ℝ} (ha₀pos : 0 < a₀) (ha₀a : a₀ ≤ a)
    (x : ℂ) :
    ‖MeasureTheory.truncCompl r 1 x‖ₑ ^ a₀ ≤ ‖r x‖ₑ ^ a := by
  rw [MeasureTheory.truncCompl]
  split_ifs with h
  · rw [enorm_zero, ENNReal.zero_rpow_of_pos ha₀pos]; exact zero_le
  · rw [not_le] at h
    exact ENNReal.rpow_le_rpow_of_exponent_le (le_of_lt h) ha₀a

lemma enorm_trunc_rpow_le {r : ℂ → ℂ} {a₁ a : ℝ} (ha₁pos : 0 < a₁) (haa₁ : a ≤ a₁) (x : ℂ) :
    ‖MeasureTheory.trunc r 1 x‖ₑ ^ a₁ ≤ ‖r x‖ₑ ^ a := by
  rw [MeasureTheory.trunc]
  split_ifs with h
  · exact ENNReal.rpow_le_rpow_of_exponent_ge h haa₁
  · rw [enorm_zero, ENNReal.zero_rpow_of_pos ha₁pos]; exact zero_le

/-- The `L^{q}`-norm of `truncCompl r 1` (large part) is at most `(eLpNorm r p)^{p/q}`. -/
lemma eLpNorm_truncCompl_le {r : ℂ → ℂ} {q p : ℝ≥0∞}
    (hq0 : q ≠ 0) (hqtop : q ≠ ⊤) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (hqp : q ≤ p) :
    eLpNorm (MeasureTheory.truncCompl r 1) q volume
      ≤ eLpNorm r p volume ^ (p.toReal / q.toReal) := by
  have ha₀pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hapos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hqp' : q.toReal ≤ p.toReal := (ENNReal.toReal_le_toReal hqtop hptop).mpr hqp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop]
  have hlint : (∫⁻ x, ‖MeasureTheory.truncCompl r 1 x‖ₑ ^ q.toReal ∂volume)
      ≤ ∫⁻ x, ‖r x‖ₑ ^ p.toReal ∂volume :=
    lintegral_mono (fun x => enorm_truncCompl_rpow_le ha₀pos hqp' x)
  have heq : (∫⁻ x, ‖r x‖ₑ ^ p.toReal ∂volume) = eLpNorm r p volume ^ p.toReal := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, one_div,
      ENNReal.rpow_inv_rpow hapos.ne']
  calc (∫⁻ x, ‖MeasureTheory.truncCompl r 1 x‖ₑ ^ q.toReal ∂volume) ^ (1 / q.toReal)
      ≤ (∫⁻ x, ‖r x‖ₑ ^ p.toReal ∂volume) ^ (1 / q.toReal) := by gcongr
    _ = (eLpNorm r p volume ^ p.toReal) ^ (1 / q.toReal) := by rw [heq]
    _ = eLpNorm r p volume ^ (p.toReal / q.toReal) := by
        rw [← ENNReal.rpow_mul]
        congr 1; field_simp

/-- The `L^{q}`-norm of `trunc r 1` (small part) is at most `(eLpNorm r p)^{p/q}` for `p ≤ q`. -/
lemma eLpNorm_trunc_le {r : ℂ → ℂ} {q p : ℝ≥0∞}
    (hq0 : q ≠ 0) (hqtop : q ≠ ⊤) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (hpq : p ≤ q) :
    eLpNorm (MeasureTheory.trunc r 1) q volume
      ≤ eLpNorm r p volume ^ (p.toReal / q.toReal) := by
  have ha₁pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hapos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hpq' : p.toReal ≤ q.toReal := (ENNReal.toReal_le_toReal hptop hqtop).mpr hpq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop]
  have hlint : (∫⁻ x, ‖MeasureTheory.trunc r 1 x‖ₑ ^ q.toReal ∂volume)
      ≤ ∫⁻ x, ‖r x‖ₑ ^ p.toReal ∂volume :=
    lintegral_mono (fun x => enorm_trunc_rpow_le ha₁pos hpq' x)
  have heq : (∫⁻ x, ‖r x‖ₑ ^ p.toReal ∂volume) = eLpNorm r p volume ^ p.toReal := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, one_div,
      ENNReal.rpow_inv_rpow hapos.ne']
  calc (∫⁻ x, ‖MeasureTheory.trunc r 1 x‖ₑ ^ q.toReal ∂volume) ^ (1 / q.toReal)
      ≤ (∫⁻ x, ‖r x‖ₑ ^ p.toReal ∂volume) ^ (1 / q.toReal) := by gcongr
    _ = (eLpNorm r p volume ^ p.toReal) ^ (1 / q.toReal) := by rw [heq]
    _ = eLpNorm r p volume ^ (p.toReal / q.toReal) := by
        rw [← ENNReal.rpow_mul]
        congr 1; field_simp

/-- A boundary estimate: if `eLpNorm (T F) q ≤ M · eLpNorm F q`, `eLpNorm F q ≤ 1`,
`eLpNorm Gf q' ≤ 1` with `q, q'` conjugates, then `‖∫ (T F)·Gf‖ₑ ≤ M`. -/
lemma boundary_enorm_le {T : (ℂ → ℂ) → ℂ → ℂ} {q q' : ℝ≥0∞} [ENNReal.HolderConjugate q q']
    {M : ℝ≥0} {F Gf : ℂ → ℂ}
    (hTF_aesm : AEStronglyMeasurable (T F) volume) (hGf_aesm : AEStronglyMeasurable Gf volume)
    (hTF : eLpNorm (T F) q volume ≤ M * eLpNorm F q volume)
    (hF1 : eLpNorm F q volume ≤ 1) (hGf1 : eLpNorm Gf q' volume ≤ 1) :
    ‖∫ x, T F x * Gf x ∂volume‖ₑ ≤ (M : ℝ≥0∞) := by
  calc ‖∫ x, T F x * Gf x ∂volume‖ₑ
      ≤ eLpNorm (T F) q volume * eLpNorm Gf q' volume :=
        enorm_integral_mul_le hTF_aesm hGf_aesm
    _ ≤ ((M : ℝ≥0∞) * eLpNorm F q volume) * eLpNorm Gf q' volume := by gcongr
    _ ≤ ((M : ℝ≥0∞) * 1) * 1 := by gcongr
    _ = (M : ℝ≥0∞) := by rw [mul_one, mul_one]

/-- Extend a pairing bound from simple test functions to all of `L^{p'}`, given that `T sf ∈ L^p`.
The functional `g ↦ ‖∫ (T sf)·g‖ₑ` is bounded by `M·eLpNorm g p'` on simple functions, hence
(by density and Hölder continuity) on all of `L^{p'}`. -/
lemma pairing_le_of_simple {Tsf : ℂ → ℂ} {p p' : ℝ≥0∞} {M : ℝ≥0∞}
    [hpp' : ENNReal.HolderConjugate p p'] (hp'top : p' ≠ ⊤)
    (hTsf : MemLp Tsf p volume) (hMtop : M ≠ ⊤)
    (hsimple : ∀ sg : MeasureTheory.SimpleFunc ℂ ℂ, MemLp (sg : ℂ → ℂ) p' volume →
      ‖∫ x, Tsf x * (sg : ℂ → ℂ) x ∂volume‖ₑ ≤ M * eLpNorm (sg : ℂ → ℂ) p' volume)
    {g : ℂ → ℂ} (hg : MemLp g p' volume) :
    ‖∫ x, Tsf x * g x ∂volume‖ₑ ≤ M * eLpNorm g p' volume := by
  set Ntf := eLpNorm Tsf p volume with hNtf
  have hNtftop : Ntf ≠ ⊤ := hTsf.2.ne
  set C := M + Ntf with hC
  have hCtop : C ≠ ⊤ := by rw [hC]; finiteness
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  -- Choose a simple approximation `gε` to `g` in `L^{p'}` with small error.
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / (C + 1) with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    apply ENNReal.div_ne_zero.mpr
    exact ⟨by simpa using hε.ne', by finiteness⟩
  obtain ⟨gε, hgε_lt, hgε_mem⟩ := hg.exists_simpleFunc_eLpNorm_sub_lt hp'top hδ0
  -- Split the integral.
  have hintegrable_g : Integrable (fun x => Tsf x * g x) volume :=
    integrable_mul_of_memLp (q := p) (q' := p') (hqq' := hpp') (F := Tsf) (G := g) hTsf hg
  have hintegrable_gε : Integrable (fun x => Tsf x * (gε : ℂ → ℂ) x) volume :=
    integrable_mul_of_memLp (q := p) (q' := p') (hqq' := hpp')
      (F := Tsf) (G := (gε : ℂ → ℂ)) hTsf hgε_mem
  have hsplit : (∫ x, Tsf x * g x ∂volume)
      = (∫ x, Tsf x * (gε : ℂ → ℂ) x ∂volume)
        + ∫ x, Tsf x * (g x - (gε : ℂ → ℂ) x) ∂volume := by
    rw [← integral_add hintegrable_gε
      (by simpa [Pi.sub_def, mul_sub] using hintegrable_g.sub hintegrable_gε)]
    congr 1; ext x; ring
  -- Bound the error term via Hölder.
  have hg_sub_mem : MemLp (fun x => g x - (gε : ℂ → ℂ) x) p' volume := hg.sub hgε_mem
  have herr : ‖∫ x, Tsf x * (g x - (gε : ℂ → ℂ) x) ∂volume‖ₑ ≤ Ntf * δ := by
    refine le_trans (enorm_integral_mul_le (q := p) (q' := p') (hqq' := hpp')
      (F := Tsf) (g := fun x => g x - (gε : ℂ → ℂ) x) hTsf.1 hg_sub_mem.1) ?_
    rw [hNtf]
    gcongr
    rw [show (fun x => g x - (gε : ℂ → ℂ) x) = g - (gε : ℂ → ℂ) from rfl]
    exact le_of_lt hgε_lt
  -- Bound `eLpNorm gε p' ≤ eLpNorm g p' + δ`.
  have hgεnorm : eLpNorm (gε : ℂ → ℂ) p' volume ≤ eLpNorm g p' volume + δ := by
    have hstep : eLpNorm (gε : ℂ → ℂ) p' volume
        ≤ eLpNorm g p' volume + eLpNorm ((gε : ℂ → ℂ) - g) p' volume := by
      have := eLpNorm_sub_le (f := (gε : ℂ → ℂ)) (g := g) (p := p') (μ := volume)
        hgε_mem.1 hg.1 hpp'.symm.one_le
      calc eLpNorm (gε : ℂ → ℂ) p' volume
          = eLpNorm (g + ((gε : ℂ → ℂ) - g)) p' volume := by
            congr 1; ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
        _ ≤ eLpNorm g p' volume + eLpNorm ((gε : ℂ → ℂ) - g) p' volume :=
            eLpNorm_add_le hg.1 (hgε_mem.sub hg).1 hpp'.symm.one_le
    refine le_trans hstep ?_
    gcongr
    rw [eLpNorm_sub_comm]
    exact le_of_lt hgε_lt
  -- Combine.
  calc ‖∫ x, Tsf x * g x ∂volume‖ₑ
      ≤ ‖∫ x, Tsf x * (gε : ℂ → ℂ) x ∂volume‖ₑ
          + ‖∫ x, Tsf x * (g x - (gε : ℂ → ℂ) x) ∂volume‖ₑ := by
        rw [hsplit]; exact enorm_add_le _ _
    _ ≤ M * eLpNorm (gε : ℂ → ℂ) p' volume + Ntf * δ := by
        gcongr
        exact hsimple gε hgε_mem
    _ ≤ M * (eLpNorm g p' volume + δ) + Ntf * δ := by gcongr
    _ = M * eLpNorm g p' volume + (M + Ntf) * δ := by ring
    _ ≤ M * eLpNorm g p' volume + ε := by
        gcongr
        rw [← hC, hδ]
        calc C * ((ε : ℝ≥0∞) / (C + 1))
            ≤ (C + 1) * ((ε : ℝ≥0∞) / (C + 1)) := by gcongr; exact le_self_add
          _ = (ε : ℝ≥0∞) := by
              rw [mul_comm, ENNReal.div_mul_cancel (by simp) (by finiteness)]

set_option maxHeartbeats 400000 in
-- Large local context (the full exponent bookkeeping of the Stein argument) needs a higher budget.
/-- **Three-lines bound (per test function `g`).** For simple `f, g` with `eLpNorm f p = 1`
and `eLpNorm g p' ≤ 1` (where `p'` is the conjugate of `p`), the pairing `∫ T(f)·g` has
modulus at most `M₀^{1-θ}·M₁^θ`. Here `p₀ < p₁`. -/
lemma three_lines_bound
    {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ p : ℝ≥0∞} {M₀ M₁ : ℝ≥0} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₀top : p₀ ≠ ⊤) (hp₁ : 1 ≤ p₁) (hp₁top : p₁ ≠ ⊤) (hp₀p₁ : p₀ < p₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hmeas : ∀ s : ℂ → ℂ, MemLp s p volume → AEStronglyMeasurable (T s) volume)
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (hT₀ : ∀ s : ℂ → ℂ, MemLp s p₀ volume → eLpNorm (T s) p₀ volume ≤ M₀ * eLpNorm s p₀ volume)
    (hT₁ : ∀ s : ℂ → ℂ, MemLp s p₁ volume → eLpNorm (T s) p₁ volume ≤ M₁ * eLpNorm s p₁ volume)
    (sf sg : MeasureTheory.SimpleFunc ℂ ℂ)
    (hfmem : MemLp (sf : ℂ → ℂ) p volume) (hf1 : eLpNorm (sf : ℂ → ℂ) p volume = 1)
    (hgmem : MemLp (sg : ℂ → ℂ) (1 - p⁻¹)⁻¹ volume)
    (hg1 : eLpNorm (sg : ℂ → ℂ) (1 - p⁻¹)⁻¹ volume ≤ 1) :
    ‖∫ x, T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x ∂volume‖ₑ
      ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ := by
  classical
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hp₀p₁ne : p₀ ≠ p₁ := hp₀p₁.ne
  -- Basic exponent facts.
  have hp₀0 : p₀ ≠ 0 := (lt_of_lt_of_le one_pos hp₀).ne'
  have hp₁0 : p₁ ≠ 0 := (lt_of_lt_of_le one_pos hp₁).ne'
  obtain ⟨hptop, hp0, h1p⟩ := p_ne_top_of_interp hp₀ hp₁ hp₁top ⟨hθ0, hθ1⟩ hp
  -- The conjugate exponent `p' = (1 - p⁻¹)⁻¹`.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'def
  have hpp' : ENNReal.HolderConjugate p p' := holderConjugate_inv h1p
  -- `p₁ > 1` since `p₀ < p₁` and `p₀ ≥ 1`.
  have h1p₁ : 1 < p₁ := lt_of_le_of_lt hp₀ hp₀p₁
  -- Real exponents.
  set a := p.toReal with ha
  set a₀ := p₀.toReal with ha₀
  set a₁ := p₁.toReal with ha₁
  have ha₀pos : 0 < a₀ := ENNReal.toReal_pos hp₀0 hp₀top
  have ha₁pos : 0 < a₁ := ENNReal.toReal_pos hp₁0 hp₁top
  have hapos : 0 < a := ENNReal.toReal_pos hp0 hptop
  have h1a₀ : 1 ≤ a₀ := by
    rw [ha₀, show (1:ℝ) = (1:ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_le_toReal (by simp) hp₀top).mpr hp₀
  have h1a₁ : 1 ≤ a₁ := by
    rw [ha₁, show (1:ℝ) = (1:ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_le_toReal (by simp) hp₁top).mpr hp₁
  -- Interpolation in reals: `1/a = (1-θ)/a₀ + θ/a₁`.
  have hinterp : a⁻¹ = (1 - θ) * a₀⁻¹ + θ * a₁⁻¹ :=
    toReal_interp hp₀top hp₁top hp₀0 hp₁0 hptop hp0 ⟨hθ0, hθ1⟩ hp
  -- Conjugate exponents and their reals.
  set p₀' : ℝ≥0∞ := (1 - p₀⁻¹)⁻¹ with hp₀'def
  set p₁' : ℝ≥0∞ := (1 - p₁⁻¹)⁻¹ with hp₁'def
  have hp₀p₀' : ENNReal.HolderConjugate p₀ p₀' := holderConjugate_inv hp₀
  have hp₁p₁' : ENNReal.HolderConjugate p₁ p₁' := holderConjugate_inv hp₁
  set a' := p'.toReal with ha'
  -- `a₀ < a₁` since `p₀ < p₁` (both finite).
  have ha₀a₁ : a₀ < a₁ := (ENNReal.toReal_lt_toReal hp₀top hp₁top).mpr hp₀p₁
  -- `1/a < 1` strictly, hence `a > 1`.
  have h1a : 1 < a := by
    have hstrict : a⁻¹ < 1 := by
      rw [hinterp]
      rcases eq_or_lt_of_le h1a₀ with ha₀1 | ha₀1
      · -- a₀ = 1, so a₁ > 1
        have ha₁1 : 1 < a₁ := by rw [← ha₀1] at ha₀a₁; exact ha₀a₁
        have : θ * a₁⁻¹ < θ * 1 := by
          apply mul_lt_mul_of_pos_left _ hθ0
          rw [inv_lt_one₀ ha₁pos]; exact ha₁1
        rw [mul_one] at this
        rw [← ha₀1]; simp only [inv_one, mul_one]; linarith
      · -- a₀ > 1
        have : (1 - θ) * a₀⁻¹ < (1 - θ) * 1 := by
          apply mul_lt_mul_of_pos_left _ (by linarith)
          rw [inv_lt_one₀ ha₀pos]; exact ha₀1
        rw [mul_one] at this
        have h2 : θ * a₁⁻¹ ≤ θ * 1 := by
          apply mul_le_mul_of_nonneg_left _ hθ0.le
          rw [inv_le_one₀ ha₁pos]; exact h1a₁
        rw [mul_one] at h2; linarith
    rw [inv_lt_one₀ hapos] at hstrict; exact hstrict
  have h1p_lt : 1 < p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_toReal hptop, ← ha]
    exact (ENNReal.ofReal_lt_ofReal_iff hapos).mpr h1a
  have hp'top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr h1p_lt).ne
  have hp'0 : p' ≠ 0 := (ENNReal.HolderConjugate.pos p' p).ne'
  have ha'pos : 0 < a' := ENNReal.toReal_pos hp'0 hp'top
  -- `1/a + 1/a' = 1` (real conjugate relation).
  have hconj : a⁻¹ + a'⁻¹ = 1 := by
    have h := hpp'.inv_add_inv_eq_one
    have := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_add (by simp [hp0]) (by simp [hp'0]), ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_one] at this
  -- `b₀ = 1 - 1/a₀ = 1/a₀'`, `b₁ = 1 - 1/a₁`.
  set b₀ := 1 - a₀⁻¹ with hb₀
  set b₁ := 1 - a₁⁻¹ with hb₁
  have hb₀nonneg : 0 ≤ b₀ := by
    rw [hb₀]
    have : a₀⁻¹ ≤ 1 := by rw [inv_le_one₀ ha₀pos]; exact h1a₀
    linarith
  have hb₁pos : 0 < b₁ := by
    rw [hb₁]
    have : a₁⁻¹ < 1 := by
      rw [inv_lt_one₀ ha₁pos]; linarith [lt_of_le_of_lt h1a₀ ha₀a₁]
    linarith
  -- The exponent functions.
  set P := affLine (a / a₀) (a / a₁) with hPdef
  set Q := affLine (a' * b₀) (a' * b₁) with hQdef
  have hPdiff : Differentiable ℂ P := differentiable_affLine _ _
  have hQdiff : Differentiable ℂ Q := differentiable_affLine _ _
  -- Real-exponent helper identities.
  have ha_div₀ : a / a₀ = a * a₀⁻¹ := div_eq_mul_inv _ _
  have ha_div₁ : a / a₁ = a * a₁⁻¹ := div_eq_mul_inv _ _
  -- `P θ = 1`.
  have hPθ : P (θ : ℂ) = 1 := by
    rw [hPdef, affLine]
    have : (a / a₀ : ℝ) * (1 - θ) + (a / a₁ : ℝ) * θ = 1 := by
      rw [ha_div₀, ha_div₁]
      have : a * a₀⁻¹ * (1 - θ) + a * a₁⁻¹ * θ = a * ((1 - θ) * a₀⁻¹ + θ * a₁⁻¹) := by ring
      rw [this, ← hinterp, mul_inv_cancel₀ hapos.ne']
    push_cast
    exact_mod_cast this
  -- `Q θ = 1`.
  have hQθ : Q (θ : ℂ) = 1 := by
    rw [hQdef, affLine]
    have hval : (a' * b₀) * (1 - θ) + (a' * b₁) * θ = 1 := by
      rw [hb₀, hb₁]
      have hexp : (1 - θ) * (1 - a₀⁻¹) + θ * (1 - a₁⁻¹) = 1 - a⁻¹ := by
        rw [hinterp]; ring
      have : a' * (1 - a₀⁻¹) * (1 - θ) + a' * (1 - a₁⁻¹) * θ
          = a' * ((1 - θ) * (1 - a₀⁻¹) + θ * (1 - a₁⁻¹)) := by ring
      rw [this, hexp]
      have ha'inv : a'⁻¹ = 1 - a⁻¹ := by linarith [hconj]
      rw [← ha'inv, mul_inv_cancel₀ ha'pos.ne']
    push_cast
    exact_mod_cast hval
  -- Positivity of the exponent slopes.
  have haa₀pos : 0 < a / a₀ := div_pos hapos ha₀pos
  have haa₁pos : 0 < a / a₁ := div_pos hapos ha₁pos
  have hQ1pos : 0 < a' * b₁ := mul_pos ha'pos hb₁pos
  -- Boundary real parts.
  have hPre0 : ∀ z : ℂ, z.re = 0 → (P z).re = a / a₀ := by
    intro z hz; rw [hPdef, affLine_re, hz]; ring
  have hPre1 : ∀ z : ℂ, z.re = 1 → (P z).re = a / a₁ := by
    intro z hz; rw [hPdef, affLine_re, hz]; ring
  have hQre0 : ∀ z : ℂ, z.re = 0 → (Q z).re = a' * b₀ := by
    intro z hz; rw [hQdef, affLine_re, hz]; ring
  have hQre1 : ∀ z : ℂ, z.re = 1 → (Q z).re = a' * b₁ := by
    intro z hz; rw [hQdef, affLine_re, hz]; ring
  -- Strip bounds for the real parts (needed for boundedness).
  have hPstrip : ∀ z ∈ verticalClosedStrip 0 1,
      (P z).re ∈ Set.Icc (min (a / a₀) (a / a₁)) (max (a / a₀) (a / a₁)) := by
    intro z hz
    simp only [verticalClosedStrip, Set.mem_preimage, Set.mem_Icc] at hz
    rw [hPdef, affLine_re]
    constructor
    · rw [show a / a₀ * (1 - z.re) + a / a₁ * z.re
            = a / a₀ + (a / a₁ - a / a₀) * z.re by ring]
      rcases le_total (a / a₀) (a / a₁) with h | h
      · rw [min_eq_left h]; nlinarith [hz.1]
      · rw [min_eq_right h]; nlinarith [hz.2, hz.1]
    · rw [show a / a₀ * (1 - z.re) + a / a₁ * z.re
            = a / a₀ + (a / a₁ - a / a₀) * z.re by ring]
      rcases le_total (a / a₀) (a / a₁) with h | h
      · rw [max_eq_right h]; nlinarith [hz.2, hz.1]
      · rw [max_eq_left h]; nlinarith [hz.1]
  have hQstrip : ∀ z ∈ verticalClosedStrip 0 1,
      (Q z).re ∈ Set.Icc (min (a' * b₀) (a' * b₁)) (max (a' * b₀) (a' * b₁)) := by
    intro z hz
    simp only [verticalClosedStrip, Set.mem_preimage, Set.mem_Icc] at hz
    rw [hQdef, affLine_re]
    constructor
    · rw [show a' * b₀ * (1 - z.re) + a' * b₁ * z.re
            = a' * b₀ + (a' * b₁ - a' * b₀) * z.re by ring]
      rcases le_total (a' * b₀) (a' * b₁) with h | h
      · rw [min_eq_left h]; nlinarith [hz.1]
      · rw [min_eq_right h]; nlinarith [hz.2, hz.1]
    · rw [show a' * b₀ * (1 - z.re) + a' * b₁ * z.re
            = a' * b₀ + (a' * b₁ - a' * b₀) * z.re by ring]
      rcases le_total (a' * b₀) (a' * b₁) with h | h
      · rw [max_eq_right h]; nlinarith [hz.2, hz.1]
      · rw [max_eq_left h]; nlinarith [hz.1]
  -- Key exponent identities relating boundary norms back to `p` and `p'`.
  have hexp_p₀ : p₀ * ENNReal.ofReal (a / a₀) = p := by
    apply mul_ofReal_eq hp₀top hp₀0 hptop hp0 haa₀pos.le
    rw [← ha₀, ← ha]; field_simp
  have hexp_p₁ : p₁ * ENNReal.ofReal (a / a₁) = p := by
    apply mul_ofReal_eq hp₁top hp₁0 hptop hp0 haa₁pos.le
    rw [← ha₁, ← ha]; field_simp
  -- `p₁'.toReal = (a' * b₁)⁻¹` type identities via `b₁ = (p₁'.toReal)⁻¹`.
  have hp₁'top : p₁' ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p₁' p₁).mpr h1p₁).ne
  have hp₁'0 : p₁' ≠ 0 := (ENNReal.HolderConjugate.pos p₁' p₁).ne'
  have hb₁_eq : (p₁'.toReal)⁻¹ = b₁ := by
    rw [hp₁'def, hb₁, ENNReal.toReal_inv, inv_inv,
      ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hp₁) (by simp),
      ENNReal.toReal_one, ENNReal.toReal_inv, ha₁]
  have hp₁'toReal_pos : 0 < p₁'.toReal := ENNReal.toReal_pos hp₁'0 hp₁'top
  have hexp_p₁' : p₁' * ENNReal.ofReal (a' * b₁) = p' := by
    apply mul_ofReal_eq hp₁'top hp₁'0 hp'top hp'0 hQ1pos.le
    rw [← ha', ← hb₁_eq]
    field_simp
  -- Fiber finiteness.
  have hfibf : ∀ y, y ≠ 0 → volume (sf ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    (SimpleFunc.measure_preimage_lt_top_of_memLp hp0 hptop sf hfmem y hy).ne
  have hfibg : ∀ y', y' ≠ 0 → volume (sg ⁻¹' {y'}) ≠ ⊤ := fun y' hy' =>
    (SimpleFunc.measure_preimage_lt_top_of_memLp hp'0 hp'top sg hgmem y' hy').ne
  -- The fiber indicators and their `MemLp` membership.
  set uf : ℂ → ℂ → ℂ := fun y => T ((sf ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) with huf
  set vg : ℂ → ℂ → ℂ := fun y' => (sg ⁻¹' {y'}).indicator (fun _ => (1 : ℂ)) with hvg
  have hindf_mem : ∀ y, y ≠ 0 → MemLp ((sf ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) p₀ volume :=
    fun y hy => memLp_indicator_const p₀ (sf.measurableSet_fiber y) (1 : ℂ) (Or.inr (hfibf y hy))
  have hindg_mem : ∀ y', y' ≠ 0 → MemLp (vg y') p₀' volume :=
    fun y' hy' => memLp_indicator_const p₀' (sg.measurableSet_fiber y') (1 : ℂ)
      (Or.inr (hfibg y' hy'))
  have hindf_memp : ∀ y, y ≠ 0 → MemLp ((sf ⁻¹' {y}).indicator (fun _ => (1 : ℂ))) p volume :=
    fun y hy => memLp_indicator_const p (sf.measurableSet_fiber y) (1 : ℂ) (Or.inr (hfibf y hy))
  have huf_mem : ∀ y, y ≠ 0 → MemLp (uf y) p₀ volume := by
    intro y hy
    have hbound := hT₀ _ (hindf_mem y hy)
    have hmeasy : AEStronglyMeasurable (uf y) volume := hmeas _ (hindf_memp y hy)
    refine ⟨hmeasy, lt_of_le_of_lt hbound ?_⟩
    exact ENNReal.mul_lt_top (by simp) (hindf_mem y hy).2
  -- Integrability of each product `T(𝟙_{fy}) · 𝟙_{gy'}`.
  have hint : ∀ y ∈ sf.range.filter (· ≠ 0), ∀ y' ∈ sg.range.filter (· ≠ 0),
      Integrable (fun x => uf y x * vg y' x) volume := by
    intro y hy y' hy'
    have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
    have hy'0 : y' ≠ 0 := (Finset.mem_filter.mp hy').2
    exact integrable_mul_of_memLp (q := p₀) (q' := p₀') (huf_mem y hy0) (hindg_mem y' hy'0)
  -- The analytic function `F z = ∫ T(f_z)·g_z`, identified with the double sum `G`.
  set coef : ℂ → ℂ → ℂ := fun y y' => ∫ x, uf y x * vg y' x ∂volume with hcoef
  set G := doubleSum P Q (sf.range.filter (· ≠ 0)) (sg.range.filter (· ≠ 0)) coef with hG
  -- Master identity: `∫ T(f_z)·g_z = G z` for every `z`.
  have hFG : ∀ z : ℂ, ∫ x, T (fun x => fpow (P z) (sf x)) x * fpow (Q z) (sg x) ∂volume = G z := by
    intro z
    rw [hG, doubleSum,
      integral_T_fpow_eq_double_sum hadd hsmul sf sg (P z) (Q z) hfibf hint]
  -- `G θ = ∫ T(sf)·sg`.
  have hfθ : (fun x => fpow (P (θ : ℂ)) (sf x)) = (sf : ℂ → ℂ) := by
    ext x; rw [hPθ, fpow_one]
  have hgθ : (fun x => fpow (Q (θ : ℂ)) (sg x)) = (sg : ℂ → ℂ) := by
    ext x; rw [hQθ, fpow_one]
  have hGθ : G (θ : ℂ) = ∫ x, T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x ∂volume := by
    rw [← hFG (θ : ℂ), hfθ]
    congr 1
    ext x; rw [congrFun hgθ x]
  -- Differentiability of `G`.
  have hGdiff : Differentiable ℂ G := by
    rw [hG]; exact differentiable_doubleSum hPdiff hQdiff _ _ _
  have hGdiffcl : DiffContOnCl ℂ G (verticalStrip 0 1) := hGdiff.diffContOnCl
  -- AEStronglyMeasurability of `g_z` for any `z` (it is `fpow ∘ simple`, hence measurable).
  have hg_aesm : ∀ c : ℂ, AEStronglyMeasurable (fun x => fpow c (sg x)) volume :=
    fun c => (memLp_fpow_comp sg c hfibg p').1
  -- AEStronglyMeasurability of `T(f_z)`: `f_z ∈ L^p`, so `hmeas` applies.
  have hTf_aesm : ∀ c : ℂ, AEStronglyMeasurable (T (fun x => fpow c (sf x))) volume :=
    fun c => hmeas _ (memLp_fpow_comp sf c hfibf p)
  -- The `g`-side norm bound at `Re z = 0`.
  have hgnorm0 : ∀ z : ℂ, z.re = 0 →
      eLpNorm (fun x => fpow (Q z) (sg x)) p₀' volume ≤ 1 := by
    intro z hz
    have hcre : (Q z).re = a' * b₀ := hQre0 z hz
    apply eLpNorm_fpow_comp_le_one
    rcases eq_or_lt_of_le hp₀ with hp₀eq | hp₀lt
    · -- p₀ = 1, so b₀ = 0, (Q z).re = 0, p₀' = ⊤
      right
      have hb₀0 : b₀ = 0 := by
        rw [hb₀, ha₀, ← hp₀eq]; simp
      refine ⟨by rw [hcre, hb₀0, mul_zero], ?_⟩
      rw [hp₀'def, ← hp₀eq]; simp
    · -- p₀ > 1
      left
      have hp₀top' : p₀' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p₀' p₀).mpr hp₀lt).ne
      have hp₀'0 : p₀' ≠ 0 := (ENNReal.HolderConjugate.pos p₀' p₀).ne'
      have hp₀toReal_pos : 0 < p₀'.toReal := ENNReal.toReal_pos hp₀'0 hp₀top'
      have hb₀_eq : (p₀'.toReal)⁻¹ = b₀ := by
        rw [hp₀'def, hb₀, ENNReal.toReal_inv, inv_inv,
          ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hp₀) (by simp),
          ENNReal.toReal_one, ENNReal.toReal_inv, ha₀]
      have hb₀pos : 0 < b₀ := by rw [← hb₀_eq]; positivity
      have hcrepos : 0 < (Q z).re := by rw [hcre]; positivity
      refine ⟨hcrepos, ?_⟩
      have hexp_p₀' : p₀' * ENNReal.ofReal ((Q z).re) = p' := by
        rw [hcre]
        apply mul_ofReal_eq hp₀top' hp₀'0 hp'top hp'0 (mul_pos ha'pos hb₀pos).le
        rw [← ha', ← mul_assoc, ← hb₀_eq, mul_comm p₀'.toReal a',
          mul_assoc, mul_inv_cancel₀ hp₀toReal_pos.ne', mul_one]
      rw [hexp_p₀']; exact hg1
  -- The `g`-side norm bound at `Re z = 1`.
  have hgnorm1 : ∀ z : ℂ, z.re = 1 →
      eLpNorm (fun x => fpow (Q z) (sg x)) p₁' volume ≤ 1 := by
    intro z hz
    apply eLpNorm_fpow_comp_le_one
    left
    refine ⟨by rw [hQre1 z hz]; exact hQ1pos, ?_⟩
    rw [hQre1 z hz, hexp_p₁']; exact hg1
  -- The `f`-side norm bounds.
  have hfnorm0 : ∀ z : ℂ, z.re = 0 →
      eLpNorm (fun x => fpow (P z) (sf x)) p₀ volume ≤ 1 := by
    intro z hz
    apply eLpNorm_fpow_comp_le_one
    left
    refine ⟨by rw [hPre0 z hz]; exact haa₀pos, ?_⟩
    rw [hPre0 z hz, hexp_p₀, hf1]
  have hfnorm1 : ∀ z : ℂ, z.re = 1 →
      eLpNorm (fun x => fpow (P z) (sf x)) p₁ volume ≤ 1 := by
    intro z hz
    apply eLpNorm_fpow_comp_le_one
    left
    refine ⟨by rw [hPre1 z hz]; exact haa₁pos, ?_⟩
    rw [hPre1 z hz, hexp_p₁, hf1]
  -- Boundary bound at `Re z = 0`: `‖G z‖ ≤ M₀`.
  have hbd0 : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖G z‖ ≤ (M₀ : ℝ) := by
    intro z hz
    have hz0 : z.re = 0 := hz
    have hge : ‖G z‖ₑ ≤ (M₀ : ℝ≥0∞) := by
      rw [← hFG z]
      exact boundary_enorm_le (q := p₀) (q' := p₀') (T := T)
        (hTf_aesm (P z)) (hg_aesm (Q z))
        (hT₀ _ (memLp_fpow_comp sf (P z) hfibf p₀)) (hfnorm0 z hz0) (hgnorm0 z hz0)
    have : ‖G z‖ ≤ (M₀ : ℝ≥0∞).toReal := by
      rw [← toReal_enorm]; exact ENNReal.toReal_mono (by simp) hge
    simpa using this
  -- Boundary bound at `Re z = 1`: `‖G z‖ ≤ M₁`.
  have hbd1 : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖G z‖ ≤ (M₁ : ℝ) := by
    intro z hz
    have hz1 : z.re = 1 := hz
    have hge : ‖G z‖ₑ ≤ (M₁ : ℝ≥0∞) := by
      rw [← hFG z]
      exact boundary_enorm_le (q := p₁) (q' := p₁') (T := T)
        (hTf_aesm (P z)) (hg_aesm (Q z))
        (hT₁ _ (memLp_fpow_comp sf (P z) hfibf p₁)) (hfnorm1 z hz1) (hgnorm1 z hz1)
    have : ‖G z‖ ≤ (M₁ : ℝ≥0∞).toReal := by
      rw [← toReal_enorm]; exact ENNReal.toReal_mono (by simp) hge
    simpa using this
  -- Boundedness of `‖G‖` on the closed strip.
  have hRf0 : ∀ y ∈ sf.range.filter (· ≠ 0), y ≠ 0 := fun y hy => (Finset.mem_filter.mp hy).2
  have hRg0 : ∀ y' ∈ sg.range.filter (· ≠ 0), y' ≠ 0 := fun y' hy' => (Finset.mem_filter.mp hy').2
  have hBdd : BddAbove ((norm ∘ G) '' verticalClosedStrip 0 1) := by
    refine ⟨∑ y ∈ sf.range.filter (· ≠ 0), ∑ y' ∈ sg.range.filter (· ≠ 0),
        max (‖y‖ ^ min (a / a₀) (a / a₁)) (‖y‖ ^ max (a / a₀) (a / a₁)) *
          max (‖y'‖ ^ min (a' * b₀) (a' * b₁)) (‖y'‖ ^ max (a' * b₀) (a' * b₁)) *
          ‖coef y y'‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Function.comp_apply, hG]
    exact norm_doubleSum_le _ _ coef hRf0 hRg0 hPstrip hQstrip hz
  -- Apply the Hadamard three-lines theorem at `z = θ`.
  have hθmem : (θ : ℂ) ∈ verticalClosedStrip 0 1 := by
    simp only [verticalClosedStrip, Set.mem_preimage, Complex.ofReal_re, Set.mem_Icc]
    exact ⟨hθ0.le, hθ1.le⟩
  have hthree := norm_le_interp_of_mem_verticalClosedStrip' (f := G) (z := (θ : ℂ))
    (a := (M₀ : ℝ)) (b := (M₁ : ℝ)) (l := 0) (u := 1) (by norm_num) hθmem hGdiffcl hBdd hbd0 hbd1
  -- Simplify the exponents.
  rw [Complex.ofReal_re] at hthree
  simp only [sub_zero, div_one] at hthree
  -- `‖∫ T(sf)·sg‖ ≤ M₀^{1-θ} M₁^θ` (real norms).
  rw [hGθ] at hthree
  -- Convert to the `enorm` goal.
  rw [← toReal_enorm] at hthree
  -- The RHS as a real to ℝ≥0∞.
  rw [show ((M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ)
      = ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ) by
    rw [ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]]
  rw [← ENNReal.ofReal_toReal (a := ‖∫ x, T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x ∂volume‖ₑ) (by
    simp [enorm_ne_top])]
  rw [toReal_enorm]
  exact ENNReal.ofReal_le_ofReal hthree

/-- A simple function in `L^p` is in `L^q` for every `q` (finite-measure nonzero fibers). -/
lemma simpleFunc_memLp_of_memLp {p : ℝ≥0∞} {s : MeasureTheory.SimpleFunc ℂ ℂ}
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (hs : MemLp (s : ℂ → ℂ) p volume) (q : ℝ≥0∞) :
    MemLp (s : ℂ → ℂ) q volume :=
  SimpleFunc.memLp_of_finite_measure_preimage q
    (fun y hy => SimpleFunc.measure_preimage_lt_top_of_memLp hp0 hptop s hs y hy)

/-- The homogeneous pairing bound for simple `sg`: `‖∫ T(sf)·sg‖ₑ ≤ M·eLpNorm sg p'`,
where `M = M₀^{1-θ}M₁^θ`, derived from `three_lines_bound` by scaling `sg`. -/
lemma pairing_simple_g
    {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ p : ℝ≥0∞} {M₀ M₁ : ℝ≥0} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₀top : p₀ ≠ ⊤) (hp₁ : 1 ≤ p₁) (hp₁top : p₁ ≠ ⊤) (hp₀p₁ : p₀ < p₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hmeas : ∀ s : ℂ → ℂ, MemLp s p volume → AEStronglyMeasurable (T s) volume)
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (hT₀ : ∀ s : ℂ → ℂ, MemLp s p₀ volume → eLpNorm (T s) p₀ volume ≤ M₀ * eLpNorm s p₀ volume)
    (hT₁ : ∀ s : ℂ → ℂ, MemLp s p₁ volume → eLpNorm (T s) p₁ volume ≤ M₁ * eLpNorm s p₁ volume)
    (sf sg : MeasureTheory.SimpleFunc ℂ ℂ)
    (hfmem : MemLp (sf : ℂ → ℂ) p volume) (hf1 : eLpNorm (sf : ℂ → ℂ) p volume = 1)
    (hgmem : MemLp (sg : ℂ → ℂ) (1 - p⁻¹)⁻¹ volume) :
    ‖∫ x, T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x ∂volume‖ₑ
      ≤ ((M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ) * eLpNorm (sg : ℂ → ℂ) (1 - p⁻¹)⁻¹ volume := by
  obtain ⟨_, _, h1p⟩ := p_ne_top_of_interp hp₀ hp₁ hp₁top hθ hp
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'def
  set M : ℝ≥0∞ := (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ with hM
  set d : ℝ≥0∞ := eLpNorm (sg : ℂ → ℂ) p' volume with hd
  have hdtop : d ≠ ⊤ := hgmem.2.ne
  have hp'0 : p' ≠ 0 := by rw [hp'def]; exact (holderConjugate_inv h1p).symm.ne_zero
  rcases eq_or_ne d 0 with hd0 | hd0
  · -- `sg =ᵐ 0`, so the integral vanishes.
    have hsg0 : (sg : ℂ → ℂ) =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff hgmem.1 hp'0).mp hd0
    have hae : (fun x => T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x) =ᵐ[volume] fun _ => 0 := by
      filter_upwards [hsg0] with x hx; rw [hx]; simp
    rw [integral_congr_ae hae]
    simp [hd0]
  · -- Scale `sg` by `d⁻¹` (real positive).
    have hdrpos : 0 < d.toReal := ENNReal.toReal_pos hd0 hdtop
    set dr : ℝ := d.toReal with hdr
    have hnorm_inv : ‖(dr⁻¹ : ℂ)‖ₑ = ENNReal.ofReal dr⁻¹ := by
      rw [show (dr⁻¹ : ℂ) = ((dr⁻¹ : ℝ) : ℂ) by push_cast; ring, ← ofReal_norm,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    set sg' : MeasureTheory.SimpleFunc ℂ ℂ := (dr⁻¹ : ℂ) • sg with hsg'
    have hcoe : (sg' : ℂ → ℂ) = (dr⁻¹ : ℂ) • (sg : ℂ → ℂ) := SimpleFunc.coe_smul _ _
    have hsg'mem : MemLp (sg' : ℂ → ℂ) p' volume := by rw [hcoe]; exact hgmem.const_smul _
    have hsg'norm : eLpNorm (sg' : ℂ → ℂ) p' volume ≤ 1 := by
      rw [hcoe, eLpNorm_const_smul, hnorm_inv, ← hd]
      rw [show d = ENNReal.ofReal dr by rw [hdr, ENNReal.ofReal_toReal hdtop],
        ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hdrpos.ne', ENNReal.ofReal_one]
    have hbound := three_lines_bound hp₀ hp₀top hp₁ hp₁top hp₀p₁ hθ hp hmeas hadd hsmul hT₀ hT₁
      sf sg' hfmem hf1 hsg'mem hsg'norm
    -- Unscale: `∫ T(sf)·sg' = d⁻¹ · ∫ T(sf)·sg`.
    have hintsg' : (∫ x, T (sf : ℂ → ℂ) x * (sg' : ℂ → ℂ) x ∂volume)
        = (dr⁻¹ : ℂ) * ∫ x, T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x ∂volume := by
      rw [show (∫ x, T (sf : ℂ → ℂ) x * (sg' : ℂ → ℂ) x ∂volume)
            = ∫ x, (dr⁻¹ : ℂ) * (T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x) ∂volume from by
          congr 1; ext x; rw [hcoe]; simp only [Pi.smul_apply, smul_eq_mul]; ring]
      exact integral_const_mul (dr⁻¹ : ℂ) (fun x => T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x)
    rw [hintsg', enorm_mul, hnorm_inv] at hbound
    -- Conclude by multiplying both sides by `d`.
    rw [show d = ENNReal.ofReal dr by rw [hdr, ENNReal.ofReal_toReal hdtop]]
    calc ‖∫ x, T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x ∂volume‖ₑ
        = ENNReal.ofReal dr *
            (ENNReal.ofReal dr⁻¹ * ‖∫ x, T (sf : ℂ → ℂ) x * (sg : ℂ → ℂ) x ∂volume‖ₑ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ hdrpos.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal dr * M := by gcongr
      _ = M * ENNReal.ofReal dr := mul_comm _ _

/-- **Core simple-function bound (normalized).** For simple `sf` with `eLpNorm sf p = 1` and
`p₀ < p₁`, the operator bound `eLpNorm (T sf) p ≤ M₀^{1-θ} M₁^θ` holds. -/
lemma core_normalized
    {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ p : ℝ≥0∞} {M₀ M₁ : ℝ≥0} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₀top : p₀ ≠ ⊤) (hp₁ : 1 ≤ p₁) (hp₁top : p₁ ≠ ⊤) (hp₀p₁ : p₀ < p₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hmeas : ∀ s : ℂ → ℂ, MemLp s p volume → AEStronglyMeasurable (T s) volume)
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (hT₀ : ∀ s : ℂ → ℂ, MemLp s p₀ volume → eLpNorm (T s) p₀ volume ≤ M₀ * eLpNorm s p₀ volume)
    (hT₁ : ∀ s : ℂ → ℂ, MemLp s p₁ volume → eLpNorm (T s) p₁ volume ≤ M₁ * eLpNorm s p₁ volume)
    (sf : MeasureTheory.SimpleFunc ℂ ℂ)
    (hfmem : MemLp (sf : ℂ → ℂ) p volume) (hf1 : eLpNorm (sf : ℂ → ℂ) p volume = 1) :
    eLpNorm (T (sf : ℂ → ℂ)) p volume ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ := by
  obtain ⟨hptop, hp0, h1p⟩ := p_ne_top_of_interp hp₀ hp₁ hp₁top hθ hp
  have h1p_lt : 1 < p := by
    -- from `three_lines_bound` setup we know `p > 1`; re-derive here briefly.
    rcases lt_or_eq_of_le h1p with h | h
    · exact h
    · exfalso
      -- `p = 1` forces the conjugate `p' = ⊤`; but we don't need this path: `p₀ < p₁` and the
      -- interpolation give `p > 1`. Use the real argument.
      have hp₀0 : p₀ ≠ 0 := (lt_of_lt_of_le one_pos hp₀).ne'
      have hp₁0 : p₁ ≠ 0 := (lt_of_lt_of_le one_pos hp₁).ne'
      have hinterp := toReal_interp hp₀top hp₁top hp₀0 hp₁0 hptop hp0 hθ hp
      have ha₀a₁ : p₀.toReal < p₁.toReal := (ENNReal.toReal_lt_toReal hp₀top hp₁top).mpr hp₀p₁
      have h1a₀ : (1 : ℝ) ≤ p₀.toReal := by
        rw [show (1:ℝ) = (1:ℝ≥0∞).toReal by simp]
        exact (ENNReal.toReal_le_toReal (by simp) hp₀top).mpr hp₀
      have h1a₁ : (1 : ℝ) ≤ p₁.toReal := by
        rw [show (1:ℝ) = (1:ℝ≥0∞).toReal by simp]
        exact (ENNReal.toReal_le_toReal (by simp) hp₁top).mpr hp₁
      have ha₀pos : 0 < p₀.toReal := ENNReal.toReal_pos hp₀0 hp₀top
      have ha₁pos : 0 < p₁.toReal := ENNReal.toReal_pos hp₁0 hp₁top
      obtain ⟨hθ0, hθ1⟩ := hθ
      have hpa : p.toReal = 1 := by rw [← h]; simp
      rw [hpa] at hinterp; simp only [inv_one] at hinterp
      -- `1 = (1-θ)/a₀ + θ/a₁ < 1` if either `a₀ > 1` or `a₁ > 1`; contradiction.
      rcases eq_or_lt_of_le h1a₀ with ha₀1 | ha₀1
      · have ha₁1 : 1 < p₁.toReal := by rw [← ha₀1] at ha₀a₁; exact ha₀a₁
        have hinv0 : (p₀.toReal)⁻¹ = 1 := by rw [← ha₀1]; simp
        have : θ * (p₁.toReal)⁻¹ < θ := by
          have := mul_lt_mul_of_pos_left (inv_lt_one₀ ha₁pos |>.mpr ha₁1) hθ0
          rwa [mul_one] at this
        rw [hinv0, mul_one] at hinterp
        linarith
      · have h1θpos : (0 : ℝ) < 1 - θ := by linarith
        have : (1 - θ) * (p₀.toReal)⁻¹ < (1 - θ) := by
          have := mul_lt_mul_of_pos_left (inv_lt_one₀ ha₀pos |>.mpr ha₀1) h1θpos
          rwa [mul_one] at this
        have h2 : θ * (p₁.toReal)⁻¹ ≤ θ := by
          have := mul_le_mul_of_nonneg_left (inv_le_one₀ ha₁pos |>.mpr h1a₁) hθ0.le
          rwa [mul_one] at this
        nlinarith [hinterp]
  -- The conjugate exponent `p'`.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'def
  have hpp' : ENNReal.HolderConjugate p p' := holderConjugate_inv h1p
  have hp'top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr h1p_lt).ne
  -- `T sf ∈ L^p` via `L^{p₀} ∩ L^{p₁}`.
  have hsf₀ : MemLp (sf : ℂ → ℂ) p₀ volume :=
    simpleFunc_memLp_of_memLp hp0 hptop hfmem p₀
  have hsf₁ : MemLp (sf : ℂ → ℂ) p₁ volume :=
    simpleFunc_memLp_of_memLp hp0 hptop hfmem p₁
  have hTsf_aesm : AEStronglyMeasurable (T (sf : ℂ → ℂ)) volume := hmeas _ hfmem
  have hTsf₀ : MemLp (T (sf : ℂ → ℂ)) p₀ volume :=
    ⟨hTsf_aesm, lt_of_le_of_lt (hT₀ _ hsf₀) (ENNReal.mul_lt_top (by simp) hsf₀.2)⟩
  have hTsf₁ : MemLp (T (sf : ℂ → ℂ)) p₁ volume :=
    ⟨hTsf_aesm, lt_of_le_of_lt (hT₁ _ hsf₁) (ENNReal.mul_lt_top (by simp) hsf₁.2)⟩
  have hp₀0 : p₀ ≠ 0 := (lt_of_lt_of_le one_pos hp₀).ne'
  -- `p₀ ≤ p ≤ p₁` from the convex-combination relation on inverses.
  have hinv_le₀ : p⁻¹ ≤ p₀⁻¹ := by
    rw [hp]
    have h1 : ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹
        ≤ ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₀⁻¹ := by
      gcongr
    refine h1.trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith [hθ.2]) hθ.1.le, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  have hinv_le₁ : p₁⁻¹ ≤ p⁻¹ := by
    rw [hp]
    have h1 : ENNReal.ofReal (1 - θ) * p₁⁻¹ + ENNReal.ofReal θ * p₁⁻¹
        ≤ ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹ := by
      gcongr
    refine le_trans ?_ h1
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith [hθ.2]) hθ.1.le, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  have hp₀p : p₀ ≤ p := ENNReal.inv_le_inv.mp hinv_le₀
  have hpp₁ : p ≤ p₁ := ENNReal.inv_le_inv.mp hinv_le₁
  have hTsf : MemLp (T (sf : ℂ → ℂ)) p volume :=
    memLp_of_memLp_memLp hp₀0 hp₁top hp₀p hpp₁ hTsf₀ hTsf₁
  set M : ℝ≥0∞ := (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ with hMdef
  have hMtop : M ≠ ⊤ := by
    rw [hMdef]
    apply ENNReal.mul_ne_top <;>
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith [hθ.1, hθ.2]) (by simp)
  -- Pairing bound for all `g ∈ L^{p'}`.
  have hpairing : ∀ g : ℂ → ℂ, MemLp g p' volume →
      ‖∫ x, T (sf : ℂ → ℂ) x * g x ∂volume‖ₑ ≤ M * eLpNorm g p' volume := by
    apply pairing_le_of_simple (p := p) (p' := p') (M := M) hp'top hTsf hMtop
    intro sg hsg
    rw [hMdef]
    exact pairing_simple_g hp₀ hp₀top hp₁ hp₁top hp₀p₁ hθ hp hmeas hadd hsmul hT₀ hT₁
      sf sg hfmem hf1 hsg
  -- Apply the duality lower bound.
  calc eLpNorm (T (sf : ℂ → ℂ)) p volume
      ≤ ⨆ (g : ℂ → ℂ) (_ : MemLp g p' volume) (_ : eLpNorm g p' volume ≤ 1),
          ‖∫ x, T (sf : ℂ → ℂ) x * g x ∂volume‖ₑ :=
        eLpNorm_le_iSup_integral_mul h1p_lt hptop hTsf
    _ ≤ M := by
        refine iSup₂_le (fun g hg => iSup_le (fun hg1 => ?_))
        refine le_trans (hpairing g hg) ?_
        calc M * eLpNorm g p' volume ≤ M * 1 := by gcongr
          _ = M := mul_one _

/-- **Core simple-function bound (general).** For any simple `sf ∈ L^p` with `p₀ < p₁`,
`eLpNorm (T sf) p ≤ M₀^{1-θ}M₁^θ · eLpNorm sf p`. -/
lemma core_simple
    {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ p : ℝ≥0∞} {M₀ M₁ : ℝ≥0} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₀top : p₀ ≠ ⊤) (hp₁ : 1 ≤ p₁) (hp₁top : p₁ ≠ ⊤) (hp₀p₁ : p₀ < p₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hmeas : ∀ s : ℂ → ℂ, MemLp s p volume → AEStronglyMeasurable (T s) volume)
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (hT₀ : ∀ s : ℂ → ℂ, MemLp s p₀ volume → eLpNorm (T s) p₀ volume ≤ M₀ * eLpNorm s p₀ volume)
    (hT₁ : ∀ s : ℂ → ℂ, MemLp s p₁ volume → eLpNorm (T s) p₁ volume ≤ M₁ * eLpNorm s p₁ volume)
    (sf : MeasureTheory.SimpleFunc ℂ ℂ) (hfmem : MemLp (sf : ℂ → ℂ) p volume) :
    eLpNorm (T (sf : ℂ → ℂ)) p volume
      ≤ ((M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ) * eLpNorm (sf : ℂ → ℂ) p volume := by
  obtain ⟨hptop, hp0, h1p⟩ := p_ne_top_of_interp hp₀ hp₁ hp₁top hθ hp
  set M : ℝ≥0∞ := (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ with hMdef
  have hp₀0 : p₀ ≠ 0 := (lt_of_lt_of_le one_pos hp₀).ne'
  set c : ℝ≥0∞ := eLpNorm (sf : ℂ → ℂ) p volume with hc
  have hctop : c ≠ ⊤ := hfmem.2.ne
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- `sf =ᵐ 0`: then `eLpNorm (T sf) p₀ = 0`, so `T sf =ᵐ 0`, hence `eLpNorm (T sf) p = 0`.
    have hsf0 : (sf : ℂ → ℂ) =ᵐ[volume] 0 := (eLpNorm_eq_zero_iff hfmem.1 hp0).mp hc0
    have hsf₀ : MemLp (sf : ℂ → ℂ) p₀ volume := simpleFunc_memLp_of_memLp hp0 hptop hfmem p₀
    have hsfp₀0 : eLpNorm (sf : ℂ → ℂ) p₀ volume = 0 := eLpNorm_eq_zero_of_ae_zero hsf0
    have hTsf₀0 : eLpNorm (T (sf : ℂ → ℂ)) p₀ volume = 0 := by
      have := hT₀ _ hsf₀; rw [hsfp₀0, mul_zero] at this
      exact le_antisymm this (zero_le)
    have hTsf0 : T (sf : ℂ → ℂ) =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff (hmeas _ hfmem) hp₀0).mp hTsf₀0
    rw [eLpNorm_eq_zero_of_ae_zero hTsf0]
    exact zero_le
  · -- Scale `sf` to norm 1.
    have hcrpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
    set cr : ℝ := c.toReal with hcr
    set sf' : MeasureTheory.SimpleFunc ℂ ℂ := (cr⁻¹ : ℂ) • sf with hsf'
    have hcoe : (sf' : ℂ → ℂ) = (cr⁻¹ : ℂ) • (sf : ℂ → ℂ) := SimpleFunc.coe_smul _ _
    have hnorm_inv : ‖(cr⁻¹ : ℂ)‖ₑ = ENNReal.ofReal cr⁻¹ := by
      rw [show (cr⁻¹ : ℂ) = ((cr⁻¹ : ℝ) : ℂ) by push_cast; ring, ← ofReal_norm,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hsf'mem : MemLp (sf' : ℂ → ℂ) p volume := by rw [hcoe]; exact hfmem.const_smul _
    have hsf'1 : eLpNorm (sf' : ℂ → ℂ) p volume = 1 := by
      rw [hcoe, eLpNorm_const_smul, hnorm_inv, ← hc,
        show c = ENNReal.ofReal cr by rw [hcr, ENNReal.ofReal_toReal hctop],
        ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hcrpos.ne', ENNReal.ofReal_one]
    have hbound := core_normalized hp₀ hp₀top hp₁ hp₁top hp₀p₁ hθ hp hmeas hadd hsmul hT₀ hT₁
      sf' hsf'mem hsf'1
    rw [← hMdef] at hbound
    -- `T sf' =ᵐ cr⁻¹ • T sf`.
    have hTsf' : T (sf' : ℂ → ℂ) =ᵐ[volume] (cr⁻¹ : ℂ) • T (sf : ℂ → ℂ) := by
      have := hsmul (cr⁻¹ : ℂ) (sf : ℂ → ℂ)
        (Or.inl (simpleFunc_memLp_of_memLp hp0 hptop hfmem p₀))
      rw [← hcoe] at this
      exact this
    rw [eLpNorm_congr_ae hTsf', eLpNorm_const_smul, hnorm_inv] at hbound
    -- Multiply through by `c = ofReal cr`.
    rw [show c = ENNReal.ofReal cr by rw [hcr, ENNReal.ofReal_toReal hctop]]
    calc eLpNorm (T (sf : ℂ → ℂ)) p volume
        = ENNReal.ofReal cr * (ENNReal.ofReal cr⁻¹ * eLpNorm (T (sf : ℂ → ℂ)) p volume) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ hcrpos.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal cr * M := by gcongr
      _ = M * ENNReal.ofReal cr := mul_comm _ _

/-- A.e.-subtractivity of `T` on functions in `L^{p₀} ∪ L^{p₁}`. -/
lemma T_sub_ae
    {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ : ℝ≥0∞}
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    {s t : ℂ → ℂ} (hs : MemLp s p₀ volume ∨ MemLp s p₁ volume)
    (ht : MemLp t p₀ volume ∨ MemLp t p₁ volume) :
    T (s - t) =ᵐ[volume] T s - T t := by
  have hnegt : MemLp ((-1 : ℂ) • t) p₀ volume ∨ MemLp ((-1 : ℂ) • t) p₁ volume :=
    ht.imp (fun h => h.const_smul _) (fun h => h.const_smul _)
  have h1 : T (s + (-1 : ℂ) • t) =ᵐ[volume] T s + T ((-1 : ℂ) • t) := hadd s _ hs hnegt
  have h2 : T ((-1 : ℂ) • t) =ᵐ[volume] (-1 : ℂ) • T t := hsmul (-1 : ℂ) t ht
  have hst : s - t = s + (-1 : ℂ) • t := by ext x; simp; ring
  rw [hst]
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx1 hx2 ⊢
  rw [hx1, hx2]
  ring

/-- The constant `M₀^{1-θ} M₁^θ` (NNReal, coerced) equals the ENNReal product of rpows. -/
lemma coe_const_eq {M₀ M₁ : ℝ≥0} {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    ((M₀ ^ (1 - θ) * M₁ ^ θ : ℝ≥0) : ℝ≥0∞)
      = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h1θ : (0:ℝ) < 1 - θ := by linarith
  rw [ENNReal.coe_mul]
  congr 1
  · rcases eq_or_ne M₀ 0 with h | h
    · subst h; rw [NNReal.zero_rpow h1θ.ne', ENNReal.coe_zero, ENNReal.zero_rpow_of_pos h1θ]
    · rw [ENNReal.coe_rpow_of_ne_zero h]
  · rcases eq_or_ne M₁ 0 with h | h
    · subst h; rw [NNReal.zero_rpow hθ0.ne', ENNReal.coe_zero, ENNReal.zero_rpow_of_pos hθ0]
    · rw [ENNReal.coe_rpow_of_ne_zero h]

/-- **Density step (`p₀ < p₁`).** The operator bound extends from simple functions to all of
`L^p`. -/
lemma core
    {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ p : ℝ≥0∞} {M₀ M₁ : ℝ≥0} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₀top : p₀ ≠ ⊤) (hp₁ : 1 ≤ p₁) (hp₁top : p₁ ≠ ⊤) (hp₀p₁ : p₀ < p₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hmeas : ∀ s : ℂ → ℂ, MemLp s p volume → AEStronglyMeasurable (T s) volume)
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (hT₀ : ∀ s : ℂ → ℂ, MemLp s p₀ volume → eLpNorm (T s) p₀ volume ≤ M₀ * eLpNorm s p₀ volume)
    (hT₁ : ∀ s : ℂ → ℂ, MemLp s p₁ volume → eLpNorm (T s) p₁ volume ≤ M₁ * eLpNorm s p₁ volume)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    eLpNorm (T f) p volume ≤ (M₀ ^ (1 - θ) * M₁ ^ θ : ℝ≥0) * eLpNorm f p volume := by
  classical
  obtain ⟨hptop, hp0, h1p⟩ := p_ne_top_of_interp hp₀ hp₁ hp₁top hθ hp
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h1θ : (0:ℝ) < 1 - θ := by linarith
  have hp₀0 : p₀ ≠ 0 := (lt_of_lt_of_le one_pos hp₀).ne'
  have hp₁0 : p₁ ≠ 0 := (lt_of_lt_of_le one_pos hp₁).ne'
  -- Reduce the goal constant to the ENNReal product `M`.
  set M : ℝ≥0∞ := (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ with hMdef
  have hMtop : M ≠ ⊤ := by
    rw [hMdef]
    apply ENNReal.mul_ne_top <;> exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  rw [coe_const_eq ⟨hθ0, hθ1⟩, ← hMdef]
  -- `p₀ ≤ p ≤ p₁` from the convex-combination relation on inverses.
  have hinv_le₀ : p⁻¹ ≤ p₀⁻¹ := by
    rw [hp]
    have h1 : ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹
        ≤ ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₀⁻¹ := by gcongr
    refine h1.trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith) hθ0.le, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  have hinv_le₁ : p₁⁻¹ ≤ p⁻¹ := by
    rw [hp]
    have h1 : ENNReal.ofReal (1 - θ) * p₁⁻¹ + ENNReal.ofReal θ * p₁⁻¹
        ≤ ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹ := by gcongr
    refine le_trans ?_ h1
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith) hθ0.le, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  have hp₀p : p₀ ≤ p := ENNReal.inv_le_inv.mp hinv_le₀
  have hpp₁ : p ≤ p₁ := ENNReal.inv_le_inv.mp hinv_le₁
  -- Positive real exponents and the ratio `p.toReal / p₀.toReal`, `p.toReal / p₁.toReal`.
  have ha₀pos : 0 < p₀.toReal := ENNReal.toReal_pos hp₀0 hp₀top
  have ha₁pos : 0 < p₁.toReal := ENNReal.toReal_pos hp₁0 hp₁top
  have hapos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  -- Step 1: a sequence of simple functions approximating `f` in `L^p`, with errors `< 2^{-(n+1)}`.
  set ε : ℕ → ℝ≥0∞ := fun n => (2 : ℝ≥0∞)⁻¹ ^ (n + 1) with hε
  have hεpos : ∀ n, ε n ≠ 0 := fun n => by
    rw [hε]; exact pow_ne_zero _ (by simp)
  have hchoose : ∀ n, ∃ g : MeasureTheory.SimpleFunc ℂ ℂ,
      eLpNorm (f - (g : ℂ → ℂ)) p volume < ε n ∧ MemLp (g : ℂ → ℂ) p volume :=
    fun n => hf.exists_simpleFunc_eLpNorm_sub_lt hptop (hεpos n)
  set s : ℕ → MeasureTheory.SimpleFunc ℂ ℂ := fun n => (hchoose n).choose with hs
  have hs_lt : ∀ n, eLpNorm (f - (s n : ℂ → ℂ)) p volume < ε n :=
    fun n => (hchoose n).choose_spec.1
  have hs_mem : ∀ n, MemLp (s n : ℂ → ℂ) p volume := fun n => (hchoose n).choose_spec.2
  -- Memberships at `p₀, p₁` for each simple function.
  have hs_mem₀ : ∀ n, MemLp (s n : ℂ → ℂ) p₀ volume :=
    fun n => simpleFunc_memLp_of_memLp hp0 hptop (hs_mem n) p₀
  have hs_mem₁ : ∀ n, MemLp (s n : ℂ → ℂ) p₁ volume :=
    fun n => simpleFunc_memLp_of_memLp hp0 hptop (hs_mem n) p₁
  have hTs_aesm : ∀ n, AEStronglyMeasurable (T (s n : ℂ → ℂ)) volume :=
    fun n => hmeas _ (hs_mem n)
  -- `eLpNorm (s n - f) p < ε n`.
  have hs_lt' : ∀ n, eLpNorm ((s n : ℂ → ℂ) - f) p volume < ε n := by
    intro n; rw [eLpNorm_sub_comm]; exact hs_lt n
  -- Step 2: the operator-image difference bound.
  have hTdiff : ∀ n m, eLpNorm (T (s n : ℂ → ℂ) - T (s m : ℂ → ℂ)) p volume
      ≤ M * (ε n + ε m) := by
    intro n m
    -- `T (s n - s m) =ᵐ T (s n) - T (s m)`.
    have hTsub : T ((s n : ℂ → ℂ) - (s m : ℂ → ℂ)) =ᵐ[volume]
        T (s n : ℂ → ℂ) - T (s m : ℂ → ℂ) :=
      T_sub_ae hadd hsmul (Or.inl (hs_mem₀ n)) (Or.inl (hs_mem₀ m))
    -- `(s n : ℂ→ℂ) - (s m : ℂ→ℂ)` as a simple function.
    have hcoe : ((s n - s m : MeasureTheory.SimpleFunc ℂ ℂ) : ℂ → ℂ)
        = (s n : ℂ → ℂ) - (s m : ℂ → ℂ) := SimpleFunc.coe_sub _ _
    have hmemd : MemLp ((s n - s m : MeasureTheory.SimpleFunc ℂ ℂ) : ℂ → ℂ) p volume := by
      rw [hcoe]; exact (hs_mem n).sub (hs_mem m)
    have hcs := core_simple hp₀ hp₀top hp₁ hp₁top hp₀p₁ ⟨hθ0, hθ1⟩ hp hmeas hadd hsmul hT₀ hT₁
      (s n - s m) hmemd
    rw [hcoe, ← hMdef] at hcs
    -- bound `eLpNorm ((s n) - (s m)) p ≤ ε n + ε m`.
    have htri : eLpNorm ((s n : ℂ → ℂ) - (s m : ℂ → ℂ)) p volume ≤ ε n + ε m := by
      have hsplit : (s n : ℂ → ℂ) - (s m : ℂ → ℂ)
          = ((s n : ℂ → ℂ) - f) + (f - (s m : ℂ → ℂ)) := by
        ext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
      rw [hsplit]
      refine le_trans (eLpNorm_add_le ((hs_mem n).1.sub hf.1) (hf.1.sub (hs_mem m).1) h1p) ?_
      gcongr
      · exact (hs_lt' n).le
      · exact (hs_lt m).le
    calc eLpNorm (T (s n : ℂ → ℂ) - T (s m : ℂ → ℂ)) p volume
        = eLpNorm (T ((s n : ℂ → ℂ) - (s m : ℂ → ℂ))) p volume :=
          (eLpNorm_congr_ae hTsub).symm
      _ ≤ M * eLpNorm ((s n : ℂ → ℂ) - (s m : ℂ → ℂ)) p volume := hcs
      _ ≤ M * (ε n + ε m) := by gcongr
  -- Step 3: the Cauchy bound and the a.e. limit.
  set B : ℕ → ℝ≥0∞ := fun N => (M + 1) * (2 : ℝ≥0∞)⁻¹ ^ N with hB
  have hBsum : ∑' N, B N ≠ ⊤ := by
    rw [hB, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    finiteness
  have h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (T (s n : ℂ → ℂ) - T (s m : ℂ → ℂ)) p volume < B N := by
    intro N n m hn hm
    have hεmono : ∀ k, N ≤ k → ε k ≤ (2 : ℝ≥0∞)⁻¹ ^ (N + 1) := by
      intro k hk
      rw [hε]
      exact pow_le_pow_right_of_le_one' (by simp) (by omega)
    have hsum_le : ε n + ε m ≤ (2 : ℝ≥0∞)⁻¹ ^ N := by
      calc ε n + ε m ≤ (2 : ℝ≥0∞)⁻¹ ^ (N + 1) + (2 : ℝ≥0∞)⁻¹ ^ (N + 1) :=
            add_le_add (hεmono n hn) (hεmono m hm)
        _ = (2 : ℝ≥0∞)⁻¹ ^ N := by
            have h2 : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
              ENNReal.mul_inv_cancel (by simp) (by simp)
            rw [← two_mul, pow_succ]
            calc (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ N * (2 : ℝ≥0∞)⁻¹)
                = ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * (2 : ℝ≥0∞)⁻¹ ^ N := by ring
              _ = (2 : ℝ≥0∞)⁻¹ ^ N := by rw [h2, one_mul]
    have hc0 : (2 : ℝ≥0∞)⁻¹ ^ N ≠ 0 := pow_ne_zero _ (by simp)
    have hMfin : M * (2 : ℝ≥0∞)⁻¹ ^ N ≠ ⊤ := by finiteness
    calc eLpNorm (T (s n : ℂ → ℂ) - T (s m : ℂ → ℂ)) p volume
        ≤ M * (ε n + ε m) := hTdiff n m
      _ ≤ M * (2 : ℝ≥0∞)⁻¹ ^ N := by gcongr
      _ < (M + 1) * (2 : ℝ≥0∞)⁻¹ ^ N := by
          rw [add_mul, one_mul]
          exact ENNReal.lt_add_right hMfin (by positivity)
  have h_ae_ex : ∀ᵐ x ∂volume, ∃ l : ℂ, atTop.Tendsto (fun n => T (s n : ℂ → ℂ) x) (𝓝 l) :=
    MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm hTs_aesm h1p hBsum h_cau
  -- Define the limit function `h`.
  set h : ℂ → ℂ := fun x => if hx : ∃ l : ℂ, atTop.Tendsto (fun n => T (s n : ℂ → ℂ) x) (𝓝 l)
      then hx.choose else 0 with hh
  have h_tendsto : ∀ᵐ x ∂volume, atTop.Tendsto (fun n => T (s n : ℂ → ℂ) x) (𝓝 (h x)) := by
    filter_upwards [h_ae_ex] with x hx
    rw [hh]; dsimp only; rw [dif_pos hx]
    exact hx.choose_spec
  -- Step 4: `eLpNorm h p ≤ M * eLpNorm f p`.
  set Cf : ℝ≥0∞ := M * eLpNorm f p volume with hCf
  -- For each `n`, `eLpNorm (T (s n)) p ≤ M * (eLpNorm f p + ε n)`.
  have hTsn_bound : ∀ n, eLpNorm (T (s n : ℂ → ℂ)) p volume ≤ M * (eLpNorm f p volume + ε n) := by
    intro n
    have hcs := core_simple hp₀ hp₀top hp₁ hp₁top hp₀p₁ ⟨hθ0, hθ1⟩ hp hmeas hadd hsmul hT₀ hT₁
      (s n) (hs_mem n)
    rw [← hMdef] at hcs
    have htri : eLpNorm (s n : ℂ → ℂ) p volume ≤ eLpNorm f p volume + ε n := by
      have hsplit : (s n : ℂ → ℂ) = f + ((s n : ℂ → ℂ) - f) := by
        ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [hsplit]
      refine le_trans (eLpNorm_add_le hf.1 ((hs_mem n).1.sub hf.1) h1p) ?_
      gcongr
      exact (hs_lt' n).le
    calc eLpNorm (T (s n : ℂ → ℂ)) p volume
        ≤ M * eLpNorm (s n : ℂ → ℂ) p volume := hcs
      _ ≤ M * (eLpNorm f p volume + ε n) := by gcongr
  -- `M * (eLpNorm f p + ε n) → Cf`.
  have hε_tendsto : atTop.Tendsto ε (𝓝 0) := by
    have hpow : atTop.Tendsto (fun n => (2 : ℝ≥0∞)⁻¹ ^ n) (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hmul := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)⁻¹) hpow
      (Or.inr (show (2 : ℝ≥0∞)⁻¹ ≠ ⊤ by simp))
    rw [mul_zero] at hmul
    have heq : (fun n => (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ n) = ε := by
      funext n; rw [hε]; rw [← pow_succ']
    rwa [heq] at hmul
  have hbound_tendsto : atTop.Tendsto (fun n => M * (eLpNorm f p volume + ε n)) (𝓝 Cf) := by
    rw [hCf]
    have h1 : atTop.Tendsto (fun n => eLpNorm f p volume + ε n) (𝓝 (eLpNorm f p volume + 0)) :=
      Filter.Tendsto.add tendsto_const_nhds hε_tendsto
    rw [add_zero] at h1
    exact ENNReal.Tendsto.const_mul h1 (Or.inr hMtop)
  have hCftop : Cf ≠ ⊤ := by rw [hCf]; finiteness
  have hh_bound : eLpNorm h p volume ≤ Cf := by
    refine ENNReal.le_of_forall_pos_le_add (fun δ hδ _ => ?_)
    have hev : ∀ᶠ n in atTop, eLpNorm (T (s n : ℂ → ℂ)) p volume ≤ Cf + δ := by
      have hlt : Cf < Cf + δ := ENNReal.lt_add_right hCftop (by simpa using hδ.ne')
      filter_upwards [hbound_tendsto.eventually_lt_const hlt] with n hn
      exact (hTsn_bound n).trans hn.le
    exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto hev hTs_aesm h_tendsto
  -- Step 5: `h =ᵐ T f`.
  -- The error and its truncations.
  set r : ℕ → ℂ → ℂ := fun n => f - (s n : ℂ → ℂ) with hr
  have hr_mem : ∀ n, MemLp (r n) p volume := fun n => hf.sub (hs_mem n)
  have hr_lt : ∀ n, eLpNorm (r n) p volume < ε n := hs_lt
  set b : ℕ → ℂ → ℂ := fun n => MeasureTheory.truncCompl (r n) 1 with hbdef
  set g : ℕ → ℂ → ℂ := fun n => MeasureTheory.trunc (r n) 1 with hgdef
  -- Memberships of the truncations.
  have hb_mem : ∀ n, MemLp (b n) p₀ volume := by
    intro n
    refine ⟨(hr_mem n).1.truncCompl, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_truncCompl_le hp₀0 hp₀top hp0 hptop hp₀p) ?_
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (hr_mem n).2.ne
  have hg_mem : ∀ n, MemLp (g n) p₁ volume := by
    intro n
    refine ⟨(hr_mem n).1.trunc, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_trunc_le hp₁0 hp₁top hp0 hptop hpp₁) ?_
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (hr_mem n).2.ne
  -- The bounds on `T b n` and `T g n`.
  have hTb_bound : ∀ n,
      eLpNorm (T (b n)) p₀ volume ≤ M₀ * eLpNorm (r n) p volume ^ (p.toReal / p₀.toReal) := by
    intro n
    refine le_trans (hT₀ _ (hb_mem n)) ?_
    gcongr
    exact eLpNorm_truncCompl_le hp₀0 hp₀top hp0 hptop hp₀p
  have hTg_bound : ∀ n,
      eLpNorm (T (g n)) p₁ volume ≤ M₁ * eLpNorm (r n) p volume ^ (p.toReal / p₁.toReal) := by
    intro n
    refine le_trans (hT₁ _ (hg_mem n)) ?_
    gcongr
    exact eLpNorm_trunc_le hp₁0 hp₁top hp0 hptop hpp₁
  -- The decomposition `T f - T (s n) =ᵐ T (b n) + T (g n)`.
  have hdecomp : ∀ n, T f - T (s n : ℂ → ℂ) =ᵐ[volume] T (b n) + T (g n) := by
    intro n
    -- `f = ((s n) + b n) + g n` as functions.
    have hfeq : f = ((s n : ℂ → ℂ) + b n) + g n := by
      have htac := MeasureTheory.trunc_add_truncCompl (f := r n) (t := 1)
      funext x
      have hx := congrFun htac x
      simp only [Pi.add_apply] at hx
      simp only [hbdef, hgdef, Pi.add_apply]
      have hrx : r n x = f x - (s n : ℂ → ℂ) x := rfl
      rw [hrx] at hx
      linear_combination -hx
    have hun_mem : MemLp ((s n : ℂ → ℂ) + b n) p₀ volume := (hs_mem₀ n).add (hb_mem n)
    have h1 : T ((s n : ℂ → ℂ) + b n) =ᵐ[volume] T (s n : ℂ → ℂ) + T (b n) :=
      hadd (s n : ℂ → ℂ) (b n) (Or.inl (hs_mem₀ n)) (Or.inl (hb_mem n))
    have h2 : T (((s n : ℂ → ℂ) + b n) + g n)
        =ᵐ[volume] T ((s n : ℂ → ℂ) + b n) + T (g n) :=
      hadd ((s n : ℂ → ℂ) + b n) (g n) (Or.inl hun_mem) (Or.inr (hg_mem n))
    rw [← hfeq] at h2
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Pi.add_apply, Pi.sub_apply] at hx1 hx2 ⊢
    rw [hx2, hx1]; ring
  -- `eLpNorm (r n) p → 0`.
  have hr_tendsto : atTop.Tendsto (fun n => eLpNorm (r n) p volume) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε_tendsto
      (fun n => zero_le) (fun n => (hr_lt n).le)
  -- `(eLpNorm (r n) p)^c → 0` for positive `c`.
  have hrpow_tendsto : ∀ c : ℝ, 0 < c →
      atTop.Tendsto (fun n => eLpNorm (r n) p volume ^ c) (𝓝 0) := by
    intro c hc
    have hcont : atTop.Tendsto (fun n => eLpNorm (r n) p volume ^ c) (𝓝 ((0 : ℝ≥0∞) ^ c)) :=
      ((ENNReal.continuous_rpow_const (y := c)).tendsto 0).comp hr_tendsto
    rwa [ENNReal.zero_rpow_of_pos hc] at hcont
  -- `eLpNorm (T (b n)) p₀ → 0` and `eLpNorm (T (g n)) p₁ → 0`.
  have hTb_zero : atTop.Tendsto (fun n => eLpNorm (T (b n)) p₀ volume) (𝓝 0) := by
    have hbnd : atTop.Tendsto
        (fun n => (M₀ : ℝ≥0∞) * eLpNorm (r n) p volume ^ (p.toReal / p₀.toReal)) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (M₀ : ℝ≥0∞))
        (hrpow_tendsto (p.toReal / p₀.toReal) (by positivity)) (Or.inr (by simp))
      rwa [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbnd
      (fun n => zero_le) (fun n => hTb_bound n)
  have hTg_zero : atTop.Tendsto (fun n => eLpNorm (T (g n)) p₁ volume) (𝓝 0) := by
    have hbnd : atTop.Tendsto
        (fun n => (M₁ : ℝ≥0∞) * eLpNorm (r n) p volume ^ (p.toReal / p₁.toReal)) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (M₁ : ℝ≥0∞))
        (hrpow_tendsto (p.toReal / p₁.toReal) (by positivity)) (Or.inr (by simp))
      rwa [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbnd
      (fun n => zero_le) (fun n => hTg_bound n)
  -- `b n` and `g n` are also in `L^p` (dominated by `r n`), giving measurability of their images.
  have hb_memp : ∀ n, MemLp (b n) p volume := fun n => (hr_mem n).truncCompl
  have hg_memp : ∀ n, MemLp (g n) p volume := fun n => (hr_mem n).trunc
  have hTb_aesm : ∀ n, AEStronglyMeasurable (T (b n)) volume := fun n => hmeas _ (hb_memp n)
  have hTg_aesm : ∀ n, AEStronglyMeasurable (T (g n)) volume := fun n => hmeas _ (hg_memp n)
  -- Convergence in measure of `T (b n)` and `T (g n)` to `0`.
  have hTb_TIM : TendstoInMeasure volume (fun n => T (b n)) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_eLpNorm hp₀0 hTb_aesm aestronglyMeasurable_const
    refine hTb_zero.congr (fun n => eLpNorm_congr_ae ?_)
    filter_upwards with x
    exact (sub_zero (T (b n) x)).symm
  have hTg_TIM : TendstoInMeasure volume (fun n => T (g n)) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_eLpNorm hp₁0 hTg_aesm aestronglyMeasurable_const
    refine hTg_zero.congr (fun n => eLpNorm_congr_ae ?_)
    filter_upwards with x
    exact (sub_zero (T (g n) x)).symm
  -- Extract a subsequence along which `T (b ·) → 0` a.e.
  obtain ⟨ns, hns_mono, hns_b⟩ := hTb_TIM.exists_seq_tendsto_ae
  -- Along `ns`, `T (g ·) → 0` still in measure; extract a further subsequence.
  have hTg_TIM_ns : TendstoInMeasure volume (fun k => T (g (ns k))) atTop 0 :=
    fun δ hδ => (hTg_TIM δ hδ).comp hns_mono.tendsto_atTop
  obtain ⟨ms, hms_mono, hms_g⟩ := hTg_TIM_ns.exists_seq_tendsto_ae
  -- The composite subsequence `ns ∘ ms`.
  set ks : ℕ → ℕ := fun k => ns (ms k) with hks
  have hks_mono : StrictMono ks := hns_mono.comp hms_mono
  -- Along `ks`: `T (b ·) → 0` and `T (g ·) → 0` a.e.
  have hks_b : ∀ᵐ x ∂volume, atTop.Tendsto (fun k => T (b (ks k)) x) (𝓝 (0 : ℂ)) := by
    filter_upwards [hns_b] with x hx
    exact hx.comp hms_mono.tendsto_atTop
  have hks_g : ∀ᵐ x ∂volume, atTop.Tendsto (fun k => T (g (ks k)) x) (𝓝 (0 : ℂ)) := hms_g
  -- The decomposition holds a.e. simultaneously over all indices.
  have hdecomp_all : ∀ᵐ x ∂volume, ∀ k,
      T f x - T (s (ks k) : ℂ → ℂ) x = T (b (ks k)) x + T (g (ks k)) x := by
    rw [ae_all_iff]
    intro k
    filter_upwards [hdecomp (ks k)] with x hx
    simpa using hx
  -- `T (s (ks ·)) → h` a.e. (subsequence of the full sequence).
  have hks_h : ∀ᵐ x ∂volume, atTop.Tendsto (fun k => T (s (ks k) : ℂ → ℂ) x) (𝓝 (h x)) := by
    filter_upwards [h_tendsto] with x hx
    exact hx.comp hks_mono.tendsto_atTop
  -- Conclude `h =ᵐ T f`.
  have hheq : h =ᵐ[volume] T f := by
    filter_upwards [hdecomp_all, hks_b, hks_g, hks_h] with x hxdec hxb hxg hxh
    -- `T (s (ks k)) x → T f x`.
    have hsum_zero : atTop.Tendsto (fun k => T (b (ks k)) x + T (g (ks k)) x) (𝓝 (0 : ℂ)) := by
      have := hxb.add hxg; simpa using this
    have hdiff_zero : atTop.Tendsto (fun k => T f x - T (s (ks k) : ℂ → ℂ) x) (𝓝 (0 : ℂ)) := by
      refine hsum_zero.congr (fun k => ?_)
      rw [hxdec k]
    have hto_Tf : atTop.Tendsto (fun k => T (s (ks k) : ℂ → ℂ) x) (𝓝 (T f x)) := by
      have hconst : atTop.Tendsto (fun _ : ℕ => T f x) (𝓝 (T f x)) := tendsto_const_nhds
      have := hconst.sub hdiff_zero
      simpa using this
    exact tendsto_nhds_unique hxh hto_Tf
  -- Final bound.
  calc eLpNorm (T f) p volume
      = eLpNorm h p volume := (eLpNorm_congr_ae hheq).symm
    _ ≤ Cf := hh_bound
    _ = M * eLpNorm f p volume := hCf

end RieszThorin

/-- **Riesz–Thorin / Stein complex interpolation.** An a.e.-linear operator `T`
bounded `L^{p₀} → L^{p₀}` with constant `M₀` and `L^{p₁} → L^{p₁}` with constant
`M₁` is bounded `Lᵖ → Lᵖ` with the multiplicatively-sharp constant
`M₀^{1-θ} · M₁^θ`, where `1/p = (1-θ)/p₀ + θ/p₁`. -/
theorem eLpNorm_interpolation_of_hasStrongType
    {T : (ℂ → ℂ) → ℂ → ℂ} {p₀ p₁ p : ℝ≥0∞} {M₀ M₁ : ℝ≥0} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₀top : p₀ ≠ ⊤) (hp₁ : 1 ≤ p₁) (hp₁top : p₁ ≠ ⊤) (hp₀p₁ : p₀ ≠ p₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hmeas : ∀ s : ℂ → ℂ, MemLp s p volume → AEStronglyMeasurable (T s) volume)
    (hadd : ∀ s t : ℂ → ℂ, (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      (MemLp t p₀ volume ∨ MemLp t p₁ volume) → T (s + t) =ᵐ[volume] T s + T t)
    (hsmul : ∀ (c : ℂ) (s : ℂ → ℂ), (MemLp s p₀ volume ∨ MemLp s p₁ volume) →
      T (c • s) =ᵐ[volume] c • T s)
    (hT₀ : ∀ s : ℂ → ℂ, MemLp s p₀ volume → eLpNorm (T s) p₀ volume ≤ M₀ * eLpNorm s p₀ volume)
    (hT₁ : ∀ s : ℂ → ℂ, MemLp s p₁ volume → eLpNorm (T s) p₁ volume ≤ M₁ * eLpNorm s p₁ volume)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    eLpNorm (T f) p volume ≤ (M₀ ^ (1 - θ) * M₁ ^ θ : ℝ≥0) * eLpNorm f p volume := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases lt_or_gt_of_ne hp₀p₁ with hlt | hgt
  · -- `p₀ < p₁`: apply the density lemma directly.
    exact RieszThorin.core hp₀ hp₀top hp₁ hp₁top hlt ⟨hθ0, hθ1⟩ hp hmeas hadd hsmul hT₀ hT₁ hf
  · -- `p₁ < p₀`: swap roles, replacing `θ` by `1 - θ`.
    have hθ' : (1 - θ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hp' : p⁻¹ = ENNReal.ofReal (1 - (1 - θ)) * p₁⁻¹ + ENNReal.ofReal (1 - θ) * p₀⁻¹ := by
      rw [show (1 : ℝ) - (1 - θ) = θ by ring, hp]; ring
    have hbound := RieszThorin.core hp₁ hp₁top hp₀ hp₀top hgt hθ' hp' hmeas
      (fun s t hs ht => hadd s t hs.symm ht.symm)
      (fun c s hs => hsmul c s hs.symm) hT₁ hT₀ hf
    -- Reconcile the constant: `M₁^(1-(1-θ)) * M₀^(1-θ) = M₀^(1-θ) * M₁^θ`.
    rwa [show (M₁ ^ (1 - (1 - θ)) * M₀ ^ (1 - θ) : ℝ≥0) = (M₀ ^ (1 - θ) * M₁ ^ θ : ℝ≥0) by
      rw [show (1 : ℝ) - (1 - θ) = θ by ring, mul_comm]] at hbound

end NoWanderingDomains

