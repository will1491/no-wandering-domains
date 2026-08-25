/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.InverseQC.LusinN

/-!
# Inverse-is-QC: per-slice absolute continuity and the weak gradient

Continues `InverseQC.LusinN`. From the fibered Lusin-(N) of `g = f⁻¹` and the multiplicity
area formula (`multiplicityAreaFormula_noSingularPart`), almost every slice of `g` is
absolutely continuous (the converse no-singular-part / Banach–Zaretsky route via
`MonotoneDecompN` and the variation lower bound `lintegral_nnnorm_deriv_le_eVariationOn`).
This yields the weak gradient (`inverse_hasWeakGradient`, `inverse_memW12loc`) and hence the
root result `IsQCAnalytic.inverse_isQCAnalytic`.
-/

open MeasureTheory Complex
open scoped ENNReal ComplexConjugate

namespace NoWanderingDomains

/-! ## Absolute continuity on lines of the quasiconformal inverse

The map `g = f⁻¹` is absolutely continuous on almost every horizontal and vertical line, with
line derivatives the a.e.-defined pointwise partials `(Dg w) 1`, `(Dg w) I`.
The line derivatives are the genuine pointwise partials (they a.e. exist and equal
`(Df (g w))⁻¹` by `inverse_differentiableAt_ae`), recovered via Fubini; only the *absolute
continuity* — the "no singular part" claim — is the genuine analytic content, isolated as
`inverse_slice_absolutelyContinuous_core_x` / `..._y` (proven via the planar multiplicity area
formula `multiplicityAreaFormula_noSingularPart`) and packaged by
`inverse_reverseLengthArea_weakGradient`.

**This is the classical reverse length–area theorem for the inverse —
genuinely not derivable from the pointwise a.e. data.** The hypothesis `IsQCAnalytic f b` is
the load-bearing input: it supplies the forward map's genuine `W^{1,2}_loc`/modulus structure
(`hf.2.1 : MemW12loc f`), which the area-preserving singular shear `g⟨x,y⟩ = x + i(y + s x)`
(`s` continuous singular increasing) lacks. That shear is injective, continuous,
a.e.-differentiable with condition N⁺ and the pointwise dilatation bound (the inverse-side
data this file already proves), yet its horizontal slices `y + s ·` are singular (not AC), so
it is NOT ACL. The forward structure rules it out by the reverse length–area / Banach–Zaretsky
method (`QC/Foundations/BanachZaretsky.lean`).
-/

/-! ## Step 3 / (b'): assembling per-slice absolute continuity

With the fibered Lusin-(N) (Steps 1–2) in hand, the
**continuous-monotone Jordan decomposition with Lusin-(N) pieces** of each slice component — the
classical reverse length–area / Federer area-formula upper bound — is established below as
`inverse_slice_monotoneDecompN` (now PROVEN, from the per-slice MAF via
`inverse_slice_componentAC`). Everything surrounding it — the slice derivative (Fubini),
the interval-integrability of the derivative (the `L²_loc ⊆ L¹_loc` energy bound), and the
Banach–Zaretsky bridge from the decomposition to absolute continuity — is fully proven. -/

/-- **The derivative of a continuous monotone difference is interval-integrable.** -/
private theorem intervalIntegrable_deriv_monotone_sub {p q : ℝ → ℝ}
    (hp : Monotone p) (hq : Monotone q) (a c : ℝ) :
    IntervalIntegrable (fun t => deriv p t - deriv q t) volume a c :=
  (hp.monotoneOn _).intervalIntegrable_deriv.sub (hq.monotoneOn _).intervalIntegrable_deriv

/-- **An `ℝ`-interval-integrable function lifts to a `ℂ`-interval-integrable one via `ofReal`.** -/
private theorem intervalIntegrable_ofReal_comp {φ : ℝ → ℝ} {a c : ℝ}
    (hφ : IntervalIntegrable φ volume a c) :
    IntervalIntegrable (fun t => (φ t : ℂ)) volume a c := by
  rw [intervalIntegrable_iff] at hφ ⊢
  exact Complex.ofRealCLM.integrable_comp hφ

/-- **A complex function with interval-integrable real and imaginary parts is interval-integrable.**
Stated for the recombination `t ↦ (φre t) + (φim t) • I`. -/
private theorem intervalIntegrable_complex_of_re_im {φre φim : ℝ → ℝ} {a c : ℝ}
    (hre : IntervalIntegrable φre volume a c) (him : IntervalIntegrable φim volume a c) :
    IntervalIntegrable (fun t => (φre t : ℂ) + (φim t : ℝ) • Complex.I) volume a c := by
  have h2 : IntervalIntegrable (fun t => (φim t : ℂ) * Complex.I) volume a c :=
    (intervalIntegrable_ofReal_comp him).mul_const Complex.I
  refine (intervalIntegrable_ofReal_comp hre).add ?_
  refine h2.congr (fun t _ => ?_)
  rw [Complex.real_smul]

/-- A function `h : ℝ → ℝ` admits a **continuous-monotone Jordan decomposition with Lusin-(N)
pieces**: `h = p − q` with `p, q` continuous monotone and each carrying null sets to null sets.
This is the structural content the reverse length–area / Federer area formula supplies for the
slices of a quasiconformal inverse — and which the singular shear's slices lack. -/
def MonotoneDecompN (h : ℝ → ℝ) : Prop :=
  ∃ p q : ℝ → ℝ, Monotone p ∧ Continuous p ∧ Monotone q ∧ Continuous q ∧
    (∀ S : Set ℝ, volume S = 0 → volume (p '' S) = 0) ∧
    (∀ S : Set ℝ, volume S = 0 → volume (q '' S) = 0) ∧ h = p - q

/-- **Converse Banach–Zaretsky packaging: a continuous function that is absolutely continuous on
every interval admits a continuous-monotone Jordan decomposition with Lusin-(N) pieces.** The
decomposition is the primitive split `h = (h 0 + ∫₀ˣ (h')⁺) − (∫₀ˣ (h')⁻)` of the FTC primitive
of the a.e. derivative `h' = deriv h`: each piece is a primitive of a nonnegative
interval-integrable function, hence continuous, monotone, and Lusin-(N) by `luzinN_of_primitive`.

This is the converse Banach–Zaretsky direction: where condition (N) of the monotone pieces
yields AC, here AC of the (continuous) function yields condition (N) of the canonical
primitive pieces. It is the brick that turns the per-slice absolute continuity produced by the
reverse length–area squeeze into the `MonotoneDecompN` shape the keystone consumes. -/
theorem monotoneDecompN_of_continuous_ac {h : ℝ → ℝ} (_hcont : Continuous h)
    (hac : ∀ a c : ℝ, AbsolutelyContinuousOnInterval h a c) : MonotoneDecompN h := by
  classical
  -- `deriv h` is interval-integrable on every interval (AC ⟹ deriv interval-integrable).
  have hII : ∀ a c : ℝ, IntervalIntegrable (deriv h) volume a c := fun a c =>
    (hac a c).intervalIntegrable_deriv
  -- The positive and negative parts of `deriv h`.
  set φp : ℝ → ℝ := fun t => max (deriv h t) 0 with hφp
  set φn : ℝ → ℝ := fun t => max (-(deriv h t)) 0 with hφn
  have hφpnn : 0 ≤ φp := fun t => le_max_right _ _
  have hφnnn : 0 ≤ φn := fun t => le_max_right _ _
  have hφpII : ∀ a c : ℝ, IntervalIntegrable φp volume a c := fun a c => by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hII a c)).pos_part
  have hφnII : ∀ a c : ℝ, IntervalIntegrable φn volume a c := fun a c => by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hII a c)).neg_part
  -- The two monotone, continuous, Lusin-(N) primitive pieces.
  set p : ℝ → ℝ := fun x => h 0 + ∫ t in (0 : ℝ)..x, φp t with hpdef
  set q : ℝ → ℝ := fun x => (0 : ℝ) + ∫ t in (0 : ℝ)..x, φn t with hqdef
  have hpmono : Monotone p := by
    intro x y hxy
    simp only [hpdef, add_le_add_iff_left]
    rw [show (∫ t in (0 : ℝ)..y, φp t) = (∫ t in (0 : ℝ)..x, φp t) + ∫ t in x..y, φp t from
      (intervalIntegral.integral_add_adjacent_intervals (hφpII 0 x) (hφpII x y)).symm,
      le_add_iff_nonneg_right]
    exact intervalIntegral.integral_nonneg hxy (fun t _ => hφpnn t)
  have hqmono : Monotone q := by
    intro x y hxy
    simp only [hqdef, add_le_add_iff_left]
    rw [show (∫ t in (0 : ℝ)..y, φn t) = (∫ t in (0 : ℝ)..x, φn t) + ∫ t in x..y, φn t from
      (intervalIntegral.integral_add_adjacent_intervals (hφnII 0 x) (hφnII x y)).symm,
      le_add_iff_nonneg_right]
    exact intervalIntegral.integral_nonneg hxy (fun t _ => hφnnn t)
  have hpcont : Continuous p :=
    Continuous.add continuous_const (intervalIntegral.continuous_primitive hφpII 0)
  have hqcont : Continuous q :=
    Continuous.add continuous_const (intervalIntegral.continuous_primitive hφnII 0)
  have hpN : ∀ S : Set ℝ, volume S = 0 → volume (p '' S) = 0 := fun S hS =>
    luzinN_of_primitive hφpnn hφpII (h 0) hS
  have hqN : ∀ S : Set ℝ, volume S = 0 → volume (q '' S) = 0 := fun S hS =>
    luzinN_of_primitive hφnnn hφnII 0 hS
  -- `h = p − q`: FTC (`integral_deriv_eq_sub`) plus the `φp − φn = deriv h` split.
  have hpq : h = p - q := by
    funext x
    have hsplit : (∫ t in (0 : ℝ)..x, φp t) - ∫ t in (0 : ℝ)..x, φn t
        = ∫ t in (0 : ℝ)..x, deriv h t := by
      rw [← intervalIntegral.integral_sub (hφpII 0 x) (hφnII 0 x)]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp only [hφp, hφn]
      exact max_zero_sub_max_neg_zero_eq_self (deriv h t)
    have hftc : ∫ t in (0 : ℝ)..x, deriv h t = h x - h 0 :=
      (hac 0 x).integral_deriv_eq_sub
    simp only [Pi.sub_apply, hpdef, hqdef, zero_add]
    rw [show (h 0 + ∫ t in (0 : ℝ)..x, φp t) - ∫ t in (0 : ℝ)..x, φn t
        = h 0 + ((∫ t in (0 : ℝ)..x, φp t) - ∫ t in (0 : ℝ)..x, φn t) by ring, hsplit, hftc]
    ring
  exact ⟨p, q, hpmono, hpcont, hqmono, hqcont, hpN, hqN, hpq⟩

/-! ### The variation lower bound `∫⁻‖h'‖ ≤ eVariationOn h` (Mathlib-absent, proven here)

The classical fact that the total variation of a function dominates the integral of its a.e.
derivative. The proof routes through the (monotone) variation function
`V := variationOnFromTo h s a`:
the increment bound `|h y − h x| ≤ V y − V x` makes both `V − h` and `V + h` monotone, so a.e.
`|deriv h| ≤ deriv V`, and the monotone fundamental theorem of calculus
`MonotoneOn.intervalIntegral_deriv_mem_uIcc` bounds `∫ deriv V ≤ V c − V a = eVariationOn h`. -/

/-- The variation function `V := variationOnFromTo h (Icc a c) a` added to `±h` is monotone on
`Icc a c`. (`V − h` is `variationOnFromTo.sub_self_monotoneOn`; `V + h` is the symmetric increment
bound.) -/
private theorem monotoneOn_variation_add {h : ℝ → ℝ} {a c : ℝ}
    (hbv : LocallyBoundedVariationOn h (Set.Icc a c)) (ha : a ∈ Set.Icc a c) :
    MonotoneOn (variationOnFromTo h (Set.Icc a c) a + h) (Set.Icc a c) := by
  rintro b bs d ds bd
  rw [Pi.add_apply, Pi.add_apply]
  have hincr : |h d - h b| ≤ variationOnFromTo h (Set.Icc a c) a d
      - variationOnFromTo h (Set.Icc a c) a b := by
    calc |h d - h b| = dist (h b) (h d) := by rw [dist_comm, Real.dist_eq]
      _ ≤ variationOnFromTo h (Set.Icc a c) b d := by
          rw [variationOnFromTo.eq_of_le _ _ bd, dist_edist]
          apply ENNReal.toReal_mono (hbv b d bs ds)
          apply eVariationOn.edist_le h
          exacts [⟨bs, le_rfl, bd⟩, ⟨ds, bd, le_rfl⟩]
      _ = variationOnFromTo h (Set.Icc a c) a d - variationOnFromTo h (Set.Icc a c) a b := by
          rw [← variationOnFromTo.add hbv ha bs ds, add_sub_cancel_left]
  have hge : -(h d - h b) ≤ variationOnFromTo h (Set.Icc a c) a d
      - variationOnFromTo h (Set.Icc a c) a b :=
    le_trans (neg_le_abs _) hincr
  linarith [hge]

/-- **The variation lower bound (proven; Mathlib-absent).** For a function `h : ℝ → ℝ` whose
derivative exists a.e. (`HasDerivAt h (h' x) x`), the integral of the derivative is dominated by the
total variation on `Icc a c`:
`∫⁻ x in Icc a c, ‖h' x‖₊ ≤ eVariationOn h (Icc a c)`. -/
theorem lintegral_nnnorm_deriv_le_eVariationOn {h h' : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hderiv : ∀ᵐ x : ℝ, HasDerivAt h (h' x) x) :
    ∫⁻ x in Set.Icc a c, ‖h' x‖₊ ≤ eVariationOn h (Set.Icc a c) := by
  classical
  -- If `h` has unbounded variation the right side is `⊤`; done.
  by_cases hbvtop : eVariationOn h (Set.Icc a c) = ⊤
  · rw [hbvtop]; exact le_top
  -- Otherwise `h` is BV; let `V` be its variation function from `a`.
  have hbv : LocallyBoundedVariationOn h (Set.Icc a c) := by
    intro x y hx hy
    exact ne_top_of_le_ne_top hbvtop (eVariationOn.mono h (Set.inter_subset_left))
  have ha : a ∈ Set.Icc a c := ⟨le_refl a, hac⟩
  have hc : c ∈ Set.Icc a c := ⟨hac, le_refl c⟩
  set V : ℝ → ℝ := variationOnFromTo h (Set.Icc a c) a with hV
  -- `V` and `V ± h` are monotone on `Icc a c`.
  have hVmono : MonotoneOn V (Set.Icc a c) := variationOnFromTo.monotoneOn hbv ha
  have hVsub : MonotoneOn (V - h) (Set.Icc a c) := variationOnFromTo.sub_self_monotoneOn hbv ha
  have hVadd : MonotoneOn (V + h) (Set.Icc a c) := monotoneOn_variation_add hbv ha
  -- `V c - V a = eVariationOn h (Icc a c)` and `V a = 0`.
  have hVa : V a = 0 := variationOnFromTo.self h (Set.Icc a c) a
  have hVc : V c = (eVariationOn h (Set.Icc a c)).toReal := by
    rw [hV, variationOnFromTo.eq_of_le h _ hac, Set.inter_eq_self_of_subset_right
      (Set.Subset.refl _)]
  -- a.e. on `Icc a c`: `h`, `V` are differentiable; the derivatives satisfy `|h'| ≤ V'`.
  have key : ∀ᵐ x : ℝ, x ∈ Set.Ioo a c →
      (‖h' x‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (deriv V x) := by
    filter_upwards [hderiv, hVmono.ae_differentiableWithinAt_of_mem] with x hx hxV hmem
    have hIccnhds : Set.Icc a c ∈ nhds x := Icc_mem_nhds hmem.1 hmem.2
    have hxmem : x ∈ Set.Icc a c := Set.Ioo_subset_Icc_self hmem
    -- `V` is differentiable at the interior point `x`.
    have hVd : HasDerivAt V (deriv V x) x :=
      ((hxV hxmem).differentiableAt hIccnhds).hasDerivAt
    have hsubd : HasDerivAt (V - h) (deriv V x - h' x) x := hVd.sub hx
    have haddd : HasDerivAt (V + h) (deriv V x + h' x) x := hVd.add hx
    -- The monotone combinations have nonnegative derivative (`derivWithin = deriv` at interior).
    have hsubnn : 0 ≤ deriv V x - h' x := by
      have h0 : (0 : ℝ) ≤ derivWithin (V - h) (Set.Icc a c) x := hVsub.derivWithin_nonneg
      rwa [derivWithin_of_mem_nhds hIccnhds, hsubd.deriv] at h0
    have haddnn : 0 ≤ deriv V x + h' x := by
      have h0 : (0 : ℝ) ≤ derivWithin (V + h) (Set.Icc a c) x := hVadd.derivWithin_nonneg
      rwa [derivWithin_of_mem_nhds hIccnhds, haddd.deriv] at h0
    -- Hence `|h' x| ≤ deriv V x`, lift to `ℝ≥0∞`.
    have habs : |h' x| ≤ deriv V x := abs_le.mpr ⟨by linarith, by linarith⟩
    have hcast : (‖h' x‖₊ : ℝ≥0∞) = ENNReal.ofReal |h' x| := by
      rw [← Real.enorm_eq_ofReal_abs]; rfl
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal habs
  -- The `key` bound holds a.e. on the restricted measure `Icc a c` (the two boundary points,
  -- where `Ioo` fails, form a null set, so `key`'s `Ioo` hypothesis is discharged a.e.).
  have haea : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have haec : ∀ᵐ x : ℝ, x ≠ c := by simp [ae_iff, measure_singleton]
  have keyR : (fun x => (‖h' x‖₊ : ℝ≥0∞)) ≤ᵐ[volume.restrict (Set.Icc a c)]
      (fun x => ENNReal.ofReal (deriv V x)) := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [key, haea, haec] with x hx hxa hxc hxmem
    refine hx ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hxa), lt_of_le_of_ne hxmem.2 hxc⟩
  -- `deriv V` is interval-integrable (monotone) and nonnegative a.e.; relate the lintegral to the
  -- monotone fundamental theorem of calculus.
  have hVII : IntervalIntegrable (deriv V) volume a c :=
    MonotoneOn.intervalIntegrable_deriv (by rwa [Set.uIcc_of_le hac])
  have hVintnn : 0 ≤ ∫ x in a..c, deriv V x := by
    have hmem := MonotoneOn.intervalIntegral_deriv_mem_uIcc (f := V) (by rwa [Set.uIcc_of_le hac])
    rw [hVa, hVc, sub_zero] at hmem
    have hmem2 : ∫ x in a..c, deriv V x ∈ Set.uIcc 0 ((eVariationOn h (Set.Icc a c)).toReal) := hmem
    rw [Set.uIcc_of_le (by positivity), Set.mem_Icc] at hmem2
    exact hmem2.1
  have hVintle : ∫ x in a..c, deriv V x ≤ (eVariationOn h (Set.Icc a c)).toReal := by
    have hmem := MonotoneOn.intervalIntegral_deriv_mem_uIcc (f := V) (by rwa [Set.uIcc_of_le hac])
    rw [hVa, hVc, sub_zero] at hmem
    rw [Set.uIcc_of_le (by positivity), Set.mem_Icc] at hmem
    exact hmem.2
  -- `∫⁻ ofReal (deriv V) over Icc = ofReal (∫ deriv V)` via the integral on `Ioc = Icc` a.e.
  have hVintegrableOn : IntegrableOn (deriv V) (Set.Icc a c) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mp hVII
  have hVnn_ae : 0 ≤ᵐ[volume.restrict (Set.Icc a c)] deriv V := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [haea, haec] with x hxa hxc hxmem
    have hxIoo : x ∈ Set.Ioo a c :=
      ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hxa), lt_of_le_of_ne hxmem.2 hxc⟩
    have hIccnhds : Set.Icc a c ∈ nhds x := Icc_mem_nhds hxIoo.1 hxIoo.2
    have h0 : (0 : ℝ) ≤ derivWithin V (Set.Icc a c) x := hVmono.derivWithin_nonneg
    rwa [derivWithin_of_mem_nhds hIccnhds] at h0
  -- Integrate the comparison and bound by the monotone FTC.
  calc ∫⁻ x in Set.Icc a c, ‖h' x‖₊
      ≤ ∫⁻ x in Set.Icc a c, ENNReal.ofReal (deriv V x) := lintegral_mono_ae keyR
    _ = ENNReal.ofReal (∫ x in Set.Icc a c, deriv V x) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hVintegrableOn hVnn_ae]
    _ = ENNReal.ofReal (∫ x in a..c, deriv V x) := by
        congr 1
        rw [intervalIntegral.integral_of_le hac, MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ ≤ ENNReal.ofReal ((eVariationOn h (Set.Icc a c)).toReal) :=
        ENNReal.ofReal_le_ofReal hVintle
    _ = eVariationOn h (Set.Icc a c) := ENNReal.ofReal_toReal hbvtop

/-! ### PIECE 2 — the converse "no singular part ⟹ AC" via increment domination

If a continuous `h` has increments dominated by the integral of a nonnegative interval-integrable
`φ` (`|h y − h x| ≤ ∫ₓʸ φ` for `x ≤ y` in the window), then `h` is absolutely continuous on every
sub-interval: the φ-primitive `P x := ∫₀ˣ φ` is absolutely continuous (Mathlib), and the increment
bound makes each partial AC-sum of `h` dominated by the corresponding partial sum of `P`. -/

set_option maxHeartbeats 400000 in
-- The increment-domination AC proof is assembled inline as nested `have`s (each partial AC-sum
-- of `h` dominated by the φ-primitive's), so its elaboration needs the raised heartbeat budget.
/-- **AC by increment domination.** A function `h : ℝ → ℝ` whose increments over `[x, y] ⊆ [a, c]`
are bounded by `∫ₓʸ φ` for a nonnegative interval-integrable `φ` is absolutely continuous on
`[a, c]`. (The domination is required only for `a ≤ x ≤ y ≤ c`.) -/
theorem absolutelyContinuousOnInterval_of_increment_le_integral {h φ : ℝ → ℝ} {a c : ℝ}
    (hac : a ≤ c) (hφnn : 0 ≤ φ) (hφII : ∀ u v : ℝ, IntervalIntegrable φ volume u v)
    (hbound : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ c → |h y - h x| ≤ ∫ t in x..y, φ t) :
    AbsolutelyContinuousOnInterval h a c := by
  classical
  -- The φ-primitive `P x := ∫ₐˣ φ` is absolutely continuous on `[a, c]` (`a ∈ uIcc a c`).
  set P : ℝ → ℝ := fun x => ∫ t in a..x, φ t with hP
  have haIcc : a ∈ Set.uIcc a c := Set.left_mem_uIcc
  have hPac : AbsolutelyContinuousOnInterval P a c :=
    (hφII a c).absolutelyContinuousOnInterval_intervalIntegral haIcc
  -- The key per-pair domination: for `u, v ∈ [a, c]`, `dist (h u) (h v) ≤ dist (P u) (P v)`.
  have hpair : ∀ u ∈ Set.uIcc a c, ∀ v ∈ Set.uIcc a c,
      dist (h u) (h v) ≤ dist (P u) (P v) := by
    intro u hu v hv
    rw [Set.uIcc_of_le hac] at hu hv
    -- `dist (P u) (P v) = |∫ᵤᵛ φ| = ∫_{min..max} φ` since `φ ≥ 0`.
    have hPdiff : P u - P v = ∫ t in v..u, φ t := by
      simp only [hP]
      rw [intervalIntegral.integral_interval_sub_left (hφII a u) (hφII a v)]
    have hPdist : dist (P u) (P v) = |∫ t in v..u, φ t| := by
      rw [Real.dist_eq, hPdiff]
    rw [Real.dist_eq, hPdist]
    -- Reduce to the ordered case `min ≤ max` and apply `hbound`.
    -- Goal: `|h u - h v| ≤ |∫_{v..u} φ|`.
    rcases le_total u v with huv | hvu
    · -- `u ≤ v`: `|h u - h v| = |h v - h u| ≤ ∫ᵤᵛ φ = |∫ᵥᵘ φ|`.
      have hb := hbound u v hu.1 huv hv.2
      have hsymm : |h u - h v| = |h v - h u| := abs_sub_comm _ _
      have hintnn : (0 : ℝ) ≤ ∫ t in u..v, φ t :=
        intervalIntegral.integral_nonneg huv (fun t _ => hφnn t)
      have hflip : ∫ t in v..u, φ t = -∫ t in u..v, φ t := intervalIntegral.integral_symm u v
      have heq : |∫ t in v..u, φ t| = ∫ t in u..v, φ t := by
        rw [hflip, abs_neg, abs_of_nonneg hintnn]
      rw [hsymm, heq]; exact hb
    · -- `v ≤ u`: `|h u - h v| ≤ ∫ᵥᵘ φ = |∫ᵥᵘ φ|`.
      have hb := hbound v u hv.1 hvu hu.2
      have hintnn : (0 : ℝ) ≤ ∫ t in v..u, φ t :=
        intervalIntegral.integral_nonneg hvu (fun t _ => hφnn t)
      rw [abs_of_nonneg hintnn]; exact hb
  -- The ε-δ characterization: dominate `h`'s AC-sum by `P`'s AC-sum.
  rw [absolutelyContinuousOnInterval_iff] at hPac ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδP⟩ := hPac ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  refine lt_of_le_of_lt ?_ (hδP E hE hlen)
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hmem := hE.1 i hi
  exact hpair (E.2 i).1 hmem.1 (E.2 i).2 hmem.2

/-- **A complex slice whose real and imaginary parts each have a continuous-monotone Lusin-(N)
decomposition is absolutely continuous on every interval.** The interval-integrability of the
monotone-derivative velocity and the a.e. slice derivative are derived from the decompositions;
`absolutelyContinuousOnInterval_of_monotoneDiffLusinN` (Banach–Zaretsky) closes it. -/
private theorem absolutelyContinuousOnInterval_of_monotoneDecompN_pair {s : ℝ → ℂ}
    (hre : MonotoneDecompN (fun t => (s t).re)) (him : MonotoneDecompN (fun t => (s t).im))
    (a c : ℝ) : AbsolutelyContinuousOnInterval s a c := by
  obtain ⟨pr, qr, hprm, hprc, hqrm, hqrc, hprN, hqrN, hre_eq⟩ := hre
  obtain ⟨pii, qii, hpim, hpic, hqim, hqic, hpiN, hqiN, him_eq⟩ := him
  -- The monotone-derivative slice velocity.
  set s' : ℝ → ℂ := fun t : ℝ =>
    ((deriv pr t - deriv qr t : ℝ) : ℂ) + (deriv pii t - deriv qii t : ℝ) • Complex.I with hs'
  have hsint : ∀ a c : ℝ, IntervalIntegrable s' volume a c := fun a c =>
    intervalIntegrable_complex_of_re_im
      (intervalIntegrable_deriv_monotone_sub hprm hqrm a c)
      (intervalIntegrable_deriv_monotone_sub hpim hqim a c)
  have hsderiv : ∀ᵐ t : ℝ, HasDerivAt s (s' t) t := by
    filter_upwards [hprm.ae_differentiableAt, hqrm.ae_differentiableAt,
      hpim.ae_differentiableAt, hqim.ae_differentiableAt] with t hprd hqrd hpid hqid
    have hreD : HasDerivAt (fun t => (s t).re) (deriv pr t - deriv qr t) t := by
      rw [hre_eq]; exact hprd.hasDerivAt.sub hqrd.hasDerivAt
    have himD : HasDerivAt (fun t => (s t).im) (deriv pii t - deriv qii t) t := by
      rw [him_eq]; exact hpid.hasDerivAt.sub hqid.hasDerivAt
    have hcre : HasDerivAt (fun t => ((s t).re : ℂ)) ((deriv pr t - deriv qr t : ℝ) : ℂ) t :=
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hreD)
    have hcim : HasDerivAt (fun t => ((s t).im : ℂ) * Complex.I)
        (((deriv pii t - deriv qii t : ℝ) : ℂ) * Complex.I) t :=
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t himD)).mul_const Complex.I
    have hsum : HasDerivAt (fun t => ((s t).re : ℂ) + ((s t).im : ℝ) * Complex.I)
        (((deriv pr t - deriv qr t : ℝ) : ℂ)
          + ((deriv pii t - deriv qii t : ℝ) : ℂ) * Complex.I) t := hcre.add hcim
    have heq : (fun t => ((s t).re : ℂ) + ((s t).im : ℝ) * Complex.I) = s := by
      funext t; apply Complex.ext <;> simp
    rw [heq] at hsum
    have hval : ((deriv pr t - deriv qr t : ℝ) : ℂ)
        + ((deriv pii t - deriv qii t : ℝ) : ℂ) * Complex.I = s' t := by
      simp only [hs', Complex.real_smul]
    rw [hval] at hsum
    exact hsum
  exact absolutelyContinuousOnInterval_of_monotoneDiffLusinN hprm hprc hqrm hqrc hpim hpic hqim hqic
    hprN hqrN hpiN hqiN hre_eq him_eq hsderiv hsint a c

/-- **Continuity of a slice component of the inverse.** Each horizontal- or vertical-slice component
`x ↦ (g ⟨x, y⟩).re` etc. of the continuous inverse `g = f⁻¹` is continuous as a function `ℝ → ℝ`. -/
private theorem continuous_slice_component {g : ℂ → ℂ} (hgcont : Continuous g) (P : ℂ → ℝ)
    (hP : Continuous P) (y : ℝ) : Continuous (fun x : ℝ => P (g (Complex.mk x y))) := by
  have hslice : Continuous (fun x : ℝ => (Complex.mk x y : ℂ)) := by
    have he : (fun x : ℝ => (Complex.mk x y : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [he]; exact (Complex.continuous_ofReal).add continuous_const
  exact hP.comp (hgcont.comp hslice)

/-- **The horizontal embedding `x ↦ ⟨x, y⟩` has derivative `1`.** -/
private theorem hasDerivAt_mk_left (y : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (Complex.mk t y : ℂ)) (1 : ℂ) x := by
  have he : (fun t : ℝ => (Complex.mk t y : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [he]
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)

/-- **A.e. horizontal slice of a map differentiable a.e. has a derivative a.e.** For `G : ℂ → ℂ`
differentiable a.e. and `P : ℂ →L[ℝ] ℝ`, for almost every `y` the slice `x ↦ P(G⟨x,y⟩)` has a
derivative at almost every `x`, equal to `deriv (x ↦ P(G⟨x,y⟩)) x`. (Via Fubini on the null set
where `G` is not differentiable + the chain rule for the affine slice embedding.) -/
private theorem ae_slice_hasDerivAt_of_G {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ)
    (hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w) :
    ∀ᵐ y : ℝ, ∀ᵐ x : ℝ,
      HasDerivAt (fun t : ℝ => P (G (Complex.mk t y)))
        (deriv (fun t : ℝ => P (G (Complex.mk t y))) x) x := by
  -- The null set where `G` is not differentiable.
  set T : Set ℂ := {w | ¬ DifferentiableAt ℝ G w} with hT
  have hTnull : volume T = 0 := by
    rw [hT, ← ae_iff]; exact hGdiff
  -- For a.e. `y`, the horizontal fiber of `T` is null.
  filter_upwards [ae_slice_re_null_of_null hTnull] with y hy
  -- For `x` outside the fiber, `G` is differentiable at `⟨x,y⟩`, so the slice has a derivative.
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hy
  -- `hx : ¬ HasDerivAt (slice) (deriv slice x) x`. Show `⟨x,y⟩ ∈ T` (i.e. the fiber).
  rw [Set.mem_ofPred_eq]
  by_contra hmem
  apply hx
  rw [Set.mem_ofPred_eq, not_not] at hmem
  -- `G` differentiable at `⟨x,y⟩` ⟹ slice `x ↦ P(G⟨x,y⟩)` differentiable at `x`, so `HasDerivAt`.
  have hsliceDiff : DifferentiableAt ℝ (fun t : ℝ => P (G (Complex.mk t y))) x := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (Complex.mk t y : ℂ)) x :=
      (hasDerivAt_mk_left y x).differentiableAt
    exact P.differentiableAt.comp x (hmem.comp x h1)
  exact hsliceDiff.hasDerivAt

/-- **a.e.-slice interval integrability of a complex map** from joint local integrability (Fubini).
For a locally integrable `H : ℂ → ℂ`, for almost every `y` the slice `x ↦ H ⟨x, y⟩` is interval
integrable on every interval. (Self-contained `ℂ`-coordinate copy of the project's Fubini
helper.) -/
private theorem ae_slice_intervalIntegrable_complex {H : ℂ → ℂ}
    (hH : LocallyIntegrable H volume) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ, IntervalIntegrable (fun x => H (Complex.mk x y)) volume a b := by
  -- Transfer to `ℝ × ℝ` via the volume-preserving `ℂ ≃ ℝ × ℝ`.
  set H' : ℝ × ℝ → ℂ := fun p => H (Complex.mk p.1 p.2) with hH'
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hH'eq : H' = H ∘ Complex.measurableEquivRealProd.symm := by
    funext p; simp [hH', Complex.measurableEquivRealProd_symm_apply]
  -- Box-integrability of `H'` over `[-n,n]²` (pull back the compact image box) + Fubini.
  have hslice' : ∀ n : ℕ, ∀ᵐ y : ℝ, y ∈ Set.Icc (-(n : ℝ)) n →
      IntegrableOn (fun x => H' (x, y)) (Set.Icc (-(n : ℝ)) n) volume := by
    intro n
    have hemb : MeasurableEmbedding (Complex.measurableEquivRealProd.symm) :=
      Complex.measurableEquivRealProd.symm.measurableEmbedding
    set box : Set (ℝ × ℝ) := Set.Icc (-(n : ℝ)) n ×ˢ Set.Icc (-(n : ℝ)) n with hbox_def
    have hbox : Integrable H' ((volume.restrict (Set.Icc (-(n : ℝ)) n)).prod
        (volume.restrict (Set.Icc (-(n : ℝ)) n))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← MeasureTheory.IntegrableOn]
      change IntegrableOn H' box volume
      rw [hH'eq]
      have hpre : Complex.measurableEquivRealProd.symm ⁻¹'
          (Complex.measurableEquivRealProd.symm '' box) = box :=
        hemb.injective.preimage_image box
      rw [← hpre, MeasureTheory.MeasurePreserving.integrableOn_comp_preimage hmpsymm hemb]
      apply hH.integrableOn_isCompact
      have hcont : Continuous (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ)) := by
        have : (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ))
            = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
          funext p; apply Complex.ext <;> simp
        rw [this]
        exact (Complex.continuous_ofReal.comp continuous_fst).add
          ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
      have himg : Complex.measurableEquivRealProd.symm '' box
          = (fun p : ℝ × ℝ => (Complex.mk p.1 p.2 : ℂ)) '' box := by
        apply Set.image_congr; intro p _
        simp [Complex.measurableEquivRealProd_symm_apply]
      rw [himg]
      exact (isCompact_Icc.prod isCompact_Icc).image hcont
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
  have hyn : y ∈ Set.Icc (-(n : ℝ)) n := ⟨hyb.1, hyb.2⟩
  have hint := hy n hyn
  have hsub : Set.uIcc a b ⊆ Set.Icc (-(n : ℝ)) n := by
    intro t ht; rw [Set.mem_uIcc] at ht; rw [Set.mem_Icc]
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [intervalIntegrable_iff]
  exact hint.mono_set (le_trans Set.uIoc_subset_uIcc hsub)

/-! ### PIECE 1 — the multiplicity area formula (MAF), the single genuine GMT residual

The reverse length–area / Federer multiplicity-area inequality, specialised to the fibered maps of
the inverse `g = f⁻¹`. It is stated **per box** as a clean general residual: for the `y`-fibered
selector `Φ⟨x,y⟩ = P(g⟨x,y⟩) + i·y` (whose `det DΦ = ∂ₓ(P∘g)` and which is Lusin-(N) by Step 1
`inverse_fiber_lusinN`), the integrated total variation of the real-slice
`x ↦ P(g⟨x,y⟩)` over `y ∈ [c', d']` is bounded by the box integral of `‖∂ₓ(P∘g)‖`. -/

/-- **MULTIPLICITY AREA FORMULA (general, both axes) — now PROVEN.** For a
*continuous* map `G : ℂ → ℂ` whose `P`-component fibered map `Φ p := P(G p) • 1 + p.im • I` carries
null sets to null sets (Lusin condition (N) — supplied for the inverse `g = f⁻¹` by
`inverse_fiber_lusinN`), almost every horizontal slice `x ↦ P(G⟨x,y⟩)` has **no singular part**: its
total variation on each interval is bounded by the interval integral of the slice-derivative norm,

`∀ᵐ y, ∀ a c, eVariationOn (x ↦ P (G⟨x,y⟩)) [a,c]  ≤  ∫⁻_{x∈[a,c]} ‖∂ₓ(P∘G)‖`.

This is the per-slice Federer area formula with multiplicity (`≤` direction) for the `y`-fibered map
`Φ⟨x,y⟩ = P(G⟨x,y⟩) + i·y` (whose `det DΦ = ∂ₓ(P∘G)`): the forward Banach indicatrix bound
(`eVariationOn_le_lintegral_indicatrix`) couples the slice variation to the `Φ`-fibre count,
the area
formula (`addHaar_image_le_lintegral_abs_det_fderiv` on injective approximating pieces, with the
`{det = 0}`-image null by `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` — the genuine consumer
of the Lusin-(N) hypothesis `hΦN`) bounds the integrated fibre count by
`∫⁻ |det DΦ| = ∫⁻ ‖∂ₓ(P∘G)‖`,
and Fubini + the variation lower bound `lintegral_nnnorm_deriv_le_eVariationOn` force the per-slice
inequality. Mathlib has only the **injective** change of variables, so the multiplicity upper bound
is built here (via `MAF.multiplicityAreaFormula_general`).
**Both** the horizontal and the vertical inverse slices are instances (the latter by composing `G`
with the coordinate swap); this lemma is now PROVEN.

**Soundness / shear exclusion.** False for the area-preserving singular shear `Φ p = p + s(p.re)·I`
(`G = id`, `P = imCLM`): `det DΦ = ∂ₓ(im id) = 0` a.e. so the right side vanishes, while the slice
`x ↦ y + s x` is singular with positive variation. The `{det = 0}`-image-null step (the Lusin-(N)
consumer) is exactly what fails: that shear does not satisfy `hΦN`
(it is not `inverse_fiber_lusinN`,
lacking `f`'s super-critical gradient). -/
theorem multiplicityAreaFormula_noSingularPart {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ)
    (hGcont : Continuous G)
    (hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w)
    (hΦN : ∀ S : Set ℂ, volume S = 0 →
      volume ((fun p : ℂ => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I) '' S) = 0) :
    ∀ᵐ y : ℝ, ∀ a c : ℝ,
      eVariationOn (fun x : ℝ => P (G (Complex.mk x y))) (Set.Icc a c)
        ≤ ∫⁻ x in Set.Icc a c,
            ‖(deriv (fun t : ℝ => P (G (Complex.mk t y))) x)‖₊ := by
  -- The variation lower bound (VAR) holds a.e.-`y` for all `a ≤ c`: from the a.e.-`y` a.e.-`x`
  -- slice derivative (`ae_slice_hasDerivAt_of_G`) and `lintegral_nnnorm_deriv_le_eVariationOn`.
  have hVar : ∀ᵐ y : ℝ, ∀ a c : ℝ, a ≤ c →
      ∫⁻ x in Set.Icc a c, ‖deriv (fun s : ℝ => P (G (Complex.mk s y))) x‖₊
        ≤ eVariationOn (fun s : ℝ => P (G (Complex.mk s y))) (Set.Icc a c) := by
    filter_upwards [ae_slice_hasDerivAt_of_G P hGdiff] with y hyderiv a c hac
    exact lintegral_nnnorm_deriv_le_eVariationOn hac hyderiv
  exact NoWanderingDomains.MAF.multiplicityAreaFormula_general P hGcont hGdiff hΦN hVar

/-! ### PIECE 3 — assembly: from the per-slice MAF to per-slice AC

The per-slice no-singular-part bound `eVar (slice y) [a,c] ≤ ∫⁻_{[a,c]} ‖slice'‖` and the proven
variation increment `|slice y x₂ − slice y x₁| ≤ eVar (slice y) [x₁,x₂]` give the increment
domination `|slice y x₂ − slice y x₁| ≤ ∫_{x₁}^{x₂} ‖slice'‖`, and PIECE 2
(`absolutelyContinuousOnInterval_of_increment_le_integral`) yields absolute continuity. -/

/-- **The MAF assembly (general).** Given a family of slices `slice : ℝ → ℝ → ℝ`, each continuous,
with a.e.(`y`) a.e.(`x`) derivative `deriv (slice y) x`, the slice-derivative norm
a.e.(`y`)-interval-integrable, and the per-slice MAF no-singular-part bound, almost every slice is
absolutely continuous on every interval. This packages the increment domination plus PIECE 2.

This is the Banach–Zaretsky upgrade BV ⟹ AC, used by both the inverse
(`ae_slice_AC_horizontal_of_data`) and the forward reverse length–area development. -/
theorem ae_slice_AC_of_maf {slice : ℝ → ℝ → ℝ}
    (_hcont : ∀ y : ℝ, Continuous (slice y))
    (hderiv : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, HasDerivAt (slice y) (deriv (slice y) x) x)
    (hint : ∀ᵐ y : ℝ, ∀ u v : ℝ,
      IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume u v)
    (hmaf : ∀ᵐ y : ℝ, ∀ a c : ℝ,
      eVariationOn (slice y) (Set.Icc a c)
        ≤ ∫⁻ x in Set.Icc a c, ‖deriv (slice y) x‖₊) :
    ∀ᵐ y : ℝ, ∀ a c : ℝ, AbsolutelyContinuousOnInterval (slice y) a c := by
  classical
  -- Work with the a.e.-`y` data simultaneously.
  filter_upwards [hderiv, hint, hmaf] with y hyderiv hyint hymaf a c
  -- Reduce to the increasing case `a ≤ c` (AC is symmetric in the endpoints).
  -- The slice derivative norm `φ x := ‖fderiv ℝ (slice y) x‖`.
  set φ : ℝ → ℝ := fun x => ‖deriv (slice y) x‖ with hφ
  have hφnn : 0 ≤ φ := fun x => norm_nonneg _
  -- The key increment bound for `p ≤ q`: `|slice y q − slice y p| ≤ ∫ₚq φ`.
  have hincr : ∀ {p q : ℝ}, p ≤ q → |slice y q - slice y p| ≤ ∫ t in p..q, φ t := by
    intro p q hpq
    have hmem_p : p ∈ Set.Icc p q := ⟨le_refl p, hpq⟩
    have hmem_q : q ∈ Set.Icc p q := ⟨hpq, le_refl q⟩
    have hφII : IntervalIntegrable φ volume p q := hyint p q
    -- `∫⁻_{[p,q]} ‖deriv‖₊ = ENNReal.ofReal (∫ₚq φ)`, a finite quantity.
    have hlint_eq : ∫⁻ x in Set.Icc p q, ‖deriv (slice y) x‖₊
        = ENNReal.ofReal (∫ t in p..q, φ t) := by
      have hint_pq : IntegrableOn φ (Set.Icc p q) volume := by
        rw [integrableOn_Icc_iff_integrableOn_Ioc]
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mp hφII
      have hstep1 : ∫⁻ x in Set.Icc p q, ‖deriv (slice y) x‖₊
          = ∫⁻ x in Set.Icc p q, ENNReal.ofReal (φ x) := by
        refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
        simp only [hφ]
        exact ((ofReal_norm (deriv (slice y) x)).trans (enorm_eq_nnnorm _)).symm
      rw [hstep1, intervalIntegral.integral_of_le hpq,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_pq
          (Filter.Eventually.of_forall (fun x => hφnn x))]
    -- MAF bounds the variation by `∫⁻ φ`, which is finite, so the variation is finite.
    have hmaf_pq : eVariationOn (slice y) (Set.Icc p q)
        ≤ ENNReal.ofReal (∫ t in p..q, φ t) := by rw [← hlint_eq]; exact hymaf p q
    have hbvfin : eVariationOn (slice y) (Set.Icc p q) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmaf_pq
    -- The increment is bounded by the (finite) variation.
    have hvar : |slice y q - slice y p| ≤ (eVariationOn (slice y) (Set.Icc p q)).toReal := by
      rw [← Real.dist_eq, dist_comm, ← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hbvfin, ← edist_dist]
      exact eVariationOn.edist_le (slice y) hmem_p hmem_q
    -- Chain: `|Δ| ≤ Var.toReal ≤ (∫⁻ φ).toReal = ∫ φ` (φ ≥ 0).
    have hintnn : (0 : ℝ) ≤ ∫ t in p..q, φ t :=
      intervalIntegral.integral_nonneg hpq (fun t _ => hφnn t)
    calc |slice y q - slice y p|
        ≤ (eVariationOn (slice y) (Set.Icc p q)).toReal := hvar
      _ ≤ (ENNReal.ofReal (∫ t in p..q, φ t)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hmaf_pq
      _ = ∫ t in p..q, φ t := ENNReal.toReal_ofReal hintnn
  -- PIECE 2 closes it on `[a, c]` and `[c, a]`; combine via the AC symmetry.
  rcases le_total a c with hac | hca
  · exact absolutelyContinuousOnInterval_of_increment_le_integral hac hφnn hyint
      (fun x z _ hxz hzc => hincr hxz)
  · exact (absolutelyContinuousOnInterval_of_increment_le_integral hca hφnn hyint
      (fun x z _ hxz hzc => hincr hxz)).symm

/-- **Horizontal per-slice AC of a continuous map (general core).** For a continuous `G : ℂ → ℂ`
that is differentiable a.e., whose first-direction partial `w ↦ (DG w) 1` is `L²_loc⊆L¹_loc`, and
whose `P`-component fibered map `Φ p = P(G p)•1 + p.im•I` is Lusin-(N), almost every
horizontal slice
`x ↦ P(G⟨x,y⟩)` is absolutely continuous on every interval. Assembled from the per-slice MAF
(`multiplicityAreaFormula_noSingularPart`), the a.e. slice derivative (`ae_slice_hasDerivAt_of_G`),
and the slice-derivative interval-integrability (`ae_slice_intervalIntegrable_complex`), packaged by
`ae_slice_AC_of_maf`. **Both** inverse directions are instances: the horizontal with `G = g`, the
vertical with `G = g ∘ (coordinate swap)`. -/
private theorem ae_slice_AC_horizontal_of_data {G : ℂ → ℂ} (P : ℂ →L[ℝ] ℝ)
    (hGcont : Continuous G) (hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w)
    (hGpartial : MemLpLocOn (fun w => (fderiv ℝ G w) 1) (2 : ℝ≥0∞) Set.univ)
    (hΦN : ∀ S : Set ℂ, volume S = 0 →
      volume ((fun p : ℂ => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I) '' S) = 0) :
    ∀ᵐ y : ℝ, ∀ a c : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => P (G (Complex.mk x y))) a c := by
  classical
  set slice : ℝ → ℝ → ℝ := fun y x => P (G (Complex.mk x y)) with hslice
  -- (1) Each slice is continuous.
  have hcont : ∀ y : ℝ, Continuous (slice y) := fun y =>
    continuous_slice_component hGcont (fun z => P z) P.continuous y
  -- (2) a.e.-`y` a.e.-`x` derivative.
  have hderiv : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, HasDerivAt (slice y) (deriv (slice y) x) x :=
    ae_slice_hasDerivAt_of_G P hGdiff
  -- (3) The 2D map `H w := (P ((DG w) 1) : ℂ)` is locally integrable.
  set L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp P with hL
  have hHloc : LocallyIntegrable (fun w => L ((fderiv ℝ G w) 1)) volume := by
    have hLmem : MemLpLocOn (fun w => L ((fderiv ℝ G w) 1)) (ENNReal.ofReal 2) Set.univ := by
      intro K hK hKc
      have : IsFiniteMeasure (volume.restrict K) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
      have h2 : MemLp (fun w => (fderiv ℝ G w) 1) (ENNReal.ofReal 2) (volume.restrict K) := by
        have := hGpartial K hK hKc
        rwa [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num] at this
      exact L.comp_memLp' h2
    have hp1 : (1 : ℝ) ≤ 2 := one_le_two
    rw [← locallyIntegrableOn_univ]
    exact locallyIntegrableOn_of_memLpLocOn hp1 hLmem
  -- (4) a.e.-`y` a.e.-`x` identity `deriv (slice y) x = P ((DG ⟨x,y⟩) 1)`.
  have hderivEq : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ,
      deriv (slice y) x = P ((fderiv ℝ G (Complex.mk x y)) 1) := by
    have hae : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ G (Complex.mk x y) := by
      have hnull : volume {w : ℂ | ¬ DifferentiableAt ℝ G w} = 0 := by
        rw [← ae_iff]; exact hGdiff
      filter_upwards [ae_slice_re_null_of_null hnull] with y hy
      rw [ae_iff]; refine measure_mono_null (fun x hx => ?_) hy
      rw [Set.mem_ofPred_eq]; exact hx
    filter_upwards [hae] with y hyae
    filter_upwards [hyae] with x hxdiff
    have hsliceHD : HasDerivAt (slice y) (P ((fderiv ℝ G (Complex.mk x y)) 1)) x := by
      have hfd : HasFDerivAt G (fderiv ℝ G (Complex.mk x y)) (Complex.mk x y) :=
        hxdiff.hasFDerivAt
      have hcomp := hfd.comp_hasDerivAt x (hasDerivAt_mk_left y x)
      have := (P.hasFDerivAt.comp_hasDerivAt x hcomp)
      simpa [hslice] using! this
    exact hsliceHD.deriv
  -- (5) The slice-derivative norm is a.e.-`y`-interval-integrable.
  have hint : ∀ᵐ y : ℝ, ∀ u v : ℝ,
      IntervalIntegrable (fun x => ‖deriv (slice y) x‖) volume u v := by
    have hHslice := ae_slice_intervalIntegrable_complex hHloc
    filter_upwards [hHslice, hderivEq] with y hyint hyeq u v
    have hnorm_int : IntervalIntegrable
        (fun x => ‖L ((fderiv ℝ G (Complex.mk x y)) 1)‖) volume u v := (hyint u v).norm
    refine hnorm_int.congr_ae ?_
    refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hyeq] with x hx
    rw [hx, hL]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
  -- (6) The per-slice MAF.
  have hmaf : ∀ᵐ y : ℝ, ∀ a c : ℝ,
      eVariationOn (slice y) (Set.Icc a c)
        ≤ ∫⁻ x in Set.Icc a c, ‖deriv (slice y) x‖₊ :=
    multiplicityAreaFormula_noSingularPart P hGcont hGdiff hΦN
  -- Package by the general assembly.
  exact ae_slice_AC_of_maf hcont hderiv hint hmaf

/-- **The coordinate swap `⟨x,y⟩ ↦ ⟨y,x⟩` as a continuous linear map.** Used to reduce the vertical
slices of the inverse to the horizontal slices of `g ∘ cswap`. -/
noncomputable def cswapCLM : ℂ →L[ℝ] ℂ :=
  Complex.imCLM.smulRight (1 : ℂ) + Complex.reCLM.smulRight Complex.I

@[simp] theorem cswapCLM_apply (z : ℂ) : cswapCLM z = Complex.mk z.im z.re := by
  have : cswapCLM z = (z.im : ℂ) * 1 + (z.re : ℂ) * Complex.I := by
    simp only [cswapCLM, add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply]
    congr 1
  rw [this]; apply Complex.ext <;> simp

/-- The coordinate swap is volume-preserving (conjugate of `Prod.swap` by `ℂ ≃ ℝ × ℝ`). -/
theorem measurePreserving_cswap :
    MeasurePreserving (fun z : ℂ => Complex.mk z.im z.re) (volume : Measure ℂ) volume := by
  have h1 : MeasurePreserving Complex.measurableEquivRealProd
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
    Complex.volume_preserving_equiv_real_prod
  have h2 : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have h3 : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hcomp := (h3.comp (h2.comp h1))
  convert hcomp using 1
  funext z
  rfl

/-- **Horizontal per-slice AC of the inverse, one component selector.** Instantiates the general
core `ae_slice_AC_horizontal_of_data` with `G = g = f⁻¹`: the fibered Lusin-(N) is
`inverse_fiber_lusinN hf P imCLM`, the partial is `inverse_partial_memLpLocOn hf 1`. -/
private theorem IsQCAnalytic.inverse_ae_slice_AC_horizontal {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (P : ℂ →L[ℝ] ℝ) :
    ∀ᵐ y : ℝ, ∀ a c : ℝ,
      AbsolutelyContinuousOnInterval
        (fun x : ℝ => P ((hf.1.1.homeomorph f).symm (Complex.mk x y))) a c := by
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_invFun
  refine ae_slice_AC_horizontal_of_data P hgcont hf.inverse_differentiableAt_ae
    (hf.inverse_partial_memLpLocOn 1) ?_
  -- The fibered Lusin-(N) `Φ p = P(g p)•1 + p.im•I`, from `inverse_fiber_lusinN hf P imCLM`.
  intro S hS
  have hfib := hf.inverse_fiber_lusinN P Complex.imCLM S hS
  have heq : (fun p : ℂ => (P (g p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I)
      = fun p : ℂ => (P ((hf.1.1.homeomorph f).symm p) : ℝ) • (1 : ℂ)
          + (Complex.imCLM p : ℝ) • Complex.I := by
    funext p; rw [hg]; simp [Complex.imCLM_apply]
  rw [heq]; exact hfib

/-- **Vertical per-slice AC of the inverse, one component selector.** Reduces the vertical slices
`y ↦ P(g⟨x,y⟩)` to the *horizontal* slices of `G := g ∘ cswap` (`cswap⟨x,y⟩ = ⟨y,x⟩`): the chain
rule with the linear `cswap` (`fderiv (g∘cswap) = (fderiv g) ∘ cswap`, `cswap 1 = I`) supplies the
differentiability and `L²_loc` partial from `inverse_differentiableAt_ae` and
`inverse_partial_memLpLocOn hf I`, and the fibered Lusin-(N) from `inverse_fiber_lusinN hf P reCLM`
composed with the volume-preserving `cswap`. -/
private theorem IsQCAnalytic.inverse_ae_slice_AC_vertical {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (P : ℂ →L[ℝ] ℝ) :
    ∀ᵐ x : ℝ, ∀ a c : ℝ,
      AbsolutelyContinuousOnInterval
        (fun y : ℝ => P ((hf.1.1.homeomorph f).symm (Complex.mk x y))) a c := by
  classical
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_invFun
  set G : ℂ → ℂ := fun w => g (cswapCLM w) with hG
  -- The coordinate swap as a `MeasurableEquiv` (measure-preserving + measurable embedding).
  set cswapME : ℂ ≃ᵐ ℂ :=
    (Complex.measurableEquivRealProd.trans (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ))).trans
      Complex.measurableEquivRealProd.symm with hcswapME
  have hcswapME_eq : ∀ z : ℂ, cswapME z = cswapCLM z := by
    intro z
    rw [cswapCLM_apply]
    change Complex.measurableEquivRealProd.symm (Prod.swap (Complex.measurableEquivRealProd z))
      = Complex.mk z.im z.re
    simp [Complex.measurableEquivRealProd_apply, Complex.measurableEquivRealProd_symm_apply,
      Prod.swap]
  have hcswapMP : MeasurePreserving cswapME (volume : Measure ℂ) volume := by
    have hMP : MeasurePreserving (fun z : ℂ => Complex.mk z.im z.re)
        (volume : Measure ℂ) volume := measurePreserving_cswap
    have heqfun : (fun z : ℂ => Complex.mk z.im z.re) = ⇑cswapME := by
      funext z; rw [hcswapME_eq, cswapCLM_apply]
    rwa [heqfun] at hMP
  have hcswapEmb : MeasurableEmbedding cswapME := cswapME.measurableEmbedding
  have hGcont : Continuous G := hgcont.comp cswapCLM.continuous
  -- (a) `G` differentiable a.e.: pull `g`'s a.e. differentiability back along cswap.
  have hgd := hf.inverse_differentiableAt_ae
  have hpb : ∀ᵐ w : ℂ, DifferentiableAt ℝ g (cswapCLM w) := by
    have := hcswapMP.quasiMeasurePreserving.ae hgd
    filter_upwards [this] with w hw; rwa [hcswapME_eq] at hw
  have hGdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ G w := by
    filter_upwards [hpb] with w hw
    exact hw.comp w cswapCLM.differentiableAt
  -- (b) the partial `(fderiv G w) 1 = (fderiv g (cswap w)) I`.
  have hGfderiv : ∀ᵐ w : ℂ, (fderiv ℝ G w) 1 = (fderiv ℝ g (cswapCLM w)) Complex.I := by
    filter_upwards [hpb] with w hw
    have hcomp : HasFDerivAt G ((fderiv ℝ g (cswapCLM w)).comp cswapCLM) w :=
      (hw.hasFDerivAt).comp w cswapCLM.hasFDerivAt
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    congr 1
    rw [cswapCLM_apply]; apply Complex.ext <;> simp
  -- `(fderiv G w) 1` is `L²_loc`: a.e.-equal to `(v ↦ (fderiv g v) I) ∘ cswap`, L²_loc by MP.
  have hGpartial : MemLpLocOn (fun w => (fderiv ℝ G w) 1) (2 : ℝ≥0∞) Set.univ := by
    have hbase : MemLpLocOn (fun w => (fderiv ℝ g w) Complex.I) (2 : ℝ≥0∞) Set.univ :=
      hf.inverse_partial_memLpLocOn Complex.I
    intro K hK hKc
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    have hcswapMEcont : Continuous (cswapME : ℂ → ℂ) := by
      have : (cswapME : ℂ → ℂ) = ⇑cswapCLM := by funext z; rw [hcswapME_eq]
      rw [this]; exact cswapCLM.continuous
    have hKimg : IsCompact (cswapME '' K) := hKc.image hcswapMEcont
    -- `MemLp ((fderiv g · I) ∘ cswap) 2 (restrict K)` via measure-preserving restriction.
    have hMPK : MeasurePreserving cswapME (volume.restrict K) (volume.restrict (cswapME '' K)) :=
      hcswapMP.restrict_image_emb hcswapEmb K
    have hbaseK : MemLp (fun v => (fderiv ℝ g v) Complex.I) (2 : ℝ≥0∞)
        (volume.restrict (cswapME '' K)) := hbase _ (Set.subset_univ _) hKimg
    have hcomp_mem : MemLp ((fun v => (fderiv ℝ g v) Complex.I) ∘ cswapME) (2 : ℝ≥0∞)
        (volume.restrict K) := hbaseK.comp_measurePreserving hMPK
    -- `(fderiv G w) 1 = ((fderiv g · I) ∘ cswap) w` a.e. on `K`.
    refine MemLp.ae_eq ?_ hcomp_mem
    refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hGfderiv] with w hw
    rw [Function.comp_apply, hcswapME_eq]; exact hw.symm
  -- (c) fibered Lusin-(N) for `G`, from `inverse_fiber_lusinN hf P reCLM` + cswap.
  have hΦN : ∀ S : Set ℂ, volume S = 0 →
      volume ((fun p : ℂ => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I) '' S) = 0 := by
    intro S hS
    -- `cswap '' S` is null (cswap measure-preserving equiv).
    have hSnull : volume (cswapME '' S) = 0 := by
      rw [cswapME.image_eq_preimage_symm]
      exact (hcswapMP.symm cswapME).preimage_null hS
    -- `Φ_G p = (Φ_{g,reCLM} ∘ cswap) p` since `(cswap p).re = p.im`.
    have hfib := hf.inverse_fiber_lusinN P Complex.reCLM (cswapME '' S) hSnull
    -- `Φ_G '' S = Φ_{g,reCLM} '' (cswap '' S)`.
    have himg : (fun p : ℂ => (P (G p) : ℝ) • (1 : ℂ) + (p.im : ℝ) • Complex.I) '' S
        = (fun q : ℂ => (P ((hf.1.1.homeomorph f).symm q) : ℝ) • (1 : ℂ)
            + (Complex.reCLM q : ℝ) • Complex.I) '' (cswapME '' S) := by
      rw [Set.image_image]
      apply Set.image_congr
      intro p _
      rw [hG, hcswapME_eq, cswapCLM_apply]
      simp [hg, Complex.reCLM_apply]
    rw [himg]; exact hfib
  -- Apply the general core, then rename coordinates `(y, x) ↦ (x, y)`.
  have hcore := ae_slice_AC_horizontal_of_data P hGcont hGdiff hGpartial hΦN
  filter_upwards [hcore] with x hx a c
  have hslice_eq : (fun y : ℝ => P ((hf.1.1.homeomorph f).symm (Complex.mk x y)))
      = fun y : ℝ => P (G (Complex.mk y x)) := by
    funext y
    have hmk : cswapCLM (Complex.mk y x) = Complex.mk x y := by
      rw [cswapCLM_apply]
    simp only [hG, hmk, hg]
  rw [hslice_eq]; exact hx a c

theorem IsQCAnalytic.inverse_slice_componentAC {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    (∀ᵐ y : ℝ,
      (Continuous (fun x : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).re) ∧
        ∀ a c : ℝ, AbsolutelyContinuousOnInterval
          (fun x : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).re) a c) ∧
      (Continuous (fun x : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).im) ∧
        ∀ a c : ℝ, AbsolutelyContinuousOnInterval
          (fun x : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).im) a c)) ∧
    (∀ᵐ x : ℝ,
      (Continuous (fun y : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).re) ∧
        ∀ a c : ℝ, AbsolutelyContinuousOnInterval
          (fun y : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).re) a c) ∧
      (Continuous (fun y : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).im) ∧
        ∀ a c : ℝ, AbsolutelyContinuousOnInterval
          (fun y : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).im) a c)) := by
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_invFun
  -- Continuity of every slice component (immediate from `g` continuous).
  have hcont_hre : ∀ y : ℝ, Continuous (fun x : ℝ => (g (Complex.mk x y)).re) := fun y =>
    continuous_slice_component hgcont Complex.re Complex.continuous_re y
  have hcont_him : ∀ y : ℝ, Continuous (fun x : ℝ => (g (Complex.mk x y)).im) := fun y =>
    continuous_slice_component hgcont Complex.im Complex.continuous_im y
  have hcont_vre : ∀ x : ℝ, Continuous (fun y : ℝ => (g (Complex.mk x y)).re) := fun x => by
    have he : (fun y : ℝ => (g (Complex.mk x y)).re)
        = fun y : ℝ => Complex.re (g (Complex.mk x y)) := rfl
    rw [he]
    exact Complex.continuous_re.comp (hgcont.comp (by
      have : Continuous (fun y : ℝ => (Complex.mk x y : ℂ)) := by
        have hee : (fun y : ℝ => (Complex.mk x y : ℂ))
            = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
          funext y; apply Complex.ext <;> simp
        rw [hee]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      exact this))
  have hcont_vim : ∀ x : ℝ, Continuous (fun y : ℝ => (g (Complex.mk x y)).im) := fun x => by
    have he : (fun y : ℝ => (g (Complex.mk x y)).im)
        = fun y : ℝ => Complex.im (g (Complex.mk x y)) := rfl
    rw [he]
    exact Complex.continuous_im.comp (hgcont.comp (by
      have : Continuous (fun y : ℝ => (Complex.mk x y : ℂ)) := by
        have hee : (fun y : ℝ => (Complex.mk x y : ℂ))
            = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
          funext y; apply Complex.ext <;> simp
        rw [hee]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      exact this))
  -- AC of slice components: `re`/`im` selectors are `reCLM`/`imCLM`.
  have hre_eq : ∀ z : ℂ, z.re = Complex.reCLM z := fun z => (Complex.reCLM_apply z).symm
  have him_eq : ∀ z : ℂ, z.im = Complex.imCLM z := fun z => (Complex.imCLM_apply z).symm
  have hAC_hre := hf.inverse_ae_slice_AC_horizontal Complex.reCLM
  have hAC_him := hf.inverse_ae_slice_AC_horizontal Complex.imCLM
  have hAC_vre := hf.inverse_ae_slice_AC_vertical Complex.reCLM
  have hAC_vim := hf.inverse_ae_slice_AC_vertical Complex.imCLM
  refine ⟨?_, ?_⟩
  · filter_upwards [hAC_hre, hAC_him] with y hyre hyim
    refine ⟨⟨hcont_hre y, fun a c => ?_⟩, ⟨hcont_him y, fun a c => ?_⟩⟩
    · simpa only [← hre_eq, hg] using hyre a c
    · simpa only [← him_eq, hg] using hyim a c
  · filter_upwards [hAC_vre, hAC_vim] with x hxre hxim
    refine ⟨⟨hcont_vre x, fun a c => ?_⟩, ⟨hcont_vim x, fun a c => ?_⟩⟩
    · simpa only [← hre_eq, hg] using hxre a c
    · simpa only [← him_eq, hg] using hxim a c

/-- **MULTIPLICITY AREA FORMULA — slice monotone-(N) decomposition of the inverse (now PROVEN).**

For an `IsQCAnalytic` map `f` with inverse homeomorphism `g = f⁻¹`, almost every slice component of
`g` admits a **continuous-monotone Jordan decomposition into pieces satisfying Lusin's condition
(N)** (`MonotoneDecompN`): for almost every `y` the horizontal-slice real part
`x ↦ (g⟨x,y⟩).re` and imaginary part `x ↦ (g⟨x,y⟩).im` are continuous-monotone Lusin-(N) diffs,
and symmetrically for almost every `x` and the vertical slices.

This is the classical **Federer area formula with multiplicity** (the `≤` direction), specialised to
the `y`-fibered maps `Φ, Ψ` of the reverse length–area method. In the standard proof one bounds the
total variation of the slice component by the integral of the Banach indicatrix (multiplicity)
function (`eVariationOn_le_lintegral_indicatrix`), which the area formula bounds by the box integral
of `|det DΦ| = |∂ₓ(Re g)|`; combined with the lower bound `Var ≥ ∫|deriv|` this forces equality
(no singular part), i.e. the monotone Jordan pieces satisfy condition (N). Mathlib has only the
**injective** change-of-variables `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, *not* the
multiplicity (non-injective) upper bound, nor the variation lower bound `Var ≥ ∫|deriv|`; both are
supplied in-repo (`MultiplicityAreaFormula.lean`), so this lemma is now PROVEN. The fibered
Lusin-(N) maps that supply the condition-(N) data are fully proven above
(`IsQCAnalytic.inverse_fiber_lusinN`, Steps 1–2), genuinely consuming `f`'s
super-critical weak gradient via Morrey.

**Soundness / shear exclusion.** This statement is *false* for the area-preserving singular shear
`g⟨x,y⟩ = x + i(y + s x)` (`s` continuous strictly-increasing singular): its imaginary slice
`x ↦ y + s x` is a continuous strictly increasing function whose Jordan decomposition is itself,
and it does *not* satisfy condition (N) (it carries the null set on which `s'` is supported to a set
of positive measure). The hypothesis `hf` is load-bearing: `f`'s genuine `W^{1,2}_loc`/Gehring
super-critical structure (consumed by the fibered Lusin-(N) of Steps 1–2 via Morrey) is exactly
what excludes the shear, since the shear has no `Lᵖ`, `p > 2`, weak gradient. -/
theorem IsQCAnalytic.inverse_slice_monotoneDecompN {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    (∀ᵐ y : ℝ,
      MonotoneDecompN (fun x : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).re) ∧
      MonotoneDecompN (fun x : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).im)) ∧
    (∀ᵐ x : ℝ,
      MonotoneDecompN (fun y : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).re) ∧
      MonotoneDecompN (fun y : ℝ => ((⇑(hf.1.1.homeomorph f).symm) (Complex.mk x y)).im)) := by
  -- The four per-slice absolute-continuity facts (the area-formula squeeze residual), each paired
  -- with the slice component's continuity, are produced by `inverse_slice_componentAC`. Brick 1
  -- (`monotoneDecompN_of_continuous_ac`) turns each continuous-AC component into `MonotoneDecompN`.
  obtain ⟨hacx, hacy⟩ := hf.inverse_slice_componentAC
  refine ⟨?_, ?_⟩
  · filter_upwards [hacx] with y hy
    exact ⟨monotoneDecompN_of_continuous_ac hy.1.1 hy.1.2,
      monotoneDecompN_of_continuous_ac hy.2.1 hy.2.2⟩
  · filter_upwards [hacy] with x hx
    exact ⟨monotoneDecompN_of_continuous_ac hx.1.1 hx.1.2,
      monotoneDecompN_of_continuous_ac hx.2.1 hx.2.2⟩

/-- **The genuine slice-absolute-continuity residual (horizontal): almost every horizontal slice of
the quasiconformal inverse is absolutely continuous.** This is the reverse length–area /
Marcus–Mizel "no singular part" content (now PROVEN) that the area-preserving singular shear
violates: its
horizontal slices `y + s ·` are singular, not AC. It is sound and load-bearing on the forward
structure — the shear is *not* the inverse of an `IsQCAnalytic` map because `f`'s genuine
`W^{1,2}_loc` structure (`hf.2.1`) excludes it. The required Federer co-area / multiplicity
area-coupling (absent from Mathlib's injective-only change of variables) is supplied in-repo
(`MultiplicityAreaFormula.lean`, `inverse_slice_monotoneDecompN`), so this is now PROVEN via the
Banach–Zaretsky bridge. The downstream weak gradient and AC walls reduce to this via
the *fully proven* `hasWeakGradient_of_aeSliceAC` (`QC/LengthArea/ReverseLengthArea.lean`). -/
theorem IsQCAnalytic.inverse_slice_absolutelyContinuous_core_x {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∀ᵐ y : ℝ, ∀ a c : ℝ,
      AbsolutelyContinuousOnInterval
        (fun x : ℝ => (⇑(hf.1.1.homeomorph f).symm) ⟨x, y⟩) a c := by
  -- (b') gives, for a.e. `y`, the monotone Jordan decomposition of both slice components; the
  -- Banach–Zaretsky helper turns that into per-interval absolute continuity.
  filter_upwards [hf.inverse_slice_monotoneDecompN.1] with y hdecomp a c
  exact absolutelyContinuousOnInterval_of_monotoneDecompN_pair hdecomp.1 hdecomp.2 a c

/-- **The genuine slice-absolute-continuity residual (vertical): almost every vertical slice of the
quasiconformal inverse is absolutely continuous.** Vertical analogue of
`inverse_slice_absolutelyContinuous_core_x`; same reverse length–area content (now PROVEN), obtained
by symmetry. -/
theorem IsQCAnalytic.inverse_slice_absolutelyContinuous_core_y {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∀ᵐ x : ℝ, ∀ a c : ℝ,
      AbsolutelyContinuousOnInterval
        (fun y : ℝ => (⇑(hf.1.1.homeomorph f).symm) ⟨x, y⟩) a c := by
  -- (b') gives, for a.e. `x`, the monotone Jordan decomposition of both vertical-slice components;
  -- the Banach–Zaretsky helper turns that into per-interval absolute continuity.
  filter_upwards [hf.inverse_slice_monotoneDecompN.2] with x hdecomp a c
  exact absolutelyContinuousOnInterval_of_monotoneDecompN_pair hdecomp.1 hdecomp.2 a c

/-- **The reverse length–area / Stepanov weak gradient of the quasiconformal inverse**
(the single genuine GMT input of the inverse-AC keystone). For an `IsQCAnalytic` map `f`
with inverse homeomorphism `g = f⁻¹`, the a.e.-defined **pointwise** partials
`w ↦ (Dg w) 1`, `w ↦ (Dg w) I` are the **weak (distributional)** directional derivatives of
`g`; equivalently, the distributional gradient of `g` has *no singular part*
(`g ∈ W^{1,1}_loc` with these partials).

## The reverse length–area weak gradient (now PROVEN)

This is the **reverse length–area theorem** specialised to the inverse map. Its
mathematical content is **exactly** the
"no singular part" claim isolated by the two AC walls below. The proof requires the genuine,
irreducibly two-dimensional area-coupling of
the forward map (`hf.2.1 : MemW12loc f`, the modulus/length–area structure) — the required
Federer co-area / multiplicity input (absent from Mathlib's injective-only change of variables)
is supplied in-repo (`MultiplicityAreaFormula.lean`), so it is fully PROVEN here, reduced to the
slice-AC cores below.

## Soundness (sanity-checked against the standard counterexamples)

* **Area-preserving singular shear** `g ⟨x, y⟩ = x + i·(y + s x)` (`s` continuous strictly
  increasing singular, e.g. Minkowski `?`). It is injective, continuous, a.e.-differentiable
  with `Dg = id` a.e. (so it satisfies condition N⁺, the pointwise dilatation bound, and has
  `L²_loc` *pointwise* partials), **yet it fails this conclusion**: its true distributional
  `x`-derivative of the imaginary part is the singular measure `ds`, not the a.e.-pointwise `0`.
  So this lemma is *false* for the shear — and correctly so: the shear is **not** the inverse
  of an `IsQCAnalytic` map (`f`'s genuine `W^{1,2}_loc` structure is what excludes it). The
  hypothesis `hf` is therefore load-bearing and the statement is sound.
* **Pointwise data alone is insufficient** (the FALSE routes the project audited away): this is
  *not* derivable from condition N⁺ + injectivity + `L²_loc` pointwise partials, nor from
  `∫Var ≤ area`, nor from per-line N⁺; all of those are satisfied by the
  shear. The honest extra ingredient is precisely the *weak*-derivative identity, supplied by
  the forward Sobolev/modulus structure.

## The genuine residual, narrowed to slice absolute continuity

By the *fully proven* reduction `hasWeakGradient_of_aeSliceAC`
(`QC/LengthArea/ReverseLengthArea.lean`, the
converse Sobolev embedding *ACL ⇒ W^{1,1}_loc*), this weak-gradient statement follows from the
single fact that **almost every horizontal and vertical slice of `g` is absolutely continuous**,
established below as `inverse_slice_absolutelyContinuous_core_x` / `..._y` (now PROVEN). Those two
carry the genuine Marcus–Mizel reverse length–area content (built in-repo, beyond Mathlib's
injective change of variables); the
local integrability of the pointwise partials and a.e. differentiability are already proven
(`inverse_partial_memLpLocOn`, `inverse_differentiableAt_ae`). -/
theorem IsQCAnalytic.inverse_reverseLengthArea_weakGradient {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    HasWeakGradient (fun w => (fderiv ℝ (⇑(hf.1.1.homeomorph f).symm) w) 1)
      (fun w => (fderiv ℝ (⇑(hf.1.1.homeomorph f).symm) w) Complex.I)
      (⇑(hf.1.1.homeomorph f).symm) Set.univ := by
  -- The inverse homeomorphism `g = f⁻¹`.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_symm
  -- `g` is differentiable almost everywhere (easy inverse function theorem).
  have hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w := IsQCAnalytic.inverse_differentiableAt_ae hf
  -- The pointwise partials are locally integrable: `L²_loc ⊆ L¹_loc`
  -- (`inverse_partial_memLpLocOn`, the inverse-side change-of-variables energy bound).
  have hLIofL2 : ∀ v : ℂ, LocallyIntegrable (fun w => (fderiv ℝ g w) v) := by
    intro v
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp (fun w => (fderiv ℝ g w) v) (2 : ℝ≥0∞) (volume.restrict Kc) :=
      hf.inverse_partial_memLpLocOn v Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  -- The genuine slice-AC residual (both directions).
  have hacx := hf.inverse_slice_absolutelyContinuous_core_x
  have hacy := hf.inverse_slice_absolutelyContinuous_core_y
  -- Assemble via the fully-proven converse Sobolev embedding `ACL ⇒ W^{1,1}_loc`.
  exact hasWeakGradient_of_aeSliceAC hgcont hgdiff (hLIofL2 1) (hLIofL2 Complex.I) hacx hacy

/-- **The inverse's pointwise partials are its weak partials** (the "no singular part" content
of the inverse-is-QC keystone). For an `IsQCAnalytic` map `f` with inverse homeomorphism
`g = f⁻¹`, the a.e.-defined pointwise partials `gx w = (Dg w) 1`, `gy w = (Dg w) I` are the
**weak (distributional)** directional derivatives of `g`, i.e. `g ∈ W^{1,1}_loc` with these
partials. Equivalently, the distributional gradient of `g` has no singular part.

*Proof.* This is exactly the reverse length–area / Stepanov weak gradient of the inverse,
isolated as the single genuine GMT residual `inverse_reverseLengthArea_weakGradient` (the
"no singular part" content). *Dependency:*
`inverse_reverseLengthArea_weakGradient`. -/
theorem IsQCAnalytic.inverse_hasWeakGradient {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    HasWeakGradient (fun w => (fderiv ℝ (⇑(hf.1.1.homeomorph f).symm) w) 1)
      (fun w => (fderiv ℝ (⇑(hf.1.1.homeomorph f).symm) w) Complex.I)
      (⇑(hf.1.1.homeomorph f).symm) Set.univ :=
  hf.inverse_reverseLengthArea_weakGradient

/-- **The inverse lies in `W^{1,2}_loc`.** The inverse homeomorphism `g = f⁻¹` of an
`IsQCAnalytic` map is itself `W^{1,2}_loc`.

*Proof.* `g` is an orientation-preserving homeomorphism (`inverse_orientationPreservingHomeo`),
differentiable a.e. (`inverse_differentiableAt_ae`) with `Dg w = (Df (g w))⁻¹`, so the
inverse-side dilatation inequality (`inverse_fderiv_normSq_le_K_mul_det`) gives the a.e.
energy bound `‖Dg w‖² ≤ K · det (Dg w)` with `K = (1 + ‖b‖∞)/(1 − ‖b‖∞)`. Combined with the
genuine weak gradient of `g` (`inverse_hasWeakGradient`, the "no singular part" content), the
keystone `acl_weakGradient_of_qcInverse` yields absolute continuity on a.e. line with `L²_loc`
partials, and `memWklocP_one_of_acl` packages this as `MemW12loc g`. *Dependency:*
`inverse_orientationPreservingHomeo`, `inverse_differentiableAt_ae`,
`inverse_fderiv_normSq_le_K_mul_det`, `inverse_hasWeakGradient`,
`acl_weakGradient_of_qcInverse`, `memWklocP_one_of_acl`. -/
theorem IsQCAnalytic.inverse_memW12loc {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    MemW12loc (⇑(hf.1.1.homeomorph f).symm) := by
  classical
  -- The inverse homeomorphism `g = f⁻¹` and the standard inverse data.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.1.1 z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
    exact (hf.1.1.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg, ← hfwd z]
    exact (hf.1.1.homeomorph f).symm_apply_apply z
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_symm
  -- `g` is an orientation-preserving homeomorphism (from `inverse_orientationPreservingHomeo`).
  obtain ⟨hghomeo, hdetpos⟩ := IsQCAnalytic.inverse_orientationPreservingHomeo hf
  -- `g` is differentiable almost everywhere.
  have hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w := IsQCAnalytic.inverse_differentiableAt_ae hf
  -- ===== The inverse-side dilatation bound `‖Dg w‖² ≤ K · det (Dg w)` a.e. =====
  -- The constant `K = (1 + c)/(1 - c)` with `c = b.normInf ∈ [0, 1)`.
  set c : ℝ := b.normInf with hc
  have hc0 : 0 ≤ c := b.normInf_nonneg
  have hc1 : c < 1 := b.normInf_lt_one
  set K : ℝ := (1 + c) / (1 - c) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]; apply div_pos <;> linarith
  -- The good set of `w`: `g w ∉ D`, where `f` is differentiable with positive Jacobian at
  -- `g w` and the Beltrami/dilatation data holds. This is the same construction as in
  -- `inverse_differentiableAt_ae`; we additionally pull back the Beltrami bound.
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
  -- Pull a.e. source-side properties back through `g` (via `f`-Lusin-N), exactly as in
  -- `inverse_beltrami`.
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
  -- The Beltrami bound in the form `‖∂̄f (g w)‖ ≤ c · ‖∂f (g w)‖`.
  have hbelbnd : ∀ᵐ w, ‖dzbar f (g w)‖ ≤ c * ‖dz f (g w)‖ := by
    filter_upwards [hbelw, hμbndw] with w hbel hμ
    rw [hbel, norm_mul]
    exact mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
  -- The inverse-derivative identity `Dg w = (Df (g w))⁻¹` a.e. (easy inverse function theorem).
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
  -- Assemble the dilatation bound on `g`.
  have hdil : ∀ᵐ w, ‖fderiv ℝ g w‖ ^ 2 ≤ K * (fderiv ℝ g w).det := by
    filter_upwards [hfdetposw, hbelbnd, hgderivw] with w hwdet hwbel hwgderiv
    exact inverse_fderiv_normSq_le_K_mul_det hc0 hc1 hwdet hwbel hwgderiv
  -- ===== The genuine weak gradient of `g` (the one remaining honest wall). =====
  obtain ⟨hweakx, hweaky⟩ := IsQCAnalytic.inverse_hasWeakGradient hf
  -- ===== Assemble ACL + L²_loc via the keystone, then `memWklocP_one_of_acl`. =====
  obtain ⟨gx, gy, haclx, hacly, hgxL2, hgyL2⟩ :=
    acl_weakGradient_of_qcInverse hKpos hghomeo hgdiff hdetpos hdil hweakx hweaky
  -- The keystone produces ACL with the explicit pointwise partials; recover them.
  -- Local integrability of `g`, `gx`, `gy`.
  have hgLI : LocallyIntegrable g := hgcont.locallyIntegrable
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict Kc) := hh Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hgxLI : LocallyIntegrable gx := hLIofL2 hgxL2
  have hgyLI : LocallyIntegrable gy := hLIofL2 hgyL2
  -- `g ∈ L²_loc` (it is continuous, hence locally bounded, hence locally `L²` on compacts).
  have hgL2 : MemLpLocOn g (2 : ℝ≥0∞) Set.univ := by
    intro Kc _ hKc
    have hfin : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hgcont.continuousOn
    have hmeas : AEStronglyMeasurable g (volume.restrict Kc) :=
      hgcont.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict Kc), ‖g x‖ ≤ C := by
      rw [ae_restrict_iff' hKc.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hmeas C hbound).mono_exponent le_top
  -- Assemble.
  exact memWklocP_one_of_acl hgL2 hgxL2 hgyL2 hgLI hgxLI hgyLI haclx hacly

/-- **The inverse of an analytic-quasiconformal map is analytic-quasiconformal**
(the ROOT). The inverse homeomorphism `g = f⁻¹` of an `IsQCAnalytic` map satisfies
`IsQCAnalytic g b'` for some Beltrami coefficient `b'`.

*Proof sketch.* Assemble the three `IsQCAnalytic` fields for `g`:
`inverse_orientationPreservingHomeo`, `inverse_memW12loc`, and the Beltrami
equation from `inverse_beltrami` (whose `b'` is the witness). *Dependency:*
`inverse_beltrami`, `inverse_memW12loc`,
`inverse_orientationPreservingHomeo`. -/
theorem IsQCAnalytic.inverse_isQCAnalytic {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ b' : BeltramiCoeff, IsQCAnalytic (⇑(hf.1.1.homeomorph f).symm) b' := by
  obtain ⟨b', _, hbel⟩ := hf.inverse_beltrami
  exact ⟨b', hf.inverse_orientationPreservingHomeo, hf.inverse_memW12loc, hbel⟩

/-- **The inverse of an analytic-quasiconformal map is analytic-quasiconformal, with the
Beltrami norm controlled by that of `f`.** The inverse homeomorphism `g = f⁻¹` of an
`IsQCAnalytic` map satisfies `IsQCAnalytic g b'` for a Beltrami coefficient `b'` whose
essential-sup norm does not exceed that of `b` (indeed the reflected coefficient has the
same pointwise modulus as `b`). The `normInf` bound is the quantitative refinement of
`IsQCAnalytic.inverse_isQCAnalytic` needed to propagate a dilatation bound `(K−1)/(K+1)`
from `f` to `g`. *Dependency:* `inverse_beltrami`, `inverse_memW12loc`,
`inverse_orientationPreservingHomeo`. -/
theorem IsQCAnalytic.inverse_isQCAnalytic' {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ b' : BeltramiCoeff, b'.normInf ≤ b.normInf ∧
      IsQCAnalytic (⇑(hf.1.1.homeomorph f).symm) b' := by
  obtain ⟨b', hb'le, hbel⟩ := hf.inverse_beltrami
  exact ⟨b', hb'le, hf.inverse_orientationPreservingHomeo, hf.inverse_memW12loc, hbel⟩

end NoWanderingDomains
