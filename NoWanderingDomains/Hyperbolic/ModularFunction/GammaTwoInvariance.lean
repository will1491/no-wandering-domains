/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularFunction.JacobiIdentity

/-! # Omitted values, `Γ(2)`-invariance, and the action pillars

The omitted values `λ(τ) ≠ 0` and `λ(τ) ≠ 1` on `ℍ`; `Γ(2)`-invariance of `λ` via the
generator decomposition of `Γ(2)` into `T²`, `S T⁻² S`, and `−I` by Euclidean reduction
on matrix entries; holomorphy of `λ` on the upper half-plane. The two `SL₂(ℤ)`-action
pillars of the covering-map proof: torsion-freeness of `Γ(2)` modulo `±I` on `ℍ` and
proper discontinuity of the `Γ(2)`-action. Finally the disk version
`modularLambda : 𝔻 → ℂ ∖ {0, 1}` with its omitted values and holomorphy.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

/-! ## Range and omitted values of `λ` -/

/-- `λ(τ) ≠ 0` for `τ ∈ ℍ`. Directly from `θ₂(τ) ≠ 0` and
`θ₃(τ) ≠ 0`: `λ(τ) = θ₂⁴/θ₃⁴`, and `θ₂⁴ ≠ 0`. -/
theorem modularLambdaH_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH τ ≠ 0 := by
  unfold modularLambdaH
  have h2 := theta2_ne_zero hτ
  have h3 := theta3_ne_zero hτ
  exact div_ne_zero (pow_ne_zero 4 h2) (pow_ne_zero 4 h3)

/-- `λ(τ) ≠ 1` for `τ ∈ ℍ`. Combines Jacobi's identity
`θ₂⁴ + θ₄⁴ = θ₃⁴` (giving `λ = 1 − (θ₄/θ₃)⁴`) with `θ₄(τ) ≠ 0`. -/
theorem modularLambdaH_ne_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH τ ≠ 1 := by
  unfold modularLambdaH
  have h2 := theta2_ne_zero hτ
  have h3 := theta3_ne_zero hτ
  have h4 := theta4_ne_zero hτ
  have h3_pow : (theta3 τ)^4 ≠ 0 := pow_ne_zero 4 h3
  have h_jacobi : theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := jacobi_identity hτ
  intro h_eq
  -- λ = θ₂⁴/θ₃⁴ = 1 means θ₂⁴ = θ₃⁴.
  have h_theta2_pow_eq : theta2 τ ^ 4 = theta3 τ ^ 4 := by
    have h_eq' := h_eq
    field_simp at h_eq'
    exact h_eq'
  -- Combined with Jacobi: θ₄⁴ = 0.
  have h_theta4_pow_zero : theta4 τ ^ 4 = 0 := by
    linear_combination h_jacobi - h_theta2_pow_eq
  -- Hence θ₄ = 0, contradicting theta4_ne_zero.
  have h_theta4 : theta4 τ = 0 :=
    (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp h_theta4_pow_zero
  exact h4 h_theta4

/-! ## Modular invariance under `Γ(2)`

`Γ(2) := { γ ∈ SL₂(ℤ) | γ ≡ I (mod 2) }` is generated (as a subgroup
of `SL₂(ℤ)`) by the three matrices

  `T² = [[1, 2], [0, 1]]`,   `U := S T⁻² S = [[1, 0], [2, 1]]`,
  `-I = [[-1, 0], [0, -1]]`.

The first two act on the upper half-plane by `τ ↦ τ + 2` and
`τ ↦ τ / (2τ + 1)`, both of which preserve `λ` by
`modularLambdaH_two_add` and `modularLambdaH_div_two_tau_add_one`.
`-I` acts trivially via `SL_neg_smul`. The generator-decomposition
lemma `gamma_two_le_closure_three_gens` is proved by an explicit
Euclidean reduction on the matrix entries `(a, c)`, using the parity
constraints `a ≡ d ≡ 1`, `b ≡ c ≡ 0 (mod 2)` to force the residues
to lie strictly inside the Euclidean window. -/

/-- `(-1 : SL(2,ℤ))` acts trivially on the upper half-plane, so
`λ` is invariant under it. -/
theorem modularLambdaH_neg_one_smul (τ : UpperHalfPlane) :
    modularLambdaH (((-1 : SL(2, ℤ)) • τ : UpperHalfPlane) : ℂ)
      = modularLambdaH (τ : ℂ) := by
  have h : ((-1 : SL(2, ℤ)) • τ : UpperHalfPlane) = τ := by
    show -(1 : SL(2, ℤ)) • τ = τ
    rw [ModularGroup.SL_neg_smul, one_smul]
  rw [h]

/-- `T² : SL(2,ℤ)` acts as `τ ↦ τ + 2` on the upper half-plane.
Combined with `modularLambdaH_two_add` this gives `T²`-invariance of `λ`. -/
theorem modularLambdaH_T_sq_smul (τ : UpperHalfPlane) :
    modularLambdaH (((ModularGroup.T ^ (2 : ℤ)) • τ : UpperHalfPlane) : ℂ)
      = modularLambdaH (τ : ℂ) := by
  rw [ModularGroup.coe_T_zpow_smul_eq]
  push_cast
  exact modularLambdaH_two_add (τ : ℂ)

/-- `S * T⁻² * S : SL(2,ℤ)` acts as `τ ↦ τ / (2τ + 1)` on the upper
half-plane. Combined with `modularLambdaH_div_two_tau_add_one` this
gives `U`-invariance of `λ`. -/
theorem modularLambdaH_S_T_neg_two_S_smul (τ : UpperHalfPlane) :
    modularLambdaH
        (((ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S)
          • τ : UpperHalfPlane) : ℂ)
      = modularLambdaH (τ : ℂ) := by
  have hτ_im : 0 < (τ : ℂ).im := τ.2
  have hτ_ne : (τ : ℂ) ≠ 0 := fun h => by rw [h] at hτ_im; exact lt_irrefl 0 hτ_im
  have h_2τp1_ne : (2 * (τ : ℂ) + 1) ≠ 0 := by
    have h_im_eq : (2 * (τ : ℂ) + 1).im = 2 * (τ : ℂ).im := by
      simp [Complex.add_im, Complex.mul_im, Complex.one_im]
    intro h
    rw [h, Complex.zero_im] at h_im_eq
    linarith
  -- Decompose via mul_smul.
  rw [mul_smul, mul_smul]
  -- Compute innermost S • τ.
  have h1 : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -((τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, neg_inv]
  -- Compute T^(-2) • (S • τ).
  have h2 : ((ModularGroup.T ^ (-2 : ℤ) • (ModularGroup.S • τ) : UpperHalfPlane) : ℂ)
      = -((τ : ℂ))⁻¹ - 2 := by
    rw [ModularGroup.coe_T_zpow_smul_eq, h1]; push_cast; ring
  -- Rewrite outer S; result is the Möbius form τ/(2τ+1).
  have h3 :
      ((ModularGroup.S • (ModularGroup.T ^ (-2 : ℤ) • (ModularGroup.S • τ))
        : UpperHalfPlane) : ℂ) = (τ : ℂ) / (2 * (τ : ℂ) + 1) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, h2]
    rw [show (-(-(τ : ℂ)⁻¹ - 2) : ℂ) = ((τ : ℂ)⁻¹ + 2) from by ring]
    rw [show ((τ : ℂ)⁻¹ + 2 : ℂ) = ((1 + 2 * (τ : ℂ)) / (τ : ℂ)) from by field_simp]
    rw [inv_div, show (1 + 2 * (τ : ℂ) : ℂ) = 2 * (τ : ℂ) + 1 from by ring]
  rw [h3]
  exact modularLambdaH_div_two_tau_add_one hτ_im

/-- The matrix `U := (-1) * (S * T⁻² * S)` equals `[[1, 0], [2, 1]]`. -/
theorem U_matrix_val :
    ∀ (i j : Fin 2),
      ((((-1 : SL(2, ℤ)) *
        (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S))
        : SL(2, ℤ)).val) i j
        = (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  intro i j
  have h_eq : ((((-1 : SL(2, ℤ)) *
        (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S))
        : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
        = (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, ModularGroup.coe_S,
        ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply]
  exact h_eq

/-- The matrix of `U^k = ((-1)·(S T⁻² S))^k` equals `[[1, 0], [2k, 1]]`
for any `k : ℤ`. Proved by induction on `k`. -/
theorem U_matrix_zpow_val (k : ℤ) :
    ∀ (i j : Fin 2),
      (((((-1 : SL(2, ℤ)) *
        (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S))
        : SL(2, ℤ)) ^ k).val) i j
        = (!![1, 0; 2 * k, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  -- Define the SL element for brevity and the matrix equality.
  set U : SL(2, ℤ) :=
    (-1 : SL(2, ℤ)) *
      (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S) with hU_def
  have h_U_val : ∀ (i j : Fin 2),
      ((U : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
        = (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := U_matrix_val
  -- Nat-power case.
  have h_pow_nat : ∀ (n : ℕ), ∀ (i j : Fin 2),
      ((U ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
        = (!![1, 0; 2 * (n : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro n
    induction n with
    | zero =>
      intro i j
      have : ((U ^ 0 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [pow_zero]; exact Matrix.SpecialLinearGroup.coe_one
      rw [this]
      fin_cases i <;> fin_cases j <;> simp
    | succ m ih =>
      intro i j
      have h_succ : ((U ^ (m + 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          = ((U ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            ((U : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul]
      rw [h_succ]
      have h_ih_eq : ((U ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          = !![1, 0; 2 * (m : ℤ), 1] := by
        ext i' j'
        exact ih i' j'
      have h_U_eq : ((U : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2, 1] := by
        ext i' j'; exact h_U_val i' j'
      rw [h_ih_eq, h_U_eq]
      push_cast
      fin_cases i <;> fin_cases j <;>
        (simp [Matrix.mul_apply, Fin.sum_univ_succ]; try ring)
  -- Generic integer case: split by `Int.induction_on`.
  intro i j
  induction k using Int.induction_on with
  | zero =>
    rw [zpow_zero]
    change ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
    rw [Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  | succ m ih =>
    rw [show ((m : ℤ) + 1) = (((m + 1 : ℕ)) : ℤ) from by push_cast; ring, zpow_natCast]
    exact h_pow_nat (m + 1) i j
  | pred m ih =>
    -- Goal: U^(-(m+1)) entry. Use zpow_neg + zpow_natCast to reduce to inverse of U^(m+1).
    rw [show (-(m : ℤ) - 1) = -((m + 1 : ℕ) : ℤ) from by push_cast; ring]
    rw [zpow_neg, zpow_natCast]
    -- (((U^(m+1))⁻¹ : SL(2,ℤ)) : Matrix) i j: compute via inverse.
    have h_pow : ((U ^ (m + 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = !![1, 0; 2 * ((m + 1 : ℕ) : ℤ), 1] := by
      ext i' j'
      exact h_pow_nat (m + 1) i' j'
    have h_inv_val : (((U ^ (m + 1))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = !![1, 0; -(2 * ((m + 1 : ℕ) : ℤ)), 1] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, h_pow]
      rw [Matrix.adjugate_fin_two_of]
      ext i' j'
      fin_cases i' <;> fin_cases j' <;> simp
    rw [h_inv_val]
    fin_cases i <;> fin_cases j <;> (simp; try ring)

/-- `T² ∈ Γ(2)`: the matrix `[[1, 2], [0, 1]]` reduces to `I` mod 2. -/
theorem T_sq_mem_gamma_two : ModularGroup.T ^ (2 : ℤ) ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  have h_val := ModularGroup.coe_T_zpow (2 : ℤ)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [h_val]; decide)

/-- `S * T⁻² * S ∈ Γ(2)`: the matrix `[[-1, 0], [-2, -1]]` reduces to `I` mod 2. -/
theorem S_T_neg_two_S_mem_gamma_two :
    (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S)
      ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  have h_eq : ∀ (i j : Fin 2),
      ((ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S
        : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
      = (!![-1, 0; -2, -1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ModularGroup.coe_S, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h_eq] <;> decide

/-- `(-1) ∈ Γ(2)`: the matrix `[[-1, 0], [0, -1]]` reduces to `I` mod 2. -/
theorem neg_one_mem_gamma_two : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (change (((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ _ : ZMod 2) = _ ;
     rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] ;
     decide)

/-- **Generator decomposition for `Γ(2)`.** Every element of `Γ(2)` lies
in the subgroup of `SL₂(ℤ)` generated by `T²`, `S * T⁻² * S`, and `-1`.
The proof is an Euclidean reduction on `|a| + |c|` (where
`a = γ 0 0`, `c = γ 1 0`), using `T^{±2}` to shift `a` and
`(S T⁻² S)^{±1}` to shift `c`; the parity `a` odd, `c` even forces
the residue inequalities to be strict. -/
theorem gamma_two_le_closure_three_gens :
    CongruenceSubgroup.Gamma 2 ≤
      Subgroup.closure ({ModularGroup.T ^ (2 : ℤ),
        ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S,
        (-1 : SL(2, ℤ))} : Set (SL(2, ℤ))) := by
  set H : Subgroup (SL(2, ℤ)) := Subgroup.closure
    ({ModularGroup.T ^ (2 : ℤ),
      ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S,
      (-1 : SL(2, ℤ))} : Set (SL(2, ℤ))) with hH_def
  -- The three generators lie in `H`.
  have hT2_in : ModularGroup.T ^ (2 : ℤ) ∈ H :=
    Subgroup.subset_closure (by simp)
  have hM_in :
      (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S) ∈ H :=
    Subgroup.subset_closure (by simp)
  have hN_in : (-1 : SL(2, ℤ)) ∈ H :=
    Subgroup.subset_closure (by simp)
  -- Derived: `U := (-1) * M ∈ H` (where `M = S T⁻² S`; note `U` has matrix `[[1,0],[2,1]]`).
  have hU_in : ((-1 : SL(2, ℤ)) *
      (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S)) ∈ H :=
    Subgroup.mul_mem H hN_in hM_in
  -- Strong induction on the size `n` bounding `|a| + |c|`.
  suffices key : ∀ (n : ℕ) (γ : SL(2, ℤ)),
      γ ∈ CongruenceSubgroup.Gamma 2 →
      (γ.val 0 0).natAbs + (γ.val 1 0).natAbs ≤ n →
      γ ∈ H by
    intro γ hγ
    exact key _ γ hγ le_rfl
  intro n
  induction n with
  | zero =>
    intro γ hγ hbound
    -- `a.natAbs ≤ 0 ⟹ a = 0`, but `a ≡ 1 (mod 2)` ⟹ `a ≠ 0`.
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    obtain ⟨ha, _, _, _⟩ := hγ
    have h_a_natAbs : (γ.val 0 0).natAbs = 0 := by omega
    have h_a_zero : γ.val 0 0 = 0 := Int.natAbs_eq_zero.mp h_a_natAbs
    rw [h_a_zero] at ha
    exact absurd ha (by decide)
  | succ n ih =>
    intro γ hγ hbound
    by_cases hc : γ.val 1 0 = 0
    · -- **Base case `c = 0`.** Then `det γ = a*d = 1` with `a, d` odd,
      -- so `(a, d) ∈ {(1,1), (-1,-1)}`, and `b = 2k` even from `Γ(2)`.
      have h_det_eq : γ.val 0 0 * γ.val 1 1 = 1 := by
        have h := γ.det_coe
        rw [Matrix.det_fin_two, hc] at h
        linarith
      have hγ' := hγ
      rw [CongruenceSubgroup.Gamma_mem] at hγ'
      obtain ⟨_, hb_zmod, _, _⟩ := hγ'
      have h_b_dvd : (2 : ℤ) ∣ γ.val 0 1 := by
        have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ.val 0 1) 2).mp hb_zmod
        exact_mod_cast h
      obtain ⟨k, hk⟩ := h_b_dvd
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h_det_eq with ⟨ha, hd⟩ | ⟨ha, hd⟩
      · -- Case `(a, d) = (1, 1)`: `γ = T^(2k) = (T²)^k`.
        have hγ_eq : γ = (ModularGroup.T ^ (2 : ℤ)) ^ k := by
          apply Subtype.ext
          rw [show ((ModularGroup.T ^ (2 : ℤ)) ^ k : SL(2, ℤ))
              = ModularGroup.T ^ (2 * k : ℤ) from (zpow_mul _ 2 k).symm]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [ModularGroup.coe_T_zpow, ha, hd, hc, hk, mul_comm 2 k]
        rw [hγ_eq]
        exact Subgroup.zpow_mem H hT2_in k
      · -- Case `(a, d) = (-1, -1)`: `γ = (-1) · (T²)^(-k)`.
        have hγ_eq : γ = (-1 : SL(2, ℤ)) * (ModularGroup.T ^ (2 : ℤ)) ^ (-k : ℤ) := by
          apply Subtype.ext
          show γ.val = ((-1 : SL(2, ℤ)) * (ModularGroup.T ^ (2 : ℤ)) ^ (-k : ℤ)).val
          have h_pow_eq : ((ModularGroup.T ^ (2 : ℤ)) ^ (-k : ℤ) : SL(2, ℤ))
              = ModularGroup.T ^ (-2 * k : ℤ) := by
            rw [← zpow_mul]; congr 1; ring
          rw [show ((-1 : SL(2, ℤ)) * (ModularGroup.T ^ (2 : ℤ)) ^ (-k : ℤ)).val
              = -((ModularGroup.T ^ (2 : ℤ)) ^ (-k : ℤ)).val from by
            rw [Matrix.SpecialLinearGroup.coe_mul,
              Matrix.SpecialLinearGroup.coe_neg,
              Matrix.SpecialLinearGroup.coe_one, neg_one_mul]]
          rw [h_pow_eq]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [ModularGroup.coe_T_zpow, ha, hd, hc, hk]
        rw [hγ_eq]
        exact Subgroup.mul_mem H hN_in (Subgroup.zpow_mem H hT2_in _)
    · -- **Reduction.** Use `T^(±2)` or `U = -1·M` (matrix `[[1,0],[2,1]]`) to
      -- shift `(a, c)` toward `(odd, 0)` via Euclidean division. By the parity
      -- constraints `a` odd, `c` even, the residue inequalities are strict, so
      -- `|a| + |c|` strictly decreases in each step.
      have hγ' := hγ
      rw [CongruenceSubgroup.Gamma_mem] at hγ'
      obtain ⟨ha_zmod, _, hc_zmod, _⟩ := hγ'
      -- Parity & positivity facts.
      have hc_2_dvd : (2 : ℤ) ∣ γ.val 1 0 := by
        have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ.val 1 0) 2).mp hc_zmod
        exact_mod_cast h
      have hc_natAbs_pos : 0 < (γ.val 1 0).natAbs := Int.natAbs_pos.mpr hc
      have ha_odd : Odd (γ.val 0 0) := by
        rw [Int.odd_iff]
        rcases Int.emod_two_eq (γ.val 0 0) with h0 | h1
        · exfalso
          have hdvd : (2 : ℤ) ∣ γ.val 0 0 := Int.dvd_of_emod_eq_zero h0
          have h0_zmod : (γ.val 0 0 : ZMod 2) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hdvd)
          rw [h0_zmod] at ha_zmod; exact absurd ha_zmod (by decide)
        · exact h1
      have ha_natAbs_odd : Odd (γ.val 0 0).natAbs := Int.natAbs_odd.mpr ha_odd
      have ha_natAbs_pos : 0 < (γ.val 0 0).natAbs := Odd.pos ha_natAbs_odd
      have hc_natAbs_even : Even (γ.val 1 0).natAbs := by
        obtain ⟨q, hq⟩ := hc_2_dvd
        refine ⟨q.natAbs, ?_⟩
        rw [hq, Int.natAbs_mul]; push_cast; ring
      -- Parity ⟹ `|a| ≠ |c|`.
      have h_aNe_c : (γ.val 0 0).natAbs ≠ (γ.val 1 0).natAbs := by
        intro h
        rw [h] at ha_natAbs_odd
        exact (Nat.not_odd_iff_even.mpr hc_natAbs_even) ha_natAbs_odd
      rcases lt_or_gt_of_ne h_aNe_c with h_aLt | h_aGt
      · -- **Sub-case B: `|a| < |c|`.** Apply `U^k` (matrix `[[1,0],[2k,1]]`)
        -- to reduce `c` modulo `2a`.
        set m_nat : ℕ := 2 * (γ.val 0 0).natAbs with hm_def
        have hm_pos : 0 < m_nat := by rw [hm_def]; omega
        set r : ℤ := (γ.val 1 0).bmod m_nat with hr_def
        obtain ⟨q', hq'⟩ : ∃ q' : ℤ, γ.val 1 0 = q' * (m_nat : ℤ) + r := by
          have hdvd : (m_nat : ℤ) ∣ (γ.val 1 0 - r) := by
            have h1 : (γ.val 1 0 - r) % (m_nat : ℤ) = 0 := by
              rw [hr_def, Int.sub_emod, Int.bmod_emod]; simp
            exact Int.dvd_of_emod_eq_zero h1
          obtain ⟨q', hq'⟩ := hdvd
          exact ⟨q', by linarith⟩
        have hr_lt : r < (γ.val 0 0).natAbs := by
          have h := @Int.bmod_lt (γ.val 1 0) m_nat hm_pos
          have hmcast : ((m_nat : ℤ) + 1) / 2 = (γ.val 0 0).natAbs := by
            rw [hm_def]; push_cast; omega
          rw [hmcast] at h; exact h
        have hr_ge : -((γ.val 0 0).natAbs : ℤ) ≤ r := by
          have h := @Int.le_bmod (γ.val 1 0) m_nat hm_pos
          have hmcast : (m_nat : ℤ) / 2 = (γ.val 0 0).natAbs := by
            rw [hm_def]; push_cast; omega
          rw [hmcast] at h; exact h
        -- `r` is even (since `c` is even and `q'·m` is even).
        have hr_even : Even r := by
          have hc_even_z : Even (γ.val 1 0) := by
            obtain ⟨q, hq⟩ := hc_2_dvd
            refine ⟨q, ?_⟩; linarith
          have hm_eq : (m_nat : ℤ) = 2 * (γ.val 0 0).natAbs := by
            rw [hm_def]; push_cast; ring
          have hm_even : Even ((m_nat : ℤ)) := ⟨(γ.val 0 0).natAbs, by rw [hm_eq]; ring⟩
          have hqm_even : Even (q' * (m_nat : ℤ)) := hm_even.mul_left q'
          have h_sub_even : Even (γ.val 1 0 - q' * (m_nat : ℤ)) :=
            hc_even_z.sub hqm_even
          have hr_eq : r = γ.val 1 0 - q' * (m_nat : ℤ) := by linarith
          rw [hr_eq]; exact h_sub_even
        have hr_natAbs_lt : r.natAbs < (γ.val 0 0).natAbs := by
          have h_abs_le : r.natAbs ≤ (γ.val 0 0).natAbs := by omega
          rcases lt_or_eq_of_le h_abs_le with h | h
          · exact h
          · exfalso
            have hr_natAbs_even : Even r.natAbs := Int.natAbs_even.mpr hr_even
            rw [h] at hr_natAbs_even
            exact (Nat.not_odd_iff_even.mpr hr_natAbs_even) ha_natAbs_odd
        -- Define `k_red := -q' · sign(a)`. Then `2*k_red*a + c = r`.
        set k_red : ℤ := -q' * (γ.val 0 0).sign with hk_def
        have h_sign_a : (γ.val 0 0).sign * γ.val 0 0 = ((γ.val 0 0).natAbs : ℤ) := by
          have h_ne : γ.val 0 0 ≠ 0 := by
            intro hz; rw [hz] at ha_natAbs_pos; simp at ha_natAbs_pos
          have hss : (γ.val 0 0).sign * (γ.val 0 0).sign = 1 := by
            rcases lt_or_gt_of_ne h_ne with h_neg | h_pos
            · have h_s : (γ.val 0 0).sign = -1 :=
                Int.sign_eq_neg_one_iff_neg.mpr h_neg
              rw [h_s]; decide
            · have h_s : (γ.val 0 0).sign = 1 :=
                Int.sign_eq_one_iff_pos.mpr h_pos
              rw [h_s]; decide
          have h_eq : (γ.val 0 0).sign * γ.val 0 0 =
              (γ.val 0 0).sign * ((γ.val 0 0).sign * ((γ.val 0 0).natAbs : ℤ)) := by
            congr 1; exact (Int.sign_mul_natAbs _).symm
          rw [h_eq, ← mul_assoc, hss, one_mul]
        have h_2kac_eq_r : 2 * k_red * γ.val 0 0 + γ.val 1 0 = r := by
          rw [hk_def]
          have h_factor : 2 * (-q' * (γ.val 0 0).sign) * γ.val 0 0
              = -2 * q' * ((γ.val 0 0).sign * γ.val 0 0) := by ring
          rw [h_factor, h_sign_a]
          have hm_int : (m_nat : ℤ) = 2 * (γ.val 0 0).natAbs := by
            rw [hm_def]; push_cast; ring
          linear_combination hq' + q' * hm_int
        -- Set up the `U` element. Show `U ∈ Γ(2)`.
        set U_elt : SL(2, ℤ) := (-1 : SL(2, ℤ)) *
          (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S) with hU_elt_def
        have hU_in_Gamma : U_elt ∈ CongruenceSubgroup.Gamma 2 :=
          Subgroup.mul_mem _ neg_one_mem_gamma_two S_T_neg_two_S_mem_gamma_two
        have hU_pow_in_Gamma : U_elt ^ k_red ∈ CongruenceSubgroup.Gamma 2 :=
          Subgroup.zpow_mem _ hU_in_Gamma k_red
        -- `U^k_red ∈ H`.
        have hU_pow_in_H : U_elt ^ k_red ∈ H := Subgroup.zpow_mem H hU_in k_red
        -- `γ' := U^k_red * γ`. `γ' ∈ Γ(2)`.
        set γ' : SL(2, ℤ) := U_elt ^ k_red * γ with hγ'_def
        have hγ'_in_Gamma : γ' ∈ CongruenceSubgroup.Gamma 2 :=
          Subgroup.mul_mem _ hU_pow_in_Gamma hγ
        -- Matrix entries of `γ'`.
        have h_U_00 : ((U_elt ^ k_red : SL(2, ℤ)).val) 0 0 = 1 :=
          U_matrix_zpow_val k_red 0 0
        have h_U_01 : ((U_elt ^ k_red : SL(2, ℤ)).val) 0 1 = 0 :=
          U_matrix_zpow_val k_red 0 1
        have h_U_10 : ((U_elt ^ k_red : SL(2, ℤ)).val) 1 0 = 2 * k_red :=
          U_matrix_zpow_val k_red 1 0
        have h_U_11 : ((U_elt ^ k_red : SL(2, ℤ)).val) 1 1 = 1 :=
          U_matrix_zpow_val k_red 1 1
        have hγ'_00 : γ'.val 0 0 = γ.val 0 0 := by
          change ((U_elt ^ k_red * γ : SL(2, ℤ)).val) 0 0 = γ.val 0 0
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]
          change ((U_elt ^ k_red : SL(2, ℤ)).val) 0 0 * γ.val 0 0 +
              Finset.sum Finset.univ (fun i : Fin 1 =>
                ((U_elt ^ k_red : SL(2, ℤ)).val) 0 (Fin.succ i) * γ.val (Fin.succ i) 0)
              = γ.val 0 0
          simp [h_U_00, h_U_01]
        have hγ'_10 : γ'.val 1 0 = r := by
          change ((U_elt ^ k_red * γ : SL(2, ℤ)).val) 1 0 = r
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]
          change ((U_elt ^ k_red : SL(2, ℤ)).val) 1 0 * γ.val 0 0 +
              Finset.sum Finset.univ (fun i : Fin 1 =>
                ((U_elt ^ k_red : SL(2, ℤ)).val) 1 (Fin.succ i) * γ.val (Fin.succ i) 0)
              = r
          simp [h_U_10, h_U_11]
          linarith [h_2kac_eq_r]
        have hγ'_bound : (γ'.val 0 0).natAbs + (γ'.val 1 0).natAbs ≤ n := by
          rw [hγ'_00, hγ'_10]
          omega
        have hγ'_in_H : γ' ∈ H := ih γ' hγ'_in_Gamma hγ'_bound
        have hγ_eq : γ = (U_elt ^ k_red)⁻¹ * γ' := by
          rw [hγ'_def]; group
        rw [hγ_eq]
        exact Subgroup.mul_mem H (Subgroup.inv_mem H hU_pow_in_H) hγ'_in_H
      · -- **Sub-case A: `|a| > |c|`.** Apply `(T²)^k` (matrix `[[1,2k],[0,1]]`)
        -- to reduce `a` modulo `2c`.
        set m_nat : ℕ := 2 * (γ.val 1 0).natAbs with hm_def
        have hm_pos : 0 < m_nat := by rw [hm_def]; omega
        set r : ℤ := (γ.val 0 0).bmod m_nat with hr_def
        obtain ⟨q', hq'⟩ : ∃ q' : ℤ, γ.val 0 0 = q' * (m_nat : ℤ) + r := by
          have hdvd : (m_nat : ℤ) ∣ (γ.val 0 0 - r) := by
            have h1 : (γ.val 0 0 - r) % (m_nat : ℤ) = 0 := by
              rw [hr_def, Int.sub_emod, Int.bmod_emod]; simp
            exact Int.dvd_of_emod_eq_zero h1
          obtain ⟨q', hq'⟩ := hdvd
          exact ⟨q', by linarith⟩
        have hr_lt : r < (γ.val 1 0).natAbs := by
          have h := @Int.bmod_lt (γ.val 0 0) m_nat hm_pos
          have hmcast : ((m_nat : ℤ) + 1) / 2 = (γ.val 1 0).natAbs := by
            rw [hm_def]; push_cast; omega
          rw [hmcast] at h; exact h
        have hr_ge : -((γ.val 1 0).natAbs : ℤ) ≤ r := by
          have h := @Int.le_bmod (γ.val 0 0) m_nat hm_pos
          have hmcast : (m_nat : ℤ) / 2 = (γ.val 1 0).natAbs := by
            rw [hm_def]; push_cast; omega
          rw [hmcast] at h; exact h
        have hr_odd : Odd r := by
          have hm_eq : (m_nat : ℤ) = 2 * (γ.val 1 0).natAbs := by
            rw [hm_def]; push_cast; ring
          have hm_even : Even ((m_nat : ℤ)) := ⟨(γ.val 1 0).natAbs, by rw [hm_eq]; ring⟩
          have hqm_even : Even (q' * (m_nat : ℤ)) := hm_even.mul_left q'
          have h_sub_odd : Odd (γ.val 0 0 - q' * (m_nat : ℤ)) :=
            ha_odd.sub_even hqm_even
          have hr_eq : r = γ.val 0 0 - q' * (m_nat : ℤ) := by linarith
          rw [hr_eq]; exact h_sub_odd
        have hr_natAbs_lt : r.natAbs < (γ.val 1 0).natAbs := by
          have h_abs_le : r.natAbs ≤ (γ.val 1 0).natAbs := by omega
          rcases lt_or_eq_of_le h_abs_le with h | h
          · exact h
          · exfalso
            have hr_natAbs_odd : Odd r.natAbs := Int.natAbs_odd.mpr hr_odd
            rw [h] at hr_natAbs_odd
            exact (Nat.not_odd_iff_even.mpr hc_natAbs_even) hr_natAbs_odd
        -- Define `k_red := -q' · sign(c)`. Then `a + 2*k_red*c = r`.
        set k_red : ℤ := -q' * (γ.val 1 0).sign with hk_def
        have h_sign_c : (γ.val 1 0).sign * γ.val 1 0 = ((γ.val 1 0).natAbs : ℤ) := by
          have h_ne : γ.val 1 0 ≠ 0 := hc
          have hss : (γ.val 1 0).sign * (γ.val 1 0).sign = 1 := by
            rcases lt_or_gt_of_ne h_ne with h_neg | h_pos
            · have h_s : (γ.val 1 0).sign = -1 :=
                Int.sign_eq_neg_one_iff_neg.mpr h_neg
              rw [h_s]; decide
            · have h_s : (γ.val 1 0).sign = 1 :=
                Int.sign_eq_one_iff_pos.mpr h_pos
              rw [h_s]; decide
          have h_eq : (γ.val 1 0).sign * γ.val 1 0 =
              (γ.val 1 0).sign * ((γ.val 1 0).sign * ((γ.val 1 0).natAbs : ℤ)) := by
            congr 1; exact (Int.sign_mul_natAbs _).symm
          rw [h_eq, ← mul_assoc, hss, one_mul]
        have h_a_plus_2kc_eq_r : γ.val 0 0 + 2 * k_red * γ.val 1 0 = r := by
          rw [hk_def]
          have h_factor : 2 * (-q' * (γ.val 1 0).sign) * γ.val 1 0
              = -2 * q' * ((γ.val 1 0).sign * γ.val 1 0) := by ring
          rw [h_factor, h_sign_c]
          have hm_int : (m_nat : ℤ) = 2 * (γ.val 1 0).natAbs := by
            rw [hm_def]; push_cast; ring
          linear_combination hq' + q' * hm_int
        -- `T²^k_red ∈ Γ(2)` and ∈ `H`.
        have hT2_pow_in_Gamma :
            (ModularGroup.T ^ (2 : ℤ)) ^ k_red ∈ CongruenceSubgroup.Gamma 2 :=
          Subgroup.zpow_mem _ T_sq_mem_gamma_two k_red
        have hT2_pow_in_H : (ModularGroup.T ^ (2 : ℤ)) ^ k_red ∈ H :=
          Subgroup.zpow_mem H hT2_in k_red
        -- `γ' := T²^k_red * γ`.
        set γ' : SL(2, ℤ) := (ModularGroup.T ^ (2 : ℤ)) ^ k_red * γ with hγ'_def
        have hγ'_in_Gamma : γ' ∈ CongruenceSubgroup.Gamma 2 :=
          Subgroup.mul_mem _ hT2_pow_in_Gamma hγ
        -- Matrix of `T²^k_red = T^(2*k_red)`.
        have hT2_pow_val : ∀ (i j : Fin 2),
            ((ModularGroup.T ^ (2 : ℤ)) ^ k_red : SL(2, ℤ)).val i j
              = (!![1, 2 * k_red; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
          intro i j
          have hT2_eq : ((ModularGroup.T ^ (2 : ℤ)) ^ k_red : SL(2, ℤ))
              = ModularGroup.T ^ (2 * k_red : ℤ) := by rw [← zpow_mul]
          rw [hT2_eq]
          have h := ModularGroup.coe_T_zpow (2 * k_red)
          change ((ModularGroup.T ^ (2 * k_red : ℤ) : SL(2, ℤ)) :
              Matrix (Fin 2) (Fin 2) ℤ) i j = _
          rw [h]
        have hγ'_00 : γ'.val 0 0 = r := by
          change (((ModularGroup.T ^ (2 : ℤ)) ^ k_red * γ : SL(2, ℤ)).val) 0 0 = r
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]
          have h0 := hT2_pow_val 0 0
          have h1 := hT2_pow_val 0 1
          simp at h0 h1
          simp [h0, h1]
          linarith [h_a_plus_2kc_eq_r]
        have hγ'_10 : γ'.val 1 0 = γ.val 1 0 := by
          change (((ModularGroup.T ^ (2 : ℤ)) ^ k_red * γ : SL(2, ℤ)).val) 1 0 = γ.val 1 0
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]
          have h0 := hT2_pow_val 1 0
          have h1 := hT2_pow_val 1 1
          simp at h0 h1
          simp [h0, h1]
        have hγ'_bound : (γ'.val 0 0).natAbs + (γ'.val 1 0).natAbs ≤ n := by
          rw [hγ'_00, hγ'_10]
          omega
        have hγ'_in_H : γ' ∈ H := ih γ' hγ'_in_Gamma hγ'_bound
        have hγ_eq : γ = ((ModularGroup.T ^ (2 : ℤ)) ^ k_red)⁻¹ * γ' := by
          rw [hγ'_def]; group
        rw [hγ_eq]
        exact Subgroup.mul_mem H (Subgroup.inv_mem H hT2_pow_in_H) hγ'_in_H

/-- **`Γ(2)`-invariance of `λ` on `ℍ`.** For every
`γ ∈ Γ(2) ⊂ SL₂(ℤ)` and every `τ ∈ ℍ`, `λ(γ·τ) = λ(τ)`. Proof:
`gamma_two_le_closure_three_gens` reduces to the three generators
`T²`, `S T⁻² S`, `-I`, each of which is handled by
`modularLambdaH_T_sq_smul`, `modularLambdaH_S_T_neg_two_S_smul`, and
`modularLambdaH_neg_one_smul`. -/
theorem modularLambdaH_gamma2_invariant
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (_hγ : γ ∈ CongruenceSubgroup.Gamma 2) (τ : UpperHalfPlane) :
    modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ)
      = modularLambdaH (τ : ℂ) := by
  -- Reduce `γ ∈ Γ(2)` to `γ ∈ closure({T², ST⁻²S, -1})`.
  have hγ_in_closure := gamma_two_le_closure_three_gens _hγ
  -- The action-preservation property for all `τ` simultaneously.
  suffices h : ∀ (g : SL(2, ℤ)), g ∈ Subgroup.closure
      ({ModularGroup.T ^ (2 : ℤ),
        ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S,
        (-1 : SL(2, ℤ))} : Set (SL(2, ℤ))) →
      ∀ τ : UpperHalfPlane,
      modularLambdaH ((g • τ : UpperHalfPlane) : ℂ)
        = modularLambdaH (τ : ℂ) by
    exact h γ hγ_in_closure τ
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    intro τ
    rcases hx with h_eq | h_eq | h_eq
    · rw [h_eq]; exact modularLambdaH_T_sq_smul τ
    · rw [h_eq]; exact modularLambdaH_S_T_neg_two_S_smul τ
    · rw [h_eq]; exact modularLambdaH_neg_one_smul τ
  | one =>
    intro τ; rw [one_smul]
  | mul x y _ _ ihx ihy =>
    intro τ; rw [mul_smul, ihx, ihy]
  | inv x _ ih =>
    intro τ
    have h_eq : (x : SL(2, ℤ)) • (x⁻¹ • τ : UpperHalfPlane) = τ := by
      rw [← mul_smul, mul_inv_cancel, one_smul]
    have h_inv :
        modularLambdaH ((x • (x⁻¹ • τ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
          = modularLambdaH ((x⁻¹ • τ : UpperHalfPlane) : ℂ) :=
      ih (x⁻¹ • τ : UpperHalfPlane)
    rw [h_eq] at h_inv
    exact h_inv.symm

/-! ## Holomorphy -/

/-- `λ` is holomorphic on the upper half-plane. Follows from
`theta3_ne_zero` on `ℍ` together with the differentiability of the
theta nullwerte. -/
theorem modularLambdaH_differentiableOn :
    DifferentiableOn ℂ modularLambdaH { τ : ℂ | 0 < τ.im } := by
  intro τ hτ
  have hτ_pos : 0 < τ.im := hτ
  have h3 : theta3 τ ≠ 0 := theta3_ne_zero hτ_pos
  have h3_pow : (theta3 τ)^4 ≠ 0 := pow_ne_zero 4 h3
  unfold modularLambdaH
  apply DifferentiableAt.differentiableWithinAt
  refine DifferentiableAt.div ?_ ?_ h3_pow
  · exact (theta2_differentiableAt hτ_pos).pow 4
  · exact (theta3_differentiableAt hτ_pos).pow 4

/-! ## `Γ(2)`-action on `ℍ`: torsion-freeness and proper discontinuity

The two pillars of the covering-map proof that depend only on the
`SL₂(ℤ)`-action live here. The remaining pillars (`λ' ≠ 0` and
orbit identification) require Step D and live in
`ModularCoveringMap/`. -/

/-- **Pillar 1: `Γ(2)` is torsion-free modulo `±I` on `ℍ`.** Any
`γ ∈ Γ(2)` with a fixed point in `ℍ` is `±I`. Proof by trace
analysis: an elliptic element of `SL₂(ℤ)` has `|tr γ| < 2`, hence
`tr γ ∈ {-1, 0, 1}`; for `γ ∈ Γ(2)`, `tr γ ≡ a + d ≡ 0 (mod 2)`, so
`tr γ = 0`. But a trace-zero `γ ∈ Γ(2)` has `bc = -a² - 1 ≡ 2 (mod 4)`
while `bc ≡ 0 (mod 4)` from evenness — contradiction. -/
theorem gamma_two_fixed_point_implies_pm_one
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma 2)
    (τ : UpperHalfPlane) (h_fixed : γ • τ = τ) :
    γ = 1 ∨ γ = -1 := by
  -- Set up entries.
  set a : ℤ := γ.val 0 0 with ha_def
  set b : ℤ := γ.val 0 1 with hb_def
  set c : ℤ := γ.val 1 0 with hc_def
  set d : ℤ := γ.val 1 1 with hd_def
  -- Determinant condition.
  have h_det : a * d - b * c = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    linarith
  -- Γ(2) parity conditions.
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨ha_zmod, hb_zmod, hc_zmod, hd_zmod⟩ := hγ
  have h_a_odd : a % 2 = 1 := by
    rcases Int.emod_two_eq a with h0 | h1
    · exfalso
      have h_dvd : (2 : ℤ) ∣ a := Int.dvd_of_emod_eq_zero h0
      have h0_zmod : (a : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h_dvd)
      rw [h0_zmod] at ha_zmod
      exact absurd ha_zmod (by decide)
    · exact h1
  have h_d_odd : d % 2 = 1 := by
    rcases Int.emod_two_eq d with h0 | h1
    · exfalso
      have h_dvd : (2 : ℤ) ∣ d := Int.dvd_of_emod_eq_zero h0
      have h0_zmod : (d : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h_dvd)
      rw [h0_zmod] at hd_zmod
      exact absurd hd_zmod (by decide)
    · exact h1
  have h_b_even : (2 : ℤ) ∣ b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp (by exact_mod_cast hb_zmod)
  have h_c_even : (2 : ℤ) ∣ c :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd c 2).mp (by exact_mod_cast hc_zmod)
  -- Imaginary part of τ.
  have h_im_pos : 0 < (τ : ℂ).im := τ.2
  have h_im_ne : (τ : ℂ).im ≠ 0 := ne_of_gt h_im_pos
  -- Möbius form of the fixed-point equation.
  have h_fixed_coe : ((γ • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) := by rw [h_fixed]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h_fixed_coe
  simp only [algebraMap_int_eq, eq_intCast] at h_fixed_coe
  push_cast at h_fixed_coe
  rw [show ((γ.val 0 0 : ℤ) : ℂ) = (a : ℂ) from rfl,
      show ((γ.val 0 1 : ℤ) : ℂ) = (b : ℂ) from rfl,
      show ((γ.val 1 0 : ℤ) : ℂ) = (c : ℂ) from rfl,
      show ((γ.val 1 1 : ℤ) : ℂ) = (d : ℂ) from rfl] at h_fixed_coe
  -- h_fixed_coe : ((a:ℂ) * τ + b) / ((c:ℂ) * τ + d) = τ
  -- Step 2: denominator nonzero, polynomial form.
  have h_denom_ne : ((c : ℂ) * (τ : ℂ) + (d : ℂ)) ≠ 0 := by
    intro h
    by_cases hc_zero_int : c = 0
    · rw [hc_zero_int, Int.cast_zero, zero_mul, zero_add] at h
      have hd_zero : d = 0 := by exact_mod_cast h
      omega
    · have h_im : ((c : ℂ) * (τ : ℂ) + (d : ℂ)).im = (c : ℝ) * (τ : ℂ).im := by
        simp [Complex.add_im, Complex.mul_im, Complex.intCast_im, Complex.intCast_re]
      rw [h, Complex.zero_im] at h_im
      rcases mul_eq_zero.mp h_im.symm with h1 | h1
      · exact hc_zero_int (by exact_mod_cast h1)
      · exact h_im_ne h1
  -- Multiply through: (a τ + b) = τ (c τ + d).
  have h_mul : (a : ℂ) * (τ : ℂ) + (b : ℂ) =
      (τ : ℂ) * ((c : ℂ) * (τ : ℂ) + (d : ℂ)) := by
    have h_eq : (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((c : ℂ) * (τ : ℂ) + (d : ℂ))) *
        ((c : ℂ) * (τ : ℂ) + (d : ℂ)) =
        (τ : ℂ) * ((c : ℂ) * (τ : ℂ) + (d : ℂ)) := by
      rw [h_fixed_coe]
    rw [div_mul_cancel₀ _ h_denom_ne] at h_eq
    exact h_eq
  -- Polynomial form: c τ² + (d - a) τ - b = 0.
  have h_poly : (c : ℂ) * (τ : ℂ)^2 + ((d : ℂ) - (a : ℂ)) * (τ : ℂ) - (b : ℂ) = 0 := by
    linear_combination -h_mul
  -- Step 3: take imaginary part.
  -- (cτ² + (d-a)τ - b).im = c·Im(τ²) + (d-a)·τ.im - 0
  --                       = c·2·τ.re·τ.im + (d-a)·τ.im
  --                       = τ.im · (2cτ.re + (d-a))
  have h_im_eq : (τ : ℂ).im * (2 * (c : ℝ) * (τ : ℂ).re + ((d : ℝ) - (a : ℝ))) = 0 := by
    have h_poly_im : ((c : ℂ) * (τ : ℂ)^2 + ((d : ℂ) - (a : ℂ)) * (τ : ℂ) -
        (b : ℂ)).im = 0 := by rw [h_poly]; simp
    have h_τsq_im : ((τ : ℂ)^2).im = 2 * (τ : ℂ).re * (τ : ℂ).im := by
      rw [sq, Complex.mul_im]; ring
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.intCast_im,
      Complex.intCast_re, zero_mul, add_zero, Complex.sub_re, sub_zero,
      h_τsq_im] at h_poly_im
    linarith
  -- Since τ.im ≠ 0, the bracket vanishes.
  have h_lin : 2 * (c : ℝ) * (τ : ℂ).re + ((d : ℝ) - (a : ℝ)) = 0 := by
    rcases mul_eq_zero.mp h_im_eq with h | h
    · exact absurd h h_im_ne
    · exact h
  -- Step 4: case split on c.
  by_cases hc_zero : c = 0
  · -- Case c = 0: from h_lin, d = a; det gives a² = 1; h_poly gives b = 0.
    have h_d_eq_a : d = a := by
      have h_real_eq : (d : ℝ) = (a : ℝ) := by
        rw [hc_zero] at h_lin
        push_cast at h_lin
        linarith
      exact_mod_cast h_real_eq
    have h_ad : a * d = 1 := by
      rw [hc_zero] at h_det; linarith
    rw [h_d_eq_a] at h_ad
    -- a² = 1 ⟹ a = ±1.
    have ha_pm : a = 1 ∨ a = -1 := by
      have h_a_sq : a * a = 1 := h_ad
      have : a = 1 ∨ a = -1 := by
        rcases lt_trichotomy a 0 with h_neg | h_zero | h_pos
        · right; nlinarith
        · exfalso; rw [h_zero] at h_a_sq; linarith
        · left; nlinarith
      exact this
    -- From h_poly with c = 0, d = a: (a - a) τ - b = 0, so b = 0.
    have h_b_zero : b = 0 := by
      rw [hc_zero, h_d_eq_a] at h_poly
      push_cast at h_poly
      have : -(b : ℂ) = 0 := by linear_combination h_poly
      have : (b : ℂ) = 0 := by linear_combination -this
      exact_mod_cast this
    -- Conclude γ = ±I.
    rcases ha_pm with ha_one | ha_neg
    · left
      apply Subtype.ext
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;>
        simp [← ha_def, ← hb_def, ← hc_def, ← hd_def,
          ha_one, h_b_zero, hc_zero, h_d_eq_a]
    · right
      apply Subtype.ext
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;>
        simp [← ha_def, ← hb_def, ← hc_def, ← hd_def,
          ha_neg, h_b_zero, hc_zero, h_d_eq_a]
  · -- Case c ≠ 0: derive contradiction via discriminant + parity.
    exfalso
    have hc_real_ne : (c : ℝ) ≠ 0 := by exact_mod_cast hc_zero
    -- From h_lin: τ.re = (a - d) / (2c).
    have h_τre : (τ : ℂ).re = ((a : ℝ) - (d : ℝ)) / (2 * (c : ℝ)) := by
      have h_2c_ne : (2 * (c : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hc_real_ne
      field_simp
      linarith
    -- Real part of h_poly: c·(τ.re² - τ.im²) + (d-a)·τ.re - b = 0.
    have h_re_eq : (c : ℝ) * ((τ : ℂ).re^2 - (τ : ℂ).im^2) +
        ((d : ℝ) - (a : ℝ)) * (τ : ℂ).re - (b : ℝ) = 0 := by
      have h_poly_re : ((c : ℂ) * (τ : ℂ)^2 + ((d : ℂ) - (a : ℂ)) * (τ : ℂ) -
          (b : ℂ)).re = 0 := by rw [h_poly]; simp
      have h_τsq_re : ((τ : ℂ)^2).re = (τ : ℂ).re^2 - (τ : ℂ).im^2 := by
        rw [sq, Complex.mul_re]; ring
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.intCast_re,
        Complex.intCast_im, zero_mul, sub_zero, Complex.sub_im,
        h_τsq_re] at h_poly_re
      linarith
    -- Substitute τ.re into h_re_eq and clear to get the discriminant equation.
    -- c · ((a-d)²/(4c²) - τ.im²) + (d-a)·(a-d)/(2c) - b = 0
    -- Multiply by 4c²:
    -- c · (a-d)² - 4c³·τ.im² + 2c·(d-a)(a-d) - 4c²·b = 0
    -- c·(a-d)² - 4c³·τ.im² - 2c·(a-d)² - 4c²·b = 0
    -- -c·(a-d)² - 4c³·τ.im² - 4c²·b = 0
    -- ÷(-c): (a-d)² + 4c²·τ.im² + 4cb = 0
    -- So (a-d)² + 4bc = -4c²·τ.im².
    have h_disc_eq : ((a : ℝ) - (d : ℝ))^2 + 4 * (b : ℝ) * (c : ℝ) =
        -(4 * (c : ℝ)^2 * (τ : ℂ).im^2) := by
      have h_2c_ne : (2 * (c : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hc_real_ne
      have h := h_re_eq
      rw [h_τre] at h
      field_simp at h
      nlinarith [h]
    -- Use det: (a-d)² + 4bc = (a+d)² - 4 since ad - bc = 1.
    have h_disc_trace : ((a : ℝ) - (d : ℝ))^2 + 4 * (b : ℝ) * (c : ℝ) =
        ((a : ℝ) + (d : ℝ))^2 - 4 := by
      have h_det_real : ((a : ℝ)) * ((d : ℝ)) - ((b : ℝ)) * ((c : ℝ)) = 1 := by
        exact_mod_cast h_det
      nlinarith [h_det_real]
    -- Therefore (a+d)² - 4 = -4c²·τ.im² < 0 ⟹ (a+d)² < 4.
    have h_trace_sq_lt : ((a : ℝ) + (d : ℝ))^2 < 4 := by
      have h_τim_sq_pos : 0 < (τ : ℂ).im^2 := by positivity
      have h_c_sq_pos : 0 < (c : ℝ)^2 := by positivity
      nlinarith [h_disc_eq, h_disc_trace, h_τim_sq_pos, h_c_sq_pos]
    -- |a + d| < 2 as integer.
    have h_trace_int_bound : |a + d| < 2 := by
      have h_abs_sq : ((|a + d| : ℤ) : ℝ)^2 < 4 := by
        push_cast
        rw [_root_.sq_abs]
        exact_mod_cast h_trace_sq_lt
      have h_abs_nn : 0 ≤ |a + d| := abs_nonneg _
      have h_abs_real : 0 ≤ ((|a + d| : ℤ) : ℝ) := by exact_mod_cast h_abs_nn
      have h_lt_real : ((|a + d| : ℤ) : ℝ) < 2 := by nlinarith [h_abs_sq, h_abs_real]
      exact_mod_cast h_lt_real
    -- a + d is even (both odd) and |a + d| < 2 ⟹ a + d = 0.
    have h_trace_eq : a + d = 0 := by
      have h_sum_mod : (a + d) % 2 = 0 := by omega
      have h_sum_range : -2 < a + d ∧ a + d < 2 := abs_lt.mp h_trace_int_bound
      omega
    -- d = -a, bc = -a² - 1 ≡ 2 (mod 4), but b, c even ⟹ bc ≡ 0 (mod 4). Contradiction.
    have h_d_eq_neg_a : d = -a := by linarith
    have h_bc : b * c = -(a * a) - 1 := by
      rw [h_d_eq_neg_a] at h_det
      linarith
    obtain ⟨b', hb'⟩ := h_b_even
    obtain ⟨c', hc'⟩ := h_c_even
    have h_a_sq_mod : (a * a) % 4 = 1 := by
      have h_k : ∃ k : ℤ, a = 2 * k + 1 := ⟨a / 2, by omega⟩
      obtain ⟨k, hk⟩ := h_k
      rw [hk]
      have h_eq : (2*k + 1) * (2*k + 1) = 4 * (k*k + k) + 1 := by ring
      rw [h_eq]
      omega
    have h_bc_mod : (b * c) % 4 = 0 := by
      rw [hb', hc']
      have : 2 * b' * (2 * c') = 4 * (b' * c') := by ring
      omega
    rw [h_bc] at h_bc_mod
    omega

set_option maxHeartbeats 400000 in
-- The Mobius entry-bound chain (compactness extractions for `ε_K`, `M_K`,
-- `R_K`, `ε_L`, `R_L`, the imaginary-part identity, the denominator-norm
-- bound, and the linear bound on `γ.val 1 1`) compiles a long arithmetic
-- term that exceeds the default heartbeat budget during elaboration.
/-- Entry-bound helper for Pillar 2. For compact `K, L ⊆ ℍ`, there is an
integer `N` such that every `γ ∈ SL₂(ℤ)` moving a point of `K` into `L`
has all entries bounded by `N` in absolute value. Used to reduce
proper discontinuity to a finite-matrix-box argument. The proof:
extract `ε_K, M_K, R_K, ε_L, R_L` from compactness; bound
`normSq (γ.val 1 0 · z + γ.val 1 1) ≤ M_K / ε_L` via the imaginary-part
identity `Im(γ • z) = Im(z) / normSq(denom γ z)`; from this bound on
`normSq` extract `|c|, |d|` bounds via the `(c·x + d)² + (c·y)²`
expansion; bound `|a|, |b|` similarly using `γ • z = (a z + b)/(c z + d)`
and `|γ • z| ≤ R_L`. -/
theorem gamma_two_smul_entry_bound
    {K L : Set UpperHalfPlane} (hK : IsCompact K) (hL : IsCompact L) :
    ∃ N : ℕ, ∀ (γ : SL(2, ℤ)) (z : UpperHalfPlane),
      z ∈ K → γ • z ∈ L → ∀ (i j : Fin 2), |γ.val i j| ≤ (N : ℤ) := by
  -- Empty K or L: vacuous.
  by_cases hK_ne : K.Nonempty
  swap
  · exact ⟨0, fun _ z hz _ _ _ => absurd ⟨z, hz⟩ hK_ne⟩
  by_cases hL_ne : L.Nonempty
  swap
  · exact ⟨0, fun _ _ _ h _ _ => absurd ⟨_, h⟩ hL_ne⟩
  -- Compactness bounds.
  have hImK : IsCompact ((fun z : UpperHalfPlane => (z : ℂ).im) '' K) :=
    hK.image (by fun_prop)
  have hImL : IsCompact ((fun z : UpperHalfPlane => (z : ℂ).im) '' L) :=
    hL.image (by fun_prop)
  obtain ⟨ε_K, ⟨z_K, hz_K_in, hz_K_im⟩, hε_K_min⟩ := hImK.exists_isLeast (hK_ne.image _)
  have hε_K_pos : 0 < ε_K := hz_K_im ▸ z_K.2
  obtain ⟨M_K, hM_K⟩ := hImK.bddAbove
  obtain ⟨ε_L, ⟨z_L, hz_L_in, hz_L_im⟩, hε_L_min⟩ := hImL.exists_isLeast (hL_ne.image _)
  have hε_L_pos : 0 < ε_L := hz_L_im ▸ z_L.2
  have hKC : IsCompact ((fun z : UpperHalfPlane => (z : ℂ)) '' K) :=
    hK.image UpperHalfPlane.continuous_coe
  have hLC : IsCompact ((fun z : UpperHalfPlane => (z : ℂ)) '' L) :=
    hL.image UpperHalfPlane.continuous_coe
  obtain ⟨R_K, _, hR_K⟩ := hKC.isBounded.subset_closedBall_lt 0 0
  obtain ⟨R_L, _, hR_L⟩ := hLC.isBounded.subset_closedBall_lt 0 0
  have hM_K_pos : 0 < M_K := lt_of_lt_of_le hε_K_pos (hM_K ⟨z_K, hz_K_in, hz_K_im⟩)
  have hR_K_nn : 0 ≤ R_K := by
    have h := hR_K ⟨z_K, hz_K_in, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact (norm_nonneg _).trans h
  have hR_L_nn : 0 ≤ R_L := by
    have h := hR_L ⟨z_L, hz_L_in, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact (norm_nonneg _).trans h
  set Q : ℝ := M_K / ε_L with hQ_def
  have hQ_pos : 0 < Q := div_pos hM_K_pos hε_L_pos
  have hsQ_nn : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  -- The aggregate real bound.
  set B : ℝ := Real.sqrt Q / ε_K + Real.sqrt Q + R_K * Real.sqrt Q / ε_K +
    R_L * Real.sqrt Q / ε_K + R_L * Real.sqrt Q + R_K * R_L * Real.sqrt Q / ε_K with hB_def
  have hB_nn : 0 ≤ B := by rw [hB_def]; positivity
  refine ⟨⌈B⌉₊, fun γ z hz_K h_γz_L i j => ?_⟩
  -- Per-γ bounds at the witness z.
  have hz_im_ge : ε_K ≤ (z : ℂ).im := hε_K_min ⟨z, hz_K, rfl⟩
  have hz_im_le : (z : ℂ).im ≤ M_K := hM_K ⟨z, hz_K, rfl⟩
  have hz_im_pos : 0 < (z : ℂ).im := z.2
  have hγz_im_ge : ε_L ≤ (γ • z : UpperHalfPlane).im := hε_L_min ⟨γ • z, h_γz_L, rfl⟩
  have hγz_im_pos : 0 < (γ • z : UpperHalfPlane).im := (γ • z).2
  have hz_re_le : |(z : ℂ).re| ≤ R_K := by
    have h := hR_K ⟨z, hz_K, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact (Complex.abs_re_le_norm _).trans h
  have hγz_norm_le : ‖((γ • z : UpperHalfPlane) : ℂ)‖ ≤ R_L := by
    have h := hR_L ⟨γ • z, h_γz_L, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  -- Entry abbreviations.
  set a : ℤ := γ.val 0 0 with ha_def
  set b : ℤ := γ.val 0 1 with hb_def
  set c : ℤ := γ.val 1 0 with hc_def
  set d : ℤ := γ.val 1 1 with hd_def
  -- Express γ • z via the Möbius formula on ℂ.
  have h_γz_eq : ((γ • z : UpperHalfPlane) : ℂ) =
      ((a : ℂ) * (z : ℂ) + (b : ℂ)) / ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast]
    push_cast; ring
  -- denom ≠ 0 by positive imaginary part.
  have h_denom_ne : ((c : ℂ) * (z : ℂ) + (d : ℂ)) ≠ 0 := by
    intro hzero
    have h_γz_re : ((γ • z : UpperHalfPlane) : ℂ).re = 0 := by
      rw [h_γz_eq, hzero]; simp
    have h_γz_im : ((γ • z : UpperHalfPlane) : ℂ).im = 0 := by
      rw [h_γz_eq, hzero]; simp
    have h_im_val : (γ • z : UpperHalfPlane).im = ((γ • z : UpperHalfPlane) : ℂ).im := rfl
    rw [h_im_val, h_γz_im] at hγz_im_pos
    exact lt_irrefl 0 hγz_im_pos
  -- normSq(cz + d) = z.im / (γ • z).im via im of the Möbius quotient.
  have h_normSq_pos : 0 < Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) :=
    Complex.normSq_pos.mpr h_denom_ne
  have h_normSq_eq : Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) =
      (z : ℂ).im / (γ • z : UpperHalfPlane).im := by
    have h_im_val : (γ • z : UpperHalfPlane).im = ((γ • z : UpperHalfPlane) : ℂ).im := rfl
    have h_det : (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) = 1 := by
      have := γ.det_coe
      rw [Matrix.det_fin_two] at this
      exact_mod_cast this
    have h_γz_im_eq : ((γ • z : UpperHalfPlane) : ℂ).im =
        (z : ℂ).im / Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by
      rw [h_γz_eq, Complex.div_im]
      have h_num : ((a : ℂ) * (z : ℂ) + (b : ℂ)).im * ((c : ℂ) * (z : ℂ) + (d : ℂ)).re -
          ((a : ℂ) * (z : ℂ) + (b : ℂ)).re * ((c : ℂ) * (z : ℂ) + (d : ℂ)).im =
          (z : ℂ).im := by
        simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
          Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero]
        linear_combination (z : ℂ).im * h_det
      rw [← sub_div, h_num]
    rw [h_im_val, h_γz_im_eq]
    field_simp
  -- normSq(cz + d) ≤ Q.
  have h_normSq_le_Q : Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) ≤ Q := by
    rw [h_normSq_eq, hQ_def]
    apply div_le_div₀ hM_K_pos.le hz_im_le hε_L_pos hγz_im_ge
  -- normSq expansion: (cx + d)² + (cy)².
  have h_normSq_expand : Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) =
      ((c : ℝ) * (z : ℂ).re + d)^2 + ((c : ℝ) * (z : ℂ).im)^2 := by
    rw [Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  -- (c · y)² ≤ Q.
  have hcy_sq : ((c : ℝ) * (z : ℂ).im)^2 ≤ Q := by
    have h := h_normSq_le_Q
    rw [h_normSq_expand] at h
    nlinarith [sq_nonneg ((c : ℝ) * (z : ℂ).re + d)]
  -- |c| ≤ √Q / ε_K.
  have hc_bound : |(c : ℝ)| ≤ Real.sqrt Q / ε_K := by
    have h_abs_eq : |(c : ℝ) * (z : ℂ).im| = |(c : ℝ)| * (z : ℂ).im := by
      rw [abs_mul, abs_of_pos hz_im_pos]
    have h_abs_le : |(c : ℝ) * (z : ℂ).im| ≤ Real.sqrt Q := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hcy_sq
    rw [h_abs_eq] at h_abs_le
    have h_mono : |(c : ℝ)| * ε_K ≤ |(c : ℝ)| * (z : ℂ).im :=
      mul_le_mul_of_nonneg_left hz_im_ge (abs_nonneg _)
    rw [le_div_iff₀ hε_K_pos]
    linarith
  -- (cx + d)² ≤ Q ⟹ |cx + d| ≤ √Q.
  have hcxd_sq : ((c : ℝ) * (z : ℂ).re + d)^2 ≤ Q := by
    have h := h_normSq_le_Q
    rw [h_normSq_expand] at h
    nlinarith [sq_nonneg ((c : ℝ) * (z : ℂ).im)]
  have hcxd_abs : |(c : ℝ) * (z : ℂ).re + d| ≤ Real.sqrt Q := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hcxd_sq
  -- |d| ≤ √Q + R_K · √Q / ε_K.
  have hd_bound : |(d : ℝ)| ≤ Real.sqrt Q + R_K * Real.sqrt Q / ε_K := by
    have h_decompose : (d : ℝ) = ((c : ℝ) * (z : ℂ).re + d) - (c : ℝ) * (z : ℂ).re := by ring
    calc |(d : ℝ)| = |((c : ℝ) * (z : ℂ).re + d) - (c : ℝ) * (z : ℂ).re| := by rw [← h_decompose]
      _ ≤ |(c : ℝ) * (z : ℂ).re + d| + |(c : ℝ) * (z : ℂ).re| := abs_sub _ _
      _ ≤ Real.sqrt Q + |(c : ℝ)| * |(z : ℂ).re| := by rw [abs_mul]; linarith
      _ ≤ Real.sqrt Q + (Real.sqrt Q / ε_K) * R_K := by gcongr
      _ = Real.sqrt Q + R_K * Real.sqrt Q / ε_K := by ring
  -- Now (a, b) bounds via |γ•z| · |cz+d|.
  have h_az_b_eq : (a : ℂ) * (z : ℂ) + (b : ℂ) =
      ((γ • z : UpperHalfPlane) : ℂ) * ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by
    rw [h_γz_eq, div_mul_cancel₀ _ h_denom_ne]
  have h_az_b_normSq : Complex.normSq ((a : ℂ) * (z : ℂ) + (b : ℂ)) ≤ R_L^2 * Q := by
    rw [h_az_b_eq, map_mul]
    have h_γz_normSq_le : Complex.normSq ((γ • z : UpperHalfPlane) : ℂ) ≤ R_L^2 := by
      rw [Complex.normSq_eq_norm_sq]
      have h_nn : 0 ≤ ‖((γ • z : UpperHalfPlane) : ℂ)‖ := norm_nonneg _
      nlinarith [hγz_norm_le]
    have h_cd_nn : 0 ≤ Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) :=
      Complex.normSq_nonneg _
    calc Complex.normSq ((γ • z : UpperHalfPlane) : ℂ) *
        Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ))
        ≤ R_L^2 * Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) :=
          mul_le_mul_of_nonneg_right h_γz_normSq_le h_cd_nn
      _ ≤ R_L^2 * Q := mul_le_mul_of_nonneg_left h_normSq_le_Q (sq_nonneg _)
  have h_az_b_expand : Complex.normSq ((a : ℂ) * (z : ℂ) + (b : ℂ)) =
      ((a : ℝ) * (z : ℂ).re + b)^2 + ((a : ℝ) * (z : ℂ).im)^2 := by
    rw [Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  -- (a · y)² ≤ R_L² · Q.
  have hay_sq : ((a : ℝ) * (z : ℂ).im)^2 ≤ R_L^2 * Q := by
    have h := h_az_b_normSq
    rw [h_az_b_expand] at h
    nlinarith [sq_nonneg ((a : ℝ) * (z : ℂ).re + b)]
  -- |a| ≤ R_L · √Q / ε_K.
  have ha_bound : |(a : ℝ)| ≤ R_L * Real.sqrt Q / ε_K := by
    have h_abs_eq : |(a : ℝ) * (z : ℂ).im| = |(a : ℝ)| * (z : ℂ).im := by
      rw [abs_mul, abs_of_pos hz_im_pos]
    have h_abs_le : |(a : ℝ) * (z : ℂ).im| ≤ R_L * Real.sqrt Q := by
      rw [← Real.sqrt_sq_eq_abs]
      have h_sqrt : Real.sqrt (((a : ℝ) * (z : ℂ).im)^2) ≤ Real.sqrt (R_L^2 * Q) :=
        Real.sqrt_le_sqrt hay_sq
      rw [Real.sqrt_mul (sq_nonneg R_L), Real.sqrt_sq hR_L_nn] at h_sqrt
      exact h_sqrt
    rw [h_abs_eq] at h_abs_le
    have h_mono : |(a : ℝ)| * ε_K ≤ |(a : ℝ)| * (z : ℂ).im :=
      mul_le_mul_of_nonneg_left hz_im_ge (abs_nonneg _)
    rw [le_div_iff₀ hε_K_pos]
    linarith
  -- (ax + b)² ≤ R_L² · Q ⟹ |ax + b| ≤ R_L · √Q.
  have haxb_sq : ((a : ℝ) * (z : ℂ).re + b)^2 ≤ R_L^2 * Q := by
    have h := h_az_b_normSq
    rw [h_az_b_expand] at h
    nlinarith [sq_nonneg ((a : ℝ) * (z : ℂ).im)]
  have haxb_abs : |(a : ℝ) * (z : ℂ).re + b| ≤ R_L * Real.sqrt Q := by
    rw [← Real.sqrt_sq_eq_abs]
    have h_sqrt : Real.sqrt (((a : ℝ) * (z : ℂ).re + b)^2) ≤ Real.sqrt (R_L^2 * Q) :=
      Real.sqrt_le_sqrt haxb_sq
    rw [Real.sqrt_mul (sq_nonneg R_L), Real.sqrt_sq hR_L_nn] at h_sqrt
    exact h_sqrt
  -- |b| ≤ R_L · √Q + R_K · R_L · √Q / ε_K.
  have hb_bound : |(b : ℝ)| ≤ R_L * Real.sqrt Q + R_K * R_L * Real.sqrt Q / ε_K := by
    have h_decompose : (b : ℝ) = ((a : ℝ) * (z : ℂ).re + b) - (a : ℝ) * (z : ℂ).re := by ring
    calc |(b : ℝ)| = |((a : ℝ) * (z : ℂ).re + b) - (a : ℝ) * (z : ℂ).re| := by rw [← h_decompose]
      _ ≤ |(a : ℝ) * (z : ℂ).re + b| + |(a : ℝ) * (z : ℂ).re| := abs_sub _ _
      _ ≤ R_L * Real.sqrt Q + |(a : ℝ)| * |(z : ℂ).re| := by rw [abs_mul]; linarith
      _ ≤ R_L * Real.sqrt Q + (R_L * Real.sqrt Q / ε_K) * R_K := by gcongr
      _ = R_L * Real.sqrt Q + R_K * R_L * Real.sqrt Q / ε_K := by ring
  -- Combine: each integer entry ≤ N := ⌈B⌉₊.
  have h_each_le : ∀ (x : ℝ), 0 ≤ x → x ≤ B → x ≤ (⌈B⌉₊ : ℝ) :=
    fun x _ hx => hx.trans (Nat.le_ceil _)
  have h_pos_terms : 0 ≤ Real.sqrt Q / ε_K ∧ 0 ≤ R_K * Real.sqrt Q / ε_K ∧
      0 ≤ R_L * Real.sqrt Q / ε_K ∧ 0 ≤ R_L * Real.sqrt Q ∧
      0 ≤ R_K * R_L * Real.sqrt Q / ε_K := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> positivity
  have ha_le_B : |(a : ℝ)| ≤ B := by
    rw [hB_def]; linarith [ha_bound, h_pos_terms.1, h_pos_terms.2.1, hsQ_nn,
      h_pos_terms.2.2.2.1, h_pos_terms.2.2.2.2]
  have hb_le_B : |(b : ℝ)| ≤ B := by
    rw [hB_def]; linarith [hb_bound, h_pos_terms.1, h_pos_terms.2.1, hsQ_nn,
      h_pos_terms.2.2.1]
  have hc_le_B : |(c : ℝ)| ≤ B := by
    rw [hB_def]; linarith [hc_bound, h_pos_terms.2.1, hsQ_nn,
      h_pos_terms.2.2.1, h_pos_terms.2.2.2.1, h_pos_terms.2.2.2.2]
  have hd_le_B : |(d : ℝ)| ≤ B := by
    rw [hB_def]; linarith [hd_bound, h_pos_terms.1, h_pos_terms.2.2.1,
      h_pos_terms.2.2.2.1, h_pos_terms.2.2.2.2]
  have ha_int : |a| ≤ (⌈B⌉₊ : ℤ) := by
    have h : |(a : ℝ)| ≤ ((⌈B⌉₊ : ℕ) : ℝ) := h_each_le _ (abs_nonneg _) ha_le_B
    have h_cast : (|a| : ℝ) = |(a : ℝ)| := by rfl
    rw [← h_cast] at h
    exact_mod_cast h
  have hb_int : |b| ≤ (⌈B⌉₊ : ℤ) := by
    have h : |(b : ℝ)| ≤ ((⌈B⌉₊ : ℕ) : ℝ) := h_each_le _ (abs_nonneg _) hb_le_B
    have h_cast : (|b| : ℝ) = |(b : ℝ)| := by rfl
    rw [← h_cast] at h
    exact_mod_cast h
  have hc_int : |c| ≤ (⌈B⌉₊ : ℤ) := by
    have h : |(c : ℝ)| ≤ ((⌈B⌉₊ : ℕ) : ℝ) := h_each_le _ (abs_nonneg _) hc_le_B
    have h_cast : (|c| : ℝ) = |(c : ℝ)| := by rfl
    rw [← h_cast] at h
    exact_mod_cast h
  have hd_int : |d| ≤ (⌈B⌉₊ : ℤ) := by
    have h : |(d : ℝ)| ≤ ((⌈B⌉₊ : ℕ) : ℝ) := h_each_le _ (abs_nonneg _) hd_le_B
    have h_cast : (|d| : ℝ) = |(d : ℝ)| := by rfl
    rw [← h_cast] at h
    exact_mod_cast h
  -- Match each entry to a, b, c, d.
  fin_cases i <;> fin_cases j
  · exact ha_int
  · exact hb_int
  · exact hc_int
  · exact hd_int

/-- **Pillar 2: `Γ(2)` acts properly discontinuously on `ℍ`.** Follows
from `gamma_two_smul_entry_bound` (finite bounded-entries box) by
intersecting with `Γ(2)` and observing `↥Γ(2) → SL(2, ℤ)` is injective. -/
theorem gamma_two_properlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul (CongruenceSubgroup.Gamma 2) UpperHalfPlane := by
  refine ⟨fun {K L} hK hL => ?_⟩
  obtain ⟨N, hN⟩ := gamma_two_smul_entry_bound hK hL
  -- The set of γ moving K into L is a subset of bounded-entries matrices.
  apply Set.Finite.subset (s := {γ : ↥(CongruenceSubgroup.Gamma 2) |
    ∀ (i j : Fin 2), |((γ : SL(2, ℤ))).val i j| ≤ (N : ℤ)})
  · -- Bounded-entries set is finite: inject into a box of bounded integer matrices.
    have hT_inj : Function.Injective
        (fun γ : ↥(CongruenceSubgroup.Gamma 2) => ((γ : SL(2, ℤ))).val) := by
      intro γ₁ γ₂ heq
      apply Subtype.ext; apply Subtype.ext; exact heq
    have hbox_finite : ({m : Matrix (Fin 2) (Fin 2) ℤ |
        ∀ i j, m i j ∈ Set.Icc (-(N : ℤ)) N} : Set _).Finite := by
      apply Set.Finite.subset
        (s := Set.univ.pi (fun _ : Fin 2 =>
          Set.univ.pi (fun _ : Fin 2 => Set.Icc (-(N : ℤ)) N)))
      · apply Set.Finite.pi; intro _
        apply Set.Finite.pi; intro _
        exact Set.finite_Icc _ _
      · intro m hm i _ j _; exact hm i j
    refine (hbox_finite.preimage hT_inj.injOn).subset ?_
    intro γ hγ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    intro i j
    rw [Set.mem_Icc]
    have h_abs := hγ i j
    rw [abs_le] at h_abs
    exact h_abs
  -- For every γ in the LHS set, all entries bounded.
  intro γ ⟨w, ⟨z, hz_K, h_eq⟩, hw_L⟩ i j
  have h_smul_in_L : γ • z ∈ L := by
    have : γ • z = w := h_eq
    rw [this]; exact hw_L
  exact hN (↑γ : SL(2, ℤ)) z hz_K h_smul_in_L i j

/-! ## Disk version `modularLambda : 𝔻 → ℂ ∖ {0, 1}` -/

/-- The disk modular function takes values in the triply-punctured plane.
Reduces to `modularLambdaH_ne_zero` and `modularLambdaH_ne_one` via the
Cayley transform: `cayleyToHalfPlane` sends `𝔻` to `ℍ`, so
`(cayleyToHalfPlane z).im > 0`. -/
theorem modularLambda_omits {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    modularLambda z ≠ 0 ∧ modularLambda z ≠ 1 := by
  unfold modularLambda
  have hτ_pos : 0 < (cayleyToHalfPlane z).im := cayleyToHalfPlane_im_pos hz
  exact ⟨modularLambdaH_ne_zero hτ_pos, modularLambdaH_ne_one hτ_pos⟩

/-- `modularLambda` is holomorphic on the unit disk. Composition of
`cayleyToHalfPlane : 𝔻 → ℍ` (Möbius, hence differentiable on `𝔻`) with
`modularLambdaH` (differentiable on `ℍ`). -/
theorem modularLambda_differentiableOn :
    DifferentiableOn ℂ modularLambda (ball (0 : ℂ) 1) := by
  intro z hz
  unfold modularLambda
  have h_one_sub_ne : (1 - z) ≠ 0 := by
    simp only [Metric.mem_ball, dist_zero_right] at hz
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz; simp at hz
  have h_cayley_diff : DifferentiableAt ℂ cayleyToHalfPlane z := by
    unfold cayleyToHalfPlane
    fun_prop (disch := exact h_one_sub_ne)
  have hτ_pos : 0 < (cayleyToHalfPlane z).im := cayleyToHalfPlane_im_pos hz
  have h_modH_diff : DifferentiableAt ℂ modularLambdaH (cayleyToHalfPlane z) := by
    have h3 : theta3 (cayleyToHalfPlane z) ≠ 0 := theta3_ne_zero hτ_pos
    have h3_pow : (theta3 (cayleyToHalfPlane z))^4 ≠ 0 := pow_ne_zero 4 h3
    unfold modularLambdaH
    refine DifferentiableAt.div ?_ ?_ h3_pow
    · exact (theta2_differentiableAt hτ_pos).pow 4
    · exact (theta3_differentiableAt hτ_pos).pow 4
  exact (h_modH_diff.comp z h_cayley_diff).differentiableWithinAt

end NoWanderingDomains
