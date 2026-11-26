module

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Topology.Separation.CompletelyRegular
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability
public import Lib.General.Measure.IdempotentKernel
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.Holomorphic.HighestVectorExtension
import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors
import Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration
import Lib.General.LinearAlgebra.PolarDecomposition

/-!
# The idempotent e_λ, the operator π(e_λ), and rigidity of highest vectors of type Λ

The file studies the function `e_λ = New.HCParam.dsKernel l = deg_λ · conj c_λ` on `U(diag ε)`,
where `l = 2λ`, and the operator `π(f) = New.integratedRep π f = ∫ f(g) π(g) dg`. In the main
results `λ` has gap `500 n³ + A` (`New.HCParam.HasLargeGap`), `π` has growth `‖g‖ ^ A` and an
invariant positive definite sesquilinear form `B` on `X` (`New.IsUnitaryRep`), and the `gl n`-module
`ρ` on a complex space `M` is its derivative along a linear map `ι : M → X` (`New.IsDerivedAction`).

* `New.coeff_eq_dsCoeff_of_isKHighest` (rigidity): a `K`-highest vector `x` of weight
  `Λ = New.HCParam.lowestKType l` with Casimir value at least
  `κ_λ = New.HCParam.casimirValue l = |λ|² − |ρ|²` (ρ here the half-sum of positive roots) has the
  matrix coefficient `B x (π g x) = B x x c_λ(g)`.
* `New.integratedRep_fix_of_isKHighest`: if `‖g‖ ^ A f` is integrable and `f * e_λ = e_λ`, then
  `π(f)` fixes such a vector.
* `New.exists_integration_by_parts`, `New.integratedRep_dsKernel_casimir`: integration by parts, and
  `π(e_λ) Ω = κ_λ π(e_λ)`.
* `New.re_integratedRep_dsKernel_pos`, `New.integratedRep_eq_zero_of_notMem_rootCone`: a condition
  under which `π(e_λ)` does not kill a vector, and one under which it does.
* `New.HCParam.HasLargeGap.isIdempotentKernel_dsKernel`,
  `New.HCParam.HasLargeGap.exists_bump_conv_dsKernel`: `e_λ` is a minimal idempotent, reproduced by
  a bump function.

`ρ.casimirK 1` is the Casimir operator `Ω = ∑ E_ab E_ba` of all of `gl n` (all signs equal).

Notions from other files:
* `New.HCParam.IsKHighest`: `x` is a `K`-highest vector of weight `ν`: each `E a a` acts on it by
  `ν a`, and it is killed by the compact raising operators, the `E a b` with `ε a = ε b` and
  `l b < l a`.
* `New.HCParam.lowestKType`: the integer vector Λ = λ+ρ−2ρ_c for a parameter l = 2λ, the highest
  weight of the lowest K-type.
* `New.HCParam.dsCoeff`, `New.HCParam.DsModule`: The function c_λ, and the module U(𝔤)c_λ it
  generates under right derivatives (action `New.HCParam.dsAction`, generator
  `New.HCParam.dsGenerator`).
* `New.weightMinors`, `New.HCParam.kTypeNormSq`: The coefficient m_ν of a highest vector of weight ν
  (a product of principal minors), and ∫_K |m_ν|².
* `New.HCParam.rootCone`: The cone of the positive roots for the order given by l.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration`,
`Lib.DiscreteSeries.Theta.LocalCorrespondence` and `Lib.DiscreteSeries.FlenstedJensen.PsiKTypes` for
sources.
-/

@[expose] public section

namespace New

open Matrix MeasureTheory ComplexConjugate Complex DiscreteSeries Norms.L2Operator ComplexOrder
  GlModule Submodule WithLp HCParam

private lemma grp_inv_inv {G : Type*} [Group G] (a : G) : a⁻¹⁻¹ = a := inv_inv a

private lemma grp_mul_inv_rev {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  _root_.mul_inv_rev a b

private lemma grp_m2 {G : Type*} [Group G] (u k : G) : (u * k)⁻¹ * u = k⁻¹ := by
  rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

private lemma grp_polar_lhs {G : Type*} [Group G] (k₁ κ u : G) :
    (k₁⁻¹ * κ * u)⁻¹ = u⁻¹ * κ⁻¹ * k₁ := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc]

private lemma prodL2_perp_zero {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}
    {l : HCParam (n := n) ε} {g : ℕ} [l.HasGap g] {ν : n → ℤ}
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {P : GlModule n (WithLp 2 (H₁ × H₂))} (P_unitary : IsUnitaryCasimirGe l P)
    {x₁ : H₁} {y₂ : H₂} {c : ℂ} (hc : inner ℂ x₁ x₁ = c) (hy₂ : ‖y₂‖ = 1)
    (highest : ∀ t : ℂ, l.IsKHighest P ν (toLp 2 (x₁, t • y₂))) :
    toLp 2 (x₁, (-c) • y₂) ∈ (P.filtration ε (toLp 2 (x₁, (1 : ℂ) • y₂)) 0)ᗮ :=
  (highest 1).filtration_le_of_word_mem (innerSLFlip ℂ _).ker
    (fun a b h_sign h_lt w _ ↦ by
      change inner ℂ (P.E a b w) (toLp 2 (x₁, (-c) • y₂)) = 0
      rw [P_unitary.inner_E_left, (highest (-c)).2 b a h_sign.symm h_lt,
        inner_zero_right, mul_zero])
    (fun w hw ↦ by
      obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hw)
      rw [word]
      change inner ℂ (toLp 2 (x₁, (1 : ℂ) • y₂)) (toLp 2 (x₁, (-c) • y₂)) = 0
      rw [WithLp.prod_inner_apply]
      change inner ℂ x₁ x₁ + inner ℂ ((1 : ℂ) • y₂) ((-c) • y₂) = 0
      rw [hc, one_smul, inner_smul_right, inner_self_eq_norm_sq_to_K y₂, hy₂,
        RCLike.ofReal_one, one_pow, mul_one, add_neg_cancel])

private lemma prodL2_at_one_inner {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {x₁ : H₁} {y₂ : H₂} {w : WithLp 2 (H₁ × H₂)} {c c₁ c₂ : ℂ}
    (hc : conj c = c) (h₁ : inner ℂ x₁ w.fst = c₁) (h₂ : inner ℂ y₂ w.snd = c₂) :
    inner ℂ (toLp 2 (x₁, (-c) • y₂)) w = c₁ - c * c₂ := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ x₁ w.fst + inner ℂ ((-c) • y₂) w.snd = c₁ - c * c₂
  rw [h₁, inner_smul_left, h₂, map_neg, hc, neg_mul, sub_eq_add_neg]

private lemma prodL2_norm_sub_le {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {a b c : ℂ} {C : ℝ} {w : WithLp 2 (H₁ × H₂)}
    (hC : 0 ≤ C) (ha : ‖a‖ ≤ C * ‖w.fst‖) (hb : ‖b‖ ≤ ‖w.snd‖) :
    ‖a - c * b‖ ≤ (C + ‖c‖) * ‖w‖ := by
  rw [add_mul]
  refine (norm_sub_le a (c * b)).trans (add_le_add
    (ha.trans (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le ..) hC)) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb.trans (WithLp.norm_snd_le ..)) (norm_nonneg c)

-- `n` indexes the signs `ε`, `π` is a representation of `U(diag ε)` on `X`, and `f` is a function
-- on `U(diag ε)`
variable {n : Type} [Fintype n] [DecidableEq n]
  {ε : n → ℤˣ} {A : ℕ} {X : Type*} {l : HCParam (n := n) ε} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (π : USign ε →* X →L[ℂ] X) (f : USign ε → ℂ)

@[fun_prop]
theorem continuous_dsKernel : Continuous l.dsKernel :=
  continuous_const.mul (Complex.conjCLE.continuous.comp (continuous_dsCoeff l continuous_id))

/-- For `l = 2λ` a parameter of some gap `h` (`New.HCParam.HasGap`),
`conj ((-l).dsKernel x) = l.dsKernel x` for every `x` in `U(diag ε)`. That is, `conj(e_{−λ}) = e_λ`
for the kernel `e_λ = deg_λ · conj(c_λ)` given by `dsKernel`. -/
lemma conj_dsKernel_neg {h : ℕ} (hg : l.HasGap h) (x : USign ε) :
    conj ((-l).dsKernel x) = l.dsKernel x := by
  have h_deg : (-l).formalDegree = l.formalDegree := by
    simp only [formalDegree, dsCoeff_neg hg, RCLike.norm_conj]
  rw [dsKernel, dsKernel, map_mul, Complex.conj_ofReal, h_deg, dsCoeff_neg hg, Complex.conj_conj]

/-! ### The operator `π(f)` -/

/-- For a representation π of U(diag ε) by bounded operators and a function f, the operator π(f)
with π(f)x = ∫ f(g)π(g)x dg, when such a bounded operator exists. -/
noncomputable def integratedRep : X →L[ℂ] X := strongIntegral volume fun g ↦ f g • π g

variable {π f} [Nonempty n]
  {M Y W : Type*} [AddCommGroup M] [Module ℂ M]
  {B : X →L⋆[ℂ] X →L[ℂ] ℂ} {ι : M →ₗ[ℂ] X} {v : M} {c : ℝ} {ρ : GlModule n M}
  (hu : IsUnitaryRep A π B) [MeasurableSpace W]
  {ν : Measure W} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  (hf : Integrable fun g : USign ε ↦ f g * ‖g.val.val‖ ^ A)

attribute [local fun_prop] IsUnitaryRep.continuous

/-- If `f` is integrable for a nonzero measure and its real part is positive everywhere, then the
real part of its integral is positive. -/
theorem re_integral_pos [NeZero ν] {f : W → ℂ} (hf_int : Integrable f ν)
    (hf_pos : ∀ w : W, 0 < re (f w)) :
    0 < (integral ν f).re := by
  refine .trans_eq ?_ (integral_re hf_int)
  refine (integral_pos_iff_support_of_nonneg (fun w ↦ (hf_pos w).le) hf_int.re).2 ?_
  rw [Function.support_eq_univ fun w : W ↦ (hf_pos w).ne', pos_iff_ne_zero, ne_eq,
    Measure.measure_univ_eq_zero]
  exact NeZero.ne ν

omit [Nonempty n] in
/-- Let l be a parameter of any gap, π a representation as in `New.IsUnitaryRep` with derivative ρ
along ι, and v in M a K-highest vector of weight ν, with ν K-dominant for the order −l (ν b ≤ ν a
whenever ε a = ε b and l b < l a). Then for every continuous linear functional φ on X, ∫_K
conj(m_ν(k)) φ(π(k)ιv) dk = (∫_K |m_ν|²) φ(ιv), with m_ν = `weightMinors ν` and ∫_K
|m_ν|² = `ν.kTypeNormSq`. -/
theorem HCParam.IsKHighest.integral_conj_weightMinors_mul (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) {h : ℕ} {ν : HCParam ε}
    (hv_highest : l.IsKHighest ρ ν v) [h_gap : l.HasGap h] (hν : IsKDominant ε (-l) ν)
    (φ : X →L[ℂ] ℂ) :
    ∫ k : maxCompactU ε, conj (weightMinors ν k) * φ (π k (ι v)) ∂haarK ε =
      ν.kTypeNormSq * φ (ι v) := by
  -- The coefficient `k ↦ φ (π k (ι v))` is holomorphic of weight `ν` on `K`, so its integral
  -- against `conj (weightMinors ν k)` is `ν.kTypeNormSq` times its value at `1`. The lemmas are
  -- stated for a family of places; here the family is `Unit`.
  have h_cont (y : M) : Continuous fun g : USign ε ↦ φ (π g (ι y)) :=
    φ.continuous.comp (hu.continuous (ι y))
  have h_hol : IsHolOfWeight ε (-l) (fun _ : Unit ↦ ν)
      (fun k : Unit → USign ε ↦ φ (π (k ()) (ι v))) ε := by
    simpa only [ContinuousMultilinearMap.mkPiAlgebra_apply, Fintype.prod_unique,
      LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply] using
      isHolOfWeight_coeffMap h_gap.neg.1
        (fun _ : Unit ↦ by rwa [neg_neg])
        (fun _ ↦ hd.isCoeffMap φ) (.mkPiAlgebra ℂ Unit ℂ) fun _ ↦ h_cont
  have h_int := h_hol.integral_mul_conj_weightMinors h_gap.neg.1 hν
    ((h_cont v).comp (continuous_apply ()))
  simp only [Pi.one_apply, map_one, one_apply_eq_self, mul_comm (φ _)] at h_int
  exact h_int

/-- If `π` is a representation as in `New.IsUnitaryRep` of growth exponent `A` and
`g ↦ f g * ‖g‖ ^ A` is integrable on `U(diag ε)`, then so is each `g ↦ f g • π g x`. -/
theorem integrable_smul_rep (hu : IsUnitaryRep A π B)
    (hf : Integrable fun g : USign ε ↦ f g * ‖g.val.val‖ ^ A) (x : X) :
    Integrable fun g : USign ε ↦ f g • π g x := by
  -- the integrable function `f g * ‖g‖ ^ A` times the bounded function `‖g‖ ^ (-A) • π g x`
  obtain ⟨c, hc⟩ := hu.growth
  have h_ne (g : USign ε) : ‖g.val.val‖ ^ A ≠ 0 :=
    pow_ne_zero A (norm_pos_iff.2 g.val.isUnit.ne_zero).ne'
  have bound (g : USign ε) : ‖(‖g.val.val‖ ^ A : ℂ)⁻¹ • π g x‖ ≤ c * ‖x‖ := by
    rw [norm_smul, norm_inv, Complex.norm_pow, Complex.norm_real, norm_norm]
    calc (‖g.val.val‖ ^ A)⁻¹ * ‖π g x‖
        ≤ (‖g.val.val‖ ^ A)⁻¹ * (‖π g‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((π g).le_opNorm x)
            (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _))
      _ ≤ (‖g.val.val‖ ^ A)⁻¹ * (c * ‖g.val.val‖ ^ A * ‖x‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc g) (norm_nonneg x))
            (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _))
      _ = c * ‖x‖ := by rw [mul_comm c, mul_assoc, inv_mul_cancel_left₀ (h_ne g)]
  have h_cont : Continuous fun g : USign ε ↦ ((‖g.val.val‖ : ℂ) ^ A)⁻¹ • π g x :=
    (((Complex.continuous_ofReal.comp
      (Units.continuous_val.comp continuous_subtypeVal).norm).pow A).inv₀
      fun g ↦ pow_ne_zero A (Complex.ofReal_ne_zero.2
        (norm_pos_iff.2 g.val.isUnit.ne_zero).ne')).smul (hu.continuous x)
  have h_int := hf.smul_bdd _ h_cont.aestronglyMeasurable (.of_forall bound)
  refine h_int.congr (.of_forall fun g ↦ ?_)
  change (f g * (‖g.val.val‖ : ℂ) ^ A) • ((‖g.val.val‖ : ℂ) ^ A)⁻¹ • π g x = f g • π g x
  rw [smul_smul, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero A (Complex.ofReal_ne_zero.2
      (norm_pos_iff.2 g.val.isUnit.ne_zero).ne')), mul_one]

variable [CompleteSpace X]

include hu hf in
/-- If `g ↦ f g * ‖g‖ ^ A` is integrable and `π` is as in `New.IsUnitaryRep` with exponent `A`, then
a continuous linear map `T` takes `π(f) x` to the integral of `g ↦ f g • T (π g x)`. -/
theorem map_integratedRep (T : X →L[ℂ] Y) (x : X) :
    T (integratedRep π f x) = ∫ g : USign ε, f g • T (π g x) := by
  rw [integratedRep, strongIntegral_apply volume (fun g ↦ f g • π g) (integrable_smul_rep hu hf)]
  exact (T.integral_comp_comm (integrable_smul_rep hu hf x)).symm.trans
    (integral_congr_ae (.of_forall fun g ↦ T.map_smul (f g) (π g x)))

/-! ### The kernel `e_λ`, its bump function, and the operator `π(e_λ)` -/

/-- For n ≥ 1 (`Nonempty n`) and a doubled parameter l = 2λ for the signs ε with gap 500n³+A
(`HasLargeGap`), the function `l.dsKernel` on U(diag ε), e_λ(g) = deg_λ·conj(c_λ(g)), is an
idempotent kernel in the sense of `New.IsIdempotentKernel`. That is, it is continuous and
integrable, e(g⁻¹) = conj e(g), e(1) ≠ 0, and ∫ e(z) e(x⁻¹z⁻¹y) dz = e(x⁻¹) e(y)/e(1). -/
theorem HCParam.HasLargeGap.isIdempotentKernel_dsKernel (hg : l.HasLargeGap A) :
    IsIdempotentKernel l.dsKernel where
  continuous := continuous_dsKernel
  integrable := by
    simpa only [pow_zero, mul_one] using hg.integrable_dsKernel_mul_norm_pow 0 (Nat.zero_le _)
  apply_inv g := by
    rw [dsKernel, dsKernel, map_mul, Complex.conj_ofReal, dsCoeff_inv hg, Complex.conj_conj]
  apply_one_ne_zero := by
    rw [dsKernel, Subgroup.coe_one, Units.val_one, dsCoeff_one, map_one, mul_one]
    exact Complex.ofReal_ne_zero.2 (formalDegree_pos hg).ne'
  convolution_eq x y := by
    -- the integrand is that of Schur orthogonality for `dsCoeff`, times `l.formalDegree ^ 2`
    have h_schur : l.formalDegree * ∫ z : USign ε, l.dsCoeff ↑(y⁻¹ * z * x) * conj (l.dsCoeff z) =
        l.dsCoeff ↑y⁻¹ * l.dsCoeff x :=
      dsCoeff_schur_orthogonality hg y⁻¹ x
    have h_integrand (z : USign ε) : l.dsKernel z * l.dsKernel ((z * x)⁻¹ * y) = l.formalDegree *
        (l.formalDegree * (l.dsCoeff ↑(y⁻¹ * z * x) * conj (l.dsCoeff z))) := by
      rw [dsKernel, dsKernel, ← dsCoeff_inv hg ((z * x)⁻¹ * y), grp_mul_inv_rev, grp_inv_inv,
        ← mul_assoc y⁻¹ z x]
      ring
    have h_value : l.dsKernel x⁻¹ / l.dsKernel 1 * l.dsKernel y =
        l.formalDegree * (l.dsCoeff ↑y⁻¹ * l.dsCoeff x) := by
      rw [dsKernel, dsKernel, dsKernel, Subgroup.coe_one, Units.val_one, dsCoeff_one, map_one,
        mul_one, dsCoeff_inv hg, Complex.conj_conj, ← dsCoeff_inv hg y,
        mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 (formalDegree_pos hg).ne')]
      ring
    simp only [h_integrand, integral_const_mul, h_schur, h_value]

/-- For `n ≥ 1` and `λ = l / 2` with gap `500 n³ + A`, let `e_λ = l.dsKernel`. Then there is a
smooth compactly supported `α` on `U(diag ε)` with `∫ α(x⁻¹) e_λ(x⁻¹ g) dx = e_λ(g)` for all `g`. So
`β * e_λ = e_λ` for the function `β(x) = α(x⁻¹)`; the inverse comes from the convention of
`New.DiscreteSeries.smear`. -/
theorem HCParam.HasLargeGap.exists_bump_conv_dsKernel (hg : l.HasLargeGap A) :
    ∃ α : Bumps ε, ∀ g : USign ε,
      ∫ x : USign ε, α.val.val x⁻¹ * l.dsKernel (x⁻¹ * g) = l.dsKernel g := by
  -- `smear l.dsCoeffSmooth.1 α` is `g ↦ ∫ y, α y⁻¹ • l.dsCoeff (g * y)`
  obtain ⟨α, hα⟩ : ∃ α : Bumps ε,
      (smear l.dsCoeffSmooth.val (SmoothU.continuous l.dsCoeffSmooth)) α = l.dsGenerator.val :=
    exists_smear_dsCoeffSmooth_eq hg l.dsGenerator
  refine ⟨α, fun g ↦ ?_⟩
  -- evaluate at `g⁻¹`; `dsCoeff` at an inverse is the conjugate (`dsCoeff_inv`)
  have h_sm (x : USign ε) : l.dsCoeffSmooth.val x = l.dsCoeff x := rfl
  have h_gen (x : USign ε) : l.dsGenerator.val.val x = l.dsCoeff x := rfl
  have h_eval : ∫ y : USign ε, α.val.val y⁻¹ * l.dsCoeff ↑(g⁻¹ * y) = l.dsCoeff ↑g⁻¹ := by
    simpa only [smear, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, h_sm, h_gen] using
      congrFun hα g⁻¹
  rw [dsKernel, ← dsCoeff_inv hg g, ← h_eval, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  dsimp only
  rw [dsKernel, ← dsCoeff_inv hg (y⁻¹ * g), grp_mul_inv_rev, grp_inv_inv]
  ring

/-- Integration by parts. Let `λ = l / 2` have gap `500 n³ + A`, and let `π` be as in
`New.IsUnitaryRep` with derivative `ρ` along `ι`. Let `(-l).DsModule` be the space U(𝔤)c_{−λ}
generated by c_{−λ} under right derivatives, with gl_n-action `dsAction`. Then there is a linear map
`P` from this space to bounded operators on `X` such that (a) `P(c_{−λ})` is `π(e_λ)`, the
integrated operator `x ↦ ∫ e_λ(g) π(g) x dg` of `e_λ = l.dsKernel` = deg_λ · conj(c_λ); (b)
`P f (ι (ρ Y v)) = −P (Y·f) (ι v)` for all `Y` in gl_n(ℂ), `f` and `v`. -/
theorem exists_integration_by_parts (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) :
    ∃ P : (-l).DsModule →ₗ[ℂ] X →L[ℂ] X,
      -- (a) the operator of the kernel is the value of `P` at the generator
      integratedRep π l.dsKernel = P (-l).dsGenerator ∧
      -- (b) integration by parts
      ∀ (Y : Matrix n n ℂ) (f : (-l).DsModule) (v : M),
        P f (ι (ρ Y v)) = -P ((-l).dsAction Y f) (ι v) := by
  -- Take `l.formalDegree` times `P f = integratedRep π f`. For `Y` in the real Lie algebra put
  -- `F g = f g • π g (ι v)` and let `F'` be its derivative along `Y`. Then `∫ F' = 0`, because
  -- `∫ t in 0..1, F' (g * expU (t • Y)) = F (g * expU Y) - F g` and the measure is right invariant.
  have h_int (f : (-l).DsModule) (x : X) : Integrable fun g : USign ε ↦ f.val.val g • π g x :=
    integrable_smul_rep hu (HasLargeGap.integrable_mul_norm_pow hg.neg f A A.le_succ) x
  have h_apply (f : (-l).DsModule) (x : X) :
      integratedRep π f.val.val x = ∫ g : USign ε, f.val.val g • π g x :=
    strongIntegral_apply volume (fun g ↦ f.val.val g • π g) (h_int f) x
  -- `P f = π(f)`, linear in `f` since all these integrands are integrable
  let P : (-l).DsModule →ₗ[ℂ] X →L[ℂ] X :=
    { toFun f := integratedRep π f.val.val
      map_add' f₁ f₂ := by
        ext x
        rw [_root_.add_apply, h_apply, h_apply, h_apply, ← integral_add (h_int f₁ x) (h_int f₂ x)]
        exact integral_congr_ae (.of_forall fun g ↦ add_smul (f₁.val.val g) (f₂.val.val g) (π g x))
      map_smul' c f := by
        ext x
        rw [RingHom.id_apply, _root_.smul_apply, h_apply, h_apply, ← integral_smul]
        exact integral_congr_ae (.of_forall fun g ↦ mul_smul c (f.val.val g) (π g x)) }
  have h_real (Y : unitaryLie (signMatrix ε)) (f : (-l).DsModule) (v : M) :
      ∫ g : USign ε, f.val.val g • π g (ι (ρ Y v)) =
        -∫ g : USign ε, ((-l).dsAction Y f).val.val g • π g (ι v) := by
    let F (g : USign ε) : X := f.val.val g • π g (ι v)
    let F' (g : USign ε) : X :=
      f.val.val g • π g (ι (ρ Y v)) + ((-l).dsAction Y f).val.val g • π g (ι v)
    have hF : Integrable F := h_int f (ι v)
    have hF' : Integrable F' := (h_int f _).add (h_int _ _)
    have h_deriv (g : USign ε) (t : ℝ) :
        HasDerivAt (fun s : ℝ ↦ F (g * expU (s • Y))) (F' (g * expU (t • Y))) t :=
      (hasDerivAt_rightDeriv_expU f.val g Y t).smul (hd.isCoeffMap 1 g Y v t)
    have h_cont (g : USign ε) : Continuous fun t : ℝ ↦ F' (g * expU (t • Y)) := by
      have h_exp : Continuous fun t : ℝ ↦ g * expU (t • Y) :=
        continuous_const.mul (continuous_expU.comp (continuous_id.smul continuous_const))
      exact (((SmoothU.continuous f.val).comp h_exp).smul ((hu.continuous _).comp h_exp)).add
        (((SmoothU.continuous ((-l).dsAction Y f).val).comp h_exp).smul
          ((hu.continuous _).comp h_exp))
    have h_ftc (g : USign ε) :
        ∫ t in Set.Ioc (0 : ℝ) 1, F' (g * expU (t • Y)) = F (g * expU Y) - F g := by
      have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ h_deriv g t) ((h_cont g).intervalIntegrable 0 1)
      rw [intervalIntegral.integral_of_le zero_le_one, one_smul, zero_smul, expU_zero,
        mul_one] at h1
      exact h1
    have h_meas : Measurable (fun p : ℝ × USign ε ↦ p.2 * expU (p.1 • Y)) :=
      (continuous_snd.mul (continuous_expU.comp (continuous_fst.smul continuous_const))).measurable
    rw [← add_eq_zero_iff_eq_neg, ← integral_add (h_int f _) (h_int _ _)]
    calc ∫ g : USign ε, F' g = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ g : USign ε, F' g := by
          simp [Set.univ_inter]
      _ = ∫ g : USign ε, ∫ t in Set.Ioc (0 : ℝ) 1, F' (g * expU (t • Y)) :=
        (integral_skew_product (T := fun t g ↦ g * expU (t • Y))
          (fun t ↦ map_mul_right_eq_self volume (expU (t • Y))) (hF'.comp_snd _) h_meas).2.symm
      _ = ∫ g : USign ε, (F (g * expU Y) - F g) := by simp only [h_ftc]
      _ = 0 := by rw [integral_sub (hF.comp_mul_right _) hF, integral_mul_right_eq_self F, sub_self]
  refine ⟨l.formalDegree • P, ?_, fun Y f v ↦ ?_⟩
  · -- the generator `(-l).dsGenerator` is the conjugate of `l.dsCoeff`
    have h_kernel :
        l.dsKernel = ((l.formalDegree : ℂ) • (-l).dsGenerator : (-l).DsModule).val.val :=
      funext fun g ↦ by rw [dsKernel, ← dsCoeff_neg hg]; rfl
    rw [h_kernel]
    exact P.map_smul l.formalDegree (-l).dsGenerator
  · -- a complex matrix is `Y₁ + I • Y₂` with `Y₁`, `Y₂` in the real Lie algebra
    have h_P_real (Z : unitaryLie (signMatrix ε)) :
        P f (ι (ρ Z v)) = -P ((-l).dsAction Z f) (ι v) := by
      change integratedRep π f.val.val (ι (ρ Z v)) =
        -integratedRep π ((-l).dsAction Z f).val.val (ι v)
      rw [h_apply, h_apply]
      exact h_real Z f v
    have h_P : P f (ι (ρ Y v)) = -P ((-l).dsAction Y f) (ι v) := by
      let Y₁ := unitaryLiePart ε Y
      let Y₂ := unitaryLiePart ε (-I • Y)
      have hY : Y = (Y₁ : Matrix n n ℂ) + I • (Y₂ : Matrix n n ℂ) :=
        eq_unitaryLiePart_add_I_smul ε Y
      rw [hY, ρ.ρ.map_add, ρ.ρ.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        ι.map_add, ι.map_smul, (P f).map_add, (P f).map_smul, h_P_real Y₁, h_P_real Y₂,
        ((-l).dsAction.ρ).map_add, ((-l).dsAction.ρ).map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, P.map_add, P.map_smul, _root_.add_apply, _root_.smul_apply,
        smul_neg, ← neg_add]
    change l.formalDegree • P f (ι (ρ Y v)) = -(l.formalDegree • P ((-l).dsAction Y f) (ι v))
    rw [h_P, smul_neg]

/-- Let `l = 2λ` have gap `500 n³ + A`, let `e_λ = l.dsKernel`, and let `π` be a representation of
`U(diag ε)` on `X` with `IsUnitaryRep A π B` (strongly continuous, `‖π g‖ ≤ C‖g‖^A`, `B` hermitian,
positive definite and invariant) whose derivative along `ι` is the `gl n`-module `ρ`. Then
`π(e_λ) ι(Ω v) = κ_λ π(e_λ) ι(v)` for every `v`. Here `π(e_λ) = integratedRep π l.dsKernel`,
`Ω = ρ.casimirK 1` is the Casimir operator of `gl n`, and `κ_λ = New.HCParam.casimirValue l`. -/
theorem integratedRep_dsKernel_casimir (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) :
    integratedRep π l.dsKernel (ι (ρ.casimirK 1 v)) =
      ofReal l.casimirValue • integratedRep π l.dsKernel (ι v) := by
  obtain ⟨P, hP_eq, hP_ibp⟩ := exists_integration_by_parts hg hu hd
  -- the lemma on the Casimir value of `c_{-λ}` takes the gap of `-l` as an instance
  have gap_neg : (-l).HasLargeGap A := hg.neg
  have h_generator : (-l).dsAction.casimirK 1 (-l).dsGenerator =
      ofReal (-l).casimirValue • (-l).dsGenerator :=
    casimirK_generatedModule casimir_dsCoeffSmooth _
  -- integrate by parts twice (the signs cancel and `E a b`, `E b a` change places), then use the
  -- Casimir value at the generator
  calc
    integratedRep π l.dsKernel (ι (ρ.casimirK 1 v))
      = P ((-l).dsAction.casimirK 1 (-l).dsGenerator) (ι v) := by
        have h_filt (a : n) :
            (Finset.univ.filter fun b : n ↦ (1 : n → ℤˣ) a = (1 : n → ℤˣ) b) = Finset.univ :=
          Finset.filter_true_of_mem fun _ _ ↦ rfl
        rw [hP_eq, casimirK, casimirK, casimir, casimir]
        simp only [LinearMap.sum_apply, mul_apply_eq_comp, GlModule.E, map_sum,
          _root_.sum_apply, h_filt, hP_ibp, neg_neg]
        exact Finset.sum_comm
    _ = ofReal l.casimirValue • integratedRep π l.dsKernel (ι v) := by
        have h_val : (-l).casimirValue = l.casimirValue := by
          simp only [casimirValue, Pi.neg_apply, Int.cast_neg, neg_sq, twoRho_neg]
        rw [h_generator, map_smul, _root_.smul_apply, ← hP_eq, h_val]

omit [CompleteSpace X] [Nonempty n] in
/-- For `π` as in `New.IsUnitaryRep` with derivative `ρ` along `ι`, the weight `ν` of a `K`-highest
vector `v` with `ι v ≠ 0` is `K`-dominant for the order `-l`: if `ε a = ε b` and `l b < l a`, then
`ν b ≤ ν a`. -/
theorem HCParam.IsKHighest.isKDominant_of_isUnitaryRep (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) {ν : n → ℤ} (hv : l.IsKHighest ρ ν v) (hv_ne : ι v ≠ 0) :
    IsKDominant ε (-l) ν := by
  intro a b h_sign h_lt
  -- the square norm of `ι (E b a v)` is `ν a - ν b` times that of `ι v`
  obtain ⟨H, _, _, j, h_inner, -⟩ := hu.exists_innerProductSpace
  have norm_nonneg : 0 ≤ RCLike.re (B (ι (ρ.E b a v)) (ι (ρ.E b a v))) := by
    simpa only [← h_inner] using inner_self_nonneg
  rw [hd.form_E_eq_sign_mul hu] at norm_nonneg
  have h_comm : ρ.E a b (ρ.E b a v) = ((ν a : ℂ) - ν b) • v := by
    rw [GlModule.E, GlModule.E, ρ.apply_apply_eq_swap_add_bracket, ← GlModule.E, ← GlModule.E,
      hv.2 a b h_sign (neg_lt_neg_iff.1 h_lt), map_zero, zero_add]
    have h_br : single a b (1 : ℂ) * single b a 1 - single b a 1 * single a b 1 =
        single a a 1 - single b b 1 := by
      rw [single_mul_single_same, single_mul_single_same, mul_one]
    rw [h_br, map_sub, LinearMap.sub_apply, ← GlModule.E, ← GlModule.E, hv.1 a, hv.1 b, sub_smul]
  have h_sign_sq : (ε b * ε b).val = (1 : ℤ) := by
    rcases Int.units_eq_one_or (ε b) with h | h <;> rw [h] <;> rfl
  rw [h_sign, h_sign_sq, Int.cast_one, one_mul, h_comm, map_smul, map_smul,
    smul_eq_mul, RCLike.re_eq_complex_re, Complex.mul_re, Complex.sub_re, Complex.intCast_re,
    Complex.intCast_re, Complex.sub_im, Complex.intCast_im, Complex.intCast_im, sub_self,
    zero_mul, sub_zero] at norm_nonneg
  have h_sub : (0 : ℝ) ≤ (ν a : ℝ) - (ν b : ℝ) :=
    nonneg_of_mul_nonneg_left norm_nonneg (hu.pos (ι v) hv_ne)
  exact Int.cast_le.1 (sub_nonneg.1 h_sub)

/-- Let `λ = l / 2` have gap `500 n³ + A`, let `π` be as in `New.IsUnitaryRep` with derivative `ρ`
along `ι`, and let `v` be `K`-highest of weight `ν`. Suppose `ν - New.HCParam.lowestKType l` lies
outside `New.HCParam.rootCone l`, the cone of integer vectors `β` with `o ⬝ᵥ β ≤ 0` for every
integer `o` strictly reversing the order of `l`; this cone contains all sums of the roots
`e_a − e_b` with `l b < l a`. Then `π(e_λ)` kills every translate `π y (ι v)`, where
`e_λ = New.HCParam.dsKernel l` is `g ↦ deg_λ · conj(c_λ(g))` and `π(e_λ) x = ∫ e_λ(g) π(g) x dg`. -/
theorem integratedRep_eq_zero_of_notMem_rootCone (hg : l.HasLargeGap A)
    (hu : IsUnitaryRep A π B) (hd : IsDerivedAction π ι ρ) {ν : n → ℤ}
    (hv : l.IsKHighest ρ ν v) (hν_cone : ν - l.lowestKType ∉ l.rootCone) (y : USign ε) :
    integratedRep π l.dsKernel (π y (ι v)) = 0 := by
  -- Averaging over `K` against `conj (weightMinors ν k)` multiplies `ι v` by `kTypeNormSq ν > 0`,
  -- but kills `dsCoeff` when `ν - l.lowestKType` is outside the cone. So the integral of `dsCoeff`
  -- against any coefficient of `π y (ι v)` vanishes, and the form of
  -- `integratedRep π l.dsKernel (π y (ι v))` with itself is one of these.
  by_contra h_ne
  -- `B` is an inner product for which `π` acts by isometries; so its coefficients are bounded.
  obtain ⟨H, _, _, j, h_inner, h_norm⟩ := hu.exists_innerProductSpace
  have hν : IsKDominant ε (-l) ν :=
    hv.isKDominant_of_isUnitaryRep hu hd fun h_zero ↦ h_ne (by rw [h_zero, map_zero, map_zero])
  let T : ℂ := (toHCParam ε ν).kTypeNormSq
  have h_vec (w : X) :
      ∫ k : maxCompactU ε, conj (weightMinors ν k) * B (π k.val⁻¹ w) (ι v) ∂haarK ε =
        T * B w (ι v) := by
    simpa only [T, hu.form_apply_eq_form_inv_apply] using
      hv.integral_conj_weightMinors_mul hu hd hν (B w)
  have h_psi (g : USign ε) :
      ∫ k : maxCompactU ε, conj (weightMinors ν k) * l.dsCoeff ↑(y * k * g) ∂haarK ε = 0 :=
    integral_conj_weightMinors_mul_dsCoeff_eq_zero hg y g hν hν_cone
  have h_zero (w : X) : ∫ g : USign ε, l.dsCoeff g * B (π y⁻¹ (π g w)) (ι v) = 0 := by
    -- Move the average over `K` from the coefficient to `dsCoeff`: `integral_conv` evaluates one
    -- double integral with the average on the coefficient (`on_vec`) or on `dsCoeff` (`on_psi`).
    have h_bdd : IsBoundedMeasurable fun g : USign ε ↦ B w (π g⁻¹ (ι v)) :=
      .of_continuous ⟨‖j w‖ * ‖j (ι v)‖, fun g ↦ by
        rw [← h_inner]
        exact (norm_inner_le_norm (j w) (j (π g⁻¹ (ι v)))).trans_eq
          (congrArg (‖j w‖ * ·) (h_norm g⁻¹ (ι v)))⟩
        ((B w).continuous.comp ((hu.continuous (ι v)).comp continuous_inv))
    have h_wm_cont : Continuous fun k : maxCompactU ε ↦ conj (weightMinors ν k) :=
      Complex.conjCLE.continuous.comp (DiscreteSeries.continuous_weightMinors
        (Units.continuous_val.comp (continuous_subtypeVal.comp continuous_subtypeVal))
        fun k ↦ GeneralLinearGroup.det_ne_zero k.val.val)
    obtain ⟨on_vec, on_psi⟩ :=
      integral_conv (fun k : maxCompactU ε ↦ (y * k.val)⁻¹) (ν := haarK ε)
        (k := fun k : maxCompactU ε ↦ conj (weightMinors ν k))
        (integrable_of_compactSpace h_wm_cont)
        (hg.integrable l.dsGenerator) h_bdd
    have h_gen (g : USign ε) : l.dsGenerator.val.val g = l.dsCoeff g := rfl
    have h_exchange :
        ∫ g : USign ε, l.dsCoeff g *
          (∫ k : maxCompactU ε, conj (weightMinors ν k) *
            B w (π ((y * k)⁻¹ * g)⁻¹ (ι v)) ∂haarK ε) =
        ∫ g : USign ε, (∫ k : maxCompactU ε, conj (weightMinors ν k) *
            l.dsCoeff ↑(y * k * g) ∂haarK ε) * B w (π g⁻¹ (ι v)) := by
      simpa only [grp_inv_inv, mul_assoc, smul_eq_mul, h_gen] using on_vec.symm.trans on_psi
    have h_average (g : USign ε) :
        ∫ k : maxCompactU ε, conj (weightMinors ν k) *
          B w (π ((y * k)⁻¹ * g)⁻¹ (ι v)) ∂haarK ε = T * B (π y⁻¹ (π g w)) (ι v) := by
      rw [← h_vec (π y⁻¹ (π g w))]
      refine integral_congr_ae (.of_forall fun k ↦ ?_)
      dsimp only
      congr 1
      rw [hu.form_apply_eq_form_inv_apply, grp_inv_inv, grp_mul_inv_rev,
        rep_apply_apply, rep_apply_apply]
    simp only [h_average, h_psi, zero_mul, integral_zero, mul_left_comm (l.dsCoeff _),
      integral_const_mul] at h_exchange
    exact (mul_eq_zero.1 h_exchange).resolve_left
      (Complex.ofReal_ne_zero.2 (kTypeNormSq_pos _).ne')
  let w : X := integratedRep π l.dsKernel (π y (ι v))
  have h_integrand (g : USign ε) : l.dsKernel g⁻¹ • B w (π g⁻¹ (π y (ι v))) =
      l.formalDegree * (l.dsCoeff g * B (π y⁻¹ (π g w)) (ι v)) := by
    rw [dsKernel, dsCoeff_inv hg, Complex.conj_conj, smul_eq_mul,
      hu.form_apply_eq_form_inv_apply, hu.form_apply_eq_form_inv_apply, grp_inv_inv, mul_assoc]
  have h_self : B w w = 0 := by
    rw [map_integratedRep hu (hg.integrable_dsKernel_mul_norm_pow A A.le_succ),
      ← integral_inv_eq_self]
    simp only [h_integrand, integral_const_mul, h_zero, mul_zero]
  exact lt_irrefl 0 (h_self ▸ hu.pos w h_ne)

/-- Let `λ = l / 2` have gap `500 n³ + A`, let `π` be a representation of `U(diag ε)` with invariant
positive form `B` and growth exponent `A` (`New.IsUnitaryRep`), and let `ρ` be its derivative along
`ι`. Let `v` be `K`-highest of weight `Λ = New.HCParam.lowestKType l` and `x = ι v`. If
`B x (π z x) > 0` for every positive definite `z` in `U(diag ε)`, then `Re B x (π(e_λ) x) > 0`,
where `e_λ = New.HCParam.dsKernel l` is the function `g ↦ deg_λ · conj(c_λ(g))` and
`π(e_λ) x = ∫ e_λ(g) π(g) x dg`. -/
theorem re_integratedRep_dsKernel_pos (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) (hv : l.IsKHighest ρ l.lowestKType v)
    (h_pos : ∀ z : USign ε, z.val.val.PosDef → 0 < B (ι v) (π z (ι v))) :
    0 < (B (ι v) (integratedRep π l.dsKernel (ι v))).re := by
  -- Average the integrand over `g ↦ k₁⁻¹ g k₂`, `k₁, k₂ ∈ K`. At `g = κ z` the average is, by
  -- `dsCoeff_polar`, `h_left` and `h_right`, a mean over `K` of positive numbers.
  set Λ : HCParam ε := l.lowestKType
  set x : X := ι v
  -- Averaging over `K` against `conj (weightMinors Λ)` in the second argument of `B`, or against
  -- `weightMinors Λ` in the first, multiplies `x` by `Λ.kTypeNormSq`.
  have h_right (w : X) (g : USign ε) :
      ∫ k : maxCompactU ε, weightMinors Λ k.val.val.valᴴ * B w (π (g * k) x) ∂haarK ε =
        Λ.kTypeNormSq * B w (π g x) := by
    simpa only [ContinuousLinearMap.comp_apply, rep_apply_apply, conj_weightMinors] using
      hv.integral_conj_weightMinors_mul hu hd hg.isKDominant_lowestKType (B w ∘L π g)
  have h_left (w : X) :
      ∫ k : maxCompactU ε, weightMinors Λ k * B x (π k.val⁻¹ w) ∂haarK ε =
        Λ.kTypeNormSq * B x w := by
    have h1 := congrArg conj (h_right w 1)
    rw [map_mul, Complex.conj_ofReal, hu.conj_symm, map_one, one_apply_eq_self,
      ← integral_conj] at h1
    refine (integral_congr_ae (.of_forall fun k ↦ ?_)).trans h1
    rw [map_mul, conj_weightMinors, conjTranspose_conjTranspose, one_mul, hu.conj_symm,
      hu.form_apply_eq_form_inv_apply, grp_inv_inv]
  let μ : Measure (maxCompactU ε × maxCompactU ε) := (haarK ε).prod (haarK ε)
  let Φ (g : USign ε) : ℂ := B x (l.dsKernel g • π g x)
  have kernel_int : Integrable fun g : USign ε ↦ l.dsKernel g * (‖(g : Matrix n n ℂ)‖ : ℂ) ^ A :=
    hg.integrable_dsKernel_mul_norm_pow A A.le_succ
  have Φ_int : Integrable Φ := (B x).integrable_comp (integrable_smul_rep hu kernel_int x)
  let T (k : maxCompactU ε × maxCompactU ε) (g : USign ε) : USign ε := ↑k.1⁻¹ * (g * k.2)
  have h_invariant (k : maxCompactU ε × maxCompactU ε) : Measure.map (T k) volume = volume :=
    ((measurePreserving_mul_right _ k.2.val).mul_left _ (k.1⁻¹).val).map_eq
  have h_meas_K : Measurable T.uncurry :=
    ((continuous_subtypeVal.comp (continuous_fst.comp continuous_fst).inv).mul
      (continuous_snd.mul
        (continuous_subtypeVal.comp (continuous_snd.comp continuous_fst)))).measurable
  -- The average of `Φ` over `K × K` is integrable, with the same integral as `Φ`.
  obtain ⟨avg_int, avg_eq⟩ := integral_skew_product h_invariant (Φ_int.comp_snd μ) h_meas_K
  have h_avg : B x (integratedRep π l.dsKernel x) =
      ∫ g : USign ε, ∫ k, Φ (↑k.1⁻¹ * (g * k.2)) ∂μ := by
    rw [avg_eq]
    dsimp only
    rw [integral_const, probReal_univ, one_smul, map_integratedRep hu kernel_int]
    refine integral_congr_ae (.of_forall fun g ↦ ((B x).map_smul _ _).symm)
  refine (re_integral_pos avg_int fun g ↦ ?_).trans_eq (congrArg re h_avg.symm)
  change 0 < (∫ k, Φ (↑k.1⁻¹ * (g * k.2)) ∂μ).re
  obtain ⟨κ, z, hz, rfl, -⟩ := exists_polar g
  have conj_pos (u : USign ε) : (u.val.valᴴ * z.val.val * u.val.val).PosDef :=
    hz.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 u.val.isUnit)
  have hK_adj_eq (a : maxCompactU ε) :
      (a.val.val.valᴴ : Matrix n n ℂ) = (a⁻¹ : maxCompactU ε).val.val.val := by
    rw [← maxCompactU.coe_inv a, ← coe_units_inv, ← Subgroup.coe_inv, ← Subgroup.coe_inv]
  have hK_mul (a b : maxCompactU ε) :
      (a * b : maxCompactU ε).val.val.val = a.val.val.val * b.val.val.val := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul]
  -- `dsCoeff_polar` writes `Φ (k₁⁻¹ κ z k₂)` as the mean over `u ∈ K` of `Ψ (k₁, k₂) u`.
  let Ψ (k : maxCompactU ε × maxCompactU ε) (u : maxCompactU ε) : ℂ :=
    l.formalDegree * (weightMinors Λ (u.val.val.valᴴ * κ.val.val.valᴴ * k.1) *
      weightMinors Λ (k.2.val.val.valᴴ * u) /
        weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u) / Λ.kTypeNormSq) *
      B x (π (k.1⁻¹ * κ * z * k.2) x)
  have h_polar (k : maxCompactU ε × maxCompactU ε) :
      ∫ u, Ψ k u ∂haarK ε = Φ (↑k.1⁻¹ * (κ * z * k.2)) := by
    have h_coeff : conj (l.dsCoeff ↑(↑k.1⁻¹ * (κ * z * k.2) : USign ε)) =
        (∫ u : maxCompactU ε, weightMinors Λ (u.val.val.valᴴ * κ.val.val.valᴴ * k.1) *
          weightMinors Λ (k.2.val.val.valᴴ * u) /
            weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u) ∂haarK ε) / Λ.kTypeNormSq := by
      have h1 := congrArg conj (dsCoeff_polar hg (k.1⁻¹ * κ) k.2⁻¹ hz)
      rw [grp_inv_inv, map_div₀, Complex.conj_ofReal, ← integral_conj] at h1
      refine (congrArg (fun g : USign ε ↦ conj (l.dsCoeff g)) ?_).trans (h1.trans ?_)
      · rw [Subgroup.coe_mul, mul_assoc, mul_assoc, mul_assoc]
      · refine congrArg (· / (Λ.kTypeNormSq : ℂ)) (integral_congr_ae (.of_forall fun u ↦ ?_))
        dsimp only
        rw [map_div₀, map_mul, Complex.conj_conj, conj_weightMinors, conj_weightMinors,
          ← hK_mul, hK_adj_eq, grp_polar_lhs, hK_mul, hK_mul, ← hK_adj_eq, ← hK_adj_eq,
          ← hK_adj_eq k.2, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
          hz.1.eq, ← Matrix.mul_assoc]
    simp only [Φ, Ψ, dsKernel, h_coeff, map_smul, smul_eq_mul]
    simp only [integral_mul_const, integral_const_mul, integral_div, mul_assoc]
  have hK_mat : Continuous fun k : maxCompactU ε ↦ (k.val.val.val : Matrix n n ℂ) :=
    Units.continuous_val.comp (continuous_subtypeVal.comp continuous_subtypeVal)
  have hK_adj : Continuous fun k : maxCompactU ε ↦ (k.val.val.valᴴ : Matrix n n ℂ) :=
    continuous_star.comp hK_mat
  have hΨ_cont :
      Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦ Ψ p.1 p.2 := by
    have h_u : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        (p.2.val.val.val : Matrix n n ℂ) := hK_mat.comp continuous_snd
    have h_uH : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        (p.2.val.val.valᴴ : Matrix n n ℂ) := hK_adj.comp continuous_snd
    have h_k1 : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        (p.1.1.val.val.val : Matrix n n ℂ) := hK_mat.comp (continuous_fst.comp continuous_fst)
    have h_k2H : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        (p.1.2.val.val.valᴴ : Matrix n n ℂ) := hK_adj.comp (continuous_snd.comp continuous_fst)
    have h1 : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        weightMinors Λ (p.2.val.val.valᴴ * κ.val.val.valᴴ * p.1.1) :=
      DiscreteSeries.continuous_weightMinors ((h_uH.mul continuous_const).mul h_k1) fun p ↦ by
        rw [det_mul, det_mul, det_conjTranspose, det_conjTranspose]
        exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 (GeneralLinearGroup.det_ne_zero _))
          (star_ne_zero.2 (GeneralLinearGroup.det_ne_zero _))) (GeneralLinearGroup.det_ne_zero _)
    have h2 : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        weightMinors Λ (p.1.2.val.val.valᴴ * p.2) :=
      DiscreteSeries.continuous_weightMinors (h_k2H.mul h_u) fun p ↦ by
        rw [det_mul, det_conjTranspose]
        exact mul_ne_zero (star_ne_zero.2 (GeneralLinearGroup.det_ne_zero _))
          (GeneralLinearGroup.det_ne_zero _)
    have h3 : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        weightMinors (-paramAddRho l) (p.2.val.val.valᴴ * z * p.2) :=
      DiscreteSeries.continuous_weightMinors ((h_uH.mul continuous_const).mul h_u) fun p ↦
        (conj_pos p.2.val).det_pos.ne'
    have hB : Continuous fun p : (maxCompactU ε × maxCompactU ε) × maxCompactU ε ↦
        B x (π (p.1.1⁻¹ * κ * z * p.1.2) x) :=
      (B x).continuous.comp ((hu.continuous x).comp
        ((((continuous_subtypeVal.comp (continuous_fst.comp continuous_fst)).inv.mul
          continuous_const).mul continuous_const).mul
          (continuous_subtypeVal.comp (continuous_snd.comp continuous_fst))))
    exact ((continuous_const.mul
      (((h1.mul h2).div h3 fun p ↦ (weightMinors_pos (conj_pos p.2.val) _).ne').div_const
        _)).mul hB)
  have Ψ_int : Integrable Ψ.uncurry (μ.prod (haarK ε)) := integrable_of_compactSpace hΨ_cont
  -- For fixed `u`, substitute `(κ u k₁, u k₂)` for `(k₁, k₂)` and use `h_left`, `h_right`.
  have h_inner (u : maxCompactU ε) :
      ∫ k, Ψ k u ∂μ = Λ.kTypeNormSq * l.formalDegree *
        (weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u))⁻¹ *
          B x (π (u⁻¹ * z * u) x) := by
    let c : ℂ := l.formalDegree / weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u) /
      Λ.kTypeNormSq
    have h_subst (k₁ k₂ : maxCompactU ε) : Ψ ((κ * u, u) * (k₁, k₂)) u = c *
        (weightMinors Λ k₂.val.val.valᴴ *
          (weightMinors Λ k₁ * B x (π k₁.val⁻¹ (π (u⁻¹ * z * u * k₂) x)))) := by
      have h_m1 : u.val.val.valᴴ * κ.val.val.valᴴ * (κ * u * k₁ : maxCompactU ε).val.val.val =
          k₁.val.val.val := by
        rw [hK_adj_eq, hK_adj_eq, ← hK_mul, ← hK_mul, mul_assoc κ u k₁, mul_assoc u⁻¹ κ⁻¹,
          inv_mul_cancel_left, inv_mul_cancel_left]
      have h_m2 : (u * k₂ : maxCompactU ε).val.val.valᴴ * u.val.val.val = k₂.val.val.valᴴ := by
        rw [hK_adj_eq, hK_adj_eq, ← hK_mul, grp_m2]
      have h_grp : ((κ * u * k₁)⁻¹ : maxCompactU ε).val * κ.val * z * (u * k₂ : maxCompactU ε).val =
          k₁.val⁻¹ * ((u⁻¹ : maxCompactU ε).val * z * u.val * k₂.val) := by
        simp only [Subgroup.coe_inv, Subgroup.coe_mul, grp_mul_inv_rev, mul_assoc,
          inv_mul_cancel_left]
      dsimp only [Ψ, c, Prod.mk_mul_mk]
      rw [h_m1, h_m2, h_grp, rep_apply_apply]
      ring
    have h_int_k : Integrable (fun k : maxCompactU ε × maxCompactU ε ↦ Ψ ((κ * u, u) * k) u) μ := by
      have h_cont := hΨ_cont.comp
        (((continuous_const (y := (κ * u, u))).mul continuous_id).prodMk
          (continuous_const (y := u)))
      dsimp only [Function.comp_def] at h_cont
      exact integrable_of_compactSpace h_cont
    rw [← integral_mul_left_eq_self _ (κ * u, u), integral_prod_symm _ h_int_k]
    simp only [h_subst, integral_const_mul, h_left, mul_left_comm _ (ofReal Λ.kTypeNormSq), h_right]
    dsimp only [c]
    have h_ne : (Λ.kTypeNormSq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (kTypeNormSq_pos Λ).ne'
    calc
      _ = (Λ.kTypeNormSq : ℂ) * (Λ.kTypeNormSq : ℂ)⁻¹ * (Λ.kTypeNormSq * l.formalDegree *
            (weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u))⁻¹ *
              B x (π (u⁻¹ * z * u) x)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = Λ.kTypeNormSq * l.formalDegree *
            (weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u))⁻¹ *
              B x (π (u⁻¹ * z * u) x) := by
          rw [mul_inv_cancel₀ h_ne, one_mul]
  -- Each factor on the right of `h_inner` is positive, `u⁻¹ z u` being positive definite.
  have h_inner_pos (u : maxCompactU ε) : 0 < ∫ k, Ψ k u ∂μ := by
    rw [h_inner]
    have h_z : ((u⁻¹ : maxCompactU ε).val * z * u.val).val.val.PosDef := by
      have h_eq : ((u⁻¹ : maxCompactU ε).val * z * u.val).val.val =
          u.val.val.valᴴ * z.val.val * u.val.val.val := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hK_adj_eq u]
      rw [h_eq]
      exact conj_pos u.val
    have h1 : (0 : ℂ) < Λ.kTypeNormSq := pos_iff.2 ⟨kTypeNormSq_pos Λ, rfl⟩
    have h2 : (0 : ℂ) < l.formalDegree := pos_iff.2 ⟨formalDegree_pos hg, rfl⟩
    have h3 : (0 : ℂ) < (weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u))⁻¹ :=
      inv_pos.2 (weightMinors_pos (conj_pos u.val) _)
    exact mul_pos (mul_pos (mul_pos h1 h2) h3) (h_pos _ h_z)
  simp_rw [← h_polar, integral_integral_swap Ψ_int]
  exact re_integral_pos Ψ_int.integral_prod_right fun u ↦ (pos_iff.1 (h_inner_pos u)).1

/-! ### Rigidity of highest vectors -/

omit [Nonempty n] in
/-- Let two `gl n`-modules on inner product spaces have inner products invariant under `𝔲(ε)` and
Casimir operator at least `New.HCParam.casimirValue l` (`New.IsUnitaryCasimirGe`). Then the
componentwise action on their orthogonal direct sum is a `gl n`-module with the same property. -/
theorem IsUnitaryCasimirGe.exists_prodL2 {H₁ H₂ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {ρ₁ : GlModule n H₁} {ρ₂ : GlModule n H₂} (h₁ : IsUnitaryCasimirGe l ρ₁)
    (h₂ : IsUnitaryCasimirGe l ρ₂) :
    ∃ P : GlModule n (WithLp 2 (H₁ × H₂)),
      (∀ (Y : Matrix n n ℂ) (w : WithLp 2 (H₁ × H₂)), P Y w = toLp 2 (ρ₁ Y w.fst, ρ₂ Y w.snd)) ∧
      IsUnitaryCasimirGe l P := by
  let P : GlModule n (WithLp 2 (H₁ × H₂)) :=
    { ρ := (WithLp.linearEquiv 2 ℂ (H₁ × H₂)).symm.conj.toLinearMap ∘ₗ
        LinearMap.prodMapLinear ℂ H₁ H₂ H₁ H₂ ℂ ∘ₗ ρ₁.ρ.prod ρ₂.ρ
      map_bracket Y Z := by
        apply LinearMap.ext; intro w; apply WithLp.ofLp_injective 2; apply Prod.ext
        · change ρ₁ (Y * Z - Z * Y) w.fst = ρ₁ Y (ρ₁ Z w.fst) - ρ₁ Z (ρ₁ Y w.fst)
          rw [ρ₁.map_bracket]; rfl
        · change ρ₂ (Y * Z - Z * Y) w.snd = ρ₂ Y (ρ₂ Z w.snd) - ρ₂ Z (ρ₂ Y w.snd)
          rw [ρ₂.map_bracket]; rfl }
  have P_apply (Y : Matrix n n ℂ) (w : WithLp 2 (H₁ × H₂)) :
      P Y w = toLp 2 (ρ₁ Y w.fst, ρ₂ Y w.snd) := rfl
  -- inner products, square norms and Casimir operators add up over the two components
  refine ⟨P, P_apply, fun a b v w ↦ ?_, fun y ↦ ?_⟩
  · rw [GlModule.E, P_apply, P_apply, WithLp.prod_inner_apply, WithLp.prod_inner_apply,
      ← GlModule.E, ← GlModule.E, h₁.inner_E_left, h₂.inner_E_left, mul_add]
    rfl
  · have h_casimir : P.casimirK 1 y = toLp 2 (ρ₁.casimirK 1 y.fst, ρ₂.casimirK 1 y.snd) := by
      apply WithLp.ofLp_injective 2; apply Prod.ext
      · change (P.casimirK 1 y).ofLp.1 = ρ₁.casimirK 1 y.fst
        rw [casimirK, casimir, casimirK, casimir, LinearMap.sum_apply, WithLp.ofLp_sum,
          Prod.fst_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [LinearMap.sum_apply, WithLp.ofLp_sum, Prod.fst_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun b _ ↦ rfl
      · change (P.casimirK 1 y).ofLp.2 = ρ₂.casimirK 1 y.snd
        rw [casimirK, casimir, casimirK, casimir, LinearMap.sum_apply, WithLp.ofLp_sum,
          Prod.snd_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [LinearMap.sum_apply, WithLp.ofLp_sum, Prod.snd_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun b _ ↦ rfl
    rw [h_casimir, prod_norm_sq_eq_of_L2, mul_add, WithLp.prod_inner_apply, add_re]
    exact add_le_add (h₁.casimirValue_mul_le y.fst) (h₂.casimirValue_mul_le y.snd)

attribute [-simp] Complex.coe_smul coe_inner Subtype.forall in
omit [CompleteSpace X] [Nonempty n] in
/-- Let `π` be a representation of `U(diag ε)` on the normed space `X` with `IsUnitaryRep A π B`: it
is strongly continuous with `‖π g‖ ≤ C‖g‖^A`, and `B` is a hermitian, positive definite,
`π`-invariant bounded form. Let `ρ` be the `gl n`-module on `M` that is the derivative of `π` along
`ι`, let `j` carry `B` to the inner product of `H`, and let `ι (Ω v) = c • ι v` with
`Ω = ρ.casimirK 1` and `c ≥ κ_λ = New.HCParam.casimirValue l = |λ|² − |ρ|²`, where `l = 2λ` and this
`ρ` is the half-sum of positive roots, not the module. Then `ρ` descends to a `gl n`-module `σ` on
the range of `j ∘ ι`, compatible with `ρ`, and the submodule generated by `j (ι v)` is as in
`New.IsUnitaryCasimirGe`: its inner product is invariant under `𝔲(ε)` and its Casimir operator is at
least `κ_λ`. -/
theorem exists_isUnitaryCasimirGe_generatedModule (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (j : X ≃ₗ[ℂ] H) (inner_j : ∀ x y : X, inner ℂ (j x) (j y) = B x y)
    (hv_casimir : ι (ρ.casimirK 1 v) = ofReal c • ι v) (hc_ge : l.casimirValue ≤ c) :
    ∃ σ : GlModule n (j.toLinearMap ∘ₗ ι).range,
      (∀ (Y : Matrix n n ℂ) (w : M), σ Y ((j.toLinearMap ∘ₗ ι).rangeRestrict w) =
        (j.toLinearMap ∘ₗ ι).rangeRestrict (ρ Y w)) ∧
      IsUnitaryCasimirGe l (σ.generatedModule ((j.toLinearMap ∘ₗ ι).rangeRestrict v)) := by
  let jι : M →ₗ[ℂ] H := j.toLinearMap ∘ₗ ι
  let x : jι.range := jι.rangeRestrict v
  have skew (a b : n) (u w : M) :
      B (ι (ρ.E a b u)) (ι w) = (ε a * ε b).val * B (ι u) (ι (ρ.E b a w)) :=
    hd.form_E_eq_sign_mul hu a b u w
  -- by skewness `ρ` keeps the kernel of `ι`, so it descends to a module `σ` on the range
  have h_ker (Y : Matrix n n ℂ) (w : M) (hw : jι w = 0) : jι (ρ Y w) = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    nth_rw 1 [apply_eq_sum]
    rw [LinearMap.sum_apply, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [LinearMap.sum_apply, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [LinearMap.smul_apply, map_smul, inner_smul_left]
    have h0 : inner ℂ (jι (ρ.E a b w)) (jι (ρ Y w)) = 0 := by
      change inner ℂ (j (ι (ρ.E a b w))) (j (ι (ρ Y w))) = 0
      rw [inner_j, skew, ← inner_j]
      change (ε a * ε b).val * inner ℂ (jι w) (j (ι (ρ.E b a (ρ Y w)))) = 0
      rw [hw, inner_zero_left, mul_zero]
    rw [h0, mul_zero]
  obtain ⟨σ, σ_apply⟩ := ρ.exists_action_on_range jι h_ker
  refine ⟨σ, σ_apply, ?_⟩
  change IsUnitaryCasimirGe l (σ.generatedModule x)
  refine ⟨?_, fun y ↦ ?_⟩
  · rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := jι.surjective_rangeRestrict y
    obtain ⟨w, rfl⟩ := jι.surjective_rangeRestrict z
    have gen_apply (Y : Matrix n n ℂ) (u : M) (hu_mem : jι.rangeRestrict u ∈ σ.filtration 1 x 0) :
        (σ.generatedModule x Y ⟨jι.rangeRestrict u, hu_mem⟩ : H) = j (ι (ρ Y u)) :=
      congrArg Subtype.val (σ_apply Y u)
    rw [coe_inner, coe_inner, coe_inner, coe_inner, gen_apply, gen_apply]
    change inner ℂ (j (ι (ρ.E a b u))) (j (ι w)) =
      (ε a * ε b).val * inner ℂ (j (ι u)) (j (ι (ρ.E b a w)))
    rw [inner_j, inner_j, skew]
  · -- `Ω` acts on all of the generated module by `c`
    have Ω_x : σ.casimirK 1 x = ofReal c • x := by
      ext
      have h1 : j (ι (ρ.casimirK 1 v)) = ofReal c • j (ι v) := by rw [hv_casimir, map_smul]
      change ((σ.casimirK 1 x : jι.range) : H) = ofReal c • j (ι v)
      rw [← h1]
      simp only [casimirK, casimir, LinearMap.sum_apply, mul_apply_eq_comp, Submodule.coe_sum,
        x, σ_apply, map_sum]
      rfl
    rw [casimirK_generatedModule Ω_x, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, ← RCLike.re_eq_complex_re,
      ← norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact mul_le_mul_of_nonneg_right hc_ge (sq_nonneg _)

attribute [-simp] Complex.coe_smul coe_inner Subtype.forall in
omit [CompleteSpace X] in
/-- Rigidity. Let `λ` have gap `500 n³ + A`, let `π` be a representation of `U(diag ε)` with
invariant positive form `B` and growth exponent `A` (`New.IsUnitaryRep`), and `ρ` its derivative
along `ι`. Let `v` be `K`-highest of weight `New.HCParam.lowestKType l` with `ι (Ω v) = c • ι v` for
the Casimir operator `Ω` of `gl n`, where `c ≥ New.HCParam.casimirValue l`. Then
`B (ι v) (π g (ι v)) = B (ι v) (ι v) c_λ(g)` for all `g`, where `c_λ = New.HCParam.dsCoeff l`.

A variant of Parthasarathy's criterion recognizing a discrete series by its lowest `K`-type `μ`: for
a large gap, with a Casimir bound in place of the absence of the types `μ - α`, as an equality of
matrix coefficients. -/
theorem coeff_eq_dsCoeff_of_isKHighest (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) (hv : l.IsKHighest ρ l.lowestKType v)
    (hv_casimir : ι (ρ.casimirK 1 v) = ofReal c • ι v) (hc_ge : l.casimirValue ≤ c) (g : USign ε) :
    B (ι v) (π g (ι v)) = B (ι v) (ι v) * l.dsCoeff g := by
  -- Let `x` be the image of `v` in an inner product space for `B` (`inner_j`), on which `π` acts
  -- by isometries (`norm_j`). In the sum of the module generated by `x` with `l.DsModule` the
  -- vector `(x, -⟪x, x⟫ • dsGenerator)` is highest and orthogonal to `(x, dsGenerator)`, hence to
  -- all that the latter generates. Test this on coefficients.
  obtain ⟨H, _, _, j, inner_j, norm_j⟩ := hu.exists_innerProductSpace
  let jι : M →ₗ[ℂ] H := j.toLinearMap ∘ₗ ι
  let x : jι.range := jι.rangeRestrict v
  obtain ⟨σ, σ_apply, gen_unitary⟩ : ∃ σ : GlModule n jι.range,
      (∀ (Y : Matrix n n ℂ) (w : M), σ Y (jι.rangeRestrict w) = jι.rangeRestrict (ρ Y w)) ∧
      IsUnitaryCasimirGe l (σ.generatedModule x) :=
    exists_isUnitaryCasimirGe_generatedModule hu hd j inner_j hv_casimir hc_ge
  have gen_apply (Y : Matrix n n ℂ) (u : M) (hu_mem : jι.rangeRestrict u ∈ σ.filtration 1 x 0) :
      (σ.generatedModule x Y ⟨jι.rangeRestrict u, hu_mem⟩ : H) = j (ι (ρ Y u)) :=
    congrArg Subtype.val (σ_apply Y u)
  -- the componentwise action `P` on the orthogonal sum of the two modules
  obtain ⟨P, P_apply, P_unitary⟩ := gen_unitary.exists_prodL2 hg.isUnitaryCasimirGe
  let d (t : ℂ) : WithLp 2 (σ.filtration 1 x 0 × l.DsModule) :=
    toLp 2 (⟨x, self_mem_filtration⟩, t • l.dsGenerator)
  have highest (t : ℂ) : l.IsKHighest P l.lowestKType (d t) := by
    have gen_highest := isKHighest_dsGenerator hg
    have gen_mk (Y : Matrix n n ℂ) (y : σ.filtration 1 x 0) :
        σ.generatedModule x Y y = ⟨σ Y y.val, (σ.generatedModule x Y y).prop⟩ := rfl
    simp_all [d, x, smul_smul, mul_comm, IsKHighest, WithLp.ext_iff]
  -- A highest vector is orthogonal to lowered vectors, and `norm_dsGenerator` handles `d 1` itself.
  have perp_zero : d (-inner ℂ x x) ∈ (P.filtration ε (d 1) 0)ᗮ :=
    prodL2_perp_zero P_unitary (coe_inner ..) hg.norm_dsGenerator highest
  -- Orthogonality to the step `0` of the filtration spreads to all steps.
  have perp (s : ℕ) : d (-inner ℂ x x) ∈ (P.filtration ε (d 1) s)ᗮ :=
    mem_orthogonal_filtration_of_casimirK 0 P_unitary (highest 1) _ (highest _).casimirK_eq_smul
      (by rw [Nat.cast_zero, add_zero]) perp_zero s
  -- the coefficient map `(j (ι u), w) ↦ B (ι v) (π g (ι u)) - ⟪x, x⟫ * w g` is bounded, and by
  -- `perp` it vanishes for `g = 1` on all that `d 1` generates; so it vanishes on `d 1` for every
  -- `g` (analytic vectors, `coeffMap_eq_zero`)
  let coef (g : USign ε) : WithLp 2 (σ.filtration 1 x 0 × l.DsModule) →ₗ[ℂ] ℂ :=
    { toFun w := B (ι v) (π g (j.symm w.fst)) - inner ℂ x x * w.snd.val.val g
      map_add' w w' := by
        change B (ι v) (π g (j.symm (w.fst.val + w'.fst.val))) -
            inner ℂ x x * (w.snd.val.val g + w'.snd.val.val g) = _
        rw [j.symm.map_add, (π g).map_add, (B (ι v)).map_add, mul_add, add_sub_add_comm]
      map_smul' t w := by
        change B (ι v) (π g (j.symm (t • w.fst.val))) -
            inner ℂ x x * (t * w.snd.val.val g) = _
        rw [j.symm.map_smul, (π g).map_smul, (B (ι v)).map_smul, RingHom.id_apply, smul_eq_mul,
          smul_eq_mul, mul_sub, mul_left_comm] }
  have coef_apply (g : USign ε) (w : WithLp 2 (σ.filtration 1 x 0 × l.DsModule)) :
      coef g w = B (ι v) (π g (j.symm w.fst)) - inner ℂ x x * w.snd.val.val g := rfl
  have is_coef : P.IsCoeffMap coef := by
    rintro g Y ⟨⟨y, hy⟩, w⟩ t
    obtain ⟨u, rfl⟩ := jι.surjective_rangeRestrict y
    simp only [coef_apply, P_apply, WithLp.toLp_fst, WithLp.toLp_snd, gen_apply]
    refine .sub ?_ (.const_mul _ (hasDerivAt_rightDeriv_expU ..))
    have h_u : j.symm ((jι.rangeRestrict u : jι.range) : H) = ι u := j.symm_apply_apply (ι u)
    rw [h_u, j.symm_apply_apply]
    exact hd.isCoeffMap (B (ι v)) g Y u t
  have bounded (g : USign ε) (w : WithLp 2 (σ.filtration 1 x 0 × l.DsModule)) :
      ‖coef g w‖ ≤ (‖j (ι v)‖ + ‖inner ℂ x x‖) * ‖w‖ :=
    prodL2_norm_sub_le (norm_nonneg _)
      (by
        rw [← inner_j]
        refine (norm_inner_le_norm (j (ι v)) (j (π g (j.symm w.fst)))).trans ?_
        rw [norm_j, j.apply_symm_apply, norm_coe, norm_coe])
      (hg.norm_apply_le_norm w.snd g)
  have at_one (s : ℕ) (w : WithLp 2 (σ.filtration 1 x 0 × l.DsModule))
      (hw : w ∈ P.filtration ε (d 1) s) : coef 1 w = 0 := by
    have h_inner : inner ℂ (d (-inner ℂ x x)) w = coef 1 w := by
      have inner_fst : inner ℂ ⟨x, self_mem_filtration⟩ w.fst = B (ι v) (j.symm w.fst) := by
        rw [← inner_j, j.apply_symm_apply, coe_inner, coe_inner]
        rfl
      have inner_snd : inner ℂ l.dsGenerator w.snd = w.snd.val.val 1 := by
        rw [← hg.isDerivedAction_toL2_and_inner_toL2.2.1, map_one]
        rfl
      rw [coef_apply, map_one, one_apply_eq_self]
      exact prodL2_at_one_inner (inner_self_conj x) inner_fst inner_snd
    rw [← h_inner]
    exact inner_left_of_mem_orthogonal hw (perp s)
  have h_zero : coef g (d 1) = 0 :=
    (highest 1).coeffMap_eq_zero P_unitary is_coef bounded at_one g
  have x_norm_sq : inner ℂ x x = B (ι v) (ι v) := inner_j (ι v) (ι v)
  rw [coef_apply, x_norm_sq] at h_zero
  change B (ι v) (π g (j.symm (j (ι v)))) -
    B (ι v) (ι v) * (1 • l.dsGenerator).val.val g = 0 at h_zero
  rw [j.symm_apply_apply, one_smul, sub_eq_zero] at h_zero
  exact h_zero

/-- Let `λ = l / 2` have gap `500 n³ + A`, let `π`, `B` be as in `New.IsUnitaryRep` with
exponent `A`, `ρ` the derivative of `π` along `ι`, and `‖g‖ ^ A • f g` integrable. Suppose (a)
`f * e_λ = e_λ` for `e_λ = New.HCParam.dsKernel l`; (b) `v` is `K`-highest of weight
`New.HCParam.lowestKType l`; (c) `ι (Ω v) = c • ι v` for the Casimir operator `Ω = ρ.casimirK 1`,
with `c ≥ New.HCParam.casimirValue l`. Then `π(f) = ∫ f(g) π(g) dg` fixes `ι v`. -/
theorem integratedRep_fix_of_isKHighest (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) (hf : Integrable fun g : USign ε ↦ f g * ‖g.val.val‖ ^ A)
    (hv : l.IsKHighest ρ l.lowestKType v) (hv_casimir : ι (ρ.casimirK 1 v) = ofReal c • ι v)
    (hc_ge : l.casimirValue ≤ c)
    (h_repr : ∀ g : USign ε, ∫ y : USign ε, f y * l.dsKernel (y⁻¹ * g) = l.dsKernel g) :
    integratedRep π f (ι v) = ι v := by
  -- The vector `d = π(f) x - x`, with `x = ι v`, is orthogonal to the orbit of `x`, by `h_repr` and
  -- `B x (π g x) = B x x * l.dsCoeff g` (`coeff_eq_dsCoeff_of_isKHighest`); so it is orthogonal to
  -- itself.
  by_contra h_ne
  have h_psi (g : USign ε) : ∫ y : USign ε, f y * l.dsCoeff ↑(g * y) = l.dsCoeff g := by
    have h1 := h_repr g⁻¹
    rw [dsKernel, dsCoeff_inv hg, Complex.conj_conj] at h1
    have h2 : ∫ y : USign ε, f y * l.dsKernel (y⁻¹ * g⁻¹) =
        l.formalDegree * ∫ y : USign ε, f y * l.dsCoeff ↑(g * y) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      dsimp only
      rw [dsKernel, ← dsCoeff_inv hg (y⁻¹ * g⁻¹), grp_mul_inv_rev, grp_inv_inv, grp_inv_inv]
      ring
    rw [h2] at h1
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (formalDegree_pos hg).ne') h1
  let d : X := integratedRep π f (ι v) - ι v
  have h_orth (g : USign ε) : B d (π g (ι v)) = 0 := by
    rw [← hu.conj_symm, map_sub, map_integratedRep hu hf, ← grp_inv_inv g]
    simp only [← hu.form_apply_eq_form_inv_apply, rep_apply_apply,
      coeff_eq_dsCoeff_of_isKHighest hg hu hd hv hv_casimir hc_ge, smul_eq_mul, mul_left_comm (f _),
      integral_const_mul, h_psi, sub_self, map_zero]
  have h_zero : B d d = 0 := calc
    _ = B d (integratedRep π f (ι v)) - B d (π 1 (ι v)) := by rw [map_one, ← map_sub]; rfl
    _ = 0 := by simp only [map_integratedRep hu hf, h_orth, smul_zero, integral_zero, sub_zero]
  exact lt_irrefl 0 (h_zero ▸ hu.pos d (sub_ne_zero.2 h_ne))

end New
