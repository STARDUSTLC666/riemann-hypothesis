module

public import Lib.Weil.DualPair.FiniteAction
import Lib.Weil.Construction.CanonicalTheta
import Lib.Weil.DualPair.WeilAction

/-!
# Theta kernels of unitary pairs modulo an ideal: formal laws and seesaw identities

This file proves the formal laws of the theta kernel θ^{S,T}_{a,b}[Ψ,P](g,h) =
`New.modKernel` S T a b 𝔪 Ψ P g h. Here S and T are spaces of ranks n and n′, and a and b are
characters of [U(1)]. Ψ is a function on n′ × n matrices over O_E/𝔪, and P is a polynomial whose
variables are indexed by an infinite place and a matrix position (row, column). The kernel is
`New.pairTheta` of the datum `New.modDatum`; the laws cover bilinearity, twisting, integral
translations, seesaw identities, negation, passing to a smaller ideal and relabelling.

## Main definitions and results

* `New.exists_conj_modKernel_eq_mul_modKernel_neg`: the complex conjugate of a kernel is a kernel
  for the negated first space, up to a factor of modulus one.
* `New.modKernel_mul_stdLevel_left`, `New.modKernel_mul_stdLevel_right`: right translation by the
  lattice stabiliser `New.stdLevel` acts on Ψ through its reduction `New.Modulus.reductionGL`, up to
  a scalar; `New.modDatum_factor`, `New.modKernel_factor`: passing to a smaller ideal.
* `New.modKernel_block_right`, `New.modKernel_sum_right`, `New.modKernel_sum_left`,
  `New.Rows.modKernelStdSpace_block`: seesaw identities, the kernel of a direct sum at block
  diagonal elements is a product.

Notions from other files:
* `New.pairWeil`: The representation ω_{a,b}(g, h) = a(det h) b(det g)⁻¹ ω(`onHom` (g, h)); the
  scalar is `New.pairChar a b (g, h)`.
* `New.Modulus`: a nonzero ideal of O_E prime to its complex conjugate, that is, never divisible by
  both w and w̄; `𝔪.ResidueRing` is O_E/𝔪 and `𝔪.places` the set of primes dividing 𝔪.
* `New.Space.boxProd`: the product f₁ ⊠ f₂ of data on two blocks of coordinates.
* `New.negSource` (`Lib.Weil.DualPair.FiniteAction`): the change of coordinates x ↦ (1, u⁻¹) x from
  Hom(S⁻,T) to Hom(S,T); `negSource.map` pulls data on Hom(S,T) back to data on Hom(S⁻,T).

## Relation to the literature

Known; see `Lib.Weil.DualPair.GaloisLaw` for sources.

See also `Lib.Weil.DualPair.ThetaLiftConvergence`.
-/

@[expose] public section

noncomputable section

section KernelLaws

namespace New

open NumberField Matrix MvPolynomial ComplexConjugate WeilData Space Fock Weil CoordChange Modulus
  Fintype Function Pi Ideal.Quotient

variable {E : Type} [Field E] [CMType E]
  {n n' n₁ n₂ : Type _} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n₁]
  [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] [WeilData E] {s : n → ℤˣ} {s' : n' → ℤˣ}
  {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
  (𝔪 : Modulus E) (V : Space E n₁ s₁)

/-- Reduction modulo 𝔪, as a homomorphism from the stabiliser of Ô^n in the finite adelic
unitary group to GL_n(O_E/𝔪). -/
def Modulus.reductionGL {E : Type} [Field E] [NumberField E] [IsCMField E] (𝔪 : Modulus E) :
    stdLevel E n →* GL n 𝔪.ResidueRing := stdLevel.map n 𝔪.reduction

omit [WeilData E] in
@[simp]
lemma Modulus.factor_reductionGL {𝔪 𝔫 : Modulus E} {h : 𝔫.ideal ≤ 𝔪.ideal} {k : stdLevel E n} :
    (reductionGL 𝔫 k).val.map (factor h) = (reductionGL 𝔪 k).val :=
  Matrix.ext fun i j ↦ by
    rw [Matrix.map_apply, reductionGL, reductionGL, stdLevel.map_apply, stdLevel.map_apply,
      𝔪.factor_reduction _ h]

/-- The theta kernel θ^{S,I}_{a,b}[Ψ, P](g, (1, h)), where I is the standard space I_{n′} of rank n′
and h lies in its finite adelic unitary group. -/
abbrev modKernelStdSpace (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : Gf E n') : ℂ :=
  modKernel S (stdSpace E n') a b 𝔪 Ψ P g (1, h)

/-- The datum on Hom(S, T) with the function Ψ on matrices modulo 𝔪 at the places dividing 𝔪 and the
vacuum at the other finite places, as an element of the finite part of the space of data. -/
def vacuumDatum (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) : (S.hom T).finitePart :=
  ⟨(S.hom T).schrodingerOp 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix)) (vacElem (S.hom T)),
    schrodingerOp_mem_finitePart ..⟩

/-- For maps e, f of row and column indices, the ℂ-algebra map of polynomial rings sending the
variable X_(i,r,c) to X_(i,e(r),f(c)). -/
abbrev renameRowsCols {ι a b c d : Type*} (e : a → c) (f : b → d) :
    MvPolynomial (ι × a × b) ℂ →ₐ[ℂ] MvPolynomial (ι × c × d) ℂ :=
  rename (R := ℂ) (Prod.map (id (α := ι)) (Prod.map e f))

/-! ### Bilinearity, twisting, integral translations and seesaw identities -/

private lemma modDatum_smul (c : ℂ) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
    modDatum S T 𝔪 (c • Ψ) v = c • modDatum S T 𝔪 Ψ v := by
  rw [modDatum, modDatum, Pi.smul_comp, 𝔪.liftFn.map_smul,
    ((S.hom T).schrodingerOp 𝔪.places).map_smul, _root_.smul_apply,
    ((S.hom T).integrated v).map_smul]

/-- The value θ^{S,T}_{a,b}[Ψ, P](g, h) of the theta kernel as a complex bilinear form in the
function Ψ modulo 𝔪 and the polynomial P. -/
def modKernelBilin (g : G E s) (h : G E s') :
    (Matrix n' n 𝔪.ResidueRing → ℂ) →ₗ[ℂ] MvPolynomial (InfinitePlace E × n' × n) ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun Ψ P ↦ modKernel S T a b 𝔪 Ψ P g h)
    (fun Ψ Ψ' P ↦ by
      rw [modKernel, modKernel, modKernel, pairTheta, pairTheta, pairTheta, modDatum, modDatum,
        modDatum, Pi.add_comp, 𝔪.liftFn.map_add, ((S.hom T).schrodingerOp 𝔪.places).map_add,
        _root_.add_apply, ((S.hom T).integrated _).map_add,
        (pairWeil S T a b (g, h)).map_add, (S.hom T).θ.map_add])
    (fun c Ψ P ↦ by
      rw [modKernel, modKernel, pairTheta, pairTheta, modDatum_smul,
        (pairWeil S T a b (g, h)).map_smul, (S.hom T).θ.map_smul])
    (fun Ψ P P' ↦ by
      rw [modKernel, modKernel, modKernel, pairTheta, pairTheta, pairTheta, modDatum, modDatum,
        modDatum, (polyVector _).map_add, (S.hom T).integrated.map_add,
        _root_.add_apply, (pairWeil S T a b (g, h)).map_add, (S.hom T).θ.map_add])
    (fun c Ψ P ↦ by
      rw [modKernel, modKernel, pairTheta, pairTheta, modDatum, modDatum, (polyVector _).map_smul,
        (S.hom T).integrated.map_smul, _root_.smul_apply,
        (pairWeil S T a b (g, h)).map_smul, (S.hom T).θ.map_smul])

@[simp]
lemma modKernelBilin_apply (g : G E s) (h : G E s') (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
    modKernelBilin S T a b 𝔪 g h Ψ P = modKernel S T a b 𝔪 Ψ P g h :=
  rfl

/-- Multiplying the characters `a`, `b` of the Weil representation of a pair by characters `μ`, `μ'`
of `[U(1)]` multiplies the operator `ω_{a,b}(g, h)` by `μ (det h) / μ' (det g)`. -/
lemma pairWeil_twist (μ μ' : AutChar E) (g : G E s) (h : G E s') :
    pairWeil S T (a * μ) (b * μ') (g, h) =
      ((μ.val h.det : ℂ) / (μ'.val g.det : ℂ)) • pairWeil S T a b (g, h) := by
  have h_char : pairChar (a * μ) (b * μ') (g, h) =
      μ.val h.det / μ'.val g.det * pairChar a b (g, h) := by
    rw [pairChar_apply, pairChar_apply]
    change ((a.val h.det : ℂ) * (μ.val h.det : ℂ)) *
        ((b.val g.det : ℂ) * (μ'.val g.det : ℂ))⁻¹ = _
    rw [mul_inv, div_eq_mul_inv]
    ring
  ext f
  rw [_root_.smul_apply, pairWeil_apply, pairWeil_apply, h_char, mul_smul]

/-- For hermitian spaces `S` and `T`, characters `a`, `b`, `μ`, `μ'` in `AutChar E`, a test
function `f` in `𝒮 (S.hom T)`, and unitary group elements `g : G E s` and `h : G E s'`:
replacing the characters `a`, `b` of the theta kernel `pairTheta S T a b f` by `a * μ` and `b * μ'`
multiplies its value at `(g, h)` by `μ (det h) / μ' (det g)`. -/
lemma pairTheta_twist (μ μ' : AutChar E) (f : 𝒮 (S.hom T)) (g : G E s) (h : G E s') :
    pairTheta S T (a * μ) (b * μ') f (g, h) =
      μ.val h.det / μ'.val g.det * pairTheta S T a b f (g, h) := by
  rw [pairTheta, pairTheta, pairWeil_twist, _root_.smul_apply, (S.hom T).θ.map_smul, smul_eq_mul]

/-- Twisting the characters: for characters μ, μ′ of [U(1)], θ_{aμ,bμ′}[Ψ,P](g,h) = μ(det h)
μ′(det g)⁻¹ θ_{a,b}[Ψ,P](g,h), for all Ψ modulo 𝔪, polynomials P, and g, h. -/
lemma modKernel_twist (μ μ' : AutChar E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : G E s') :
    modKernel S T (a * μ) (b * μ') 𝔪 Ψ P g h =
      μ.val h.det / μ'.val g.det * modKernel S T a b 𝔪 Ψ P g h :=
  pairTheta_twist S T a b μ μ' _ g h

/-- For integral finite k in U(S) and k′ in U(T), ω_{a,b}(k, k′) sends the datum `New.modDatum` of
Ψ mod 𝔪 and a real Fock vector v to a(det k′) b(det k)⁻¹ times the datum of x ↦ Ψ(k′⁻¹xk) and v,
with k, k′ reduced modulo 𝔪 and `New.detFin` the finite determinant. -/
lemma pairWeil_modDatum_stdLevel (k : stdLevel E n) (k' : stdLevel E n')
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
    pairWeil S T a b ((1, k.val), 1, k'.val) (modDatum S T 𝔪 Ψ v) =
      (a.val (detFin s' k'.val) * (b.val (detFin s k.val))⁻¹).val •
        modDatum S T 𝔪 (fun x : Matrix n' n 𝔪.ResidueRing ↦
          Ψ ((𝔪.reductionGL k')⁻¹.val * x * (𝔪.reductionGL k).val)) v := by
  -- The pair is integral, so it acts on the vacuum by the stated character value.
  have h_vac : pairWeil S T a b ((1, k.val), 1, k'.val) (S.hom T).vacElem =
      (a.val (detFin s' k'.val) * (b.val (detFin s k.val))⁻¹).val • (S.hom T).vacElem :=
    pairWeil_eq_smul_of_projOn_eq ⊤ (S.hom T).projOn_vacElem
      ⟨k.2, Gf.mem_supportedOn.2 fun _ h _ ↦ (h trivial).elim⟩
      ⟨k'.2, Gf.mem_supportedOn.2 fun _ h _ ↦ (h trivial).elim⟩
  -- Reduction modulo `𝔪` commutes with `x ↦ k'⁻¹ x k`.
  have h_eq (F : Matrix n' n 𝔪.ResidueRing → ℂ) (y : n' × n → 𝔸f E) :
      𝔪.liftFn (F ∘ vecToMatrix) y =
        liftIntegralFn 𝔪.reduction F (idem 𝔪.places • vecToMatrix y) := by
    rw [liftFn_apply]
    by_cases hy : ∀ i : n' × n, idem 𝔪.places * y i ∈ Ô E
    · rw [dite_eq_left hy]
      have hM : idem 𝔪.places • vecToMatrix y =
          (Matrix.of fun i j ↦ (⟨idem 𝔪.places * y (i, j), hy (i, j)⟩ : Ô E)).map
            (Ô E).subtype := Matrix.ext fun _ _ ↦ rfl
      rw [hM, liftIntegralFn_map_subtype]
      rfl
    · rw [dite_eq_right hy, liftIntegralFn_of_not_isIntMatrix (M := idem 𝔪.places • vecToMatrix y)
        _ _ fun h ↦ hy fun ⟨i, j⟩ ↦ h i j]
  have hk' : ((stdLevel.map n' (.id _) k'⁻¹).map 𝔪.reduction).val = (𝔪.reductionGL k')⁻¹.val :=
    congrArg Units.val (by
      rw [show (𝔪.reductionGL k')⁻¹ = 𝔪.reductionGL k'⁻¹ from (map_inv 𝔪.reductionGL k').symm]
      exact Units.ext (Matrix.ext fun _ _ ↦ rfl))
  have hk : ((stdLevel.map n (.id _) k).map 𝔪.reduction).val = (𝔪.reductionGL k).val :=
    Matrix.ext fun _ _ ↦ rfl
  have h_lift : (fun x : n' × n → 𝔸f E ↦ 𝔪.liftFn (Ψ ∘ vecToMatrix)
        (matrixToVec ((k'.val⁻¹ : Gf E n').val.val * vecToMatrix x * k.val.val.val))) =
      𝔪.liftFn ((fun X : Matrix n' n 𝔪.ResidueRing ↦
        Ψ ((𝔪.reductionGL k')⁻¹.val * X * (𝔪.reductionGL k).val)) ∘ vecToMatrix) := by
    funext x
    rw [h_eq, h_eq]
    have h_mat : idem 𝔪.places • ((k'.val⁻¹ : Gf E n').val.val * vecToMatrix x * k.val.val.val) =
        ((stdLevel.map n' (.id _) k'⁻¹).map (Ô E).subtype).val *
          (idem 𝔪.places • vecToMatrix x) *
          ((stdLevel.map n (.id _) k).map (Ô E).subtype).val := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      rfl
    change liftIntegralFn 𝔪.reduction Ψ
        (idem 𝔪.places • ((k'.val⁻¹ : Gf E n').val.val * vecToMatrix x * k.val.val.val)) = _
    rw [h_mat, liftIntegralFn_mul, hk', hk]
  -- The pair is trivial at infinity, so it acts only on the finite datum: it replaces the lift of
  -- `Ψ` by its translate under `x ↦ k'⁻¹ x k` and scales the vacuum.
  rw [modDatum, pairWeil_integrated_fin,
    pairWeil_schrodingerOp_of_mem 𝔪.isConjDisjoint_places k.property k'.property, h_vac, map_smul,
    map_smul, h_lift, modDatum]

/-- Let `modKernel S T a b 𝔪 Ψ P` be the theta kernel (g, h) ↦ θ(ω_{a,b}(g, h) f) on the adelic
unitary groups of `S` and `T`, where the datum f is built from a function `Ψ` on n′ × n matrices
modulo `𝔪` and the Fock vector of the polynomial `P`. For `k` in the stabiliser of Ô^n in the finite
unitary group, the kernel at (g·(1, k), h) equals the kernel at (g, h) with `Ψ` replaced by
x ↦ b(det k)⁻¹ Ψ(x k̄). Here k̄ is the reduction of `k` modulo `𝔪`. -/
lemma modKernel_mul_stdLevel_left (k : stdLevel E n) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : G E s') :
    modKernel S T a b 𝔪 Ψ P (g * (1, k.val)) h =
      modKernel S T a b 𝔪 ((b.val (detFin s k.val) : ℂ)⁻¹ •
        fun x : Matrix n' n 𝔪.ResidueRing ↦ Ψ (x * (𝔪.reductionGL k).val)) P g h := by
  -- The pair `((1, k), 1)` acts on the datum of `Ψ` as stated.
  have h_act (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
      pairWeil S T a b ((1, k.val), 1) (modDatum S T 𝔪 Ψ v) = modDatum S T 𝔪
        ((b.val (detFin s k.val) : ℂ)⁻¹ • fun x ↦ Ψ (x * (𝔪.reductionGL k).val)) v := by
    have h := pairWeil_modDatum_stdLevel S T a b 𝔪 k 1 Ψ v
    rw [show ((1 : GInf E s'), (1 : stdLevel E n').val) = (1 : G E s') from Prod.mk_one_one] at h
    have hc : (a.val (detFin s' (1 : stdLevel E n').val) * (b.val (detFin s k.val))⁻¹).val =
        (b.val (detFin s k.val) : ℂ)⁻¹ := by
      change (a.val (G.det (1 : G E s')) * (b.val (detFin s k.val))⁻¹).val = _
      rw [map_one, map_one, one_mul]
      rfl
    have hΨ : (fun x : Matrix n' n 𝔪.ResidueRing ↦
          Ψ ((𝔪.reductionGL (1 : stdLevel E n'))⁻¹.val * x * (𝔪.reductionGL k).val)) =
        fun x ↦ Ψ (x * (𝔪.reductionGL k).val) :=
      funext fun x ↦ by rw [map_one, inv_one, Units.val_one, Matrix.one_mul]
    rw [h, hc, hΨ, modDatum_smul]
  rw [modKernel, modKernel, ← h_act, ← pairTheta_mul]
  simp only [Prod.mk_mul_mk, mul_one]

/-- Let `modKernel S T a b 𝔪 Ψ P` be the theta kernel (g, h) ↦ θ(ω_{a,b}(g, h) f) on the adelic
unitary groups of `S` and `T`, where the datum f is built from a function `Ψ` on n′ × n matrices
modulo `𝔪` and the Fock vector of the polynomial `P`. For `k` in the stabiliser of Ô^{n′} in the
finite unitary group, the kernel at (g, (x, h k)) equals the kernel at (g, (x, h)) with `Ψ` replaced
by y ↦ a(det k) Ψ(k̄⁻¹ y). Here k̄ is the reduction of `k` modulo `𝔪`. -/
lemma modKernel_mul_stdLevel_right (k : stdLevel E n') (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (x : GInf E s') (h : Gf E n') :
    modKernel S T a b 𝔪 Ψ P g (x, h * k.val) =
      modKernel S T a b 𝔪 ((a.val (detFin s' k.val) : ℂ) •
        fun y : Matrix n' n 𝔪.ResidueRing ↦ Ψ ((𝔪.reductionGL k)⁻¹.val * y)) P g (x, h) := by
  -- The pair `(1, (1, k))` acts on the datum of `Ψ` as stated.
  have h_act (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
      pairWeil S T a b (1, 1, k.val) (modDatum S T 𝔪 Ψ v) = modDatum S T 𝔪
        ((a.val (detFin s' k.val) : ℂ) • fun y ↦ Ψ ((𝔪.reductionGL k)⁻¹.val * y)) v := by
    have h := pairWeil_modDatum_stdLevel S T a b 𝔪 1 k Ψ v
    rw [show ((1 : GInf E s), (1 : stdLevel E n).val) = (1 : G E s) from Prod.mk_one_one] at h
    have hc : (a.val (detFin s' k.val) * (b.val (detFin s (1 : stdLevel E n).val))⁻¹).val =
        (a.val (detFin s' k.val) : ℂ) := by
      change (a.val (detFin s' k.val) * (b.val (G.det (1 : G E s)))⁻¹).val = _
      rw [map_one, map_one, inv_one, mul_one]
    have hΨ : (fun y : Matrix n' n 𝔪.ResidueRing ↦
          Ψ ((𝔪.reductionGL k)⁻¹.val * y * (𝔪.reductionGL (1 : stdLevel E n)).val)) =
        fun y ↦ Ψ ((𝔪.reductionGL k)⁻¹.val * y) :=
      funext fun y ↦ by rw [map_one, Units.val_one, Matrix.mul_one]
    rw [h, hc, hΨ, modDatum_smul]
  rw [modKernel, modKernel, ← h_act, ← pairTheta_mul]
  simp only [Prod.mk_mul_mk, mul_one]

omit [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂] [WeilData E] in
/-- Along a splitting `e` of the coordinates, the lift `liftFn` to finite adelic vectors (Φ of the
reduction mod 𝔪 of the components at the places dividing 𝔪 if these are integral, 0 otherwise) of a
product of functions modulo `𝔪` of the two blocks is the product of their lifts. -/
lemma Modulus.liftFn_mul_blocks (e : n₁ ⊕ n₂ ≃ n) (Φ₁ : (n₁ → 𝔪.ResidueRing) → ℂ)
    (Φ₂ : (n₂ → 𝔪.ResidueRing) → ℂ) :
    𝔪.liftFn (fun y : n → 𝔪.ResidueRing ↦ Φ₁ (y ∘ e ∘ Sum.inl) * Φ₂ (y ∘ e ∘ Sum.inr)) =
      fun x : n → 𝔸f E ↦ 𝔪.liftFn Φ₁ (x ∘ e ∘ Sum.inl) * 𝔪.liftFn Φ₂ (x ∘ e ∘ Sum.inr) := by
  have _ : Nonempty (Fintype n₁) ∧ Nonempty (Fintype n₂) := ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩
  funext x
  -- `x` is integral at `𝔪.places` exactly when both blocks are
  have h_int : (∀ i : n, idem 𝔪.places * x i ∈ Ô E) ↔
      (∀ i : n₁, idem 𝔪.places * (x ∘ e ∘ Sum.inl) i ∈ Ô E) ∧
        ∀ i : n₂, idem 𝔪.places * (x ∘ e ∘ Sum.inr) i ∈ Ô E := by
    rw [← e.forall_congr_right, Sum.forall]
    rfl
  rw [liftFn_apply, liftFn_apply, liftFn_apply]
  by_cases hx : ∀ i : n, idem 𝔪.places * x i ∈ Ô E
  · obtain ⟨hx₁, hx₂⟩ := h_int.1 hx
    rw [dite_eq_left hx, dite_eq_left hx₁, dite_eq_left hx₂]
    rfl
  · rw [dite_eq_right hx]
    rcases not_and_or.1 (mt h_int.2 hx) with hx₁ | hx₂
    · rw [dite_eq_right hx₁, zero_mul]
    · rw [dite_eq_right hx₂, mul_zero]

/-- Let `e` split the coordinates of `S` into those of `V₁` and `V₂`, compatibly with the signs.
Take on each `Vᵢ` the datum given by the Fock vector of a polynomial `Pᵢ`, a function `Φᵢ` modulo
`𝔪` at the primes dividing `𝔪`, and the vacuum elsewhere. The product `boxProd` of these data is
the datum on `S` given by `P₁ P₂` and `Φ₁ Φ₂`, read on the two blocks of coordinates. -/
lemma boxProd_integrated_schrodingerOp_liftFn {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂)
    (V₁ : Space E n₁ s₁) (V₂ : Space E n₂ s₂) (Φ₁ : (n₁ → 𝔪.ResidueRing) → ℂ)
    (Φ₂ : (n₂ → 𝔪.ResidueRing) → ℂ) (P₁ : MvPolynomial (InfinitePlace E × n₁) ℂ)
    (P₂ : MvPolynomial (InfinitePlace E × n₂) ℂ) :
    boxProd hs
      (V₁.integrated (polyVector (realSigns E s₁) P₁)
        (V₁.schrodingerOp 𝔪.places (𝔪.liftFn Φ₁) V₁.vacElem))
      (V₂.integrated (polyVector (realSigns E s₂) P₂)
        (V₂.schrodingerOp 𝔪.places (𝔪.liftFn Φ₂) V₂.vacElem)) =
      S.integrated
        (polyVector (realSigns E s)
          (rename (Prod.map id (e ∘ Sum.inl)) P₁ * rename (Prod.map id (e ∘ Sum.inr)) P₂))
        (S.schrodingerOp 𝔪.places
          (𝔪.liftFn fun y : n → 𝔪.ResidueRing ↦ Φ₁ (y ∘ e ∘ Sum.inl) * Φ₂ (y ∘ e ∘ Sum.inr))
          S.vacElem) := by
  rw [boxProd_integrated, realBoxProd_polyVector,
    boxProd_schrodingerOp hs 𝔪.isConjDisjoint_places (𝔪.liftFn_mul_blocks e Φ₁ Φ₂)]
  rfl

/-- Seesaw identity in the second space, along a sign-compatible splitting `e` of the coordinates
of `T` into those of `V₁` and `V₂`. Let the point of `T` be block diagonal with blocks the points
of `V₁` and `V₂`, and let `h` be block diagonal with blocks `h₁` and `h₂`. With Ψ₁, P₁ and Ψ₂, P₂
read on the two blocks of rows, θ^{S,T}_{a,bb′}[Ψ₁Ψ₂, P₁P₂](g, h) is
θ^{S,V₁}_{a,b}[Ψ₁,P₁](g,h₁) · θ^{S,V₂}_{a,b′}[Ψ₂,P₂](g,h₂). -/
lemma modKernel_block_right {e : n₁ ⊕ n₂ ≃ n'} (hs : s' ∘ e = s₁ ⊕ᵥ s₂) {V₁ : Space E n₁ s₁}
    {V₂ : Space E n₂ s₂} (h_point : T.x.val.submatrix e e = fromBlocks V₁.x 0 0 V₂.x)
    {h : G E s'} {h₁ : G E s₁} {h₂ : G E s₂}
    (h_group : h.adeleMatrix.submatrix e e = fromBlocks h₁.adeleMatrix 0 0 h₂.adeleMatrix)
    (b' : AutChar E) (Ψ₁ : Matrix n₁ n 𝔪.ResidueRing → ℂ) (Ψ₂ : Matrix n₂ n 𝔪.ResidueRing → ℂ)
    (P₁ : MvPolynomial (InfinitePlace E × n₁ × n) ℂ)
    (P₂ : MvPolynomial (InfinitePlace E × n₂ × n) ℂ) (g : G E s) :
    modKernel S T a (b * b') 𝔪
        (fun x : Matrix n' n 𝔪.ResidueRing ↦
          Ψ₁ (x.submatrix (e ∘ Sum.inl) id) * Ψ₂ (x.submatrix (e ∘ Sum.inr) id))
        (renameRowsCols (e ∘ Sum.inl) id P₁ * renameRowsCols (e ∘ Sum.inr) id P₂) g h =
      modKernel S V₁ a b 𝔪 Ψ₁ P₁ g h₁ * modKernel S V₂ a b' 𝔪 Ψ₂ P₂ g h₂ := by
  -- The product of the two data is the datum of the product function and the product polynomial.
  have h_datum : boxProd (homSigns_sum_target hs)
        (modDatum S V₁ 𝔪 Ψ₁ (polyVector (realSigns E (homSigns s s₁)) P₁))
        (modDatum S V₂ 𝔪 Ψ₂ (polyVector (realSigns E (homSigns s s₂)) P₂)) =
      modDatum S T 𝔪 (fun x : Matrix n' n 𝔪.ResidueRing ↦
          Ψ₁ (x.submatrix (e ∘ Sum.inl) id) * Ψ₂ (x.submatrix (e ∘ Sum.inr) id))
        (polyVector (realSigns E (homSigns s s'))
          (renameRowsCols (e ∘ Sum.inl) id P₁ * renameRowsCols (e ∘ Sum.inr) id P₂)) :=
    boxProd_integrated_schrodingerOp_liftFn (S.hom T) 𝔪 (homSigns_sum_target hs) (S.hom V₁)
      (S.hom V₂) (Ψ₁ ∘ vecToMatrix) (Ψ₂ ∘ vecToMatrix) P₁ P₂
  -- `θ` and `pairWeil` are multiplicative for `boxProd`.
  simp only [modKernel, pairTheta]
  rw [← h_datum, pairWeil_boxProd_target hs S a b b' h_group, theta_boxProd_target hs S h_point]

/-- Seesaw identity in the second space: the kernel of (S, T ⊕ V) for characters a, bb′, the product
ΨΨ′ on the two row blocks and PP′ (P, P′ read in the variables of the two row blocks), at (g, h ⊕
h′), is θ^{S,T}_{a,b}[Ψ,P](g,h) · θ^{S,V}_{a,b′}[Ψ′,P′](g,h′). -/
lemma modKernel_sum_right (b' : AutChar E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (Ψ' : Matrix n₁ n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (P' : MvPolynomial (InfinitePlace E × n₁ × n) ℂ) (g : G E s) (h : G E s') (h' : G E s₁) :
    modKernel S (T.sum V) a (b * b') 𝔪
        (fun x : Matrix (n' ⊕ n₁) n 𝔪.ResidueRing ↦ Ψ x.toRows₁ * Ψ' x.toRows₂)
        (renameRowsCols Sum.inl id P * renameRowsCols Sum.inr id P') g (G.sum (h, h')) =
      modKernel S T a b 𝔪 Ψ P g h * modKernel S V a b' 𝔪 Ψ' P' g h' :=
  -- The point of `T.sum V` and `G.sum (h, h')` are block diagonal along the identity splitting.
  modKernel_block_right S (T.sum V) a b 𝔪 signs_comp_refl
    (by rw [Equiv.coe_refl, submatrix_id_id]; rfl)
    (by rw [Equiv.coe_refl, submatrix_id_id, G.adeleMatrix_sum]) b' Ψ Ψ' P P' g

/-- For a modulus 𝔪, a function Ψ on `n' × n` matrices over O_E/𝔪 and a polynomial P in variables
indexed by (infinite place, row, column), the theta kernel θ^{S,T}_{a,b}[Ψ,P](g,h) = θ(ω_{a,b}(g,h)
f) (`modKernel`) is built from the datum f given by Ψ and the Fock vector of P. Seesaw identity in
the first space: the kernel of (S ⊕ V, T) for characters aa′, b, the product ΨΨ′ on the two column
blocks and PP′ (P, P′ read in the variables of the two column blocks), at (g ⊕ g′, h), is
θ^{S,T}_{a,b}[Ψ,P](g,h) · θ^{V,T}_{a′,b}[Ψ′,P′](g′,h). -/
lemma modKernel_sum_left (a' : AutChar E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (Ψ' : Matrix n' n₁ 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (P' : MvPolynomial (InfinitePlace E × n' × n₁) ℂ) (g : G E s) (g' : G E s₁) (h : G E s') :
    modKernel (S.sum V) T (a * a') b 𝔪
        (fun x : Matrix n' (n ⊕ n₁) 𝔪.ResidueRing ↦ Ψ x.toCols₁ * Ψ' x.toCols₂)
        (renameRowsCols id Sum.inl P * renameRowsCols id Sum.inr P') (G.sum (g, g')) h =
      modKernel S T a b 𝔪 Ψ P g h * modKernel V T a' b 𝔪 Ψ' P' g' h := by
  -- The product of the two data is the datum of the product function and the product polynomial.
  have h_datum : boxProd homSigns_sum_source
        (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P))
        (modDatum V T 𝔪 Ψ' (polyVector (realSigns E (homSigns s₁ s')) P')) =
      modDatum (S.sum V) T 𝔪 (fun x : Matrix n' (n ⊕ n₁) 𝔪.ResidueRing ↦ Ψ x.toCols₁ * Ψ' x.toCols₂)
        (polyVector (realSigns E (homSigns (s ⊕ᵥ s₁) s'))
          (renameRowsCols id Sum.inl P * renameRowsCols id Sum.inr P')) :=
    boxProd_integrated_schrodingerOp_liftFn ((S.sum V).hom T) 𝔪 homSigns_sum_source (S.hom T)
      (V.hom T) (Ψ ∘ vecToMatrix) (Ψ' ∘ vecToMatrix) P P'
  -- `θ` and `pairWeil` are multiplicative for `boxProd`.
  simp only [modKernel, pairTheta]
  rw [← h_datum, pairWeil_boxProd_source, theta_boxProd_source]

/-! ### Negation -/

/-- The unit of O_E/𝔪 that is the reduction of the chosen element of norm −1 of Ô. -/
def Modulus.normNegOne : 𝔪.ResidueRingˣ := Weil.normNegOne.map 𝔪.reduction.toMonoidHom

/-- Let Ψ be a function on n′ × n matrices over O_E/𝔪 and P a complex polynomial. The antilinear map
`negSource.map`, from data on Hom(S,T) to data on Hom(S⁻,T), sends the datum `modDatum` of v_P and Ψ
to the datum of v_{P̄} and x ↦ conj(Ψ(u⁻¹x)). Here P̄ is P with conjugated coefficients, the
polynomial vectors use the signs s′s and s′(−s) respectively, and u = `𝔪.normNegOne` is the unit of
O_E/𝔪 obtained by reducing the chosen ε ∈ Ô with εε̄ = −1. -/
lemma map_negSource_modDatum (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
    negSource.map (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) =
      modDatum S.neg T 𝔪 (fun x : Matrix n' n 𝔪.ResidueRing ↦ conj (Ψ (𝔪.normNegOne⁻¹ • x)))
        (polyVector (realSigns E (homSigns (-s) s')) (MvPolynomial.map conj P)) := by
  have h_idem (R : Set (FinPlace E)) (x : n' × n → 𝔸f E) :
      (negSource (s := s) (s' := s')).finEquiv (idem R • x) =
        idem R • (negSource (s := s) (s' := s')).finEquiv x :=
    smul_comm (Weil.normNegOne (E := E))⁻¹ (idem R) x
  -- The real part: negating the signs conjugates the holomorphic coordinates.
  have h_real : negSource.realMap (polyVector (realSigns E (homSigns s s')) P) =
      polyVector (realSigns E (homSigns (-s) s')) (MvPolynomial.map conj P) := by
    have h_sign_neg (i : InfinitePlace E × n' × n) :
        realSigns E (homSigns (-s) s') i = -realSigns E (homSigns s s') i := by
      simp only [realSigns, homSigns, pairSign, Pi.neg_apply, mul_neg]
    ext x
    have h_coord : conj ∘ holomorphicCoord (realSigns E (homSigns s s')) x =
        holomorphicCoord (realSigns E (homSigns (-s) s')) x := funext fun i ↦ by
      simp only [Function.comp_apply, holomorphicCoord_eq, h_sign_neg]
      rcases Int.units_eq_one_or (realSigns E (homSigns s s') i) with h_sign | h_sign
      · rw [h_sign, ite_eq_left rfl, ite_eq_right (by decide), Pi.star_apply, Complex.star_def,
          starRingEnd_self_apply]
      · rw [h_sign, ite_eq_right (by decide), neg_neg, ite_eq_left rfl]
        rfl
    change conj (polyVector (realSigns E (homSigns s s')) P x) =
      polyVector (realSigns E (homSigns (-s) s')) (MvPolynomial.map conj P) x
    rw [polyVector_apply, polyVector_apply, map_mul, (isVacuum_realVac (ε := 1)).conj_apply x,
      ← h_coord, map_eval]
  -- The finite part: `negSource` scales by the unit `normNegOne⁻¹` of `Ô`, which keeps integrality
  -- and reduces to `𝔪.normNegOne⁻¹`.
  have h_fin : (fun x : n' × n → 𝔸f E ↦
        conj (𝔪.liftFn (Ψ ∘ vecToMatrix) ((negSource (s := s) (s' := s')).finEquiv x))) =
      𝔪.liftFn ((fun X : Matrix n' n 𝔪.ResidueRing ↦ conj (Ψ (𝔪.normNegOne⁻¹ • X))) ∘
        vecToMatrix) := by
    funext x
    let c : (Ô E)ˣ := Weil.normNegOne⁻¹
    have h_int (i : n' × n) : idem 𝔪.places * (c • x) i ∈ Ô E ↔ idem 𝔪.places * x i ∈ Ô E := by
      have h_mul : idem 𝔪.places * (c • x) i = (c.val : 𝔸f E) * (idem 𝔪.places * x i) := by
        change idem 𝔪.places * ((c.val : 𝔸f E) * x i) = _
        rw [mul_left_comm]
      rw [h_mul]
      refine ⟨fun h ↦ ?_, fun h ↦ mul_mem c.val.2 h⟩
      have h' := mul_mem c⁻¹.val.2 h
      rwa [← mul_assoc, ← Subring.coe_mul, Units.inv_mul, OneMemClass.coe_one, one_mul] at h'
    change conj (𝔪.liftFn (Ψ ∘ vecToMatrix) (c • x)) = _
    rw [liftFn_apply, liftFn_apply]
    by_cases hx : ∀ i : n' × n, idem 𝔪.places * x i ∈ Ô E
    · rw [dite_eq_left hx, dite_eq_left fun i ↦ (h_int i).2 (hx i)]
      refine congrArg conj (congrArg Ψ (Matrix.ext fun i j ↦ ?_))
      have h_mul : (⟨idem 𝔪.places * (c • x) (i, j), (h_int (i, j)).2 (hx (i, j))⟩ : Ô E) =
          c.val * ⟨idem 𝔪.places * x (i, j), hx (i, j)⟩ := by
        ext1
        change idem 𝔪.places * ((c.val : 𝔸f E) * x (i, j)) =
          (c.val : 𝔸f E) * (idem 𝔪.places * x (i, j))
        rw [mul_left_comm]
      exact (congrArg 𝔪.reduction h_mul).trans (map_mul 𝔪.reduction _ _)
    · rw [dite_eq_right hx, dite_eq_right fun h ↦ hx fun i ↦ (h_int i).1 (h i), map_zero]
  rw [modDatum, map_integrated, h_real, CoordChange.map_schrodingerOp _ (h_idem _) (h_idem _)
    𝔪.isConjDisjoint_places 𝔪.isConjDisjoint_places, h_fin, modDatum]

/-- Negating S conjugates theta kernels: for some c of modulus one depending only on S and T, the
conjugate of θ^{S,T}_{a,b}[Ψ,P](g,h) (`New.modKernel`, the theta kernel of the datum built from Ψ on
matrices mod 𝔪 and the Fock vector of P, with a, b twisting the action) is c
θ^{S⁻,T}_{a⁻¹υⁿ,b⁻¹υ^{n′}}[Ψ′,P̄](g,h) for all a, b, 𝔪, Ψ, P, g, h, where n, n′ are the sizes. Here
S⁻ is `New.Space.neg` S, and Ψ′(x) is the conjugate of Ψ(u⁻¹x), with u the unit of O_E/𝔪 reducing
the chosen element of norm −1 of Ô. P̄ has the conjugate coefficients, and υ is the splitting
character of the Weil data restricted to the norm-one ideles. On the right, `New.G.neg` moves g to
the group of S⁻. -/
lemma exists_conj_modKernel_eq_mul_modKernel_neg :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ (a b : AutChar E) (𝔪 : Modulus E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
          (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s) (h : G E s'),
        conj (modKernel S T a b 𝔪 Ψ P g h) =
          c * modKernel S.neg T (a⁻¹ * upsilonU1 ^ card n) (b⁻¹ * upsilonU1 ^ card n') 𝔪
            (fun x : Matrix n' n 𝔪.ResidueRing ↦ conj (Ψ (𝔪.normNegOne⁻¹ • x)))
            (MvPolynomial.map conj P) (G.neg g) h := by
  -- The map `negSource` conjugates `θ` up to the phase `c` and intertwines the actions `pairWeil`.
  obtain ⟨c, hc, hθ⟩ := exists_theta_negSource S T
  refine ⟨c, hc, fun a b 𝔪 Ψ P g h ↦ ?_⟩
  simp only [modKernel, pairTheta]
  rw [← hθ, map_smul, ← pairWeil_negSource, map_negSource_modDatum, smul_eq_mul]

/-! ### Passing to a smaller ideal -/

variable {S T a b 𝔪}

/-- If the ideal 𝔪′ is contained in 𝔪, the datum modulo 𝔪′ given by the pullback of Ψ under
reduction to O_E/𝔪 and by the real Fock vector v equals the datum modulo 𝔪 given by Ψ and v. -/
lemma modDatum_factor {𝔪' : Modulus E} (h : 𝔪'.ideal ≤ 𝔪.ideal) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
    modDatum S T 𝔪' (fun x : Matrix n' n 𝔪'.ResidueRing ↦ Ψ (x.map (factor h))) v =
      modDatum S T 𝔪 Ψ v := by
  -- The box function at the new places `R` names a projection that fixes the vacuum, so by
  -- `schrodingerOp_union` the right side is named at `𝔪'.places` by `𝔪.liftFn _` times this box
  -- function.
  let R : Set (FinPlace E) := 𝔪'.places \ 𝔪.places
  have h_sub : 𝔪.places ⊆ 𝔪'.places := fun w hw ↦ h.trans hw
  have h_union : 𝔪.places ∪ R = 𝔪'.places := Set.union_sdiff_cancel h_sub
  have h_conj : (𝔪.places ∪ R).IsConjDisjoint := h_union ▸ 𝔪'.isConjDisjoint_places
  have h_diff : R.IsConjDisjoint :=
    𝔪'.isConjDisjoint_places.mono Set.sdiff_subset (Set.preimage_mono Set.sdiff_subset)
  have h_lift : 𝔪.liftFn (Ψ ∘ vecToMatrix) * boxIndicator (n' × n) R =
      𝔪'.liftFn ((fun X : Matrix n' n 𝔪'.ResidueRing ↦ Ψ (X.map (factor h))) ∘ vecToMatrix) := by
    funext x
    have h_int : (∀ i : n' × n, idem 𝔪'.places * x i ∈ Ô E) ↔
        (∀ i : n' × n, idem 𝔪.places * x i ∈ Ô E) ∧ x ∈ integralBox (n' × n) R := by
      rw [← h_union, mem_integralBox, ← forall_and]
      refine forall_congr' fun i ↦ ?_
      rw [idem_mul_mem_Ô, idem_mul_mem_Ô, idem_mul_mem_Ô, ← forall_and]
      exact forall_congr' fun w ↦ ⟨fun hw ↦ ⟨fun h₁ ↦ hw (.inl h₁), fun h₂ ↦ hw (.inr h₂)⟩,
        fun ⟨h₁, h₂⟩ hw ↦ hw.elim h₁ h₂⟩
    simp only [Pi.mul_apply, liftFn_apply, boxIndicator_apply]
    by_cases hx : ∀ i : n' × n, idem 𝔪'.places * x i ∈ Ô E
    · obtain ⟨hx_old, hx_new⟩ := h_int.1 hx
      -- The parts of `x` at the two sets of places agree modulo `𝔪`.
      have h_red (i : n' × n) : 𝔪.reduction ⟨idem 𝔪.places * x i, hx_old i⟩ =
          factor h (𝔪'.reduction ⟨idem 𝔪'.places * x i, hx i⟩) := by
        rw [𝔪.factor_reduction _ h]
        refine 𝔪.reduction_congr fun w hw ↦ ?_
        change idem 𝔪.places w * x i w = idem 𝔪'.places w * x i w
        rw [idem_of_mem hw, idem_of_mem (h_sub hw)]
      rw [dite_eq_left hx, dite_eq_left hx_old, ite_eq_left hx_new, mul_one]
      exact congrArg Ψ (Matrix.ext fun i j ↦ h_red (i, j))
    · -- Either `x` is not integral at `𝔪.places`, or it lies outside the box at `R`.
      obtain hx_old | hx_new := not_and_or.1 (mt h_int.2 hx)
      · rw [dite_eq_right hx, dite_eq_right hx_old, zero_mul]
      · rw [dite_eq_right hx, ite_eq_right hx_new, mul_zero]
  rw [modDatum, modDatum, ← h_lift, ← h_union,
    schrodingerOp_union _ h_conj disjoint_sdiff_self_right,
    schrodingerOp_boxIndicator h_diff, projOn_vacElem]

/-- Change of modulus: if the ideal 𝔪′ is contained in 𝔪, a function Ψ on matrices modulo 𝔪, read
modulo 𝔪′ through the reduction O_E/𝔪′ → O_E/𝔪, has the same theta kernel as Ψ, for all characters
a, b of [U(1)], polynomials P and points g, h. -/
lemma modKernel_factor {𝔪' : Modulus E} (h_le : 𝔪'.ideal ≤ 𝔪.ideal)
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s)
    (h : G E s') :
    modKernel S T a b 𝔪' (fun x : Matrix n' n 𝔪'.ResidueRing ↦ Ψ (x.map (factor h_le))) P g h =
      modKernel S T a b 𝔪 Ψ P g h := by
  rw [modKernel, modKernel, modDatum_factor h_le]

/-! ### Relabelling, and the seesaw identity for a standard space split into blocks -/

/-- The theta kernel θ[Ψ, P](g, h) is unchanged when the coordinates of S and T are relabelled
by sign-compatible bijections e, e′ and Ψ, P, g, h are relabelled accordingly. -/
lemma modKernel_reindex (e : n ≃ n₁) (he : s ∘ e.symm = s₁) (e' : n' ≃ n₂) (he' : s' ∘ e'.symm = s₂)
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (g : G E s)
    (h : G E s') :
    modKernel (S.reindex (t := s₁) e he) (T.reindex (t := s₂) e' he') a b 𝔪
        (fun x : Matrix n₂ n₁ 𝔪.ResidueRing ↦ Ψ (x.submatrix e' e)) (renameRowsCols e' e P)
        (G.reindex e he g) (G.reindex e' he' h) =
      modKernel S T a b 𝔪 Ψ P g h := by
  subst he he'
  -- View the relabelled space as the sum of `S.hom T` and the zero space `V₀`, on which the
  -- trivial datum has theta value `1`; then `θ`, `ω` and the data are multiplicative.
  let S' : Space E n₁ (s ∘ e.symm) := S.reindex e rfl
  let T' : Space E n₂ (s' ∘ e'.symm) := T.reindex e' rfl
  let g' : G E (s ∘ e.symm) := G.reindex e rfl g
  let h' : G E (s' ∘ e'.symm) := G.reindex e' rfl h
  let ε : (n' × n) ⊕ Empty ≃ n₂ × n₁ := .trans (.sumEmpty ..) (e'.prodCongr e)
  let V₀ : Space E Empty 1 := stdSpace E Empty
  let f₀ : 𝒮 V₀ :=
    V₀.integrated (polyVector (realSigns E 1) 1) (V₀.schrodingerOp 𝔪.places (𝔪.liftFn 1) V₀.vacElem)
  have h_one : V₀.θ (V₀.ω 1 f₀) = 1 := by
    have hf₀ : f₀ = V₀.vacElem := by
      dsimp only [f₀]
      rw [polyVector_one, liftFn_one, schrodingerOp_boxIndicator 𝔪.isConjDisjoint_places,
        V₀.projOn_vacElem]
      exact V₀.projReal_vacElem
    rw [map_one, one_apply_eq_self, hf₀, theta_apply,
      vacElem_apply_eq_prod_lineTheta fun _ ↦ _root_.funext fun i ↦ i.elim]
    exact Finset.prod_empty
  have h_signs : homSigns (s ∘ e.symm) (s' ∘ e'.symm) ∘ ε = homSigns s s' ⊕ᵥ 1 := by
    funext x
    rcases x with ⟨i, j⟩ | x
    · simp only [Function.comp_apply, ε, Equiv.trans_apply, Equiv.sumEmpty_apply_inl,
        Equiv.prodCongr_apply, Prod.map_apply, homSigns, pairSign, Sum.elim_inl,
        Equiv.symm_apply_apply]
    · exact x.elim
  have h_point : (S'.hom T').x.val.submatrix ε ε = fromBlocks (S.hom T).x 0 0 V₀.x := by
    refine Matrix.ext fun p q ↦ ?_
    rcases p with ⟨i, j⟩ | p
    · rcases q with ⟨k, l⟩ | q
      · change kroneckerMap (· * ·) T'.x.1 S'.x⁻¹.1ᵀ (e' i, e j) (e' k, e l) =
          kroneckerMap (· * ·) T.x.1 S.x⁻¹.1ᵀ (i, j) (k, l)
        simp only [kroneckerMap_apply, transpose_apply]
        change T.x.1 (e'.symm (e' i)) (e'.symm (e' k)) * S.x⁻¹.1 (e.symm (e l)) (e.symm (e j)) = _
        rw [e'.symm_apply_apply, e'.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]
      · exact q.elim
    · exact p.elim
  have h_group : (G.onHom (g', h')).adeleMatrix.submatrix ε ε =
      fromBlocks (G.onHom (g, h)).adeleMatrix 0 0 (1 : G E (1 : Empty → ℤˣ)).adeleMatrix := by
    refine Matrix.ext fun p q ↦ ?_
    rcases p with ⟨i, j⟩ | p
    · rcases q with ⟨k, l⟩ | q
      · rw [submatrix_apply, fromBlocks_apply₁₁, G.adeleMatrix_onHom, G.adeleMatrix_onHom,
          kroneckerMap_apply, kroneckerMap_apply, transpose_apply, transpose_apply,
          show g'⁻¹ = G.reindex e rfl g⁻¹ from (map_inv (G.reindex e rfl) g).symm,
          G.adeleMatrix_reindex, G.adeleMatrix_reindex]
        change h.adeleMatrix (e'.symm (e' i)) (e'.symm (e' k)) *
            g⁻¹.adeleMatrix (e.symm (e l)) (e.symm (e j)) = _
        rw [e'.symm_apply_apply, e'.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]
      · exact q.elim
    · exact p.elim
  -- The product of the datum with the trivial one is the relabelled datum.
  have h_datum : boxProd (V := S'.hom T') h_signs
        (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) f₀ =
      modDatum S' T' 𝔪 (fun x : Matrix n₂ n₁ 𝔪.ResidueRing ↦ Ψ (x.submatrix e' e))
        (polyVector (realSigns E (homSigns (s ∘ e.symm) (s' ∘ e'.symm)))
          (renameRowsCols e' e P)) := by
    simp only [modDatum, f₀, boxProd_integrated_schrodingerOp_liftFn, map_one, Pi.one_apply,
      mul_one]
    rfl
  have h_det {m m' : Type _} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
      {t : m → ℤˣ} (f : m ≃ m') (x : G E t) : (G.reindex f rfl x).det = x.det := by
    ext1
    exact Matrix.det_submatrix_equiv_self f.symm x.adeleMatrix
  have h_char : pairChar a b (g', h') = pairChar a b (g, h) := by
    rw [pairChar_apply, pairChar_apply, h_det e g, h_det e' h]
  simp only [modKernel, pairTheta, pairWeil_apply, map_smul]
  rw [h_char, ← h_datum, omega_boxProd _ h_group, theta_boxProd _ h_point, h_one, mul_one]

/-- Seesaw identity for the standard space I_n = `New.stdSpace E n`, split as I_{n₁} ⊕ I_{n₂} along
a bijection ε, with `U.block ε` the block diagonal embedding of the unitary groups. Here
`New.modKernelStdSpace` is the theta kernel with a standard second space and finite second argument.
With Ψ, P read on the n₁ rows and Ψ′, P′ on the n₂ rows, θ^{T,I_n}_{a,bb′}[ΨΨ′, PP′](g, h ⊕ h′) =
θ^{T,I_{n₁}}_{a,b}[Ψ,P](g,h) · θ^{T,I_{n₂}}_{a,b′}[Ψ′,P′](g,h′) for finite adelic h, h′. The
polynomials are read on the blocks by `renameRowsCols`, which renames the rows of the variables. -/
lemma Rows.modKernelStdSpace_block {T : Space E n' s'} {a b : AutChar E} {𝔪 : Modulus E}
    (ε : n₁ ⊕ n₂ ≃ n) (b' : AutChar E) (Ψ : Matrix n₁ n' 𝔪.ResidueRing → ℂ)
    (Ψ' : Matrix n₂ n' 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n₁ × n') ℂ)
    (P' : MvPolynomial (InfinitePlace E × n₂ × n') ℂ) (g : G E s')
    (h : U (1 : Matrix n₁ n₁ (𝔸f E))) (h' : U (1 : Matrix n₂ n₂ (𝔸f E))) :
    modKernelStdSpace T a (b * b') 𝔪
        (fun x : Matrix n n' 𝔪.ResidueRing ↦
          Ψ (x.submatrix (ε ∘ Sum.inl) id) * Ψ' (x.submatrix (ε ∘ Sum.inr) id))
        (renameRowsCols (ε ∘ Sum.inl) id P * renameRowsCols (ε ∘ Sum.inr) id P') g
        (U.block ε (h, h')) =
      modKernelStdSpace T a b 𝔪 Ψ P g h * modKernelStdSpace T a b' 𝔪 Ψ' P' g h' := by
  -- The signs, the point of `stdSpace E n` and the matrix of `U.block ε (h, h')` split along `ε`.
  have h_signs : (1 : n → ℤˣ) ∘ ε = (1 : n₁ → ℤˣ) ⊕ᵥ (1 : n₂ → ℤˣ) := by
    funext i
    cases i <;> rfl
  refine modKernel_block_right T (stdSpace E n) a b 𝔪 h_signs ?_ ?_ b' Ψ Ψ' P P' g
  · rw [stdSpace_x, stdSpace_x, stdSpace_x, Units.val_one, Units.val_one, Units.val_one,
      Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]
  · refine Matrix.ext fun i j ↦ ?_
    rcases i with i | i <;> rcases j with j | j <;> refine Prod.ext (_root_.funext fun _ ↦ ?_) ?_
    all_goals first
      | exact congrFun (congrFun ((Matrix.submatrix_one_equiv (α := ℂ) ε).trans
          Matrix.fromBlocks_one.symm) _) _
      | (change (U.block ε (h, h')).val.val (ε _) (ε _) = _
         rw [U.block_val, submatrix_apply, ε.symm_apply_apply, ε.symm_apply_apply]
         rfl)

end New

end KernelLaws

end
