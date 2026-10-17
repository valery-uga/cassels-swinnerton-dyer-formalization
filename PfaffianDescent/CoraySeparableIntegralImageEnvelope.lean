import PfaffianDescent.CorayPerfectPowerRootEnvelopeFinite
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! SOURCE ONLY / UNVERIFIED. The actual image of the integral closure
in the separable subextension retains original K. Its finite type and
whole original integral-closure envelope inclusion are derived from the
actual field extension, not supplied as certificates. -/
noncomputable section
namespace PfaffianDescent.Coray
universe u v w z a

variable (K : Type u) [Field K]
variable (B : Type v) [CommRing B] [Algebra K B]
variable (F : Type w) [Field F] [Algebra B F] [Algebra K F]
variable (L : Type z) [Field L] [Algebra F L] [Algebra B L] [Algebra K L]
variable [IsScalarTower K B F] [IsScalarTower K F L]
variable [IsScalarTower B F L] [IsScalarTower K B L]

private theorem originalSeparableClosure_scalarTower :
    IsScalarTower K B (separableClosure F L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro k
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply K B L k

/-- The ACTUAL image in SAME L of integralClosure B (separableClosure F L),
viewed as an original K-subalgebra by the literal coefficient inclusion. -/
def originalSeparableIntegralImage : Subalgebra K L := by
  letI : IsScalarTower K B (separableClosure F L) :=
    originalSeparableClosure_scalarTower K B F L
  exact ((integralClosure B (separableClosure F L)).restrictScalars K).map
    ((separableClosure F L).val.restrictScalars K)

/-- The original image is finite type over SAME K: normal noetherian B
and the actual finite separable subextension derive its integral closure
finite over B, then finite type passes through original K and literal image.
Perfectness of K is not needed for this construction. -/
theorem originalSeparableIntegralImage_finiteType
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [IsFractionRing B F] [FiniteDimensional F L]
    [Algebra.FiniteType K B] :
    Algebra.FiniteType K (originalSeparableIntegralImage K B F L) := by
  letI : IsScalarTower K B (separableClosure F L) :=
    originalSeparableClosure_scalarTower K B F L
  let S := separableClosure F L
  letI : Module.Finite B (integralClosure B S) :=
    IsIntegralClosure.finite B F S (integralClosure B S)
  letI : Algebra.FiniteType K (integralClosure B S) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K B)
      (inferInstance : Algebra.FiniteType B (integralClosure B S))
  let f : S →ₐ[K] L := S.val.restrictScalars K
  let V : Subalgebra K S := (integralClosure B S).restrictScalars K
  let e : integralClosure B S ≃ₐ[K] V :=
    { toFun := fun x => ⟨(x : S), x.property⟩
      invFun := fun x => ⟨(x : S), x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      commutes' := fun k => Subtype.ext rfl }
  letI : Algebra.FiniteType K V :=
    (inferInstance : Algebra.FiniteType K (integralClosure B S)).equiv e
  change Algebra.FiniteType K (V.map f)
  exact Algebra.FiniteType.of_surjective (f.subalgebraMap V)
    (f.subalgebraMap_surjective V)

/-- SAME whole integral closure of A in L contains the actual separable
integral image, and is contained in one derived actual power-root envelope.
The exponent is derived from finite L/F through the native separable
closure/purely inseparable decomposition; it is not an input. -/
theorem originalIntegralClosure_separableImage_and_envelope
    [FiniteDimensional F L]
    (A : Type a) [CommRing A] [Algebra B A] [Algebra K A]
    [Algebra A L] [IsScalarTower K B A] [IsScalarTower K A L]
    [IsScalarTower B A L] [Algebra.IsIntegral B A]
    (p : ℕ) [ExpChar K p] :
    let U := (integralClosure A L).restrictScalars K
    let T := originalSeparableIntegralImage K B F L
    T ≤ U ∧ ∃ n : ℕ, U ≤ (powerRootEnvelope T p n).restrictScalars K := by
  letI : IsScalarTower K B (separableClosure F L) :=
    originalSeparableClosure_scalarTower K B F L
  let S := separableClosure F L
  let T := originalSeparableIntegralImage K B F L
  let U := (integralClosure A L).restrictScalars K
  have hT : T ≤ U := by
    intro x hx
    change x ∈ ((integralClosure B S).restrictScalars K).map
      (S.val.restrictScalars K) at hx
    rcases Subalgebra.mem_map.mp hx with ⟨s, hs, rfl⟩
    change IsIntegral A (s : L)
    have hsB : IsIntegral B s := hs
    have hsL : IsIntegral B (s : L) := hsB.map (S.val.restrictScalars B)
    exact hsL.tower_top
  letI : ExpChar S p :=
    expChar_of_injective_ringHom (algebraMap K S).injective p
  have hExponent : IsPurelyInseparable.HasExponent S L := inferInstance
  rcases (IsPurelyInseparable.hasExponent_iff' S L p).mp hExponent with ⟨n, hn⟩
  refine ⟨hT, n, ?_⟩
  intro x hx
  change x ^ (p ^ n) ∈ T
  have hxA : IsIntegral A x := hx
  have hxB : IsIntegral B x := isIntegral_trans (R := B) (A := A) x hxA
  have hpower : IsIntegral B (x ^ (p ^ n)) :=
    (integralClosure B L).pow_mem hxB _
  rcases hn x with ⟨s, hs⟩
  have hsValue : (s : L) = x ^ (p ^ n) := hs
  have hsL : IsIntegral B (s : L) := hsValue.symm ▸ hpower
  have hsIntegral : IsIntegral B s :=
    (isIntegral_algHom_iff (S.val.restrictScalars B) Subtype.val_injective).mp hsL
  change x ^ (p ^ n) ∈ ((integralClosure B S).restrictScalars K).map
    (S.val.restrictScalars K)
  exact Subalgebra.mem_map.mpr ⟨s, hsIntegral, hs⟩

end PfaffianDescent.Coray
