import PfaffianDescent.CoraySeparableIntegralImageEnvelope

/-! SOURCE ONLY / UNVERIFIED. Construct the literal B coefficient map
into the actual separable integral image and derive it finite. The whole
original integral closure obtains its literal T-action, injects ordinarily
T-linearly into the actual power-root envelope, and is finite over A by
actual module towers. No desired normalization finiteness is a premise. -/
noncomputable section
namespace PfaffianDescent.Coray
universe u v w z a
variable (K : Type u) [Field K]
variable (B : Type v) [CommRing B] [Algebra K B]
variable (F : Type w) [Field F] [Algebra B F] [Algebra K F]
variable (L : Type z) [Field L] [Algebra F L] [Algebra B L] [Algebra K L]
variable [IsScalarTower K B F] [IsScalarTower K F L]
variable [IsScalarTower B F L] [IsScalarTower K B L]

private theorem separableIntegralModule_originalTower :
    IsScalarTower K B (separableClosure F L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro k
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply K B L k

/-- The literal original B->L map factors through the ACTUAL separable
integral image. This map keeps the original K coefficient action. -/
def originalSeparableIntegralImage_baseMap :
    B →ₐ[K] originalSeparableIntegralImage K B F L := by
  letI : IsScalarTower K B (separableClosure F L) :=
    separableIntegralModule_originalTower K B F L
  let S := separableClosure F L
  refine (IsScalarTower.toAlgHom K B L).codRestrict
    (originalSeparableIntegralImage K B F L) ?_
  intro b
  change algebraMap B L b ∈ ((integralClosure B S).restrictScalars K).map
    (S.val.restrictScalars K)
  exact Subalgebra.mem_map.mpr
    ⟨algebraMap B S b, isIntegral_algebraMap, rfl⟩

/-- The ACTUAL B coefficient map into embedded T is finite, derived via
finite separable integral closure and an actual B-linear surjection to its
literal image. No finite-T map/generators premise. -/
theorem originalSeparableIntegralImage_baseMap_finite
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [IsFractionRing B F] [FiniteDimensional F L] :
    (originalSeparableIntegralImage_baseMap K B F L).toRingHom.Finite := by
  letI : IsScalarTower K B (separableClosure F L) :=
    separableIntegralModule_originalTower K B F L
  let S := separableClosure F L
  let T := originalSeparableIntegralImage K B F L
  let b := originalSeparableIntegralImage_baseMap K B F L
  letI : Algebra B T := b.toRingHom.toAlgebra
  letI : Module.Finite B (integralClosure B S) :=
    IsIntegralClosure.finite B F S (integralClosure B S)
  let g : integralClosure B S →ₐ[B] T :=
    { toFun := fun x => ⟨(x : S), Subalgebra.mem_map.mpr ⟨(x : S), x.property, rfl⟩⟩
      map_zero' := Subtype.ext rfl
      map_one' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      commutes' := by
        intro c
        apply Subtype.ext
        exact (S.val.restrictScalars B).commutes c }
  have hg : Function.Surjective g := by
    rintro ⟨t, ht⟩
    change t ∈ ((integralClosure B S).restrictScalars K).map
      (S.val.restrictScalars K) at ht
    rcases Subalgebra.mem_map.mp ht with ⟨s, hs, hst⟩
    exact ⟨⟨s, hs⟩, Subtype.ext hst⟩
  change Module.Finite B T
  exact Module.Finite.of_surjective g.toLinearMap hg

/-- Original perfect K, actual normal finite-type base B with fraction
field F, and actual finite L/F derive finiteness of WHOLE integralClosure
A L over A. Integral B->A is an actual tower hypothesis, not a supplied
normalization/separability/exponent certificate. -/
theorem perfectField_integralClosure_finite_of_finite_normal_base
    [PerfectField K]
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [IsFractionRing B F] [FiniteDimensional F L] [Algebra.FiniteType K B]
    (A : Type a) [CommRing A] [Algebra B A] [Algebra K A]
    [Algebra A L] [IsScalarTower K B A] [IsScalarTower K A L]
    [IsScalarTower B A L] [Algebra.IsIntegral B A] :
    Module.Finite A (integralClosure A L) := by
  let T := originalSeparableIntegralImage K B F L
  let b := originalSeparableIntegralImage_baseMap K B F L
  letI : Algebra B T := b.toRingHom.toAlgebra
  letI : Module.Finite B T := originalSeparableIntegralImage_baseMap_finite K B F L
  letI : Algebra.FiniteType K T := originalSeparableIntegralImage_finiteType K B F L
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  obtain ⟨p, hp⟩ := ExpChar.exists K
  letI : ExpChar K p := hp
  obtain ⟨hTU, n, hUE⟩ :=
    originalIntegralClosure_separableImage_and_envelope K B F L A p
  let i : T →ₐ[K] integralClosure A L :=
    { toFun := fun t => ⟨(t : L), hTU t.property⟩
      map_zero' := Subtype.ext rfl
      map_one' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      commutes' := fun k => Subtype.ext rfl }
  letI : Algebra T (integralClosure A L) := i.toRingHom.toAlgebra
  letI : IsScalarTower B T (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq fun c => Subtype.ext rfl
  letI : Module.Finite T (powerRootEnvelope T p n) :=
    perfectField_finiteType_powerRootEnvelope_finite T p n
  letI : IsNoetherian T (powerRootEnvelope T p n) := inferInstance
  let f : integralClosure A L →ₗ[T] powerRootEnvelope T p n :=
    { toFun := fun x => ⟨(x : L), hUE x.property⟩
      map_add' := fun x y => Subtype.ext rfl
      map_smul' := fun t x => Subtype.ext rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : powerRootEnvelope T p n => (z : L)) h
  letI : Module.Finite T (integralClosure A L) := Module.Finite.of_injective f hf
  letI : Module.Finite B (integralClosure A L) := Module.Finite.trans T (integralClosure A L)
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)

end PfaffianDescent.Coray
