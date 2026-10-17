import PfaffianDescent.CorayBoundedOriginalEvaluationRationalMap
import PfaffianDescent.CorayOriginalFunctionFieldTensorDomain
import PfaffianDescent.CorayProjectiveEvaluationCoefficientNaturality
import PfaffianDescent.CorayProjectiveEvaluationLinearForm
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Source-only / unverified. Canonical tensor coordinates of the SAME
original basis remain independent over every coefficient field. Genuine
geometric integrality makes the tensor ring a domain. Its actual fraction
field supplies an explicit projective evaluation point with the SAME
original point recovered by the coefficient projection. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct AlgebraicGeometry PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Scalar multiplication inherited by the actual fraction localization,
with its canonical coefficient hom stated explicitly. -/
private theorem nativeFractionRing_smul {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (c : R) (z : FractionRing A) :
    c • z = algebraMap A (FractionRing A) (algebraMap R A c) * z := by
  exact Algebra.smul_def c z

/-- The canonical fraction inclusion is linear for the existing
source algebra action and the localization's inherited action. -/
private def nativeFractionRingLinearMap {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] : A →ₗ[R] FractionRing A where
  toFun := algebraMap A (FractionRing A)
  map_add' := map_add _
  map_smul' c z := by
    rw [Algebra.smul_def, map_mul, nativeFractionRing_smul, RingHom.id_apply]

variable {K L B : Type u} [Field K] [CommRing L] [Algebra K L]
  [Field B] [Algebra K B]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
variable {m : ℕ}
  (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
local notation "F" => AlgebraicGeometry.Scheme.functionField (hypersurface p hp)
local notation "φ" => schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)

include hp0 in
/-- A bounded ordinary carrier/action transport before tensoring. The
identity equivalence retains the independently defined original-pi action. -/
private theorem cubicThroughPointBasisNativeCoordinates_linearIndependent :
    letI : Algebra K F := RingHom.toAlgebra φ
    LinearIndependent K (fun i =>
      (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i)) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  let E := schemeFunctionFieldOriginalRingLinearEquiv (hypersurfaceToBase p hp)
  have hli := evaluatedBasis_linearIndependent
    (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
    (B := SchemeFunctionFieldOver (hypersurfaceToBase p hp)) (ι := Fin m)
    b (cubicThroughPointGenericLinearEvaluation p hp n y hpy j)
    (cubicThroughPointGenericLinearEvaluation_injective p hp n y hpy j hp0)
  have hE := hli.map' E.toLinearMap (LinearMap.ker_eq_bot.mpr E.injective)
  exact hE

/-- Exact canonical scalar extension of the actual original basis values. -/
def cubicThroughPointBasisTensorCoordinates :
    letI : Algebra K F := RingHom.toAlgebra φ
    Fin m → B ⊗[K] F := by
  letI : Algebra K F := RingHom.toAlgebra φ
  exact fun i => (1 : B) ⊗ₜ[K]
    (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i)

include hp0 in
/-- Flat field extension preserves the actual original evaluation's
basis independence. The identity carrier equivalence proves the SAME
original-pi scalar action before tensoring. -/
theorem cubicThroughPointBasisTensorCoordinates_linearIndependent :
    letI : Algebra K F := RingHom.toAlgebra φ
    LinearIndependent B (cubicThroughPointBasisTensorCoordinates (B := B) p hp n y hpy j b) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  change LinearIndependent B (fun i => (1 : B) ⊗ₜ[K]
    (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i))
  exact Module.Flat.linearIndependent_one_tmul
    (cubicThroughPointBasisNativeCoordinates_linearIndependent p hp hp0 n y hpy j b)

/-- Exact canonical inclusion of the original function field into the
fraction field of its genuine original-K tensor domain. -/
def cubicOriginalFunctionFieldToTensorFraction :
    letI : Algebra K F := RingHom.toAlgebra φ
    F →+* FractionRing (B ⊗[K] F) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  exact (algebraMap (B ⊗[K] F) (FractionRing (B ⊗[K] F))).comp
    (Algebra.TensorProduct.includeRight : F →ₐ[K] B ⊗[K] F).toRingHom

/-- The new coefficient hom is the canonical tensor coefficient
inclusion followed by the canonical fraction-ring map. -/
def cubicTensorFractionCoefficientHom :
    letI : Algebra K F := RingHom.toAlgebra φ
    B →+* FractionRing (B ⊗[K] F) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  exact (algebraMap (B ⊗[K] F) (FractionRing (B ⊗[K] F))).comp
    (algebraMap B (B ⊗[K] F))

/-- The actual original coefficients agree in the canonical tensor ring;
this supplies the coefficient square internally, without a certificate. -/
theorem cubicTensorFractionCoefficientHom_original :
    letI : Algebra K F := RingHom.toAlgebra φ
    (cubicTensorFractionCoefficientHom (B := B) p hp).comp (algebraMap K B) =
      (cubicOriginalFunctionFieldToTensorFraction (B := B) p hp).comp φ := by
  letI : Algebra K F := RingHom.toAlgebra φ
  ext c
  change algebraMap (B ⊗[K] F) (FractionRing (B ⊗[K] F))
    (algebraMap K B c ⊗ₜ[K] (1 : F)) =
      algebraMap (B ⊗[K] F) (FractionRing (B ⊗[K] F))
        ((1 : B) ⊗ₜ[K] φ c)
  have h := Algebra.TensorProduct.tmul_one_eq_one_tmul (R := K) (A := B) (B := F) c
  exact congrArg (algebraMap (B ⊗[K] F) (FractionRing (B ⊗[K] F))) h

/-- The actual coefficient hom describes the existing fraction-field
scalar action; this is an equality of values, not replacement of an action. -/
private theorem cubicTensorFractionCoefficientHom_smul (c : B) :
    letI : Algebra K F := RingHom.toAlgebra φ
    ∀ z : FractionRing (B ⊗[K] F),
      c • z = cubicTensorFractionCoefficientHom (B := B) p hp c * z := by
  letI : Algebra K F := RingHom.toAlgebra φ
  intro z
  exact nativeFractionRing_smul c z

/-- Canonical tensor coordinates viewed in the actual tensor fraction field. -/
def cubicThroughPointBasisTensorFractionCoordinates :
    letI : Algebra K F := RingHom.toAlgebra φ
    Fin m → FractionRing (B ⊗[K] F) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  exact fun i => algebraMap (B ⊗[K] F) (FractionRing (B ⊗[K] F))
    (cubicThroughPointBasisTensorCoordinates (B := B) p hp n y hpy j b i)

include hp0 in
/-- Localization of the genuine tensor domain remains injective, so no
new B-linear relation appears among the SAME actual basis coordinates.
The B action is exactly the canonical coefficient inclusion above. -/
theorem cubicThroughPointBasisTensorFractionCoordinates_linearIndependent :
    letI : Algebra K F := RingHom.toAlgebra φ
    letI : Algebra B (FractionRing (B ⊗[K] F)) :=
      (cubicTensorFractionCoefficientHom (B := B) p hp).toAlgebra
    LinearIndependent B
      (cubicThroughPointBasisTensorFractionCoordinates (B := B) p hp n y hpy j b) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  let T := B ⊗[K] F
  let G := FractionRing T
  letI : IsDomain T := cubicOriginalFunctionField_tensor_isDomain (B := B) p hp hp0
  letI : Algebra B G := (cubicTensorFractionCoefficientHom (B := B) p hp).toAlgebra
  let ℓ : T →ₗ[B] G := nativeFractionRingLinearMap (R := B) (A := T)
  have hℓ : Function.Injective ℓ := IsFractionRing.injective T G
  have hli := cubicThroughPointBasisTensorCoordinates_linearIndependent (B := B)
    p hp hp0 n y hpy j b
  exact hli.map' ℓ (LinearMap.ker_eq_bot.mpr hℓ)

include hp0 in
theorem cubicThroughPointBasisTensorFractionCoordinates_ne_zero (a : Fin m) :
    letI : Algebra K F := RingHom.toAlgebra φ
    cubicThroughPointBasisTensorFractionCoordinates (B := B) p hp n y hpy j b a ≠ 0 := by
  letI : Algebra K F := RingHom.toAlgebra φ
  letI : Algebra B (FractionRing (B ⊗[K] F)) :=
    (cubicTensorFractionCoefficientHom (B := B) p hp).toAlgebra
  exact (cubicThroughPointBasisTensorFractionCoordinates_linearIndependent (B := B)
    p hp hp0 n y hpy j b).ne_zero a

include hp0 in
/-- The exact tensor coordinates define a specified projective point
over B. Its denominator is proved nonzero, and the field property comes
from the actual cubic's geometric integrality. -/
def cubicThroughPointBasisTensorFractionPoint (a : Fin m) :
    letI : Algebra K F := RingHom.toAlgebra φ
    Spec (.of (FractionRing (B ⊗[K] F))) ⟶
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) B)) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  letI : IsDomain (B ⊗[K] F) := cubicOriginalFunctionField_tensor_isDomain (B := B) p hp hp0
  exact projectiveEvaluationPoint (cubicTensorFractionCoefficientHom (B := B) p hp)
    (cubicThroughPointBasisTensorFractionCoordinates (B := B) p hp n y hpy j b) a
    (cubicThroughPointBasisTensorFractionCoordinates_ne_zero (B := B) p hp hp0 n y hpy j b a)

/-- The SAME original generic point is recovered by projecting the
specified B-point through the ACTUAL projective coefficient morphism.
This is not merely existence of some point over B. -/
theorem cubicThroughPointBasisTensorFractionPoint_toOriginal (a : Fin m) :
    letI : Algebra K F := RingHom.toAlgebra φ
    cubicThroughPointBasisTensorFractionPoint (B := B) p hp hp0 n y hpy j b a ≫
      projectiveEvaluationCoefficientMap (σ := Fin m) (algebraMap K B) =
        Spec.map (CommRingCat.ofHom (cubicOriginalFunctionFieldToTensorFraction (B := B) p hp)) ≫
          cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a := by
  letI : Algebra K F := RingHom.toAlgebra φ
  letI : IsDomain (B ⊗[K] F) := cubicOriginalFunctionField_tensor_isDomain (B := B) p hp hp0
  exact projectiveEvaluationPoint_coefficient_naturality (algebraMap K B) φ
    (cubicTensorFractionCoefficientHom (B := B) p hp)
    (cubicOriginalFunctionFieldToTensorFraction (B := B) p hp)
    (cubicTensorFractionCoefficientHom_original (B := B) p hp)
    (fun i => (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i)) a
    (cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a)
    (cubicThroughPointBasisTensorFractionCoordinates_ne_zero (B := B) p hp hp0 n y hpy j b a)

/-- The specified tensor-fraction point belongs to the ACTUAL Cartesian
base change of the original evaluation map, by the proved original-point
identity, not by an assumed image-membership certificate. -/
def cubicThroughPointBasisTensorFractionPointToEvaluationPullback (a : Fin m) :
    letI : Algebra K F := RingHom.toAlgebra φ
    Spec (.of (FractionRing (B ⊗[K] F))) ⟶
      CategoryTheory.Limits.pullback
        (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a)
        (projectiveEvaluationCoefficientMap (σ := Fin m) (algebraMap K B)) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  exact CategoryTheory.Limits.pullback.lift
    (Spec.map (CommRingCat.ofHom (cubicOriginalFunctionFieldToTensorFraction (B := B) p hp)))
    (cubicThroughPointBasisTensorFractionPoint (B := B) p hp hp0 n y hpy j b a)
    (cubicThroughPointBasisTensorFractionPoint_toOriginal (B := B) p hp hp0 n y hpy j b a).symm

/-- The exact B-point factors through the ACTUAL scheme-theoretic image
of the ACTUAL coefficient-changed original map. Together with the separate
flat-image kernel identity, this links its coordinate test to the original
image's coefficient change. -/
theorem cubicThroughPointBasisTensorFractionPoint_factors_evaluationImage (a : Fin m) :
    letI : Algebra K F := RingHom.toAlgebra φ
    let qB := CategoryTheory.Limits.pullback.snd
      (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a)
      (projectiveEvaluationCoefficientMap (σ := Fin m) (algebraMap K B))
    (cubicThroughPointBasisTensorFractionPointToEvaluationPullback (B := B)
      p hp hp0 n y hpy j b a ≫ qB.toImage) ≫ qB.imageι =
        cubicThroughPointBasisTensorFractionPoint (B := B) p hp hp0 n y hpy j b a := by
  letI : Algebra K F := RingHom.toAlgebra φ
  dsimp only
  rw [Category.assoc, Scheme.Hom.toImage_imageι]
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

/-- No nonzero B-hyperplane equation vanishes at the actual normalized
B-point of the actual changed image. B/K is arbitrary, so this includes
an algebraic closure without a characteristic-zero restriction. -/
theorem cubicThroughPointBasisTensorFractionPoint_linearForm_zero_iff
    (a : Fin m) (c : Fin m → B) :
    letI : Algebra K F := RingHom.toAlgebra φ
    letI : IsDomain (B ⊗[K] F) := cubicOriginalFunctionField_tensor_isDomain (B := B) p hp hp0
    projectiveEvaluationChartMap
      (cubicTensorFractionCoefficientHom (B := B) p hp)
      (cubicThroughPointBasisTensorFractionCoordinates (B := B) p hp n y hpy j b) a
      (cubicThroughPointBasisTensorFractionCoordinates_ne_zero (B := B) p hp hp0 n y hpy j b a)
      (projectiveChartLinearForm a c) = 0 ↔ c = 0 := by
  letI : Algebra K F := RingHom.toAlgebra φ
  letI : IsDomain (B ⊗[K] F) := cubicOriginalFunctionField_tensor_isDomain (B := B) p hp hp0
  letI : Algebra B (FractionRing (B ⊗[K] F)) :=
    (cubicTensorFractionCoefficientHom (B := B) p hp).toAlgebra
  rw [projectiveEvaluationChartMap_linearForm_zero_iff]
  have hsum : (∑ i, cubicTensorFractionCoefficientHom (B := B) p hp (c i) *
      cubicThroughPointBasisTensorFractionCoordinates (B := B) p hp n y hpy j b i) =
      ∑ i, c i •
        cubicThroughPointBasisTensorFractionCoordinates (B := B) p hp n y hpy j b i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (cubicTensorFractionCoefficientHom_smul (B := B) p hp (c i)
      (cubicThroughPointBasisTensorFractionCoordinates (B := B) p hp n y hpy j b i)).symm
  rw [hsum]
  constructor
  · intro h
    exact funext (Fintype.linearIndependent_iff.mp
      (cubicThroughPointBasisTensorFractionCoordinates_linearIndependent (B := B)
        p hp hp0 n y hpy j b) c h)
  · rintro rfl
    rw [← hsum]
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

end PfaffianDescent.Coray
end
