import PfaffianDescent.CorayEntireModelIncidenceCycle
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Unramified.Field

/-! Source only: the literal entire incidence scheme is reduced in
characteristic zero. No replacement by its reduction or chosen summand. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite formally unramified scheme over a field is reduced, using its
actual global-sections algebra and actual affine isomorphism. -/
theorem finiteFormallyUnramifiedScheme_isReduced
    {F : Type u} [Field F] {X : Scheme.{u}}
    (pi : X ⟶ Spec (.of F)) [IsFinite pi] [FormallyUnramified pi] : IsReduced X := by
  letI : IsAffine X := isAffine_of_isAffineHom pi
  let phi := Spec.preimage (X.isoSpec.inv ≫ pi)
  letI : Algebra F Γ(X, ⊤) := phi.hom.toAlgebra
  have hspec : FormallyUnramified (Spec.map phi) := by
    rw [Spec.map_preimage]
    exact MorphismProperty.comp_mem (@FormallyUnramified.{u})
      X.isoSpec.inv pi inferInstance inferInstance
  have hring : phi.hom.FormallyUnramified :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified.{u})).mp hspec
  letI : Algebra.FormallyUnramified F Γ(X, ⊤) := hring
  have hfinite : IsFinite (Spec.map phi) := by
    rw [Spec.map_preimage]
    infer_instance
  letI : Module.Finite F Γ(X, ⊤) := (IsFinite.SpecMap_iff phi).mp hfinite
  letI : _root_.IsReduced Γ(X, ⊤) := Algebra.FormallyUnramified.isReduced_of_field F Γ(X, ⊤)
  exact isReduced_of_isOpenImmersion X.isoSpec.hom

variable {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M] [Module.Finite K M]

/-- The actual component-to-original map is formally unramified: its
coefficient map is a base change of the separable finite field extension,
and its component quotient immersion is a monomorphism. No GI or smoothness
of D, reduced fibre or separability certificate is supplied. -/
theorem coefficientComponentToOriginal_formallyUnramified
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal) :
    FormallyUnramified (coefficientComponentToOriginal I D hID) := by
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  let g := projectiveCoefficientMap (algebraMap K M) I IM rfl
  let j := schemeQuotientMap IM D hID
  letI : Algebra.FormallyUnramified K M := Algebra.FormallyUnramified.of_isSeparable K M
  letI : FormallyUnramified b :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified.{u})).mpr
      (RingHom.formallyUnramified_algebraMap.mpr inferInstance)
  letI : FormallyUnramified g := MorphismProperty.of_isPullback (P := @FormallyUnramified.{u})
    (isPullback_projectiveCoefficientMap (algebraMap K M) I IM rfl).flip inferInstance
  letI : IsClosedImmersion j := schemeQuotientMap_closedImmersion IM D hID
  change FormallyUnramified (j ≫ g)
  exact MorphismProperty.comp_mem (@FormallyUnramified.{u})
    j g inferInstance inferInstance

/-- The SAME actual entire incidence Z_D is reduced in characteristic zero.
The actual first projection is finite and formally unramified over kappa(P),
so no separate reducedness premise or change of scheme is needed. -/
theorem originalPointModelIncidence_literalScheme_isReduced
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) :
    IsReduced (originalPointModelIncidenceScheme I D hID P) := by
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let c := pullback.fst ep f
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hID).1
  letI : FormallyUnramified f := coefficientComponentToOriginal_formallyUnramified I D hID
  letI : IsFinite c := by dsimp only [c]; infer_instance
  letI : FormallyUnramified c :=
    MorphismProperty.pullback_fst (P := @FormallyUnramified.{u}) ep f inferInstance
  exact finiteFormallyUnramifiedScheme_isReduced c

end PfaffianDescent.Coray
