import PfaffianDescent.VoisinActualSelectedFrameFiber
import PfaffianDescent.VoisinGenericChartEvaluationInjective
import PfaffianDescent.VoisinRelativeTripleFiberIdealIso

/-! Finiteness of the actual canonical eight-point field fiber follows
from finiteness of its selected relative frame near the generic point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.canonicalIntrinsic_isFinite_of_selectedFiniteNeighborhood
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
    (w : ActualGenericEightPresentation p hp a ha i hz) :
    let Q := cubicConfigurationBase p hp 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let F := O.residueField (i (genericPoint U))
    let bCan := quadraticOrderedLiftFunctionFieldHom p hp
      (i (genericPoint U)) hz
    let bSel : K →+* F :=
      (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom
    let s := openImmersion_genericResidueLift i
    let f : Γ(U, ⊤) →+* F :=
      (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
    let x := pulledEightLinearChartCoordinates
      (equationIdeal p hp) w.zc w.hzc U w.t
    let β := affineFunctionHom (i ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)
    letI : Algebra Q.functionField F := bCan.toAlgebra
    letI : Algebra K F := bSel.toAlgebra
    ∀ (m : Fin 8 ↪ Monomials (Fin 4) 2)
      (hdet : quadraticMinorDet m x ≠ 0),
      let S := Localization.Away (quadraticMinorDet m x)
      letI : IsDomain S := Localization.Away.isDomain hdet
      let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
      let pS := p.map βS
      let hpS := hp.map βS
      let q₀ := quadraticSelectedOpenPolynomial m x 0
      let q₁ := quadraticSelectedOpenPolynomial m x 1
      let hq₀ := quadraticSelectedOpenPolynomial_isHomogeneous m x 0
      let hq₁ := quadraticSelectedOpenPolynomial_isHomogeneous m x 1
      ∀ (V : (Spec (.of S)).Opens),
        genericPoint (Spec (.of S)) ∈ V →
        IsFinite ((relativeTripleIntersectionToBase
          pS q₀ q₁ hpS hq₀ hq₁) ∣_ V) →
        IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
          (p.map bSel) (hp.map bSel)
          (w.canonicalVectors p hp a ha i hz))) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let F := O.residueField (i (genericPoint U))
  let bCan := quadraticOrderedLiftFunctionFieldHom p hp
    (i (genericPoint U)) hz
  let bSel : K →+* F :=
    (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)).hom
  let s := openImmersion_genericResidueLift i
  let f : Γ(U, ⊤) →+* F :=
    (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
  let x := pulledEightLinearChartCoordinates
    (equationIdeal p hp) w.zc w.hzc U w.t
  let β := affineFunctionHom (i ≫
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).hom)
  letI : Algebra Q.functionField F := bCan.toAlgebra
  letI : Algebra K F := bSel.toAlgebra
  intro m hdet
  have hm : IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
      (fun k j => f (x k j))).det :=
    openImmersion_genericQuadraticMinor_isUnit i m x hdet
  let S := Localization.Away (quadraticMinorDet m x)
  letI : IsDomain S := Localization.Away.isDomain hdet
  let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
  let pS := p.map βS
  let hpS := hp.map βS
  let q₀ := quadraticSelectedOpenPolynomial m x 0
  let q₁ := quadraticSelectedOpenPolynomial m x 1
  let hq₀ := quadraticSelectedOpenPolynomial_isHomogeneous m x 0
  let hq₁ := quadraticSelectedOpenPolynomial_isHomogeneous m x 1
  intro V hη hfin
  letI : IsFinite ((relativeTripleIntersectionToBase
      pS q₀ q₁ hpS hq₀ hq₁) ∣_ V) := hfin
  let g := quadraticMinorSelectedPointLift m x f hm
  have hg : Function.Injective g :=
    openImmersion_genericSelectedPointLift_injective i m x hm
  let I := intrinsicEightPointTripleHomogeneousIdeal
    (p.map bSel) (hp.map bSel)
    (w.canonicalVectors p hp a ha i hz)
  have hI : I = relativeTripleIntersectionHomogeneousIdeal
      (pS.map g) (q₀.map g) (q₁.map g)
      (hpS.map g) (hq₀.map g) (hq₁.map g) :=
    w.intrinsicIdeal_eq_selectedFrameFiber p hp a ha i hz m hm
  exact intrinsicIdeal_isFinite_at_injectiveFieldPoint_of_finiteNeighborhood
    pS q₀ q₁ hpS hq₀ hq₁ V hη g hg I hI

end PfaffianDescent
