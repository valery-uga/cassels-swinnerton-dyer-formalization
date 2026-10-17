import PfaffianDescent.VoisinActualSelectedFrameFiber
import PfaffianDescent.VoisinRelativeTripleFiberIdealIso

/-! The canonical generic eight-point scheme is the actual field fiber
of the selected relative triple-intersection family. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def ActualGenericEightPresentation.selectedFrameFiber_iso_pullback
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
      (hm : IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
        (fun k j => f (x k j))).det),
      let S := Localization.Away (quadraticMinorDet m x)
      let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
      let pS := p.map βS
      let hpS := hp.map βS
      let q₀ := quadraticSelectedOpenPolynomial m x 0
      let q₁ := quadraticSelectedOpenPolynomial m x 1
      let hq₀ := quadraticSelectedOpenPolynomial_isHomogeneous m x 0
      let hq₁ := quadraticSelectedOpenPolynomial_isHomogeneous m x 1
      let g := quadraticMinorSelectedPointLift m x f hm
      scheme (intrinsicEightPointTripleHomogeneousIdeal
        (p.map bSel) (hp.map bSel)
        (w.canonicalVectors p hp a ha i hz)) ≅
      pullback (relativeTripleIntersectionToBase
        pS q₀ q₁ hpS hq₀ hq₁)
        (Spec.map (CommRingCat.ofHom g)) := by
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
  intro m hm
  let S := Localization.Away (quadraticMinorDet m x)
  let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
  let pS := p.map βS
  let hpS := hp.map βS
  let q₀ := quadraticSelectedOpenPolynomial m x 0
  let q₁ := quadraticSelectedOpenPolynomial m x 1
  let hq₀ := quadraticSelectedOpenPolynomial_isHomogeneous m x 0
  let hq₁ := quadraticSelectedOpenPolynomial_isHomogeneous m x 1
  let g := quadraticMinorSelectedPointLift m x f hm
  let I := intrinsicEightPointTripleHomogeneousIdeal
    (p.map bSel) (hp.map bSel)
    (w.canonicalVectors p hp a ha i hz)
  have hI : I = relativeTripleIntersectionHomogeneousIdeal
      (pS.map g) (q₀.map g) (q₁.map g)
      (hpS.map g) (hq₀.map g) (hq₁.map g) :=
    w.intrinsicIdeal_eq_selectedFrameFiber p hp a ha i hz m hm
  exact intrinsicIdeal_scheme_iso_relativeTripleBaseChange
    g pS q₀ q₁ hpS hq₀ hq₁ I hI

end PfaffianDescent
