import PfaffianDescent.ProjectivePositiveTwist
import PfaffianDescent.VoisinProjectiveSpaceCech
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import AllCharacteristics.HomogeneousProjective
import Mathlib.RingTheory.Length

/-! Source only. A separate degree-one chart is chosen at each ACTUAL point.
No single open is required to contain all points; no Infinite instance occurs.
The map is the native stalk of actual homogeneous multiplication. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} {σ : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every literal positive-twist native stalk is the whole local ring as
a module over itself. The frame is constructed from an internally chosen
degree-one section outside that point's homogeneous prime. -/
def quotientPositiveTwist_nativeStalkUnitIso_anyField
    (I : HomogeneousIdeal (homogeneousSubmodule σ K)) (m : ℕ) (x : scheme I) :
    (schemeModuleStalkModuleFunctor (scheme I) x).obj
        (positiveSheafOfModules (grading I) m) ≅
      ModuleCat.of ((scheme I).presheaf.stalk x) ((scheme I).presheaf.stalk x) := by
  let 𝓑 := grading I
  let F := schemeModuleStalkModuleFunctor (scheme I) x
  letI : (positivePointIdeal 𝓑 x).IsPrime := ProjectiveSpectrum.isPrime x
  have hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne
      (homogeneousSubmodule σ K) 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  have hchart := exists_degreeOne_mem_primeCompl_of_irrelevant_le_span 𝓑 hspan x
  let ell : 𝓑 1 := Classical.choose hchart
  have hell : (ell : CoordinateRing I) ∈ (positivePointIdeal 𝓑 x).primeCompl :=
    Classical.choose_spec hchart
  let s : 𝓑 m := degreeOnePower 𝓑 ell m
  have hs : (s : CoordinateRing I) ∈ (positivePointIdeal 𝓑 x).primeCompl := by
    change (ell : CoordinateRing I) ^ m ∈ (positivePointIdeal 𝓑 x).primeCompl
    exact (positivePointIdeal 𝓑 x).primeCompl.pow_mem hell m
  let a := positiveMulHomogeneous 𝓑 s 0
  have hbij : Function.Bijective (F.map a).hom := by
    change Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (positiveMulHomogeneousPresheaf 𝓑 s 0))
    exact positiveMulHomogeneous_stalkMap_bijective_of_mem_primeCompl
      𝓑 s 0 x hs ell hell
  letI : IsIso (F.map a) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  let e0 : F.obj (show (scheme I).Modules from
      SheafOfModules.unit (scheme I).ringCatSheaf) ≅
      F.obj (positiveSheafOfModules 𝓑 0) :=
    F.mapIso (unitIsoZeroTwist 𝓑 ≪≫ (positiveZeroTwistIso 𝓑).symm)
  let em : F.obj (positiveSheafOfModules 𝓑 (0 + m)) ≅
      F.obj (positiveSheafOfModules 𝓑 m) :=
    F.mapIso (eqToIso (congrArg (positiveSheafOfModules 𝓑) (Nat.zero_add m)))
  exact em.symm ≪≫ (asIso (F.map a)).symm ≪≫ e0.symm ≪≫
    schemeModuleUnitStalkIso (scheme I) x

/-- Native composition length of the ACTUAL positive twist equals the
entire structure-stalk length, including every nilpotent layer. -/
theorem quotientPositiveTwist_nativeStalk_length_anyField
    (I : HomogeneousIdeal (homogeneousSubmodule σ K)) (m : ℕ) (x : scheme I) :
    Module.length ((scheme I).presheaf.stalk x)
        ((schemeModuleStalkModuleFunctor (scheme I) x).obj
          (positiveSheafOfModules (grading I) m)) =
      Module.length ((scheme I).presheaf.stalk x) ((scheme I).presheaf.stalk x) :=
  (quotientPositiveTwist_nativeStalkUnitIso_anyField I m x).toLinearEquiv.length_eq

end PfaffianDescent.Coray
