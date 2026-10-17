import PfaffianDescent.ActualAffineDifferentialBasicOpenNaturality
import PfaffianDescent.ModulePresheafHomFromActualBasis
import PfaffianDescent.SchemeRelativeDifferentialsSheaf

/- SOURCE ONLY / UNVERIFIED. Canonical affine comparison, constructed
internally on the actual principal-open basis and then genuinely glued.
Its IsIso proof is a further leaf, not supplied as an assumption here. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- The natural localization comparison on the actual principal-open basis. -/
def actualAffineDifferentialBasicOpenComparison :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
      (schemeRelativeDifferentialsPresheaf
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))).presheaf ⟶
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
      (affineKaehlerModuleSheaf (k := k) (R := R)).presheaf where
  app f := AddCommGrpCat.ofHom
    (actualAffineDifferentialPresheafBasicOpenEquiv (k := k) f.unop).toAddEquiv.toAddMonoidHom
  naturality {f h} i := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact congrArg (fun a => a x)
      (actualAffineDifferentialBasicOpen_naturality
        (k := k) f.unop h.unop i.unop.hom.le)

/-- A genuine module-presheaf map on ALL actual affine opens, extended from
canonical Kähler localization comparisons. No comparison square is assumed. -/
def actualAffineDifferentialPresheafToTilde :
    schemeRelativeDifferentialsPresheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶
        (affineKaehlerModuleSheaf (k := k) (R := R)).val :=
  modulePresheafHomFromActualBasis _ _
    (PrimeSpectrum.basicOpen (R := R)) PrimeSpectrum.isBasis_basic_opens
    actualAffineDifferentialBasicOpenComparison
    (fun i r x =>
      (actualAffineDifferentialPresheafBasicOpenEquiv (k := k) i).map_smul r x)

/-- Sheafification gives the actual scheme differential sheaf's canonical
comparison to the actual affine Kähler module sheaf. -/
def actualAffineDifferentialSheafToTilde :
    schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶
        affineKaehlerModuleSheaf (k := k) (R := R) := by
  let a := actualAffineDifferentialPresheafToTilde (k := k) (R := R)
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).homEquiv _ _).symm a

end PfaffianDescent
