import PfaffianDescent.ActualPositiveTwistNativeChartUnitIso
import PfaffianDescent.ActualCubicPositiveTwoDifferentialPointFiber
import PfaffianDescent.ActualCubicNativeChartDifferentialSheafIso
import PfaffianDescent.ActualAffineDifferentialGenuineToTildeIso

/- SOURCE ONLY / UNVERIFIED. GENUINE global Omega(2) on the SAME original
cubic is the actual Kaehler tilde module on its native standard chart. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The exact tensor/chart composition, built while all module objects
and three constituent Isos are abstract. -/
private def actualModuleTensorChartCompositeIso
    {Y : Scheme.{u}} {M T A N : Y.Modules}
    (eTensor : A ≅ schemeModuleTensor M T) (eM : M ≅ N)
    (eT : T ≅ SheafOfModules.unit Y.ringCatSheaf) : A ≅ N :=
  eTensor ≪≫ schemeModuleTensorMapIso eM eT ≪≫ schemeModuleTensorUnitRightIso N

/-- Compute the factory hom before specializing the chart or differential objects. -/
private lemma actualModuleTensorChartCompositeIso_hom
    {Y : Scheme.{u}} {M T A N : Y.Modules}
    (eTensor : A ≅ schemeModuleTensor M T) (eM : M ≅ N)
    (eT : T ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (actualModuleTensorChartCompositeIso eTensor eM eT).hom =
      eTensor.hom ≫ schemeModuleTensorMap eM.hom eT.hom ≫
        (schemeModuleTensorUnitRightIso N).hom := by
  rfl

/-- A composite Iso together with its hom computation, derived by the factory.
The equation is a proved result stored internally, not an input certificate. -/
private structure ActualModuleTensorChartData
    {Y : Scheme.{u}} {M T A N : Y.Modules}
    (eTensor : A ≅ schemeModuleTensor M T) (eM : M ≅ N)
    (eT : T ≅ SheafOfModules.unit Y.ringCatSheaf) where
  iso : A ≅ N
  hom_eq : iso.hom = eTensor.hom ≫ schemeModuleTensorMap eM.hom eT.hom ≫
    (schemeModuleTensorUnitRightIso N).hom
  iso_eq : iso = actualModuleTensorChartCompositeIso eTensor eM eT

private def actualModuleTensorChartDataOfIsos
    {Y : Scheme.{u}} {M T A N : Y.Modules}
    (eTensor : A ≅ schemeModuleTensor M T) (eM : M ≅ N)
    (eT : T ≅ SheafOfModules.unit Y.ringCatSheaf) :
    ActualModuleTensorChartData eTensor eM eT where
  iso := actualModuleTensorChartCompositeIso eTensor eM eT
  hom_eq := actualModuleTensorChartCompositeIso_hom eTensor eM eT
  iso_eq := by
    apply Iso.ext
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct the SAME native chart composite and its computation internally.
Its inferred type avoids duplicating concrete sheaf-module type expressions.
The opaque wrapper below protects its concrete Iso value from normalization. -/
private def actualCubicPositiveTwoNativeChartDataValue
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :=
  let I := equationIdeal p hp
  let R := ChartRing I j
  let f := chartι I j
  let Omega := schemeRelativeDifferentials (hypersurfaceToBase p hp)
  letI : Algebra K R := (chartBaseMap I j).toAlgebra
  let eOmega : (Scheme.Modules.pullback f).obj Omega ≅
      (tilde.functor (.of R)).obj (ModuleCat.of R (KaehlerDifferential K R)) :=
    (actualCubicNativeChartDifferentialSheafIso p hp j).symm ≪≫
      actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
  actualModuleTensorChartDataOfIsos
    (actualPositiveTwistPullbackTensorIso I f Omega 2) eOmega
    (actualPositiveTwistNativeChartUnitIso I j 2)

/-- Keep the fully defined native data value opaque when projecting its Iso
and derived equation. The type is inferred from that checked value declaration. -/
private opaque actualCubicPositiveTwoNativeChartData
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    type_of% (actualCubicPositiveTwoNativeChartDataValue p hp j) :=
  actualCubicPositiveTwoNativeChartDataValue p hp j

def actualCubicPositiveTwoNativeChartTildeIso
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    (Scheme.Modules.pullback (chartι (equationIdeal p hp) j)).obj
      (actualCubicPositiveTwoDifferentials p hp) ≅
        (tilde.functor (.of (ChartRing (equationIdeal p hp) j))).obj
          (ModuleCat.of (ChartRing (equationIdeal p hp) j)
            (KaehlerDifferential K (ChartRing (equationIdeal p hp) j))) := by
  exact (actualCubicPositiveTwoNativeChartData p hp j).iso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The hom of the SAME native Omega(2) chart Iso, computed through the
abstract tensor/chart hom equation without altering its construction. -/
lemma actualCubicPositiveTwoNativeChartTildeIso_hom
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    let W := schemeRelativeDifferentials (hypersurfaceToBase p hp)
    let N := (tilde.functor (.of R)).obj (ModuleCat.of R (KaehlerDifferential K R))
    let eOmega := (actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
      actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
    (actualCubicPositiveTwoNativeChartTildeIso p hp a).hom =
      (actualPositiveTwistPullbackTensorIso I (chartι I a) W 2).hom ≫
        schemeModuleTensorMap eOmega.hom (actualPositiveTwistNativeChartUnitIso I a 2).hom ≫
          (schemeModuleTensorUnitRightIso N).hom := by
  exact (actualCubicPositiveTwoNativeChartData p hp a).hom_eq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Opacity changes reduction behavior only: the actual native chart Iso
is equal to the complete original three-Iso composition, including its inverse. -/
lemma actualCubicPositiveTwoNativeChartTildeIso_eq_composite
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    let W := schemeRelativeDifferentials (hypersurfaceToBase p hp)
    let N := (tilde.functor (.of R)).obj (ModuleCat.of R (KaehlerDifferential K R))
    let eOmega := (actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
      actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
    actualCubicPositiveTwoNativeChartTildeIso p hp a =
      actualPositiveTwistPullbackTensorIso I (chartι I a) W 2 ≪≫
        schemeModuleTensorMapIso eOmega (actualPositiveTwistNativeChartUnitIso I a 2) ≪≫
          schemeModuleTensorUnitRightIso N := by
  exact (actualCubicPositiveTwoNativeChartData p hp a).iso_eq

end PfaffianDescent
