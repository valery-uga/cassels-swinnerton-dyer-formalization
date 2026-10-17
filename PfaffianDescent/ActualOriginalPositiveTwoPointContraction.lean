import PfaffianDescent.ActualGlobalPositiveTwistConormalContraction
import PfaffianDescent.ActualPositiveTwistNativeChartUnitIso
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice

/- SOURCE ONLY / UNVERIFIED. The original native O2 point generator is
constructed using the SAME original chart factorization. The global
conormal contraction square therefore has no supplied twist Iso premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Preserve the complete Iso and derive its equality internally. -/
private def actualWholeIsoData {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) : {iso : M ≅ N // iso = e} := ⟨e, rfl⟩

private def actualOriginalPositiveTwoPointTrivializationDataValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let T := positiveSheafOfModules (grading I) 2
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsIso (pullbackUnitComparison j) := isIso_pullbackUnitComparison j
  actualWholeIsoData (eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj T)
      C.factorization.symm) ≪≫
    (Scheme.Modules.pullbackComp j f).symm.app T ≪≫
    (Scheme.Modules.pullback j).mapIso (actualPositiveTwistNativeChartUnitIso I C.index 2) ≪≫
    asIso (pullbackUnitComparison j))

/-- Fully supplied data; opacity avoids repeated normalization.
The equality field retains the whole original composite, including its inverse. -/
private opaque actualOriginalPositiveTwoPointTrivializationData
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalPositiveTwoPointTrivializationDataValue p hp P hP) :=
  actualOriginalPositiveTwoPointTrivializationDataValue p hp P hP

def actualOriginalPositiveTwoPointTrivialization
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    (Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of ((hypersurface p hp).residueField P.1))).ringCatSheaf :=
  (actualOriginalPositiveTwoPointTrivializationData p hp P hP).val

/-- The actual original-point trivialization is the complete original Iso. -/
lemma actualOriginalPositiveTwoPointTrivialization_eq_composite
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let T := positiveSheafOfModules (grading I) 2
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsIso (pullbackUnitComparison j) := isIso_pullbackUnitComparison j
    actualOriginalPositiveTwoPointTrivialization p hp P hP =
      eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj T)
        C.factorization.symm) ≪≫
      (Scheme.Modules.pullbackComp j f).symm.app T ≪≫
      (Scheme.Modules.pullback j).mapIso (actualPositiveTwistNativeChartUnitIso I C.index 2) ≪≫
      asIso (pullbackUnitComparison j) := by
  exact (actualOriginalPositiveTwoPointTrivializationData p hp P hP).property

lemma actualOriginalPositiveTwoPointContraction_square
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let T := (Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) 2)
    let e := actualOriginalPositiveTwoPointTrivialization p hp P hP
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    actualGlobalPositiveTwistConormalDifferentialMap I q 2 ≫
      (actualPositiveTwistPullbackTensorIso I q (schemeRelativeDifferentials (toBase I)) 2).hom ≫
      (actualPointTwistUntwistIso
        ((Scheme.Modules.pullback q).obj (schemeRelativeDifferentials (toBase I))) T e).hom =
    (actualPositiveTwistPullbackTensorIso I q (closedImmersionModule q) 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj (closedImmersionModule q)) T e).hom ≫
      actualGlobalClosedConormalDifferentialMap (toBase I) q := by
  dsimp only
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  exact actualGlobalPositiveTwistConormalDifferentialMap_contract
    (equationIdeal p hp) ((hypersurface p hp).fromSpecResidueField P.1) 2
    (actualOriginalPositiveTwoPointTrivialization p hp P hP)

end PfaffianDescent
