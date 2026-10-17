import PfaffianDescent.ActualOriginalIdealQuadraticNativeRestriction
import Mathlib.RingTheory.Kaehler.Basic

/- SOURCE ONLY / UNVERIFIED. GENUINE original quadratic ideal section
restricts to the original residue ideal I and then to the ACTUAL I/I^2.
Residue vanishing is derived from the real original sheaf-H0 membership. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalIdealQuadraticConormalClass
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let R := ChartRing (equationIdeal p hp) C.index
    letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    ActualOriginalPointIdealQuadraticSections p hp P →ₗ[K]
      (RingHom.ker C.residue).Cotangent := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  let I := RingHom.ker C.residue
  let restrictToIdeal : ActualOriginalPointIdealQuadraticSections p hp P →ₗ[K] I :=
    { toFun s := ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
      map_add' s t := Subtype.ext
        ((actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP).map_add s t)
      map_smul' c s := Subtype.ext
        ((actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP).map_smul c s) }
  exact (I.toCotangent.restrictScalars K).comp restrictToIdeal

lemma actualOriginalIdealQuadraticConormalClass_apply
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let R := ChartRing (equationIdeal p hp) C.index
    letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    actualOriginalIdealQuadraticConormalClass p hp P hP s =
      (RingHom.ker C.residue).toCotangent
        ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
          actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩ := rfl

end PfaffianDescent
