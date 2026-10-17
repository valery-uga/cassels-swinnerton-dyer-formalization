import PfaffianDescent.CorayGeometricallyIntegralNormalizationConstants

/-!
# Actual original p/q geometrically integral curve normalization constant rank

SOURCE ONLY / UNVERIFIED. This concrete caller derives original integrality
from genuine geometric integrality of the ORIGINAL toBase morphism. The
accepted actual normalization H0 finiteness is discharged from p/q internally.
No replacement ground field or supplied constant-rank certificate is used.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine geometrically integral original selected projective p/q curve
has normalization unit global sections of rank one over the SAME ORIGINAL K.
Actual original integrality and normalization H0 finiteness are internal.
The geometric-integrality branch itself is explicit and not constructed by
interpolation, nor asserted for every selected equation. -/
theorem projectiveIntersection_geometricallyIntegral_genericNormalization_unit_topSections_finrank_eq_one
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) = 1 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  have hfinite : Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) :=
    projectiveIntersection_genericNormalization_unit_topSections_finite_native
      p q hp hp0 n hn hq hnot
  exact integralGenericNormalization_unit_topSections_finrank_eq_one_of_geometricallyIntegral
    X (toBase I) hfinite

end PfaffianDescent.Coray
