import AllCharacteristics.HomogeneousTupleQuotient
import AllCharacteristics.UniversalHomogeneous

/-!
# The actual quartet quotient of the universal cubic family

The universal cubic equation over its affine coefficient scheme has an
actual finite surjective quotient of its fourth ordered relative power.
All maps are constructed over the original coefficient ring, including
the integers and fields of characteristics two and three.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u
variable (R : Type u) [CommRing R]

/-- The actual unordered-quartet scheme of the universal cubic equation. -/
noncomputable def cubicQuartetQuotient : Scheme.{u} :=
  HomogeneousProjective.tupleQuotient
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual finite-group quotient map from four ordered points of the universal cubic. -/
noncomputable def cubicQuartetQuotientMap :
    (orderedFamilyPowerOver (familyToCoefficients R (Fin 4) 3) 4).left ⟶ cubicQuartetQuotient R :=
  HomogeneousProjective.tupleQuotientMap
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual unordered-quartet scheme maps to the universal cubic coefficient scheme. -/
noncomputable def cubicQuartetQuotientToCoefficients :
    cubicQuartetQuotient R ⟶ Spec (.of (Coefficients (Fin 4) 3 R)) :=
  HomogeneousProjective.tupleQuotientToBase
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal quartet quotient map retains the original cubic coefficient map. -/
theorem cubicQuartetQuotientMap_toCoefficients :
    cubicQuartetQuotientMap R ≫ cubicQuartetQuotientToCoefficients R =
      (orderedFamilyPowerOver (familyToCoefficients R (Fin 4) 3) 4).hom :=
  HomogeneousProjective.tupleQuotientMap_toBase
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal cubic quartet quotient morphism is finite. -/
instance isFinite_cubicQuartetQuotientMap : IsFinite (cubicQuartetQuotientMap R) :=
  HomogeneousProjective.isFinite_tupleQuotientMap
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal cubic quartet quotient morphism is surjective. -/
instance surjective_cubicQuartetQuotientMap : Surjective (cubicQuartetQuotientMap R) :=
  HomogeneousProjective.surjective_tupleQuotientMap
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal cubic quartet quotient morphism is proper. -/
instance isProper_cubicQuartetQuotientMap : IsProper (cubicQuartetQuotientMap R) := by
  infer_instance

end UniversalHomogeneous
end AllCharacteristics
