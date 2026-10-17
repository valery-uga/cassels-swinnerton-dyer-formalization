import PfaffianDescent.PlaneCubicProjectivePartialTransition175
import Mathlib.RingTheory.Localization.Away.Basic

/-! SOURCE ONLY175. The true projective chart intersection, followed by
localization at its own chosen partial, has explicit actual transition units.
The native Kähler residue expressions agree with the cyclic sign. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (j l m : Fin 3)

noncomputable local instance nativeProjectiveOverlapAlgebra175 :
    Algebra K (ChartOverlapRing (equationIdeal p hp) j l) :=
  (GradedChart.baseMap (grading (equationIdeal p hp))
    (z := coordinate (equationIdeal p hp) j * coordinate (equationIdeal p hp) l)).toAlgebra

/-- The derivative value on the actual chart intersection, retaining its
original whole hypersurface equation. -/
def actualProjectiveOverlapLeftPartial175 : ChartOverlapRing (equationIdeal p hp) j l :=
  chartOverlapLeftMap (equationIdeal p hp) j l
    ((pderiv m p).eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j))

/-- The actual common partial open inside the true projective intersection. -/
abbrev actualProjectivePartialOverlapRing175 :=
  Localization.Away (actualProjectiveOverlapLeftPartial175 p hp j l m)

/-- The original projective transition unit, restricted to this actual open. -/
def actualProjectivePartialCoordinateUnit175 :
    (actualProjectivePartialOverlapRing175 p hp j l m)ˣ :=
  Units.map (algebraMap (ChartOverlapRing (equationIdeal p hp) j l)
    (actualProjectivePartialOverlapRing175 p hp j l m)).toMonoidHom
    (chartOverlapUnit (equationIdeal p hp) j l)

/-- The first derivative unit is constructed by the actual localization. -/
def actualProjectivePartialLeftUnit175 :
    (actualProjectivePartialOverlapRing175 p hp j l m)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (actualProjectiveOverlapLeftPartial175 p hp j l m)).unit

theorem actualProjectivePartialLeftUnit_val175 :
    (actualProjectivePartialLeftUnit175 p hp j l m :
      actualProjectivePartialOverlapRing175 p hp j l m) =
      algebraMap (ChartOverlapRing (equationIdeal p hp) j l)
        (actualProjectivePartialOverlapRing175 p hp j l m)
        (actualProjectiveOverlapLeftPartial175 p hp j l m) := by
  rw [actualProjectivePartialLeftUnit175, IsUnit.unit_spec]

/-- The right derivative unit is derived from cubic homogeneity. -/
def actualProjectivePartialRightUnit175 :
    (actualProjectivePartialOverlapRing175 p hp j l m)ˣ :=
  actualProjectivePartialCoordinateUnit175 p hp j l m ^ 2 *
    actualProjectivePartialLeftUnit175 p hp j l m

theorem actualProjectivePartialRightUnit_val175 :
    (actualProjectivePartialRightUnit175 p hp j l m :
      actualProjectivePartialOverlapRing175 p hp j l m) =
      algebraMap (ChartOverlapRing (equationIdeal p hp) j l)
        (actualProjectivePartialOverlapRing175 p hp j l m)
        (chartOverlapRightMap (equationIdeal p hp) j l
          ((pderiv m p).eval₂ (chartBaseMap (equationIdeal p hp) l)
            (chartCoordinate (equationIdeal p hp) l))) := by
  rw [actualProjectivePartialRightUnit175]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    actualProjectivePartialCoordinateUnit175, Units.coe_map,
    actualProjectivePartialLeftUnit175, IsUnit.unit_spec]
  rw [planeCubic_actualProjectiveOverlap_partial_transition175, map_mul, map_pow]
  rfl

/-- In the SAME localized native Ω, the right chart's positive residue
expression equals the left chart's negative expression. For cyclic charts
(j,l,m)=(0,1,2), (1,2,0), or (2,0,1), these are precisely the matching
oriented local residue expressions. Every map and denominator unit is
constructed from the original cubic and actual projective chart overlap. -/
theorem planeCubic_actualProjectivePartialOverlap_residue_cancel175 :
    let I := equationIdeal p hp
    let H := ChartOverlapRing I j l
    let R := actualProjectivePartialOverlapRing175 p hp j l m
    (((actualProjectivePartialRightUnit175 p hp j l m)⁻¹ : Rˣ) : R) •
      KaehlerDifferential.D K R
        (algebraMap H R (chartOverlapRightMap I j l (chartCoordinate I l j))) =
      -((((actualProjectivePartialLeftUnit175 p hp j l m)⁻¹ : Rˣ) : R) •
        KaehlerDifferential.D K R
          (algebraMap H R (chartOverlapLeftMap I j l (chartCoordinate I j l)))) := by
  let I := equationIdeal p hp
  let H := ChartOverlapRing I j l
  let R := actualProjectivePartialOverlapRing175 p hp j l m
  have hu : (actualProjectivePartialCoordinateUnit175 p hp j l m : R) =
      algebraMap H R (chartOverlapRightMap I j l (chartCoordinate I l j)) := by
    rw [actualProjectivePartialCoordinateUnit175, Units.coe_map, chartOverlapUnit_val]
    rfl
  have hui : (((actualProjectivePartialCoordinateUnit175 p hp j l m)⁻¹ : Rˣ) : R) =
      algebraMap H R (chartOverlapLeftMap I j l (chartCoordinate I j l)) := by
    rw [actualProjectivePartialCoordinateUnit175, Units.coe_map_inv, chartOverlapUnit_inv]
    rfl
  have h := nativeUnitDifferential_quadraticTransition_cancel175 (K := K)
    (actualProjectivePartialCoordinateUnit175 p hp j l m)
    (actualProjectivePartialLeftUnit175 p hp j l m)
  rw [hu, hui] at h
  exact h

end PfaffianDescent.Coray
