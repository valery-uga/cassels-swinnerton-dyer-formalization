import AllCharacteristics.CoordinateCharts
import AllCharacteristics.GradedChartCoordinates
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! SOURCE ONLY / UNVERIFIED. The inverse morphism is constructed on an
actual basic open of the SAME original cubic. The quadratic polynomials
are intermediate outputs of paired-coordinate descent, not a certificate
of birationality. This module does not yet claim the forward map or iso. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.InverseChart
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k]

abbrev PlaneIndex := ULift.{u} (Fin 2)

section Quotient
variable (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))

def quadraticClass (Q : MvPolynomial (Fin 4) k) : CoordinateRing I :=
  Ideal.Quotient.mk I.toIdeal Q

theorem quadraticClass_mem (Q : MvPolynomial (Fin 4) k)
    (hQ : Q.IsHomogeneous 2) : quadraticClass I Q ∈ grading I 2 :=
  ⟨Q, hQ, rfl⟩

abbrev QuadraticChartRing (Q : MvPolynomial (Fin 4) k) :=
  Away (grading I) (quadraticClass I Q)

def quadraticChartι (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2) :
    Spec (.of (QuadraticChartRing I Q)) ⟶ scheme I :=
  Proj.awayι (grading I) (quadraticClass I Q) (quadraticClass_mem I Q hQ)
    (by decide : 0 < 2)

instance quadraticChartι_isOpenImmersion
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2) :
    IsOpenImmersion (quadraticChartι I Q hQ) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (grading I) (quadraticClass I Q)
    (quadraticClass_mem I Q hQ) (by decide : 0 < 2)))

def quadraticChartBaseMap (Q : MvPolynomial (Fin 4) k) :
    k →+* QuadraticChartRing I Q :=
  GradedChart.baseMap (grading I) (z := quadraticClass I Q)

theorem quadraticChartι_toBase
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2) :
    quadraticChartι I Q hQ ≫ toBase I =
      Spec.map (CommRingCat.ofHom (quadraticChartBaseMap I Q)) := by
  change Proj.awayι (grading I) (quadraticClass I Q) (quadraticClass_mem I Q hQ)
      (by decide : 0 < 2) ≫ (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (grading I 0)))) =
    Spec.map (CommRingCat.ofHom ((fromZeroRingHom (grading I)
      (.powers (quadraticClass I Q))).comp (algebraMap k (grading I 0))))
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

def quadraticFraction (Q R : MvPolynomial (Fin 4) k)
    (hQ : Q.IsHomogeneous 2) (hR : R.IsHomogeneous 2) : QuadraticChartRing I Q :=
  Away.mk (grading I) (quadraticClass_mem I Q hQ) 1 (quadraticClass I R)
    (by simpa only [one_smul] using quadraticClass_mem I R hR)

/-- The actual polynomial-ring map encoding the inverse T,U functions. -/
def inverseCoordinateRingHom
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k)
    (hR : ∀ i, (R i).IsHomogeneous 2) :
    MvPolynomial PlaneIndex k →+* QuadraticChartRing I Q :=
  MvPolynomial.eval₂Hom (quadraticChartBaseMap I Q)
    (fun i => quadraticFraction I Q (R i) hQ (hR i))

theorem inverseCoordinateRingHom_X
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k)
    (hR : ∀ i, (R i).IsHomogeneous 2) (i : PlaneIndex) :
    inverseCoordinateRingHom I Q hQ R hR (X i) =
      quadraticFraction I Q (R i) hQ (hR i) :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- This is a genuine morphism from the original homogeneous quotient's
quadratic basic open to actual affine two-space. -/
def inverseChartSpecHom
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k)
    (hR : ∀ i, (R i).IsHomogeneous 2) :
    Spec (.of (QuadraticChartRing I Q)) ⟶ AffineSpace PlaneIndex (Spec (.of k)) :=
  Spec.map (CommRingCat.ofHom (inverseCoordinateRingHom I Q hQ R hR)) ≫
    (AffineSpace.SpecIso PlaneIndex (.of k)).inv

theorem inverseChartSpecHom_over
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k)
    (hR : ∀ i, (R i).IsHomogeneous 2) :
    inverseChartSpecHom I Q hQ R hR ≫ (𝔸(PlaneIndex; Spec (.of k)) ↘ Spec (.of k)) =
      quadraticChartι I Q hQ ≫ toBase I := by
  have hcomp : (inverseCoordinateRingHom I Q hQ R hR).comp
      (MvPolynomial.C : k →+* MvPolynomial PlaneIndex k) =
      quadraticChartBaseMap I Q := by
    apply RingHom.ext
    intro r
    exact MvPolynomial.eval₂_C _ _ r
  rw [inverseChartSpecHom, Category.assoc, AffineSpace.SpecIso_inv_over,
    quadraticChartι_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]

end Quotient

/-- Specialization to the literal original cubic. Its equation or
coordinate system is not replaced by a new abstract cubic. -/
def originalCubicInverseHom
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k)
    (hR : ∀ i, (R i).IsHomogeneous 2) :
    (Proj.basicOpen (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q)).toScheme ⟶
      AffineSpace PlaneIndex (Spec (.of k)) :=
  (Proj.basicOpenIsoSpec (grading (equationIdeal F hF))
    (quadraticClass (equationIdeal F hF) Q)
    (quadraticClass_mem (equationIdeal F hF) Q hQ) (by decide : 0 < 2)).hom ≫
      inverseChartSpecHom (equationIdeal F hF) Q hQ R hR

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem originalCubicInverseHom_over
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k)
    (hR : ∀ i, (R i).IsHomogeneous 2) :
    originalCubicInverseHom F hF Q hQ R hR ≫
        (𝔸(PlaneIndex; Spec (.of k)) ↘ Spec (.of k)) =
      (Proj.basicOpen (grading (equationIdeal F hF))
        (quadraticClass (equationIdeal F hF) Q)).ι ≫ hypersurfaceToBase F hF := by
  rw [originalCubicInverseHom, Category.assoc, inverseChartSpecHom_over]
  dsimp only [hypersurfaceToBase]
  simp only [quadraticChartι, Proj.awayι, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end PfaffianDescent.QuadraticSkewRationality.InverseChart
