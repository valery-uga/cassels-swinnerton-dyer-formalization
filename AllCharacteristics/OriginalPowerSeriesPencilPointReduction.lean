import AllCharacteristics.PrescribedLaurentPencilGenericPoint
import AllCharacteristics.HypersurfaceReduction

/-! SOURCE ONLY / UNVERIFIED. Exact map of the GIVEN original point into
the pencil special fiber and its coefficient square. The lift theorem below
is deliberately named _of_relativeSmooth: pointwise smoothness of the original
surface has NOT yet been transported to relative smoothness at this SAME map.
This is a conditional interface helper, not a completed literal Section6 caller. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p g : MvPolynomial (Fin 4) k)
variable (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3)

/-- Canonical special-fiber inclusion, with literal equation reduction. -/
def prescribedPencilOriginalReductionMap :
    hypersurface p hp ⟶ hypersurface (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg) :=
  hypersurfaceReductionMap (PowerSeries.constantCoeff (R := k))
    (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg)
    p hp (prescribedPowerSeriesPencil_constantCoeff p g)

theorem prescribedPencilOriginalReductionMap_base :
    prescribedPencilOriginalReductionMap p g hp hg ≫
      hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg) =
    hypersurfaceToBase p hp ≫
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) :=
  hypersurfaceReductionMap_toBase _ _ _ _ _ _

variable (q : Spec (.of L) ⟶ hypersurface p hp)
variable (hq : q ≫ hypersurfaceToBase p hp =
  Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- The original q itself, never a point chosen from a Jacobian existence proof. -/
def prescribedPencilOriginalSpecialPoint :
    Spec (.of L) ⟶ hypersurface (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg) :=
  q ≫ prescribedPencilOriginalReductionMap p g hp hg

theorem prescribedPencilOriginalSpecialPoint_base :
    prescribedPencilOriginalSpecialPoint p g hp hg q ≫
        hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap k L).comp (PowerSeries.constantCoeff (R := k)))) := by
  change (q ≫ prescribedPencilOriginalReductionMap p g hp hg) ≫ _ = _
  rw [Category.assoc, prescribedPencilOriginalReductionMap_base,
    ← Category.assoc, hq, ← Spec.map_comp]
  rfl

/-- Exact original-point reduction, GIVEN relative smoothness at its canonical
special inclusion. That input is the precise remaining interface obligation;
it is not claimed derived from original-surface smoothness by this helper. -/
theorem prescribedPencilOriginalPoint_lift_of_relativeSmooth
    (hsm : prescribedPencilOriginalSpecialPoint p g hp hg q
        (IsLocalRing.closedPoint L) ∈
      (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg)).smoothLocus) :
    ∃ s : Spec (.of (PowerSeries L)) ⟶ hypersurface
        (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg),
      s ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg) =
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (PowerSeries L))) ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := L))) ≫ s =
        q ≫ prescribedPencilOriginalReductionMap p g hp hg :=
  prescribedPowerSeriesPencil_lift_given_smooth_point p g hp hg
    (prescribedPencilOriginalSpecialPoint p g hp hg q)
    (prescribedPencilOriginalSpecialPoint_base p g hp hg q hq) hsm

end AllCharacteristics
