import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Source-only / unverified. A quasi-compact map from an integral scheme
has an integral scheme-theoretic image. Reducedness is proved on the
actual quotient-ring affine cover, rather than supplied for the image. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- Each defining affine quotient of the actual image injects into a
ring of sections of the reduced source. -/
theorem schemeImage_affineQuotient_isReduced [IsReduced X] (U : Y.affineOpens) :
    _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U) := by
  rw [Scheme.Hom.ker_apply]
  exact isReduced_of_injective (RingHom.kerLift (f.app U).hom)
    (RingHom.kerLift_injective (f.app U).hom)

/-- The actual scheme-theoretic image of a reduced source is reduced. -/
theorem schemeImage_isReduced [IsReduced X] : IsReduced f.image := by
  have hReduced : ∀ U : Y.affineOpens,
      IsReduced (f.ker.subschemeCover.openCover.X U) := fun U => by
    letI : _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U) :=
      schemeImage_affineQuotient_isReduced f U
    change IsReduced (Spec (CommRingCat.of (Γ(Y, U) ⧸ f.ker.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover f.image f.ker.subschemeCover.openCover hReduced

/-- Image support is the closure of the image of the irreducible source;
the preceding reducedness proof then gives integrality. -/
theorem schemeImage_isIntegral [IsIntegral X] : IsIntegral f.image := by
  letI : IsReduced f.image := schemeImage_isReduced f
  have hs : IsIrreducible (f.ker.support : Set Y) := by
    rw [Scheme.Hom.support_ker]
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ X).image f
        f.continuous.continuousOn).closure
  letI : IrreducibleSpace f.image := Subtype.irreducibleSpace hs
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

end PfaffianDescent.Coray
end
