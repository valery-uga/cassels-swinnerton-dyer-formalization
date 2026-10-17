import PfaffianDescent.VoisinPlaneConicActualImmersion
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import AllCharacteristics.ProjectivePoints
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Nonemptiness of the actual plane–quadric projective intersection

Two positive-degree homogeneous equations in four variables have a common
nonzero zero over an algebraic closure. A field-valued zero of the two
generators gives a point of their actual projective quotient scheme.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective scheme cut out by a plane equation and a
quadratic equation is nonempty, even when the conic has no rational point
over the ground field. -/
theorem planeConicScheme_nonempty
    (ell q : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hq : q.IsHomogeneous 2) :
    Nonempty (planeConicScheme ell q hell hq) := by
  let L : Type u := AlgebraicClosure K
  letI : Field L := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K L := inferInstanceAs (Algebra K (AlgebraicClosure K))
  let φ : K →+* L := algebraMap K L
  obtain ⟨x, hx, hellx, hqx⟩ :=
    exists_nonzero_common_zero_of_homogeneous_pos
      (ell.map φ) (q.map φ) (hell.map φ) (hq.map φ)
      (by decide : 0 < 1) (by decide : 0 < 2)
  have hellzero : ell.eval₂ φ x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self,
      MvPolynomial.eval₂_map, RingHom.id_comp] using hellx
  have hqzero : q.eval₂ φ x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self,
      MvPolynomial.eval₂_map, RingHom.id_comp] using hqx
  have he : ∀ r : MvPolynomial (Fin 4) K,
      r ∈ (planeConicHomogeneousIdeal ell q hell hq).toIdeal →
        r.eval₂ φ x = 0 := by
    have hle : (planeConicHomogeneousIdeal ell q hell hq).toIdeal ≤
        RingHom.ker (eval₂Hom φ x) := by
      change Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)) ≤
        RingHom.ker (eval₂Hom φ x)
      apply Ideal.span_le.mpr
      intro r hr
      rcases hr with rfl | rfl
      · exact hellzero
      · exact hqzero
    intro r hr
    exact hle hr
  obtain ⟨s, -⟩ := point_of_coordinates
    (planeConicHomogeneousIdeal ell q hell hq) φ x hx he
  exact ⟨s (IsLocalRing.closedPoint L)⟩

end PfaffianDescent
