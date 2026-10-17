import PfaffianDescent.VoisinPlaneConicSerreJacobianEndpoint
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smoothness input for the converse chartwise Jacobian criterion

The abstract smoothness of a projective cubic restricts to each actual
standard affine chart. This identifies the formally smooth quotient algebra
to which a converse hypersurface Jacobian argument must be applied.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Each actual standard affine chart of a smooth cubic is smooth over
the ground field. -/
theorem smoothCubic_chartBaseMap_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4) :
    (chartBaseMap (equationIdeal p hp) j).Smooth := by
  have hc : Smooth (Spec.map (CommRingCat.ofHom
      (chartBaseMap (equationIdeal p hp) j))) := by
    rw [← chartι_toBase]
    have hbase : Smooth (toBase (equationIdeal p hp)) :=
      inferInstanceAs (Smooth (hypersurfaceToBase p hp))
    letI : Smooth (toBase (equationIdeal p hp)) := hbase
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mp hc

/-- In particular, each affine chart algebra is formally smooth over the
ground field. This is the starting point for a square-zero thickening proof
of the reverse Jacobian criterion. -/
theorem smoothCubic_chartAlgebra_formallySmooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    Algebra.FormallySmooth K (ChartRing (equationIdeal p hp) j) := by
  letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
    (chartBaseMap (equationIdeal p hp) j).toAlgebra
  exact (RingHom.smooth_algebraMap.mp
    (smoothCubic_chartBaseMap_smooth p hp j)).formallySmooth

/-- Formal smoothness supplies an actual section of the first-order
thickening of the normalized chart polynomial presentation. Algebraically,
the remaining reverse-Jacobian step is to expand this section on `p` and
`X_j - 1` and extract a Bézout identity for the partial derivatives. -/
theorem smoothCubic_chartPresentation_squareZero_split
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    let f : MvPolynomial (Fin 4) K →ₐ[K]
        ChartRing (equationIdeal p hp) j :=
      MvPolynomial.aeval (chartCoordinate (equationIdeal p hp) j)
    ∃ g, f.kerSquareLift.comp g = AlgHom.id K _ := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let f : MvPolynomial (Fin 4) K →ₐ[K] ChartRing I j :=
    MvPolynomial.aeval (chartCoordinate I j)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := eval₂_chartCoordinate_surjective I j y
    exact ⟨x, by
      simpa only [f, MvPolynomial.aeval_eq_eval₂Hom,
        RingHom.algebraMap_toAlgebra] using hx⟩
  exact (Algebra.FormallySmooth.iff_split_surjection f hf).mp
    (smoothCubic_chartAlgebra_formallySmooth p hp j)

end PfaffianDescent
