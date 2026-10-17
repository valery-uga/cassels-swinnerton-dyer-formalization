import PfaffianDescent.QuarticTwistedCubicRelativeCoordinate
import PfaffianDescent.QuarticTwistedCubicHilbertNinetyGalois

namespace PfaffianDescent.QuarticNet

open Matrix
open scoped MatrixGroups

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

/-- The ambient projective cocycle defined by an arbitrary geometric
coordinate matrix. -/
noncomputable def ambientCoordinateCocycle (rho : G →* L ≃+* L)
    (M : GL (Fin 4) L) :
    ProjectiveCocycle (L := L) 4 rho where
  toFun g := Matrix.ProjGenLinGroup.mk (ambientCoboundary rho M g)
  map_one' := by
    change Matrix.ProjGenLinGroup.mk
      (M⁻¹ * Matrix.GeneralLinearGroup.map (rho 1).toRingHom M) = 1
    rw [rho.map_one]
    change Matrix.ProjGenLinGroup.mk (M⁻¹ * M) = 1
    rw [inv_mul_cancel, Matrix.ProjGenLinGroup.mk_one]
  map_mul' g h := by
    change Matrix.ProjGenLinGroup.mk (ambientCoboundary rho M (g * h)) =
      Matrix.ProjGenLinGroup.mk (ambientCoboundary rho M g) *
        Matrix.ProjGenLinGroup.map (rho g).toRingHom
          (Matrix.ProjGenLinGroup.mk (ambientCoboundary rho M h))
    rw [Matrix.ProjGenLinGroup.map_mk, ← Matrix.ProjGenLinGroup.mk.map_mul]
    exact congrArg Matrix.ProjGenLinGroup.mk (ambientCoboundary_mul rho M g h).symm

@[simp] theorem ambientCoordinateCocycle_apply (rho : G →* L ≃+* L)
    (M : GL (Fin 4) L) (g : G) :
    ambientCoordinateCocycle rho M g =
      Matrix.ProjGenLinGroup.mk (ambientCoboundary rho M g) := rfl

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u v

/-- For a ground three-quadric ideal, every term of its ambient Galois
coordinate cocycle stabilizes the standard twisted-cubic ideal. -/
theorem galoisRelativeCoordinate_preserves_standardTwistedCubicIdeal
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (M : GL (Fin 4) L) (σ : Gal(L/K))
    (hM : (Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K L) (Q i)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L) :
    (standardTwistedCubicIdeal L).map
      (linearSubstitution (ambientCoboundary (ProjectiveCocycle.galFieldAction K L) M σ :
        Matrix (Fin 4) (Fin 4) L)).toRingHom = standardTwistedCubicIdeal L := by
  change (standardTwistedCubicIdeal L).map
    (linearSubstitution ((M⁻¹ * Matrix.GeneralLinearGroup.map σ.toRingHom M :
      GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L)).toRingHom =
        standardTwistedCubicIdeal L
  exact standardTwistedCubicIdeal_map_relativeCoordinate_of_algEquiv Q M σ hM

end PfaffianDescent.QuarticNet
