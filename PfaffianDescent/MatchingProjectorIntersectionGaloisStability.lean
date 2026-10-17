import PfaffianDescent.ActualMatchingProjectorGaloisPair
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.Algebra.MvPolynomial.Equiv

/-! SOURCE ONLY, UNVERIFIED. The literal INTERSECTION of the two projector
line ideals is Galois-stable. The actual coefficient action is an ideal
order isomorphism, so this preserves the WHOLE ideal, including nilpotents. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E]
attribute [local instance] MvPolynomial.gradedAlgebra

def matchingProjectorIntersectionIdeal (P : Matrix (Fin 4) (Fin 4) E) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) E) :=
  projectorLineIdeal P ⊓ projectorLineIdeal (1 - P)

theorem matchingProjectorIntersectionIdeal_map_galois_pair
    (P : Matrix (Fin 4) (Fin 4) E) (g : E ≃ₐ[k] E)
    (hP : P.map g.toRingHom = P ∨ P.map g.toRingHom = 1 - P) :
    (matchingProjectorIntersectionIdeal P).toIdeal.map (MvPolynomial.map g.toRingHom) =
      (matchingProjectorIntersectionIdeal P).toIdeal := by
  let e := MvPolynomial.mapAlgEquiv (Fin 4) g
  have hInf : ((projectorLineIdeal P).toIdeal ⊓
      (projectorLineIdeal (1 - P)).toIdeal).map (MvPolynomial.map g.toRingHom) =
      (projectorLineIdeal P).toIdeal.map (MvPolynomial.map g.toRingHom) ⊓
        (projectorLineIdeal (1 - P)).toIdeal.map (MvPolynomial.map g.toRingHom) :=
    (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm.map_inf _ _
  change ((projectorLineIdeal P).toIdeal ⊓
      (projectorLineIdeal (1 - P)).toIdeal).map (MvPolynomial.map g.toRingHom) = _
  rw [hInf, projectorLineIdeal_baseChange, projectorLineIdeal_baseChange]
  have hOneMinus : (1 - P).map g.toRingHom = 1 - P.map g.toRingHom := by
    ext m n
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  rw [hOneMinus]
  rcases hP with hP | hP
  · rw [hP]
    rfl
  · rw [hP]
    have hComp : (1 : Matrix (Fin 4) (Fin 4) E) - (1 - P) = P := by
      abel
    rw [hComp, inf_comm]
    rfl

end PfaffianDescent.QuarticNet
