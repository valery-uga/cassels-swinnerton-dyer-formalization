import PfaffianDescent.PolynomialCoefficientExtensionIntersection
import PfaffianDescent.MatchingProjectorIntersectionGaloisStability

/-! SOURCE ONLY, UNVERIFIED. Exact scalar extension of the WHOLE matching
intersection, over arbitrary field extensions and in every characteristic. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial
universe u
variable {E K : Type u} [Field E] [Field K] [Algebra E K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem matchingProjectorIntersectionIdeal_baseChange
    (P : Matrix (Fin 4) (Fin 4) E) :
    (matchingProjectorIntersectionIdeal P).toIdeal.map
        (MvPolynomial.map (algebraMap E K)) =
      (matchingProjectorIntersectionIdeal (P.map (algebraMap E K))).toIdeal := by
  have hComp : (1 - P).map (algebraMap E K) = 1 - P.map (algebraMap E K) := by
    ext m n
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  change ((projectorLineIdeal P).toIdeal ⊓ (projectorLineIdeal (1 - P)).toIdeal).map
      (MvPolynomial.map (algebraMap E K)) = _
  rw [PfaffianDescent.mvPolynomial_coefficientExtension_map_inf,
    projectorLineIdeal_baseChange, projectorLineIdeal_baseChange, hComp]
  rfl

/-- A ground ideal whose E-extension is the actual projector intersection
has EXACTLY the original K-intersection after extending to K. The structural
E-level identity is used only inside the actual matching construction below. -/
theorem matchingGroundIntersection_extension_to_original
    {k : Type u} [Field k] [Algebra k E] [Algebra k K] [IsScalarTower k E K]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (P : Matrix (Fin 4) (Fin 4) E)
    (hJ : J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
      (matchingProjectorIntersectionIdeal P).toIdeal) :
    J.toIdeal.map (MvPolynomial.map (algebraMap k K)) =
      (matchingProjectorIntersectionIdeal (P.map (algebraMap E K))).toIdeal := by
  have hcoeff : (algebraMap E K).comp (algebraMap k E) = algebraMap k K := by
    ext z
    exact (IsScalarTower.algebraMap_apply k E K z).symm
  have hpoly : (MvPolynomial.map (σ := Fin 4) (algebraMap E K)).comp
      (MvPolynomial.map (algebraMap k E)) = MvPolynomial.map (algebraMap k K) := by
    apply RingHom.ext
    intro q
    rw [RingHom.comp_apply, MvPolynomial.map_map, hcoeff]
  calc
    J.toIdeal.map (MvPolynomial.map (algebraMap k K)) =
        (J.toIdeal.map (MvPolynomial.map (algebraMap k E))).map
          (MvPolynomial.map (algebraMap E K)) := by rw [Ideal.map_map, hpoly]
    _ = (matchingProjectorIntersectionIdeal P).toIdeal.map
        (MvPolynomial.map (algebraMap E K)) := by rw [hJ]
    _ = _ := matchingProjectorIntersectionIdeal_baseChange P

end PfaffianDescent.QuarticNet
