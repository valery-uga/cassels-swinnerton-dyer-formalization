import PfaffianDescent.VoisinPlaneConicCubicSections
import PfaffianDescent.VoisinPlaneConicActualImmersion
import PfaffianDescent.HomogeneousQuotientMap

/-!
# Cubic coordinate restriction to a conic

For homogeneous ideals `I ⊆ J`, the kernel of the map on degree `d`
coordinate pieces is exactly the image of the degree `d` part of `J`.
The plane-conic specialization identifies this kernel with the existing
twelve-dimensional cubic system on the smooth cubic surface.
-/

noncomputable section

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Restriction of a homogeneous coordinate class along a homogeneous
closed immersion, on a fixed degree. -/
noncomputable def gradedQuotientPieceLinearMap
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    grading I d →ₗ[K] grading J d where
  toFun z := ⟨coordinateQuotientMap I J hIJ z.1,
    coordinateQuotientMap_mem I J hIJ z.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact (coordinateQuotientMap I J hIJ).map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (Ideal.Quotient.factorₐ K hIJ) a x.1

/-- Every homogeneous class on the smaller closed subscheme lifts in the
same degree from the larger one. -/
theorem gradedQuotientPieceLinearMap_surjective
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    Function.Surjective (gradedQuotientPieceLinearMap I J hIJ d) := by
  intro y
  obtain ⟨q, hq⟩ := homogeneousIdealPieceQuotientMap_surjective J d y
  refine ⟨homogeneousIdealPieceQuotientMap I d q, ?_⟩
  apply Subtype.ext
  have hv := congrArg Subtype.val hq
  change Ideal.Quotient.mk J.toIdeal q.1 = y.1 at hv
  change Ideal.Quotient.factor hIJ
    (Ideal.Quotient.mk I.toIdeal q.1) = y.1
  rw [Ideal.Quotient.factor_mk]
  exact hv

/-- The kernel consists precisely of classes represented by degree `d`
polynomials in the larger homogeneous ideal. -/
theorem gradedQuotientPieceLinearMap_ker
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    LinearMap.ker (gradedQuotientPieceLinearMap I J hIJ d) =
      (homogeneousIdealPiece J d).map (homogeneousIdealPieceQuotientMap I d) := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := homogeneousIdealPieceQuotientMap_surjective I d x
    have hqJ : q ∈ homogeneousIdealPiece J d := by
      have hx' := LinearMap.mem_ker.mp hx
      have hv := congrArg Subtype.val hx'
      rw [← hq] at hv
      change Ideal.Quotient.mk J.toIdeal q.1 = 0 at hv
      exact Ideal.Quotient.eq_zero_iff_mem.mp hv
    exact ⟨q, hqJ, hq⟩
  · rintro ⟨q, hqJ, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change Ideal.Quotient.mk J.toIdeal q.1 = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqJ

/-- The kernel of cubic coordinate restriction from a cubic surface to an
actual plane conic is the cubic system of the conic on the surface. -/
theorem cubicToPlaneConic_gradedRestriction_ker
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    LinearMap.ker (gradedQuotientPieceLinearMap
      (equationIdeal p hp) (planeConicHomogeneousIdeal ell q hell hq)
      (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3) =
    fixedCurveCubicSurfaceSystem p hp
      (planeConicHomogeneousIdeal ell q hell hq) := by
  rw [gradedQuotientPieceLinearMap_ker]
  rfl

/-- The degree-three coordinate restriction kernel for a plane conic on a
smooth cubic has dimension at most twelve. -/
theorem cubicToPlaneConic_gradedRestriction_ker_finrank_le_twelve
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2)
    (hp0 : p ≠ 0) (hell0 : ell ≠ 0) (hq0 : q ≠ 0)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    finrank K (LinearMap.ker (gradedQuotientPieceLinearMap
      (equationIdeal p hp) (planeConicHomogeneousIdeal ell q hell hq)
      (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3)) ≤ 12 := by
  rw [cubicToPlaneConic_gradedRestriction_ker p ell q hp hell hq hpc]
  exact fixedCurveCubicSurfaceSystem_finrank_le_twelve_of_plane_conic
    p hp hp0 (planeConicHomogeneousIdeal ell q hell hq)
    ⟨ell, hell⟩ ⟨q, hq⟩ hell0 hq0 rfl hpc

end PfaffianDescent
