import AllCharacteristics.HomogeneousProjectiveAmbient
import AllCharacteristics.ProjectiveBaseChange
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! SOURCE ONLY / UNVERIFIED. The actual scheme cut out by a homogeneous
cubic AND its four partials, with no reduction of its scheme structure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S]

def cubicJacobianIdeal (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) R) :=
  equationIdeal p hp ⊔ ⨆ j : Fin 4, equationIdeal (pderiv j p) hp.pderiv

theorem equationIdeal_le_cubicJacobianIdeal
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) :
    (equationIdeal p hp).toIdeal ≤ (cubicJacobianIdeal p hp).toIdeal := by
  simp only [cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
    HomogeneousIdeal.toIdeal_iSup]
  exact le_sup_left

theorem pderiv_mem_cubicJacobianIdeal
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    pderiv j p ∈ (cubicJacobianIdeal p hp).toIdeal := by
  simp only [cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
    HomogeneousIdeal.toIdeal_iSup]
  have h₁ : (equationIdeal (pderiv j p) hp.pderiv).toIdeal ≤
      ⨆ a : Fin 4, (equationIdeal (pderiv a p) hp.pderiv).toIdeal :=
    le_iSup (fun a : Fin 4 => (equationIdeal (pderiv a p) hp.pderiv).toIdeal) j
  have h₂ : (⨆ a : Fin 4, (equationIdeal (pderiv a p) hp.pderiv).toIdeal) ≤
      (equationIdeal p hp).toIdeal ⊔
        ⨆ a : Fin 4, (equationIdeal (pderiv a p) hp.pderiv).toIdeal := le_sup_right
  exact h₂ (h₁ (Ideal.subset_span (Set.mem_singleton _)))

theorem cubicJacobianIdeal_map
    (f : R →+* S) (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) :
    (cubicJacobianIdeal p hp).toIdeal.map (MvPolynomial.map f) =
      (cubicJacobianIdeal (p.map f) (hp.map f)).toIdeal := by
  simp only [cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
    HomogeneousIdeal.toIdeal_iSup, Ideal.map_sup, Ideal.map_iSup]
  rw [equationIdeal_map f p hp]
  apply congrArg (fun J : Ideal (MvPolynomial (Fin 4) S) =>
    (equationIdeal (p.map f) (hp.map f)).toIdeal ⊔ J)
  apply congrArg (fun J : Fin 4 → Ideal (MvPolynomial (Fin 4) S) => ⨆ j, J j)
  funext j
  simpa only [MvPolynomial.pderiv_map] using
    equationIdeal_map f (pderiv j p) hp.pderiv

/-- The underlying projective locus is EXACTLY the simultaneous vanishing
of the original equation and all four partials, in every characteristic. -/
theorem cubicJacobianProjectiveZeroLocus_mem_iff
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    (x : Proj (homogeneousSubmodule (Fin 4) R)) :
    x ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) R)
        (cubicJacobianIdeal p hp).toIdeal ↔
      p ∈ x.asHomogeneousIdeal.toIdeal ∧
        ∀ j : Fin 4, pderiv j p ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [ProjectiveSpectrum.mem_zeroLocus]
  change (cubicJacobianIdeal p hp).toIdeal ≤ x.asHomogeneousIdeal.toIdeal ↔
    p ∈ x.asHomogeneousIdeal.toIdeal ∧
      ∀ j : Fin 4, pderiv j p ∈ x.asHomogeneousIdeal.toIdeal
  simp only [cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
    HomogeneousIdeal.toIdeal_iSup, sup_le_iff, iSup_le_iff]
  change (Ideal.span {p} ≤ x.asHomogeneousIdeal.toIdeal ∧
    ∀ j : Fin 4, Ideal.span {pderiv j p} ≤ x.asHomogeneousIdeal.toIdeal) ↔ _
  simp only [Ideal.span_le, Set.singleton_subset_iff]
  rfl

/-- This map is proper INTERNALLY, over every commutative coefficient ring. -/
theorem cubicJacobianProjection_isProper
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) :
    IsProper (toBase (cubicJacobianIdeal p hp)) := inferInstance

/-- The actual derivative-image is closed, with no closedness/properness input. -/
theorem cubicJacobianProjection_range_isClosed
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) :
    IsClosed (Set.range (toBase (cubicJacobianIdeal p hp))) := by
  simpa only [Set.image_univ] using
    (toBase (cubicJacobianIdeal p hp)).isClosedMap Set.univ isClosed_univ

/-- Its image is literally the projection of the projective common-zero locus
of p and the four partials, not the nonsmooth locus with a new name. -/
theorem cubicJacobianProjection_range_eq_projectiveZeroLocus_image
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) :
    Set.range (toBase (cubicJacobianIdeal p hp)) =
      ambientToBase '' ProjectiveSpectrum.zeroLocus
        (homogeneousSubmodule (Fin 4) R) (cubicJacobianIdeal p hp).toIdeal := by
  let I := cubicJacobianIdeal p hp
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨quotientProjMap I z, ?_, ?_⟩
    · rw [← range_quotientProjMap I]
      exact Set.mem_range_self z
    · exact congrArg (fun m : scheme I ⟶ Spec (.of R) => m z) (quotientProjMap_toBase I)
  · rintro ⟨x, hx, hxy⟩
    rw [← range_quotientProjMap I] at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨z, ?_⟩
    exact (congrArg (fun m : scheme I ⟶ Spec (.of R) => m z) (quotientProjMap_toBase I)).symm.trans hxy

end AllCharacteristics

