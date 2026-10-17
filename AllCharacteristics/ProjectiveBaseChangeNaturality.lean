import AllCharacteristics.PullbackRestriction
import AllCharacteristics.HypersurfaceCoefficientNaturality

/-!
# Naturality of the projective base-change identification

The canonical projective coefficient morphisms commute with equality transport.
The isomorphism from a coefficient-changed projective scheme to its actual
pullback commutes with further coefficient change and the actual restriction
map of pullbacks.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient morphisms commute with transport between equal homogeneous ideals. -/
theorem projectiveCoefficientMap_transport (f : R →+* S)
    (I I' : HomogeneousIdeal (homogeneousSubmodule σ R))
    (J J' : HomogeneousIdeal (homogeneousSubmodule σ S))
    (hf : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
    (hf' : I'.toIdeal.map (MvPolynomial.map f) = J'.toIdeal)
    (hI : I = I') (hJ : J = J') :
    eqToHom (congrArg scheme hJ) ≫ projectiveCoefficientMap f I' J' hf' =
      projectiveCoefficientMap f I J hf ≫ eqToHom (congrArg scheme hI) := by
  subst I'
  subst J'
  exact (Category.id_comp _).trans (Category.comp_id _).symm

variable (f : R →+* S) (g : S →+* T)
variable (I : HomogeneousIdeal (homogeneousSubmodule σ R))

/-- The actual restriction map from the composite coefficient fiber to the first fiber. -/
noncomputable def projectiveFiberRestriction :
    pullback (toBase I) (Spec.map (CommRingCat.ofHom (g.comp f))) ⟶
      pullback (toBase I) (Spec.map (CommRingCat.ofHom f)) :=
  pullbackRestriction (toBase I) (Spec.map (CommRingCat.ofHom f))
    (Spec.map (CommRingCat.ofHom (g.comp f))) (Spec.map (CommRingCat.ofHom g))
    (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

/-- Further coefficient restriction preserves the original projective total-space projection. -/
theorem projectiveFiberRestriction_fst :
    projectiveFiberRestriction f g I ≫ pullback.fst (toBase I) (Spec.map (CommRingCat.ofHom f)) =
      pullback.fst (toBase I) (Spec.map (CommRingCat.ofHom (g.comp f))) :=
  pullbackRestriction_fst _ _ _ _ _

/-- Its base projection is the prescribed coefficient-spectrum morphism. -/
theorem projectiveFiberRestriction_snd :
    projectiveFiberRestriction f g I ≫ pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom f)) =
      pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom (g.comp f))) ≫
        Spec.map (CommRingCat.ofHom g) :=
  pullbackRestriction_snd _ _ _ _ _

/-- Further coefficient restriction is an actual Cartesian base change. -/
theorem isPullback_projectiveFiberRestriction :
    IsPullback (projectiveFiberRestriction f g I)
      (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom (g.comp f))))
      (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom f))) (Spec.map (CommRingCat.ofHom g)) :=
  isPullback_pullbackRestriction _ _ _ _ _

variable (J : HomogeneousIdeal (homogeneousSubmodule σ S))
variable (K : HomogeneousIdeal (homogeneousSubmodule σ T))
variable (hf : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
variable (hg : J.toIdeal.map (MvPolynomial.map g) = K.toIdeal)

/-- The global projective base-change identification commutes with further coefficient change. -/
theorem projectiveBaseChangeIso_naturality :
    (projectiveBaseChangeIso (g.comp f) I K (coefficientIdeal_comp f g I J K hf hg)).hom ≫
      projectiveFiberRestriction f g I =
    projectiveCoefficientMap g J K hg ≫ (projectiveBaseChangeIso f I J hf).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, projectiveFiberRestriction_fst, projectiveBaseChangeIso_hom_fst,
      Category.assoc, projectiveBaseChangeIso_hom_fst, projectiveCoefficientMap_comp]
  · rw [Category.assoc, projectiveFiberRestriction_snd, ← Category.assoc,
      projectiveBaseChangeIso_hom_snd, Category.assoc, projectiveBaseChangeIso_hom_snd,
      projectiveCoefficientMap_toBase]

end HomogeneousProjective
end AllCharacteristics
