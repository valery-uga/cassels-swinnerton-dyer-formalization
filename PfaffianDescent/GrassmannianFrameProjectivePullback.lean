import PfaffianDescent.GrassmannianFrameProjectiveGluing

/-!
# Pulling back the global projective Grassmannian-frame family

Any family of homogeneous systems classified by the glued Grassmannian has
an actual relative projective family of its members.  Its equation-parameter
map is inherited from the global frame family.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable (K : Type u) [CommRing K] {m n : ℕ}
variable {τ : Type} [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The relative projective family classified by a morphism to the
Grassmannian of homogeneous systems. -/
noncomputable def grassmannianFrameProjectiveFamilyPullback
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) : Scheme.{u} :=
  pullback (grassmannianFrameProjectiveToGrassmannian K d e) f

/-- Projection of the pulled-back family to its parameter scheme. -/
noncomputable def grassmannianFrameProjectiveFamilyPullbackToBase
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    grassmannianFrameProjectiveFamilyPullback K d e f ⟶ X :=
  pullback.snd _ _

/-- The member of the ambient equation space represented by a point of a
pulled-back Grassmannian family. -/
noncomputable def grassmannianFrameProjectiveFamilyPullbackToGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    grassmannianFrameProjectiveFamilyPullback K d e f ⟶
      projectiveParameters K τ d :=
  pullback.fst _ _ ≫ grassmannianFrameProjectiveToGlobalParameters K d e

/-- The pulled-back projective member lies over the classified
Grassmannian point. -/
theorem grassmannianFrameProjectiveFamilyPullback_condition
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    pullback.fst (grassmannianFrameProjectiveToGrassmannian K d e) f ≫
      grassmannianFrameProjectiveToGrassmannian K d e =
    grassmannianFrameProjectiveFamilyPullbackToBase K d e f ≫ f :=
  pullback.condition

/-- The pulled-back family is Cartesian over its classifying map. -/
theorem isPullback_grassmannianFrameProjectiveFamily
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    IsPullback
      (pullback.fst (grassmannianFrameProjectiveToGrassmannian K d e) f)
      (grassmannianFrameProjectiveFamilyPullbackToBase K d e f)
      (grassmannianFrameProjectiveToGrassmannian K d e) f :=
  IsPullback.of_hasPullback _ _

/-- Pulling a classified projective family back once more is canonically the
projective family classified by the composite map. -/
noncomputable def grassmannianFrameProjectiveFamilyPullback_baseChangeIso
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X) :
    pullback (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≅
      grassmannianFrameProjectiveFamilyPullback K d e (g ≫ f) :=
  pullbackLeftPullbackSndIso
    (grassmannianFrameProjectiveToGrassmannian K d e) f g

set_option backward.isDefEq.respectTransparency false in
/-- The base-change identification preserves the represented ambient
homogeneous equation. -/
theorem grassmannianFrameProjectiveFamilyPullback_baseChangeIso_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X) :
    (grassmannianFrameProjectiveFamilyPullback_baseChangeIso K d e f g).hom ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e (g ≫ f) =
      pullback.fst (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f := by
  simpa only [grassmannianFrameProjectiveFamilyPullbackToGlobalParameters,
    grassmannianFrameProjectiveFamilyPullback_baseChangeIso,
    grassmannianFrameProjectiveFamilyPullbackToBase] using
    (pullbackLeftPullbackSndIso_hom_fst_assoc
      (grassmannianFrameProjectiveToGrassmannian K d e) f g
      (grassmannianFrameProjectiveToGlobalParameters K d e))

/-- Transport a point between projective families classified by equal
Grassmannian morphisms. -/
noncomputable def grassmannianFrameProjectiveFamilyPullbackPointCast
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    {f g : X ⟶ grassmannianScheme K m n} (h : f = g)
    (s : Y ⟶ grassmannianFrameProjectiveFamilyPullback K d e f) :
    Y ⟶ grassmannianFrameProjectiveFamilyPullback K d e g :=
  s ≫ eqToHom (congrArg
    (grassmannianFrameProjectiveFamilyPullback K d e) h)

/-- Casting the classifying morphism of a pulled-back family preserves its
projection to the common base. -/
theorem grassmannianFrameProjectiveFamilyPullbackPointCast_toBase
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    {f g : X ⟶ grassmannianScheme K m n} (h : f = g)
    (s : Y ⟶ grassmannianFrameProjectiveFamilyPullback K d e f) :
    grassmannianFrameProjectiveFamilyPullbackPointCast K d e h s ≫
        grassmannianFrameProjectiveFamilyPullbackToBase K d e g =
      s ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e f := by
  subst g
  simp [grassmannianFrameProjectiveFamilyPullbackPointCast]

/-- Casting the classifying morphism of a pulled-back family preserves its
represented ambient homogeneous equation. -/
theorem grassmannianFrameProjectiveFamilyPullbackPointCast_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    {f g : X ⟶ grassmannianScheme K m n} (h : f = g)
    (s : Y ⟶ grassmannianFrameProjectiveFamilyPullback K d e f) :
    grassmannianFrameProjectiveFamilyPullbackPointCast K d e h s ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e g =
      s ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f := by
  subst g
  simp [grassmannianFrameProjectiveFamilyPullbackPointCast]

end PfaffianDescent
