import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineIdeal

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
variable {A : Type u} [CommRing A]
set_option backward.isDefEq.respectTransparency false

/-- The actual coordinate-ring map of an arbitrary closed immersion into
an affine chart. Its source is proved affine internally. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    A →+* Γ(Z, ⊤) := by
  letI : IsAffine Z := isAffine_of_isAffineHom i
  exact (Spec.preimage (Z.isoSpec.inv ≫ i)).hom

/-- Replacing the source by its actual canonical affine spectrum retains
the literal closed-immersion ideal sheaf. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersion_kernel_eq
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    (Spec.map (CommRingCat.ofHom
      (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap i))).ker = i.ker := by
  letI : IsAffine Z := isAffine_of_isAffineHom i
  change (Spec.map (Spec.preimage (Z.isoSpec.inv ≫ i))).ker = i.ker
  rw [Spec.map_preimage, Scheme.Hom.ker_comp_of_isIso]

/-- The actual arbitrary affine-chart closed ideal is the tilde module of
its actual coordinate-ring kernel. No quotient-source certificate is supplied. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionTildeIso
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IdealSheafDataModule.closedImmersionModule i ≅
      (tilde.functor (CommRingCat.of A)).obj
        (ModuleCat.of A (RingHom.ker
          (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap i))) := by
  letI : IsAffine Z := isAffine_of_isAffineHom i
  let g := cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap i
  have hg : Spec.map (CommRingCat.ofHom g) = Z.isoSpec.inv ≫ i := by
    change Spec.map (Spec.preimage (Z.isoSpec.inv ≫ i)) = _
    exact Spec.map_preimage _
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) := hg.symm ▸ inferInstance
  have he : IdealSheafDataModule.closedImmersionModule i =
      IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)) := by
    unfold IdealSheafDataModule.closedImmersionModule
    rw [cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersion_kernel_eq]
  exact eqToIso he ≪≫ cubicClosedPointSerreSurfaceJetCotangent_affineIdealTildeIso g

end PfaffianDescent
