import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentFiber

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
set_option backward.isDefEq.respectTransparency false

/-- The actual affine closed-immersion ideal is the SAME ideal sheaf as
that of the quotient by the literal original coordinate-ring kernel. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineIdeal_kernel_eq
    (g : A →+* B) :
    (Spec.map (CommRingCat.ofHom g)).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker g)))).ker := by
  rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
  congr 1
  ext x
  let φ := CommRingCat.ofHom g
  let ψ := CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker g))
  change (Spec.map φ).appTop.hom x = 0 ↔ (Spec.map ψ).appTop.hom x = 0
  have hφ := affineStructureToPushforwardUnit_globalKernel_mem_iff φ x
  have hψ := affineStructureToPushforwardUnit_globalKernel_mem_iff ψ x
  rw [LinearMap.mem_ker, affineStructureToPushforwardUnit_map_apply] at hφ hψ
  rw [hφ, hψ]
  exact (Ideal.Quotient.eq_zero_iff_mem).symm

/-- Native arbitrary affine closed immersion, compared with tilde of its SAME H. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineIdealTildeIso
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))] :
    IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)) ≅
      (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (RingHom.ker g)) :=
  eqToIso (congrArg IdealSheafDataModule.idealModule
    (cubicClosedPointSerreSurfaceJetCotangent_affineIdeal_kernel_eq g)) ≪≫
    (affineQuotientIdealTildeClosedImmersionModuleIso (RingHom.ker g)).symm

end PfaffianDescent
