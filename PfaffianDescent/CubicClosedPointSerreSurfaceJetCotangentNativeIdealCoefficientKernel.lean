import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSectionHom

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open IdealSheafDataModule BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every actual affine ideal-section inclusion has coefficient in the SAME literal ring kernel. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdealCoefficientKernel
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (t : SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶
      closedImmersionModule (Spec.map (CommRingCat.ofHom g))) :
    g ((affineGlobalSectionsUnitLinearEquiv (A := A))
      (unitEndomorphismValue (t ≫ closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom g))))) = 0 := by
  let e := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g
  let h := e.symm (t.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤)))
  have he := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv_toUnit g h
  rw [e.apply_symm_apply] at he
  have hc : unitEndomorphismValue (t ≫ closedImmersionModuleToUnit
      (Spec.map (CommRingCat.ofHom g))) =
      (affineGlobalSectionsUnitLinearEquiv (A := A)).symm h.1 := he
  rw [hc, LinearEquiv.apply_symm_apply]
  exact h.2

end PfaffianDescent
