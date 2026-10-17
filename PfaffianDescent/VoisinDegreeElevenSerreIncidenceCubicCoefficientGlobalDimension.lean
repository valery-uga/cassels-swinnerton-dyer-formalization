import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalSectionsIso

/-! # Native section dimension on the same coefficient-changed Serre bundle -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCubicCoefficientGlobalSections_finiteDimensional
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :
    FiniteDimensional F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) := by
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  letI := serreIncidenceGlobalSectionsField_finiteDimensional (L := F)
    (hypersurfaceToBase p hp) e C
  exact Module.Finite.equiv (serreIncidenceCubicCoefficientGlobalSectionsIso (F := F) p hp e.E)

theorem serreIncidenceCubicCoefficientGlobalSections_finrank
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :
    Module.finrank F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) =
    Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) := by
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  rw [← (serreIncidenceCubicCoefficientGlobalSectionsIso (F := F) p hp e.E).finrank_eq]
  exact serreIncidenceGlobalSectionsField_finrank (L := F) (hypersurfaceToBase p hp) e C

end PfaffianDescent
