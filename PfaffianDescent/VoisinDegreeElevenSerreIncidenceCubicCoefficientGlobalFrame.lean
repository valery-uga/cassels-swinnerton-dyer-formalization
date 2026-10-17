import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalSectionsIso

/-! # The coefficient-cubic section frame is the literal scalar extension of the old frame -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist Module
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceCubicCoefficientGlobalFrame
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))] :
    F ⊗[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E) ≃ₗ[F]
    SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj
          (show (hypersurface p hp).Modules from e.E)) := by
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  exact (serreIncidenceGlobalSectionsFieldFrame (L := F) (hypersurfaceToBase p hp) e C).trans
    (serreIncidenceCubicCoefficientGlobalSectionsIso p hp (show (hypersurface p hp).Modules from e.E))

def serreIncidenceCubicCoefficientGlobalBasis
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E)) = 9) :=
  ((finBasisOfFinrankEq K _ h9).baseChange F).map
    (serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C)

theorem serreIncidenceCubicCoefficientGlobalBasis_repr_tmul
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E)) = 9)
    (a : F) (s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E)) (i : Fin 9) :
    (serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9).repr
      (serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C (a ⊗ₜ[K] s)) i =
      algebraMap K F ((finBasisOfFinrankEq K _ h9).repr s i) * a := by
  let z := serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C
  change ((finBasisOfFinrankEq K _ h9).baseChange F).repr
    (z.symm (z (a ⊗ₜ[K] s))) i = _
  rw [z.symm_apply_apply, Basis.baseChange_repr_tmul]
  exact Algebra.smul_def _ _

end PfaffianDescent
