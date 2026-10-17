import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionFrame

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Actual E-linear combination of ORIGINAL canonical Fin9 sections pulled
along the literal twice-coefficient composite, on the SAME coefficient cubic. -/
def pointSplittingCubicSerreGroundChosenSection_originalCombinationMap
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9) :
    (E ⊗[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) →ₗ[E]
    SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
        ((hp.map (algebraMap K F)).map (algebraMap F E)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
          (p.map (algebraMap K F)) (hp.map (algebraMap K F)) ≫
          cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) := by
  let b := Module.finBasisOfFinrankEq K
    (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9
  exact (b.baseChange E).constr E (fun i =>
    serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
        ((hp.map (algebraMap K F)).map (algebraMap F E)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
        (p.map (algebraMap K F)) (hp.map (algebraMap K F)) ≫
        cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) e.E (b i))

/-- The linear-combination operator is literally the sum of the Q-coordinate
scalars times the original canonical section pullbacks. -/
theorem pointSplittingCubicSerreGroundChosenSection_originalCombinationMap_apply
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (v : E ⊗[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) :
    pointSplittingCubicSerreGroundChosenSection_originalCombinationMap (F := F) p hp e h9 v =
    ∑ i : Fin 9,
      ((Module.finBasisOfFinrankEq K
        (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9).baseChange E).repr v i •
      serreActualPulledGlobalSection (hypersurfaceToBase p hp)
        (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
          ((hp.map (algebraMap K F)).map (algebraMap F E)))
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
          (p.map (algebraMap K F)) (hp.map (algebraMap K F)) ≫
          cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) e.E
        (Module.finBasisOfFinrankEq K
          (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9 i) := by
  rw [pointSplittingCubicSerreGroundChosenSection_originalCombinationMap, Module.Basis.constr_apply]
  exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)

end PfaffianDescent
