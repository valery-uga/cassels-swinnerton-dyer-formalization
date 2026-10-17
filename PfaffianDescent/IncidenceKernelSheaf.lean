import PfaffianDescent.CoordinateModuleSheafMaps
import PfaffianDescent.CoordinateModuleSheafFree
import PfaffianDescent.IncidenceRestrictionMatrix
import PfaffianDescent.GrassmannianSmooth
import PfaffianDescent.SchemeAffineFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

/-- The universal graph matrix as global regular functions on its affine chart. -/
noncomputable def grassmannianChartRegularMatrix :
    Matrix (Fin 3) (Fin 3) Γ(grassmannianChartScheme K 3 3, ⊤) :=
  fun i j => affineFunctionHom (𝟙 (grassmannianChartScheme K 3 3)) (MvPolynomial.X (i, j))

/-- The regular-function matrix of the actual isotropy equations on a chart. -/
noncomputable def incidenceChartRestrictionMatrix (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    Matrix IncidenceEquationIndex AlternatingTripleIndex Γ(grassmannianChartScheme K 3 3, ⊤) :=
  incidenceRestrictionMatrix _ σ (grassmannianChartRegularMatrix K)

noncomputable abbrev incidenceChartEquationSheaf (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (grassmannianScheme K 3 3).Modules :=
  (Scheme.Modules.pushforward (grassmannianChartι K σ)).obj
    (coordinateModuleSheaf (grassmannianChartScheme K 3 3) IncidenceEquationIndex)

/-- The ambient forty-five coefficient functions restrict to the isotropy equations on each chart. -/
noncomputable def incidenceChartRestrictionSheafMap (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    coordinateModuleSheaf (grassmannianScheme K 3 3) AlternatingTripleIndex ⟶
      incidenceChartEquationSheaf K σ := by
  classical
  exact coordinateModuleSheafPull (grassmannianChartι K σ) AlternatingTripleIndex ≫
    (Scheme.Modules.pushforward (grassmannianChartι K σ)).map
      (coordinateModuleSheafMatrix (grassmannianChartScheme K 3 3) AlternatingTripleIndex
        IncidenceEquationIndex (incidenceChartRestrictionMatrix K σ))

/-- The chart restriction maps combined into a single morphism of actual sheaves. -/
noncomputable def incidenceRestrictionSheafMap :
    coordinateModuleSheaf (grassmannianScheme K 3 3) AlternatingTripleIndex ⟶
      ∏ᶜ (fun σ : Equiv.Perm (Fin 3 ⊕ Fin 3) => incidenceChartEquationSheaf K σ) :=
  Pi.lift (incidenceChartRestrictionSheafMap K)

/-- The actual sheaf of ambient triples satisfying every tautological isotropy equation. -/
noncomputable def incidenceKernelSheaf : (grassmannianScheme K 3 3).Modules :=
  kernel (incidenceRestrictionSheafMap K)

noncomputable def incidenceKernelSheafι :
    incidenceKernelSheaf K ⟶ coordinateModuleSheaf (grassmannianScheme K 3 3) AlternatingTripleIndex :=
  kernel.ι (incidenceRestrictionSheafMap K)

instance incidenceKernelSheafι_mono : Mono (incidenceKernelSheafι K) := by
  constructor
  intro Z f g h
  exact equalizer.hom_ext h

lemma incidenceKernelSheaf_equations (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceKernelSheafι K ≫ incidenceChartRestrictionSheafMap K σ = 0 := by
  have hp : incidenceRestrictionSheafMap K ≫ Pi.π (fun σ => incidenceChartEquationSheaf K σ) σ =
      incidenceChartRestrictionSheafMap K σ := Pi.lift_π _ _
  have hk : incidenceKernelSheafι K ≫ incidenceRestrictionSheafMap K = 0 :=
    kernel.condition (incidenceRestrictionSheafMap K)
  exact (congrArg (fun g => incidenceKernelSheafι K ≫ g) hp.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ Pi.π (fun σ => incidenceChartEquationSheaf K σ) σ) hk).trans
        (zero_comp)))

/-- The kernel sheaf has the universal property of the simultaneous actual isotropy equations. -/
noncomputable def incidenceKernelSheafLift (M : (grassmannianScheme K 3 3).Modules)
    (f : M ⟶ coordinateModuleSheaf (grassmannianScheme K 3 3) AlternatingTripleIndex)
    (h : ∀ σ, f ≫ incidenceChartRestrictionSheafMap K σ = 0) : M ⟶ incidenceKernelSheaf K :=
  kernel.lift (incidenceRestrictionSheafMap K) f (by
    apply Pi.hom_ext
    intro σ
    simpa only [Category.assoc, incidenceRestrictionSheafMap, Pi.lift_π, zero_comp] using h σ)

lemma incidenceKernelSheafLift_ι (M : (grassmannianScheme K 3 3).Modules)
    (f : M ⟶ coordinateModuleSheaf (grassmannianScheme K 3 3) AlternatingTripleIndex)
    (h : ∀ σ, f ≫ incidenceChartRestrictionSheafMap K σ = 0) :
    incidenceKernelSheafLift K M f h ≫ incidenceKernelSheafι K = f :=
  kernel.lift_ι _ _ _

end
end PfaffianDescent
