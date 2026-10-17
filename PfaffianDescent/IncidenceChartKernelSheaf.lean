import PfaffianDescent.IncidenceFiberLinearNaturality
import PfaffianDescent.CoordinateModuleSheafMaps
import PfaffianDescent.CoordinateModuleSheafFree
import PfaffianDescent.SheafIsoSections

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (X : Scheme.{u}) (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (T : Matrix (Fin 3) (Fin 3) Γ(X, ⊤))

/-- Restriction to a graph of regular functions, as a morphism of actual sheaves. -/
noncomputable def incidenceGraphRestrictionSheaf :
    coordinateModuleSheaf X AlternatingTripleIndex ⟶ coordinateModuleSheaf X IncidenceEquationIndex := by
  classical
  exact coordinateModuleSheafMatrix X _ _ (incidenceRestrictionMatrix Γ(X, ⊤) σ T)

/-- The free-coordinate projection, as a morphism of actual sheaves. -/
noncomputable def incidenceGraphProjectionSheaf :
    coordinateModuleSheaf X AlternatingTripleIndex ⟶ coordinateModuleSheaf X IncidenceFiberIndex := by
  classical
  exact coordinateModuleSheafMatrix X _ _ (incidenceFiberProjectionMatrix Γ(X, ⊤) σ T)

lemma incidenceGraphRestrictionSheaf_sections (U : X.Opens) :
    ((incidenceGraphRestrictionSheaf X σ T).val.app (op U)).hom =
      incidenceRestrictionMap Γ(X, U) σ (T.map (regularFunctionRestrict X U)) := by
  classical
  change Matrix.toLin' ((incidenceRestrictionMatrix Γ(X, ⊤) σ T).map (regularFunctionRestrict X U)) = _
  exact (congrArg Matrix.toLin' (incidenceRestrictionMatrix_map (regularFunctionRestrict X U) σ T)).trans
    (incidenceRestrictionMatrix_toLin _ σ _)

lemma incidenceGraphProjectionSheaf_sections (U : X.Opens) :
    ((incidenceGraphProjectionSheaf X σ T).val.app (op U)).hom =
      incidenceFiberProjection Γ(X, U) σ (T.map (regularFunctionRestrict X U)) := by
  classical
  change Matrix.toLin' ((incidenceFiberProjectionMatrix Γ(X, ⊤) σ T).map (regularFunctionRestrict X U)) = _
  exact (congrArg Matrix.toLin' (incidenceFiberProjectionMatrix_map (regularFunctionRestrict X U) σ T)).trans
    (incidenceFiberProjectionMatrix_toLin _ σ _)

/-- Every open has the thirty-six actual graph-kernel coordinates. -/
noncomputable def incidenceGraphSheafKernelSectionEquiv (U : X.Opens) :
    ((incidenceGraphRestrictionSheaf X σ T).val.app (op U)).hom.ker ≃ₗ[X.ringCatSheaf.obj.obj (op U)]
      (coordinateModuleSheaf X IncidenceFiberIndex).val.obj (op U) := by
  classical
  change (Matrix.toLin' ((incidenceRestrictionMatrix Γ(X, ⊤) σ T).map (regularFunctionRestrict X U))).ker ≃ₗ[Γ(X, U)]
    (IncidenceFiberIndex → Γ(X, U))
  have he : Matrix.toLin' ((incidenceRestrictionMatrix Γ(X, ⊤) σ T).map (regularFunctionRestrict X U)) =
      incidenceRestrictionMap Γ(X, U) σ (T.map (regularFunctionRestrict X U)) :=
    incidenceGraphRestrictionSheaf_sections X σ T U
  exact (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker he)).trans
    (incidenceRestrictionFiberEquiv Γ(X, U) σ (T.map (regularFunctionRestrict X U)))

lemma incidenceGraphSheafKernelSectionEquiv_apply (U : X.Opens)
    (c : ((incidenceGraphRestrictionSheaf X σ T).val.app (op U)).hom.ker) :
    incidenceGraphSheafKernelSectionEquiv X σ T U c =
      (incidenceGraphProjectionSheaf X σ T).val.app (op U) c.1 := by
  have hc' : ((incidenceGraphRestrictionSheaf X σ T).val.app (op U)).hom c.1 = 0 := c.2
  have hc : incidenceRestrictionMap Γ(X, U) σ (T.map (regularFunctionRestrict X U)) c.1 = 0 :=
    (congrArg (fun f : (AlternatingTripleIndex → Γ(X, U)) →ₗ[Γ(X, U)] (IncidenceEquationIndex → Γ(X, U)) => f c.1)
      (incidenceGraphRestrictionSheaf_sections X σ T U)).symm.trans hc' 
  have he := incidenceFiberProjection_kernel Γ(X, U) σ (T.map (regularFunctionRestrict X U)) ⟨c.1, hc⟩
  exact he.symm.trans ((congrArg (fun f => f c.1)
    (incidenceGraphProjectionSheaf_sections X σ T U)).symm)

/-- The actual sheaf kernel of graph restriction is the free sheaf of rank thirty-six. -/
noncomputable def incidenceGraphKernelSheafIso :
    kernel (incidenceGraphRestrictionSheaf X σ T) ≅ coordinateModuleSheaf X IncidenceFiberIndex :=
  sheafKernelIsoOfSectionEquiv X.ringCatSheaf (incidenceGraphRestrictionSheaf X σ T)
    (incidenceGraphProjectionSheaf X σ T)
    (fun U => incidenceGraphSheafKernelSectionEquiv X σ T U.unop)
    (fun U c => incidenceGraphSheafKernelSectionEquiv_apply X σ T U.unop c)

noncomputable def incidenceGraphKernelSheafFree :
    kernel (incidenceGraphRestrictionSheaf X σ T) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} IncidenceFiberIndex) :=
  incidenceGraphKernelSheafIso X σ T ≪≫ coordinateModuleSheafFree X IncidenceFiberIndex

instance incidenceGraphKernelSheaf_isLocallyFree :
    (kernel (incidenceGraphRestrictionSheaf X σ T)).IsLocallyFree :=
  sheaf_isLocallyFree_of_freeIso X.ringCatSheaf _ _ (incidenceGraphKernelSheafFree X σ T).symm

end
end PfaffianDescent
