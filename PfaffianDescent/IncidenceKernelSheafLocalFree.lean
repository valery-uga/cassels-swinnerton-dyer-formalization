import PfaffianDescent.IncidenceOpenChartEquations
import PfaffianDescent.IncidenceOpenChartNaturality
import PfaffianDescent.SheafIsoSections
import PfaffianDescent.SheafFreeCover

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (K : Type u) [CommRing K] (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (U : (grassmannianScheme K 3 3).Opens) (hU : U ≤ (grassmannianChartι K σ).opensRange)

/-- Actual coordinates on the global kernel sheaf restricted to a Grassmannian chart. -/
noncomputable def incidenceKernelSheafChartCoordinates :
    (incidenceKernelSheaf K).over U ⟶
      (coordinateModuleSheaf (grassmannianScheme K 3 3) IncidenceFiberIndex).over U := by
  classical
  exact (incidenceKernelSheafι K).over U ≫
    coordinateModuleSheafOverMatrix (grassmannianScheme K 3 3) U _ _
      (incidenceFiberProjectionMatrix _ σ (incidenceOpenChartMatrix K σ U hU))

lemma incidenceKernelSheafChartCoordinates_sections (V : (Over U)ᵒᵖ)
    (x : ((incidenceKernelSheaf K).over U).val.obj V) :
    (incidenceKernelSheafChartCoordinates K σ U hU).val.app V x =
      incidenceKernelSheafOpenSectionsEquiv K σ V.unop.left ((leOfHom V.unop.hom).trans hU) x := by
  classical
  let ρ := regularFunctionRestrictFrom (grassmannianScheme K 3 3) U V.unop.left (leOfHom V.unop.hom)
  let c := (incidenceKernelSheafι K).val.app (op V.unop.left) x
  change Matrix.toLin' ((incidenceFiberProjectionMatrix _ σ (incidenceOpenChartMatrix K σ U hU)).map ρ) c = _
  have he := incidenceFiberProjectionMatrix_map ρ σ (incidenceOpenChartMatrix K σ U hU)
  have ht := incidenceOpenChartMatrix_restrict K σ U V.unop.left hU (leOfHom V.unop.hom)
  have hP : Matrix.toLin' ((incidenceFiberProjectionMatrix _ σ (incidenceOpenChartMatrix K σ U hU)).map ρ) =
      incidenceFiberProjection _ σ (incidenceOpenChartMatrix K σ V.unop.left ((leOfHom V.unop.hom).trans hU)) := by
    rw [he, ht, incidenceFiberProjectionMatrix_toLin]
  exact (congrArg (fun f => f c) hP).trans
    (incidenceKernelSheafOpenSectionsEquiv_apply K σ V.unop.left ((leOfHom V.unop.hom).trans hU) x).symm

/-- The global kernel sheaf is actually free of rank thirty-six on every Grassmannian chart. -/
noncomputable def incidenceKernelSheafChartIso :
    (incidenceKernelSheaf K).over U ≅
      (coordinateModuleSheaf (grassmannianScheme K 3 3) IncidenceFiberIndex).over U := by
  apply sheafIsoOfBijectiveSections ((grassmannianScheme K 3 3).ringCatSheaf.over U)
    (incidenceKernelSheafChartCoordinates K σ U hU)
  intro V
  let E := incidenceKernelSheafOpenSectionsEquiv K σ V.unop.left ((leOfHom V.unop.hom).trans hU)
  have he : (fun x => (incidenceKernelSheafChartCoordinates K σ U hU).val.app V x) = E :=
    funext (incidenceKernelSheafChartCoordinates_sections K σ U hU V)
  change Function.Bijective (fun x => (incidenceKernelSheafChartCoordinates K σ U hU).val.app V x)
  rw [he]
  exact E.bijective

noncomputable def incidenceKernelSheafChartFree :
    (incidenceKernelSheaf K).over U ≅
      SheafOfModules.free (R := (grassmannianScheme K 3 3).ringCatSheaf.over U) (ULift.{u} IncidenceFiberIndex) :=
  incidenceKernelSheafChartIso K σ U hU ≪≫ coordinateModuleSheafOverFree (grassmannianScheme K 3 3) U IncidenceFiberIndex

end
section
variable (K : Type u) [CommRing K]

lemma grassmannianChartOpens_coversTop :
    (Opens.grothendieckTopology (grassmannianScheme K 3 3)).CoversTop
      (fun σ : Equiv.Perm (Fin 3 ⊕ Fin 3) => (grassmannianChartι K σ).opensRange) :=
  (Opens.coversTop_iff _ _).mpr (by
    apply TopologicalSpace.IsOpenCover.mk
    apply le_antisymm le_top
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, y, hy⟩ := (grassmannianGlueData K 3 3).openCover.exists_eq x
    exact ⟨i.down, y, hy⟩)

/-- The actual incidence kernel sheaf on the Grassmannian is locally free. -/
instance incidenceKernelSheaf_isLocallyFree : (incidenceKernelSheaf K).IsLocallyFree :=
  sheaf_isLocallyFree_of_coverIso (grassmannianScheme K 3 3).ringCatSheaf (incidenceKernelSheaf K)
    (fun σ : Equiv.Perm (Fin 3 ⊕ Fin 3) => (grassmannianChartι K σ).opensRange)
    (grassmannianChartOpens_coversTop K) (fun _ => ULift.{u} IncidenceFiberIndex)
    (fun σ => (incidenceKernelSheafChartFree K σ (grassmannianChartι K σ).opensRange le_rfl).symm)

/-- The actual locally free kernel sheaf has thirty-six generators in each of its chart bases. -/
theorem incidenceKernelSheaf_local_rank_thirty_six :
    Fintype.card IncidenceFiberIndex = 36 ∧ ∀ σ : Equiv.Perm (Fin 3 ⊕ Fin 3), Nonempty
      ((incidenceKernelSheaf K).over (grassmannianChartι K σ).opensRange ≅
        SheafOfModules.free (R := (grassmannianScheme K 3 3).ringCatSheaf.over (grassmannianChartι K σ).opensRange)
          (ULift.{u} IncidenceFiberIndex)) :=
  ⟨incidenceFiberIndex_card, fun σ => ⟨incidenceKernelSheafChartFree K σ _ le_rfl⟩⟩

end
end PfaffianDescent
