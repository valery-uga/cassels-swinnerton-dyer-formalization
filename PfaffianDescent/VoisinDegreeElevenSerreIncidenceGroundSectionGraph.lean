import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeProductChart

/-! # Actual graphs of ground-field section parameters -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (base : X ⟶ Spec (.of K)) (M : X.Modules)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
variable (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
variable (b : finiteDimensionalProjectiveChartRing K
  (SchemeModuleGlobalSectionsOver base M) j →+* K)
variable (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
  (SchemeModuleGlobalSectionsOver base M)) j) = RingHom.id K)

def serreIncidenceGroundSectionParameter :
    Spec (.of K) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M :=
  Spec.map (CommRingCat.ofHom b) ≫ finiteDimensionalProjectiveChartι K
    (SchemeModuleGlobalSectionsOver base M) j

include hb in
@[reassoc]
theorem serreIncidenceGroundSectionParameter_toBase :
    serreIncidenceGroundSectionParameter base M j b ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M = 𝟙 _ := by
  unfold serreIncidenceGroundSectionParameter
  change (Spec.map (CommRingCat.ofHom b) ≫ finiteDimensionalProjectiveChartι K
    (SchemeModuleGlobalSectionsOver base M) j) ≫
    finiteDimensionalProjectiveParametersToBase K (SchemeModuleGlobalSectionsOver base M) = _
  rw [Category.assoc, finiteDimensionalProjectiveChartι_toBase]
  have h := finiteDimensionalProjectiveChart_specMap_toBase j b (RingHom.id K) hb
  simpa using h

def serreIncidenceGroundSectionGraph :
    X ⟶ properFiniteIncidenceParameterSpace base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M) :=
  pullback.lift (𝟙 X) (base ≫ serreIncidenceGroundSectionParameter base M j b) (by
    rw [Category.id_comp, Category.assoc,
      serreIncidenceGroundSectionParameter_toBase base M j b hb, Category.comp_id])

@[reassoc (attr := simp)]
theorem serreIncidenceGroundSectionGraph_fst :
    serreIncidenceGroundSectionGraph base M j b hb ≫
      pullback.fst base (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
      𝟙 X := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem serreIncidenceGroundSectionGraph_snd :
    serreIncidenceGroundSectionGraph base M j b hb ≫
      pullback.snd base (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
      base ≫ serreIncidenceGroundSectionParameter base M j b := pullback.lift_snd _ _ _

variable {ι : Type u} (C : SchemeModuleFiniteFreeAffineCover M ι)

def serreIncidenceGroundSectionChartGraph (i : C.ι) :
    (C.U i : Scheme.{u}) ⟶ (C.projectiveSectionOpenCover base M).X (i,j) :=
  pullback.lift (𝟙 _) (((C.U i).ι ≫ base) ≫ Spec.map (CommRingCat.ofHom b)) (by
    change (C.U i).ι ≫ base =
      (((C.U i).ι ≫ base) ≫ Spec.map (CommRingCat.ofHom b)) ≫
        (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j ≫
          schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    rw [Category.assoc]
    change _ = ((C.U i).ι ≫ base) ≫
      (serreIncidenceGroundSectionParameter base M j b ≫
        schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    rw [serreIncidenceGroundSectionParameter_toBase base M j b hb, Category.comp_id])

@[reassoc (attr := simp)]
theorem serreIncidenceGroundSectionChartGraph_surface (i : C.ι) :
    serreIncidenceGroundSectionChartGraph base M j b hb C i ≫
      C.projectiveSectionOpenCoverToSurfaceChart base M (i,j) = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem serreIncidenceGroundSectionChartGraph_parameter (i : C.ι) :
    serreIncidenceGroundSectionChartGraph base M j b hb C i ≫
      C.projectiveSectionOpenCoverToParameterChart base M (i,j) =
      ((C.U i).ι ≫ base) ≫ Spec.map (CommRingCat.ofHom b) :=
  pullback.lift_snd _ _ _

/-- The actual local graph is the restriction of the actual global graph. -/
theorem serreIncidenceGroundSectionChartGraph_comp (i : C.ι) :
    serreIncidenceGroundSectionChartGraph base M j b hb C i ≫
      (C.projectiveSectionOpenCover base M).f (i,j) =
    (C.U i).ι ≫ serreIncidenceGroundSectionGraph base M j b hb := by
  apply pullback.hom_ext
  · erw [Category.assoc, C.projectiveSectionOpenCover_f_comp_ambientFst base M (i,j)]
    simp only [SchemeModuleFiniteFreeAffineCover.projectiveSectionOpenCoverToSurface,
      ← Category.assoc, serreIncidenceGroundSectionChartGraph_surface base M j b hb C i,
      Category.id_comp]
    exact ((Category.assoc (C.U i).ι _ _).trans
      ((congrArg (fun q => (C.U i).ι ≫ q)
        (serreIncidenceGroundSectionGraph_fst base M j b hb)).trans
          (Category.comp_id _))).symm
  · erw [Category.assoc, C.projectiveSectionOpenCover_f_comp_ambientSnd base M (i,j)]
    simp only [← Category.assoc, serreIncidenceGroundSectionChartGraph_parameter base M j b hb C i]
    change (((C.U i).ι ≫ base) ≫ serreIncidenceGroundSectionParameter base M j b) = _
    exact (Category.assoc (C.U i).ι base _).trans
      (((Category.assoc (C.U i).ι _ _).trans
        (congrArg (fun q => (C.U i).ι ≫ q)
          (serreIncidenceGroundSectionGraph_snd base M j b hb))).symm)

end
end PfaffianDescent
