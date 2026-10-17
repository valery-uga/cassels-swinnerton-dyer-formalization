import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualChosenChartSection
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalScalar
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualChosenMarkedRange
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundZeroKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSurfaceScaleCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedGraphSurface

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_chosen_quotient_nonzero
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X B Z₀ : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (hconst : Function.Surjective (affineFunctionHom base))
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover (show X.Modules from e.E) ι)
    (i : Z₀ ⟶ X) [IsClosedImmersion i]
    (hlocal : ∀ k, localSectionZeroIdealOfOver (C.U k) ι
      (C.trivialization k) e.canonicalSection = i.ker.comap (C.U k).ι)
    (cfg : B ⟶ Spec (.of K)) (marked : Fin 3 → (B ⟶ X))
    (hm : ∀ n, marked n ≫ base = cfg)
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))))
    (b : finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) j →+* K)
    (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) j) = RingHom.id K) :
    let M : X.Modules := e.E
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let zero := C.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero),
      s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ serreIncidenceGroundSectionParameter base M j b →
      ∀ n : Fin 3,
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) ∉ Set.range i →
      SheafOfModules.sectionsMap e.projection
        (e.E.unitHomEquiv (cubicClosedPointSerreFiniteZeroResidual_chosenChartSection base M j b)) ≠
        zeroSection N := by
  let M : X.Modules := e.E
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let zero := C.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  let t := serreIncidenceGroundSectionParameter base M j b
  let v₀ := cubicClosedPointSerreFiniteZeroResidual_chosenChartSection base M j b
  dsimp only
  intro s hsp n hout hzero
  obtain ⟨a,ha⟩ := cubicClosedPointSerreFiniteZeroResidual_projection_zero_scalar_canonical
    base e hconst v₀ hzero
  have hane : a ≠ 0 := by
    intro h
    apply cubicClosedPointSerreFiniteZeroResidual_chosenChartSection_nonzero base M j b
    change v₀ = 0
    rw [ha,h,zero_smul]
  have hk : zero.ker.comap (serreIncidenceGroundSectionGraph base M j b hb) = i.ker := by
    apply serreIncidenceGroundSectionGraph_kernel_eq base M j b hb v₀
      (fun k => (cubicClosedPointSerreFiniteZeroResidual_chosenChartSection_coordinates base M j b k).symm) C i
    intro k
    rw [ha]
    exact (serreIncidenceSurfaceSectionZeroIdeal_smul_unit base M (C.U k) ι
      (localFreeIsoOfOver (C.U k) ι (C.trivialization k)) a (isUnit_iff_ne_zero.mpr hane)
      (e.inclusion : SchemeModuleGlobalSectionsOver base M)).trans (hlocal k)
  have ht : t ≫ pp = 𝟙 _ := serreIncidenceGroundSectionParameter_toBase base M j b hb
  let gr := serreIncidenceGroundSectionGraph base M j b hb
  let v := serreIncidenceClosedGraphZeroIso base pp t ht gr
    (serreIncidenceGroundSectionGraph_fst base M j b hb)
    (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk
  have hv := serreIncidenceClosedGraphZeroIso_hom_snd base pp t ht gr
    (serreIncidenceGroundSectionGraph_fst base M j b hb)
    (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk
  have hvi := serreIncidenceClosedGraphZeroIso_hom_surface base pp t ht gr
    (serreIncidenceGroundSectionGraph_fst base M j b hb)
    (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk
  exact hout (cubicClosedPointSerreFiniteZeroResidual_chosenMarked_mem_surface_range
    cfg base pp marked hm zero s t (i ≫ base) i v hv hvi
    (Spec.map (CommRingCat.ofHom (algebraMap K E))) hsp n (IsLocalRing.closedPoint E))

end PfaffianDescent
