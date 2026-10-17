import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSurfaceBasisCoordinates

/-! # Actual invertible ground scaling preserves actual local section zero ideals -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

lemma serreIncidence_span_unit_mul {R : Type u} [CommRing R]
    {ι : Type*} (c : R) (hc : IsUnit c) (g : ι → R) :
    Ideal.span (Set.range fun i => c * g i) = Ideal.span (Set.range g) := by
  obtain ⟨v, rfl⟩ := hc
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Ideal.mul_mem_left (Ideal.span (Set.range fun i => (v : R) * g i))
      ((v⁻¹ : Rˣ) : R) (Ideal.subset_span ⟨i, rfl⟩)
    simpa only [SetLike.mem_coe, ← mul_assoc, Units.inv_mul, one_mul] using h

/-- Ground-field scaling is literal multiplication of the actual restricted
free coordinates by the corresponding constant regular function. -/
theorem serreIncidenceSurfaceSectionCoordinate_smul
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (U : X.Opens) (ι : Type u) [Fintype ι] [DecidableEq ι]
    (t : SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) ι ≅
      (Scheme.Modules.overEquiv U).functor.obj (M.over U))
    (a : K) (s : SchemeModuleGlobalSectionsOver base M) (i : ι) :
    sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
      (schemeModuleGlobalSectionsOverEquivSections base M (a • s))) i =
    affineFunctionHom (U.ι ≫ base) a *
      sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
        (schemeModuleGlobalSectionsOverEquivSections base M s)) i := by
  have hs := serreIncidenceSurfaceBasisCoordinate_reconstruct base M U ι t (a • s) i
  have ht := serreIncidenceSurfaceBasisCoordinate_reconstruct base M U ι t s i
  rw [affineFunctionHom_comp]
  have hsum : (∑ k, U.ι.appTop (affineFunctionHom base
      ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr (a • s) k)) *
      sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
        (schemeModuleGlobalSectionsOverEquivSections base M
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) i) =
    U.ι.appTop (affineFunctionHom base a) *
      (∑ k, U.ι.appTop (affineFunctionHom base
        ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s k)) *
        sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
          (schemeModuleGlobalSectionsOverEquivSections base M
            (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact hs.symm.trans (hsum.trans (congrArg (fun z =>
    U.ι.appTop (affineFunctionHom base a) * z) ht))

/-- The actual local zero ideal is unchanged by an invertible ground scalar. -/
theorem serreIncidenceSurfaceSectionZeroIdeal_smul_unit
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (U : X.Opens) (ι : Type u) [Fintype ι] [DecidableEq ι]
    (t : SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) ι ≅
      (Scheme.Modules.overEquiv U).functor.obj (M.over U))
    (a : K) (ha : IsUnit a) (s : SchemeModuleGlobalSectionsOver base M) :
    sectionZeroIdealOfFreeIso ι t (restrictSectionToOpen U
      (schemeModuleGlobalSectionsOverEquivSections base M (a • s))) =
    sectionZeroIdealOfFreeIso ι t (restrictSectionToOpen U
      (schemeModuleGlobalSectionsOverEquivSections base M s)) := by
  unfold sectionZeroIdealOfFreeIso freeSectionZeroIdeal
  apply congrArg Scheme.IdealSheafData.ofIdealTop
  have h : (fun i => sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
      (schemeModuleGlobalSectionsOverEquivSections base M (a • s))) i) =
    (fun i => affineFunctionHom (U.ι ≫ base) a *
      sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
        (schemeModuleGlobalSectionsOverEquivSections base M s)) i) := by
    funext i
    exact serreIncidenceSurfaceSectionCoordinate_smul base M U ι t a s i
  change Ideal.span (Set.range _) = Ideal.span (Set.range _)
  exact (congrArg (fun q => Ideal.span (Set.range q)) h).trans
    (serreIncidence_span_unit_mul _ (ha.map (affineFunctionHom (U.ι ≫ base))) _)

end PfaffianDescent
