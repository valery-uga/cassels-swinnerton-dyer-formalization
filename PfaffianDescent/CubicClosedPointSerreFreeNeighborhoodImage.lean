import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodUnitExtension

/-! # Free neighborhoods inside a chart are actual ambient neighborhoods -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual free identification on an affine subopen of a chart transports
to an actual free identification on its ambient image open. -/
theorem cubicClosedPointSerreFreeNeighborhood_image
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (V : (U : Scheme).Opens)
    (hV : IsAffineOpen V)
    (t : SheafOfModules.free (R := (V : Scheme).ringCatSheaf) (ULift.{u} (Fin 2)) ≅
      (M.restrict U.ι).restrict V.ι) :
    IsAffineOpen (U.ι ''ᵁ V) ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over (U.ι ''ᵁ V))
        (ULift.{u} (Fin 2)) ≅ M.over (U.ι ''ᵁ V)) := by
  let W := U.ι ''ᵁ V
  let f : (V : Scheme) ⟶ X := V.ι ≫ U.ι
  have hrange : Set.range f = Set.range W.ι := by
    change Set.range (V.ι ≫ U.ι) = Set.range (U.ι ''ᵁ V).ι
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.range_ι]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let e : (V : Scheme) ≅ (W : Scheme) := IsOpenImmersion.isoOfRangeEq f W.ι hrange
  have he : e.inv ≫ f = W.ι := IsOpenImmersion.isoOfRangeEq_inv_fac f W.ι hrange
  have hW : IsAffineOpen W := by
    letI : IsAffine (V : Scheme) := hV
    exact IsAffine.of_isIso e.inv
  let R := Scheme.Modules.restrictFunctor e.inv
  letI : R.IsLeftAdjoint := by dsimp [R]; infer_instance
  let η := (Scheme.Modules.restrictUnitIso e.inv).symm
  let a := (Scheme.Modules.restrictFunctorComp V.ι U.ι).app M
  let b := (Scheme.Modules.restrictFunctorComp e.inv f).app M
  let c := (Scheme.Modules.restrictFunctorCongr he).app M
  let tw : SheafOfModules.free (R := (W : Scheme).ringCatSheaf) (ULift.{u} (Fin 2)) ≅
      M.restrict W.ι :=
    SheafOfModules.mapFreeIso R (ULift.{u} (Fin 2)) η ≪≫
      R.mapIso (t ≪≫ a.symm) ≪≫ b.symm ≪≫ c
  let F := (Scheme.Modules.overEquiv W).functor
  let d := BundleSectionZeroLocus.overEquivFreeIso (X := X) W (ULift.{u} (Fin 2))
  let z := (Scheme.Modules.overFunctorEquiv W).app M
  exact ⟨hW, ⟨F.preimageIso (d.symm ≪≫ tw ≪≫ z.symm)⟩⟩

/-- Point membership is preserved by the actual ambient-image transport. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_ambient_of_chart
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (x : U)
    (h : ∃ (V : (U : Scheme).Opens), x ∈ V ∧ IsAffineOpen V ∧
      Nonempty (SheafOfModules.free (R := (U : Scheme).ringCatSheaf.over V)
        (ULift.{u} (Fin 2)) ≅ (M.restrict U.ι).over V)) :
    ∃ (W : X.Opens), U.ι x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over W)
        (ULift.{u} (Fin 2)) ≅ M.over W) := by
  obtain ⟨V, hxV, hV, ⟨t⟩⟩ := h
  let F := (Scheme.Modules.overEquiv V).functor
  let a := BundleSectionZeroLocus.overEquivFreeIso (X := (U : Scheme)) V (ULift.{u} (Fin 2))
  let b := (Scheme.Modules.overFunctorEquiv V).app (M.restrict U.ι)
  let tv := a ≪≫ F.mapIso t ≪≫ b
  obtain ⟨hW, ht⟩ := cubicClosedPointSerreFreeNeighborhood_image M U V hV tv
  exact ⟨U.ι ''ᵁ V, ⟨x, hxV, rfl⟩, hW, ht⟩

end PfaffianDescent
