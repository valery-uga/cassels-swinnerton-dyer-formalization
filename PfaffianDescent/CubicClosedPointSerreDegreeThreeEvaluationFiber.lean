import PfaffianDescent.CubicClosedPointSerreFreeNeighborhood

/-! # The actual rank-two pullback at a field-valued point -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual rank-two cover constructs a literal free rank-two pullback
at a field-valued point; no fiber coordinate is an input. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationFiber_exists_freeIso
    {L : Type u} [Field L] {X : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (j : Spec (.of L) ⟶ X) :
    Nonempty (SheafOfModules.free (R := (Spec (.of L)).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅ (Scheme.Modules.pullback j).obj (show X.Modules from e.E)) := by
  have hx : j default ∈ ⨆ i, C.U i := by rw [C.covers]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hrange : Set.range j ⊆ Set.range (C.U i).ι := by
    rintro x ⟨y, rfl⟩
    have hy : y = default := Subsingleton.elim _ _
    subst y
    exact ⟨⟨j default, hi⟩, rfl⟩
  let jU := IsOpenImmersion.lift (C.U i).ι j hrange
  have hj : jU ≫ (C.U i).ι = j := IsOpenImmersion.lift_fac _ _ _
  let eU := localFreeIsoOfOver (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i) ≪≫
    (Scheme.Modules.overFunctorEquiv (C.U i)).app (show X.Modules from e.E)
  exact ⟨pullbackFreeIso jU (ULift.{u} (Fin 2)) eU ≪≫
    (Scheme.Modules.pullback jU).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (C.U i).ι).app (show X.Modules from e.E)) ≪≫
    (Scheme.Modules.pullbackComp jU (C.U i).ι).app (show X.Modules from e.E) ≪≫
    (Scheme.Modules.pullbackCongr hj).app (show X.Modules from e.E)⟩

end PfaffianDescent
