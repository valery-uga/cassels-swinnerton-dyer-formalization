import PfaffianDescent.SchemeModuleFixedFrameFunctionFieldShrinking
import PfaffianDescent.SchemeModuleClosedPointCanonicalFrameRestriction
import PfaffianDescent.SchemeModuleClosedPointDualStalkFunctionField

/-! SAME point-factor field maps on an actual smaller common complement.
Canonical chart restriction and genuine generic germs prove the comparison;
no field-map equality or image condition is input. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

/-- Negative factor coordinates on ANY actual common complement are the
SAME original ideal inclusion followed by the original generic germ. -/
theorem schemeModuleClosedPointIdealFixedComplementOpenToFunctionField_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C)
    (U : X.Opens) [Nonempty U] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ m : SchemeModuleOpenSectionsOver pi (closedImmersionModule i) U,
      (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi (closedImmersionModule i) C
          (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) U m : X.functionField) =
        X.germToFunctionField U ((closedImmersionModuleToUnit i).val.app (op U) m) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let j := closedImmersionModuleToUnit i
  let W : X.Opens := U ⊓ C
  letI : Nonempty W := ⟨⟨genericPoint X, generic_mem U, generic_mem C⟩⟩
  let f : W ⟶ U := homOfLE inf_le_left
  let g : W ⟶ C := homOfLE inf_le_right
  let e := schemeModuleClosedPointIdealOverCanonicalIso P C hPC
  intro m
  have hc : (e.hom.val.app (op (Over.mk g)) (M.val.map f.op m) : Γ(X, W)) =
      j.val.app (op W) (M.val.map f.op m) := rfl
  exact (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C e U m).trans
    ((congrArg (X.germToFunctionField W) hc).trans
      ((congrArg (X.germToFunctionField W) (PresheafOfModules.naturality_apply j.val f.op m)).trans
        (X.presheaf.germ_res_apply f (genericPoint X) (generic_mem W) _)))

/-- Positive factor coordinates on ANY actual nonempty common complement
are precisely the accepted canonical point local map, with the SAME
original-pi K actions. The complement restriction is derived internally. -/
theorem schemeModuleClosedPointDualFixedComplementOpenToFunctionField_eq_pointMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C)
    (U : X.Opens) [Nonempty U] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi D C
        (schemeModuleClosedPointDualOverCanonicalIso P C hPC) U =
      schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  let B := schemeClosedPointComplementOpen P
  letI : Nonempty B := ⟨⟨genericPoint X, schemeClosedPoint_generic_mem_complement P hP⟩⟩
  have hCB : C ≤ B := by
    intro y hy
    change y ≠ P.1
    intro he
    exact hPC (he ▸ hy)
  let f : C ⟶ B := homOfLE hCB
  let eB := schemeModuleClosedPointDualOverCanonicalIso P B (schemeClosedPoint_not_mem_complement P)
  have hC : SchemeModuleInternalHom.overUnitChartRestrict D f eB =
      schemeModuleClosedPointDualOverCanonicalIso P C hPC :=
    schemeModuleClosedPointDualOverCanonicalIso_restrict P f (schemeClosedPoint_not_mem_complement P)
  have hbase : schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi D B eB U =
      schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U := by
    let W : X.Opens := U ⊓ B
    letI : Nonempty W := ⟨⟨genericPoint X, generic_mem U,
      schemeClosedPoint_generic_mem_complement P hP⟩⟩
    change (schemeModuleChartSectionsToFunctionFieldLinearMap pi D W
        (SchemeModuleInternalHom.overUnitChartRestrict D
          (homOfLE (show W ≤ B from inf_le_right)) eB)).comp
        (schemeModuleOpenSectionsRestrictionLinearMap pi D (show W ≤ U from inf_le_left)) =
      (schemeModuleChartSectionsToFunctionFieldLinearMap pi D W
        (schemeModuleClosedPointDualOverCanonicalIso P W
          (fun h => schemeClosedPoint_not_mem_complement P h.2))).comp
        (schemeModuleOpenSectionsRestrictionLinearMap pi D (show W ≤ U from inf_le_left))
    rw [schemeModuleClosedPointDualOverCanonicalIso_restrict P
      (homOfLE (show W ≤ B from inf_le_right)) (schemeClosedPoint_not_mem_complement P)]
  exact (congrArg (fun e => schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi D C e U) hC).symm.trans
    ((schemeModuleFixedFrameOpenToFunctionFieldLinearMap_shrink pi D B C f eB U).trans hbase)

/-- The common-complement positive factor stalk map at its SAME center
is exactly the accepted canonical dual stalk map. Thus its genuine DVR
range theorem applies without a newly supplied frame comparison. -/
theorem schemeModuleClosedPointDualFixedComplementStalkToFunctionField_eq_pointMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    letI := schemeModuleStalkModule D P.1
    schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D C
        (schemeModuleClosedPointDualOverCanonicalIso P C hPC) P.1 =
      schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  letI := schemeModuleStalkModule D P.1
  apply LinearMap.ext
  intro a
  obtain ⟨U, hxU, m, rfl⟩ := D.presheaf.exists_germ_eq a
  letI : Nonempty U := ⟨⟨P.1, hxU⟩⟩
  exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi D C
    (schemeModuleClosedPointDualOverCanonicalIso P C hPC) P.1 U hxU m).trans
      ((DFunLike.congr_fun
        (schemeModuleClosedPointDualFixedComplementOpenToFunctionField_eq_pointMap pi P hP C hPC U) m).trans
          (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_germ pi P hP U hxU m).symm)

end PfaffianDescent
