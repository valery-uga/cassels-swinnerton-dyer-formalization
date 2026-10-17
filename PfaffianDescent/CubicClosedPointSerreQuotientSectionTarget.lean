import PfaffianDescent.FiniteProjectiveProjectionFormula

/-! # The actual positive-three quotient at a closed cubic point

A field point lies in one native projective coordinate chart. The supported
projection formula and the actual positive-twist chart trivialization identify
the original twisted quotient sheaf with the pushforward of the point's unit.
No sheaf or section comparison is supplied as a premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The actual quotient sheaf for the positive cubic twist at a closed field
point is its literal unit-sheaf pushforward. -/
def cubicClosedPointSerreQuotientSection_targetIso
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i] :
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₃ ≅
    (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) := by
  let I := equationIdeal p hp
  let T := positiveSheafOfModules (grading I) 3
  have hcover : ∃ k : Fin 4, i default ∈ quotientCoordinateOpen I k := by
    have hx : i default ∈ (⨆ k : Fin 4, quotientCoordinateOpen I k) := by
      rw [quotientCoordinateOpen_iSup I]
      trivial
    exact Opens.mem_iSup.mp hx
  let k := Classical.choose hcover
  let U : (hypersurface p hp).Opens := quotientCoordinateOpen I k
  have hx : i default ∈ U := Classical.choose_spec hcover
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = default := Subsingleton.elim _ _
    rw [hz]
    exact ⟨⟨i default, hx⟩, rfl⟩
  let j : Spec (.of L) ⟶ (U : Scheme) := IsOpenImmersion.lift U.ι i hrange
  have hji : j ≫ U.ι = i := IsOpenImmersion.lift_fac U.ι i hrange
  letI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  let V : ULift.{u} (Fin 4) → (hypersurface p hp).Opens :=
    fun a => quotientCoordinateOpen I a.down
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    rw [Opens.coversTop_iff]
    change ⨆ a : ULift.{u} (Fin 4), quotientCoordinateOpen I a.down = ⊤
    rw [← quotientCoordinateOpen_iSup I]
    apply le_antisymm
    · exact iSup_le fun a => le_iSup (quotientCoordinateOpen I) a.down
    · exact iSup_le fun a => le_iSup_of_le (ULift.up a) le_rfl
  let eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    quotientCoordinatePositiveTwistUnitIso_all I k 3
  let eV : ∀ a, (SheafOfModules.overFunctor (hypersurface p hp).ringCatSheaf (V a)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver (hypersurface p hp).sheaf (V a))) :=
    fun a => overFunctorIsoUnit_of_restrictIsoUnit (V a)
      (quotientCoordinatePositiveTwistUnitIso_all I a.down 3)
  let E := closedImmersionIdealTwistTargetProjectionFormulaIso U j T eT V hV eV
  change schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T ≅ _
  exact (schemeModuleTensorRight T).mapIso
      ((Scheme.Modules.pushforwardCongr hji).symm.app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) ≪≫ E ≪≫
    (Scheme.Modules.pushforwardCongr hji).app
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)

end PfaffianDescent.ProjectiveNegativeTwist
