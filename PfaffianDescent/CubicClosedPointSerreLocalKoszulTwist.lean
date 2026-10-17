import PfaffianDescent.CubicClosedPointSerreLocalKoszulSequence

/-! # The affine Koszul sequence with the actual twisted ideal endpoint -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
universe u
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- An actual source sequence, together with its prescribed ideal inclusion
factorization. The twist coordinate is the constructed tensor restriction
isomorphism, rather than an assumed kernel comparison. -/
structure CubicClosedPointSerreLocalKoszulData
    {X : Scheme.{u}} {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (U : X.Opens) (q f : Γ(X, U))
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) where
  last : (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
      SheafOfModules.unit (U : Scheme).ringCatSheaf) ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (closedImmersionIdealTwist i T)
  zero : cubicClosedPointSerreLocalKoszulFirst U q f ≫ last = 0
  shortExact : (ShortComplex.mk (cubicClosedPointSerreLocalKoszulFirst U q f)
    last zero).ShortExact
  last_inclusion : last ≫
      (schemeModuleTensorRestrictIsoOfLocalTrivialization U
        (IdealSheafDataModule.closedImmersionModule i) T eT).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i) =
    (cubicClosedPointSerreLocalKoszulPairUnitIso U).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (sectionRepresenterKoszulLast X.ringCatSheaf U q f) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U)

theorem cubicClosedPointSerreLocalKoszul_exists_data
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U))
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (hqreg : X.presheaf.germ U (i default) hx q ∈ (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U (i default) hx q})
      (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸ Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    (hmax : Ideal.span ({X.presheaf.germ U (i default) hx q,
      X.presheaf.germ U (i default) hx f} : Set _) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)))
    (haway : ∀ (y : X) (hy : y ∈ U), y ≠ i default →
      Ideal.span ({X.presheaf.germ U y hy q, X.presheaf.germ U y hy f} : Set _) = ⊤) :
    Nonempty (CubicClosedPointSerreLocalKoszulData i T U q f eT) := by
  let V : ULift.{u} (Fin 1) → X.Opens := fun _ => ⊤
  have hV : (Opens.grothendieckTopology X).CoversTop V := by
    apply (Opens.coversTop_iff X V).mpr
    exact TopologicalSpace.IsOpenCover.mk (by simp [V])
  let eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))) := fun _ => Iso.refl _
  obtain ⟨j, hz, hS, hj⟩ := cubicClosedPointSerreLocalKoszul_exists_untwistedSequence
    i V hV eV U hx q f hqreg hfreg hmax haway
  let a := schemeModuleTensorRestrictIsoOfLocalTrivialization U
    (IdealSheafDataModule.closedImmersionModule i) T eT
  let l := j ≫ a.inv
  have hzl : cubicClosedPointSerreLocalKoszulFirst U q f ≫ l = 0 := by
    simp only [l, ← Category.assoc, hz, zero_comp]
  let b : ShortComplex.mk (cubicClosedPointSerreLocalKoszulFirst U q f) j hz ≅
      ShortComplex.mk (cubicClosedPointSerreLocalKoszulFirst U q f) l hzl :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) a.symm (by simp) (by simp [l])
  refine ⟨⟨l, hzl, ShortComplex.shortExact_of_iso b hS, ?_⟩⟩
  change (j ≫ a.inv) ≫ a.hom ≫ _ = _
  simpa only [Category.assoc, a.inv_hom_id_assoc] using hj

end PfaffianDescent
