import PfaffianDescent.SchemeModulePointIncrementCohomology
import PfaffianDescent.SchemeModuleFinitePointSequenceBalance

/-! Both actual point induction steps preserve finite original-K H0/H1.
The full weighted residue degree is derived from the actual intrinsic fiber.
Finite H0/H1 of L are explicit generic induction inputs. No desired new-term
finiteness, exactness, dimension or scalar comparison is supplied.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual positive point induction, including ordinary rank-one
geometry of the new coefficient, finite H0/H1 and weighted H0-H1 change. -/
theorem schemeModuleClosedPoint_positiveIncrement_finite_and_h0_h1_change
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) (L : X.Modules)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let T := schemeModuleTensor L (SchemeModuleInternalHom.dual M)
    Module.Finite K (SchemeModuleOpenSectionsOver pi L ⊤) →
    Module.Finite K (schemeModuleCohomology X L 1) →
    schemeModuleLocallyRankOne T ∧
      Module.Finite K (SchemeModuleOpenSectionsOver pi T ⊤) ∧
      Module.Finite K (schemeModuleCohomology X T 1) ∧
      (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X T 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X L 1) + pi.residueDegree P.1 := by
  classical
  dsimp only
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let T := schemeModuleTensor L (SchemeModuleInternalHom.dual M)
  intro h0 h1
  have hM' : schemeModuleLocallyRankOne M := hM
  have hT : schemeModuleLocallyRankOne T := schemeModuleLocallyRankOne_tensor L
    (SchemeModuleInternalHom.dual M) hL (schemeModuleLocallyRankOne_dual M hM')
  let deltaL := schemeModuleRankOneTensorDualIncrement (closedImmersionModuleToUnit i) L
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
  obtain ⟨hz, hS, _hf, _hex0, _hex1, _hex2, _hsurj⟩ :=
    schemeModuleClosedPoint_positiveIncrement_lowDegreeExact pi P L hM hL
  let S := ShortComplex.mk deltaL eta hz
  obtain ⟨hF, hdimF⟩ := schemeModuleLocallyRankOne_closedPoint_fiberTop_finite_and_finrank pi P T hT
  have hv : Subsingleton (schemeModuleCohomology X S.X₃ 1) :=
    schemeModuleResiduePointPushforward_cohomology_succ_subsingleton P
      ((Scheme.Modules.pullback i).obj T) 0
  have h := schemeModuleShortExact_finite_second_and_h0_h1_balance pi S hS h0 h1 hF hv
  have hi : (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) +
      Module.finrank K (schemeModuleCohomology X L 1) =
    (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) +
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) +
      Module.finrank K (schemeModuleCohomology X T 1) := by exact_mod_cast h.2.2
  have hd : (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) : ℤ) =
      (pi.residueDegree P.1 : ℤ) := by exact_mod_cast hdimF
  exact ⟨hT, h.1, h.2.1, by
    change (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X T 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X L 1) + (pi.residueDegree P.1 : ℤ)
    omega⟩

/-- Actual negative point induction, including ordinary rank-one
geometry of the new coefficient, finite H0/H1 and weighted H0-H1 change. -/
theorem schemeModuleClosedPoint_negativeIncrement_finite_and_h0_h1_change
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) (L : X.Modules)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let R := schemeModuleTensor M L
    Module.Finite K (SchemeModuleOpenSectionsOver pi L ⊤) →
    Module.Finite K (schemeModuleCohomology X L 1) →
    schemeModuleLocallyRankOne R ∧
      Module.Finite K (SchemeModuleOpenSectionsOver pi R ⊤) ∧
      Module.Finite K (schemeModuleCohomology X R 1) ∧
      (Module.finrank K (SchemeModuleOpenSectionsOver pi R ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X R 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X L 1) - pi.residueDegree P.1 := by
  classical
  dsimp only
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let R := schemeModuleTensor M L
  intro h0 h1
  have hM' : schemeModuleLocallyRankOne M := hM
  have hR : schemeModuleLocallyRankOne R := schemeModuleLocallyRankOne_tensor M L hM' hL
  let S0 := closedImmersionIdealTwistSequence i L
  let beta := S0.f ≫ (schemeModuleTensorUnitLeftIso L).hom
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
  obtain ⟨hz, hS, _hf, _hex0, _hex1, _hex2, _hsurj⟩ :=
    schemeModuleClosedPoint_negativeIncrement_lowDegreeExact pi P L hL
  let S := ShortComplex.mk beta eta hz
  obtain ⟨hF, hdimF⟩ := schemeModuleLocallyRankOne_closedPoint_fiberTop_finite_and_finrank pi P L hL
  have hv : Subsingleton (schemeModuleCohomology X S.X₃ 1) :=
    schemeModuleResiduePointPushforward_cohomology_succ_subsingleton P
      ((Scheme.Modules.pullback i).obj L) 0
  have h := schemeModuleShortExact_finite_first_and_h0_h1_balance pi S hS h0 h1 hF hv
  have hi : (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) +
      Module.finrank K (schemeModuleCohomology X R 1) =
    (Module.finrank K (SchemeModuleOpenSectionsOver pi R ⊤) : ℤ) +
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) +
      Module.finrank K (schemeModuleCohomology X L 1) := by exact_mod_cast h.2.2
  have hd : (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) : ℤ) =
      (pi.residueDegree P.1 : ℤ) := by exact_mod_cast hdimF
  exact ⟨hR, h.1, h.2.1, by
    change (Module.finrank K (SchemeModuleOpenSectionsOver pi R ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X R 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi L ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X L 1) - (pi.residueDegree P.1 : ℤ)
    omega⟩

end PfaffianDescent.Coray
