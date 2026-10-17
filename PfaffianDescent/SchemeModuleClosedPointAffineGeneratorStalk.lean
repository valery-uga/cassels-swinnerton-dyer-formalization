import PfaffianDescent.CorayNormalizationClosedPointIdealStalk

/-! The SAME actual affine point-ideal equation generates the SAME
maximal ideal after taking its original stalk germ. The actual ideal
stalk range/localization theorem proves the equality; it is not an input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original affine generator's original germ generates the actual
maximal ideal. Only actual principality of the original affine ideal is
input; the germ/maximal-ideal comparison is proved from original maps. -/
theorem closedPointIdeal_affineGenerator_germ_maximalIdeal
    (X : Scheme.{u}) (P : closedPoints X) (V : X.affineOpens) (hPV : P.1 ∈ V.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ (m : M.val.obj (op V.1)),
      i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1)) →
      IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) = Ideal.span
        ({X.presheaf.germ V.1 P.1 hPV
          ((closedImmersionModuleToUnit i).val.app (op V.1) m)} :
            Set (X.presheaf.stalk P.1)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M P.1
  intro m hprincipal
  have hmap : (i.ker.ideal V).map (X.presheaf.germ V.1 P.1 hPV).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) :=
    (cubicClosedPointSerreZeroIdealStalk_range_eq_map i V P.1 hPV).symm.trans
      (Coray.closedPointIdeal_stalk_range_eq_maximalIdeal X P)
  calc
    _ = (i.ker.ideal V).map (X.presheaf.germ V.1 P.1 hPV).hom := hmap.symm
    _ = _ := by rw [hprincipal, Ideal.map_span, Set.image_singleton]

/-- On an integral scheme, the SAME regular affine generator has an
irreducible original germ. Nonzero follows from the actual germ injection,
and irreducibility from the internally proved maximal-ideal equality.
No DVR, uniformizer or valuation certificate is assumed. -/
theorem closedPointIdeal_affineRegularGenerator_germ_irreducible
    (X : Scheme.{u}) [IsIntegral X] (P : closedPoints X)
    (V : X.affineOpens) (hPV : P.1 ∈ V.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ (m : M.val.obj (op V.1)),
      @IsRegular (Γ(X, V.1)) inferInstance
        ((closedImmersionModuleToUnit i).val.app (op V.1) m) →
      i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1)) →
      Irreducible (X.presheaf.germ V.1 P.1 hPV
        ((closedImmersionModuleToUnit i).val.app (op V.1) m)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro m hreg hprincipal
  letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
  let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
  have hz : z ≠ 0 := isRegular_iff_ne_zero.mp hreg
  have hgz : X.presheaf.germ V.1 P.1 hPV z ≠ 0 := by
    intro he
    apply hz
    apply germ_injective_of_isIntegral X P.1 hPV
    exact he.trans (X.presheaf.germ V.1 P.1 hPV).hom.map_zero.symm
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    (X.presheaf.germ V.1 P.1 hPV z) hgz
    (closedPointIdeal_affineGenerator_germ_maximalIdeal X P V hPV m hprincipal)

end PfaffianDescent
