import PfaffianDescent.CorayCartierNativeHomCokernel

/-! Native Hom resolution of the actual intrinsic-normal residue tensor.
All maps are original precomposition, the native cokernel projection, and
the constructed OWN quotient comparisons. No global dualizing property.
SOURCE ONLY / UNVERIFIED. Root owns compiler and acceptance checks. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The native Hom cokernel projection agrees with the original residue
restriction and the actual intrinsic-normal quotient comparison. -/
theorem RegularPrincipalImmersion.actualCartierHomCokernelIntrinsicNormalIso_projection
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    cokernel.π (SchemeModuleInternalHom.precompose
        (IdealSheafDataModule.closedImmersionModuleToUnit i) W) ≫
      (H.actualCartierHomCokernelIntrinsicNormalIso W hW).hom =
    (SchemeModuleInternalHom.rankOneTensorHomIso
      (IdealSheafDataModule.closedImmersionModule i) W H.inverseCartierTwist_locallyRankOne).inv ≫
      (H.actualCartierResidueSequence W).g ≫
      (H.actualCartierResidueIntrinsicNormalTensorIso W hW).hom := by
  let f := SchemeModuleInternalHom.precompose
    (IdealSheafDataModule.closedImmersionModuleToUnit i) W
  let eC := H.actualCartierResidueHomCokernelIso W hW
  let eN := H.actualCartierResidueIntrinsicNormalTensorIso W hW
  let eH := SchemeModuleInternalHom.rankOneTensorHomIso
    (IdealSheafDataModule.closedImmersionModule i) W H.inverseCartierTwist_locallyRankOne
  change cokernel.π f ≫ (eC.hom ≫ eN.hom) =
    eH.inv ≫ ((H.actualCartierResidueSequence W).g ≫ eN.hom)
  calc
    cokernel.π f ≫ (eC.hom ≫ eN.hom) = (cokernel.π f ≫ eC.hom) ≫ eN.hom :=
      (Category.assoc _ _ _).symm
    _ = (eH.inv ≫ (H.actualCartierResidueSequence W).g) ≫ eN.hom :=
      congrArg (fun a => a ≫ eN.hom)
        (H.actualCartierResidueHomCokernelIso_projection W hW)
    _ = eH.inv ≫ ((H.actualCartierResidueSequence W).g ≫ eN.hom) :=
      Category.assoc _ _ _

/-- The actual Hom sequence ends in the SAME ambient pushforward of
the intrinsic-normal tensor. Its first map is literal ideal precomposition. -/
def RegularPrincipalImmersion.actualCartierIntrinsicNormalHomSequence
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) : ShortComplex X.Modules := by
  let f := SchemeModuleInternalHom.precompose
    (IdealSheafDataModule.closedImmersionModuleToUnit i) W
  let e := H.actualCartierHomCokernelIntrinsicNormalIso W hW
  let g := cokernel.π f ≫ e.hom
  have hz : f ≫ g = 0 := by
    calc
      f ≫ (cokernel.π f ≫ e.hom) = (f ≫ cokernel.π f) ≫ e.hom :=
        (Category.assoc _ _ _).symm
      _ = 0 ≫ e.hom := congrArg (fun a => a ≫ e.hom) (cokernel.condition f)
      _ = 0 := zero_comp
  exact ShortComplex.mk f g hz

/-- Genuine OWN residue geometry supplies an Iso of the actual residue
sequence with the native Hom sequence. Neither square is a premise. -/
def RegularPrincipalImmersion.actualCartierIntrinsicNormalHomSequenceIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    H.actualCartierResidueSequence W ≅
      H.actualCartierIntrinsicNormalHomSequence W hW := by
  let e0 := SchemeModuleInternalHom.unitTensorHomIso W
  let e1 := SchemeModuleInternalHom.rankOneTensorHomIso
    (IdealSheafDataModule.closedImmersionModule i) W H.inverseCartierTwist_locallyRankOne
  let e2 := H.actualCartierResidueIntrinsicNormalTensorIso W hW
  refine ShortComplex.isoMk e0 e1 e2
    (H.actualCartierResidueIncrement_hom_square W hW).symm ?_
  change e1.hom ≫
      (cokernel.π (SchemeModuleInternalHom.precompose
        (IdealSheafDataModule.closedImmersionModuleToUnit i) W) ≫
        (H.actualCartierHomCokernelIntrinsicNormalIso W hW).hom) =
    (H.actualCartierResidueSequence W).g ≫ e2.hom
  let Q : X.Modules := (H.actualCartierIntrinsicNormalHomSequence W hW).X₃
  have h1 : e1.hom ≫
      (cokernel.π (SchemeModuleInternalHom.precompose
        (IdealSheafDataModule.closedImmersionModuleToUnit i) W) ≫
        (H.actualCartierHomCokernelIntrinsicNormalIso W hW).hom) =
      e1.hom ≫ (e1.inv ≫ ((H.actualCartierResidueSequence W).g ≫ e2.hom)) :=
    congrArg
      (fun a : SchemeModuleInternalHom.sheaf
          (IdealSheafDataModule.closedImmersionModule i) W ⟶ Q => e1.hom ≫ a)
      (H.actualCartierHomCokernelIntrinsicNormalIso_projection W hW)
  have h2 : e1.hom ≫ (e1.inv ≫ ((H.actualCartierResidueSequence W).g ≫ e2.hom)) =
      (H.actualCartierResidueSequence W).g ≫ e2.hom :=
    e1.hom_inv_id_assoc ((H.actualCartierResidueSequence W).g ≫ e2.hom)
  exact h1.trans h2

/-- Short exactness of the SAME Hom/precomposition/pushforward sequence
is derived from the genuine OWN regular-principal residue sequence. -/
theorem RegularPrincipalImmersion.actualCartierIntrinsicNormalHomSequence_shortExact
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (H.actualCartierIntrinsicNormalHomSequence W hW).ShortExact :=
  ShortComplex.shortExact_of_iso (H.actualCartierIntrinsicNormalHomSequenceIso W hW)
    (H.actualCartierResidueSequence_shortExact W hW)

end PfaffianDescent
end
