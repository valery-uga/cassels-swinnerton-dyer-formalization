import PfaffianDescent.CanonicalPointIntrinsicComparisonData
import PfaffianDescent.PointPrincipalCechNormalizedComparison
import PfaffianDescent.PointPrincipalCechCohomologyComparison

/-! # The canonical point pullback with its computed principal residue cocycle -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped nonZeroDivisors
namespace PfaffianDescent
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u
set_option backward.isDefEq.respectTransparency false in
theorem exists_closedFieldPointCanonicalRestriction_principal_residue_cocycle
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [hExt : HasExt.{u} X.Modules]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hU : IsAffineOpen U) (hx : i default ∈ U) (q f : Γ(X, U))
    (hqmax : X.presheaf.germ U (i default) hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)))
    (hfmax : X.presheaf.germ U (i default) hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ i default →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (hqreg : X.presheaf.germ U (i default) hx q ∈ (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U (i default) hx q})
        (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸ Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    (Y : X.Modules) (y : Y.val.obj (op U)) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (i default)
    ∀ (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap
        i (i default)) = Ideal.span
          ({X.presheaf.germ U (i default) hx q, X.presheaf.germ U (i default) hx f} : Set _)),
    let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
      (X.presheaf.germ U (i default) hx q) (X.presheaf.germ U (i default) hx f) hkernel
    let s : Fin 3 → PointAdaptedAffineCover.PrincipalIndex X (i default) :=
      ![Sum.inr none, Sum.inl 0, Sum.inl 1]
    let W : X.Opens := ∏ᶜ fun k : Fin 3 => PointAdaptedAffineCover.principalOpens U (i default) q f (s k)
    let Vq : X.Opens := ∏ᶜ ![U, X.basicOpen q]
    let Vf : X.Opens := ∏ᶜ ![U, X.basicOpen f]
    let jq : Vq ⟶ U := Pi.π ![U, X.basicOpen q] 0
    let jf : Vf ⟶ U := Pi.π ![U, X.basicOpen f] 0
    let kq : W ⟶ Vq := PointAdaptedAffineCover.principalTripleFaceToPair U (i default) q f s 2
    let kf : W ⟶ Vf := PointAdaptedAffineCover.principalTripleFaceToPair U (i default) q f s 1
    ∃ (uq : Γ(X, Vq)) (uf : Γ(X, Vf))
      (z : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf
        (PointAdaptedAffineCover.principalOpens U (i default) q f)).d 3 2) (Y := Y)),
      X.presheaf.map jq.op q * uq = 1 ∧
      X.presheaf.map jf.op f * uf = 1 ∧
      (Ext.mk₀ (C := X.Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
        (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit X.ringCatSheaf)
          V hV eV U hx q f qM haway hqreg hfreg Y y) (zero_add 2) =
        schemeCoverDegreeTwoToCohomology (PointAdaptedAffineCover.principalOpens U (i default) q f)
          (PointAdaptedAffineCover.principalOpens_coversTop U (i default) hx (fieldPoint_image_isClosed i) q f) Y z ∧
      Sigma.ι (fun g : Fin 3 → PointAdaptedAffineCover.PrincipalIndex X (i default) =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 3 =>
          PointAdaptedAffineCover.principalOpens U (i default) q f (g k))) s ≫ z.1 =
        sectionRepresenterAugmentation X.ringCatSheaf W Y
          ((X.presheaf.map kq.op uq * X.presheaf.map kf.op uf) • Y.val.map (kq ≫ jq).op y) := by
  dsimp only
  letI := schemeModuleStalkModule (show X.Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  intro hkernel
  obtain ⟨b₁, b₂, zold, hb₁, hb₂, hb₃, hzold, hext⟩ :=
    exists_closedFieldPointCanonicalRestriction_intrinsic_comparison_data
      i V hV eV U hU hx q f haway hqreg hfreg Y y hkernel
  obtain ⟨uq, uf, lifts, a₂, huq, huf, ha₁, ha₂, ha₃, hcoef⟩ :=
    PointAdaptedAffineCover.exists_principal_normalized_chain_comparison
      U hU (i default) hx q f hqreg hfreg haway
  let C := sectionRepresenterCechChain X.ringCatSheaf
    (PointAdaptedAffineCover.principalOpens U (i default) q f)
  let z : DegreeTwoCocycle (C.d 3 2) (Y := Y) :=
    ⟨a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y, by
      change C.d 3 2 ≫ (a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y) = 0
      rw [← Category.assoc, ha₃, zero_comp]⟩
  have hcompare := PointAdaptedAffineCover.principal_comparison_intrinsic_class_eq_adapted
    U hU (i default) hx (fieldPoint_image_isClosed i) q f hqmax hfmax hqreg hfreg haway
      Y y b₁ b₂ hb₁ hb₂ lifts a₂ ha₁ ha₂ zold z hzold rfl
  refine ⟨uq, uf, z, huq, huf, hext.trans hcompare, ?_⟩
  change _ ≫ (a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y) = _
  rw [← Category.assoc, hcoef, sectionRepresenterOverlapScalar_comp_augmentation]

end PfaffianDescent
