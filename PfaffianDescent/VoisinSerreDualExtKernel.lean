import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.VoisinSerreDualKernelSelection
import PfaffianDescent.VoisinTwistEquivalenceSerreTerms

/-!
# Transporting Voisin's dual restriction kernel to Ext

The linear-algebra input in Voisin's Serre construction is a nonzero
functional on the sections of the finite subscheme which kills restricted
quadrics.  The homological input is a nonzero degree-two Ext class whose
contravariant image on the middle twist vanishes.

This file records the exact naturality square which relates the two and
proves that, once the two Serre-duality identifications have been
constructed, the required Ext class and the resulting nonzero Ext-one class
follow formally.  In particular, no choice of a representative of the
functional or of the Ext class is left implicit.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u v w

namespace PfaffianDescent

/-- A compatible pair of additive Serre-duality identifications for a map
`g : M ⟶ Q`.  Contravariance of Ext turns `g` into the upper horizontal map;
duality turns a section restriction `V ⟶ W` into the lower horizontal map.
The last field is precisely the naturality square needed in Voisin's
argument. -/
structure SerreDualExtKernelComparison
    (K V W : Type*) [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (M Q Y : C) (g : M ⟶ Q) (restriction : V →ₗ[K] W) where
  quotientEquiv : Ext.{w} Q Y 2 ≃+ Module.Dual K W
  middleEquiv : Ext.{w} M Y 2 ≃+ Module.Dual K V
  naturality : ∀ z : Ext.{w} Q Y 2,
    middleEquiv ((Ext.mk₀ g).comp z (zero_add 2)) =
      restriction.dualMap (quotientEquiv z)

/-- Transport a compatible Serre-duality square backwards through an exact
categorical equivalence.  This is the form used to remove an invertible
twist from all three sheaves while retaining the actual Ext classes and the
contravariant map between them. -/
noncomputable def SerreDualExtKernelComparison.transportExactEquivalence
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{w} D]
    [EnoughInjectives C]
    (E : C ≌ D) [E.functor.Additive]
    (M Q Y : C) (g : M ⟶ Q) (restriction : V →ₗ[K] W)
    (comparison : SerreDualExtKernelComparison K V W
      (E.functor.obj M) (E.functor.obj Q) (E.functor.obj Y)
      (E.functor.map g) restriction) :
    SerreDualExtKernelComparison K V W M Q Y g restriction where
  quotientEquiv :=
    (extAddEquivOfExactEquivalence E Q Y 2).trans comparison.quotientEquiv
  middleEquiv :=
    (extAddEquivOfExactEquivalence E M Y 2).trans comparison.middleEquiv
  naturality z := by
    change comparison.middleEquiv
        (extAddEquivOfExactEquivalence E M Y 2
          ((Ext.mk₀ g).comp z (zero_add 2))) = _
    rw [extAddEquivOfExactEquivalence_precomp]
    exact comparison.naturality _

/-- Transport a compatible Serre-duality square through an exact
equivalence and chosen concrete models of the three transported objects.
The square hypothesis records that the concrete quotient map is exactly the
transport of the original one. -/
noncomputable def SerreDualExtKernelComparison.transportExactEquivalenceOfIsos
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{w} D]
    [EnoughInjectives C]
    (E : C ≌ D) [E.functor.Additive]
    (M Q Y : C) (g : M ⟶ Q)
    (M' Q' Y' : D) (g' : M' ⟶ Q')
    (eM : E.functor.obj M ≅ M') (eQ : E.functor.obj Q ≅ Q')
    (eY : E.functor.obj Y ≅ Y')
    (hsquare : E.functor.map g ≫ eQ.hom = eM.hom ≫ g')
    (restriction : V →ₗ[K] W)
    (comparison : SerreDualExtKernelComparison K V W
      M' Q' Y' g' restriction) :
    SerreDualExtKernelComparison K V W M Q Y g restriction where
  quotientEquiv :=
    (extAddEquivOfExactEquivalenceOfIsos E Q Y Q' Y' eQ eY 2).trans
      comparison.quotientEquiv
  middleEquiv :=
    (extAddEquivOfExactEquivalenceOfIsos E M Y M' Y' eM eY 2).trans
      comparison.middleEquiv
  naturality z := by
    change comparison.middleEquiv
        (extAddEquivOfExactEquivalenceOfIsos E M Y M' Y' eM eY 2
          ((Ext.mk₀ g).comp z (zero_add 2))) = _
    rw [extAddEquivOfExactEquivalenceOfIsos_precomp E g g' eM eQ eY hsquare]
    exact comparison.naturality _

/-- A nonzero functional in the kernel of the dual restriction map gives a
nonzero Ext-two class in the kernel of contravariant precomposition. -/
theorem SerreDualExtKernelComparison.exists_nonzero_extTwo_kernel
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {M Q Y : C} {g : M ⟶ Q} {restriction : V →ₗ[K] W}
    (comparison : SerreDualExtKernelComparison K V W M Q Y g restriction)
    (phi : Module.Dual K W) (hphi : phi ≠ 0)
    (hkernel : restriction.dualMap phi = 0) :
    ∃ z : Ext.{w} Q Y 2,
      z ≠ 0 ∧ (Ext.mk₀ g).comp z (zero_add 2) = 0 := by
  let z := comparison.quotientEquiv.symm phi
  have hz : z ≠ 0 := by
    intro hz0
    apply hphi
    have h := congrArg comparison.quotientEquiv hz0
    simpa [z] using h
  refine ⟨z, hz, ?_⟩
  apply comparison.middleEquiv.injective
  rw [comparison.naturality, comparison.quotientEquiv.apply_symm_apply,
    hkernel]
  exact (map_zero comparison.middleEquiv).symm

/-- Nonsurjectivity of the section restriction map therefore produces the
required nonzero Ext-two kernel class. -/
theorem SerreDualExtKernelComparison.exists_nonzero_extTwo_kernel_of_not_surjective
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {M Q Y : C} {g : M ⟶ Q} {restriction : V →ₗ[K] W}
    (comparison : SerreDualExtKernelComparison K V W M Q Y g restriction)
    (hnot : ¬ Function.Surjective restriction) :
    ∃ z : Ext.{w} Q Y 2,
      z ≠ 0 ∧ (Ext.mk₀ g).comp z (zero_add 2) = 0 := by
  obtain ⟨phi, hphi, hkernel⟩ :=
    exists_nonzero_dualMap_kernel_of_not_surjective restriction hnot
  exact comparison.exists_nonzero_extTwo_kernel phi hphi hkernel

/-- Specialization to the quotient map in a twisted closed-immersion ideal
sequence.  This is the exact Ext-two datum consumed by the kernel form of
Serre's construction. -/
theorem closedImmersionIdealTwist_exists_nonzeroExtTwo_kernel_of_serreDualComparison
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules)
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [HasExt.{u} X.Modules]
    (restriction : V →ₗ[K] W)
    (comparison : SerreDualExtKernelComparison K V W
      (closedImmersionIdealTwistSequence i L).X₂
      (closedImmersionIdealTwistSequence i L).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      (closedImmersionIdealTwistSequence i L).g restriction)
    (hnot : ¬ Function.Surjective restriction) :
    ∃ z : Ext.{u} (closedImmersionIdealTwistSequence i L).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      z ≠ 0 ∧
        (Ext.mk₀ (closedImmersionIdealTwistSequence i L).g).comp z
          (zero_add 2) = 0 :=
  comparison.exists_nonzero_extTwo_kernel_of_not_surjective hnot

/-- With finite-colimit preservation as well, the same comparison produces
the nonzero Ext-one class defining the Serre extension. -/
theorem closedImmersionIdealTwist_exists_nonzeroExtOne_of_serreDualComparison
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules)
    (hlim : PreservesFiniteLimits (schemeModuleTensorRight L))
    (hcol : PreservesFiniteColimits (schemeModuleTensorRight L))
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [HasExt.{u} X.Modules]
    (restriction : V →ₗ[K] W)
    (comparison : SerreDualExtKernelComparison K V W
      (closedImmersionIdealTwistSequence i L).X₂
      (closedImmersionIdealTwistSequence i L).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      (closedImmersionIdealTwistSequence i L).g restriction)
    (hnot : ¬ Function.Surjective restriction) :
    ∃ x : Ext.{u} (closedImmersionIdealTwist i L)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1,
      x ≠ 0 := by
  letI : PreservesFiniteLimits (schemeModuleTensorRight L) := hlim
  letI : PreservesFiniteColimits (schemeModuleTensorRight L) := hcol
  obtain ⟨z, hz, hnext⟩ :=
    closedImmersionIdealTwist_exists_nonzeroExtTwo_kernel_of_serreDualComparison
      i L restriction comparison hnot
  obtain ⟨x, hx, _⟩ :=
    closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo_of_comp_eq_zero
      i L (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      z hz hnext
  exact ⟨x, hx⟩

end PfaffianDescent

namespace PfaffianDescent.ProjectiveNegativeTwist

open MvPolynomial AllCharacteristics AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

/- Transport an untwisted negative-`m` Serre-duality comparison through the
proved positive/negative twist equivalence.  The concrete object
identifications and the quotient-map square are supplied by
`VoisinTwistEquivalenceSerreTerms`; hence no twist compatibility remains as
an input to this constructor. -/
noncomputable def quotientPositiveTwistSerreDualComparisonOfUntwisted
    {K : Type u} [Field K]
    {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    (m : ℕ)
    {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [HasExt.{u} (scheme I).Modules]
    (restriction : V →ₗ[K] W)
    (comparison : SerreDualExtKernelComparison K V W
      (show (scheme I).Modules from
        SheafOfModules.unit (scheme I).ringCatSheaf)
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf))
      (sheafOfModules (grading I) m)
      (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).g
      restriction) :
    SerreDualExtKernelComparison K V W
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) m)).X₂
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) m)).X₃
      (show (scheme I).Modules from
        SheafOfModules.unit (scheme I).ringCatSheaf)
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) m)).g
      restriction := by
  letI : EnoughInjectives (scheme I).Modules :=
    sheafOfModules_enoughInjectives (scheme I).ringCatSheaf
  letI : (quotientInverseTwistEquivalence I m).functor.Additive := by
    change (schemeModuleTensorRight
      (sheafOfModules (grading I) m)).Additive
    infer_instance
  exact SerreDualExtKernelComparison.transportExactEquivalenceOfIsos
    (quotientInverseTwistEquivalence I m)
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) m)).X₂
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) m)).X₃
    (show (scheme I).Modules from
      SheafOfModules.unit (scheme I).ringCatSheaf)
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) m)).g
    (show (scheme I).Modules from
      SheafOfModules.unit (scheme I).ringCatSheaf)
    ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf))
    (sheafOfModules (grading I) m)
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).g
    (quotientInverseTwistMiddleIso I i m)
    (quotientInverseTwistTargetIso I i m)
    (quotientInverseTwistUnitIso I m)
    (quotientInverseTwist_idealSequence_g_square I i m)
    restriction comparison

/-- Paper-facing reduction of the length-eleven Serre step.  The already
proved dimension count supplies nonsurjectivity, while the supplied
comparison is exactly the geometric Serre-duality naturality square.  Once
that square is instantiated, this theorem returns the nonzero Ext-one class
without any further hypothesis from Voisin. -/
theorem cubic_length_eleven_exists_nonzeroExtOne_of_serreDualComparison
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (equationIdeal p hp))
    [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))]
    [HasExt.{u} (scheme (equationIdeal p hp)).Modules]
    (hlen : finiteSchemeRank (i ≫ toBase (equationIdeal p hp)) = 11) :
    letI := finiteSchemeCoefficientAlgebra
      (i ≫ toBase (equationIdeal p hp))
    ∀ comparison : SerreDualExtKernelComparison K
      (grading (equationIdeal p hp) 2) Γ(Z, ⊤)
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₂
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₃
      (show (scheme (equationIdeal p hp)).Modules from
        SheafOfModules.unit (scheme (equationIdeal p hp)).ringCatSheaf)
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).g
      (finiteProjectiveClosedSubschemePositiveTwoRestrictionLinearMap
        (equationIdeal p hp) i),
      ∃ x : Ext.{u}
          (closedImmersionIdealTwist i
            (positiveSheafOfModules (grading (equationIdeal p hp)) 3))
          (show (scheme (equationIdeal p hp)).Modules from
            SheafOfModules.unit (scheme (equationIdeal p hp)).ringCatSheaf) 1,
        x ≠ 0 := by
  letI := finiteSchemeCoefficientAlgebra
    (i ≫ toBase (equationIdeal p hp))
  intro comparison
  apply closedImmersionIdealTwist_exists_nonzeroExtOne_of_serreDualComparison
    i (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
    (quotientPositiveTwist_tensorRight_preservesFiniteLimits
      (equationIdeal p hp) 3)
    (quotientPositiveTwist_tensorRight_preservesFiniteColimits
      (equationIdeal p hp) 3)
    (finiteProjectiveClosedSubschemePositiveTwoRestrictionLinearMap
      (equationIdeal p hp) i)
    comparison
  exact cubic_length_eleven_positiveTwoRestriction_not_surjective
    p hp hp0 i hlen

/- Paper-facing form in which the entire positive/negative twist transport
has been discharged.  Only the untwisted negative-three Serre-duality square
remains to be supplied. -/
theorem cubic_length_eleven_exists_nonzeroExtOne_of_untwistedSerreDualComparison
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (equationIdeal p hp))
    [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))]
    [HasExt.{u} (scheme (equationIdeal p hp)).Modules]
    (hlen : finiteSchemeRank (i ≫ toBase (equationIdeal p hp)) = 11) :
    letI := finiteSchemeCoefficientAlgebra
      (i ≫ toBase (equationIdeal p hp))
    SerreDualExtKernelComparison K
        (grading (equationIdeal p hp) 2) Γ(Z, ⊤)
        (show (scheme (equationIdeal p hp)).Modules from
          SheafOfModules.unit
            (scheme (equationIdeal p hp)).ringCatSheaf)
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf))
        (sheafOfModules (grading (equationIdeal p hp)) 3)
        (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).g
        (finiteProjectiveClosedSubschemePositiveTwoRestrictionLinearMap
          (equationIdeal p hp) i) →
      ∃ x : Ext.{u}
          (closedImmersionIdealTwist i
            (positiveSheafOfModules (grading (equationIdeal p hp)) 3))
          (show (scheme (equationIdeal p hp)).Modules from
            SheafOfModules.unit
              (scheme (equationIdeal p hp)).ringCatSheaf) 1,
        x ≠ 0 := by
  letI := finiteSchemeCoefficientAlgebra
    (i ≫ toBase (equationIdeal p hp))
  intro comparison
  exact cubic_length_eleven_exists_nonzeroExtOne_of_serreDualComparison
    p hp hp0 i hlen
    (quotientPositiveTwistSerreDualComparisonOfUntwisted
      (equationIdeal p hp) i 3
      (finiteProjectiveClosedSubschemePositiveTwoRestrictionLinearMap
        (equationIdeal p hp) i)
      comparison)

end PfaffianDescent.ProjectiveNegativeTwist
