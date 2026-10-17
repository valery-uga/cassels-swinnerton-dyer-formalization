import PfaffianDescent.SchemeModuleGlobalSections

/-!
# Finite parameterized combinations of scheme-module sections

The universal member of a finite-dimensional linear system is locally a
finite sum of basis sections multiplied by regular coefficient functions.
This file packages that construction for genuine sections of a scheme
module, after pullback to an arbitrary parameter chart.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open BundleSectionZeroLocus

universe u v

noncomputable section

/-- Sum a finite family of compatible sheaf sections by summing their
representing morphisms out of the unit module. -/
noncomputable def sumSections
    {X : Scheme.{u}} {E : X.Modules} {ι : Type v} [Fintype ι]
    (s : ι → E.sections) : E.sections := by
  let E' : SheafOfModules.{u} X.ringCatSheaf := E
  exact E'.unitHomEquiv (∑ i, E'.unitHomEquiv.symm (s i))

/-- The morphism representing a finite sum is the sum of the representing
morphisms. -/
@[simp]
theorem sumSections_unitHomEquiv_symm
    {X : Scheme.{u}} {E : X.Modules} {ι : Type v} [Fintype ι]
    (s : ι → E.sections) :
    E.unitHomEquiv.symm (sumSections s) =
      let E' : SheafOfModules.{u} X.ringCatSheaf := E
      ∑ i, E'.unitHomEquiv.symm (s i) := by
  let E' : SheafOfModules.{u} X.ringCatSheaf := E
  change E'.unitHomEquiv.symm (sumSections s) =
    ∑ i, E'.unitHomEquiv.symm (s i)
  simp only [sumSections]
  rw [Equiv.symm_apply_apply]

/-- Scalar multiplication distributes over a finite sum of module
sections.  This is the finite-dimensional analogue of
`scaleSection_addSections`, and is the form needed for projective linear
systems with an arbitrary finite basis. -/
theorem scaleSection_sumSections
    {X : Scheme.{u}} {E : X.Modules} {ι : Type v} [Fintype ι]
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : ι → E.sections) :
    scaleSection a (sumSections s) =
      sumSections (fun i => scaleSection a (s i)) := by
  apply E.unitHomEquiv.symm.injective
  simp only [scaleSection, sumSections, Equiv.symm_apply_apply]
  exact Preadditive.comp_sum (C := X.Modules) Finset.univ a
    (fun i => E.unitHomEquiv.symm (s i))

set_option backward.isDefEq.respectTransparency false in
/-- Mapping a finite sum of sections along a module morphism maps each
summand. -/
theorem sectionsMap_sumSections
    {X : Scheme.{u}} {E F : X.Modules} {ι : Type v} [Fintype ι]
    (g : E ⟶ F) (s : ι → E.sections) :
    SheafOfModules.sectionsMap g (sumSections s) =
      sumSections (fun i => SheafOfModules.sectionsMap g (s i)) := by
  apply F.unitHomEquiv.symm.injective
  have h₀ := (E.unitHomEquiv_symm_comp (sumSections s) g).symm
  have h₁ := sumSections_unitHomEquiv_symm s
  have hsum := Preadditive.sum_comp (C := X.Modules) Finset.univ
    (fun i => E.unitHomEquiv.symm (s i)) g
  simp_rw [E.unitHomEquiv_symm_comp] at hsum
  have h₂ := sumSections_unitHomEquiv_symm
    (fun i => SheafOfModules.sectionsMap g (s i))
  exact h₀.trans ((congrArg (fun z => z ≫ g) h₁).trans
    (hsum.trans h₂.symm))

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of a finite sum of module sections is the finite sum of their
pullbacks. -/
theorem pullbackSection_sumSections
    {X Y : Scheme.{u}} (f : X ⟶ Y) {E : Y.Modules}
    (hunit : IsIso (pullbackUnitComparison f))
    {ι : Type v} [Fintype ι] (s : ι → E.sections) :
    pullbackSection f E hunit (sumSections s) =
      sumSections (fun i => pullbackSection f E hunit (s i)) := by
  letI : IsIso (pullbackUnitComparison f) := hunit
  let P := Scheme.Modules.pullback f
  let a := inv (pullbackUnitComparison f)
  apply (P.obj E).unitHomEquiv.symm.injective
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  rw [sumSections_unitHomEquiv_symm
    (fun i => pullbackSection f E hunit (s i))]
  simp_rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  change a ≫ P.map (E.unitHomEquiv.symm (sumSections s)) =
    ∑ i, a ≫ P.map (E.unitHomEquiv.symm (s i))
  rw [sumSections_unitHomEquiv_symm s, Functor.map_sum]
  exact Preadditive.comp_sum (C := X.Modules) Finset.univ a
    (fun i => P.map (E.unitHomEquiv.symm (s i)))

/-- A finite linear combination of sections with scalar endomorphism
coefficients. -/
noncomputable def finiteLinearCombinationSections
    {X : Scheme.{u}} {E : X.Modules} {ι : Type v} [Fintype ι]
    (a : ι → (schemeModuleUnit X ⟶ schemeModuleUnit X))
    (s : ι → E.sections) : E.sections :=
  sumSections (fun i => scaleSection (a i) (s i))

/-- A common scalar multiplying every coefficient multiplies the resulting
finite linear combination by that same scalar. -/
theorem finiteLinearCombinationSections_commonScale
    {X : Scheme.{u}} {E : X.Modules} {ι : Type v} [Fintype ι]
    (u : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (a : ι → (SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf))
    (s : ι → E.sections) :
    scaleSection u (finiteLinearCombinationSections a s) =
      finiteLinearCombinationSections (fun i => u ≫ a i) s := by
  unfold finiteLinearCombinationSections
  rw [scaleSection_sumSections]
  congr 1
  funext i
  exact scaleSection_scaleSection _ _ _

/-- A finite family of genuine global sections on `X`, pulled to `U` and
combined using regular coefficient functions on `U`.  This is the local
universal-section construction on a parameter chart. -/
noncomputable def parameterizedSchemeModuleSection
    {K : Type u} [Field K] {X U : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι]
    (f : U ⟶ X) (coeff : ι → Γ(U, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    ((Scheme.Modules.pullback f).obj M).sections :=
  finiteLinearCombinationSections
    (fun i => unitEndomorphismOfRegularFunction (coeff i))
    (fun i => pullbackSection f M (isIso_pullbackUnitComparison f)
      (schemeModuleGlobalSectionsOverEquivSections base M (s i)))

/-- The representing morphism of a parameterized section is the finite sum
of the pulled-back basis-section morphisms with their regular coefficients. -/
theorem parameterizedSchemeModuleSection_unitHomEquiv_symm
    {K : Type u} [Field K] {X U : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι]
    (f : U ⟶ X) (coeff : ι → Γ(U, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    ((Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
        (parameterizedSchemeModuleSection base M f coeff s) =
      let E' : SheafOfModules.{u} U.ringCatSheaf :=
        (Scheme.Modules.pullback f).obj M
      ∑ i, E'.unitHomEquiv.symm
        (scaleSection (unitEndomorphismOfRegularFunction (coeff i))
          (pullbackSection f M (isIso_pullbackUnitComparison f)
            (schemeModuleGlobalSectionsOverEquivSections base M (s i)))) := by
  exact sumSections_unitHomEquiv_symm _

/-- A coordinate in a finite free trivialization sends a finite sum of
sections to the corresponding sum of scalar coordinates. -/
theorem BundleSectionZeroLocus.sectionCoordinateOfFreeIso_sumSections
    {X : Scheme.{u}} {E : X.Modules} {ι : Type v} [Fintype ι]
    (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : ι → E.sections) (a : I) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso I e (sumSections s) a =
      ∑ i, BundleSectionZeroLocus.sectionCoordinateOfFreeIso I e (s i) a := by
  unfold BundleSectionZeroLocus.sectionCoordinateOfFreeIso
  have hmap := sectionsMap_sumSections e.inv s
  rw [hmap]
  unfold BundleSectionZeroLocus.freeSectionCoordinate
  have hsum := sumSections_unitHomEquiv_symm
    (fun i => SheafOfModules.sectionsMap e.inv (s i))
  rw [hsum, Preadditive.sum_comp]
  let t : ι → (SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) := fun i =>
    (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.inv (s i)) ≫
      BundleSectionZeroLocus.freeCoordinateMap I a
  change BundleSectionZeroLocus.unitEndomorphismValue (X := X) (∑ i, t i) =
    ∑ i, BundleSectionZeroLocus.unitEndomorphismValue (X := X) (t i)
  have hsum (q : Finset ι) :
      BundleSectionZeroLocus.unitEndomorphismValue (X := X)
          (∑ i ∈ q, t i) =
        ∑ i ∈ q, BundleSectionZeroLocus.unitEndomorphismValue (X := X) (t i) := by
    classical
    induction q using Finset.induction_on with
    | empty => simp [BundleSectionZeroLocus.unitEndomorphismValue_zero]
    | insert b q hb ih =>
        simp only [Finset.sum_insert, hb, not_false_eq_true,
          BundleSectionZeroLocus.unitEndomorphismValue_add, ih]
  simpa [t] using hsum Finset.univ

/-- A free coordinate of a finite linear combination is the corresponding
linear combination of the free coordinates. -/
theorem BundleSectionZeroLocus.sectionCoordinateOfFreeIso_finiteLinearCombinationSections
    {X : Scheme.{u}} {E : X.Modules} {ι : Type v} [Fintype ι]
    (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (coeff : ι → Γ(X, ⊤)) (s : ι → E.sections) (a : I) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso I e
        (finiteLinearCombinationSections
          (fun i => BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
            (coeff i)) s) a =
      ∑ i, coeff i *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso I e (s i) a := by
  unfold finiteLinearCombinationSections
  rw [BundleSectionZeroLocus.sectionCoordinateOfFreeIso_sumSections]
  apply Finset.sum_congr rfl
  intro i hi
  rw [BundleSectionZeroLocus.sectionCoordinateOfFreeIso_scale,
    BundleSectionZeroLocus.unitEndomorphismValue_ofRegularFunction]

/-- In a finite free trivialization, a parameterized section has the expected
coefficient-by-coordinate expansion. -/
theorem BundleSectionZeroLocus.sectionCoordinateOfFreeIso_parameterizedSchemeModuleSection
    {K : Type u} [Field K] {X U : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι]
    (f : U ⟶ X) (coeff : ι → Γ(U, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M)
    (I : Type u)
    (e : SheafOfModules.free (R := U.ringCatSheaf) I ≅
      (Scheme.Modules.pullback f).obj M)
    (a : I) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso I e
        (parameterizedSchemeModuleSection base M f coeff s) a =
      ∑ i, coeff i *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso I e
          (BundleSectionZeroLocus.pullbackSection f M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
            (schemeModuleGlobalSectionsOverEquivSections base M (s i))) a := by
  unfold parameterizedSchemeModuleSection
  exact BundleSectionZeroLocus.sectionCoordinateOfFreeIso_finiteLinearCombinationSections
    I e coeff _ a

end

end PfaffianDescent
