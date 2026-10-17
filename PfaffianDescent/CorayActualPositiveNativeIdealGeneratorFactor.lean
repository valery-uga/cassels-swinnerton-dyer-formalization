import PfaffianDescent.CorayActualPositiveNativeWholeGeneratorMatrix
import PfaffianDescent.CorayActualAmbientIdealPositiveNativeChart
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! Actual native epimorphic generator factor through the whole original
ideal tensored with O(m). SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The literal normalized generator, with codomain restricted to the OWN
scheme-theoretic quotient-chart kernel. The kernel includes all nilpotents. -/
def actualDegreeZeroChartGeneratorToQuotientKernel
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → PolyA) (hg : Ideal.span (Set.range g) = I.toIdeal) (j : Fin 4) :
    (ι → HomogeneousLocalization.Away PS (X j)) →ₗ[HomogeneousLocalization.Away PS (X j)]
      RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j) :=
  (actualDegreeZeroChartGeneratorMap j g).codRestrict _ (fun x => by
    rw [← actualDegreeZeroChartGeneratorMap_range_eq_quotientKernel I g hg j]
    exact LinearMap.mem_range_self _ x)

/-- Surjectivity comes from the actual range equality, not from a supplied
native sheaf or global section-surjectivity certificate. -/
theorem actualDegreeZeroChartGeneratorToQuotientKernel_surjective
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → PolyA) (hg : Ideal.span (Set.range g) = I.toIdeal) (j : Fin 4) :
    Function.Surjective (actualDegreeZeroChartGeneratorToQuotientKernel I g hg j) := by
  intro y
  have hy : y.val ∈ (actualDegreeZeroChartGeneratorMap j g).range := by
    rw [actualDegreeZeroChartGeneratorMap_range_eq_quotientKernel I g hg j]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem actualDegreeZeroChartGeneratorToQuotientKernel_subtype
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → PolyA) (hg : Ideal.span (Set.range g) = I.toIdeal) (j : Fin 4) :
    ModuleCat.ofHom (actualDegreeZeroChartGeneratorToQuotientKernel I g hg j) ≫
      ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype =
    ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g) := rfl

/-- The actual native generator factor has target the pullback of the OWN
ideal tensor O(m), not a transported or replacement kernel sheaf. -/
def actualPositiveNativeIdealGeneratorFactor
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → PolyA) (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (m : ℕ) (hm : ∀ i, d i ≤ m) (j : Fin 4) :
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
        (∐ fun i => positiveSheafOfModules PS (m - d i)) ⟶
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
        (schemeModuleTensor (IdealSheafDataModule.closedImmersionModule (quotientProjMap I))
          (positiveSheafOfModules PS m)) :=
  (actualPositiveNativeWholeGeneratorFrame (K := K) j d m).hom ≫
    (actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) ι).hom ≫
    (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map
      (ModuleCat.ofHom (actualDegreeZeroChartGeneratorToQuotientKernel I g hg j)) ≫
    (actualAmbientHomogeneousIdealPositiveNativeChartIso I j m).inv

/-- This native factor is epi: its only nonisomorphic factor is tilde of
the literal surjective normalized generator into the actual ideal kernel. -/
theorem actualPositiveNativeIdealGeneratorFactor_epi
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → PolyA) (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (m : ℕ) (hm : ∀ i, d i ≤ m) (j : Fin 4) :
    Epi (actualPositiveNativeIdealGeneratorFactor I g d hhom hg m hm j) := by
  let F := tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  let c := ModuleCat.ofHom (actualDegreeZeroChartGeneratorToQuotientKernel I g hg j)
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : Epi c := (ModuleCat.epi_iff_surjective c).mpr
    (actualDegreeZeroChartGeneratorToQuotientKernel_surjective I g hg j)
  letI : Epi (F.map c) := Functor.map_epi F c
  change Epi ((actualPositiveNativeWholeGeneratorFrame (K := K) j d m).hom ≫
    (actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) ι).hom ≫ F.map c ≫
      (actualAmbientHomogeneousIdealPositiveNativeChartIso I j m).inv)
  infer_instance

/-- The epimorphic factor followed by the ACTUAL native ideal-twist inclusion
is exactly the pullback of the original generator map. No comparison premise
is added; the full chart matrix and ideal-inclusion comparisons are derived. -/
theorem actualPositiveNativeIdealGeneratorFactor_inclusion
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → PolyA) (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (m : ℕ) (hm : ∀ i, d i ≤ m) (j : Fin 4) :
    actualPositiveNativeIdealGeneratorFactor I g d hhom hg m hm j ≫
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
          (actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)) =
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
        (actualPositiveFiniteGeneratorMap g d hhom m hm) := by
  let B := HomogeneousLocalization.Away PS (X j)
  let F := tilde.functor (CommRingCat.of B)
  let Q := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let E := actualPositiveNativeWholeGeneratorFrame (K := K) j d m
  let ePi := actualFinitePiTildeUnitIso B ι
  let t := tildeSelf (R := CommRingCat.of B)
  let J := actualAmbientHomogeneousIdealPositiveNativeChartIso I j m
  let em := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let v := actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)
  let G := actualPositiveFiniteGeneratorMap g d hhom m hm
  let c := ModuleCat.ofHom (actualDegreeZeroChartGeneratorToQuotientKernel I g hg j)
  let k := ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype
  let w := F.map k ≫ t.hom
  have hi : J.hom ≫ w = Q.map v ≫ em.hom :=
    actualAmbientHomogeneousIdealPositiveNativeChartIso_inclusion I j m
  have hji : J.inv ≫ Q.map v ≫ em.hom = w := (J.inv_comp_eq).mpr hi.symm
  have hc : F.map c ≫ F.map k = F.map (ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g)) :=
    (F.map_comp c k).symm.trans
      (congrArg F.map (actualDegreeZeroChartGeneratorToQuotientKernel_subtype I g hg j))
  have hgmap : E.inv ≫ Q.map G ≫ em.hom =
      ePi.hom ≫ F.map (ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g)) ≫ t.hom :=
    (actualPositiveFiniteGeneratorMap_nativeWholeMatrix g d hhom m hm j).trans
      (actualNormalizedSpecUnitGeneratorMatrix_tilde j g).symm
  have hge : E.hom ≫ ePi.hom ≫
      F.map (ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g)) ≫ t.hom =
      Q.map G ≫ em.hom := ((E.inv_comp_eq).mp hgmap).symm
  apply (cancel_mono em.hom).mp
  change (E.hom ≫ ePi.hom ≫ F.map c ≫ J.inv) ≫ Q.map v ≫ em.hom =
    Q.map G ≫ em.hom
  have h₁ : (E.hom ≫ ePi.hom ≫ F.map c ≫ J.inv) ≫ Q.map v ≫ em.hom =
      E.hom ≫ ePi.hom ≫ F.map c ≫ w := by
    simpa only [Category.assoc] using
      congrArg (fun z => E.hom ≫ ePi.hom ≫ F.map c ≫ z) hji
  have h₂ : E.hom ≫ ePi.hom ≫ F.map c ≫ w =
      E.hom ≫ ePi.hom ≫ F.map (ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g)) ≫
        t.hom := by
    simpa only [w, Category.assoc] using
      congrArg (fun z => E.hom ≫ ePi.hom ≫ z ≫ t.hom) hc
  exact h₁.trans (h₂.trans hge)

end PfaffianDescent.Coray
