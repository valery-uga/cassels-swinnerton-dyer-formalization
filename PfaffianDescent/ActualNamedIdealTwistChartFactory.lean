import PfaffianDescent.ActualOriginalIdealTwistSourceRefinement

/- SOURCE ONLY / UNVERIFIED. Shared named restriction-source factories.
The entire existing raw unit and ideal Isos are retained after eliminating
an ordinary chart-map equality. No original-data caller supplies a desired
inclusion, basis action or comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original refined unit construction, with its named source object. -/
def actualNamedIdealTwistChartUnitIso
    {X Y : Scheme.{u}} (U : X.Opens) (f : Y ⟶ (U : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [hf0 : IsOpenImmersion f0] (hF : f0 = f ≫ U.ι)
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor f0).obj T ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  subst f0
  exact cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p

/-- Faithful equality of the WHOLE unit Iso, including inverse, to the
literal original restriction-composition construction. -/
lemma actualNamedIdealTwistChartUnitIso_heq_source
    {X Y : Scheme.{u}} (U : X.Opens) (f : Y ⟶ (U : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [IsOpenImmersion f0] (hF : f0 = f ≫ U.ι)
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    HEq (actualNamedIdealTwistChartUnitIso U f f0 hF T p)
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p) := by
  subst f0
  exact HEq.refl _

/-- The original ideal-twist construction, with its named source object. -/
def actualNamedIdealTwistChartIso
    {X Y Z : Scheme.{u}} (U : X.Opens) (f : Y ⟶ (U : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [hf0 : IsOpenImmersion f0] (hF : f0 = f ≫ U.ι)
    (q : Z ⟶ X) [hq : IsClosedImmersion q]
    (j : Z ⟶ Y) [hj : IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor f0).obj (closedImmersionIdealTwist q T) ≅
      closedImmersionModule j := by
  subst f0
  exact actualOriginalIdealTwistSourceRefinementIso U f q j hfac T p

/-- Faithful equality of the WHOLE ideal Iso, including its original
source-equality transport and inverse, to the literal raw construction. -/
lemma actualNamedIdealTwistChartIso_heq_source
    {X Y Z : Scheme.{u}} (U : X.Opens) (f : Y ⟶ (U : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [IsOpenImmersion f0] (hF : f0 = f ≫ U.ι)
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    HEq (actualNamedIdealTwistChartIso U f f0 hF q j hfac T p)
      (actualOriginalIdealTwistSourceRefinementIso U f q j hfac T p) := by
  subst f0
  exact HEq.refl _

/-- The actual inclusion comparison is proved while all schemes and
modules are abstract, retaining the SAME named restriction source. -/
lemma actualNamedIdealTwistChartIso_toInclusion
    {X Y Z : Scheme.{u}} (U : X.Opens) (f : Y ⟶ (U : Scheme)) [IsIso f]
    (f0 : Y ⟶ X) [IsOpenImmersion f0] (hF : f0 = f ≫ U.ι)
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U.ι = q) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (actualNamedIdealTwistChartIso U f f0 hF q j hfac T p).hom ≫
      closedImmersionModuleToUnit j =
    (Scheme.Modules.restrictFunctor f0).map (actualIdealTwistInclusion q T) ≫
      (actualNamedIdealTwistChartUnitIso U f f0 hF T p).hom := by
  subst f0
  exact actualOriginalIdealTwistSourceRefinementIso_toInclusion U f q j hfac T p

/-- The SAME original factorization expressed using the named chart map. -/
def actualNamedIdealChartFactorization
    {X Y Z : Scheme.{u}} (U : X.Opens) (f : Y ⟶ (U : Scheme))
    (f0 : Y ⟶ X) (hF : f0 = f ≫ U.ι)
    (q : Z ⟶ X) (j : Z ⟶ Y) (hfac : (j ≫ f) ≫ U.ι = q) :
    j ≫ f0 = q := by
  rw [hF]
  exact (Category.assoc j f U.ι).symm.trans hfac

end PfaffianDescent
