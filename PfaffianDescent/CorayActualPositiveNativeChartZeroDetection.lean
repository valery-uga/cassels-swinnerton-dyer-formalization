import PfaffianDescent.CorayActualPositiveNativeWholeGeneratorMatrix
import PfaffianDescent.SchemeModuleStalkMono
import Mathlib.Topology.Sheaves.Stalks

/-! The actual four native coordinate charts jointly detect zero morphisms.
All functors, stalks and sheaf maps remain native. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

private lemma zero_map_of_natIso
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    {F G : C ⥤ D} (E : F ≅ G) {M N : C} (f : M ⟶ N)
    (h : F.map f = 0) : G.map f = 0 := by
  apply (cancel_epi (E.hom.app M)).mp
  have hn : E.hom.app M ≫ G.map f = F.map f ≫ E.hom.app N :=
    (E.hom.naturality f).symm
  have hz : F.map f ≫ E.hom.app N = 0 := by rw [h, zero_comp]
  exact hn.trans (hz.trans comp_zero.symm)

private theorem additiveSheaf_hom_eq_of_stalk
    {X : TopCat.{u}} {M N : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f g : M ⟶ N)
    (h : ∀ x : X, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g.hom) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext N V.unop
  intro x hx
  have hf := TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop x hx f.hom s
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop x hx g.hom s
  have he := ConcreteCategory.congr_hom (h x) (M.presheaf.germ V.unop x hx s)
  exact hf.symm.trans (he.trans hg)

private theorem schemeModule_zero_of_stalk_zero
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : X, (schemeModuleStalkFunctor X x).map f = 0) : f = 0 := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  apply T.map_injective
  apply additiveSheaf_hom_eq_of_stalk (T.map f) (T.map (0 : M ⟶ N))
  intro x
  let G := schemeModuleStalkFunctor X x
  letI : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  change G.map f = G.map (0 : M ⟶ N)
  exact (h x).trans (G.map_zero M N).symm

private theorem isoPullback_isFaithful
    {X Y : Scheme.{u}} (e : X ≅ Y) : (Scheme.Modules.pullback e.inv).Faithful := by
  let P := Scheme.Modules.pullback e.inv
  let Q := Scheme.Modules.pullback e.hom
  let E : P ⋙ Q ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact Functor.Faithful.of_comp_iso E

/-- The original four native away pullbacks jointly detect zero. This is
proved from the actual cover and stalk restriction, rather than supplied
as a gluing or image-identification certificate. -/
theorem actualPositiveNativeCharts_jointlyDetectZero
    {M N : (Proj PS).Modules} (f : M ⟶ N)
    (h : ∀ j : Fin 4, (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map f = 0) :
    f = 0 := by
  apply schemeModule_zero_of_stalk_zero f
  intro x
  have hx : x ∈ (⨆ j : Fin 4, p3StandardOpen (K := K) j) := by
    rw [p3StandardOpen_iSup K]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := p3StandardOpen (K := K) j
  let y : U.toScheme := ⟨x, hj⟩
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  let R := Scheme.Modules.restrictFunctor U.ι
  let G := schemeModuleStalkFunctor U.toScheme y
  letI : P.Faithful := isoPullback_isFaithful e
  letI : P.IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction e.inv).isLeftAdjoint
  letI : P.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint P
  letI : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  have hchart : (R ⋙ P).map f = 0 :=
    zero_map_of_natIso (actualPositiveNativeChartRestrictionIso (K := K) j) f (h j)
  have hr : R.map f = 0 := P.zero_of_map_zero (R.map f) hchart
  have hg : (R ⋙ G).map f = 0 :=
    (congrArg G.map hr).trans (G.map_zero (R.obj M) (R.obj N))
  exact zero_map_of_natIso (Scheme.Modules.restrictStalkNatIso U.ι y) f hg

end PfaffianDescent.Coray
