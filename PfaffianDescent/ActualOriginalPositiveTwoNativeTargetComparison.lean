import PfaffianDescent.ActualOriginalPositiveTwoNativeTargetSheafSquare
import PfaffianDescent.ActualOriginalUntwistedDifferentialChartCoherence
import PfaffianDescent.ActualCubicPositiveTwoNativePointFiber
import PfaffianDescent.ActualOriginalPositiveTwoContractedNativeDifferentialMap
import PfaffianDescent.ActualCubicPositiveTwoChartContractedNativeDifferentialMap

/-! SOURCE ONLY, UNVERIFIED. Contingency028 derives the complete native
Omega(2) fiber comparison at an arbitrary cubic chart and field point,
with separate named factory identifications before final equality transfer,
then inserts the SAME original quartic point, whole O2 trivialization,
and accepted coordinate basis law. The original public proposition and
protected producer sources are retained. No desired comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

universe v w x v' w' x'

/-- Cancellation in abstract categories avoids unfolding the original cubic
point, chart, and sheaf isomorphisms during the categorical proof. -/
private lemma actualFiberNativeTargetSquare_of_basis
    {C : Type v} [Category.{v'} C] {D : Type w} [Category.{w'} D]
    {E : Type x} [Category.{x'} E]
    (Pq : C ⥤ D) (Pf : C ⥤ E) (Pj : E ⥤ D)
    (N : Pq ≅ Pf ⋙ Pj) {W A : C} {B : E} {F : D}
    (a : W ⟶ A) (U₁ : Pq.obj A ≅ F) (U₂ : F ≅ Pq.obj W)
    (eChart : Pf.obj A ≅ B) (eOmega : Pf.obj W ≅ B)
    (hInsert : Pq.map a ≫ (U₁ ≪≫ U₂).hom = 𝟙 (Pq.obj W))
    (hChart : Pf.map a ≫ eChart.hom = eOmega.hom) :
    N.hom.app A ≫ Pj.map eChart.hom =
      U₁.hom ≫ U₂.hom ≫ N.hom.app W ≫ Pj.map eOmega.hom := by
  let U := U₁ ≪≫ U₂
  have hInv : Pq.map a = U.inv := (U.comp_hom_eq_id).mp hInsert
  letI : IsIso (Pq.map a) := by
    rw [hInv]
    infer_instance
  have hn : Pq.map a ≫ N.hom.app A =
      N.hom.app W ≫ Pj.map (Pf.map a) := N.hom.naturality a
  have hLeft : Pq.map a ≫ (N.hom.app A ≫ Pj.map eChart.hom) =
      N.hom.app W ≫ Pj.map eOmega.hom := by
    calc
      _ = (Pq.map a ≫ N.hom.app A) ≫ Pj.map eChart.hom :=
        (Category.assoc _ _ _).symm
      _ = (N.hom.app W ≫ Pj.map (Pf.map a)) ≫ Pj.map eChart.hom := by rw [hn]
      _ = N.hom.app W ≫ Pj.map (Pf.map a ≫ eChart.hom) := by
        rw [Pj.map_comp, Category.assoc]
      _ = _ := by rw [hChart]
  have hRight : Pq.map a ≫ (U.hom ≫ N.hom.app W ≫ Pj.map eOmega.hom) =
      N.hom.app W ≫ Pj.map eOmega.hom := by
    rw [← Category.assoc (Pq.map a), hInsert, Category.id_comp]
  have hResult : N.hom.app A ≫ Pj.map eChart.hom =
      U.hom ≫ N.hom.app W ≫ Pj.map eOmega.hom := by
    apply (cancel_epi (Pq.map a)).1
    exact hLeft.trans hRight.symm
  simpa only [U, Iso.trans_hom, Category.assoc] using hResult

/-- Fold the original pullback tensor map into a whole point untwist Iso
while the scheme, modules, field point, and basis section are abstract. The
only hom comparison is the tensor Iso's proved defining hom equation. -/
private lemma actualFiberNativePointInsertionWholeIso_contract
    {X : Scheme.{u}} {L : Type u} [Field L]
    (q : Spec (.of L) ⟶ X) (W T : X.Modules)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (eT : (Scheme.Modules.pullback q).obj T ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map v ≫ eT.hom =
      BundleSectionZeroLocus.pullbackUnitComparison q)
    (U₁ : (Scheme.Modules.pullback q).obj (schemeModuleTensor W T) ≅
      schemeModuleTensor ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T))
    (hU₁ : U₁.hom = cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q W T) :
    (Scheme.Modules.pullback q).map (actualModuleTwistBasisInsertion W T v) ≫
      (U₁ ≪≫ actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom =
          𝟙 ((Scheme.Modules.pullback q).obj W) := by
  change (Scheme.Modules.pullback q).map (actualModuleTwistBasisInsertion W T v) ≫
    U₁.hom ≫ schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback q).obj W)) eT.hom ≫
      (schemeModuleTensorUnitRightIso ((Scheme.Modules.pullback q).obj W)).hom = _
  rw [hU₁]
  exact actualModuleTwistBasisInsertion_pullback_contract q W T v eT hv

/-- Resolve all Scheme.Modules category instances, pullback functor objects,
point tensor objects, and whole-Iso hom conversions before a cubic, chart,
or original residue point is inserted. This theorem constructs the square
from naturality and the two basis laws; it does not assume the square. -/
private lemma actualFiberSchemeNativeTargetSquare_of_point_basis
    {X Y : Scheme.{u}} {L : Type u} [Field L]
    (f : Y ⟶ X) (j : Spec (.of L) ⟶ Y) (q : Spec (.of L) ⟶ X)
    (hfac : j ≫ f = q) (W T : X.Modules)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (eT : (Scheme.Modules.pullback q).obj T ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map v ≫ eT.hom =
      BundleSectionZeroLocus.pullbackUnitComparison q)
    (U₁ : (Scheme.Modules.pullback q).obj (schemeModuleTensor W T) ≅
      schemeModuleTensor ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T))
    (hU₁ : U₁.hom = cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q W T)
    (B : Y.Modules)
    (eChart : (Scheme.Modules.pullback f).obj (schemeModuleTensor W T) ≅ B)
    (eOmega : (Scheme.Modules.pullback f).obj W ≅ B)
    (hChart : (Scheme.Modules.pullback f).map (actualModuleTwistBasisInsertion W T v) ≫
      eChart.hom = eOmega.hom) :
    let N := actualPullbackFactorizationNatIso f j q hfac
    N.hom.app (schemeModuleTensor W T) ≫ (Scheme.Modules.pullback j).map eChart.hom =
      U₁.hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
          ((Scheme.Modules.pullback q).obj T) eT).hom ≫
        N.hom.app W ≫ (Scheme.Modules.pullback j).map eOmega.hom := by
  exact actualFiberNativeTargetSquare_of_basis
    (C := X.Modules) (D := (Spec (.of L)).Modules) (E := Y.Modules)
    (W := W) (A := schemeModuleTensor W T) (B := B)
    (F := schemeModuleTensor ((Scheme.Modules.pullback q).obj W)
      ((Scheme.Modules.pullback q).obj T))
    (Scheme.Modules.pullback q) (Scheme.Modules.pullback f) (Scheme.Modules.pullback j)
    (actualPullbackFactorizationNatIso f j q hfac)
    (actualModuleTwistBasisInsertion W T v) U₁
    (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
      ((Scheme.Modules.pullback q).obj T) eT) eChart eOmega
    (actualFiberNativePointInsertionWholeIso_contract q W T v eT hv U₁ hU₁) hChart

/-- Resolve the full native target square at an arbitrary cubic chart index
and arbitrary field-valued chart factorization, before the quartic chart
choice is inserted. The raw coordinate-basis section, differential Iso,
positive tensor, and tilde target are all elaborated at this earlier level.
Only the ordinary point basis law is abstract here; the original caller
supplies its accepted proof internally. -/
private lemma actualFiberCubicChartNativeTargetSquare_of_pointBasis
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    let j := Spec.map (CommRingCat.ofHom rho)
    let f := chartι I a
    let W := schemeRelativeDifferentials (toBase I)
    let T := positiveSheafOfModules (grading I) 2
    let N := actualPullbackFactorizationNatIso f j q hfac
    N.hom.app (schemeModuleTensor W T) ≫
      (Scheme.Modules.pullback j).map (actualCubicPositiveTwoNativeChartTildeIso p hp a).hom =
    (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom ≫
      N.hom.app W ≫
      (Scheme.Modules.pullback j).map
        (((actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
          actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)).hom) := by
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  let f := chartι I a
  let j := Spec.map (CommRingCat.ofHom rho)
  let W := schemeRelativeDifferentials (toBase I)
  let T := positiveSheafOfModules (grading I) 2
  let s := actualPositiveTwistChartBasisInvHom I
    ⟨coordinate I a, coordinate_mem I a⟩ 2
  let eOmega := (actualCubicNativeChartDifferentialSheafIso p hp a).symm ≪≫
    actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
  exact actualFiberSchemeNativeTargetSquare_of_point_basis
    (X := hypersurface p hp) (Y := Spec (.of R)) (L := L)
    f j q hfac W T s eT hv
    (actualPositiveTwistPullbackTensorIso I q W 2)
    (actualPositiveTwistPullbackTensorIso_hom I q W 2)
    _ (actualCubicPositiveTwoNativeChartTildeIso p hp a) eOmega
    (actualCubicPositiveTwoNativeChartTildeIso_basisInsertion p hp a)

private lemma actualFiberFunctorThreeIsoComposition
    {C : Type v} [Category.{v'} C] {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) {C₀ C₁ C₂ C₃ : C} {D₀ D₁ : D}
    (a : D₀ ⟶ D₁) (b : D₁ ⟶ F.obj C₃)
    (r : C₂ ≅ C₃) (d : C₁ ≅ C₂) (e : C₀ ≅ C₁) :
    (a ≫ b) ≫ F.map (e ≪≫ (d ≪≫ r)).inv =
      (a ≫ b ≫ F.map r.inv ≫ F.map d.inv) ≫ F.map e.inv := by
  simp only [Iso.trans_inv, Functor.map_comp, Category.assoc]

/-- Resolve the restriction/pullback composition before inserting a cubic. -/
private lemma actualFiberSchemeDifferentialChartCoherence
    {K L : Type u} [CommRing K] [Field L] {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (j : Spec (.of L) ⟶ U) (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (t : U ⟶ Spec (.of K)) (ht : f ≫ g = t) :
    let W := schemeRelativeDifferentials g
    let e := eqToIso (congrArg schemeRelativeDifferentials ht.symm) ≪≫
      actualOpenImmersionDifferentialSheafPullbackIso f g
    (actualPullbackFactorizationNatIso f j q hfac).hom.app W ≫
      (Scheme.Modules.pullback j).map e.inv =
      (actualModulePointChartSourceFactorizationIso f j q hfac W
        (schemeRelativeDifferentials (f ≫ g))
        (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm).hom ≫
      ((Scheme.Modules.pullback j).mapIso
        (eqToIso (congrArg schemeRelativeDifferentials ht))).hom := by
  dsimp only
  rw [actualPullbackFactorizationNatIso_app_eqToIso]
  exact actualFiberFunctorThreeIsoComposition (Scheme.Modules.pullback j)
    (eqToIso (congrArg (fun z => (Scheme.Modules.pullback z).obj
      (schemeRelativeDifferentials g)) hfac.symm)).hom
    ((Scheme.Modules.pullbackComp j f).inv.app (schemeRelativeDifferentials g))
    ((Scheme.Modules.restrictFunctorIsoPullback f).app (schemeRelativeDifferentials g))
    (actualOpenImmersionDifferentialSheafRestrictionIso f g)
    (eqToIso (congrArg schemeRelativeDifferentials ht.symm))

/-- Transfer the proved formula to a named whole chart Iso through its definition. -/
private lemma actualFiberSchemeDifferentialChartCoherence_named
    {K L : Type u} [CommRing K] [Field L] {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (j : Spec (.of L) ⟶ U) (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (t : U ⟶ Spec (.of K)) (ht : f ≫ g = t)
    (e : schemeRelativeDifferentials t ≅
      (Scheme.Modules.pullback f).obj (schemeRelativeDifferentials g))
    (he : e = eqToIso (congrArg schemeRelativeDifferentials ht.symm) ≪≫
      actualOpenImmersionDifferentialSheafPullbackIso f g) :
    (actualPullbackFactorizationNatIso f j q hfac).hom.app (schemeRelativeDifferentials g) ≫
      (Scheme.Modules.pullback j).map e.inv =
      (actualModulePointChartSourceFactorizationIso f j q hfac
        (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
        (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm).hom ≫
      ((Scheme.Modules.pullback j).mapIso
        (eqToIso (congrArg schemeRelativeDifferentials ht))).hom := by
  subst e
  exact actualFiberSchemeDifferentialChartCoherence f g j q hfac t ht

private lemma actualFiberAssembleComparison
    {C : Type v} [Category.{v'} C] {D : Type w} [Category.{w'} D]
    {F : C ⥤ D} {C₀ C₁ C₂ C₃ : C} {D₀ D₁ D₂ D₃ : D}
    {nA : D₀ ⟶ F.obj C₀} {u : D₀ ⟶ D₁} {v : D₁ ⟶ D₂}
    {nB : D₂ ⟶ F.obj C₁} {eChart : C₀ ≅ C₃}
    {eNative : C₂ ≅ C₁} {eAffine : C₂ ≅ C₃}
    {t : D₂ ⟶ D₃} {b : D₃ ⟶ F.obj C₂}
    (h : nA ≫ F.map eChart.hom =
      u ≫ v ≫ nB ≫ F.map (eNative.symm ≪≫ eAffine).hom)
    (hc : nB ≫ F.map eNative.inv = t ≫ b) :
    nA ≫ F.map eChart.hom = (u ≫ v) ≫ t ≫ b ≫ F.map eAffine.hom := by
  calc
    _ = u ≫ v ≫ nB ≫ F.map eNative.inv ≫ F.map eAffine.hom := by
      simpa only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] using h
    _ = (u ≫ v) ≫ (nB ≫ F.map eNative.inv) ≫ F.map eAffine.hom := by
      simp only [Category.assoc]
    _ = _ := by rw [hc]; simp only [Category.assoc]

private lemma actualFiberRegroupFour
    {C : Type v} [Category.{v'} C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private lemma actualFiberFactorizationAppHom
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y) (q : Z ⟶ X)
    (hfac : j ≫ f = q) (M : X.Modules) :
    (actualPullbackFactorizationNatIso f j q hfac).hom.app M =
      (Scheme.Modules.pullbackCongr hfac).inv.app M ≫
        (Scheme.Modules.pullbackComp j f).inv.app M := rfl

/-- Convert a whole sheaf-Iso equation to equality of the complete linear
maps while the category, Gamma functor, all modules, and final linear
fiber equivalence are abstract. No concrete scheme is reduced here. -/
private lemma actualFiberWholeIsoLinearComparison
    {L : Type u} [CommRing L] {C : Type v} [Category.{v'} C]
    (G : C ⥤ ModuleCat.{u} L) {A B D : C}
    (e : A ≅ B) (c : A ⟶ D) (d : D ≅ B)
    {V : Type u} [AddCommGroup V] [Module L V]
    (a : G.obj B ≃ₗ[L] V) (h : e.hom = c ≫ d.hom) :
    ((G.mapIso e).toLinearEquiv ≪≫ₗ a).toLinearMap =
      ((G.mapIso d).toLinearEquiv ≪≫ₗ a).toLinearMap.comp (G.map c).hom := by
  apply LinearMap.ext
  intro z
  change a (G.map e.hom z) = a (G.map d.hom (G.map c z))
  rw [h, G.map_comp, ModuleCat.comp_apply]

/-- Compute the true affine differential fiber equivalence using its SAME
whole genuine-to-tilde Iso before any cubic chart algebra is inserted. -/
private lemma actualFiberAffineEquiv_eq_wholeIso
    {K R L : Type u} [CommRing K] [CommRing R] [CommRing L] [Algebra K R]
    (rho : R →+* L) :
    letI : Algebra R L := rho.toAlgebra
    actualAffineSchemeDifferentialPointFiberEquiv (k := K) rho =
      ((moduleSpecΓFunctor (R := .of L)).mapIso
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).mapIso
          (actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)))).toLinearEquiv ≪≫ₗ
        affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
          (ModuleCat.of R (KaehlerDifferential K R)) := by
  dsimp only [actualAffineSchemeDifferentialPointFiberEquiv,
    actualAffineDifferentialGenuineToTildeIso]
  rw [Iso.toLinearEquiv_symm, ← Functor.mapIso_symm, ← Functor.mapIso_symm]

/-- An abbreviation for the SAME shared upstream arbitrary-chart factory
used by the proposed original producer. No second Gamma/Et/Ebase/c body
is reconstructed in this comparison file. -/
private abbrev actualFiberChartContractedNativeMap
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback q).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase I))
          (positiveSheafOfModules (grading I) 2))) →ₗ[L]
            (L ⊗[R] KaehlerDifferential K R) := by
  dsimp only
  exact actualCubicPositiveTwoChartContractedNativeDifferentialMap p hp
    a rho q hfac eT

/-- Compute BOTH natural-Iso application/inverse components and the mapped
Iso hom before inserting any Scheme.Modules objects. This exact equality
replaces the failed concrete `simpa only [Iso.trans_hom]` conversion. -/
private lemma actualFiberFunctorPointChartWholeIso_hom
    {C : Type v} [Category.{v'} C] {D : Type w} [Category.{w'} D]
    {E : Type x} [Category.{x'} E]
    (Pq H : C ⥤ D) (Pf : C ⥤ E) (Pj : E ⥤ D)
    (n₁ : H ≅ Pq) (n₂ : Pf ⋙ Pj ≅ H)
    (M : C) {B : E} (e : Pf.obj M ≅ B) :
    ((n₁.app M).symm ≪≫ n₂.symm.app M ≪≫ Pj.mapIso e).hom =
      n₁.inv.app M ≫ n₂.inv.app M ≫ Pj.map e.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc]

/-- Resolve the same whole point/chart composite in abstract Schemes.
The given factorization and original module/Iso are retained exactly. -/
private lemma actualFiberSchemePointChartWholeIso_hom
    {X Y : Scheme.{u}} {L : Type u} [Field L]
    (f : Y ⟶ X) (j : Spec (.of L) ⟶ Y) (q : Spec (.of L) ⟶ X)
    (hfac : j ≫ f = q) (M : X.Modules) {B : Y.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ B) :
    (((Scheme.Modules.pullbackCongr hfac).app M).symm ≪≫
      (Scheme.Modules.pullbackComp j f).symm.app M ≪≫
      (Scheme.Modules.pullback j).mapIso e).hom =
        (Scheme.Modules.pullbackCongr hfac).inv.app M ≫
        (Scheme.Modules.pullbackComp j f).inv.app M ≫
        (Scheme.Modules.pullback j).map e.hom := by
  exact actualFiberFunctorPointChartWholeIso_hom
    (Scheme.Modules.pullback q) (Scheme.Modules.pullback (j ≫ f))
    (Scheme.Modules.pullback f) (Scheme.Modules.pullback j)
    (Scheme.Modules.pullbackCongr hfac) (Scheme.Modules.pullbackComp j f) M e

/-- First derive only the sheaf-morphism equality at an arbitrary cubic
chart, using the internally proved target square and chart coherence.
The whole-Iso/Gamma/linear-map continuation is checked separately. -/
private lemma actualFiberCubicChartSheafComparison_of_pointBasis
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    letI : Algebra R L := rho.toAlgebra
    let f := chartι I a
    let j := Spec.map (CommRingCat.ofHom rho)
    let W := schemeRelativeDifferentials (toBase I)
    let T := positiveSheafOfModules (grading I) 2
    let Pj := Scheme.Modules.pullback j
    let c := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom
    let Et := actualModulePointChartSourceFactorizationIso f j q hfac
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := Pj.mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I a)))
    let A := (Scheme.Modules.pullbackCongr hfac).inv.app (schemeModuleTensor W T)
    let B := (Scheme.Modules.pullbackComp j f).inv.app (schemeModuleTensor W T)
    A ≫ B ≫ Pj.map (actualCubicPositiveTwoNativeChartTildeIso p hp a).hom =
      (c ≫ Et.hom ≫ Ebase.hom) ≫
        Pj.map (actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)).hom := by
  dsimp only
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  letI : Algebra R L := rho.toAlgebra
  let f := chartι I a
  let j := Spec.map (CommRingCat.ofHom rho)
  let W := schemeRelativeDifferentials (toBase I)
  let T := positiveSheafOfModules (grading I) 2
  let N := actualPullbackFactorizationNatIso f j q hfac
  let Pj := Scheme.Modules.pullback j
  let c := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
    (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
      ((Scheme.Modules.pullback q).obj T) eT).hom
  let Et := actualModulePointChartSourceFactorizationIso f j q hfac
    W (schemeRelativeDifferentials (f ≫ toBase I))
    (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
  let Ebase := Pj.mapIso
    (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I a)))
  let eChart := actualCubicPositiveTwoNativeChartTildeIso p hp a
  let eNative := actualCubicNativeChartDifferentialSheafIso p hp a
  let eAffine := actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
  have hTarget := actualFiberCubicChartNativeTargetSquare_of_pointBasis
    p hp a rho q hfac eT hv
  have hCoherence := actualFiberSchemeDifferentialChartCoherence_named
    f (toBase I) j q hfac
    (Spec.map (CommRingCat.ofHom (chartBaseMap I a))) (chartι_toBase I a)
    eNative (by rfl)
  have hFull : N.hom.app (schemeModuleTensor W T) ≫ Pj.map eChart.hom =
      c ≫ Et.hom ≫ Ebase.hom ≫ Pj.map eAffine.hom := by
    exact actualFiberAssembleComparison
      (C := (Spec (.of R)).Modules) (D := (Spec (.of L)).Modules) (F := Pj)
      hTarget hCoherence
  let A := (Scheme.Modules.pullbackCongr hfac).inv.app (schemeModuleTensor W T)
  let B := (Scheme.Modules.pullbackComp j f).inv.app (schemeModuleTensor W T)
  have hFull' : A ≫ B ≫ Pj.map eChart.hom =
      (c ≫ Et.hom ≫ Ebase.hom) ≫ Pj.map eAffine.hom := by
    calc
      _ = (A ≫ B) ≫ Pj.map eChart.hom := (Category.assoc A B (Pj.map eChart.hom)).symm
      _ = N.hom.app (schemeModuleTensor W T) ≫ Pj.map eChart.hom :=
        congrArg (fun z => z ≫ Pj.map eChart.hom)
          (actualFiberFactorizationAppHom f j q hfac (schemeModuleTensor W T)).symm
      _ = _ := hFull.trans
        (actualFiberRegroupFour (C := (Spec (.of L)).Modules)
          c Et.hom Ebase.hom (Pj.map eAffine.hom))
  exact hFull'

/-- Finish ONLY the whole sheaf-Iso comparison at the arbitrary cubic
chart. No Gamma functor, tensor fiber, or linear-map factory is normalized
in this declaration. The raw sheaf law is supplied by the preceding proof. -/
private lemma actualFiberCubicChartWholeIsoComparison_of_pointBasis
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    let f := chartι I a
    let j := Spec.map (CommRingCat.ofHom rho)
    let W := schemeRelativeDifferentials (toBase I)
    let T := positiveSheafOfModules (grading I) 2
    let Pj := Scheme.Modules.pullback j
    let c := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom
    let Et := actualModulePointChartSourceFactorizationIso f j q hfac
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := Pj.mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I a)))
    let eQ := ((Scheme.Modules.pullbackCongr hfac).app (schemeModuleTensor W T)).symm
    let eComp := (Scheme.Modules.pullbackComp j f).symm.app (schemeModuleTensor W T)
    (eQ ≪≫ eComp ≪≫ Pj.mapIso (actualCubicPositiveTwoNativeChartTildeIso p hp a)).hom =
      (c ≫ Et.hom ≫ Ebase.hom) ≫
        (Pj.mapIso (actualAffineDifferentialGenuineToTildeIso (k := K) (R := R))).hom := by
  dsimp only
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  let f := chartι I a
  let j := Spec.map (CommRingCat.ofHom rho)
  let W := schemeRelativeDifferentials (toBase I)
  let T := positiveSheafOfModules (grading I) 2
  let Pj := Scheme.Modules.pullback j
  let c := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
    (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
      ((Scheme.Modules.pullback q).obj T) eT).hom
  let Et := actualModulePointChartSourceFactorizationIso f j q hfac
    W (schemeRelativeDifferentials (f ≫ toBase I))
    (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
  let Ebase := Pj.mapIso
    (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I a)))
  let eChart := actualCubicPositiveTwoNativeChartTildeIso p hp a
  let eAffine := actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
  let eQ := ((Scheme.Modules.pullbackCongr hfac).app (schemeModuleTensor W T)).symm
  let eComp := (Scheme.Modules.pullbackComp j f).symm.app (schemeModuleTensor W T)
  have hWhole : (eQ ≪≫ eComp ≪≫ Pj.mapIso eChart).hom =
      (c ≫ Et.hom ≫ Ebase.hom) ≫ (Pj.mapIso eAffine).hom := by
    exact (actualFiberSchemePointChartWholeIso_hom f j q hfac
      (schemeModuleTensor W T) eChart).trans
        (actualFiberCubicChartSheafComparison_of_pointBasis p hp a rho q hfac eT hv)
  exact hWhole

/-- Convert a true whole sheaf-Iso equation into the complete affine
fiber linear-map equation BEFORE a cubic/chart ring is inserted. The source
module and both morphisms are abstract; the affine equivalence uses the
SAME internally invertible genuine-to-tilde map. The original caller does
not supply this equation: its whole-Iso proof is constructed above. -/
private lemma actualFiberSchemeAffineLinearComparison
    {K R L : Type u} [CommRing K] [CommRing R] [CommRing L] [Algebra K R]
    (rho : R →+* L) {S : (Spec (.of L)).Modules}
    {e : S ≅ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
      ((tilde.functor (.of R)).obj (ModuleCat.of R (KaehlerDifferential K R)))}
    {c : S ⟶ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
      (schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap K R))))}
    (h : e.hom = c ≫
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).map
        (actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)).hom) :
    letI : Algebra R L := rho.toAlgebra
    (((moduleSpecΓFunctor (R := .of L)).mapIso e).toLinearEquiv ≪≫ₗ
      affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
        (ModuleCat.of R (KaehlerDifferential K R))).toLinearMap =
      (actualAffineSchemeDifferentialPointFiberEquiv (k := K) rho).toLinearMap.comp
        ((moduleSpecΓFunctor (R := .of L)).map c).hom := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  have hLinear := actualFiberWholeIsoLinearComparison
    (moduleSpecΓFunctor (R := .of L)) e c
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).mapIso
      (actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)))
    (affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
      (ModuleCat.of R (KaehlerDifferential K R))) h
  rw [← actualFiberAffineEquiv_eq_wholeIso (K := K) rho] at hLinear
  exact hLinear

/-- Infer the SAME whole Iso and genuine morphism directly from the
separately proved whole sheaf-Iso equation. No chart-level Et/Ebase or
other sheaf morphism is reconstructed in this specialization. -/
private def actualFiberCubicChartLinearComparisonValue
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :=
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  actualFiberSchemeAffineLinearComparison (K := K) rho
    (actualFiberCubicChartWholeIsoComparison_of_pointBasis p hp a rho q hfac eT hv)

/-- Reuse a fully supplied proved term through its inferred type. The
entire body is retained for recursive TYPE+VALUE inspection. -/
private opaque actualFiberCubicChartComparison_of_pointBasis
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :
    type_of% (actualFiberCubicChartLinearComparisonValue p hp a rho q hfac eT hv) :=
  actualFiberCubicChartLinearComparisonValue p hp a rho q hfac eT hv

/-- Identify only the native point-fiber factory at arbitrary chart data.
This definitional equality is checked BEFORE the original point is inserted,
and independently of the genuine contracted factory. -/
private lemma actualFiberNativePointFactory_eq_raw
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    letI : Algebra R L := rho.toAlgebra
    let j := Spec.map (CommRingCat.ofHom rho)
    let M := actualCubicPositiveTwoDifferentials p hp
    let eQ := ((Scheme.Modules.pullbackCongr hfac).app M).symm
    let eComp := (Scheme.Modules.pullbackComp j (chartι I a)).symm.app M
    (actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp q a rho hfac).toLinearMap =
      (((moduleSpecΓFunctor (R := .of L)).mapIso
        (eQ ≪≫ eComp ≪≫ (Scheme.Modules.pullback j).mapIso
          (actualCubicPositiveTwoNativeChartTildeIso p hp a))).toLinearEquiv ≪≫ₗ
        affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
          (ModuleCat.of R (KaehlerDifferential K R))).toLinearMap := by
  rfl

/-- Identify only the parameterized true contracted-map factory at arbitrary
chart data. Its exact literal Gamma/affine formula is checked separately. -/
private lemma actualFiberChartContractedFactory_eq_raw
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    letI : Algebra R L := rho.toAlgebra
    let f := chartι I a
    let j := Spec.map (CommRingCat.ofHom rho)
    let W := schemeRelativeDifferentials (toBase I)
    let T := positiveSheafOfModules (grading I) 2
    let Et := actualModulePointChartSourceFactorizationIso f j q hfac
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I a)))
    let c := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom
    actualFiberChartContractedNativeMap p hp a rho q hfac eT =
      (actualAffineSchemeDifferentialPointFiberEquiv (k := K) rho).toLinearMap.comp
        ((moduleSpecΓFunctor (R := .of L)).map (c ≫ Et.hom ≫ Ebase.hom)).hom := by
  dsimp only
  exact actualCubicPositiveTwoChartContractedNativeDifferentialMap_eq_formula
    p hp a rho q hfac eT

/-- Transfer the already proved literal comparison to the TWO named factory
maps while the chart index and point field are still ordinary parameters.
No original quartic choice is normalized in this declaration. -/
private def actualFiberCubicChartNamedComparisonValue
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :=
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  letI : Algebra R L := rho.toAlgebra
  (actualFiberNativePointFactory_eq_raw p hp q a rho hfac).trans
    ((actualFiberCubicChartComparison_of_pointBasis p hp a rho q hfac eT hv).trans
      (actualFiberChartContractedFactory_eq_raw p hp a rho q hfac eT).symm)

/-- A supplied proof body of the named-factory comparison. -/
private opaque actualFiberCubicChartNamedComparison
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (hv : (Scheme.Modules.pullback q).map
      (actualPositiveTwistChartBasisInvHom (equationIdeal p hp)
        ⟨coordinate (equationIdeal p hp) a, coordinate_mem (equationIdeal p hp) a⟩ 2) ≫
      eT.hom = BundleSectionZeroLocus.pullbackUnitComparison q) :
    type_of% (actualFiberCubicChartNamedComparisonValue p hp a rho q hfac eT hv) :=
  actualFiberCubicChartNamedComparisonValue p hp a rho q hfac eT hv

attribute [local irreducible] actualOriginalQuarticCotangentChartChoice
set_option backward.isDefEq.respectTransparency true

/-- Insert the SAME original point, chart choice, whole point trivialization,
and checked basis law only after the complete generic fiber equation exists. -/
private def actualOriginalNativeFiberComparisonValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  actualFiberCubicChartNamedComparison p hp C.index C.residue
    ((hypersurface p hp).fromSpecResidueField P.1) C.factorization
    (actualOriginalPositiveTwoPointTrivialization p hp P hP)
    (actualOriginalPositiveTwoPointTrivialization_basis p hp P hP)

/-- A supplied proof body, preserved for the recursive TYPE+VALUE audit. -/
private opaque actualOriginalNativeFiberComparisonProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalNativeFiberComparisonValue p hp P hP) :=
  actualOriginalNativeFiberComparisonValue p hp P hP

/-- Both factories now unfold to the SAME shared constant application at
C.index/C.residue/original q/C.factorization/original O2 trivialization.
Reflexivity no longer compares two separately reconstructed Gamma bodies. -/
private lemma actualOriginalContractedNativeFactory_eq_chartFactory
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP =
      actualFiberChartContractedNativeMap p hp C.index C.residue
        ((hypersurface p hp).fromSpecResidueField P.1) C.factorization
        (actualOriginalPositiveTwoPointTrivialization p hp P hP) := by
  rfl

lemma actualCubicPositiveTwoOriginalNativePointFiberEquiv_eq_contracted
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    (actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue
      C.factorization).toLinearMap =
        actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP := by
  dsimp only
  exact (actualOriginalNativeFiberComparisonProof p hp P hP).trans
    (actualOriginalContractedNativeFactory_eq_chartFactory p hp P hP).symm

end PfaffianDescent
