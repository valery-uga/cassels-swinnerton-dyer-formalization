import PfaffianDescent.NativeFiniteSubschemePushOpen314
import PfaffianDescent.RelativeClosedAmbientTestMap313
import PfaffianDescent.RelativeFiniteFlatHilbertFunctor197
import PfaffianDescent.NativeAmbientPullbackChart300
import Mathlib.CategoryTheory.Types.Basic

/-! SOURCE ONLY315. Actual chart-family push on ALL scheme tests is a natural
injection into the ORIGINAL separated ambient finite-flat functor. Closedness
of the whole finite image is derived by314, not assumed for the ambient open. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativePointFamilyCast_val315 {X B : Scheme.{u}}
    (F0 F1 : X ⟶ B) (h : F0 = F1) (n : ℕ) (Q : FiniteFlatHilbertPoint195 F0 n) :
    (h ▸ Q : FiniteFlatHilbertPoint195 F1 n).val = Q.val := by
  cases h
  rfl

/-- Closedness is required only for the actual finite family composite,
not for an open ambient embedding. -/
lemma nativeEmbeddedIdealComapMap315 {Y X : Scheme.{u}}
    (k : Y ⟶ X) [Mono k] (Q : Y.IdealSheafData) [IsClosedImmersion (Q.subschemeι ≫ k)] :
    (Q.map k).comap k = Q := by
  have H : IsPullback (𝟙 Q.subscheme) Q.subschemeι (Q.subschemeι ≫ k) k :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  exact (wholeIdeal_comap_eq_of_isPullback195 (𝟙 Q.subscheme) Q.subschemeι
    (Q.subschemeι ≫ k) k H).trans Q.ker_subschemeι

/-- Cartesian image/base-change law with only the actual composite family closed. -/
lemma nativeEmbeddedIdealMapComap315 {Y0 Y X0 X : Scheme.{u}}
    (dY : Y0 ⟶ Y) (k0 : Y0 ⟶ X0) (k : Y ⟶ X) (dX : X0 ⟶ X)
    (H : IsPullback dY k0 k dX) (Q : Y.IdealSheafData)
    [IsClosedImmersion (Q.subschemeι ≫ k)] :
    (Q.comap dY).map k0 = (Q.map k).comap dX := by
  let r := (Q.comapIso dY).hom ≫ pullback.snd dY Q.subschemeι
  have Hinner : IsPullback r (Q.comap dY).subschemeι Q.subschemeι dY := by
    simpa only [Scheme.IdealSheafData.comapIso_hom_fst] using
      nativePullbackDomainIso300 (IsPullback.of_hasPullback dY Q.subschemeι).flip (Q.comapIso dY)
  exact (wholeIdeal_comap_eq_of_isPullback195 r ((Q.comap dY).subschemeι ≫ k0)
    (Q.subschemeι ≫ k) dX (Hinner.paste_vert H)).symm

variable {X B : Scheme.{u}} (U : X.Opens) (F : X ⟶ B) (n : ℕ)

lemma relativeOpenChartTestMap_isOpenImmersion315 (T : Over B) :
    IsOpenImmersion (relativeClosedAmbientTestMap313 U.ι F T) :=
  MorphismProperty.of_isPullback (relativeClosedAmbientTestMap_isPullback313 U.ι F T).flip
    (inferInstance : IsOpenImmersion U.ι)

set_option backward.isDefEq.respectTransparency.types false in
lemma relativeOpenChartTestMap_natural_isPullback315 {T0 T1 : Over B} (a : T0 ⟶ T1) :
    IsPullback (relativeHilbertAmbientMap197 (U.ι ≫ F) a)
      (relativeClosedAmbientTestMap313 U.ι F T0) (relativeClosedAmbientTestMap313 U.ι F T1)
      (relativeHilbertAmbientMap197 F a) := by
  have Houter : IsPullback (relativeHilbertAmbientMap197 (U.ι ≫ F) a)
      (relativeClosedAmbientTestMap313 U.ι F T0 ≫ relativeHilbertFamily197 F T0)
      (relativeClosedAmbientTestMap313 U.ι F T1 ≫ relativeHilbertFamily197 F T1) a.left := by
    rw [relativeClosedAmbientTestMap_toTest313, relativeClosedAmbientTestMap_toTest313]
    exact relativeHilbertAmbientMap_isPullback197 (U.ι ≫ F) a
  exact Houter.of_bot (relativeClosedAmbientTestMap_natural313 U.ι F a)
    (relativeHilbertAmbientMap_isPullback197 F a)

variable [IsSeparated F]

private lemma relativeOpenAmbientFamily_separated315 (T : Over B) :
    IsSeparated (relativeHilbertFamily197 F T) := by
  change IsSeparated (pullback.fst T.hom F)
  infer_instance

lemma relativeOpenFiniteFamilyComposite_isClosed315 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n) :
    IsClosedImmersion (Q.val.subschemeι ≫ relativeClosedAmbientTestMap313 U.ι F T) := by
  let k := relativeClosedAmbientTestMap313 U.ι F T
  let f := relativeHilbertFamily197 F T
  letI : IsOpenImmersion k := relativeOpenChartTestMap_isOpenImmersion315 U F T
  letI : IsSeparated f := relativeOpenAmbientFamily_separated315 F T
  have hb : (Q.val.subschemeι ≫ k) ≫ f =
      Q.val.subschemeι ≫ relativeHilbertFamily197 (U.ι ≫ F) T :=
    (Category.assoc _ _ _).trans
      (congrArg (fun a => Q.val.subschemeι ≫ a) (relativeClosedAmbientTestMap_toTest313 U.ι F T))
  letI : IsFinite ((Q.val.subschemeι ≫ k) ≫ f) := hb.symm ▸ Q.property.1
  exact nativeFiniteClosedThroughOpen_isClosed314 Q.val.subschemeι k f

/-- Actual whole-family push on an arbitrary original test. -/
def relativeOpenFiniteFlatPointPush315 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n := by
  let k := relativeClosedAmbientTestMap313 U.ι F T
  let f := relativeHilbertFamily197 F T
  letI : IsOpenImmersion k := relativeOpenChartTestMap_isOpenImmersion315 U F T
  letI : IsSeparated f := relativeOpenAmbientFamily_separated315 F T
  let Q' : FiniteFlatHilbertPoint195 (k ≫ f) n :=
    (relativeClosedAmbientTestMap_toTest313 U.ι F T).symm ▸ Q
  exact nativeFiniteFlatPointPushOpen314 k f n Q'

lemma relativeOpenFiniteFlatPointPush_wholeIdeal315 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n) :
    (relativeOpenFiniteFlatPointPush315 U F n T Q).val =
      Q.val.map (relativeClosedAmbientTestMap313 U.ι F T) := by
  let k := relativeClosedAmbientTestMap313 U.ι F T
  let f := relativeHilbertFamily197 F T
  letI : IsOpenImmersion k := relativeOpenChartTestMap_isOpenImmersion315 U F T
  letI : IsSeparated f := relativeOpenAmbientFamily_separated315 F T
  exact (nativeFiniteFlatPointPushOpen_wholeIdeal314 k f n
    ((relativeClosedAmbientTestMap_toTest313 U.ι F T).symm ▸ Q)).trans
      (congrArg (fun I => I.map k) (nativePointFamilyCast_val315
        (relativeHilbertFamily197 (U.ι ≫ F) T) (k ≫ f)
        (relativeClosedAmbientTestMap_toTest313 U.ι F T).symm n Q))

lemma relativeOpenFiniteFlatPointPush_injective315 (T : Over B) :
    Function.Injective (relativeOpenFiniteFlatPointPush315 U F n T) := by
  intro Q R he
  let k := relativeClosedAmbientTestMap313 U.ι F T
  letI : IsOpenImmersion k := relativeOpenChartTestMap_isOpenImmersion315 U F T
  letI : IsClosedImmersion (Q.val.subschemeι ≫ k) := relativeOpenFiniteFamilyComposite_isClosed315 U F n T Q
  letI : IsClosedImmersion (R.val.subschemeι ≫ k) := relativeOpenFiniteFamilyComposite_isClosed315 U F n T R
  have hm : Q.val.map k = R.val.map k :=
    (relativeOpenFiniteFlatPointPush_wholeIdeal315 U F n T Q).symm.trans
      ((congrArg Subtype.val he).trans (relativeOpenFiniteFlatPointPush_wholeIdeal315 U F n T R))
  apply Subtype.ext
  exact (nativeEmbeddedIdealComapMap315 k Q.val).symm.trans
    ((congrArg (fun I => I.comap k) hm).trans (nativeEmbeddedIdealComapMap315 k R.val))

set_option backward.isDefEq.respectTransparency.types false in
lemma relativeOpenFiniteFlatPointPush_natural315 {T0 T1 : Over B} (a : T0 ⟶ T1)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T1) n) :
    relativeOpenFiniteFlatPointPush315 U F n T0
        ((relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map a.op Q) =
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op (relativeOpenFiniteFlatPointPush315 U F n T1 Q) := by
  letI := relativeOpenFiniteFamilyComposite_isClosed315 U F n T1 Q
  apply Subtype.ext
  exact (relativeOpenFiniteFlatPointPush_wholeIdeal315 U F n T0
      ((relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map a.op Q)).trans
    ((nativeEmbeddedIdealMapComap315 (relativeHilbertAmbientMap197 (U.ι ≫ F) a)
      (relativeClosedAmbientTestMap313 U.ι F T0) (relativeClosedAmbientTestMap313 U.ι F T1)
      (relativeHilbertAmbientMap197 F a) (relativeOpenChartTestMap_natural_isPullback315 U F a)
      Q.val).trans
        (congrArg (fun I => I.comap (relativeHilbertAmbientMap197 F a))
          (relativeOpenFiniteFlatPointPush_wholeIdeal315 U F n T1 Q).symm))

/-- Native natural inclusion of chart families into the ORIGINAL ambient functor. -/
def relativeOpenFiniteFlatPointPushNatTrans315 :
    relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ⟶ relativeFiniteFlatHilbertFunctor197 F n where
  app T := ↾fun Q => relativeOpenFiniteFlatPointPush315 U F n T.unop Q
  naturality {T0 T1} a := by
    apply ConcreteCategory.ext_apply
    intro Q
    exact relativeOpenFiniteFlatPointPush_natural315 U F n a.unop Q

end PfaffianDescent
end
