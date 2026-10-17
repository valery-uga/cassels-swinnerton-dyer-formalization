import PfaffianDescent.NativeOpenContainedFiniteFlatPointEquiv315

/-! SOURCE ONLY315, explicitly pending inverse10 prerequisite. Actual point
comparison on an arbitrary ORIGINAL test and SAME relative open embedding. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private def nativePointFamilyCastEquiv315 {X B : Scheme.{u}}
    (F0 F1 : X ⟶ B) (h : F0 = F1) (n : ℕ) :
    FiniteFlatHilbertPoint195 F0 n ≃ FiniteFlatHilbertPoint195 F1 n :=
  Equiv.cast (congrArg (fun f => FiniteFlatHilbertPoint195 f n) h)

private lemma nativePointFamilyCastEquiv_apply315 {X B : Scheme.{u}}
    (F0 F1 : X ⟶ B) (h : F0 = F1) (n : ℕ) (Q : FiniteFlatHilbertPoint195 F0 n) :
    nativePointFamilyCastEquiv315 F0 F1 h n Q = (h ▸ Q : FiniteFlatHilbertPoint195 F1 n) := by
  cases h
  rfl

variable {X B : Scheme.{u}} (U : X.Opens) (F : X ⟶ B) (n : ℕ)

def relativeOpenContainedPoint315 (T : Over B) : Type u :=
  {P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n //
    Set.range P.val.subschemeι ⊆ Set.range (relativeClosedAmbientTestMap313 U.ι F T)}

variable [IsSeparated F]

private lemma relativeOpenContainedAmbientFamily_separated315 (T : Over B) :
    IsSeparated (relativeHilbertFamily197 F T) := by
  change IsSeparated (pullback.fst T.hom F)
  infer_instance

/-- Point equivalence on every test, from the genuine ENTIRE-source open lift. -/
def relativeOpenContainedPointEquiv315 (T : Over B) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n ≃
      relativeOpenContainedPoint315 U F n T := by
  let k := relativeClosedAmbientTestMap313 U.ι F T
  let f := relativeHilbertFamily197 F T
  letI : IsOpenImmersion k := relativeOpenChartTestMap_isOpenImmersion315 U F T
  letI : IsSeparated f := relativeOpenContainedAmbientFamily_separated315 F T
  exact (nativePointFamilyCastEquiv315 (relativeHilbertFamily197 (U.ι ≫ F) T)
    (k ≫ f) (relativeClosedAmbientTestMap_toTest313 U.ι F T).symm n).trans
      (nativeOpenContainedFiniteFlatPointEquiv315 k f n)

lemma relativeOpenContainedPointEquiv_push315 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n) :
    ((relativeOpenContainedPointEquiv315 U F n T) Q).val =
      relativeOpenFiniteFlatPointPush315 U F n T Q := by
  let k := relativeClosedAmbientTestMap313 U.ι F T
  let f := relativeHilbertFamily197 F T
  letI : IsOpenImmersion k := relativeOpenChartTestMap_isOpenImmersion315 U F T
  letI : IsSeparated f := relativeOpenContainedAmbientFamily_separated315 F T
  change nativeFiniteFlatPointPushOpen314 k f n
      (nativePointFamilyCastEquiv315 (relativeHilbertFamily197 (U.ι ≫ F) T) (k ≫ f)
        (relativeClosedAmbientTestMap_toTest313 U.ι F T).symm n Q) = _
  exact congrArg (nativeFiniteFlatPointPushOpen314 k f n)
    (nativePointFamilyCastEquiv_apply315 (relativeHilbertFamily197 (U.ι ≫ F) T) (k ≫ f)
      (relativeClosedAmbientTestMap_toTest313 U.ι F T).symm n Q)

lemma relativeOpenContainedPointEquiv_wholeIdeal315 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n) :
    ((relativeOpenContainedPointEquiv315 U F n T) Q).val.val =
      Q.val.map (relativeClosedAmbientTestMap313 U.ι F T) :=
  (congrArg Subtype.val (relativeOpenContainedPointEquiv_push315 U F n T Q)).trans
    (relativeOpenFiniteFlatPointPush_wholeIdeal315 U F n T Q)

lemma relativeOpenContainedPointEquiv_inv_ambientIdeal315 (T : Over B)
    (P : relativeOpenContainedPoint315 U F n T) :
    ((relativeOpenContainedPointEquiv315 U F n T).symm P).val.map
      (relativeClosedAmbientTestMap313 U.ι F T) = P.val.val := by
  let e := relativeOpenContainedPointEquiv315 U F n T
  exact (relativeOpenContainedPointEquiv_wholeIdeal315 U F n T (e.symm P)).symm.trans
    (congrArg (fun Q : relativeOpenContainedPoint315 U F n T => Q.val.val)
      (e.apply_symm_apply P))

lemma relativeOpenContainedPointEquiv_inv_comap315 (T : Over B)
    (P : relativeOpenContainedPoint315 U F n T) :
    ((relativeOpenContainedPointEquiv315 U F n T).symm P).val =
      P.val.val.comap (relativeClosedAmbientTestMap313 U.ι F T) := by
  let Q := (relativeOpenContainedPointEquiv315 U F n T).symm P
  let k := relativeClosedAmbientTestMap313 U.ι F T
  letI : IsOpenImmersion k := relativeOpenChartTestMap_isOpenImmersion315 U F T
  letI : IsClosedImmersion (Q.val.subschemeι ≫ k) :=
    relativeOpenFiniteFamilyComposite_isClosed315 U F n T Q
  exact (nativeEmbeddedIdealComapMap315 k Q.val).symm.trans
    (congrArg (fun I => I.comap k) (relativeOpenContainedPointEquiv_inv_ambientIdeal315 U F n T P))

end PfaffianDescent
end
