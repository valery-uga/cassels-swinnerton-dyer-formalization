import PfaffianDescent.NativeFiniteFlatAmbientIsoTransport317
import PfaffianDescent.RelativeFiniteFlatHilbertFunctor197

/-! SOURCE ONLY317. Physical Cartesian chart points compare with literal197
relative points. The actual relative ambient map and WHOLE point naturality
are proved from projection diagrams before any coefficient rings are used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

variable {X B Y : Scheme.{u}} (F : X ⟶ B) (T : Over B)
variable (a : Y ⟶ X) (f : Y ⟶ T.left) (H : IsPullback a f F T.hom)

def nativeRelativeCartesianChartIso317 : Y ≅ pullback T.hom F := H.flip.isoPullback

lemma nativeRelativeCartesianChartIso_toTest317 :
    (nativeRelativeCartesianChartIso317 F T a f H).hom ≫ relativeHilbertFamily197 F T = f :=
  H.flip.isoPullback_hom_fst

lemma nativeRelativeCartesianChartIso_toOriginal317 :
    (nativeRelativeCartesianChartIso317 F T a f H).hom ≫ pullback.snd T.hom F = a :=
  H.flip.isoPullback_hom_snd

def nativeRelativeCartesianPointEquiv317 (n : ℕ) :
    FiniteFlatHilbertPoint195 f n ≃ FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
  nativeFiniteFlatPointAmbientIsoEquiv317 f (relativeHilbertFamily197 F T)
    (nativeRelativeCartesianChartIso317 F T a f H)
    (nativeRelativeCartesianChartIso_toTest317 F T a f H) n

lemma nativeRelativeCartesianPointEquiv_wholeIdeal317 (n : ℕ)
    (Q : FiniteFlatHilbertPoint195 f n) :
    (nativeRelativeCartesianPointEquiv317 F T a f H n Q).val =
      Q.val.comap (nativeRelativeCartesianChartIso317 F T a f H).inv := rfl

private lemma nativeRelativeFirstCompose317 {C : Type*} [Category C]
    {Y0 P0 Y1 P1 T0 T1 : C}
    (e0 : Y0 ⟶ P0) (q : P0 ⟶ P1) (e1 : Y1 ⟶ P1)
    (r0 : P0 ⟶ T0) (r1 : P1 ⟶ T1)
    (f0 : Y0 ⟶ T0) (f1 : Y1 ⟶ T1) (g : T0 ⟶ T1) (v : Y0 ⟶ Y1)
    (he0 : e0 ≫ r0 = f0) (he1 : e1 ≫ r1 = f1)
    (hq : q ≫ r1 = r0 ≫ g) (hv : v ≫ f1 = f0 ≫ g) :
    (e0 ≫ q) ≫ r1 = (v ≫ e1) ≫ r1 :=
  (Category.assoc e0 q r1).trans
    ((congrArg (fun t => e0 ≫ t) hq).trans
      ((Category.assoc e0 r0 g).symm.trans
        ((congrArg (fun t => t ≫ g) he0).trans
          (hv.symm.trans
            ((congrArg (fun t => v ≫ t) he1.symm).trans (Category.assoc v e1 r1).symm)))))

private lemma nativeRelativeSecondCompose317 {C : Type*} [Category C]
    {Y0 P0 Y1 P1 X0 : C}
    (e0 : Y0 ⟶ P0) (q : P0 ⟶ P1) (e1 : Y1 ⟶ P1)
    (r0 : P0 ⟶ X0) (r1 : P1 ⟶ X0)
    (a0 : Y0 ⟶ X0) (a1 : Y1 ⟶ X0) (v : Y0 ⟶ Y1)
    (he0 : e0 ≫ r0 = a0) (he1 : e1 ≫ r1 = a1)
    (hq : q ≫ r1 = r0) (hv : v ≫ a1 = a0) :
    (e0 ≫ q) ≫ r1 = (v ≫ e1) ≫ r1 :=
  (Category.assoc e0 q r1).trans
    ((congrArg (fun t => e0 ≫ t) hq).trans
      (he0.trans
        (hv.symm.trans
          ((congrArg (fun t => v ≫ t) he1.symm).trans (Category.assoc v e1 r1).symm))))

variable {Y0 Y1 : Scheme.{u}} {T0 T1 : Over B} (g : T0 ⟶ T1)
variable (a0 : Y0 ⟶ X) (f0 : Y0 ⟶ T0.left) (H0 : IsPullback a0 f0 F T0.hom)
variable (a1 : Y1 ⟶ X) (f1 : Y1 ⟶ T1.left) (H1 : IsPullback a1 f1 F T1.hom)
variable (v : Y0 ⟶ Y1) (ha : v ≫ a1 = a0) (hf : v ≫ f1 = f0 ≫ g.left)

include ha hf in
/-- The actual literal197 ambient map is compared by BOTH native projections. -/
lemma nativeRelativeCartesianChartIso_natural317 :
    (nativeRelativeCartesianChartIso317 F T0 a0 f0 H0).hom ≫
        relativeHilbertAmbientMap197 F g =
      v ≫ (nativeRelativeCartesianChartIso317 F T1 a1 f1 H1).hom := by
  apply pullback.hom_ext
  · exact nativeRelativeFirstCompose317 _ _ _ _ _ _ _ _ _
      (nativeRelativeCartesianChartIso_toTest317 F T0 a0 f0 H0)
      (nativeRelativeCartesianChartIso_toTest317 F T1 a1 f1 H1)
      (relativeHilbertAmbientMap_fst197 F g) hf
  · exact nativeRelativeSecondCompose317 _ _ _ _ _ _ _ _
      (nativeRelativeCartesianChartIso_toOriginal317 F T0 a0 f0 H0)
      (nativeRelativeCartesianChartIso_toOriginal317 F T1 a1 f1 H1)
      (relativeHilbertAmbientMap_snd197 F g) ha

private lemma nativeRelativeInverseDiagram317 {C : Type*} [Category C]
    {Y0 P0 Y1 P1 : C} (e0 : Y0 ≅ P0) (e1 : Y1 ≅ P1)
    (q : P0 ⟶ P1) (v : Y0 ⟶ Y1) (h : e0.hom ≫ q = v ≫ e1.hom) :
    e0.inv ≫ v = q ≫ e1.inv := by
  apply (cancel_mono e1.hom).mp
  exact (Category.assoc e0.inv v e1.hom).trans
    ((congrArg (fun t => e0.inv ≫ t) h.symm).trans
      ((e0.inv_hom_id_assoc q).trans
        ((Category.assoc q e1.inv e1.hom).trans
          ((congrArg (fun t => q ≫ t) e1.inv_hom_id).trans (Category.comp_id q))).symm))

include ha hf in
/-- The original whole physical Cartesian family reduction agrees with the
literal197 functor, and hence with any genuine representing NatIso312. -/
lemma nativeRelativeCartesianPointEquiv_natural317
    (Hv : IsPullback v f0 f1 g.left) (n : ℕ)
    (Q : FiniteFlatHilbertPoint195 f1 n) :
    nativeRelativeCartesianPointEquiv317 F T0 a0 f0 H0 n
        (finiteFlatHilbertBaseChange195 v f0 f1 g.left Hv n Q) =
      (relativeFiniteFlatHilbertFunctor197 F n).map g.op
        (nativeRelativeCartesianPointEquiv317 F T1 a1 f1 H1 n Q) := by
  have hinv : (nativeRelativeCartesianChartIso317 F T0 a0 f0 H0).inv ≫ v =
      relativeHilbertAmbientMap197 F g ≫
        (nativeRelativeCartesianChartIso317 F T1 a1 f1 H1).inv :=
    nativeRelativeInverseDiagram317 _ _ _ _
      (nativeRelativeCartesianChartIso_natural317 F g a0 f0 H0 a1 f1 H1 v ha hf)
  apply Subtype.ext
  exact (Q.val.comap_comp (nativeRelativeCartesianChartIso317 F T0 a0 f0 H0).inv v).symm.trans
    ((congrArg Q.val.comap hinv).trans
      (Q.val.comap_comp (relativeHilbertAmbientMap197 F g)
        (nativeRelativeCartesianChartIso317 F T1 a1 f1 H1).inv))

end PfaffianDescent
end
