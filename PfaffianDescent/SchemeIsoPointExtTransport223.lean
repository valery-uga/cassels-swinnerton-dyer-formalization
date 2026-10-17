import PfaffianDescent.SchemeIsoClosedPointSupportTransport223
import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatExt

/-! Native Ext transport through a genuine scheme isomorphism preserves
nonzero and the actual unit precomposition, with canonical support maps. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section GenericExtCuts
universe uC vC uD vD wC wD
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The literal native pullback/precomposition/postcomposition as one
additive map, with all category dictionaries fixed before specialization. -/
private def schemeIsoExtCoordinateAddHomCut223
    {Q N : C} {Q' N' : D} (A : F.obj Q ≅ Q') (B : F.obj N ≅ N')
    (n : ℕ) : Ext.{wC} Q N n →+ Ext.{wD} Q' N' n :=
  (extPostcompIsoOfIso B).toAddMonoidHom.comp
    ((extPrecompIsoOfIso A).toAddMonoidHom.comp (F.mapExtAddHom Q N n))

private theorem schemeIsoExtCoordinate_zero_iff_cut223
    [F.Full] [F.Faithful] [EnoughInjectives C] [F.PreservesInjectiveObjects]
    {Q N : C} {Q' N' : D} (A : F.obj Q ≅ Q') (B : F.obj N ≅ N')
    (n : ℕ) (z : Ext.{wC} Q N n) :
    schemeIsoExtCoordinateAddHomCut223 F A B n z = 0 ↔ z = 0 := by
  let L : Ext.{wC} Q N n →+ Ext.{wD} Q' N' n :=
    schemeIsoExtCoordinateAddHomCut223 F A B n
  have hi : Function.Injective L :=
    (extPostcompIsoOfIso B).injective.comp
      ((extPrecompIsoOfIso A).injective.comp
        (F.mapExt_bijective_of_preservesInjectiveObjects Q N n).injective)
  constructor
  · intro hz
    exact hi (hz.trans L.map_zero.symm)
  · intro hz
    exact (congrArg (fun x => L x) hz).trans L.map_zero

private theorem schemeIsoExtCoordinate_unit_cut223
    {U Q N : C} {U' Q' N' : D}
    (A : F.obj Q ≅ Q') (B : F.obj N ≅ N') (V : F.obj U ≅ U')
    (q : U ⟶ Q) (q' : U' ⟶ Q')
    (hsquare : q' ≫ A.inv = V.inv ≫ F.map q)
    (n : ℕ) (z : Ext.{wC} Q N n) :
    (Ext.mk₀ q').comp (schemeIsoExtCoordinateAddHomCut223 F A B n z) (zero_add n) =
      ((Ext.mk₀ V.inv).comp
        (((Ext.mk₀ q).comp z (zero_add n)).mapExactFunctor F)
        (zero_add n)).comp (Ext.mk₀ B.hom) (add_zero n) := by
  change (Ext.mk₀ q').comp
    (((Ext.mk₀ A.inv).comp (z.mapExactFunctor F) (zero_add n)).comp
      (Ext.mk₀ B.hom) (add_zero n)) (zero_add n) = _
  rw [← Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, hsquare,
    ← Ext.mk₀_comp_mk₀_assoc, ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp]

private theorem schemeIsoExtMappedUnit_zero_cut223
    {U Q N : C} {U' N' : D} (V : F.obj U ≅ U') (B : F.obj N ≅ N')
    (q : U ⟶ Q) (n : ℕ) (z : Ext.{wC} Q N n)
    (hz : (Ext.mk₀ q).comp z (zero_add n) = 0) :
    ((Ext.mk₀ V.inv).comp
      (((Ext.mk₀ q).comp z (zero_add n)).mapExactFunctor F)
      (zero_add n)).comp (Ext.mk₀ B.hom) (add_zero n) = 0 := by
  rw [hz, Ext.mapExactFunctor_zero, Ext.comp_zero, Ext.zero_comp]

end GenericExtCuts

section
variable {Y Z T : Scheme.{u}} (e : Z ≅ Y) (i : T ⟶ Y) [IsClosedImmersion i]
  [HasExt.{u} Y.Modules] [HasExt.{u} Z.Modules]
  (N : Y.Modules) (N' : Z.Modules)
  (B : (Scheme.Modules.pullback e.hom).obj N ≅ N') (n : ℕ)

/-- Entire native Ext class with the actual coefficient-scheme support and
the actual target twist coordinate. It does not choose a replacement class. -/
def schemeIsoClosedPointExtTransport223
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit T.ringCatSheaf)) N n) :
    Ext.{u} ((Scheme.Modules.pushforward (i ≫ e.inv)).obj
      (SheafOfModules.unit T.ringCatSheaf)) N' n :=
  let P : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback e.hom
  let Q : Y.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let Q' : Z.Modules := (Scheme.Modules.pushforward (i ≫ e.inv)).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let A : P.obj Q ≅ Q' := schemeIsoClosedPointPullbackSupportIso223 e i
  schemeIsoExtCoordinateAddHomCut223 (C := Y.Modules) (D := Z.Modules) P
    (Q := Q) (N := N) (Q' := Q') (N' := N') A B n z

/-- Genuine geometric pullback is an equivalence; the canonical endpoint
isomorphisms reflect zero in every native Ext degree. -/
theorem schemeIsoClosedPointExtTransport_eq_zero_iff223
    [EnoughInjectives Y.Modules]
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit T.ringCatSheaf)) N n) :
    schemeIsoClosedPointExtTransport223 e i N N' B n z = 0 ↔ z = 0 := by
  let P : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback e.hom
  let Q : Y.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let Q' : Z.Modules := (Scheme.Modules.pushforward (i ≫ e.inv)).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let A : P.obj Q ≅ Q' := schemeIsoClosedPointPullbackSupportIso223 e i
  let E : Y.Modules ≌ Z.Modules :=
    cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoEquivalence e
  letI : P.IsEquivalence := E.isEquivalence_functor
  exact schemeIsoExtCoordinate_zero_iff_cut223
    (C := Y.Modules) (D := Z.Modules) P
    (Q := Q) (N := N) (Q' := Q') (N' := N') A B n z

/-- Canonical unit precomposition is actual geometric pullback of the SAME
original unit precomposition, followed by the derived target coordinate. -/
theorem schemeIsoClosedPointExtTransport_unit223
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit T.ringCatSheaf)) N n) :
    (Ext.mk₀.{u} (C := Z.Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ e.inv))).comp
      (schemeIsoClosedPointExtTransport223 e i N N' B n z) (zero_add n) =
    ((Ext.mk₀.{u} (C := Z.Modules)
      (cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).inv).comp
      (Ext.mapExactFunctor.{u, u} (C := Y.Modules) (D := Z.Modules)
        (Scheme.Modules.pullback e.hom)
        ((Ext.mk₀.{u} (C := Y.Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp z
          (zero_add n)))
      (zero_add n)).comp (Ext.mk₀.{u} (C := Z.Modules) B.hom) (add_zero n) := by
  let P : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback e.hom
  let U : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let U' : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let Q : Y.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let Q' : Z.Modules := (Scheme.Modules.pushforward (i ≫ e.inv)).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let A : P.obj Q ≅ Q' := schemeIsoClosedPointPullbackSupportIso223 e i
  let V : P.obj U ≅ U' := cubicPointTraceFieldBaseChangePullbackUnitIso e.hom
  let q : U ⟶ Q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let q' : U' ⟶ Q' :=
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ e.inv)
  let w : Ext.{u} U N n :=
    (Ext.mk₀.{u} (C := Y.Modules) q).comp z (zero_add n)
  let w' : Ext.{u} (P.obj U) (P.obj N) n :=
    Ext.mapExactFunctor.{u, u} (C := Y.Modules) (D := Z.Modules) P w
  let v : Ext.{u} U' N' n :=
    ((Ext.mk₀.{u} (C := Z.Modules) V.inv).comp w' (zero_add n)).comp
      (Ext.mk₀.{u} (C := Z.Modules) B.hom) (add_zero n)
  have hsquare : q' ≫ A.inv = V.inv ≫ P.map q :=
    schemeIsoClosedPointPullbackSupportIso_unit_inv223 e i
  have hunit :
      (Ext.mk₀.{u} (C := Z.Modules) q').comp
        (schemeIsoExtCoordinateAddHomCut223
          (C := Y.Modules) (D := Z.Modules) P
          (Q := Q) (N := N) (Q' := Q') (N' := N') A B n z)
        (zero_add n) = v :=
    schemeIsoExtCoordinate_unit_cut223.{u + 1, u, u + 1, u, u, u}
      (C := Y.Modules) (D := Z.Modules) P
      (U := U) (Q := Q) (N := N) (U' := U') (Q' := Q') (N' := N')
      A B V q q' hsquare n z
  exact hunit

/-- Zero original unit image gives zero transported unit image through the
actual support/twist maps; no injectivity or comparison certificate is used. -/
theorem schemeIsoClosedPointExtTransport_unit_eq_zero223
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit T.ringCatSheaf)) N n)
    (hz : (Ext.mk₀.{u} (C := Y.Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp z
      (zero_add n) = 0) :
    (Ext.mk₀.{u} (C := Z.Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ e.inv))).comp
      (schemeIsoClosedPointExtTransport223 e i N N' B n z) (zero_add n) = 0 := by
  let P : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback e.hom
  let U : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let U' : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let Q : Y.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let Q' : Z.Modules := (Scheme.Modules.pushforward (i ≫ e.inv)).obj
    (SheafOfModules.unit T.ringCatSheaf)
  let V : P.obj U ≅ U' := cubicPointTraceFieldBaseChangePullbackUnitIso e.hom
  let q : U ⟶ Q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let q' : U' ⟶ Q' :=
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ e.inv)
  let w : Ext.{u} U N n :=
    (Ext.mk₀.{u} (C := Y.Modules) q).comp z (zero_add n)
  let w' : Ext.{u} (P.obj U) (P.obj N) n :=
    Ext.mapExactFunctor.{u, u} (C := Y.Modules) (D := Z.Modules) P w
  let v : Ext.{u} U' N' n :=
    ((Ext.mk₀.{u} (C := Z.Modules) V.inv).comp w' (zero_add n)).comp
      (Ext.mk₀.{u} (C := Z.Modules) B.hom) (add_zero n)
  have hunit :
      (Ext.mk₀.{u} (C := Z.Modules) q').comp
        (schemeIsoClosedPointExtTransport223 e i N N' B n z) (zero_add n) = v :=
    schemeIsoClosedPointExtTransport_unit223 e i N N' B n z
  have hzero : v = 0 :=
    schemeIsoExtMappedUnit_zero_cut223.{u + 1, u, u + 1, u, u, u}
      (C := Y.Modules) (D := Z.Modules) P
      (U := U) (Q := Q) (N := N) (U' := U') (N' := N') V B q n z hz
  exact hunit.trans hzero

end
end PfaffianDescent
