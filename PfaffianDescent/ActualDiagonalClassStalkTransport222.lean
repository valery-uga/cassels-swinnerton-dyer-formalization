import PfaffianDescent.ActualDiagonalPointSummandStalk222
import PfaffianDescent.CubicPointTraceFieldBaseChangeDiagonalExtZero

/-! Exact native Ext extraction at the actual rational diagonal stalk.
This is a transport cut, not an original-geometric nonvanishing factory. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Invertible actual degree-zero source transport reflects native Ext zero. -/
lemma ext_precomp_isIso_eq_zero_iff222
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {M N O : C} (a : M ⟶ N) [IsIso a] (n : ℕ) (z : Ext.{w} N O n) :
    (Ext.mk₀ a).comp z (zero_add n) = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hi := congrArg (fun t => (Ext.mk₀ (inv a)).comp t (zero_add n)) h
    simpa only [Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, Ext.mk₀_id_comp,
      Ext.comp_zero] using hi
  · intro h
    rw [h, Ext.comp_zero]

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))
  [IsClosedImmersion i]
  [HasExt.{u} X.Modules]
  [HasExt.{u} (schemeBaseChangeToField (L := L) X p).Modules]

/-- The actual diagonal extraction equals invertible native source transport
of the actual pulled-back class, at the literal tensor diagonal point. -/
theorem cubicPointTraceFieldBaseChangeDiagonalExtClass_stalk222
    (N : X.Modules) (n : ℕ)
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n) :
    let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
    let j := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi
    let x := j (d (default : Spec (.of L)))
    ∀ hExtStalk : HasExt.{u + 1} (ModuleCat
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x)),
    letI := hExtStalk
    let H := schemeModuleStalkModuleFunctor (schemeBaseChangeToField (L := L) X p) x
    let a := H.map (cubicPointTraceFieldBaseChangePointSummandSection K L p i hi) ≫
      H.map (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).inv
    (cubicPointTraceFieldBaseChangeDiagonalExtClass K L p i hi N n z).mapExactFunctor H =
      (Ext.mk₀ a).comp
        ((cubicPointTraceFieldBaseChangeFlatPullbackExtMap
          (cubicPointTraceFieldBaseChangeProjection K L p) _ N n z).mapExactFunctor H)
        (zero_add n) := by
  dsimp only
  intro hExtStalk
  letI := hExtStalk
  rw [cubicPointTraceFieldBaseChangeDiagonalExtClass,
    cubicPointTraceFieldBaseChangeExtendedSupportExtMap,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc]

/-- Diagonal extraction reflects zero on this native stalk. A later original
caller must prove the actual flat pullback stalk nonzero from its constructed
coefficient-one class; that result is not silently assumed here. -/
theorem cubicPointTraceFieldBaseChangeDiagonalExtClass_stalk_zero_iff222
    (N : X.Modules) (n : ℕ)
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n) :
    let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
    let j := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi
    let x := j (d (default : Spec (.of L)))
    ∀ hExtStalk : HasExt.{u + 1} (ModuleCat
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x)),
    letI := hExtStalk
    let H := schemeModuleStalkModuleFunctor (schemeBaseChangeToField (L := L) X p) x
    (cubicPointTraceFieldBaseChangeDiagonalExtClass K L p i hi N n z).mapExactFunctor H = 0 ↔
      (cubicPointTraceFieldBaseChangeFlatPullbackExtMap
        (cubicPointTraceFieldBaseChangeProjection K L p) _ N n z).mapExactFunctor H = 0 := by
  dsimp only
  intro hExtStalk
  letI := hExtStalk
  let H := schemeModuleStalkModuleFunctor (schemeBaseChangeToField (L := L) X p)
    ((cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)
      ((cubicPointTraceFieldBaseChangeTensorDiagonal K L) (default : Spec (.of L))))
  letI : IsIso (H.map (cubicPointTraceFieldBaseChangePointSummandSection K L p i hi)) :=
    cubicPointTraceFieldBaseChangePointSummandSection_stalk_isIso222 K L p i hi
  rw [cubicPointTraceFieldBaseChangeDiagonalExtClass_stalk222 K L p i hi N n z hExtStalk]
  exact ext_precomp_isIso_eq_zero_iff222 _ _ _

end
end PfaffianDescent
