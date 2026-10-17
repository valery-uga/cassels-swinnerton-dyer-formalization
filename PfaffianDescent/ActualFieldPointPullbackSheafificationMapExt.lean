import PfaffianDescent.ActualPointLocalAdjunctionSectionEvaluation
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.RingTheory.KrullDimension.Zero

/-! SOURCE ONLY / UNVERIFIED. Genuine local raw sections detect actual
maps out of a point pullback of a sheafification. Both real adjunctions
prove this generation property; no spanning certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

private lemma fieldModule_empty_subsingleton
    {L : Type u} [Field L] (N : (Spec (.of L)).Modules) :
    Subsingleton Γ(N, ⊥) := by
  change Subsingleton ((modulesSpecToSheaf.obj N).obj.obj (op ⊥))
  have ht := (modulesSpecToSheaf.obj N).isTerminalOfEmpty
  have hz : IsZero ((modulesSpecToSheaf.obj N).obj.obj (op ⊥)) :=
    IsZero.of_iso (isZero_zero (ModuleCat L))
      ((isZero_zero (ModuleCat L)).isoIsTerminal ht).symm
  exact ModuleCat.subsingleton_of_isZero hz

/- Equality is checked on actual point classes of the actual raw
sheafification unit. This retains both actual adjunctions and maps. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualFieldPointPullbackSheafificationMap_ext
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (A : PresheafOfModules X.ringCatSheaf.obj)
    (N : (Spec (.of L)).Modules)
    (d₁ d₂ : (Scheme.Modules.pullback q).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj A) ⟶ N)
    (h : ∀ (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤) (a : A.obj (op U)),
      (moduleSpecΓFunctor (R := .of L)).map d₁
        (actualPointLocalSectionClass q
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj A) U hU
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app A).app (op U) a)) =
      (moduleSpecΓFunctor (R := .of L)).map d₂
        (actualPointLocalSectionClass q
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj A) U hU
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app A).app (op U) a))) :
    d₁ = d₂ := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let sa := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let pa := Scheme.Modules.pullbackPushforwardAdjunction q
  apply (pa.homEquiv _ _).injective
  apply (sa.homEquiv _ _).injective
  ext1 U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let x₀ : Spec (.of L) := (⊥ : PrimeSpectrum L)
  by_cases hx : q x₀ ∈ U.unop
  · have hU : q ⁻¹ᵁ U.unop = ⊤ := by
      ext x
      change q x ∈ U.unop ↔ True
      simpa only [Subsingleton.elim x x₀, hx, true_iff]
    let t := eqToHom (congrArg op hU)
    apply (ConcreteCategory.bijective_of_isIso ((Scheme.Modules.presheaf N).map t)).injective
    have h₁ := actualPointLocalAdjunctionSectionEvaluation q (F.obj A) N U.unop hU
      ((sa.unit.app A).app U a) d₁
    have h₂ := actualPointLocalAdjunctionSectionEvaluation q (F.obj A) N U.unop hU
      ((sa.unit.app A).app U a) d₂
    exact h₁.symm.trans ((h U.unop hU a).trans h₂)
  · have hU : q ⁻¹ᵁ U.unop = ⊥ := by
      ext x
      change q x ∈ U.unop ↔ False
      simpa only [Subsingleton.elim x x₀, hx, false_iff]
    have hs : Subsingleton (N.val.obj (op (q ⁻¹ᵁ U.unop))) := by
      rw [hU]
      exact fieldModule_empty_subsingleton N
    exact @Subsingleton.elim _ hs _ _

end PfaffianDescent
