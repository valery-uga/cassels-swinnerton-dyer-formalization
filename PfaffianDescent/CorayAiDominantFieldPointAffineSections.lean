import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option autoImplicit false

/-- A dominant field point meets every nonempty open in its entire source.
This is an actual preimage equality, not a supplied image certificate. -/
theorem dominantFieldPoint_preimage_nonemptyOpen_eq_top001
    {E : Type u} [Field E] (X : Scheme.{u})
    (p : Spec (.of E) ⟶ X) [IsDominant p]
    (U : X.Opens) [hU0 : Nonempty U] : p ⁻¹ᵁ U = ⊤ := by
  let z0 := Classical.choice hU0
  obtain ⟨z, hz⟩ := p.denseRange.exists_mem_open U.isOpen
    (show (U : Set X).Nonempty from ⟨z0.1, z0.2⟩)
  apply top_unique
  intro w _
  change p w ∈ U
  change p z ∈ U at hz
  exact (Subsingleton.elim w z) ▸ hz

/-- The literal affine section map of a dominant field point is injective,
commutes with the original ground structure map, and has a finite-type
source over that same ground map. None of these conclusions is assumed. -/
theorem integralScheme_dominantFieldPoint_affineSection_embedding001
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [LocallyOfFiniteType pi]
    (p : Spec (.of E) ⟶ X) [IsDominant p] [QuasiCompact p]
    (hBase : p ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    ∃ g : Γ(X, U) →+* E,
      Function.Injective g ∧ g.comp beta = algebraMap K E ∧ beta.FiniteType := by
  classical
  let hPi : U ≤ pi ⁻¹ᵁ (⊤ : (Spec (.of K)).Opens) := by simp
  letI : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isDominant p
  have hPreTop := dominantFieldPoint_preimage_nonemptyOpen_eq_top001 X p U
  let hPre : (⊤ : (Spec (.of E)).Opens) ≤ p ⁻¹ᵁ U := le_of_eq hPreTop.symm
  let r := p.appLE U ⊤ hPre
  let delta := (Spec (.of E)).presheaf.map (homOfLE hPre).op
  have hArrow : homOfLE hPre = eqToHom hPreTop.symm := Subsingleton.elim _ _
  letI : IsIso delta := by
    dsimp only [delta]
    rw [hArrow]
    infer_instance
  have hr : Function.Injective r.hom :=
    (ConcreteCategory.bijective_of_isIso delta).1.comp (p.app_injective U)
  let g : Γ(X, U) →+* E := (Scheme.ΓSpecIso (.of E)).hom.hom.comp r.hom
  have hg : Function.Injective g :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of E)).hom).1.comp hr
  have hTop : pi.appLE ⊤ U hPi ≫ r =
      (Spec.map (CommRingCat.ofHom (algebraMap K E))).appTop := by
    calc
      _ = (p ≫ pi).appLE ⊤ ⊤
          (hPre.trans ((Opens.map p.base).map (homOfLE hPi)).le) :=
        Scheme.Hom.appLE_comp_appLE p pi ⊤ U ⊤ hPi hPre
      _ = (p ≫ pi).appTop := by
        change (p ≫ pi).appTop ≫ (Spec (.of E)).presheaf.map
          (𝟙 (⊤ : (Spec (.of E)).Opens)).op = (p ≫ pi).appTop
        simp
      _ = _ := congrArg (fun f : Spec (.of E) ⟶ Spec (.of K) => f.appTop) hBase
  have hScalar :
      (Scheme.ΓSpecIso (.of K)).inv ≫ pi.appLE ⊤ U hPi ≫ r ≫
        (Scheme.ΓSpecIso (.of E)).hom = CommRingCat.ofHom (algebraMap K E) := by
    rw [← Category.assoc (pi.appLE ⊤ U hPi) r (Scheme.ΓSpecIso (.of E)).hom, hTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have hCoeff : g.comp
      ((pi.appLE ⊤ U hPi).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) =
      algebraMap K E := by
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of E => f.hom) hScalar
  have hFinite :
      ((pi.appLE ⊤ U hPi).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).FiniteType :=
    (pi.finiteType_appLE (isAffineOpen_top _) hU hPi).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  exact ⟨g, hg, hCoeff, hFinite⟩

end PfaffianDescent.Coray
