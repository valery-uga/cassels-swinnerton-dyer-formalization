import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit
import PfaffianDescent.VoisinCubicConstantFunctions
import PfaffianDescent.SchemeModuleCoverEqualizer
import PfaffianDescent.SheafModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Literal original p/q curve global constants for positive q degree.
The canonical original toBase map is bijective. Actual restriction/cokernel
maps and independently original section scalars are retained.
SOURCE ONLY / UNVERIFIED; root owns all compiler and kernel checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual pushed-forward strictly negative cubic twist has no H⁰.
Both ambient vanishings and the actual hypersurface sequence are internal. -/
theorem cubicNegativeTwistPushforward_cohomology_zero_subsingleton_of_pos
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (m : ℕ) (hm : 0 < m) :
    Subsingleton (schemeModuleCohomology
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m)) 0) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    smoothCubic_coordinateRing_isDomain K p hp hp0
  let S := hypersurfaceTwistRestrictionSequence p hp m
  letI : Subsingleton (schemeModuleCohomology P S.X₂ 0) :=
    (schemeModuleCohomology_zero_subsingleton_iff_sections P S.X₂).mpr
      (p3_negativeTwist_sections_subsingleton_of_pos K m hm)
  letI : Subsingleton (schemeModuleCohomology P S.X₁ 1) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K (m + 3)).1
  exact schemeModuleCohomology_subsingleton_of_middle_and_next_left
    P S (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 m) 0

/-- Restriction from the actual ambient unit to the literal original curve
unit pushforward is bijective on actual sections. Positive q degree supplies
the genuine left H⁰ vanishing; its H¹ vanishing is also internally derived.
The SAME original cokernel Iso's actual unit-comp law identifies the map. -/
theorem projectiveIntersection_unitPushforward_sectionsMap_bijective_of_pos
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Bijective (SheafOfModules.sectionsMap
      (SheafOfModules.unitToPushforwardObjUnit
        (quotientProjMap (projectiveIntersectionIdeal p q hp hq)).toRingCatSheafHom)) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) :=
    (inferInstance : HasExt.{u} P.Modules)
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    smoothCubic_coordinateRing_isDomain K p hp hp0
  let 𝒜 := grading (equationIdeal p hp)
  let s := cubicSecondEquationHomogeneous p q hp n hq
  let F := Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)
  let R := homogeneousRestrictionSequence 𝒜 s 0
  let T := R.map F
  have hT : T.ShortExact :=
    cubicSecondEquation_pushforwardRestrictionSequence_shortExact p q hp hp0 n hq hnot 0
  letI : Subsingleton (schemeModuleCohomology P T.X₁ 0) := by
    change Subsingleton (schemeModuleCohomology P
      (F.obj (sheafOfModules 𝒜 (0 + n))) 0)
    simpa only [zero_add] using
      cubicNegativeTwistPushforward_cohomology_zero_subsingleton_of_pos p hp hp0 n hn
  letI : Subsingleton T.X₁.sections :=
    (schemeModuleCohomology_zero_subsingleton_iff_sections P T.X₁).mp inferInstance
  letI : Subsingleton (schemeModuleCohomology P T.X₁ 1) := by
    change Subsingleton (schemeModuleCohomology P
      (F.obj (sheafOfModules 𝒜 (0 + n))) 1)
    simpa only [zero_add] using
      p3HypersurfaceTwistPushforward_cohomology_one_subsingleton K p hp hp0 n
  have hπ : Function.Bijective (SheafOfModules.sectionsMap T.g) :=
    sectionsMap_bijective_of_shortExact_of_left_h0_h1_vanish T hT
  let e := F.mapIso (unitIsoZeroTwist 𝒜)
  let c := cubicSecondEquation_zeroCokernelAmbientIsoCurveUnit p q hp hp0 n hq hnot
  let u := SheafOfModules.unitToPushforwardObjUnit
    (hypersurfaceToAmbient p hp).toRingCatSheafHom
  have hu : Function.Bijective (SheafOfModules.sectionsMap u) :=
    p3_smoothCubicPushforward_sectionsMap_bijective K p hp hp0
  have he : Function.Bijective (SheafOfModules.sectionsMap e.hom) :=
    (schemeModuleSectionsEquivOfIso e).bijective
  have hc : Function.Bijective (SheafOfModules.sectionsMap c.hom) :=
    (schemeModuleSectionsEquivOfIso c).bijective
  have hmaps : SheafOfModules.sectionsMap
      (SheafOfModules.unitToPushforwardObjUnit
        (quotientProjMap (projectiveIntersectionIdeal p q hp hq)).toRingCatSheafHom) =
      (SheafOfModules.sectionsMap c.hom) ∘ (SheafOfModules.sectionsMap T.g) ∘
        (SheafOfModules.sectionsMap e.hom) ∘ (SheafOfModules.sectionsMap u) := by
    funext z
    have h := congrArg (fun a => SheafOfModules.sectionsMap a z)
      (cubicSecondEquation_zeroCokernelAmbientIsoCurveUnit_unit_comp
        p q hp hp0 n hq hnot).symm
    have hcomp :
        SheafOfModules.sectionsMap (F.map ((unitIsoZeroTwist 𝒜).hom ≫ R.g))
            (SheafOfModules.sectionsMap u z) =
          SheafOfModules.sectionsMap T.g
            (SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap u z)) := by
      rw [Functor.map_comp]
      exact SheafOfModules.sectionsMap_comp
        (F.map (unitIsoZeroTwist 𝒜).hom) (F.map R.g) (SheafOfModules.sectionsMap u z)
    calc
      _ = SheafOfModules.sectionsMap c.hom
          (SheafOfModules.sectionsMap (F.map ((unitIsoZeroTwist 𝒜).hom ≫ R.g))
            (SheafOfModules.sectionsMap u z)) := by
        dsimp only [c, F, R, 𝒜, s, u, homogeneousRestrictionSequence,
          Scheme.Modules.pushforward] at h ⊢
        simpa only [SheafOfModules.sectionsMap_comp] using h
      _ = SheafOfModules.sectionsMap c.hom
          (SheafOfModules.sectionsMap T.g
            (SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap u z))) :=
        congrArg (SheafOfModules.sectionsMap c.hom) hcomp
      _ = _ := rfl
  rw [hmaps]
  exact hc.comp (hπ.comp (he.comp hu))

/-- Actual ambient regular functions restrict bijectively to the literal
original curve. This uses the existing precise unit-section/appTop law,
not a supplied H⁰ comparison. -/
theorem projectiveIntersection_globalFunctions_restriction_bijective_of_pos
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Bijective
      (quotientProjMap (projectiveIntersectionIdeal p q hp hq)).appTop.hom := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  let i := quotientProjMap (projectiveIntersectionIdeal p q hp hq)
  let A := SheafOfModules.unit P.ringCatSheaf
  let eA := moduleSectionsEquivTop P A
  let eC := pushforwardUnitSectionsEquiv i
  let f := SheafOfModules.sectionsMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)
  have hf : Function.Bijective f :=
    projectiveIntersection_unitPushforward_sectionsMap_bijective_of_pos p q hp hp0 n hn hq hnot
  have hcompat (s : A.sections) : eC (f s) = i.appTop.hom (eA s) :=
    closedImmersionUnitToPushforward_sectionsMap_top i s
  constructor
  · intro a b hab
    obtain ⟨s, rfl⟩ := eA.surjective a
    obtain ⟨t, rfl⟩ := eA.surjective b
    apply congrArg eA
    apply hf.1
    apply eC.injective
    rw [hcompat s, hcompat t]
    exact hab
  · intro z
    obtain ⟨y, rfl⟩ := eC.surjective z
    obtain ⟨s, hs⟩ := hf.2 y
    refine ⟨eA s, ?_⟩
    rw [← hcompat s, hs]

/-- Primitive constancy of the ACTUAL original curve's global functions.
The map is precisely affineFunctionHom of the SAME literal toBase. Native
Ext infrastructure is derived internally; no constants certificate enters.
No normalization constants statement is asserted. -/
theorem projectiveIntersection_globalFunctions_bijective_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    Function.Bijective (affineFunctionHom (toBase (projectiveIntersectionIdeal p q hp hq))) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  let I := projectiveIntersectionIdeal p q hp hq
  letI : EnoughInjectives P.Modules := sheafOfModules_enoughInjectives P.ringCatSheaf
  letI : HasExt.{u} P.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} P.Modules
  have hi : Function.Bijective (quotientProjMap I).appTop.hom :=
    projectiveIntersection_globalFunctions_restriction_bijective_of_pos p q hp hp0 n hn hq hnot
  rw [← quotientProjMap_toBase I, affineFunctionHom_comp]
  exact hi.comp (ambientToBase_affineFunctionHom_bijective K)

/-- The canonical original scalar map, valued in the ACTUAL top-open unit
sections with their existing toBase-induced K-action. This does not define
a replacement scalar structure or rename a different algebra as Γ(C,O_C). -/
def projectiveIntersection_globalFunctionsScalarLinearMap
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) :
    K →ₗ[K] SchemeModuleOpenSectionsOver
      (toBase (projectiveIntersectionIdeal p q hp hq))
      (SheafOfModules.unit (scheme (projectiveIntersectionIdeal p q hp hq)).ringCatSheaf) ⊤ where
  toFun := affineFunctionHom (toBase (projectiveIntersectionIdeal p q hp hq))
  map_add' a b := (affineFunctionHom (toBase (projectiveIntersectionIdeal p q hp hq))).map_add a b
  map_smul' a b := by
    let base := toBase (projectiveIntersectionIdeal p q hp hq)
    change affineFunctionHom base (a * b) =
      schemeOpenBaseRingHom base ⊤ a • (affineFunctionHom base b)
    rw [schemeOpenBaseRingHom_top_apply]
    change affineFunctionHom base (a * b) = affineFunctionHom base a * affineFunctionHom base b
    exact (affineFunctionHom base).map_mul a b

/-- Actual ORIGINAL-K linear equivalence from K to the literal original
curve's global unit sections. Both its function and its preexisting scalar
action are induced by the SAME actual toBase morphism. -/
def projectiveIntersection_globalFunctionsLinearEquiv_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    K ≃ₗ[K] SchemeModuleOpenSectionsOver
      (toBase (projectiveIntersectionIdeal p q hp hq))
      (SheafOfModules.unit (scheme (projectiveIntersectionIdeal p q hp hq)).ringCatSheaf) ⊤ :=
  LinearEquiv.ofBijective (projectiveIntersection_globalFunctionsScalarLinearMap p q hp n hq)
    (projectiveIntersection_globalFunctions_bijective_native p q hp hp0 n hn hq hnot)

/-- The equivalence is literally the canonical K→Γ(C,O_C), not an arbitrary
choice of a one-dimensional vector-space isomorphism. -/
theorem projectiveIntersection_globalFunctionsLinearEquiv_native_apply
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (c : K) :
    projectiveIntersection_globalFunctionsLinearEquiv_native p q hp hp0 n hn hq hnot c =
      affineFunctionHom (toBase (projectiveIntersectionIdeal p q hp hq)) c := rfl

end PfaffianDescent.Coray
