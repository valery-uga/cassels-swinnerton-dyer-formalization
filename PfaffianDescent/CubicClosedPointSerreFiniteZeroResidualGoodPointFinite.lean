import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenFibreIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedFibreProperties
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedInfinityEndpointIso

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_goodOpen_fieldPoint_finite
    {E : Type u} [Field E] {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [IsProper g] (s : Spec (.of E) ⟶ Y)
    (hs : s (IsLocalRing.closedPoint E) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) :
    Finite (pullback g s : Scheme) := by
  let U := cubicClosedPointSerreFiniteZeroResidual_goodOpen g
  have hr : Set.range s ⊆ Set.range U.ι := by
    rintro _ ⟨z,rfl⟩
    rw [U.range_ι]
    exact (congrArg s (Subsingleton.elim z (IsLocalRing.closedPoint E))) ▸ hs
  let u := IsOpenImmersion.lift U.ι s hr
  have hu : u ≫ U.ι = s := IsOpenImmersion.lift_fac U.ι s hr
  let gU := g.resLE U (g ⁻¹ᵁ U) le_rfl
  letI : IsFinite gU := by
    dsimp [gU]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact cubicClosedPointSerreFiniteZeroResidual_goodOpen_finite g
  letI : Finite (pullback gU u : Scheme) :=
    cubicClosedPointSerreFiniteZeroResidual_finiteToField_finite (pullback.snd gU u)
  let v := cubicClosedPointSerreFiniteZeroResidual_openFibreIso g U u ≪≫
    pullback.congrHom rfl hu
  exact Finite.of_injective v.inv v.inv.injective

theorem cubicClosedPointSerreFiniteZeroResidual_fieldBaseChange_finite_descend
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    {D : Scheme.{u}} (d : D ⟶ Spec (.of K))
    [Finite (pullback d (Spec.map (CommRingCat.ofHom (algebraMap K E))) : Scheme)] :
    Finite D := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  letI : Surjective r := (surjective_iff _).mpr (by
    intro y
    exact ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ _⟩)
  exact Finite.of_surjective (pullback.fst d r) ((surjective_iff _).mp inferInstance)

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedSelected_endpoint_finite
    {K : Type u} [Field K] {X : Scheme.{u}} {N : X.Modules}
    (f : X ⟶ Spec (.of K)) [IsSeparated f] (e : SerreExtensionData X N)
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    [Finite (C.localPencilZeroGluedScheme e seed 0 (𝟙 _) : Scheme)] :
    ((C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed ≫
      projectiveLineAmbientToLine K f) ⁻¹'
        {projectiveLineEndpoint K true (IsLocalRing.closedPoint K)}).Finite := by
  let i := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  let ep := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true
  let g := i ≫ projectiveLineAmbientToLine K f
  let s := projectiveLineEndpoint K true
  let a := cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_iso f C seed
  letI : Finite (pullback i ep : Scheme) := Finite.of_injective a.hom a.hom.injective
  have h : IsPullback (pullback.fst i ep) (pullback.snd i ep ≫ f) g s :=
    (IsPullback.of_hasPullback i ep).paste_vert
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_isPullback f true)
  letI : Finite (pullback g s : Scheme) :=
    Finite.of_injective h.isoPullback.inv h.isoPullback.inv.injective
  have hr : Set.range s = {s (IsLocalRing.closedPoint K)} := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact congrArg s (Subsingleton.elim z (IsLocalRing.closedPoint K))
    · intro hy
      exact ⟨IsLocalRing.closedPoint K,hy.symm⟩
  have hf : (Set.range (pullback.fst g s)).Finite := Set.finite_range _
  rw [Scheme.Pullback.range_fst,hr] at hf
  exact hf

end PfaffianDescent
