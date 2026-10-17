import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalStalk
import Mathlib.RingTheory.Ideal.Operations

/-! # The Serre quotient identifies fiber values with ideal first derivatives -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A surjection whose kernel lies in the ideal multiple induces an actual
isomorphism of the two residue quotients. -/
def cubicClosedPointSerreDegreeThreeEvaluation_residueQuotientEquiv
    {R E M : Type u} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M] (I : Ideal R) (p : E →ₗ[R] M)
    (hsurj : Function.Surjective p)
    (hker : p.ker ≤ I • (⊤ : Submodule R E)) :
    (E ⧸ I • (⊤ : Submodule R E)) ≃ₗ[R]
      (M ⧸ I • (⊤ : Submodule R M)) := by
  let f := (I • (⊤ : Submodule R E)).mapQ
    (I • (⊤ : Submodule R M)) p (Submodule.smul_top_le_comap_smul_top I p)
  apply LinearEquiv.ofBijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, Submodule.comap_smul_top_of_surjective I p hsurj,
      sup_eq_left.mpr hker, Submodule.mkQ_map_self]
  · apply LinearMap.range_eq_top.mp
    rw [Submodule.range_mapQ, LinearMap.range_eq_top.mpr hsurj,
      Submodule.map_top, Submodule.range_mkQ]

/-- The quotient isomorphism literally sends a section value to its image
under the extension projection, modulo the ideal multiple. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_residueQuotientEquiv_apply
    {R E M : Type u} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M] (I : Ideal R) (p : E →ₗ[R] M)
    (hsurj : Function.Surjective p)
    (hker : p.ker ≤ I • (⊤ : Submodule R E)) (e : E) :
    cubicClosedPointSerreDegreeThreeEvaluation_residueQuotientEquiv I p hsurj hker
      (Submodule.Quotient.mk e) = Submodule.Quotient.mk (p e) := rfl

/-- Exactness makes the kernel lie in the ideal multiple whenever the
canonical section has coordinates in that ideal. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_kernel_le_smul_of_coordinates
    {R E M : Type u} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M] (I : Ideal R) (i : R →ₗ[R] E)
    (p : E →ₗ[R] M) (hexact : Function.Exact i p)
    (t : E ≃ₗ[R] R × R) (hfirst : (t (i 1)).1 ∈ I) (hsecond : (t (i 1)).2 ∈ I) :
    p.ker ≤ I • (⊤ : Submodule R E) := by
  have hi : i 1 ∈ I • (⊤ : Submodule R E) := by
    have hdecomp : i 1 = (t (i 1)).1 • t.symm (1, 0) +
        (t (i 1)).2 • t.symm (0, 1) := by
      apply t.injective
      simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
      ext <;> simp
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hfirst (Submodule.mem_top))
      (Submodule.smul_mem_smul hsecond (Submodule.mem_top))
  intro z hz
  obtain ⟨r, rfl⟩ := (hexact z).mp hz
  have hir : i r = r • i 1 := by simpa using i.map_smul r (1 : R)
  rw [hir]
  exact Submodule.smul_mem _ r hi

namespace ProjectiveNegativeTwist
open AllCharacteristics.HomogeneousProjective
attribute [local instance] MvPolynomial.gradedAlgebra

section Native
variable (K : Type u) [Field K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
  (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
  [hExt : HasExt.{u} (hypersurface p hp).Modules]
  [hExtStalk : HasExt.{u + 1}
    (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
  (e : SerreExtensionSequenceData (hypersurface p hp)
    (closedImmersionIdealTwist i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
  (hne :
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
    (closedImmersionIdealTwistSequence_shortExact i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
      (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e hExt)
      (show 1 + 1 = 2 by omega) ≠ 0)

include hp0 hne in
/-- The actual original Serre projection's kernel is contained in the maximal
ideal multiple of its actual stalk. Native lci coordinates and the checked
canonical coordinate ideal discharge this containment. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_native_stalk_kernel_le :
    let X := hypersurface p hp
    let x := i default
    let N : X.Modules := e.E
    let M : X.Modules := closedImmersionIdealTwist i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
    letI := schemeModuleStalkModule N x
    letI := schemeModuleStalkModule M x
    (schemeModuleStalkLinearMap e.projection x).ker ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (N.presheaf.stalk x)) := by
  dsimp only
  let X := hypersurface p hp
  let x := i default
  let R := X.presheaf.stalk x
  let N : X.Modules := e.E
  let M : X.Modules := closedImmersionIdealTwist i
    (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
  letI : Module R (N.presheaf.stalk x) := schemeModuleStalkModule N x
  letI : Module R (M.presheaf.stalk x) := schemeModuleStalkModule M x
  let d := Classical.choice (cubicClosedPointSerreLocalKoszulNative_exists_chart K p hp hp0 i)
  let xU : d.U := ⟨x, d.mem⟩
  obtain ⟨a, _, _⟩ := cubicClosedPointSerreLocalKoszulFree_exists_idealCoordinate
    i (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
    d.U d.q d.f d.twist d.sequence xU
  let q := X.presheaf.germ d.U x d.mem d.q
  let f := X.presheaf.germ d.U x d.mem d.f
  have hspan : Ideal.span ({q, f} : Set R) = IsLocalRing.maximalIdeal R := d.span_maximal
  have hq : q ∈ IsLocalRing.maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hf : f ∈ IsLocalRing.maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hfree : Module.Free R (N.presheaf.stalk x) :=
    cubicClosedPointSerreLocalFree_stalk_free K p hp hp0 i e hne
  obtain ⟨t, _⟩ := serreExtension_stalk_exists_freeCoordinates_of_quotientEquiv_at_lci_point
    e x q f a.toLinearEquiv d.regular_first d.regular_second hq hf hfree
  have ht := cubicClosedPointSerreFiniteZeroResidual_canonical_stalk_span K p hp hp0 i e hne t
  change Ideal.span ({(t (serreExtensionStalkCanonicalSection e x 1)).1,
    (t (serreExtensionStalkCanonicalSection e x 1)).2} : Set R) =
      IsLocalRing.maximalIdeal R at ht
  have hfirst : (t (serreExtensionStalkCanonicalSection e x 1)).1 ∈
      IsLocalRing.maximalIdeal R := ht ▸ Ideal.subset_span (by simp)
  have hsecond : (t (serreExtensionStalkCanonicalSection e x 1)).2 ∈
      IsLocalRing.maximalIdeal R := ht ▸ Ideal.subset_span (by simp)
  have hexact : Function.Exact (serreExtensionStalkCanonicalSection e x)
      (schemeModuleStalkLinearMap e.projection x) := by
    exact functionExact_precomp_of_surjective
      (schemeModuleStalkLinearMap e.inclusion x)
      (presheafOfModules_unitStalkLinearEquiv X.presheaf x)
      (schemeModuleStalkLinearMap e.projection x)
      (serreExtension_stalk_linear_exact e x)
      (presheafOfModules_unitStalkLinearEquiv X.presheaf x).surjective
  exact cubicClosedPointSerreDegreeThreeEvaluation_kernel_le_smul_of_coordinates
    (IsLocalRing.maximalIdeal R) (serreExtensionStalkCanonicalSection e x)
    (schemeModuleStalkLinearMap e.projection x) hexact t hfirst hsecond

include hp0 hne in
/-- The literal original stalk projection induces the native fiber-to-first-
derivative isomorphism. Neither a fiber coordinate nor a dimension certificate
is supplied. -/
def cubicClosedPointSerreDegreeThreeEvaluation_native_stalk_firstDerivativeEquiv :
    let X := hypersurface p hp
    let x := i default
    let N : X.Modules := e.E
    let M : X.Modules := closedImmersionIdealTwist i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
    letI := schemeModuleStalkModule N x
    letI := schemeModuleStalkModule M x
    (N.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (N.presheaf.stalk x))) ≃ₗ[X.presheaf.stalk x]
    (M.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x))) := by
  dsimp only
  let X := hypersurface p hp
  let x := i default
  let N : X.Modules := e.E
  let M : X.Modules := closedImmersionIdealTwist i
    (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
  letI := schemeModuleStalkModule N x
  letI := schemeModuleStalkModule M x
  exact cubicClosedPointSerreDegreeThreeEvaluation_residueQuotientEquiv
    (IsLocalRing.maximalIdeal ((hypersurface p hp).presheaf.stalk (i default)))
    (schemeModuleStalkLinearMap e.projection (i default))
    (serreExtension_projection_stalkMap_surjective e (i default))
    (cubicClosedPointSerreDegreeThreeEvaluation_native_stalk_kernel_le K p hp hp0 i e hne)

/-- The native isomorphism commutes with the literal actual stalk projection. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_native_stalk_firstDerivativeEquiv_apply :
    let X := hypersurface p hp
    let x := i default
    let N : X.Modules := e.E
    let M : X.Modules := closedImmersionIdealTwist i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
    letI := schemeModuleStalkModule N x
    letI := schemeModuleStalkModule M x
    ∀ z : N.presheaf.stalk x,
      cubicClosedPointSerreDegreeThreeEvaluation_native_stalk_firstDerivativeEquiv
        K p hp hp0 i e hne (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk (schemeModuleStalkLinearMap e.projection x z) := by
  dsimp only
  intro z
  rfl

end Native
end ProjectiveNegativeTwist
end PfaffianDescent
