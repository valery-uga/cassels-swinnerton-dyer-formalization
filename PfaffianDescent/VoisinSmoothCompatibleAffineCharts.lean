import PfaffianDescent.VoisinSmoothEightConfigurationIntegrality
import PfaffianDescent.VoisinSelectedConfigurationAffineChart

/-!
# Compatible affine charts through a geometric configuration point

The quotient-chart construction depends only on the underlying point of the
ordered configuration scheme.  Recording that form lets a point with a
nontrivial residue field determine affine charts containing the unordered
generic point.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A geometric ordered configuration point lying in a prescribed common
affine chart has compatible ordered and unordered quotient charts; when the
unordered base is integral, the unordered chart also contains its generic
point. -/
theorem exists_cubicConfiguration_compatible_affineCharts_inside_commonOpen_at_point
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (V : (hypersurface p hp).affineOpens)
    (x : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hxV : x.val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp) V.val 8) :
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (i : U ⟶ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left)
      (j : Q ⟶ cubicConfigurationBase p hp 8)
      (r : U ⟶ Q),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ Surjective r ∧
      IsIntegralHom r ∧ IsFinite r ∧
      x ∈ Set.range i ∧
      configurationQuotientMap (equationIdeal p hp) 8 x ∈ Set.range j ∧
      genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j ∧
      i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j ∧
      (∀ z : U, (i z).val ∈
        orderedFamilyCommonOpen (hypersurfaceToBase p hp) V.val 8) := by
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hi, hτi, b, hb, j, hj,
    hxi, hcomm, _, hinside⟩ :=
    exists_projectiveConfigurationQuotient_affineChart_inside_commonOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 V x hxV
  let Q := affineSchemeActionQuotient (Equiv.Perm (Fin 8))
    τ hτ₁ hτcomp b hb
  let r : U ⟶ Q := affineSchemeActionQuotientMap
    (Equiv.Perm (Fin 8)) τ hτ₁ hτcomp b hb
  have hQa : IsAffine Q := inferInstance
  obtain ⟨u, hu⟩ := hxi
  have hQj : configurationQuotientMap (equationIdeal p hp) 8 x ∈
      Set.range j := by
    refine ⟨r u, ?_⟩
    have hcommpoint := congrArg
      (fun f : U ⟶ cubicConfigurationBase p hp 8 => f u) hcomm
    have hquotx : configurationQuotientMap (equationIdeal p hp) 8 (i u) =
        configurationQuotientMap (equationIdeal p hp) 8 x :=
      congrArg _ hu
    exact hcommpoint.symm.trans hquotx
  letI : IsOpenImmersion j := hj
  have hgeneric : genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j :=
    (@genericPoint_specializes (cubicConfigurationBase p hp 8) _ _ _
      (configurationQuotientMap (equationIdeal p hp) 8 x)).mem_open
        (IsOpenImmersion.isOpen_range j) hQj
  have hsurjr : Surjective r := by
    dsimp only [r]
    infer_instance
  have hintr : IsIntegralHom r := by
    dsimp only [r]
    infer_instance
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  have hret : Etale r := by
    dsimp only [r]
    exact etale_affineConfigurationActionQuotientMap
      (hypersurfaceToBase p hp) 8 τ hτ₁ hτcomp b hb i hτi
  letI : Etale r := hret
  have hfinr : IsFinite r :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType r).mpr
      ⟨hintr, inferInstance⟩
  exact ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr,
    ⟨u, hu⟩, hQj, hgeneric, hcomm, hinside⟩

end PfaffianDescent
