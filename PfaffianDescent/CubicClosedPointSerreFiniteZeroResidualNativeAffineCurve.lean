import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffinePairFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualProjectiveLineLocal
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_spec_stalk_isField_of_prime_bot
    {C : Type u} [CommRing C] (y : Spec (.of C)) (hy : y.asIdeal = ⊥) :
    IsField ((Spec (.of C)).presheaf.stalk y) := by
  letI : Algebra (CommRingCat.of C) ((Spec (.of C)).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of C) y
  letI : IsLocalization.AtPrime ((Spec (.of C)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of C) y
  rw [isField_iff_maximalIdeal_eq,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal y.asIdeal, hy, Ideal.map_bot]

theorem cubicClosedPointSerreFiniteZeroResidual_spec_curve_point_field_or_maximal
    {C : Type u} [CommRing C] [IsDomain C] [IsPrincipalIdealRing C]
    (y : Spec (.of C)) :
    IsField ((Spec (.of C)).presheaf.stalk y) ∨ y.asIdeal.IsMaximal := by
  by_cases hy : y.asIdeal = ⊥
  · exact Or.inl (cubicClosedPointSerreFiniteZeroResidual_spec_stalk_isField_of_prime_bot y hy)
  · exact Or.inr (IsPrime.to_maximal_ideal hy)

theorem cubicClosedPointSerreFiniteZeroResidual_nativeAffine_pair_zero_flat_of_curve
    {C B : Type u} [CommRing C] [IsDomain C] [IsPrincipalIdealRing C]
    [CommRing B] [IsNoetherianRing B]
    (g : C →+* B) [Flat (Spec.map (CommRingCat.ofHom g))] (a b : B)
    [LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span ({a, b} : Set B)))) ≫ Spec.map (CommRingCat.ofHom g))]
    (hR : ∀ y : Spec (.of C), IsRegularLocalRing ((Spec (.of C)).presheaf.stalk y))
    (hdR : ∀ y : Spec (.of C), ringKrullDim ((Spec (.of C)).presheaf.stalk y) ≤ 1)
    (hF : let f := Spec.map (CommRingCat.ofHom g)
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))
      ∀ z, (f (i z)).asIdeal.IsMaximal →
        IsRegularLocalRing ((f.fiber (f (i z))).presheaf.stalk (f.asFiber (i z))) ∧
          ringKrullDim ((f.fiber (f (i z))).presheaf.stalk (f.asFiber (i z))) = 2) :
    Flat (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B)))) ≫
      Spec.map (CommRingCat.ofHom g)) := by
  apply Flat.of_stalkMap
  intro z
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))
  let f := Spec.map (CommRingCat.ofHom g)
  let y := f (i z)
  let R := (Spec (.of C)).presheaf.stalk y
  rcases cubicClosedPointSerreFiniteZeroResidual_spec_curve_point_field_or_maximal y with hf | hm
  · exact RingHom.Flat.of_isField hf _
  letI : y.asIdeal.IsMaximal := hm
  letI : IsRegularLocalRing R := hR y
  rcases cubicClosedPointSerreFiniteZeroResidual_regularLocal_field_or_parameter_of_dim_le_one
    R (hdR y) with hf | ⟨π, hπ, hd⟩
  · exact RingHom.Flat.of_isField hf _
  obtain ⟨t, ht⟩ := (inferInstance : y.asIdeal.IsPrincipal)
  have hgeom := hF z hm
  letI := hgeom.1
  exact cubicClosedPointSerreFiniteZeroResidual_nativeAffine_pair_zero_stalk_flat
    g a b z hd t ht hgeom.2

end PfaffianDescent
