import PfaffianDescent.CorayOwnPositiveHomogeneousNativeSurjectivity
import PfaffianDescent.CorayComponentHilbertFunctionBound

/-! SOURCE ONLY. Eventual native Hilbert dictionary of the ORIGINAL prime
coordinate component. The canonical map is bijective; actual constants are
not replaced by the original field, and no genus statement is inferred. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing canonical grade map is eventually bijective for the SAME
relevant prime component. Nonemptiness comes from the original point P. -/
theorem projectivePrime_eventually_positiveHomogeneousGlobalSectionLinearMap_bijective
    [HasExt.{u} (Proj PS).Modules] (C : HomogeneousIdeal PS)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Function.Bijective (positiveHomogeneousGlobalSectionLinearMap C m) := by
  letI : C.toIdeal.IsPrime := hprime
  letI : IsDomain (CoordinateRing C) := (Ideal.Quotient.isDomain_iff_prime C.toIdeal).mpr hprime
  letI : Nonempty (scheme C) := ⟨P⟩
  obtain ⟨B, hB⟩ := homogeneousIdeal_eventually_positiveHomogeneousGlobalSectionLinearMap_surjective C
  exact ⟨B, fun m hm => ⟨positiveHomogeneousGlobalSectionLinearMap_injective C m, hB m hm⟩⟩

/-- Genuine eventual native H0 finiteness and Hilbert equality, with the
original toBase-C field action. The equivalence is the existing canonical
fraction section map, not a rank certificate or transported scalar action. -/
theorem projectivePrime_eventually_positiveTwist_topSections_finite_and_gradeRank
    [HasExt.{u} (Proj PS).Modules] (C : HomogeneousIdeal PS)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
        (positiveSheafOfModules (grading C) m) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (positiveSheafOfModules (grading C) m) ⊤) = Module.finrank K (grading C m) := by
  obtain ⟨B, hB⟩ := projectivePrime_eventually_positiveHomogeneousGlobalSectionLinearMap_bijective C hprime P
  refine ⟨B, fun m hm => ?_⟩
  let e := (LinearEquiv.ofBijective (positiveHomogeneousGlobalSectionLinearMap C m) (hB m hm)).trans
    (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase C)
      (positiveSheafOfModules (grading C) m))
  letI : Module.Finite K (grading C m) := by
    change Module.Finite K ((homogeneousSubmodule (Fin 4) K m).map
      (Ideal.Quotient.mkₐ K C.toIdeal).toLinearMap)
    infer_instance
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm⟩

/-- Full original p/q/minimal-component input discharges primality
internally and retains SAME C, P, degree and original base actions. -/
theorem selectedProjectiveMinimalComponent_eventually_ownPositiveTwist_topSections_finite_and_gradeRank
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal PS)
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
        (positiveSheafOfModules (grading C) m) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (positiveSheafOfModules (grading C) m) ⊤) = Module.finrank K (grading C m) := by
  letI : EnoughInjectives (Proj PS).Modules := sheafOfModules_enoughInjectives (Proj PS).ringCatSheaf
  letI : HasExt.{u} (Proj PS).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (Proj PS).Modules
  exact projectivePrime_eventually_positiveTwist_topSections_finite_and_gradeRank C hCmin.isPrime P

end PfaffianDescent.Coray
