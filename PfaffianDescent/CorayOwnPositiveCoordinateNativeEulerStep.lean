import PfaffianDescent.SchemeModuleFiniteClosedSupportNativeAcyclic
import PfaffianDescent.CorayOwnPositiveCoordinateCokernelHZero
import PfaffianDescent.SchemeModuleFinitePointSequenceBalance

/-! SOURCE ONLY. The SAME original integral component and its SAME positive
coordinate multiplication have actual acyclic cokernel. Native H0-H1 changes
by the actual cokernel rank. No genus, constant-field=K or Hilbert-degree
comparison certificate occurs. Finiteness of the preceding coefficient is
only the explicit induction input for the final finite-rank step. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original p/q geometry proves finite closed-point support of the actual
coordinate zero locus. This does not replace the whole Cartier cut by its
reduction: only the underlying support set is used here. -/
theorem selectedProjectivePrimeComponent_coordinateZero_finite_closedPoints
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) :
    ({x : scheme C | coordinate C j ∈ x.asHomogeneousIdeal} : Set (scheme C)).Finite ∧
      ∀ x ∈ ({x : scheme C | coordinate C j ∈ x.asHomogeneousIdeal} : Set (scheme C)),
        IsClosed ({x} : Set (scheme C)) := by
  classical
  let X := scheme C
  letI : IsIntegral X := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toBase C)
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (toBase C)
  letI : IsNoetherian X := ⟨⟩
  let Z : Set X := {x | coordinate C j ∈ x.asHomogeneousIdeal}
  let U := Proj.basicOpen (grading C) (coordinate C j)
  have hZeq : Z = U.1ᶜ := by
    ext x
    change coordinate C j ∈ x.asHomogeneousIdeal ↔ ¬ coordinate C j ∉ x.asHomogeneousIdeal
    exact not_not.symm
  have hZclosed : IsClosed Z := by
    rw [hZeq]
    exact U.isOpen.isClosed_compl
  have hgeneric : genericPoint X ∉ Z := by
    exact (genericPoint_specializes P).mem_open U.isOpen hj
  have hdim (x : X) : Ring.DimensionLEOne (X.presheaf.stalk x) := by
    letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr
      (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
        p q hp hp0 n hq hnot C hIC x)
    exact ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  exact integralCurve_closed_avoiding_generic_finite_and_closedPoints
    X hdim Z hZclosed hgeneric

/-- All positive native cohomology of the actual coordinate-multiplication
cokernel vanishes. No acyclicity or residue-degree hypothesis is supplied. -/
theorem selectedProjectivePrimeComponent_ownPositiveCoordinateCokernel_cohomology_succ_subsingleton
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) [HasExt.{u} (scheme C).Modules]
    (m a : ℕ) :
    Subsingleton (schemeModuleCohomology (scheme C)
      (cokernel (ownPositiveCoordinateMultiplication C j m)) (a + 1)) := by
  obtain ⟨hfinite, hclosed⟩ :=
    selectedProjectivePrimeComponent_coordinateZero_finite_closedPoints
      p q hp hp0 n hq hnot C hIC hprime P j hj
  exact schemeModuleFiniteClosedSupport_cohomology_succ_subsingleton (toBase C) _
    {x : scheme C | coordinate C j ∈ x.asHomogeneousIdeal} hfinite hclosed
    (ownPositiveCoordinateCokernel_support_subset_coordinateZero C j m) a

/-- The original-coordinate H1 map on the OWN positive twists is surjective,
proved from its actual ShortExact cokernel sequence and native acyclicity. -/
theorem selectedProjectivePrimeComponent_ownPositiveCoordinate_hOneMap_surjective
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) [HasExt.{u} (scheme C).Modules]
    (m : ℕ) :
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    Function.Surjective (schemeModuleCohomologyLinearMapOver (toBase C)
      (ownPositiveCoordinateMultiplication C j m) 1) := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  let S := ShortComplex.cokernelSequence (ownPositiveCoordinateMultiplication C j m)
  letI : Subsingleton (schemeModuleCohomology (scheme C) S.X₃ 1) :=
    selectedProjectivePrimeComponent_ownPositiveCoordinateCokernel_cohomology_succ_subsingleton
      p q hp hp0 n hq hnot C hIC hprime P j hj m 0
  exact schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton (toBase C)
    (ShortComplex.cokernelSequence (ownPositiveCoordinateMultiplication C j m))
    (ownPositiveCoordinateMultiplication_cokernelSequence_shortExact C hprime P j hj m)

/-- A bounded native Euler induction step on the SAME OWN positive twists.
The quotient finiteness, its native H1 zero and ShortExactness are derived
from original geometry. The actual constants remain in H0 at degree zero. -/
theorem selectedProjectivePrimeComponent_ownPositiveCoordinate_finite_and_nativeEuler_step
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) [HasExt.{u} (scheme C).Modules]
    (m : ℕ) :
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    let L := positiveSheafOfModules (grading C) m
    let M := positiveSheafOfModules (grading C) (m + 1)
    let Q := cokernel (ownPositiveCoordinateMultiplication C j m)
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C) L ⊤) →
    Module.Finite K (schemeModuleCohomology (scheme C) L 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C) M ⊤) ∧
      Module.Finite K (schemeModuleCohomology (scheme C) M 1) ∧
      ((Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) M ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology (scheme C) M 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) L ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology (scheme C) L 1) +
          Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) Q ⊤)) := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  dsimp only
  intro h0 h1
  let S := ShortComplex.cokernelSequence (ownPositiveCoordinateMultiplication C j m)
  have hS := ownPositiveCoordinateMultiplication_cokernelSequence_shortExact C hprime P j hj m
  have hQ := selectedProjectivePrimeComponent_ownPositiveCoordinateCokernel_topSections_finite
    p q hp hp0 n hq hnot C hIC hprime P j hj m
  have hv := selectedProjectivePrimeComponent_ownPositiveCoordinateCokernel_cohomology_succ_subsingleton
    p q hp hp0 n hq hnot C hIC hprime P j hj m 0
  have h := schemeModuleShortExact_finite_second_and_h0_h1_balance (toBase C) S hS h0 h1 hQ hv
  have hBalance :
      (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) S.X₂ ⊤) : ℤ) +
          Module.finrank K (schemeModuleCohomology (scheme C) S.X₁ 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) S.X₁ ⊤) : ℤ) +
          Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) S.X₃ ⊤) +
          Module.finrank K (schemeModuleCohomology (scheme C) S.X₂ 1) := by
    exact_mod_cast h.2.2
  exact ⟨h.1, h.2.1, by
    change (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) S.X₂ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology (scheme C) S.X₂ 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) S.X₁ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology (scheme C) S.X₁ 1) +
        Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) S.X₃ ⊤)
    omega⟩

end PfaffianDescent.Coray
