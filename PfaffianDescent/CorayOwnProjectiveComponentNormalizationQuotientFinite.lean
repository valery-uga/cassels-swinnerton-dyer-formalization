import PfaffianDescent.CorayGlobalOriginalSectionsFinite
import PfaffianDescent.CorayProjectiveGlobalNormalizationSupport
import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry

/-! OWN component normalization quotient, over its actual original K structure.
Finite sections and support follow from actual curve charts; neither unit H0/H1
finiteness nor a genus/Euler theorem is asserted. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- For an actual integral projective quotient, finite original-K normalization
quotient sections follow from native chart dimension, not a finiteness certificate. -/
theorem homogeneousProjective_genericNormalizationQuotient_globalSections_finite_of_chartDimension
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsIntegral (scheme I)]
    (hchart : ∀ j : Fin 4, ringKrullDim (ChartRing I j) ≤ 1) :
    Module.Finite K (SchemeModuleGlobalSectionsOver (toBase I)
      (genericNormalizationQuotientSheaf (scheme I))) := by
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  let V : Fin 4 → X.Opens := fun j => (chartι I j).opensRange
  have hcover : ⊤ ≤ ⨆ j, V j := by
    intro x hx
    obtain ⟨j, y, hy⟩ := exists_coordinate_chart I x
    apply Opens.mem_iSup.mpr
    exact ⟨j, y, hy⟩
  have hcoverUp : ⊤ ≤ ⨆ j : ULift.{u} (Fin 4), V j.down := by
    intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcover hx)
    exact Opens.mem_iSup.mpr ⟨⟨j⟩, hj⟩
  apply schemeModule_globalSections_finite_of_finite_open_cover pi Q
    (fun j : ULift.{u} (Fin 4) => V j.down) hcoverUp
  intro jUp
  let j := jUp.down
  by_cases hnonempty : Nonempty (V j)
  · letI : Nonempty (V j) := hnonempty
    have hV : IsAffineOpen (V j) := isAffineOpen_opensRange (chartι I j)
    let e : Γ(X, V j) ≃+* ChartRing I j :=
      ((IsOpenImmersion.ΓIsoTop (chartι I j)).symm ≪≫
        Scheme.ΓSpecIso (CommRingCat.of (ChartRing I j))).commRingCatIsoToRingEquiv
    have hdim : ringKrullDim Γ(X, V j) ≤ 1 := by
      rw [ringKrullDim_eq_of_ringEquiv e]
      exact hchart j
    letI : Ring.KrullDimLE 1 Γ(X, V j) := Ring.krullDimLE_iff.mpr hdim
    letI : Ring.DimensionLEOne Γ(X, V j) :=
      ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
    exact genericNormalizationQuotientSheaf_affineSections_finite_over_ground X pi (V j) hV
  · letI := schemeModuleOpenSections_subsingleton_of_not_nonempty pi Q (V j) hnonempty
    infer_instance


/-- The OWN actual quotient sheaf has finite native nonzero-stalk support. -/
theorem homogeneousProjective_genericNormalizationQuotient_stalkSupport_finite_of_chartDimension
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsIntegral (scheme I)]
    (hchart : ∀ j : Fin 4, ringKrullDim (ChartRing I j) ≤ 1) :
    (schemeModuleStalkSupport
      (genericNormalizationQuotientSheaf (scheme I))).Finite := by
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  let V : Fin 4 → X.Opens := fun j => (chartι I j).opensRange
  let Y : Fin 4 → Scheme.{u} := fun j => (V j).toScheme
  let f : ∀ j, Y j ⟶ X := fun j => (V j).ι
  have hcover : ∀ x : X, ∃ j, ∃ y : Y j, f j y = x := by
    intro x
    obtain ⟨j, z, hz⟩ := exists_coordinate_chart I x
    exact ⟨j, ⟨x, z, hz⟩, rfl⟩
  have hcoverUp : ∀ x : X, ∃ j : ULift.{u} (Fin 4), ∃ y : Y j.down,
      f j.down y = x := by
    intro x
    obtain ⟨j, y, hy⟩ := hcover x
    exact ⟨⟨j⟩, y, hy⟩
  apply schemeModuleStalkSupport_finite_of_finite_open_cover Q
    (fun j : ULift.{u} (Fin 4) => Y j.down) (fun j => f j.down) hcoverUp
  intro jUp
  let j := jUp.down
  by_cases hnonempty : Nonempty (V j)
  · letI : Nonempty (V j) := hnonempty
    have hV : IsAffineOpen (V j) := isAffineOpen_opensRange (chartι I j)
    let e : Γ(X, V j) ≃+* ChartRing I j :=
      ((IsOpenImmersion.ΓIsoTop (chartι I j)).symm ≪≫
        Scheme.ΓSpecIso (CommRingCat.of (ChartRing I j))).commRingCatIsoToRingEquiv
    have hdim : ringKrullDim Γ(X, V j) ≤ 1 := by
      rw [ringKrullDim_eq_of_ringEquiv e]
      exact hchart j
    letI : Ring.KrullDimLE 1 Γ(X, V j) := Ring.krullDimLE_iff.mpr hdim
    letI : Ring.DimensionLEOne Γ(X, V j) :=
      ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
    exact genericNormalizationQuotientSheaf_affineStalkSupport_finite X pi (V j) hV
  · have hempty : schemeModuleStalkSupport
        ((Scheme.Modules.restrictFunctor (f j)).obj Q) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hnonempty ⟨y⟩
    rw [hempty]
    exact Set.finite_empty


/-- A genuine prime component containing the original smooth-cubic/p-q curve
equations has finite OWN original-K normalization quotient sections and support.
Primeness and the actual point derive native integrality internally; literal
quotient charts derive every required curve dimension. No desired finiteness,
comparison, constants-field, or degree/genus premise is supplied. -/
theorem selectedProjectivePrimeComponent_genericNormalizationQuotient_finite_sections_and_support
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    Module.Finite K (SchemeModuleGlobalSectionsOver (toBase C)
      (genericNormalizationQuotientSheaf (scheme C))) ∧
    (schemeModuleStalkSupport
      (genericNormalizationQuotientSheaf (scheme C))).Finite := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  have hchart : ∀ j : Fin 4, ringKrullDim (ChartRing C j) ≤ 1 :=
    selectedProjectiveComponent_chart_ringKrullDim_le_one p q hp hp0 n hq hnot C hIC
  exact ⟨homogeneousProjective_genericNormalizationQuotient_globalSections_finite_of_chartDimension C hchart,
    homogeneousProjective_genericNormalizationQuotient_stalkSupport_finite_of_chartDimension C hchart⟩

end PfaffianDescent.Coray
